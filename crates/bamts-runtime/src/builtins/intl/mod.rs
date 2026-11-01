//! The JavaScript binding of ECMA-402.
//!
//! Algorithms live in `crate::intl`; this module owns what only JavaScript can
//! observe: argument conversion, the order options and properties are read in,
//! receiver checks, and the shape of the installed objects.

mod locale;
mod options;

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{
    allocate_array, allocate_string, define_data, install_constructor_function, install_function,
};
use crate::intl::canonical_locales;
use crate::intl::locale_data::DATA;
use crate::intl::locale_negotiation::LanguageTag;
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyKey, PropertyMap};

/// Name, `length`, and implementation of one installed function.
pub(super) type Method<H> = (&'static str, u32, BuiltinHandler<H>);

/// Property name, function name, and implementation of one accessor.
pub(super) type Getter<H> = (&'static str, &'static str, BuiltinHandler<H>);

/// The installed shape of one Intl class.
struct Class<'a, H: Host> {
    kind: IntlKind,
    name: &'static str,
    tag: &'static str,
    length: u32,
    constructor: BuiltinHandler<H>,
    statics: &'a [Method<H>],
    getters: &'a [Getter<H>],
    methods: &'a [Method<H>],
}

fn install_class<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    namespace: Value,
    class: &Class<'_, H>,
) {
    let prototype = builtins.intl_prototype(class.kind);
    let constructor =
        install_constructor_function(heap, builtins, class.name, class.length, class.constructor);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    for &(name, length, handler) in class.statics {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, constructor, name, function);
    }
    for &(property, name, handler) in class.getters {
        let getter = install_function(heap, builtins, name, 0, handler);
        super::temporal::define_getter(heap, prototype, property, getter);
    }
    for &(name, length, handler) in class.methods {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, prototype, name, function);
    }
    let tag_symbol = builtins.symbol_to_string_tag();
    super::define_to_string_tag(heap, prototype, tag_symbol, class.tag);
    define_data(heap, namespace, class.name, constructor);
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let namespace = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let tag_symbol = builtins.symbol_to_string_tag();
    super::define_to_string_tag(heap, namespace, tag_symbol, "Intl");
    // Classes refer to each other's instances, so every prototype exists before
    // any class is populated.
    for kind in IntlKind::ALL {
        let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
        builtins.set_intl_prototype(kind, prototype);
    }
    let functions: [Method<H>; 2] = [
        ("getCanonicalLocales", 1, get_canonical_locales::<H>),
        ("supportedValuesOf", 1, supported_values_of::<H>),
    ];
    for (name, length, handler) in functions {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, namespace, name, function);
    }
    locale::install(heap, builtins, namespace);
    globals.insert(EcmaString::encode("Intl"), namespace);
}

/// `Intl.getCanonicalLocales`.
fn get_canonical_locales<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let locales = options::canonicalize_locale_list(machine, arg(args, 0))?;
    string_array_outcome(machine, &locales)
}

/// `Intl.supportedValuesOf`.
fn supported_values_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let key = machine
        .coerce_string_observable(arg(args, 0))?
        .to_utf8_lossy();
    let values = canonical_locales::supported_values_of(&key, &*DATA)
        .map_err(|error| range_error(machine, error.message))?;
    string_array_outcome(machine, &values)
}

fn throw<H: Host>(machine: &mut Machine<'_, H>, name: &str, message: String) -> EvalFailure {
    let id = machine
        .intrinsics
        .builtins
        .id_named(name)
        .expect("error constructor is installed");
    machine.throw_error(id, message)
}

pub(super) fn range_error<H: Host>(
    machine: &mut Machine<'_, H>,
    message: impl Into<String>,
) -> EvalFailure {
    throw(machine, "RangeError", message.into())
}

pub(super) fn type_error<H: Host>(
    machine: &mut Machine<'_, H>,
    message: impl Into<String>,
) -> EvalFailure {
    throw(machine, "TypeError", message.into())
}

/// `Type(value) is Object`. `Machine::is_object` also answers true for a
/// Symbol, which every "must be an object" check here has to reject.
pub(super) fn is_object<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    Ok(!machine.coercion_is_primitive(value)?)
}

/// The Intl record `value` carries, if it is an Intl instance.
pub(super) fn intl_record<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    value: Value,
) -> Result<Option<&'a IntlObject>, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Ok(None);
    };
    Ok(match &machine.heap[index] {
        HeapEntry::Intl { value, .. } => Some(value),
        _ => None,
    })
}

/// The language tag `value` carries, if it is an `Intl.Locale`.
pub(super) fn locale_record<'a, H: Host>(
    machine: &'a Machine<'_, H>,
    value: Value,
) -> Result<Option<&'a LanguageTag>, EvalFailure> {
    Ok(match intl_record(machine, value)? {
        Some(IntlObject::Locale(tag)) => Some(tag),
        _ => None,
    })
}

/// Allocates an instance with the class's own prototype.
pub(super) fn create<H: Host>(
    machine: &mut Machine<'_, H>,
    value: IntlObject,
) -> Result<Value, EvalFailure> {
    let prototype = machine.intrinsics.builtins.intl_prototype(value.kind());
    allocate(machine, value, prototype)
}

/// Allocates the result of `new`, honouring `new.target`: an object whose
/// `prototype` is not an object gets the class's own prototype rather than
/// `Object.prototype`.
pub(super) fn construct<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: IntlKind,
    value: IntlObject,
) -> Result<BuiltinOutcome, EvalFailure> {
    let new_target = machine.current_new_target();
    let prototype = machine.get_named_property(new_target, "prototype")?;
    let prototype = if is_object(machine, prototype)? {
        prototype
    } else {
        machine.intrinsics.builtins.intl_prototype(kind)
    };
    allocate(machine, value, prototype).map(BuiltinOutcome::Value)
}

fn allocate<H: Host>(
    machine: &mut Machine<'_, H>,
    value: IntlObject,
    prototype: Value,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Intl {
            value: Box::new(value),
            bound: None,
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// Throws unless this call came through `new`.
pub(super) fn require_new<H: Host>(
    machine: &mut Machine<'_, H>,
    constructing: bool,
    name: &str,
) -> Result<(), EvalFailure> {
    if constructing {
        Ok(())
    } else {
        Err(type_error(
            machine,
            format!("Intl.{name} constructor requires new"),
        ))
    }
}

pub(super) fn string_value<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &str,
) -> Result<Value, EvalFailure> {
    allocate_string(machine, EcmaString::encode(text))
}

pub(super) fn string_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    string_value(machine, text).map(BuiltinOutcome::Value)
}

pub(super) fn optional_string_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    text: Option<&str>,
) -> Result<BuiltinOutcome, EvalFailure> {
    match text {
        Some(text) => string_outcome(machine, text),
        None => Ok(BuiltinOutcome::Value(Value::UNDEFINED)),
    }
}

/// An ordinary object for a result.
pub(super) fn new_object<H: Host>(machine: &mut Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// CreateDataProperty on a result object nothing else can see yet.
pub(super) fn define_field<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.create_data_property_key(object, PropertyKey::Named(EcmaString::encode(name)), value)
}

/// An Array of strings, as `CreateArrayFromList` makes it.
pub(super) fn string_array<H: Host>(
    machine: &mut Machine<'_, H>,
    values: &[String],
) -> Result<Value, EvalFailure> {
    let mut elements = Vec::with_capacity(values.len());
    for value in values {
        elements.push(string_value(machine, value)?);
    }
    allocate_array(machine, elements)
}

pub(super) fn string_array_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    values: &[String],
) -> Result<BuiltinOutcome, EvalFailure> {
    string_array(machine, values).map(BuiltinOutcome::Value)
}

pub(super) fn boolean_outcome(value: bool) -> BuiltinOutcome {
    BuiltinOutcome::Value(Value::boolean(value))
}

/// The argument at `index`, `undefined` when absent.
pub(super) fn arg(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}
