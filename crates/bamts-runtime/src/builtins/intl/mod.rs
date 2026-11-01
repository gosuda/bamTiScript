//! The JavaScript binding of ECMA-402.
//!
//! Algorithms live in `crate::intl`; this module owns what only JavaScript can
//! observe: argument conversion, the order options and properties are read in,
//! receiver checks, and the shape of the installed objects.

mod collator;
mod display_names;
mod list_format;
mod locale;
mod number_format;
mod options;
mod plural_rules;
mod relative_time_format;

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::super::push;
use super::{
    allocate_array, allocate_string, define_data, install_constructor_function, install_function,
};
use crate::intl::canonical_locales;
use crate::intl::locale_data::DATA;
use crate::intl::locale_negotiation::{LanguageTag, supported_locales};
use crate::intl::{IntlKind, IntlObject};
use crate::intrinsics::{BuiltinDef, BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    BoundCallable, EvalFailure, HeapEntry, Host, Machine, NativeCallable, Property, PropertyKey,
    PropertyMap,
};

/// Name, `length`, and implementation of one installed function.
pub(super) type Method<H> = (&'static str, u32, BuiltinHandler<H>);

/// Property name, function name, and implementation of one accessor.
pub(super) type Getter<H> = (&'static str, &'static str, BuiltinHandler<H>);

/// A function the runtime hands out but never installs, found again by `name`.
pub(super) fn register_hidden<H: Host>(
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    length: u32,
    handler: BuiltinHandler<H>,
) {
    builtins.register(BuiltinDef {
        name,
        length,
        handler,
    });
}

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
    let fallback_symbol = push(
        heap,
        HeapEntry::Symbol {
            description: EcmaString::encode("IntlLegacyConstructedSymbol"),
        },
    );
    builtins.set_intl_fallback_symbol(fallback_symbol);
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
    collator::install(heap, builtins, namespace);
    number_format::install(heap, builtins, namespace);
    plural_rules::install(heap, builtins, namespace);
    list_format::install(heap, builtins, namespace);
    relative_time_format::install(heap, builtins, namespace);
    display_names::install(heap, builtins, namespace);
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

/// Maps a service-core error to the exception it stands for.
pub(super) fn service_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    error: &crate::intl::plural_rules::IntlError,
) -> EvalFailure {
    match error.kind() {
        crate::intl::plural_rules::IntlErrorKind::TypeError => {
            type_error(machine, error.to_string())
        }
        _ => range_error(machine, error.to_string()),
    }
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

/// The prototype OrdinaryCreateFromConstructor picks. The service constructors
/// read it first, before their arguments; a plain call has no `new.target`.
pub(super) fn instance_prototype<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: IntlKind,
    constructing: bool,
) -> Result<Value, EvalFailure> {
    if constructing {
        let new_target = machine.current_new_target();
        let prototype = machine.get_named_property(new_target, "prototype")?;
        if is_object(machine, prototype)? {
            return Ok(prototype);
        }
    }
    Ok(machine.intrinsics.builtins.intl_prototype(kind))
}

/// OrdinaryHasInstance against an Intl constructor, whose `prototype` property
/// is fixed.
fn inherits_from<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    kind: IntlKind,
) -> Result<bool, EvalFailure> {
    if !is_object(machine, value)? {
        return Ok(false);
    }
    let prototype = machine.intrinsics.builtins.intl_prototype(kind);
    let mut object = value;
    while let Some(next) = machine.internal_get_prototype_of(object)? {
        if next == prototype {
            return Ok(true);
        }
        object = next;
    }
    Ok(false)
}

/// ChainNumberFormat and ChainDateTimeFormat: a plain call on an object that
/// inherits from the constructor initializes that object, for the sake of
/// `Intl.Constructor.call(instance)`, by hiding the real instance on it.
pub(super) fn chain_legacy_instance<H: Host>(
    machine: &mut Machine<'_, H>,
    instance: Value,
    kind: IntlKind,
    constructing: bool,
    this: Value,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing || !inherits_from(machine, this, kind)? {
        return Ok(BuiltinOutcome::Value(instance));
    }
    let symbol = machine.intrinsics.builtins.intl_fallback_symbol();
    let key = machine.to_property_key(symbol)?;
    machine.define_descriptor(
        this,
        key,
        Property::Data {
            value: instance,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    )?;
    Ok(BuiltinOutcome::Value(this))
}

/// UnwrapNumberFormat and UnwrapDateTimeFormat: the instance a legacy-chained
/// object hides, or the value itself.
pub(super) fn unwrap_legacy_instance<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    kind: IntlKind,
) -> Result<Value, EvalFailure> {
    let is_instance = intl_record(machine, value)?.is_some_and(|record| record.kind() == kind);
    if is_instance || !inherits_from(machine, value, kind)? {
        return Ok(value);
    }
    let symbol = machine.intrinsics.builtins.intl_fallback_symbol();
    let key = machine.to_property_key(symbol)?;
    machine.get_property_key(value, &key)
}

/// The cached function of a `format` or `compare` getter. The bound receiver
/// is what makes one function per instance, as those getters promise.
pub(super) fn bound_function<H: Host>(
    machine: &mut Machine<'_, H>,
    instance: Value,
    builtin: &str,
    length: u32,
) -> Result<BuiltinOutcome, EvalFailure> {
    let index = machine
        .runtime_slot(instance)
        .map_err(EvalFailure::Runtime)?
        .expect("the getter checked its receiver");
    if let HeapEntry::Intl {
        bound: Some(function),
        ..
    } = &machine.heap[index]
    {
        return Ok(BuiltinOutcome::Value(*function));
    }
    let id = machine
        .intrinsics
        .builtins
        .id_named(builtin)
        .expect("Intl registers its hidden functions");
    let target = machine
        .allocate(HeapEntry::native_function(
            NativeCallable::Builtin(id),
            PropertyMap::default(),
            None,
        ))
        .map_err(EvalFailure::Runtime)?;
    let function = machine
        .allocate(HeapEntry::native_function(
            NativeCallable::Bound(Box::new(BoundCallable {
                target,
                this_value: instance,
                arguments: Vec::new(),
            })),
            PropertyMap::default(),
            None,
        ))
        .map_err(EvalFailure::Runtime)?;
    let name = string_value(machine, "")?;
    for (key, value) in [
        ("length", crate::number_value(f64::from(length))),
        ("name", name),
    ] {
        machine.define_descriptor(
            function,
            PropertyKey::Named(EcmaString::encode(key)),
            Property::Data {
                value,
                writable: false,
                enumerable: false,
                configurable: true,
            },
        )?;
    }
    if let HeapEntry::Intl { bound, .. } = &mut machine.heap[index] {
        *bound = Some(function);
    }
    Ok(BuiltinOutcome::Value(function))
}

/// `supportedLocalesOf` of every service.
pub(super) fn supported_locales_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
) -> Result<BuiltinOutcome, EvalFailure> {
    let requested = options::canonicalize_locale_list(machine, arg(args, 0))?;
    let options = options::coerce_options_to_object(machine, arg(args, 1))?;
    let matcher = options::locale_matcher_option(machine, options)?;
    let supported = supported_locales(&requested, matcher, &*DATA)
        .map_err(|error| range_error(machine, error.to_string()))?;
    string_array_outcome(machine, &supported)
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

pub(super) fn allocate<H: Host>(
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

/// One element of a `formatToParts` result. `source` and `unit` are the
/// properties some services add.
pub(super) fn part_object<H: Host>(
    machine: &mut Machine<'_, H>,
    part_type: &str,
    value: &str,
    extra: Option<(&str, &str)>,
) -> Result<Value, EvalFailure> {
    let part = new_object(machine)?;
    let type_value = string_value(machine, part_type)?;
    define_field(machine, part, "type", type_value)?;
    let text = string_value(machine, value)?;
    define_field(machine, part, "value", text)?;
    if let Some((name, text)) = extra {
        let text = string_value(machine, text)?;
        define_field(machine, part, name, text)?;
    }
    Ok(part)
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

/// The `type` production of a Unicode locale extension.
pub(super) fn is_type_sequence(value: &str) -> bool {
    !value.is_empty()
        && value.split('-').all(|part| {
            (3..=8).contains(&part.len()) && part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

/// StringListFromIterable.
pub(super) fn string_iterable_to_list<H: Host>(
    machine: &mut Machine<'_, H>,
    iterable: Value,
) -> Result<Vec<String>, EvalFailure> {
    let mut list = Vec::new();
    if iterable == Value::UNDEFINED {
        return Ok(list);
    }
    let key = machine.to_property_key(machine.intrinsics.builtins.symbol_iterator())?;
    let object = machine.value_to_object(iterable)?;
    let method = machine.get_property_key(object, &key)?;
    if !machine.is_callable(method)? {
        return Err(type_error(machine, "value is not iterable"));
    }
    let target = machine.call_value(method, iterable, &[])?;
    if !is_object(machine, target)? {
        return Err(type_error(machine, "iterator method returned a non-object"));
    }
    let next = machine.get_named_property(target, "next")?;
    let iterator = machine.create_protocol_iterator(target, next)?;
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[iterator]);
    let result = (|| loop {
        let step = machine.iterator_step(iterator)?;
        let (done, value) = machine.iterator_result_parts(step)?;
        if done {
            return Ok(());
        }
        let Some(text) = machine.string_value(value) else {
            let failure = type_error(machine, "a list element must be a string");
            let _ = machine.close_iterator_raw(iterator);
            return Err(failure);
        };
        list.push(text.to_utf8_lossy());
    })();
    machine.pop_native_roots(depth);
    result?;
    Ok(list)
}

/// StrWhiteSpaceChar.
pub(super) fn is_string_whitespace(character: char) -> bool {
    matches!(
        character,
        '\u{9}' | '\u{a}' | '\u{b}' | '\u{c}' | '\u{d}' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202f}'
                | '\u{205f}'
                | '\u{3000}'
                | '\u{feff}'
    )
}

pub(super) fn boolean_outcome(value: bool) -> BuiltinOutcome {
    BuiltinOutcome::Value(Value::boolean(value))
}

/// The argument at `index`, `undefined` when absent.
pub(super) fn arg(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}
