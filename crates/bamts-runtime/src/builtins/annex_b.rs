//! ECMA-262 Annex B runtime builtins owned by completion leaf C9.
//!
//! Implemented here:
//! - `String.prototype` HTML wrapper methods and `substr` (§B.2.3), including
//!   the `trimLeft`/`trimRight` aliases of the already-installed
//!   `trimStart`/`trimEnd` function objects (same object identity)
//! - the `Object.prototype.__proto__` accessor (§B.2.2.1), with cycle and
//!   non-extensible rejection behind the ordinary `SetPrototypeOf` semantics
//! - the `Object.prototype` legacy accessor methods (§B.2.2.2-§B.2.2.5):
//!   `__defineGetter__`/`__defineSetter__` install a whole accessor descriptor
//!   after validating the accessor is callable, and
//!   `__lookupGetter__`/`__lookupSetter__` walk the prototype chain for the
//!   matching accessor slot
//! - `RegExp.prototype.compile` (§B.2.5.1), delegating pattern compilation to
//!   the canonical RegExp machinery
//! - RegExp legacy constructor statics (§B.2.5.2), backed by hidden per-realm
//!   state and updated through `record_legacy_match`
//!
//! Delegated surface that Annex B also names but which already has canonical
//! owners installed elsewhere; this module deliberately does not re-declare
//! it:
//! - global `escape`/`unescape` (§B.2.2) -> `builtins/uri.rs`
//! - `Date.prototype.getYear`/`setYear`/`toGMTString` (§B.2.4) ->
//!   `builtins/date_full.rs` (`toGMTString` is the same function object as
//!   `toUTCString` there)
//!
//! Integration: declare `mod annex_b;` and call
//! `annex_b::install(heap, globals, builtins);` immediately after
//! `regexp::install`; `date_full::install`, `object::install`, and
//! `string::install` must already have installed the delegated targets.

use std::collections::BTreeMap;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::{
    allocate_string, define_data, heap_index, install_function, to_integer_or_infinity, type_error,
};
use crate::intrinsics::regexp::Match;
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable, push};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

/// Installs the Annex B surface owned by this module. Runs after the core
/// Object, String, and RegExp installers; see the module documentation.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    install_proto_accessor(heap, atoms, builtins);
    install_object_accessor_methods(heap, atoms, builtins);
    install_string_annex_b(heap, atoms, builtins);
    install_regexp_compile(heap, atoms, builtins);
    install_regexp_legacy_statics(heap, atoms, globals, builtins);
}

fn install_proto_accessor<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
) {
    let getter = install_function(heap, atoms, builtins, "get __proto__", 0, proto_getter::<H>);
    let setter = install_function(heap, atoms, builtins, "set __proto__", 1, proto_setter::<H>);
    define_property(
        heap,
        atoms,
        builtins.object_prototype(),
        "__proto__",
        Property::Accessor {
            getter: Some(getter),
            setter: Some(setter),
            enumerable: false,
            configurable: true,
        },
    );
}
/// §B.2.2.2-§B.2.2.5 accessor slot addressed by the legacy `Object.prototype`
/// methods.
#[derive(Clone, Copy, PartialEq)]
enum LegacyAccessorSlot {
    Getter,
    Setter,
}

/// Installs the §B.2.2.2-§B.2.2.5 `Object.prototype` legacy accessor methods
/// as writable, non-enumerable, configurable data properties, matching the
/// surrounding `Object.prototype` surface.
fn install_object_accessor_methods<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.object_prototype();
    for (name, length, handler) in [
        (
            "__defineGetter__",
            2,
            define_getter::<H> as BuiltinHandler<H>,
        ),
        ("__defineSetter__", 2, define_setter::<H>),
        ("__lookupGetter__", 1, lookup_getter::<H>),
        ("__lookupSetter__", 1, lookup_setter::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, prototype, name, function);
    }
}

/// §B.2.2.2 `Object.prototype.__defineGetter__(P, getter)`.
fn define_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    define_legacy_accessor(
        machine,
        this,
        args,
        constructing,
        LegacyAccessorSlot::Getter,
    )
}

/// §B.2.2.3 `Object.prototype.__defineSetter__(P, setter)`.
fn define_setter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    define_legacy_accessor(
        machine,
        this,
        args,
        constructing,
        LegacyAccessorSlot::Setter,
    )
}

/// Shared body of §B.2.2.2 and §B.2.2.3: the receiver is boxed first, the
/// accessor is validated as callable before the key is coerced, and the whole
/// accessor descriptor (a single slot, non-enumerable, configurable) is
/// installed through ordinary `[[DefineOwnProperty]]` validation, so a
/// non-configurable existing property rejects the redefinition.
fn define_legacy_accessor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
    slot: LegacyAccessorSlot,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        match slot {
            LegacyAccessorSlot::Getter => "Object.prototype.__defineGetter__ is not a constructor",
            LegacyAccessorSlot::Setter => "Object.prototype.__defineSetter__ is not a constructor",
        },
    )?;
    let object = machine.value_to_object(this)?;
    let accessor = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(accessor)? {
        return Err(type_error(match slot {
            LegacyAccessorSlot::Getter => {
                "Object.prototype.__defineGetter__ requires a callable getter"
            }
            LegacyAccessorSlot::Setter => {
                "Object.prototype.__defineSetter__ requires a callable setter"
            }
        }));
    }
    let key = machine.observable_property_key(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let descriptor = Property::Accessor {
        getter: (slot == LegacyAccessorSlot::Getter).then_some(accessor),
        setter: (slot == LegacyAccessorSlot::Setter).then_some(accessor),
        enumerable: false,
        configurable: true,
    };
    machine.define_descriptor(object, key, descriptor)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

/// §B.2.2.4 `Object.prototype.__lookupGetter__(P)`.
fn lookup_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    lookup_legacy_accessor(
        machine,
        this,
        args,
        constructing,
        LegacyAccessorSlot::Getter,
    )
}

/// §B.2.2.5 `Object.prototype.__lookupSetter__(P)`.
fn lookup_setter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    lookup_legacy_accessor(
        machine,
        this,
        args,
        constructing,
        LegacyAccessorSlot::Setter,
    )
}

/// Shared body of §B.2.2.4 and §B.2.2.5: walk the receiver's prototype chain
/// and return the matching accessor slot of the first descriptor found. A
/// data property anywhere on the chain stops the search with `undefined`, as
/// does an exhausted chain.
fn lookup_legacy_accessor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
    slot: LegacyAccessorSlot,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        match slot {
            LegacyAccessorSlot::Getter => "Object.prototype.__lookupGetter__ is not a constructor",
            LegacyAccessorSlot::Setter => "Object.prototype.__lookupSetter__ is not a constructor",
        },
    )?;
    let object = machine.value_to_object(this)?;
    let key = machine.observable_property_key(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let mut current = Some(object);
    while let Some(object) = current {
        if let Some(descriptor) = machine.internal_get_own_property(object, &key)? {
            let accessor = match slot {
                LegacyAccessorSlot::Getter => descriptor.getter,
                LegacyAccessorSlot::Setter => descriptor.setter,
            };
            return Ok(BuiltinOutcome::Value(accessor.unwrap_or(Value::UNDEFINED)));
        }
        current = machine.internal_get_prototype_of(object)?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn install_string_annex_b<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.string_prototype();
    for (name, length, handler) in [
        ("anchor", 1, anchor::<H> as BuiltinHandler<H>),
        ("big", 0, big::<H>),
        ("blink", 0, blink::<H>),
        ("bold", 0, bold::<H>),
        ("fixed", 0, fixed::<H>),
        ("fontcolor", 1, fontcolor::<H>),
        ("fontsize", 1, fontsize::<H>),
        ("italics", 0, italics::<H>),
        ("link", 1, link::<H>),
        ("small", 0, small::<H>),
        ("strike", 0, strike::<H>),
        ("sub", 0, sub::<H>),
        ("sup", 0, sup::<H>),
        ("substr", 2, substr::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, prototype, name, function);
    }
    // §B.2.3: `trimLeft` is the same function object as `trimStart`, and
    // `trimRight` the same as `trimEnd`; clone the installed descriptors so
    // the identity relationship holds through the alias.
    for (alias, canonical) in [("trimLeft", "trimStart"), ("trimRight", "trimEnd")] {
        let property = clone_property(heap, atoms, prototype, canonical);
        define_property(heap, atoms, prototype, alias, property);
    }
}

fn install_regexp_compile<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
) {
    let method = install_function(heap, atoms, builtins, "compile", 1, regexp_compile::<H>);
    define_data(heap, atoms, builtins.regexp_prototype(), "compile", method);
}
const LEGACY_STATE_PRIVATE_NAME: &str = "RegExp legacy static state";
const CAPTURE_START_NAMES: [&str; 9] = [
    "capture1Start",
    "capture2Start",
    "capture3Start",
    "capture4Start",
    "capture5Start",
    "capture6Start",
    "capture7Start",
    "capture8Start",
    "capture9Start",
];
const CAPTURE_END_NAMES: [&str; 9] = [
    "capture1End",
    "capture2End",
    "capture3End",
    "capture4End",
    "capture5End",
    "capture6End",
    "capture7End",
    "capture8End",
    "capture9End",
];

fn hidden_data(value: Value) -> Property {
    Property::Data {
        value,
        writable: true,
        enumerable: false,
        configurable: false,
    }
}

fn reject_construction(constructing: bool, operation: &'static str) -> Result<(), EvalFailure> {
    if constructing {
        return Err(type_error(operation));
    }
    Ok(())
}
fn install_regexp_legacy_statics<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let constructor = globals
        .get(&EcmaString::encode("RegExp"))
        .copied()
        .expect("RegExp installs before Annex B");
    let empty = push(heap, HeapEntry::String(EcmaString::default()));
    let mut state_properties = PropertyMap::default();
    state_properties.insert(
        PropertyKey::Named(atoms.intern_str("input")),
        hidden_data(empty),
    );
    state_properties.insert(
        PropertyKey::Named(atoms.intern_str("matchInput")),
        hidden_data(empty),
    );
    for name in ["matchStart", "matchEnd", "lastParenStart", "lastParenEnd"] {
        state_properties.insert(
            PropertyKey::Named(atoms.intern_str(name)),
            hidden_data(crate::number_value(-1.0)),
        );
    }
    for name in CAPTURE_START_NAMES.into_iter().chain(CAPTURE_END_NAMES) {
        state_properties.insert(
            PropertyKey::Named(atoms.intern_str(name)),
            hidden_data(crate::number_value(-1.0)),
        );
    }
    let state = push(
        heap,
        HeapEntry::Object {
            properties: state_properties,
            prototype: None,
            boxed_primitive: None,
            extensible: false,
        },
    );
    let private_name = push(
        heap,
        HeapEntry::PrivateName {
            description: EcmaString::encode(LEGACY_STATE_PRIVATE_NAME),
        },
    );
    properties_of(heap, constructor).insert(
        PropertyKey::Private(heap_index(private_name) as u32),
        Property::Data {
            value: state,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );

    for (property, getter_name, getter, setter_name) in [
        (
            "input",
            "get input",
            legacy_input_get::<H> as BuiltinHandler<H>,
            "set input",
        ),
        ("$_", "get $_", legacy_input_get::<H>, "set $_"),
    ] {
        let getter = install_function(heap, atoms, builtins, getter_name, 0, getter);
        let setter = install_function(heap, atoms, builtins, setter_name, 1, legacy_input_set::<H>);
        define_property(
            heap,
            atoms,
            constructor,
            property,
            Property::Accessor {
                getter: Some(getter),
                setter: Some(setter),
                enumerable: false,
                configurable: true,
            },
        );
    }
    for (property, getter_name, getter) in [
        (
            "lastMatch",
            "get lastMatch",
            legacy_last_match_get::<H> as BuiltinHandler<H>,
        ),
        ("$&", "get $&", legacy_last_match_get::<H>),
        ("lastParen", "get lastParen", legacy_last_paren_get::<H>),
        ("$+", "get $+", legacy_last_paren_get::<H>),
        (
            "leftContext",
            "get leftContext",
            legacy_left_context_get::<H>,
        ),
        ("$`", "get $`", legacy_left_context_get::<H>),
        (
            "rightContext",
            "get rightContext",
            legacy_right_context_get::<H>,
        ),
        ("$'", "get $'", legacy_right_context_get::<H>),
        ("$1", "get $1", legacy_capture_1_get::<H>),
        ("$2", "get $2", legacy_capture_2_get::<H>),
        ("$3", "get $3", legacy_capture_3_get::<H>),
        ("$4", "get $4", legacy_capture_4_get::<H>),
        ("$5", "get $5", legacy_capture_5_get::<H>),
        ("$6", "get $6", legacy_capture_6_get::<H>),
        ("$7", "get $7", legacy_capture_7_get::<H>),
        ("$8", "get $8", legacy_capture_8_get::<H>),
        ("$9", "get $9", legacy_capture_9_get::<H>),
    ] {
        let getter = install_function(heap, atoms, builtins, getter_name, 0, getter);
        define_property(
            heap,
            atoms,
            constructor,
            property,
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }
}

#[derive(Clone, Copy)]
enum LegacyStatic {
    Input,
    LastMatch,
    LastParen,
    LeftContext,
    RightContext,
    Capture(usize),
}

fn regexp_constructor<H: Host>(machine: &Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .intrinsics
        .global("RegExp")
        .ok_or_else(|| type_error("RegExp constructor is unavailable"))
}

fn legacy_state(heap: &[HeapEntry], constructor: Value) -> Value {
    let index = heap_index(constructor);
    let HeapEntry::NativeFunction { properties, .. } = &heap[index] else {
        panic!("RegExp constructor must be a native function");
    };
    properties
        .iter()
        .find_map(|(key, property)| {
            let PropertyKey::Private(private_index) = key else {
                return None;
            };
            let Some(HeapEntry::PrivateName { description }) = heap.get(*private_index as usize)
            else {
                return None;
            };
            if !description.eq_ascii(LEGACY_STATE_PRIVATE_NAME) {
                return None;
            }
            match property {
                Property::Data { value, .. } => Some(*value),
                Property::Accessor { .. } => None,
            }
        })
        .expect("Annex B installs RegExp legacy state")
}

fn legacy_state_value(
    heap: &[HeapEntry],
    atoms: &crate::AtomTable,
    state: Value,
    name: &str,
) -> Value {
    let HeapEntry::Object { properties, .. } = &heap[heap_index(state)] else {
        panic!("RegExp legacy state must be an object");
    };
    match properties
        .get_ascii(atoms, name)
        .unwrap_or_else(|| panic!("RegExp legacy state contains {name}"))
    {
        Property::Data { value, .. } => *value,
        Property::Accessor { .. } => panic!("RegExp legacy state fields are data properties"),
    }
}

fn set_legacy_state_value(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    state: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(state)] else {
        panic!("RegExp legacy state must be an object");
    };
    properties.insert(
        PropertyKey::Named(atoms.intern_str(name)),
        hidden_data(value),
    );
}

fn checked_legacy_state<H: Host>(
    machine: &Machine<'_, H>,
    this: Value,
) -> Result<Value, EvalFailure> {
    let constructor = regexp_constructor(machine)?;
    if this != constructor {
        return Err(type_error(
            "RegExp legacy static accessor called on incompatible receiver",
        ));
    }
    Ok(legacy_state(&machine.heap, constructor))
}

fn stored_index(
    heap: &[HeapEntry],
    atoms: &crate::AtomTable,
    state: Value,
    name: &str,
) -> Option<usize> {
    let number = super::value_number(legacy_state_value(heap, atoms, state, name));
    (number >= 0.0).then_some(number as usize)
}

fn legacy_static_get<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    kind: LegacyStatic,
) -> Result<BuiltinOutcome, EvalFailure> {
    let state = checked_legacy_state(machine, this)?;
    let input_value = legacy_state_value(
        &machine.heap,
        &machine.atoms,
        state,
        if matches!(kind, LegacyStatic::Input) {
            "input"
        } else {
            "matchInput"
        },
    );
    if matches!(kind, LegacyStatic::Input) {
        return Ok(BuiltinOutcome::Value(input_value));
    }
    let input = machine
        .string_value(input_value)
        .expect("RegExp legacy input is a string");
    let range =
        match kind {
            LegacyStatic::Input => unreachable!("handled above"),
            LegacyStatic::LastMatch => {
                stored_index(&machine.heap, &machine.atoms, state, "matchStart").zip(stored_index(
                    &machine.heap,
                    &machine.atoms,
                    state,
                    "matchEnd",
                ))
            }
            LegacyStatic::LastParen => {
                stored_index(&machine.heap, &machine.atoms, state, "lastParenStart").zip(
                    stored_index(&machine.heap, &machine.atoms, state, "lastParenEnd"),
                )
            }
            LegacyStatic::LeftContext => {
                stored_index(&machine.heap, &machine.atoms, state, "matchStart").map(|end| (0, end))
            }
            LegacyStatic::RightContext => {
                stored_index(&machine.heap, &machine.atoms, state, "matchEnd")
                    .map(|start| (start, input.len_units()))
            }
            LegacyStatic::Capture(index) => stored_index(
                &machine.heap,
                &machine.atoms,
                state,
                CAPTURE_START_NAMES[index],
            )
            .zip(stored_index(
                &machine.heap,
                &machine.atoms,
                state,
                CAPTURE_END_NAMES[index],
            )),
        };
    let result = range
        .and_then(|(start, end)| input.slice_units(start..end))
        .unwrap_or_default();
    Ok(BuiltinOutcome::Value(allocate_string(machine, result)?))
}

fn legacy_input_get<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "RegExp legacy getter is not a constructor")?;
    legacy_static_get(machine, this, LegacyStatic::Input)
}

fn legacy_input_set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "RegExp input setter is not a constructor")?;
    let state = checked_legacy_state(machine, this)?;
    let input =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let input = allocate_string(machine, input)?;
    set_legacy_state_value(&mut machine.heap, &mut machine.atoms, state, "input", input);
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

macro_rules! legacy_static_getter {
    ($name:ident, $kind:expr) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            reject_construction(constructing, "RegExp legacy getter is not a constructor")?;
            legacy_static_get(machine, this, $kind)
        }
    };
}

legacy_static_getter!(legacy_last_match_get, LegacyStatic::LastMatch);
legacy_static_getter!(legacy_last_paren_get, LegacyStatic::LastParen);
legacy_static_getter!(legacy_left_context_get, LegacyStatic::LeftContext);
legacy_static_getter!(legacy_right_context_get, LegacyStatic::RightContext);
legacy_static_getter!(legacy_capture_1_get, LegacyStatic::Capture(0));
legacy_static_getter!(legacy_capture_2_get, LegacyStatic::Capture(1));
legacy_static_getter!(legacy_capture_3_get, LegacyStatic::Capture(2));
legacy_static_getter!(legacy_capture_4_get, LegacyStatic::Capture(3));
legacy_static_getter!(legacy_capture_5_get, LegacyStatic::Capture(4));
legacy_static_getter!(legacy_capture_6_get, LegacyStatic::Capture(5));
legacy_static_getter!(legacy_capture_7_get, LegacyStatic::Capture(6));
legacy_static_getter!(legacy_capture_8_get, LegacyStatic::Capture(7));
legacy_static_getter!(legacy_capture_9_get, LegacyStatic::Capture(8));

fn store_range(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    state: Value,
    start_name: &str,
    end_name: &str,
    range: Option<&std::ops::Range<usize>>,
) {
    let (start, end) = range.map_or((-1.0, -1.0), |range| (range.start as f64, range.end as f64));
    set_legacy_state_value(heap, atoms, state, start_name, crate::number_value(start));
    set_legacy_state_value(heap, atoms, state, end_name, crate::number_value(end));
}

/// Records the successful match state used by the Annex B RegExp constructor
/// accessors. The canonical RegExp executor must call this once for every
/// successful built-in match, after matching and before returning to user code.
pub(super) fn record_legacy_match<H: Host>(
    machine: &mut Machine<'_, H>,
    input: &EcmaString,
    matched: &Match,
) -> Result<(), EvalFailure> {
    let constructor = regexp_constructor(machine)?;
    let state = legacy_state(&machine.heap, constructor);
    let input_value = allocate_string(machine, input.clone())?;
    set_legacy_state_value(
        &mut machine.heap,
        &mut machine.atoms,
        state,
        "input",
        input_value,
    );
    set_legacy_state_value(
        &mut machine.heap,
        &mut machine.atoms,
        state,
        "matchInput",
        input_value,
    );
    store_range(
        &mut machine.heap,
        &mut machine.atoms,
        state,
        "matchStart",
        "matchEnd",
        Some(&matched.range),
    );
    let last_paren = matched
        .captures
        .iter()
        .skip(1)
        .rev()
        .find_map(Option::as_ref);
    store_range(
        &mut machine.heap,
        &mut machine.atoms,
        state,
        "lastParenStart",
        "lastParenEnd",
        last_paren,
    );
    for index in 0..9 {
        store_range(
            &mut machine.heap,
            &mut machine.atoms,
            state,
            CAPTURE_START_NAMES[index],
            CAPTURE_END_NAMES[index],
            matched.captures.get(index + 1).and_then(Option::as_ref),
        );
    }
    Ok(())
}

/// Returns a mutable view of the named-property map of an intrinsic that has
/// one, mirroring the target kinds accepted by `define_data`.
fn properties_of(heap: &mut [HeapEntry], object: Value) -> &mut PropertyMap {
    let index = heap_index(object);
    match &mut heap[index] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::Function { properties, .. }
        | HeapEntry::Script { properties, .. }
        | HeapEntry::NativeFunction { properties, .. }
        | HeapEntry::RegExp { properties, .. }
        | HeapEntry::Date { properties, .. }
        | HeapEntry::Temporal { properties, .. }
        | HeapEntry::Intl { properties, .. } => properties,
        _ => panic!("Annex B property target must be an ordinary object"),
    }
}

fn define_property(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    object: Value,
    name: &str,
    property: Property,
) {
    properties_of(heap, object).insert(PropertyKey::Named(atoms.intern_str(name)), property);
}

fn clone_property(
    heap: &[HeapEntry],
    atoms: &crate::AtomTable,
    object: Value,
    name: &str,
) -> Property {
    let index = heap_index(object);
    let properties = match &heap[index] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::Function { properties, .. }
        | HeapEntry::Script { properties, .. }
        | HeapEntry::NativeFunction { properties, .. }
        | HeapEntry::RegExp { properties, .. }
        | HeapEntry::Date { properties, .. }
        | HeapEntry::Temporal { properties, .. }
        | HeapEntry::Intl { properties, .. } => properties,
        _ => panic!("Annex B property source must be an ordinary object"),
    };
    properties
        .get_ascii(atoms, name)
        .unwrap_or_else(|| panic!("{name} must be installed before the Annex B surface"))
        .clone()
}

/// §B.2.3 CreateHTML shared algorithm selection: coerces the receiver string
/// first and rejects nullish receivers before any argument coercion.
fn coerce_this_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    operation: &'static str,
) -> Result<EcmaString, EvalFailure> {
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error(operation));
    }
    machine.coerce_string_observable(this)
}

/// §B.2.3.2.1 CreateHTML ( value, tag, attribute, value ): the attribute
/// value is coerced after the receiver content, and only `"` is escaped.
fn create_html<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    tag: &'static str,
    attribute: &'static str,
) -> Result<BuiltinOutcome, EvalFailure> {
    let content = coerce_this_string(
        machine,
        this,
        "String HTML wrapper method called on null or undefined",
    )?;
    let mut output = EcmaStringBuilder::with_capacity(content.len_units() + 2 * tag.len() + 8);
    output.push_utf8("<");
    output.push_utf8(tag);
    if !attribute.is_empty() {
        let value =
            machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
        output.push_utf8(" ");
        output.push_utf8(attribute);
        output.push_utf8("=\"");
        for &unit in value.as_units() {
            if unit == u16::from(b'"') {
                output.push_utf8("&quot;");
            } else {
                output.push_unit(unit);
            }
        }
        output.push_unit(u16::from(b'"'));
    }
    output.push_utf8(">");
    for &unit in content.as_units() {
        output.push_unit(unit);
    }
    output.push_utf8("</");
    output.push_utf8(tag);
    output.push_utf8(">");
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

macro_rules! html_wrapper {
    ($name:ident, $tag:literal, $attribute:literal) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            args: &[Value],
            constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            reject_construction(
                constructing,
                concat!(
                    "String.prototype.",
                    stringify!($name),
                    " is not a constructor"
                ),
            )?;
            create_html(machine, this, args, $tag, $attribute)
        }
    };
}

html_wrapper!(anchor, "a", "name");
html_wrapper!(big, "big", "");
html_wrapper!(blink, "blink", "");
html_wrapper!(bold, "b", "");
html_wrapper!(fixed, "tt", "");
html_wrapper!(fontcolor, "font", "color");
html_wrapper!(fontsize, "font", "size");
html_wrapper!(italics, "i", "");
html_wrapper!(link, "a", "href");
html_wrapper!(small, "small", "");
html_wrapper!(strike, "strike", "");
html_wrapper!(sub, "sub", "");
html_wrapper!(sup, "sup", "");

/// §B.2.3.1 `String.prototype.substr(start, length)` (LegacySubstr).
fn substr<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "String.prototype.substr is not a constructor")?;
    let text = coerce_this_string(
        machine,
        this,
        "String.prototype.substr called on null or undefined",
    )?;
    let size = text.len_units() as f64;
    let start_number =
        machine.coerce_number_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let raw_start = to_integer_or_infinity(machine, start_number)?;
    let start = if raw_start == f64::NEG_INFINITY {
        0.0
    } else if raw_start < 0.0 {
        (size + raw_start).max(0.0)
    } else {
        raw_start
    };
    let raw_length = match args.get(1).copied() {
        Some(value) if value != Value::UNDEFINED => {
            let number = machine.coerce_number_observable(value)?;
            to_integer_or_infinity(machine, number)?
        }
        _ => size,
    };
    if start > size {
        return Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::default(),
        )?));
    }
    let result_length = raw_length.clamp(0.0, size - start);
    let start_index = start as usize;
    let length = result_length as usize;
    let result = text
        .slice_units(start_index..start_index + length)
        .expect("substr bounds are clamped to the string");
    Ok(BuiltinOutcome::Value(allocate_string(machine, result)?))
}

/// §B.2.2.1.1 `get Object.prototype.__proto__`.
fn proto_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        "Object.prototype.__proto__ getter is not a constructor",
    )?;
    let object = machine.value_to_object(this)?;
    Ok(BuiltinOutcome::Value(
        machine
            .internal_get_prototype_of(object)?
            .unwrap_or(Value::NULL),
    ))
}

fn is_annex_object<H: Host>(machine: &Machine<'_, H>, value: Value) -> Result<bool, EvalFailure> {
    let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
        return Ok(false);
    };
    Ok(machine.is_object(value)
        && !matches!(
            machine.heap[index],
            HeapEntry::Symbol { .. } | HeapEntry::PrivateName { .. }
        ))
}

/// §B.2.2.1.2 `set Object.prototype.__proto__`: a non-Object non-null value is
/// a silent no-op; only then does the ordinary `SetPrototypeOf` run.
fn proto_setter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        "Object.prototype.__proto__ setter is not a constructor",
    )?;
    if matches!(this.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Err(type_error(
            "Object.prototype.__proto__ setter called on null or undefined",
        ));
    }
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    if value != Value::NULL && !is_annex_object(machine, value)? {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let object = machine.value_to_object(this)?;
    let prototype = (value != Value::NULL).then_some(value);
    if machine.internal_set_prototype_of(object, prototype)? {
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    } else {
        Err(type_error("Object.prototype.__proto__ setter failed"))
    }
}

/// §B.2.5.1 `RegExp.prototype.compile(pattern, flags)`.
fn regexp_compile<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        "RegExp.prototype.compile is not a constructor",
    )?;
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "RegExp.prototype.compile called on incompatible receiver",
        ));
    };
    if !matches!(machine.heap[index], HeapEntry::RegExp { .. }) {
        return Err(type_error(
            "RegExp.prototype.compile called on incompatible receiver",
        ));
    }
    let pattern_arg = args.first().copied().unwrap_or(Value::UNDEFINED);
    let flags_arg = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let (pattern, flags) = match super::regexp::regexp_parts(machine, pattern_arg) {
        Some((source, original_flags)) => {
            if flags_arg != Value::UNDEFINED {
                return Err(type_error(
                    "RegExp.prototype.compile flags must be undefined when pattern is a RegExp",
                ));
            }
            (source, original_flags)
        }
        None => (
            if pattern_arg == Value::UNDEFINED {
                EcmaString::default()
            } else {
                machine.coerce_string_observable(pattern_arg)?
            },
            if flags_arg == Value::UNDEFINED {
                EcmaString::default()
            } else {
                machine.coerce_string_observable(flags_arg)?
            },
        ),
    };
    super::regexp::compile(machine, &pattern, &flags)?;
    let flags = super::regexp::canonical_regexp_flags(&flags);
    let HeapEntry::RegExp {
        pattern: source_slot,
        flags: flags_slot,
        ..
    } = &mut machine.heap[index]
    else {
        unreachable!("RegExp brand was checked above");
    };
    *source_slot = pattern;
    *flags_slot = flags;
    // RegExpInitialize performs `Set(obj, "lastIndex", 0, true)` after the
    // matcher state is replaced, so a read-only `lastIndex` throws while the
    // recompiled pattern remains installed.
    reset_last_index(machine, this)?;
    Ok(BuiltinOutcome::Value(this))
}

/// The observable `Set(obj, "lastIndex", 0)` performed by RegExpInitialize:
/// a writable data slot is rewritten in place, an accessor runs its setter,
/// and read-only or setterless descriptors throw.
fn reset_last_index<H: Host>(
    machine: &mut Machine<'_, H>,
    regexp: Value,
) -> Result<(), EvalFailure> {
    let key = PropertyKey::Named(machine.intern_str("lastIndex"));
    let descriptor = {
        let properties = properties_of(&mut machine.heap, regexp);
        properties.get(&key).cloned()
    };
    if let Some(descriptor) = descriptor {
        match descriptor {
            Property::Data { writable: true, .. } => {}
            Property::Data { .. } => {
                return Err(type_error("set lastIndex of RegExp"));
            }
            Property::Accessor {
                setter: Some(setter),
                ..
            } => {
                machine.call_value(setter, regexp, &[Value::int32(0)])?;
                return Ok(());
            }
            Property::Accessor { .. } => {
                return Err(type_error("set read-only lastIndex of RegExp"));
            }
        }
    }
    machine.set_data_property(regexp, "lastIndex", Value::int32(0))
}

#[cfg(test)]
mod tests {
    use super::super::{
        test_support::{blank_program, ordinary_object},
        value_number,
    };
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};
    use std::sync::atomic::{AtomicBool, Ordering};

    struct ControlledHost {
        zone: &'static str,
    }

    impl Host for ControlledHost {
        fn env(&self, name: &str) -> Option<&str> {
            (name == "TZ").then_some(self.zone)
        }

        fn now_ms(&mut self) -> u64 {
            1_704_067_200_123
        }
    }

    fn machine<'a>(
        module: &'a bamts_bytecode::Program<bamts_bytecode::Verified>,
        host: &'a mut ControlledHost,
    ) -> Machine<'a, ControlledHost> {
        Machine::new(module, host, Limits::default())
    }

    fn text(machine: &mut Machine<'_, ControlledHost>, source: &str) -> Value {
        allocate_string(machine, EcmaString::encode(source)).expect("string allocation succeeds")
    }

    fn call(
        machine: &mut Machine<'_, ControlledHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let function = machine.get_named_property(receiver, name)?;
        machine.call_value(function, receiver, args)
    }

    fn call_string_method(
        machine: &mut Machine<'_, ControlledHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let prototype = string_prototype(machine);
        let function = machine.get_named_property(prototype, name)?;
        machine.call_value(function, receiver, args)
    }

    fn string_prototype(machine: &Machine<'_, ControlledHost>) -> Value {
        machine.intrinsics.builtins.string_prototype()
    }

    fn native(
        machine: &mut Machine<'_, ControlledHost>,
        name: &'static str,
        length: u32,
        handler: BuiltinHandler<ControlledHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, id, name, length)
    }

    fn assert_type_error(result: Result<Value, EvalFailure>) {
        assert!(
            matches!(
                result,
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ),
            "expected a TypeError, got {result:?}"
        );
    }

    fn assert_text_of(machine: &mut Machine<'_, ControlledHost>, value: Value, expected: &str) {
        let text = machine.string_value(value).expect("value is a string");
        assert!(
            text.eq_ascii(expected),
            "expected {expected:?}, got {:?}",
            text.to_utf8_lossy()
        );
    }

    fn own_data_property(
        machine: &mut Machine<'_, ControlledHost>,
        object: Value,
        name: &str,
    ) -> Property {
        let key = PropertyKey::Named(machine.intern_str(name));
        machine
            .own_descriptor(object, &key)
            .expect("descriptor lookup succeeds")
            .unwrap_or_else(|| panic!("{name} is installed"))
    }

    #[test]
    fn installed_surface_has_spec_names_lengths_and_descriptors() {
        let module = blank_program("<annex b surface>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let prototype = string_prototype(&machine);
        for (name, length) in [
            ("anchor", 1),
            ("big", 0),
            ("blink", 0),
            ("bold", 0),
            ("fixed", 0),
            ("fontcolor", 1),
            ("fontsize", 1),
            ("italics", 0),
            ("link", 1),
            ("small", 0),
            ("strike", 0),
            ("sub", 0),
            ("sup", 0),
            ("substr", 2),
            ("trimLeft", 0),
            ("trimRight", 0),
        ] {
            let Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            } = own_data_property(&mut machine, prototype, name)
            else {
                panic!("{name} is a writable, non-enumerable, configurable data property");
            };
            let length_value = machine.get_named_property(value, "length").unwrap();
            assert_eq!(
                value_number(length_value),
                f64::from(length),
                "{name} length"
            );
            let name_value = machine.get_named_property(value, "name").unwrap();
            let expected_name = match name {
                "trimLeft" => "trimStart",
                "trimRight" => "trimEnd",
                _ => name,
            };
            assert_text_of(&mut machine, name_value, expected_name);
        }
        let regexp_prototype = machine.intrinsics.builtins.regexp_prototype();
        let Property::Data {
            value: compile,
            writable: true,
            enumerable: false,
            configurable: true,
        } = own_data_property(&mut machine, regexp_prototype, "compile")
        else {
            panic!("compile is a writable, non-enumerable, configurable data property");
        };
        let length = machine.get_named_property(compile, "length").unwrap();
        assert_eq!(value_number(length), 1.0);
    }

    #[test]
    fn proto_accessor_is_a_non_enumerable_configurable_accessor() {
        let module = blank_program("<__proto__ descriptor>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        let proto_key = PropertyKey::Named(machine.intern_str("__proto__"));
        let Property::Accessor {
            getter: Some(getter),
            setter: Some(setter),
            enumerable: false,
            configurable: true,
        } = machine
            .own_descriptor(object_prototype, &proto_key)
            .expect("descriptor lookup succeeds")
            .expect("__proto__ accessor is installed")
        else {
            panic!("__proto__ is a non-enumerable, configurable accessor");
        };
        let getter_name = machine.get_named_property(getter, "name").unwrap();
        assert_text_of(&mut machine, getter_name, "get __proto__");
        let setter_name = machine.get_named_property(setter, "name").unwrap();
        assert_text_of(&mut machine, setter_name, "set __proto__");
    }

    #[test]
    fn html_wrappers_render_exact_output() {
        let module = blank_program("<html wrappers>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let prototype = string_prototype(&machine);
        let underscore = text(&mut machine, "_");
        let angle = text(&mut machine, "<");
        let b = text(&mut machine, "b");
        let anchored_underscore =
            call_string_method(&mut machine, underscore, "anchor", &[b]).unwrap();
        assert_text_of(&mut machine, anchored_underscore, "<a name=\"b\">_</a>");
        let anchored_angle = call_string_method(&mut machine, angle, "anchor", &[angle]).unwrap();
        assert_text_of(&mut machine, anchored_angle, "<a name=\"<\"><</a>");
        let red = text(&mut machine, "red");
        let red_underscore =
            call_string_method(&mut machine, underscore, "fontcolor", &[red]).unwrap();
        assert_text_of(&mut machine, red_underscore, "<font color=\"red\">_</font>");
        let size = text(&mut machine, "3");
        let sized_underscore =
            call_string_method(&mut machine, underscore, "fontsize", &[size]).unwrap();
        assert_text_of(&mut machine, sized_underscore, "<font size=\"3\">_</font>");
        let url = text(&mut machine, "x://y");
        let linked_underscore =
            call_string_method(&mut machine, underscore, "link", &[url]).unwrap();
        assert_text_of(&mut machine, linked_underscore, "<a href=\"x://y\">_</a>");
        for (method, expected) in [
            ("big", "<big>_</big>"),
            ("blink", "<blink>_</blink>"),
            ("bold", "<b>_</b>"),
            ("fixed", "<tt>_</tt>"),
            ("italics", "<i>_</i>"),
            ("small", "<small>_</small>"),
            ("strike", "<strike>_</strike>"),
            ("sub", "<sub>_</sub>"),
            ("sup", "<sup>_</sup>"),
        ] {
            let wrapped = call_string_method(&mut machine, underscore, method, &[]).unwrap();
            assert_text_of(&mut machine, wrapped, expected);
        }
        let _ = prototype;
    }

    #[test]
    fn html_wrappers_escape_only_quotes_in_attributes() {
        let module = blank_program("<html escaping>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let prototype = string_prototype(&machine);
        let subject = text(&mut machine, "x");
        let attribute = text(&mut machine, "&\"<&quot;\"");
        let escaped = call_string_method(&mut machine, subject, "anchor", &[attribute]).unwrap();
        assert_text_of(
            &mut machine,
            escaped,
            "<a name=\"&&quot;<&quot;&quot;\">x</a>",
        );
        let numeric =
            call_string_method(&mut machine, subject, "anchor", &[Value::int32(0x2A)]).unwrap();
        assert_text_of(&mut machine, numeric, "<a name=\"42\">x</a>");
        let _ = prototype;
    }

    static THIS_ORDER: AtomicBool = AtomicBool::new(false);
    static ATTR_ORDER: AtomicBool = AtomicBool::new(false);

    fn this_to_string(
        machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert!(
            !ATTR_ORDER.swap(true, Ordering::SeqCst),
            "attribute must not be coerced before the receiver"
        );
        THIS_ORDER.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("S"),
        )?))
    }

    fn attribute_to_string(
        machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert!(
            THIS_ORDER.load(Ordering::SeqCst),
            "receiver coercion runs first"
        );
        ATTR_ORDER.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("A"),
        )?))
    }

    fn coerced_object(
        machine: &mut Machine<'_, ControlledHost>,
        handler: BuiltinHandler<ControlledHost>,
    ) -> Value {
        let object = ordinary_object(machine);
        let function = native(machine, "toString", 0, handler);
        machine
            .set_data_property(object, "toString", function)
            .expect("toString installs on the probe object");
        object
    }

    #[test]
    fn html_wrappers_coerce_receiver_before_attribute() {
        THIS_ORDER.store(false, Ordering::SeqCst);
        ATTR_ORDER.store(false, Ordering::SeqCst);
        let module = blank_program("<html coercion order>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let this = coerced_object(&mut machine, this_to_string);
        let attribute = coerced_object(&mut machine, attribute_to_string);
        let wrapped = call_string_method(&mut machine, this, "anchor", &[attribute]).unwrap();
        assert_text_of(&mut machine, wrapped, "<a name=\"A\">S</a>");
        assert!(THIS_ORDER.load(Ordering::SeqCst));
        assert!(ATTR_ORDER.load(Ordering::SeqCst));
    }

    static ATTRIBUTE_TRIED: AtomicBool = AtomicBool::new(false);

    fn attribute_probe(
        machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        ATTRIBUTE_TRIED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("probe"),
        )?))
    }

    #[test]
    fn html_wrappers_reject_nullish_and_symbol_receivers_before_attribute_coercion() {
        ATTRIBUTE_TRIED.store(false, Ordering::SeqCst);
        let module = blank_program("<html errors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let attribute = coerced_object(&mut machine, attribute_probe);
        assert_type_error(call_string_method(
            &mut machine,
            Value::UNDEFINED,
            "anchor",
            &[attribute],
        ));
        assert_type_error(call_string_method(
            &mut machine,
            Value::NULL,
            "fontcolor",
            &[attribute],
        ));
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert_type_error(call_string_method(
            &mut machine,
            symbol,
            "link",
            &[attribute],
        ));
        assert!(
            !ATTRIBUTE_TRIED.load(Ordering::SeqCst),
            "a failing receiver coercion must precede attribute coercion"
        );
        let receiver = text(&mut machine, "x");
        let ignored = call_string_method(&mut machine, receiver, "big", &[attribute]).unwrap();
        assert_text_of(&mut machine, ignored, "<big>x</big>");
        assert!(
            !ATTRIBUTE_TRIED.load(Ordering::SeqCst),
            "attribute-less wrappers must not coerce ignored arguments"
        );
        assert_type_error(call_string_method(
            &mut machine,
            receiver,
            "anchor",
            &[symbol],
        ));
    }

    #[test]
    fn html_wrappers_coerce_bigint_content_and_attributes() {
        let module = blank_program("<html bigint>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let bigint = machine
            .allocate(HeapEntry::BigInt("10".to_owned()))
            .expect("BigInt allocation succeeds");
        let wrapped = call_string_method(&mut machine, bigint, "bold", &[]).unwrap();
        assert_text_of(&mut machine, wrapped, "<b>10</b>");
        let bigint2 = machine
            .allocate(HeapEntry::BigInt("8".to_owned()))
            .expect("BigInt allocation succeeds");
        let receiver = text(&mut machine, "x");
        let wrapped = call_string_method(&mut machine, receiver, "fontsize", &[bigint2]).unwrap();
        assert_text_of(&mut machine, wrapped, "<font size=\"8\">x</font>");
    }

    #[test]
    fn trim_aliases_are_the_same_function_objects() {
        let module = blank_program("<trim aliases>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let prototype = string_prototype(&machine);
        for (alias, canonical) in [("trimLeft", "trimStart"), ("trimRight", "trimEnd")] {
            assert_eq!(
                machine.get_named_property(prototype, alias).unwrap(),
                machine.get_named_property(prototype, canonical).unwrap(),
                "{alias} is the same function object as {canonical}"
            );
        }
    }

    #[test]
    fn substr_applies_legacy_start_and_length_rules_on_code_units() {
        let module = blank_program("<substr>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let abc = text(&mut machine, "abc");
        for (args, expected) in [
            (&[][..], "abc"),
            (&[Value::int32(0)][..], "abc"),
            (&[Value::int32(1)][..], "bc"),
            (&[Value::int32(2)][..], "c"),
            (&[crate::number_value(-1.0)][..], "c"),
            (&[crate::number_value(-2.0)][..], "bc"),
            (&[crate::number_value(-3.0)][..], "abc"),
            (&[crate::number_value(-4.0)][..], "abc"),
            (&[crate::number_value(-1.1)][..], "c"),
            (&[Value::number(f64::NEG_INFINITY)][..], "abc"),
            (&[Value::number(f64::INFINITY)][..], ""),
            (&[Value::int32(1), Value::int32(2)][..], "bc"),
            (&[Value::int32(1), crate::number_value(-1.0)][..], ""),
            (&[Value::int32(0), Value::number(f64::NAN)][..], ""),
            (&[Value::int32(1), Value::UNDEFINED][..], "bc"),
            (&[crate::number_value(-100.0), Value::int32(2)][..], "ab"),
        ] {
            let result = call_string_method(&mut machine, abc, "substr", args).unwrap();
            assert_text_of(&mut machine, result, expected);
        }
        let surrogate = machine
            .allocate(HeapEntry::String(EcmaString::from_units(&[
                0x0068, 0xd801, 0xdc37,
            ])))
            .expect("string allocation succeeds");
        let value =
            call_string_method(&mut machine, surrogate, "substr", &[Value::int32(1)]).unwrap();
        let result = machine
            .string_value(value)
            .expect("substr result is a string");
        assert_eq!(result.as_units(), &[0xd801, 0xdc37]);
        let value = call_string_method(
            &mut machine,
            surrogate,
            "substr",
            &[Value::int32(2), Value::int32(1)],
        )
        .unwrap();
        let result = machine
            .string_value(value)
            .expect("substr result is a string");
        assert_eq!(result.as_units(), &[0xdc37]);
    }

    static SUBSTR_STEP: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    fn substr_value_of(
        machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let step = SUBSTR_STEP.fetch_add(1, Ordering::SeqCst);
        assert_eq!(step, 0, "receiver coerces before start and length");
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("abc"),
        )?))
    }

    fn start_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let step = SUBSTR_STEP.fetch_add(1, Ordering::SeqCst);
        assert_eq!(step, 1, "start coerces after the receiver");
        Ok(BuiltinOutcome::Value(crate::number_value(-1.0)))
    }

    fn length_value_of(
        _machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let step = SUBSTR_STEP.fetch_add(1, Ordering::SeqCst);
        assert_eq!(step, 2, "length coerces after start");
        Ok(BuiltinOutcome::Value(Value::int32(1)))
    }

    #[test]
    fn substr_coerces_receiver_then_start_then_length() {
        SUBSTR_STEP.store(0, Ordering::SeqCst);
        let module = blank_program("<substr coercion>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let this = coerced_object(&mut machine, substr_value_of);
        let start = coerced_object(&mut machine, start_value_of);
        let length = coerced_object(&mut machine, length_value_of);
        let result = call_string_method(&mut machine, this, "substr", &[start, length]).unwrap();
        assert_text_of(&mut machine, result, "c");
        assert_eq!(SUBSTR_STEP.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn substr_rejects_nullish_symbol_and_bigint_inputs_with_typed_errors() {
        let module = blank_program("<substr errors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        assert_type_error(call_string_method(
            &mut machine,
            Value::UNDEFINED,
            "substr",
            &[],
        ));
        assert_type_error(call_string_method(&mut machine, Value::NULL, "substr", &[]));
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert_type_error(call_string_method(&mut machine, symbol, "substr", &[]));
        let bigint = machine
            .allocate(HeapEntry::BigInt("3".to_owned()))
            .expect("BigInt allocation succeeds");
        let receiver = text(&mut machine, "abc");
        assert_type_error(call_string_method(
            &mut machine,
            receiver,
            "substr",
            &[bigint],
        ));
        let this = text(&mut machine, "abc");
        assert_type_error(call_string_method(&mut machine, this, "substr", &[symbol]));
    }

    #[test]
    fn proto_getter_follows_prototypes_and_wraps_primitive_receivers() {
        let module = blank_program("<__proto__ get>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let object = ordinary_object(&mut machine);
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        assert_eq!(
            call(&mut machine, object, "__proto__", &[]).unwrap_or_else(|_| {
                let getter = proto_getter_function(&mut machine);
                machine.call_value(getter, object, &[]).unwrap()
            }),
            object_prototype
        );
        let getter = proto_getter_function(&mut machine);
        let null = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .expect("object allocation succeeds");
        assert_eq!(machine.call_value(getter, null, &[]).unwrap(), Value::NULL);
        assert_eq!(
            machine.call_value(getter, Value::int32(5), &[]).unwrap(),
            machine.intrinsics.number_prototype
        );
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert_eq!(
            machine.call_value(getter, symbol, &[]).unwrap(),
            machine.intrinsics.builtins.symbol_prototype()
        );
    }

    fn proto_getter_function(machine: &mut Machine<'_, ControlledHost>) -> Value {
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        let proto_key = PropertyKey::Named(machine.intern_str("__proto__"));
        let Property::Accessor {
            getter: Some(getter),
            ..
        } = machine
            .own_descriptor(object_prototype, &proto_key)
            .expect("descriptor lookup succeeds")
            .expect("__proto__ accessor is installed")
        else {
            panic!("__proto__ has a getter");
        };
        getter
    }

    fn proto_setter_function(machine: &mut Machine<'_, ControlledHost>) -> Value {
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        let proto_key = PropertyKey::Named(machine.intern_str("__proto__"));
        let Property::Accessor {
            setter: Some(setter),
            ..
        } = machine
            .own_descriptor(object_prototype, &proto_key)
            .expect("descriptor lookup succeeds")
            .expect("__proto__ accessor is installed")
        else {
            panic!("__proto__ has a setter");
        };
        setter
    }

    fn process_env_and_timeout(
        machine: &mut Machine<'_, ControlledHost>,
    ) -> [(&'static str, Value); 2] {
        let prototype = Some(machine.intrinsics.builtins.object_prototype());
        let process_env = machine
            .allocate(HeapEntry::ProcessEnv {
                prototype,
                extensible: true,
            })
            .expect("ProcessEnv allocation succeeds");
        let timeout = machine
            .allocate(HeapEntry::Timeout {
                id: 1,
                generation: 1,
                properties: PropertyMap::default(),
                prototype,
                extensible: true,
            })
            .expect("Timeout allocation succeeds");
        [("ProcessEnv", process_env), ("Timeout", timeout)]
    }
    fn make_non_extensible(machine: &mut Machine<'_, ControlledHost>, object: Value) {
        let index = machine.runtime_slot(object).unwrap().unwrap();
        let extensible = match &mut machine.heap[index] {
            HeapEntry::Object { extensible, .. }
            | HeapEntry::ProcessEnv { extensible, .. }
            | HeapEntry::Timeout { extensible, .. } => extensible,
            _ => panic!("fixture only freezes ordinary Annex B targets"),
        };
        *extensible = false;
    }

    #[test]
    fn proto_setter_rejects_nullish_receivers_and_noops_on_primitive_values() {
        let module = blank_program("<__proto__ set guards>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        assert!(matches!(
            machine.call_value(setter, Value::UNDEFINED, &[Value::NULL]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.call_value(setter, Value::NULL, &[Value::NULL]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let object = ordinary_object(&mut machine);
        let before = machine.internal_get_prototype_of(object).unwrap();
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        for value in [
            Value::UNDEFINED,
            Value::int32(5),
            Value::number(f64::NAN),
            symbol,
        ] {
            assert_eq!(
                machine.call_value(setter, object, &[value]).unwrap(),
                Value::UNDEFINED,
                "non-Object non-null values are a silent no-op"
            );
            assert_eq!(
                machine.internal_get_prototype_of(object).unwrap(),
                before,
                "a no-op leaves the prototype untouched"
            );
        }
        // Primitive receivers are boxed and the box absorbs the write.
        let proto = ordinary_object(&mut machine);
        assert_eq!(
            machine
                .call_value(setter, Value::int32(5), &[proto])
                .unwrap(),
            Value::UNDEFINED
        );
    }

    #[test]
    fn proto_setter_reprototypes_and_null_clears_the_chain() {
        let module = blank_program("<__proto__ set>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let object = ordinary_object(&mut machine);
        let parent = ordinary_object(&mut machine);
        assert_eq!(
            machine.call_value(setter, object, &[parent]).unwrap(),
            Value::UNDEFINED
        );
        assert_eq!(
            machine.internal_get_prototype_of(object).unwrap(),
            Some(parent)
        );
        assert_eq!(
            machine.call_value(setter, object, &[Value::NULL]).unwrap(),
            Value::UNDEFINED
        );
        assert_eq!(machine.internal_get_prototype_of(object).unwrap(), None);
        // Re-setting the current prototype is a no-op success.
        let kept = ordinary_object(&mut machine);
        assert_eq!(
            machine.call_value(setter, object, &[kept]).unwrap(),
            Value::UNDEFINED
        );
        assert_eq!(
            machine.call_value(setter, object, &[kept]).unwrap(),
            Value::UNDEFINED
        );
    }

    #[test]
    fn proto_setter_detects_direct_and_indirect_cycles() {
        let module = blank_program("<__proto__ cycles>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let object = ordinary_object(&mut machine);
        assert!(
            matches!(
                machine.call_value(setter, object, &[object]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ),
            "a direct prototype cycle is a TypeError"
        );
        let first = ordinary_object(&mut machine);
        let second = ordinary_object(&mut machine);
        machine.call_value(setter, first, &[second]).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(first).unwrap(),
            Some(second)
        );
        assert!(
            matches!(
                machine.call_value(setter, second, &[first]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ),
            "an indirect prototype cycle is a TypeError"
        );
        // The failed write leaves the previous prototype in place.
        let untouched = ordinary_object(&mut machine);
        let untouched_prototype = machine.internal_get_prototype_of(untouched).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(second).unwrap(),
            untouched_prototype
        );
    }

    #[test]
    fn proto_setter_rejects_frozen_targets_but_accepts_the_current_prototype() {
        let module = blank_program("<__proto__ frozen>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let object = ordinary_object(&mut machine);
        make_non_extensible(&mut machine, object);
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        // SameValue fast path: re-affirming the current prototype succeeds.
        assert_eq!(
            machine
                .call_value(setter, object, &[object_prototype])
                .unwrap(),
            Value::UNDEFINED
        );
        let replacement = ordinary_object(&mut machine);
        assert!(
            matches!(
                machine.call_value(setter, object, &[replacement]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ),
            "a frozen target rejects a new prototype"
        );
        assert_eq!(
            machine.internal_get_prototype_of(object).unwrap(),
            Some(object_prototype)
        );
    }

    #[test]
    fn proto_setter_mutates_extensible_process_env_and_timeout() {
        let module = blank_program("<__proto__ live ordinary mutation>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let replacement = ordinary_object(&mut machine);

        for (kind, target) in process_env_and_timeout(&mut machine) {
            assert_eq!(
                machine.call_value(setter, target, &[replacement]).unwrap(),
                Value::UNDEFINED,
                "extensible {kind} accepts a new prototype"
            );
            assert_eq!(
                machine.internal_get_prototype_of(target).unwrap(),
                Some(replacement),
                "{kind} stores the new prototype"
            );
        }
    }

    #[test]
    fn proto_setter_rejects_new_prototype_for_non_extensible_process_env_and_timeout() {
        let module = blank_program("<__proto__ live ordinary frozen rejection>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let original = machine.intrinsics.builtins.object_prototype();
        let replacement = ordinary_object(&mut machine);

        for (kind, target) in process_env_and_timeout(&mut machine) {
            make_non_extensible(&mut machine, target);
            assert!(
                matches!(
                    machine.call_value(setter, target, &[replacement]),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ),
                "non-extensible {kind} rejects a new prototype"
            );
            assert_eq!(
                machine.internal_get_prototype_of(target).unwrap(),
                Some(original),
                "rejection preserves the {kind} prototype"
            );
        }
    }

    #[test]
    fn proto_setter_accepts_current_prototype_for_non_extensible_process_env_and_timeout() {
        let module = blank_program("<__proto__ live ordinary same prototype>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let setter = proto_setter_function(&mut machine);
        let current = machine.intrinsics.builtins.object_prototype();

        for (kind, target) in process_env_and_timeout(&mut machine) {
            make_non_extensible(&mut machine, target);
            assert_eq!(
                machine.call_value(setter, target, &[current]).unwrap(),
                Value::UNDEFINED,
                "non-extensible {kind} accepts its current prototype"
            );
            assert_eq!(
                machine.internal_get_prototype_of(target).unwrap(),
                Some(current)
            );
        }
    }

    fn construct_date(machine: &mut Machine<'_, ControlledHost>, args: &[Value]) -> Value {
        let constructor = machine
            .intrinsics
            .global("Date")
            .expect("Date is installed");
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("Date constructor is native");
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, args, true)
            .expect("Date construction succeeds")
        else {
            panic!("Date construction returns a value");
        };
        value
    }

    #[test]
    fn date_annex_b_members_delegate_to_the_installed_date_surface() {
        let module = blank_program("<date annex b>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let constructor = machine
            .intrinsics
            .global("Date")
            .expect("Date is installed");
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .expect("Date has a prototype");
        assert_eq!(prototype, machine.intrinsics.builtins.date_prototype());

        let date = construct_date(&mut machine, &[Value::int32(0)]);
        assert_eq!(
            value_number(call(&mut machine, date, "getYear", &[]).unwrap()),
            70.0
        );
        call(&mut machine, date, "setYear", &[Value::int32(99)]).unwrap();
        assert_eq!(
            value_number(call(&mut machine, date, "getYear", &[]).unwrap()),
            99.0
        );

        let to_gmt = machine
            .get_named_property(prototype, "toGMTString")
            .expect("Annex B toGMTString is installed");
        let to_utc = machine
            .get_named_property(prototype, "toUTCString")
            .expect("canonical toUTCString is installed");
        assert_eq!(to_gmt, to_utc, "toGMTString delegates by function identity");
        let rendered = machine.call_value(to_gmt, date, &[]).unwrap();
        assert_text_of(&mut machine, rendered, "Fri, 01 Jan 1999 00:00:00 GMT");
    }

    #[test]
    fn escape_and_unescape_delegate_to_the_canonical_uri_surface() {
        let module = blank_program("<escape delegation>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let escape = machine
            .intrinsics
            .global("escape")
            .expect("escape is installed");
        let unescape = machine
            .intrinsics
            .global("unescape")
            .expect("unescape is installed");
        let source = text(&mut machine, "aø😀@*+-./");
        let encoded = machine
            .call_value(escape, Value::UNDEFINED, &[source])
            .unwrap();
        assert_text_of(&mut machine, encoded, "a%F8%uD83D%uDE00@*+-./");
        let escaped = text(&mut machine, "%41%u00ff%uD83D%uDE00%uZZZZ%4G");
        let decoded = machine
            .call_value(unescape, Value::UNDEFINED, &[escaped])
            .unwrap();
        let decoded = machine
            .string_value(decoded)
            .expect("unescape returns a string");
        assert_eq!(
            decoded.as_units(),
            EcmaString::encode("A\u{ff}\u{1f600}%uZZZZ%4G").as_units()
        );
        let bigint = machine
            .allocate(HeapEntry::BigInt("1".to_owned()))
            .expect("BigInt allocation succeeds");
        let encoded_bigint = machine
            .call_value(escape, Value::UNDEFINED, &[bigint])
            .unwrap();
        assert_text_of(&mut machine, encoded_bigint, "1");
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert!(matches!(
            machine.call_value(escape, Value::UNDEFINED, &[symbol]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    fn make_regexp(machine: &mut Machine<'_, ControlledHost>, pattern: &str, flags: &str) -> Value {
        let constructor = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        let pattern = text(machine, pattern);
        let flags = text(machine, flags);
        machine
            .call_value(constructor, Value::UNDEFINED, &[pattern, flags])
            .expect("RegExp() constructs")
    }

    #[test]
    fn regexp_compile_reinitializes_slots_and_resets_lastindex() {
        let module = blank_program("<regexp compile>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let regexp = make_regexp(&mut machine, "abc", "g");
        machine
            .set_data_property(regexp, "lastIndex", Value::int32(23))
            .unwrap();
        let pattern = text(&mut machine, "x");
        let flags = text(&mut machine, "ig");
        let result = call(&mut machine, regexp, "compile", &[pattern, flags]).unwrap();
        assert_eq!(result, regexp, "compile returns its receiver");
        assert_eq!(
            value_number(machine.get_named_property(regexp, "lastIndex").unwrap()),
            0.0,
            "a successful compile resets lastIndex"
        );
        assert_eq!(
            value_number(machine.get_named_property(regexp, "lastIndex").unwrap()),
            0.0
        );
        for (name, expected) in [("source", "x"), ("flags", "gi")] {
            let name_key = PropertyKey::Named(machine.intern_str(name));
            assert!(
                machine.own_descriptor(regexp, &name_key).unwrap().is_none(),
                "compile must not create an own {name} property"
            );
            let value = machine.get_named_property(regexp, name).unwrap();
            assert_text_of(&mut machine, value, expected);
        }
        let rendered = call(&mut machine, regexp, "toString", &[]).unwrap();
        assert_text_of(&mut machine, rendered, "/x/gi");
    }

    #[test]
    fn regexp_compile_applies_regexp_pattern_argument_rules() {
        let module = blank_program("<regexp compile patterns>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let regexp = make_regexp(&mut machine, "abc", "g");
        let source_regexp = make_regexp(&mut machine, "def", "m");
        // Same-object recompilation without flags succeeds.
        assert_eq!(
            call(&mut machine, regexp, "compile", &[regexp]).unwrap(),
            regexp
        );
        // A RegExp pattern with any defined flags argument rejects.
        let nullish = Value::NULL;
        let zero = Value::int32(0);
        let empty = text(&mut machine, "");
        let boolean = Value::boolean(false);
        let object = ordinary_object(&mut machine);
        let array_ctor = machine
            .intrinsics
            .global("Array")
            .expect("Array is installed");
        let array = machine
            .call_value(array_ctor, Value::UNDEFINED, &[])
            .expect("Array() constructs");
        for bad_flags in [nullish, zero, empty, boolean, object, array] {
            assert_type_error(call(
                &mut machine,
                regexp,
                "compile",
                &[source_regexp, bad_flags],
            ));
        }
        let unchanged = call(&mut machine, regexp, "toString", &[]).unwrap();
        let unchanged_text = machine
            .string_value(unchanged)
            .expect("toString returns a string");
        assert!(
            unchanged_text.eq_ascii("/abc/g"),
            "rejected compiles leave the receiver untouched"
        );
        // A RegExp pattern without flags inherits source and flags.
        call(&mut machine, regexp, "compile", &[source_regexp]).unwrap();
        let inherited = call(&mut machine, regexp, "toString", &[]).unwrap();
        assert_text_of(&mut machine, inherited, "/def/m");
        // An undefined pattern rebuilds the empty pattern and clears flags.
        call(&mut machine, regexp, "compile", &[]).unwrap();
        let rebuilt = call(&mut machine, regexp, "toString", &[]).unwrap();
        assert_text_of(&mut machine, rebuilt, "/(?:)/");
    }

    #[test]
    fn regexp_compile_rejects_incompatible_receivers() {
        let module = blank_program("<regexp compile receivers>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let pattern = text(&mut machine, "x");
        let object = ordinary_object(&mut machine);
        assert_type_error(call(&mut machine, object, "compile", &[pattern]));
        let text_receiver = text(&mut machine, "not a regexp");
        assert_type_error(call(&mut machine, text_receiver, "compile", &[pattern]));
        assert_type_error(call(&mut machine, Value::UNDEFINED, "compile", &[pattern]));
    }

    #[test]
    fn regexp_compile_propagates_syntax_and_coercion_errors() {
        let module = blank_program("<regexp compile errors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let regexp = make_regexp(&mut machine, "abc", "g");
        let bad_pattern = text(&mut machine, "(?");
        match call(&mut machine, regexp, "compile", &[bad_pattern]) {
            Err(EvalFailure::ThrowValue(error)) => {
                let syntax_prototype = {
                    let id = machine
                        .intrinsics
                        .builtins
                        .id_named("SyntaxError")
                        .expect("SyntaxError is installed");
                    machine.intrinsics.error_prototype(id)
                };
                assert!(
                    machine
                        .inherits_from_prototype(error, syntax_prototype)
                        .unwrap(),
                    "an invalid pattern throws a SyntaxError object"
                );
            }
            other => panic!("expected a thrown SyntaxError, got {other:?}"),
        }
        // The failed pattern does not replace the installed one.
        let rendered = call(&mut machine, regexp, "toString", &[]).unwrap();
        assert_text_of(&mut machine, rendered, "/abc/g");
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert_type_error(call(&mut machine, regexp, "compile", &[symbol]));
        let valid_pattern = text(&mut machine, "x");
        assert_type_error(call(
            &mut machine,
            regexp,
            "compile",
            &[valid_pattern, symbol],
        ));
        let bad_flags = text(&mut machine, "abc");
        let valid_pattern = text(&mut machine, "x");
        assert!(
            matches!(
                call(&mut machine, regexp, "compile", &[valid_pattern, bad_flags]),
                Err(EvalFailure::ThrowValue(_))
            ),
            "invalid flags throw a SyntaxError object"
        );
    }

    #[test]
    fn regexp_compile_respects_a_read_only_lastindex() {
        let module = blank_program("<regexp compile lastindex>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let regexp = make_regexp(&mut machine, "abc", "g");
        let object_constructor = machine
            .intrinsics
            .global("Object")
            .expect("Object is installed");
        let define_property_fn = machine
            .get_named_property(object_constructor, "defineProperty")
            .unwrap();
        let descriptor = ordinary_object(&mut machine);
        machine
            .set_data_property(descriptor, "value", Value::int32(45))
            .unwrap();
        machine
            .set_data_property(descriptor, "writable", Value::boolean(false))
            .unwrap();
        let last_index = text(&mut machine, "lastIndex");
        machine
            .call_value(
                define_property_fn,
                Value::UNDEFINED,
                &[regexp, last_index, descriptor],
            )
            .unwrap();
        let pattern = text(&mut machine, "b");
        let flags = text(&mut machine, "m");
        assert_type_error(call(&mut machine, regexp, "compile", &[pattern, flags]));
        // The matcher reinitialized before the failing lastIndex write.
        let rendered = call(&mut machine, regexp, "toString", &[]).unwrap();
        assert_text_of(&mut machine, rendered, "/b/m");
        assert_eq!(
            value_number(machine.get_named_property(regexp, "lastIndex").unwrap()),
            45.0
        );
    }
    #[test]
    fn regexp_legacy_statics_have_annex_b_descriptors_and_aliases() {
        let module = blank_program("<regexp legacy descriptors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let constructor = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        for property in [
            "input",
            "$_",
            "lastMatch",
            "$&",
            "lastParen",
            "$+",
            "leftContext",
            "$\x60",
            "rightContext",
            "$'",
            "$1",
            "$2",
            "$3",
            "$4",
            "$5",
            "$6",
            "$7",
            "$8",
            "$9",
        ] {
            let prop_key = PropertyKey::Named(machine.intern_str(property));
            let descriptor = machine
                .own_descriptor(constructor, &prop_key)
                .unwrap()
                .unwrap_or_else(|| panic!("RegExp.{property} is installed"));
            let Property::Accessor {
                getter: Some(_),
                setter,
                enumerable: false,
                configurable: true,
            } = descriptor
            else {
                panic!("RegExp.{property} is a non-enumerable configurable accessor");
            };
            assert_eq!(
                setter.is_some(),
                matches!(property, "input" | "$_"),
                "only the input aliases have setters"
            );
            let value = machine.get_named_property(constructor, property).unwrap();
            assert_text_of(&mut machine, value, "");
        }
    }

    #[test]
    fn regexp_legacy_accessors_require_the_intrinsic_constructor_receiver() {
        let module = blank_program("<regexp legacy receiver>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let constructor = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        let input_key = PropertyKey::Named(machine.intern_str("input"));
        let Property::Accessor {
            getter: Some(getter),
            setter: Some(setter),
            ..
        } = machine
            .own_descriptor(constructor, &input_key)
            .unwrap()
            .expect("RegExp.input is installed")
        else {
            panic!("RegExp.input has getter and setter functions");
        };
        let instance = make_regexp(&mut machine, "x", "");
        let ordinary = ordinary_object(&mut machine);
        for receiver in [Value::UNDEFINED, Value::NULL, instance, ordinary] {
            assert_type_error(machine.call_value(getter, receiver, &[]));
            assert_type_error(machine.call_value(setter, receiver, &[Value::int32(1)]));
        }
        let value = machine.call_value(getter, constructor, &[]).unwrap();
        assert_text_of(&mut machine, value, "");
    }

    #[test]
    fn regexp_legacy_match_hook_updates_contexts_and_captures() {
        let module = blank_program("<regexp legacy match state>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let constructor = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        let input = EcmaString::encode("preabcmid");
        let matched = Match {
            range: 3..6,
            captures: vec![None, Some(3..4), None, Some(5..6)],
            named: Vec::new(),
        };
        record_legacy_match(&mut machine, &input, &matched).unwrap();
        for (property, expected) in [
            ("input", "preabcmid"),
            ("$_", "preabcmid"),
            ("lastMatch", "abc"),
            ("$&", "abc"),
            ("lastParen", "c"),
            ("$+", "c"),
            ("leftContext", "pre"),
            ("$\x60", "pre"),
            ("rightContext", "mid"),
            ("$'", "mid"),
            ("$1", "a"),
            ("$2", ""),
            ("$3", "c"),
            ("$4", ""),
            ("$9", ""),
        ] {
            let value = machine.get_named_property(constructor, property).unwrap();
            assert_text_of(&mut machine, value, expected);
        }

        let replacement = text(&mut machine, "changed");
        machine
            .set_data_property(constructor, "input", replacement)
            .unwrap();
        let input_value = machine.get_named_property(constructor, "$_").unwrap();
        assert_text_of(&mut machine, input_value, "changed");
        let last_match = machine
            .get_named_property(constructor, "lastMatch")
            .unwrap();
        assert_text_of(&mut machine, last_match, "abc");

        let bigint = machine
            .allocate(HeapEntry::BigInt("10".to_owned()))
            .expect("BigInt allocation succeeds");
        machine
            .set_data_property(constructor, "$_", bigint)
            .unwrap();
        let bigint_input = machine.get_named_property(constructor, "input").unwrap();
        assert_text_of(&mut machine, bigint_input, "10");
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("s"),
            })
            .expect("symbol allocation succeeds");
        assert!(matches!(
            machine.set_data_property(constructor, "input", symbol),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }
    #[test]
    fn annex_b_owned_functions_are_not_constructors() {
        let module = blank_program("<annex b non-constructors>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let string_prototype = machine.intrinsics.builtins.string_prototype();
        let mut functions = Vec::new();
        for name in [
            "anchor",
            "big",
            "blink",
            "bold",
            "fixed",
            "fontcolor",
            "fontsize",
            "italics",
            "link",
            "small",
            "strike",
            "sub",
            "sup",
            "substr",
        ] {
            functions.push(machine.get_named_property(string_prototype, name).unwrap());
        }
        let regexp_prototype = machine.intrinsics.builtins.regexp_prototype();
        functions.push(
            machine
                .get_named_property(regexp_prototype, "compile")
                .unwrap(),
        );
        let object_prototype = machine.intrinsics.builtins.object_prototype();
        let proto_key = PropertyKey::Named(machine.intern_str("__proto__"));
        let Property::Accessor {
            getter: Some(proto_getter),
            setter: Some(proto_setter),
            ..
        } = machine
            .own_descriptor(object_prototype, &proto_key)
            .unwrap()
            .expect("__proto__ is installed")
        else {
            panic!("__proto__ has getter and setter functions");
        };
        functions.extend([proto_getter, proto_setter]);
        for name in [
            "__defineGetter__",
            "__defineSetter__",
            "__lookupGetter__",
            "__lookupSetter__",
        ] {
            functions.push(machine.get_named_property(object_prototype, name).unwrap());
        }
        let regexp_constructor = machine
            .intrinsics
            .global("RegExp")
            .expect("RegExp is installed");
        for property in ["input", "$1"] {
            let prop_key = PropertyKey::Named(machine.intern_str(property));
            let Property::Accessor { getter, setter, .. } = machine
                .own_descriptor(regexp_constructor, &prop_key)
                .unwrap()
                .unwrap_or_else(|| panic!("RegExp.{property} is installed"))
            else {
                panic!("RegExp.{property} is an accessor");
            };
            functions.extend(getter);
            functions.extend(setter);
        }
        for function in functions {
            assert_type_error(machine.construct_value(function, &[]));
        }
    }
    static DEFINE_KEY_TRIED: AtomicBool = AtomicBool::new(false);

    fn define_key_to_string(
        machine: &mut Machine<'_, ControlledHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        DEFINE_KEY_TRIED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("key"),
        )?))
    }

    fn getter_of_this(
        _machine: &mut Machine<'_, ControlledHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    fn setter_records_on_this(
        machine: &mut Machine<'_, ControlledHost>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(
            this,
            "seen",
            args.first().copied().unwrap_or(Value::UNDEFINED),
        )?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn assert_getter_slot(
        machine: &mut Machine<'_, ControlledHost>,
        object: Value,
        name: &str,
        expected: Value,
    ) {
        let Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        } = own_data_property(machine, object, name)
        else {
            panic!("{name} is a getter-only, non-enumerable, configurable accessor");
        };
        assert_eq!(getter, expected, "{name} holds the installed getter");
    }

    #[test]
    fn object_annex_b_surface_has_spec_names_lengths_and_descriptors() {
        let module = blank_program("<object annex b surface>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let prototype = machine.intrinsics.builtins.object_prototype();
        for (name, length) in [
            ("__defineGetter__", 2),
            ("__defineSetter__", 2),
            ("__lookupGetter__", 1),
            ("__lookupSetter__", 1),
        ] {
            let Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            } = own_data_property(&mut machine, prototype, name)
            else {
                panic!("{name} is a writable, non-enumerable, configurable data property");
            };
            let length_value = machine.get_named_property(value, "length").unwrap();
            assert_eq!(
                value_number(length_value),
                f64::from(length),
                "{name} length"
            );
            let name_value = machine.get_named_property(value, "name").unwrap();
            assert_text_of(&mut machine, name_value, name);
        }
    }

    #[test]
    fn define_accessor_methods_install_single_slot_dispatching_accessors() {
        let module = blank_program("<define accessor dispatch>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let object = ordinary_object(&mut machine);
        let getter = native(&mut machine, "get slot", 0, getter_of_this);
        let setter = native(&mut machine, "set slot", 1, setter_records_on_this);
        let getter_key = text(&mut machine, "getter_slot");
        call(
            &mut machine,
            object,
            "__defineGetter__",
            &[getter_key, getter],
        )
        .unwrap();
        assert_getter_slot(&mut machine, object, "getter_slot", getter);
        assert_eq!(
            machine.get_named_property(object, "getter_slot").unwrap(),
            object,
            "reading the slot dispatches the getter with the receiver"
        );
        let setter_key = text(&mut machine, "setter_slot");
        call(
            &mut machine,
            object,
            "__defineSetter__",
            &[setter_key, setter],
        )
        .unwrap();
        let Property::Accessor {
            getter: None,
            setter: Some(setter_slot),
            enumerable: false,
            configurable: true,
        } = own_data_property(&mut machine, object, "setter_slot")
        else {
            panic!("setter_slot is a setter-only, non-enumerable, configurable accessor");
        };
        assert_eq!(setter_slot, setter);
        machine
            .set_data_property(object, "setter_slot", Value::int32(42))
            .unwrap();
        let seen = machine.get_named_property(object, "seen").unwrap();
        assert_eq!(
            value_number(seen),
            42.0,
            "writing the slot dispatches the setter"
        );
    }

    #[test]
    fn define_setter_replaces_a_whole_descriptor_dropping_the_getter() {
        let module = blank_program("<define setter replaces>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let object = ordinary_object(&mut machine);
        let getter = native(&mut machine, "get both", 0, getter_of_this);
        let setter = native(&mut machine, "set both", 1, setter_records_on_this);
        let key = text(&mut machine, "both");
        call(&mut machine, object, "__defineGetter__", &[key, getter]).unwrap();
        call(&mut machine, object, "__defineSetter__", &[key, setter]).unwrap();
        let Property::Accessor {
            getter: None,
            setter: Some(setter_slot),
            enumerable: false,
            configurable: true,
        } = own_data_property(&mut machine, object, "both")
        else {
            panic!("the setter replaced the whole descriptor");
        };
        assert_eq!(setter_slot, setter);
        assert_eq!(
            machine.get_named_property(object, "both").unwrap(),
            Value::UNDEFINED,
            "the dropped getter no longer dispatches"
        );
        machine
            .set_data_property(object, "both", Value::int32(7))
            .unwrap();
        let seen = machine.get_named_property(object, "seen").unwrap();
        assert_eq!(value_number(seen), 7.0, "the surviving setter still runs");
    }

    #[test]
    fn lookup_methods_walk_the_prototype_chain_and_distinguish_slots() {
        let module = blank_program("<lookup chain>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let parent = ordinary_object(&mut machine);
        let child = ordinary_object(&mut machine);
        let proto_setter = proto_setter_function(&mut machine);
        machine.call_value(proto_setter, child, &[parent]).unwrap();
        let getter = native(&mut machine, "get inherited", 0, getter_of_this);
        let setter = native(&mut machine, "set both", 1, setter_records_on_this);
        let key = text(&mut machine, "inherited");
        call(&mut machine, parent, "__defineGetter__", &[key, getter]).unwrap();
        assert_eq!(
            call(&mut machine, parent, "__lookupGetter__", &[key]).unwrap(),
            getter,
            "an own getter is found directly"
        );
        assert_eq!(
            call(&mut machine, child, "__lookupGetter__", &[key]).unwrap(),
            getter,
            "an inherited getter is found through the chain"
        );
        assert_eq!(
            call(&mut machine, child, "__lookupSetter__", &[key]).unwrap(),
            Value::UNDEFINED,
            "a getter-only slot reports no setter"
        );
        let both_key = PropertyKey::Named(machine.intern_str("both"));
        machine
            .define_descriptor(
                parent,
                both_key,
                Property::Accessor {
                    getter: Some(getter),
                    setter: Some(setter),
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        let key = text(&mut machine, "both");
        assert_eq!(
            call(&mut machine, child, "__lookupGetter__", &[key]).unwrap(),
            getter
        );
        assert_eq!(
            call(&mut machine, child, "__lookupSetter__", &[key]).unwrap(),
            setter
        );
        machine
            .set_data_property(parent, "data", Value::int32(1))
            .unwrap();
        let key = text(&mut machine, "data");
        assert_eq!(
            call(&mut machine, child, "__lookupGetter__", &[key]).unwrap(),
            Value::UNDEFINED,
            "a data property stops the search"
        );
        assert_eq!(
            call(&mut machine, child, "__lookupSetter__", &[key]).unwrap(),
            Value::UNDEFINED
        );
        let missing = text(&mut machine, "missing");
        assert_eq!(
            call(&mut machine, child, "__lookupGetter__", &[missing]).unwrap(),
            Value::UNDEFINED,
            "an exhausted chain reports undefined"
        );
    }

    #[test]
    fn define_getter_validates_callable_before_coercing_the_key() {
        DEFINE_KEY_TRIED.store(false, Ordering::SeqCst);
        let module = blank_program("<define callable order>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let receiver = ordinary_object(&mut machine);
        let key = coerced_object(&mut machine, define_key_to_string);
        assert_type_error(call(
            &mut machine,
            receiver,
            "__defineGetter__",
            &[key, Value::int32(7)],
        ));
        assert!(
            !DEFINE_KEY_TRIED.load(Ordering::SeqCst),
            "callable validation must precede key coercion"
        );
        assert_type_error(call(
            &mut machine,
            receiver,
            "__defineSetter__",
            &[key, Value::UNDEFINED],
        ));
        assert!(
            !DEFINE_KEY_TRIED.load(Ordering::SeqCst),
            "setter validation must also precede key coercion"
        );
        let getter = native(&mut machine, "get key", 0, getter_of_this);
        call(&mut machine, receiver, "__defineGetter__", &[key, getter]).unwrap();
        assert!(
            DEFINE_KEY_TRIED.load(Ordering::SeqCst),
            "a valid callable lets the key coercion run"
        );
        assert_getter_slot(&mut machine, receiver, "key", getter);
    }

    #[test]
    fn define_accessor_methods_reject_non_configurable_redefinition() {
        let module = blank_program("<define frozen slots>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let object = ordinary_object(&mut machine);
        let getter = native(&mut machine, "get locked", 0, getter_of_this);
        let setter = native(&mut machine, "set sealed", 1, setter_records_on_this);
        let locked_key = PropertyKey::Named(machine.intern_str("locked"));
        machine
            .define_descriptor(
                object,
                locked_key,
                Property::Data {
                    value: Value::UNDEFINED,
                    writable: false,
                    enumerable: false,
                    configurable: false,
                },
            )
            .unwrap();
        let sealed_key = PropertyKey::Named(machine.intern_str("sealed"));
        machine
            .define_descriptor(
                object,
                sealed_key,
                Property::Accessor {
                    getter: None,
                    setter: None,
                    enumerable: false,
                    configurable: false,
                },
            )
            .unwrap();
        let key = text(&mut machine, "locked");
        assert_type_error(call(
            &mut machine,
            object,
            "__defineGetter__",
            &[key, getter],
        ));
        let key = text(&mut machine, "sealed");
        assert_type_error(call(
            &mut machine,
            object,
            "__defineSetter__",
            &[key, setter],
        ));
    }

    #[test]
    fn lookup_and_define_methods_accept_primitives_and_symbol_keys() {
        let module = blank_program("<primitives and symbols>");
        let mut host = ControlledHost { zone: "UTC" };
        let mut machine = machine(&module, &mut host);
        let getter = native(&mut machine, "get boxed", 0, getter_of_this);
        let boxed_key = text(&mut machine, "boxed");
        call(
            &mut machine,
            Value::int32(5),
            "__defineGetter__",
            &[boxed_key, getter],
        )
        .unwrap();
        let inherited_key2 = PropertyKey::Named(machine.intern_str("inherited"));
        machine
            .define_descriptor(
                machine.intrinsics.number_prototype,
                inherited_key2,
                Property::Accessor {
                    getter: Some(getter),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        let inherited_key = text(&mut machine, "inherited");
        assert_eq!(
            call(
                &mut machine,
                Value::int32(5),
                "__lookupGetter__",
                &[inherited_key]
            )
            .unwrap(),
            getter,
            "the lookup walks the boxed prototype chain"
        );
        assert_eq!(
            call(
                &mut machine,
                Value::int32(5),
                "__lookupSetter__",
                &[inherited_key]
            )
            .unwrap(),
            Value::UNDEFINED
        );
        let key = text(&mut machine, "k");
        for name in [
            "__defineGetter__",
            "__defineSetter__",
            "__lookupGetter__",
            "__lookupSetter__",
        ] {
            assert_type_error(call(&mut machine, Value::UNDEFINED, name, &[key, getter]));
            assert_type_error(call(&mut machine, Value::NULL, name, &[key, getter]));
        }
        let object = ordinary_object(&mut machine);
        let symbol = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("sym"),
            })
            .expect("symbol allocation succeeds");
        call(&mut machine, object, "__defineGetter__", &[symbol, getter]).unwrap();
        let slot = machine
            .runtime_slot(symbol)
            .unwrap()
            .expect("symbol has a heap slot");
        let Property::Accessor {
            getter: Some(getter_slot),
            setter: None,
            ..
        } = machine
            .own_descriptor(
                object,
                &PropertyKey::Symbol(u32::try_from(slot).expect("slot fits u32")),
            )
            .unwrap()
            .expect("symbol-keyed accessor is installed")
        else {
            panic!("the symbol key holds the getter-only accessor");
        };
        assert_eq!(getter_slot, getter);
        assert_eq!(
            call(&mut machine, object, "__lookupGetter__", &[symbol]).unwrap(),
            getter,
            "the lookup resolves symbol keys"
        );
        assert_eq!(
            call(&mut machine, object, "__lookupSetter__", &[symbol]).unwrap(),
            Value::UNDEFINED
        );
    }
}
