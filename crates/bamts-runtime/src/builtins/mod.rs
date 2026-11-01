use super::{BuiltinDef, BuiltinOutcome, BuiltinTable, native_function, push};
use crate::GetOutcome;
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, ThrowOrigin,
};
use bamts_bytecode::{DescriptorSlot, EcmaString};
use bamts_native::{Decoded, Value};
use std::collections::BTreeMap;
mod array;
pub(crate) mod bigint;
mod collections;
mod date_full;
mod function_constructor;
mod json_edge;
mod number;
mod object;
mod object_statics;
mod promise;
pub(crate) mod property_descriptor;
pub(crate) mod proxy;
pub(crate) mod reflect;
mod regexp;
pub(crate) use regexp::{canonical_source, initial_regexp_properties};
mod annex_b;
mod array_es2023;
pub(crate) mod arraybuffer;
pub(crate) mod atomics;
pub(crate) mod dataview;
mod disposable_stack;
mod error_edge;
mod map_set_edge;
mod math_edge;
mod number_format;
mod regexp_v;
mod set_methods;
mod string;
mod string_edge;
mod structured_clone;
mod symbol;
#[cfg(test)]
pub(crate) mod test_support;
mod timers;
pub(crate) mod typedarray_all;
mod uri;
pub(crate) mod weakref_finalization;
pub(crate) use collections::ordinary_runtime;
pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
    timers_available: bool,
    script_compiler: bool,
) {
    symbol::install(heap, globals, builtins);
    let bigint_prototype = bigint::install(heap, globals, builtins);
    builtins.set_bigint_prototype(bigint_prototype);
    promise::install(heap, globals, builtins);
    if timers_available {
        timers::install(heap, globals, builtins);
    }
    collections::install_iterator_prototype(heap, builtins);
    collections::install_async_iterator_prototype(heap, builtins);
    collections::install_generator_prototype(heap, builtins);
    collections::install_async_generator_prototype(heap, builtins);
    collections::install(heap, globals, builtins);
    function_constructor::install(heap, globals, builtins, script_compiler);
    map_set_edge::install(heap, globals, builtins);
    date_full::install(heap, globals, builtins);
    object::install(heap, globals, builtins);
    array::install(heap, globals, builtins);
    string::install(heap, globals, builtins);
    number::install(heap, globals, builtins);
    install_boolean(heap, globals, builtins);
    install_math(heap, globals, builtins);
    regexp::install(heap, globals, builtins);
    string_edge::install(heap, globals, builtins);
    annex_b::install(heap, globals, builtins);
    weakref_finalization::install(heap, globals, builtins);
    arraybuffer::install(heap, globals, builtins);
    atomics::install(heap, globals, builtins);
    typedarray_all::install(heap, globals, builtins);
    dataview::install(heap, globals, builtins);
    install_globals(heap, globals, builtins);
    json_edge::install(heap, globals, builtins);
    install_errors(heap, globals, builtins);
    error_edge::install(heap, globals, builtins);
    proxy::install(heap, globals, builtins);
    if let Some(id) = builtins.id_named("Proxy") {
        builtins.set_constructable(id, true);
    }
    reflect::install(heap, globals, builtins);
    uri::install(heap, globals, builtins);
    disposable_stack::install(heap, globals, builtins);
}
fn install_function<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    length: u32,
    handler: super::BuiltinHandler<H>,
) -> Value {
    let id = builtins.register(BuiltinDef {
        name,
        length,
        handler,
    });
    let definition = builtins.get(id);
    native_function(heap, id, definition.name, definition.length)
}

/// Installs a builtin **constructor** (`[[Construct]]` present). Method,
/// static, and accessor installs keep using `install_function`, which
/// registers non-constructable by default.
pub(crate) fn install_constructor_function<H: Host>(
    heap: &mut Vec<HeapEntry>,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    length: u32,
    handler: super::BuiltinHandler<H>,
) -> Value {
    let id = builtins.register_constructor(BuiltinDef {
        name,
        length,
        handler,
    });
    let definition = builtins.get(id);
    native_function(heap, id, definition.name, definition.length)
}
pub(crate) fn define_data(heap: &mut [HeapEntry], object: Value, name: &str, value: Value) {
    let index = heap_index(object);
    match &mut heap[index] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::Function { properties, .. }
        | HeapEntry::Script { properties, .. }
        | HeapEntry::NativeFunction { properties, .. }
        | HeapEntry::RegExp { properties, .. }
        | HeapEntry::Date { properties, .. } => {
            properties.insert(
                PropertyKey::Named(EcmaString::encode(name)),
                builtin_property(value),
            );
        }
        _ => panic!("intrinsic property target must be an ordinary object"),
    }
}
pub(super) fn define_to_string_tag(
    heap: &mut Vec<HeapEntry>,
    object: Value,
    symbol: Value,
    tag: &str,
) {
    let value = push(heap, HeapEntry::String(EcmaString::encode(tag)));
    let index = heap_index(object);
    let HeapEntry::Object { properties, .. } = &mut heap[index] else {
        panic!("namespace tag target must be an ordinary object");
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(symbol) as u32),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
}
/// Installs a named data property that is non-writable, non-enumerable, and
/// non-configurable onto an ordinary object, array, or native function.
pub(crate) fn define_frozen_data(heap: &mut [HeapEntry], object: Value, name: &str, value: Value) {
    let index = heap_index(object);
    let properties = match &mut heap[index] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::Function { properties, .. }
        | HeapEntry::Script { properties, .. }
        | HeapEntry::RegExp { properties, .. }
        | HeapEntry::NativeFunction { properties, .. } => properties,
        _ => panic!("frozen property target must be an ordinary object"),
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );
}
fn builtin_property(value: Value) -> Property {
    Property::Data {
        value,
        writable: true,
        enumerable: false,
        configurable: true,
    }
}
fn heap_index(value: Value) -> usize {
    let bamts_native::Decoded::HeapRef(id) = value.decode().expect("intrinsic value is valid")
    else {
        panic!("intrinsic value is a heap reference");
    };
    id.slot() as usize - 1
}
fn allocate_string<H: Host>(
    machine: &mut Machine<'_, H>,
    text: EcmaString,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::String(text))
        .map_err(EvalFailure::Runtime)
}
fn allocate_array<H: Host>(
    machine: &mut Machine<'_, H>,
    elements: Vec<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Array {
            elements,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .map_err(EvalFailure::Runtime)
}
fn value_number(value: Value) -> f64 {
    match value.decode() {
        Some(bamts_native::Decoded::Int32(value)) => f64::from(value as i32),
        Some(bamts_native::Decoded::Number(value)) => value,
        _ => f64::NAN,
    }
}

#[allow(dead_code)]
pub(crate) fn to_uint8<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<u8, EvalFailure> {
    let number = match machine.coerce_number_observable(value)?.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => unreachable!("ToNumber produces a numeric value"),
    };
    Ok(to_uint8_from_f64(number))
}

/// ECMA-262 §7.1.11 ToUint8: NaN, ±0, and ±∞ all yield 0; every other finite
/// Number is truncated toward zero and reduced modulo 256 into `[0, 256)`.
/// `rem_euclid` returns a non-negative remainder strictly less than 256 for
/// finite input, so the narrowing cast never saturates (unlike `as i64 as u8`,
/// which saturates out-of-i64 finite values such as `1e20` to 255).
#[allow(dead_code)]
fn to_uint8_from_f64(number: f64) -> u8 {
    if number.is_finite() && number != 0.0 {
        number.trunc().rem_euclid(256.0) as u8
    } else {
        0
    }
}

fn to_integer_or_infinity<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let number = value_number(machine.to_number(value)?);
    Ok(if number.is_nan() || number == 0.0 {
        0.0
    } else {
        number.trunc()
    })
}
fn type_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::TypeError { operation })
}
fn range_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::RangeError { operation })
}
fn uri_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::UriError { operation })
}
fn define_array_length(
    elements: &mut Vec<Value>,
    properties: &mut PropertyMap,
    length_writable: bool,
    length: usize,
) -> Result<(), EvalFailure> {
    if !length_writable && length != elements.len() {
        return Err(type_error("Cannot redefine non-writable array length"));
    }
    crate::apply_array_length(elements, properties, length, "define array length")
}
fn install_boolean<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.boolean_prototype();
    let constructor =
        install_constructor_function(heap, builtins, "Boolean", 1, boolean_constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    globals.insert(EcmaString::encode("Boolean"), constructor);
    let value_of = install_function(heap, builtins, "valueOf", 0, boolean_value_of::<H>);
    define_data(heap, prototype, "valueOf", value_of);
    let to_string = install_function(heap, builtins, "toString", 0, boolean_to_string::<H>);
    define_data(heap, prototype, "toString", to_string);
}
fn boolean_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value =
        Value::boolean(machine.to_boolean(args.first().copied().unwrap_or(Value::UNDEFINED)));
    if constructing {
        return machine.box_primitive(value).map(BuiltinOutcome::Value);
    }
    Ok(BuiltinOutcome::Value(value))
}
fn boolean_value_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = machine.unbox_primitive(this, "Boolean.prototype.valueOf")?;
    match value.decode() {
        Some(bamts_native::Decoded::Boolean(_)) => Ok(BuiltinOutcome::Value(value)),
        _ => Err(type_error(
            "Boolean.prototype.valueOf called on incompatible receiver",
        )),
    }
}
fn boolean_to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = machine.unbox_primitive(this, "Boolean.prototype.toString")?;
    let Some(bamts_native::Decoded::Boolean(value)) = value.decode() else {
        return Err(type_error(
            "Boolean.prototype.toString called on incompatible receiver",
        ));
    };
    let text = EcmaString::encode(if value { "true" } else { "false" });
    allocate_string(machine, text).map(BuiltinOutcome::Value)
}
fn install_math<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let math = push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.object_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    for (name, length, handler) in [
        ("abs", 1, math_abs::<H> as super::BuiltinHandler<H>),
        ("min", 2, math_min::<H>),
        ("max", 2, math_max::<H>),
        ("floor", 1, math_floor::<H>),
        ("ceil", 1, math_ceil::<H>),
        ("round", 1, math_round::<H>),
        ("trunc", 1, math_trunc::<H>),
        ("sign", 1, math_sign::<H>),
        ("pow", 2, math_pow::<H>),
        ("sqrt", 1, math_sqrt::<H>),
        ("random", 0, math_random::<H>),
        ("hypot", 2, math_hypot::<H>),
        ("log2", 1, math_log2::<H>),
        ("imul", 2, math_imul::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, math, name, function);
    }
    define_to_string_tag(heap, math, builtins.symbol_to_string_tag(), "Math");
    globals.insert(EcmaString::encode("Math"), math);
    math_edge::install(heap, builtins, math);
}
fn numeric_args<H: Host>(
    machine: &Machine<'_, H>,
    args: &[Value],
) -> Result<Vec<f64>, EvalFailure> {
    args.iter()
        .map(|value| machine.to_number(*value).map(value_number))
        .collect()
}
macro_rules! unary_math {
    ($name:ident, $body:expr) => {
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let x =
                value_number(machine.to_number(args.first().copied().unwrap_or(Value::UNDEFINED))?)
                    as f64;
            Ok(BuiltinOutcome::Value(crate::number_value(($body)(x))))
        }
    };
}
unary_math!(math_abs, f64::abs);
unary_math!(math_floor, f64::floor);
unary_math!(math_ceil, f64::ceil);
unary_math!(math_trunc, f64::trunc);
unary_math!(math_sqrt, f64::sqrt);
unary_math!(math_log2, f64::log2);
fn math_round<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let x = value_number(machine.to_number(args.first().copied().unwrap_or(Value::UNDEFINED))?);
    let rounded = if (-0.5..0.0).contains(&x) {
        -0.0
    } else {
        (x + 0.5).floor()
    };
    Ok(BuiltinOutcome::Value(crate::number_value(rounded)))
}
fn math_sign<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let x = value_number(machine.to_number(args.first().copied().unwrap_or(Value::UNDEFINED))?);
    let sign = if x == 0.0 || x.is_nan() {
        x
    } else {
        x.signum()
    };
    Ok(BuiltinOutcome::Value(crate::number_value(sign)))
}
fn math_min<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let numbers = numeric_args(machine, args)?;
    let value = numbers.into_iter().fold(f64::INFINITY, |a, b| {
        if a.is_nan() || b.is_nan() {
            f64::NAN
        } else if a == 0.0 && b == 0.0 {
            if a.is_sign_negative() || b.is_sign_negative() {
                -0.0
            } else {
                0.0
            }
        } else {
            a.min(b)
        }
    });
    Ok(BuiltinOutcome::Value(crate::number_value(value)))
}
fn math_max<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let numbers = numeric_args(machine, args)?;
    let value = numbers.into_iter().fold(f64::NEG_INFINITY, |a, b| {
        if a.is_nan() || b.is_nan() {
            f64::NAN
        } else if a == 0.0 && b == 0.0 {
            if a.is_sign_positive() || b.is_sign_positive() {
                0.0
            } else {
                -0.0
            }
        } else {
            a.max(b)
        }
    });
    Ok(BuiltinOutcome::Value(crate::number_value(value)))
}
fn math_pow<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let x = value_number(machine.to_number(args.first().copied().unwrap_or(Value::UNDEFINED))?);
    let y = value_number(machine.to_number(args.get(1).copied().unwrap_or(Value::UNDEFINED))?);
    Ok(BuiltinOutcome::Value(crate::number_value(x.powf(y))))
}
fn math_random<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        machine.host.random(),
    )))
}
fn math_hypot<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let values = numeric_args(machine, args)?;
    let max = values.iter().map(|x| x.abs()).fold(0.0, f64::max);
    let result = if max.is_infinite() {
        f64::INFINITY
    } else if values.iter().any(|x| x.is_nan()) {
        f64::NAN
    } else if max == 0.0 {
        0.0
    } else {
        max * values.iter().map(|x| (x / max).powi(2)).sum::<f64>().sqrt()
    };
    Ok(BuiltinOutcome::Value(crate::number_value(result)))
}
fn math_imul<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let a =
        value_number(machine.to_number(args.first().copied().unwrap_or(Value::UNDEFINED))?) as u32;
    let b =
        value_number(machine.to_number(args.get(1).copied().unwrap_or(Value::UNDEFINED))?) as u32;
    Ok(BuiltinOutcome::Value(Value::int32(a.wrapping_mul(b))))
}
fn install_globals<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    for (name, length, handler) in [
        (
            "parseInt",
            2,
            number::parse_int::<H> as super::BuiltinHandler<H>,
        ),
        ("parseFloat", 1, number::parse_float::<H>),
        ("isNaN", 1, number::global_is_nan::<H>),
        ("isFinite", 1, number::global_is_finite::<H>),
        ("encodeURIComponent", 1, string::encode_uri_component::<H>),
        ("decodeURIComponent", 1, string::decode_uri_component::<H>),
        ("unescape", 1, string::unescape::<H>),
        (
            "structuredClone",
            1,
            structured_clone::structured_clone::<H>,
        ),
    ] {
        let value = install_function(heap, builtins, name, length, handler);
        globals.insert(EcmaString::encode(name), value);
    }
    globals.insert(
        EcmaString::encode("Infinity"),
        crate::number_value(f64::INFINITY),
    );
    globals.insert(EcmaString::encode("NaN"), crate::number_value(f64::NAN));
    globals.insert(EcmaString::encode("undefined"), Value::UNDEFINED);
}
fn install_errors<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let error_prototype = push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.object_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    let error_to_string = install_function(heap, builtins, "toString", 0, error_to_string::<H>);
    define_data(heap, error_prototype, "toString", error_to_string);
    install_error_type(
        heap,
        globals,
        builtins,
        "Error",
        1,
        error_prototype,
        error_prototype,
    );
    for name in [
        "EvalError",
        "RangeError",
        "ReferenceError",
        "SyntaxError",
        "TypeError",
        "URIError",
        "AggregateError",
        "SuppressedError",
    ] {
        let prototype = push(
            heap,
            HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(error_prototype),
                extensible: true,
                boxed_primitive: None,
            },
        );
        let length = match name {
            "AggregateError" => 2,
            "SuppressedError" => 3,
            _ => 1,
        };
        install_error_type(
            heap,
            globals,
            builtins,
            name,
            length,
            prototype,
            error_prototype,
        );
    }
}
fn install_error_type<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    length: u32,
    prototype: Value,
    _error_prototype: Value,
) {
    let name_value = push(heap, HeapEntry::String(EcmaString::encode(name)));
    let empty = push(heap, HeapEntry::String(EcmaString::default()));
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!()
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode("name")),
        Property::Data {
            value: name_value,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    );
    properties.insert(
        PropertyKey::Named(EcmaString::encode("message")),
        Property::Data {
            value: empty,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    );
    let constructor =
        install_constructor_function(heap, builtins, name, length, error_constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    builtins.set_error_prototype(heap, constructor, prototype);
    globals.insert(EcmaString::encode(name), constructor);
}
fn define_error_field<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.define_descriptor(
        object,
        PropertyKey::Named(EcmaString::encode(name)),
        Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    )
}
fn error_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let id = machine
        .current_builtin_id()
        .ok_or_else(|| type_error("invalid error constructor"))?;
    let name = machine.intrinsics.builtins.get(id).name;
    let default_prototype = machine.intrinsics.error_prototype(id);
    let new_target = machine.current_new_target();
    let prototype = if new_target != Value::UNDEFINED {
        machine
            .constructed_prototype(new_target)
            .unwrap_or(default_prototype)
    } else {
        default_prototype
    };
    let object = if machine.inherits_from_prototype(this, prototype)? {
        this
    } else {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .map_err(EvalFailure::Runtime)?
    };
    let (message_index, options_index) = match name {
        "AggregateError" => {
            let errors = args.first().copied().unwrap_or(Value::UNDEFINED);
            let values = machine.iterable_values(errors)?;
            let array = allocate_array(machine, values)?;
            define_error_field(machine, object, "errors", array)?;
            (1, 2)
        }
        "SuppressedError" => {
            for (property, value) in [
                ("error", args.first().copied().unwrap_or(Value::UNDEFINED)),
                (
                    "suppressed",
                    args.get(1).copied().unwrap_or(Value::UNDEFINED),
                ),
            ] {
                define_error_field(machine, object, property, value)?;
            }
            (2, 3)
        }
        _ => (0, 1),
    };
    let message = args
        .get(message_index)
        .filter(|value| **value != Value::UNDEFINED)
        .map(|value| machine.to_string(*value))
        .transpose()?;
    if let Some(message) = &message {
        let text = allocate_string(machine, message.clone())?;
        define_error_field(machine, object, "message", text)?;
    }
    if let Some(options) = args
        .get(options_index)
        .copied()
        .filter(|value| *value != Value::UNDEFINED)
    {
        let cause_key = PropertyKey::Named(EcmaString::encode("cause"));
        if machine.internal_has_property(options, &cause_key)? {
            let cause = machine.get_named_property(options, "cause")?;
            define_error_field(machine, object, "cause", cause)?;
        }
    }
    let mut stack = bamts_bytecode::EcmaStringBuilder::new();
    stack.push_utf8(name);
    if let Some(message) = &message
        && !message.is_empty()
    {
        stack.push_utf8(": ");
        for &unit in message.as_units() {
            stack.push_unit(unit);
        }
    }
    stack.push_utf8("\n    at <bamts>");
    let stack = allocate_string(machine, stack.finish())?;
    define_error_field(machine, object, "stack", stack)?;
    Ok(BuiltinOutcome::Value(object))
}
fn error_to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let name_value = machine.get_named_property(this, "name")?;
    let name = machine.to_string(name_value)?;
    let message_value = machine.get_named_property(this, "message")?;
    let message = machine.to_string(message_value)?;
    let text = if name.is_empty() {
        message
    } else if message.is_empty() {
        name
    } else {
        let mut text = bamts_bytecode::EcmaStringBuilder::with_capacity(
            name.len_units()
                .saturating_add(message.len_units())
                .saturating_add(2),
        );
        for &unit in name.as_units() {
            text.push_unit(unit);
        }
        text.push_utf8(": ");
        for &unit in message.as_units() {
            text.push_unit(unit);
        }
        text.finish()
    };
    Ok(BuiltinOutcome::Value(allocate_string(machine, text)?))
}
impl<'a, H: Host> Machine<'a, H> {
    // ---- canonical internal methods -------------------------------------
    //
    // Every user-observable property, prototype, and extensibility operation
    // enters through exactly one of these entries. Each keyed method carries a
    // head Proxy check wrapped by `with_proxy_dispatch`, so trapped AND
    // transparent forwarding is depth-charged; otherwise it runs the ordinary
    // core. `[[Call]]` is `call_value`, `[[Construct]]` is
    // `internal_construct`, `[[HasProperty]]` is `internal_has_property`, and
    // `[[Delete]]` is `internal_delete` (defined beside the dispatch in
    // lib.rs).

    /// `[[Get]]` — the single canonical property read.
    pub(crate) fn internal_get(
        &mut self,
        object: Value,
        key: &PropertyKey,
        receiver: Value,
    ) -> Result<Value, EvalFailure> {
        if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| proxy::get(machine, object, key, receiver));
        }
        let outcome = if let PropertyKey::Named(name) = key
            && let Ok(name) = name.to_utf8_strict()
            && name.is_ascii()
        {
            self.resolve_get_ascii(object, &name, receiver)?
        } else {
            self.resolve_get(object, key, receiver)?
        };
        match outcome {
            GetOutcome::Value(value) => Ok(value),
            GetOutcome::Text(text) => self
                .allocate(HeapEntry::String(text))
                .map_err(EvalFailure::Runtime),
            GetOutcome::Getter(getter) => self.call_value(getter, receiver, &[]),
        }
    }

    /// `[[Set]]` — the single canonical property write. Returns a boolean on
    /// every path; `false` is data, not an error. Throw-on-false belongs to
    /// the language operation, never here.
    pub(crate) fn internal_set(
        &mut self,
        object: Value,
        key: PropertyKey,
        value: Value,
        receiver: Value,
    ) -> Result<bool, EvalFailure> {
        if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(object) {
            return self
                .with_proxy_dispatch(|machine| proxy::set(machine, object, key, value, receiver));
        }
        self.resolve_set(object, key, value, receiver)
    }

    /// `[[GetOwnProperty]]` returning the transient descriptor record.
    pub(crate) fn internal_get_own_property(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<Option<property_descriptor::PropertyDescriptor>, EvalFailure> {
        if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(object) {
            return self
                .with_proxy_dispatch(|machine| proxy::get_own_property(machine, object, key));
        }
        Ok(self
            .own_descriptor(object, key)?
            .map(property_descriptor::descriptor_from_property))
    }

    /// `[[DefineOwnProperty]]` — OrdinaryDefineOwnProperty for non-proxy
    /// receivers, validating and applying through the single `define_descriptor`
    /// seam.
    pub(crate) fn internal_define_own_property(
        &mut self,
        object: Value,
        key: PropertyKey,
        descriptor: property_descriptor::PropertyDescriptor,
    ) -> Result<bool, EvalFailure> {
        if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| {
                proxy::define_own_property(machine, object, key, descriptor)
            });
        }
        let current = self.own_descriptor(object, &key)?;
        let extensible = property_descriptor::is_extensible(self, object)?;
        property_descriptor::validate_and_apply_property_descriptor(
            self,
            Some((object, key)),
            extensible,
            descriptor,
            current,
        )
    }

    /// `[[GetPrototypeOf]]`.
    pub(crate) fn internal_get_prototype_of(
        &mut self,
        object: Value,
    ) -> Result<Option<Value>, EvalFailure> {
        if self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| proxy::get_prototype_of(machine, object));
        }
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Ok(None);
        };
        self.prototype_index(index)?.map_or(Ok(None), |prototype| {
            let slot = u32::try_from(prototype + 1).map_err(|_| {
                EvalFailure::Throw(ThrowOrigin::RangeError {
                    operation: "prototype heap slot exceeds u32",
                })
            })?;
            Ok(Some(Value::heap_ref(
                bamts_native::SlotId::from_parts(crate::RUNTIME_HEAP_SEGMENT, slot)
                    .expect("runtime prototype slot is nonzero"),
            )))
        })
    }

    /// `[[SetPrototypeOf]]` — OrdinarySetPrototypeOf with the SameValue fast
    /// path, extensibility gate, and cycle guard.
    pub(crate) fn internal_set_prototype_of(
        &mut self,
        object: Value,
        prototype: Option<Value>,
    ) -> Result<bool, EvalFailure> {
        if self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| {
                proxy::set_prototype_of(machine, object, prototype)
            });
        }
        let current = self
            .internal_get_prototype_of(object)?
            .unwrap_or(Value::NULL);
        let proposed = prototype.unwrap_or(Value::NULL);
        if self.same_value(proposed, current) {
            return Ok(true);
        }
        if !property_descriptor::is_extensible(self, object)? {
            return Ok(false);
        }
        let mut node = proposed;
        while !matches!(node.decode(), Some(Decoded::Null)) {
            if node == object {
                return Ok(false);
            }
            match self.internal_get_prototype_of(node)? {
                Some(next) => node = next,
                None => break,
            }
        }
        self.set_prototype(object, proposed)?;
        Ok(true)
    }

    /// `[[IsExtensible]]`.
    pub(crate) fn internal_is_extensible(&mut self, object: Value) -> Result<bool, EvalFailure> {
        if self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| proxy::is_extensible(machine, object));
        }
        property_descriptor::is_extensible(self, object)
    }

    /// `[[PreventExtensions]]`.
    pub(crate) fn internal_prevent_extensions(
        &mut self,
        object: Value,
    ) -> Result<bool, EvalFailure> {
        if self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| proxy::prevent_extensions(machine, object));
        }
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        let extensible = match &mut self.heap[index] {
            HeapEntry::Object { extensible, .. }
            | HeapEntry::Generator { extensible, .. }
            | HeapEntry::AsyncGenerator { extensible, .. }
            | HeapEntry::AsyncFromSync { extensible, .. }
            | HeapEntry::Script { extensible, .. }
            | HeapEntry::Array { extensible, .. }
            | HeapEntry::Function { extensible, .. }
            | HeapEntry::NativeFunction { extensible, .. }
            | HeapEntry::RegExp { extensible, .. }
            | HeapEntry::Date { extensible, .. }
            | HeapEntry::BuiltinIterator { extensible, .. }
            | HeapEntry::Collection { extensible, .. }
            | HeapEntry::TypedArray { extensible, .. }
            | HeapEntry::ArrayBuffer { extensible, .. }
            | HeapEntry::SharedArrayBuffer { extensible, .. }
            | HeapEntry::DataView { extensible, .. }
            | HeapEntry::Promise { extensible, .. }
            | HeapEntry::WeakRef { extensible, .. }
            | HeapEntry::FinalizationRegistry { extensible, .. }
            | HeapEntry::DisposableStack { extensible, .. }
            | HeapEntry::ProxyRevoker { extensible, .. }
            | HeapEntry::Timeout { extensible, .. } => extensible,
            HeapEntry::ModuleNamespace { .. }
            | HeapEntry::ExternalModuleNamespace { .. }
            | HeapEntry::Iterator { .. } => return Ok(true),
            _ => return Ok(false),
        };
        *extensible = false;
        Ok(true)
    }

    /// `[[OwnPropertyKeys]]` — integer indices ascending, then strings in
    /// insertion order, then symbols in insertion order; proxies dispatch the
    /// ownKeys trap and preserve its order verbatim.
    pub(crate) fn internal_own_property_keys(
        &mut self,
        object: Value,
    ) -> Result<Vec<PropertyKey>, EvalFailure> {
        if self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| proxy::own_property_keys(machine, object));
        }
        // The string-exotic virtual-index merge lives in the ordinary core so
        // trap order stays verbatim for proxies.
        object_statics::own_keys(self, object)
    }
    fn call_truthy(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) -> Result<bool, EvalFailure> {
        let result = self.call_value(callee, this_value, arguments)?;
        Ok(self.to_boolean(result))
    }
    #[cfg(test)]
    fn mark_frozen(&mut self, value: Value) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(());
        };
        let (properties, extensible) = match &mut self.heap[index] {
            HeapEntry::Object {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Array {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Function {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Script {
                properties,
                extensible,
                ..
            }
            | HeapEntry::NativeFunction {
                properties,
                extensible,
                ..
            }
            | HeapEntry::RegExp {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Date {
                properties,
                extensible,
                ..
            }
            | HeapEntry::BuiltinIterator {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Collection {
                properties,
                extensible,
                ..
            }
            | HeapEntry::TypedArray {
                properties,
                extensible,
                ..
            }
            | HeapEntry::ArrayBuffer {
                properties,
                extensible,
                ..
            }
            | HeapEntry::SharedArrayBuffer {
                properties,
                extensible,
                ..
            }
            | HeapEntry::DataView {
                properties,
                extensible,
                ..
            }
            | HeapEntry::WeakRef {
                properties,
                extensible,
                ..
            }
            | HeapEntry::FinalizationRegistry {
                properties,
                extensible,
                ..
            }
            | HeapEntry::DisposableStack {
                properties,
                extensible,
                ..
            }
            | HeapEntry::ProxyRevoker {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Timeout {
                properties,
                extensible,
                ..
            } => (properties, extensible),
            HeapEntry::ProcessEnv { extensible, .. } => {
                *extensible = false;
                return Ok(());
            }
            _ => return Ok(()),
        };
        *extensible = false;
        for (_, property) in &mut properties.0 {
            match property {
                Property::Data {
                    writable,
                    configurable,
                    ..
                } => {
                    *writable = false;
                    *configurable = false;
                }
                Property::Accessor { configurable, .. } => *configurable = false,
            }
        }
        Ok(())
    }
    pub(crate) fn own_descriptor(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<Option<Property>, EvalFailure> {
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Ok(None);
        };
        let properties = match &self.heap[index] {
            HeapEntry::ModuleNamespace { module } => {
                let PropertyKey::Named(name) = key else {
                    return Ok(None);
                };
                return self
                    .namespace_export(*module, name)
                    .map(|value| {
                        value.map(|value| Property::Data {
                            value,
                            writable: true,
                            enumerable: true,
                            configurable: false,
                        })
                    })
                    .map_err(EvalFailure::Runtime);
            }
            HeapEntry::Array {
                elements,
                properties,
                length_writable,
                ..
            } => {
                if matches!(key, PropertyKey::Named(name) if name.eq_ascii("length")) {
                    return Ok(Some(Property::Data {
                        value: crate::number_value(elements.len() as f64),
                        writable: *length_writable,
                        enumerable: false,
                        configurable: false,
                    }));
                }
                if let Some(property) = properties.get(key) {
                    return Ok(Some(property.clone()));
                }
                if let PropertyKey::Named(name) = key
                    && let Some(offset) = crate::array_index(name)
                    && let Some(value) = elements.get(offset as usize)
                    && *value != Value::HOLE
                {
                    return Ok(Some(Property::Data {
                        value: *value,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    }));
                }
                return Ok(None);
            }
            HeapEntry::TypedArray { properties, .. } => {
                if let PropertyKey::Named(name) = key
                    && let Some(typed_index) = typedarray_all::typed_array_index(name)
                {
                    let view = self.value_for_runtime_index(index)?;
                    let bounds = typedarray_all::typed_array_bounds(self, view)?;
                    return Ok(match typed_index {
                        Some(offset) if !bounds.out_of_bounds && offset < bounds.element_length => {
                            Some(Property::Data {
                                value: typedarray_all::read_element(self, view, offset)?,
                                writable: true,
                                enumerable: true,
                                configurable: true,
                            })
                        }
                        _ => None,
                    });
                }
                properties
            }
            HeapEntry::Object { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Timeout { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. } => properties,
            _ => return Ok(None),
        };
        Ok(properties.get(key).cloned())
    }
    /// ECMA-262 §7.2.10 SameValue(x, y) — like `same_value_zero` except that
    /// `+0` and `-0` are distinct. Mirrors the helper in `object.rs`; kept here
    /// so `validate_property_redefinition` does not depend on a private free
    /// function in another module.
    fn same_value(&self, left: Value, right: Value) -> bool {
        match (left.decode(), right.decode()) {
            (Some(Decoded::Number(a)), Some(Decoded::Number(b))) => {
                if a.is_nan() && b.is_nan() {
                    return true;
                }
                if a == 0.0 && b == 0.0 {
                    return a.is_sign_positive() == b.is_sign_positive();
                }
                a == b
            }
            (Some(Decoded::Number(a)), Some(Decoded::Int32(b)))
            | (Some(Decoded::Int32(b)), Some(Decoded::Number(a))) => {
                // Interpret the two's-complement u32 payload as a signed i32.
                let b_f64 = f64::from(b as i32);
                if a == 0.0 && b_f64 == 0.0 {
                    return a.is_sign_positive();
                }
                a == b_f64
            }
            _ => self.same_value_zero(left, right),
        }
    }
    fn validate_property_redefinition(
        &self,
        current: Option<&Property>,
        next: &Property,
    ) -> Result<(), EvalFailure> {
        let Some(current) = current else {
            return Ok(());
        };
        if current.configurable() {
            return Ok(());
        }
        if next.configurable() {
            return Err(type_error(
                "Cannot redefine property: non-configurable property cannot be made configurable",
            ));
        }
        if next.enumerable() != current.enumerable() {
            return Err(type_error(
                "Cannot redefine property: cannot change enumerability of non-configurable property",
            ));
        }
        match (current, next) {
            (
                Property::Data {
                    writable, value, ..
                },
                Property::Data {
                    writable: next_writable,
                    value: next_value,
                    ..
                },
            ) => {
                if !*writable {
                    if *next_writable {
                        return Err(type_error(
                            "Cannot redefine property: cannot make non-writable property writable",
                        ));
                    }
                    if !self.same_value(*next_value, *value) {
                        return Err(type_error(
                            "Cannot redefine property: cannot change value of non-writable property",
                        ));
                    }
                }
            }
            (Property::Data { .. }, Property::Accessor { .. }) => {
                return Err(type_error(
                    "Cannot redefine property: cannot convert non-configurable data property to accessor",
                ));
            }
            (Property::Accessor { .. }, Property::Data { .. }) => {
                return Err(type_error(
                    "Cannot redefine property: cannot convert non-configurable accessor property to data",
                ));
            }
            (
                Property::Accessor { getter, setter, .. },
                Property::Accessor {
                    getter: next_getter,
                    setter: next_setter,
                    ..
                },
            ) => {
                if !self.same_value(
                    next_getter.unwrap_or(Value::UNDEFINED),
                    getter.unwrap_or(Value::UNDEFINED),
                ) {
                    return Err(type_error(
                        "Cannot redefine property: cannot change getter of non-configurable accessor property",
                    ));
                }
                if !self.same_value(
                    next_setter.unwrap_or(Value::UNDEFINED),
                    setter.unwrap_or(Value::UNDEFINED),
                ) {
                    return Err(type_error(
                        "Cannot redefine property: cannot change setter of non-configurable accessor property",
                    ));
                }
            }
        }
        Ok(())
    }
    pub(crate) fn define_descriptor(
        &mut self,
        object: Value,
        key: PropertyKey,
        descriptor: Property,
    ) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Err(type_error("Object.defineProperty called on non-object"));
        };
        if let PropertyKey::Named(name) = &key
            && let Some(typed_index) = typedarray_all::typed_array_index(name)
            && matches!(self.heap[index], HeapEntry::TypedArray { .. })
        {
            let Some(offset) = typed_index else {
                return Err(type_error("Invalid typed array index descriptor"));
            };
            let view = self.value_for_runtime_index(index)?;
            let bounds = typedarray_all::typed_array_bounds(self, view)?;
            if bounds.out_of_bounds || offset >= bounds.element_length {
                return Err(type_error("Invalid typed array index descriptor"));
            }
            let Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            } = descriptor
            else {
                return Err(type_error("Invalid typed array index descriptor"));
            };
            return self.set_data_property_key(object, key, value);
        }
        if matches!(&key, PropertyKey::Named(name) if name.eq_ascii("length"))
            && matches!(self.heap[index], HeapEntry::Array { .. })
        {
            let Property::Data {
                value,
                writable,
                enumerable: false,
                configurable: false,
            } = descriptor
            else {
                return Err(type_error("Cannot redefine array length"));
            };
            let length = crate::exact_array_length(value)
                .ok_or_else(|| range_error("define array length"))?;
            let (old_length, old_property_bytes, length_writable) = match &self.heap[index] {
                HeapEntry::Array {
                    elements,
                    properties,
                    length_writable,
                    ..
                } => (elements.len(), properties.charge_bytes(), *length_writable),
                _ => unreachable!("array checked above"),
            };
            if writable && !length_writable {
                return Err(type_error("Cannot make array length writable"));
            }
            let growth = length
                .saturating_sub(old_length)
                .saturating_mul(std::mem::size_of::<Value>());
            self.charge_slot(index, growth)
                .map_err(EvalFailure::Runtime)?;
            let result = {
                let HeapEntry::Array {
                    elements,
                    properties,
                    length_writable,
                    ..
                } = &mut self.heap[index]
                else {
                    unreachable!("array checked above");
                };
                let result = define_array_length(elements, properties, *length_writable, length);
                if !writable {
                    *length_writable = false;
                }
                result
            };
            let (new_length, new_property_bytes) = match &self.heap[index] {
                HeapEntry::Array {
                    elements,
                    properties,
                    ..
                } => (elements.len(), properties.charge_bytes()),
                _ => unreachable!("array checked above"),
            };
            let released = old_length
                .saturating_sub(new_length)
                .saturating_mul(std::mem::size_of::<Value>())
                .saturating_add(old_property_bytes.saturating_sub(new_property_bytes));
            let released = if result.is_err() {
                released.saturating_add(growth)
            } else {
                released
            };
            self.refund_slot(index, released);
            return result;
        }
        let (extensible, exists, property_growth, property_refund, element_growth, array_index) =
            match &self.heap[index] {
                HeapEntry::Object {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::Function {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::Script {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::NativeFunction {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::RegExp {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::Date {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::BuiltinIterator {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::Collection {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::TypedArray {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::ArrayBuffer {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::SharedArrayBuffer {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::DataView {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::WeakRef {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::FinalizationRegistry {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::DisposableStack {
                    properties,
                    extensible,
                    ..
                }
                | HeapEntry::Timeout {
                    properties,
                    extensible,
                    ..
                } => {
                    let exists = properties.contains_key(&key);
                    let (property_growth, property_refund) =
                        property_definition_charges(properties, &key, &descriptor);
                    (
                        *extensible,
                        exists,
                        property_growth,
                        property_refund,
                        0,
                        None,
                    )
                }
                HeapEntry::Array {
                    elements,
                    properties,
                    extensible,
                    length_writable,
                    ..
                } => {
                    let array_index = key
                        .as_string()
                        .and_then(crate::array_index)
                        .map(|offset| offset as usize);
                    let exists = properties.contains_key(&key)
                        || array_index.is_some_and(|offset| {
                            elements
                                .get(offset)
                                .is_some_and(|element| *element != Value::HOLE)
                        });
                    if !*extensible && !exists {
                        return Err(type_error(
                            "Cannot define property, object is not extensible",
                        ));
                    }
                    if let Some(offset) = array_index
                        && offset >= elements.len()
                        && !*length_writable
                    {
                        return Err(type_error(
                            "Cannot define index beyond non-writable array length",
                        ));
                    }
                    let element_growth = array_index.map_or(0, |offset| {
                        (offset + 1)
                            .saturating_sub(elements.len())
                            .saturating_mul(std::mem::size_of::<Value>())
                    });
                    let (property_growth, property_refund) =
                        property_definition_charges(properties, &key, &descriptor);
                    (
                        *extensible,
                        exists,
                        property_growth,
                        property_refund,
                        element_growth,
                        array_index,
                    )
                }
                _ => return Err(type_error("Object.defineProperty called on non-object")),
            };
        if !extensible && !exists {
            return Err(type_error(
                "Cannot define property, object is not extensible",
            ));
        }
        let current = self.own_descriptor(object, &key)?;
        self.validate_property_redefinition(current.as_ref(), &descriptor)?;
        self.charge_slot(index, property_growth.saturating_add(element_growth))
            .map_err(EvalFailure::Runtime)?;
        match &mut self.heap[index] {
            HeapEntry::Array {
                elements,
                properties,
                length_writable,
                ..
            } => {
                if let Some(offset) = array_index {
                    if elements.len() <= offset {
                        crate::array_set_length(
                            elements,
                            properties,
                            *length_writable,
                            crate::number_value((offset + 1) as f64),
                            "define array index",
                        )?;
                    }
                    elements[offset] = Value::HOLE;
                }
                properties.insert(key, descriptor);
            }
            HeapEntry::Object { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::TypedArray { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Timeout { properties, .. } => {
                properties.insert(key, descriptor);
            }
            _ => unreachable!("validated object cannot change heap entry kind"),
        }
        self.refund_slot(index, property_refund);
        Ok(())
    }
    pub(crate) fn define_descriptor_batch<const N: usize>(
        &mut self,
        object: Value,
        descriptors: [(PropertyKey, Property); N],
    ) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Err(type_error("Object.defineProperty called on non-object"));
        };
        let extensible = match &self.heap[index] {
            HeapEntry::Object { extensible, .. }
            | HeapEntry::Function { extensible, .. }
            | HeapEntry::Script { extensible, .. }
            | HeapEntry::NativeFunction { extensible, .. }
            | HeapEntry::RegExp { extensible, .. }
            | HeapEntry::Date { extensible, .. }
            | HeapEntry::BuiltinIterator { extensible, .. }
            | HeapEntry::Collection { extensible, .. }
            | HeapEntry::TypedArray { extensible, .. }
            | HeapEntry::ArrayBuffer { extensible, .. }
            | HeapEntry::SharedArrayBuffer { extensible, .. }
            | HeapEntry::DataView { extensible, .. }
            | HeapEntry::Timeout { extensible, .. }
            | HeapEntry::DisposableStack { extensible, .. }
            | HeapEntry::Array { extensible, .. } => *extensible,
            _ => return Err(type_error("Object.defineProperty called on non-object")),
        };
        let mut growth = 0usize;
        let mut refund = 0usize;
        for (offset, (key, descriptor)) in descriptors.iter().enumerate() {
            if descriptors[..offset]
                .iter()
                .any(|(existing, _)| existing == key)
            {
                return Err(type_error("duplicate property in atomic descriptor batch"));
            }
            if matches!(&self.heap[index], HeapEntry::Array { .. })
                && matches!(key, PropertyKey::Named(name) if name.eq_ascii("length") || crate::array_index(name).is_some())
            {
                return Err(type_error(
                    "atomic descriptor batch cannot contain array index properties",
                ));
            }
            if matches!(&self.heap[index], HeapEntry::TypedArray { .. })
                && matches!(key, PropertyKey::Named(name) if typedarray_all::typed_array_index(name).is_some())
            {
                return Err(type_error(
                    "atomic descriptor batch cannot contain typed array index properties",
                ));
            }
            let current = self.own_descriptor(object, key)?;
            if !extensible && current.is_none() {
                return Err(type_error(
                    "Cannot define property, object is not extensible",
                ));
            }
            self.validate_property_redefinition(current.as_ref(), descriptor)?;
            let (added, removed) = match &self.heap[index] {
                HeapEntry::Object { properties, .. }
                | HeapEntry::Function { properties, .. }
                | HeapEntry::Script { properties, .. }
                | HeapEntry::NativeFunction { properties, .. }
                | HeapEntry::RegExp { properties, .. }
                | HeapEntry::Date { properties, .. }
                | HeapEntry::BuiltinIterator { properties, .. }
                | HeapEntry::Collection { properties, .. }
                | HeapEntry::TypedArray { properties, .. }
                | HeapEntry::ArrayBuffer { properties, .. }
                | HeapEntry::SharedArrayBuffer { properties, .. }
                | HeapEntry::DataView { properties, .. }
                | HeapEntry::Timeout { properties, .. }
                | HeapEntry::DisposableStack { properties, .. }
                | HeapEntry::Array { properties, .. } => {
                    property_definition_charges(properties, key, descriptor)
                }
                _ => unreachable!("validated object cannot change heap entry kind"),
            };
            growth = growth.saturating_add(added);
            refund = refund.saturating_add(removed);
        }
        self.charge_slot(index, growth)
            .map_err(EvalFailure::Runtime)?;
        let properties = match &mut self.heap[index] {
            HeapEntry::Object { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::TypedArray { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. }
            | HeapEntry::Timeout { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Array { properties, .. } => properties,
            _ => unreachable!("validated object cannot change heap entry kind"),
        };
        for (key, descriptor) in descriptors {
            properties.insert(key, descriptor);
        }
        self.refund_slot(index, refund);
        Ok(())
    }
    fn observable_property_key(&mut self, key: Value) -> Result<PropertyKey, EvalFailure> {
        let primitive = self.coerce_primitive_observable(key, true)?;
        Ok(
            match self.runtime_slot(primitive).map_err(EvalFailure::Runtime)? {
                Some(index) if matches!(self.heap[index], HeapEntry::Symbol { .. }) => {
                    PropertyKey::Symbol(index as u32)
                }
                Some(index) if matches!(self.heap[index], HeapEntry::PrivateName { .. }) => {
                    PropertyKey::Private(index as u32)
                }
                _ => PropertyKey::Named(self.to_string(primitive)?),
            },
        )
    }
    pub(crate) fn load_own_descriptor_slot(
        &mut self,
        object: Value,
        key: Value,
        slot: DescriptorSlot,
    ) -> Result<Value, EvalFailure> {
        if matches!(object.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return Err(type_error("Cannot convert undefined or null to object"));
        }
        let key = self.observable_property_key(key)?;
        let Some(property) = self.own_descriptor(object, &key)? else {
            return Ok(Value::UNDEFINED);
        };
        Ok(match (property, slot) {
            (Property::Data { value, .. }, DescriptorSlot::Value) => value,
            (Property::Accessor { getter, .. }, DescriptorSlot::Getter) => {
                getter.unwrap_or(Value::UNDEFINED)
            }
            (Property::Accessor { setter, .. }, DescriptorSlot::Setter) => {
                setter.unwrap_or(Value::UNDEFINED)
            }
            _ => Value::UNDEFINED,
        })
    }
    pub(crate) fn define_own_descriptor_slot(
        &mut self,
        object: Value,
        key: Value,
        src: Value,
        slot: DescriptorSlot,
    ) -> Result<(), EvalFailure> {
        let key = self.observable_property_key(key)?;
        let half = (src != Value::UNDEFINED).then_some(src);
        let updated = match (self.own_descriptor(object, &key)?, slot) {
            (None, DescriptorSlot::Value) => Property::Data {
                value: src,
                writable: true,
                enumerable: false,
                configurable: true,
            },
            (None, DescriptorSlot::Getter) => Property::Accessor {
                getter: half,
                setter: None,
                enumerable: false,
                configurable: true,
            },
            (None, DescriptorSlot::Setter) => Property::Accessor {
                getter: None,
                setter: half,
                enumerable: false,
                configurable: true,
            },
            (
                Some(Property::Data {
                    writable,
                    enumerable,
                    configurable,
                    ..
                }),
                DescriptorSlot::Value,
            ) => Property::Data {
                value: src,
                writable,
                enumerable,
                configurable,
            },
            (
                Some(Property::Accessor {
                    setter,
                    enumerable,
                    configurable,
                    ..
                }),
                DescriptorSlot::Getter,
            ) => Property::Accessor {
                getter: half,
                setter,
                enumerable,
                configurable,
            },
            (
                Some(Property::Accessor {
                    getter,
                    enumerable,
                    configurable,
                    ..
                }),
                DescriptorSlot::Setter,
            ) => Property::Accessor {
                getter,
                setter: half,
                enumerable,
                configurable,
            },
            _ => return Err(type_error("decorator replacement changes descriptor shape")),
        };
        self.define_descriptor(object, key, updated)
    }
}
fn property_definition_charges(
    properties: &PropertyMap,
    key: &PropertyKey,
    descriptor: &Property,
) -> (usize, usize) {
    match properties.get(key) {
        None => (
            key.charge_bytes().saturating_add(descriptor.charge_bytes()),
            0,
        ),
        Some(existing) => {
            let old = existing.charge_bytes();
            let new = descriptor.charge_bytes();
            if new >= old {
                (new.saturating_sub(old), 0)
            } else {
                (0, old.saturating_sub(new))
            }
        }
    }
}
#[cfg(test)]
mod tests {
    use super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;
    fn inherited_message_getter<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error(
            "inherited message getter ran before derived fields",
        ))
    }
    #[test]
    fn valita_style_message_getter_does_not_run_before_private_issue_field() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let getter = install_function(
            &mut machine.heap,
            &mut machine.intrinsics.builtins,
            "inherited message getter",
            0,
            inherited_message_getter::<TestHost>,
        );
        let mut properties = PropertyMap::default();
        properties.insert(
            PropertyKey::Named(EcmaString::encode("message")),
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
        let error = machine.intrinsics.global("Error").expect("Error exists");
        let error_prototype = machine
            .get_named_property(error, "prototype")
            .expect("Error.prototype exists");
        let prototype = machine
            .allocate(HeapEntry::Object {
                properties,
                prototype: Some(error_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("prototype allocation succeeds");
        let receiver = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("derived receiver allocation succeeds");
        let initialized = machine
            .call_value(error, receiver, &[])
            .expect("Error does not read the inherited message getter");
        assert_eq!(initialized, receiver);
        let stack = machine
            .get_named_property(receiver, "stack")
            .expect("Error creates stack on the existing receiver");
        assert!(
            machine
                .to_string(stack)
                .expect("stack is string")
                .eq_ascii("Error\n    at <bamts>")
        );
        let unrelated = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("unrelated receiver allocation succeeds");
        assert_ne!(
            machine
                .call_value(error, unrelated, &[])
                .expect("Error allocates for an unrelated receiver"),
            unrelated
        );
        let receiver_with_message = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("second derived receiver allocation succeeds");
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("issue")))
            .expect("message allocation succeeds");
        assert_eq!(
            machine
                .call_value(error, receiver_with_message, &[message])
                .expect("Error initializes the second derived receiver"),
            receiver_with_message
        );
        let stack = machine
            .get_named_property(receiver_with_message, "stack")
            .expect("Error creates the second stack");
        assert!(
            machine
                .to_string(stack)
                .expect("stack is string")
                .eq_ascii("Error: issue\n    at <bamts>")
        );
    }
    #[test]
    fn global_infinity_descriptor_is_frozen_with_exact_value() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let key = PropertyKey::Named(EcmaString::encode("Infinity"));
        let descriptor = machine
            .own_descriptor(global_this, &key)
            .expect("descriptor lookup succeeds")
            .expect("Infinity is defined on globalThis");
        match descriptor {
            Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            } => {
                assert!(!writable, "Infinity must be non-writable");
                assert!(!enumerable, "Infinity must be non-enumerable");
                assert!(!configurable, "Infinity must be non-configurable");
                assert!(
                    value_number(value).is_infinite() && value_number(value).is_sign_positive(),
                    "Infinity value must be +Infinity"
                );
            }
            Property::Accessor { .. } => panic!("Infinity must be a data property"),
        }
    }
    #[test]
    fn global_nan_descriptor_is_frozen_with_exact_value() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let key = PropertyKey::Named(EcmaString::encode("NaN"));
        let descriptor = machine
            .own_descriptor(global_this, &key)
            .expect("descriptor lookup succeeds")
            .expect("NaN is defined on globalThis");
        match descriptor {
            Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            } => {
                assert!(!writable, "NaN must be non-writable");
                assert!(!enumerable, "NaN must be non-enumerable");
                assert!(!configurable, "NaN must be non-configurable");
                assert!(value_number(value).is_nan(), "NaN value must be NaN");
            }
            Property::Accessor { .. } => panic!("NaN must be a data property"),
        }
    }
    #[test]
    fn global_undefined_descriptor_is_frozen() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let key = PropertyKey::Named(EcmaString::encode("undefined"));
        let descriptor = machine
            .own_descriptor(global_this, &key)
            .expect("descriptor lookup succeeds")
            .expect("undefined is defined on globalThis");
        assert!(matches!(
            descriptor,
            Property::Data {
                value: Value::UNDEFINED,
                writable: false,
                enumerable: false,
                configurable: false,
            }
        ));
    }
    #[test]
    fn global_infinity_and_nan_are_stable_across_reads() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let first_infinity = machine
            .get_named_property(global_this, "Infinity")
            .expect("Infinity is readable");
        let second_infinity = machine
            .get_named_property(global_this, "Infinity")
            .expect("Infinity is readable on second read");
        assert_eq!(
            first_infinity, second_infinity,
            "Infinity must be stable across reads"
        );
        let first_nan = machine
            .get_named_property(global_this, "NaN")
            .expect("NaN is readable");
        let second_nan = machine
            .get_named_property(global_this, "NaN")
            .expect("NaN is readable on second read");
        assert_eq!(first_nan, second_nan, "NaN must be stable across reads");
    }
    #[test]
    fn atomics_is_an_object_with_correct_to_string_tag() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let atomics = machine
            .intrinsics
            .global("Atomics")
            .expect("Atomics is installed");
        let object_to_string = machine.intrinsics.object_to_string();
        let result = machine
            .call_value(object_to_string, atomics, &[])
            .expect("Object.prototype.toString.call(Atomics) succeeds");
        assert!(
            machine
                .string_value(result)
                .is_some_and(|text| text.eq_ascii("[object Atomics]")),
            "Atomics must report [object Atomics]"
        );
    }
    #[test]
    fn atomics_to_string_tag_descriptor_matches_namespace_tag() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let atomics = machine
            .intrinsics
            .global("Atomics")
            .expect("Atomics is installed");
        let tag_key = PropertyKey::Symbol(heap_index(
            machine.intrinsics.builtins.symbol_to_string_tag(),
        ) as u32);
        let descriptor = machine
            .own_descriptor(atomics, &tag_key)
            .expect("descriptor lookup succeeds")
            .expect("Atomics has Symbol.toStringTag");
        match descriptor {
            Property::Data {
                value,
                writable,
                enumerable,
                configurable,
            } => {
                assert!(!writable, "Atomics toStringTag must be non-writable");
                assert!(!enumerable, "Atomics toStringTag must be non-enumerable");
                assert!(configurable, "Atomics toStringTag must be configurable");
                assert!(
                    machine
                        .string_value(value)
                        .is_some_and(|text| text.eq_ascii("Atomics")),
                    "Atomics toStringTag value must be 'Atomics'"
                );
            }
            Property::Accessor { .. } => panic!("Atomics toStringTag must be a data property"),
        }
    }
    #[test]
    fn atomics_global_binding_is_writable_and_configurable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        let key = PropertyKey::Named(EcmaString::encode("Atomics"));
        let descriptor = machine
            .own_descriptor(global_this, &key)
            .expect("descriptor lookup succeeds")
            .expect("Atomics is defined on globalThis");
        match descriptor {
            Property::Data {
                writable,
                enumerable,
                configurable,
                ..
            } => {
                assert!(writable, "Atomics global binding must be writable");
                assert!(!enumerable, "Atomics global binding must be non-enumerable");
                assert!(configurable, "Atomics global binding must be configurable");
            }
            Property::Accessor { .. } => panic!("Atomics global binding must be a data property"),
        }
    }
    #[test]
    fn atomics_claims_exactly_the_methods_it_implements() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let machine = Machine::new(&module, &mut host, Limits::default());
        let atomics = machine
            .intrinsics
            .global("Atomics")
            .expect("Atomics is installed");
        let keys = machine
            .own_property_keys(atomics)
            .expect("Atomics is an object");
        let mut method_names: Vec<_> = keys
            .into_iter()
            .filter_map(|key| match key {
                PropertyKey::Named(name) => Some(name.to_utf8_lossy()),
                _ => None,
            })
            .collect();
        method_names.sort();
        assert_eq!(
            method_names,
            [
                "add",
                "and",
                "compareExchange",
                "exchange",
                "isLockFree",
                "load",
                "notify",
                "or",
                "pause",
                "store",
                "sub",
                "wait",
                "waitAsync",
                "xor",
            ]
        );
    }
    #[test]
    fn copied_globals_are_non_enumerable_and_still_readable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("globalThis is installed");
        assert!(
            machine.enumerable_keys(global_this).unwrap().is_empty(),
            "fresh globalThis must not expose any copied globals to Object.keys/for...in"
        );
        for name in [
            "Atomics",
            "console",
            "process",
            "Object",
            "globalThis",
            "global",
        ] {
            assert!(
                machine.get_named_property(global_this, name).is_ok(),
                "{name} must still be directly accessible on globalThis"
            );
        }
    }
    #[test]
    fn suppressed_error_constructor_keeps_both_errors_non_enumerable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine
            .intrinsics
            .global("SuppressedError")
            .expect("SuppressedError exists");
        assert_eq!(
            machine.get_named_property(constructor, "length").unwrap(),
            Value::int32(3)
        );
        let error = Value::int32(11);
        let suppressed = Value::int32(22);
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("outer")))
            .expect("message allocation succeeds");
        let result = machine
            .construct_value(constructor, &[error, suppressed, message])
            .expect("SuppressedError construction succeeds");
        assert_eq!(machine.get_named_property(result, "error").unwrap(), error);
        assert_eq!(
            machine.get_named_property(result, "suppressed").unwrap(),
            suppressed
        );
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .unwrap();
        assert!(machine.inherits_from_prototype(result, prototype).unwrap());
        for (name, expected) in [("error", error), ("suppressed", suppressed)] {
            let descriptor = machine
                .own_descriptor(result, &PropertyKey::Named(EcmaString::encode(name)))
                .unwrap()
                .expect("SuppressedError has an own error field");
            assert!(matches!(
                descriptor,
                Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                } if value == expected
            ));
        }
    }
    #[test]
    fn error_own_fields_are_non_enumerable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let error_constructor = machine.intrinsics.global("Error").expect("Error exists");
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("boom")))
            .expect("message allocation succeeds");
        let error = machine
            .construct_value(error_constructor, &[message])
            .expect("Error construction succeeds");
        assert!(
            machine.enumerable_keys(error).unwrap().is_empty(),
            "Error own fields must not appear in Object.keys / for...in"
        );
        let descriptor = machine
            .own_descriptor(error, &PropertyKey::Named(EcmaString::encode("message")))
            .expect("descriptor lookup succeeds")
            .expect("Error has an own message property");
        assert!(
            matches!(
                descriptor,
                Property::Data {
                    writable: true,
                    enumerable: false,
                    configurable: true,
                    ..
                }
            ),
            "message must be a non-enumerable writable configurable data property"
        );
        let stack = machine
            .own_descriptor(error, &PropertyKey::Named(EcmaString::encode("stack")))
            .expect("descriptor lookup succeeds")
            .expect("Error has an own stack property");
        assert!(
            matches!(
                stack,
                Property::Accessor {
                    getter: Some(_),
                    setter: Some(_),
                    enumerable: false,
                    configurable: true,
                }
            ),
            "stack must be a non-enumerable configurable accessor property"
        );
        let cause = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("cause object allocation succeeds");
        let options = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("options object allocation succeeds");
        machine
            .set_data_property(options, "cause", cause)
            .expect("options.cause set succeeds");
        let msg2 = machine
            .allocate(HeapEntry::String(EcmaString::encode("outer")))
            .expect("message allocation succeeds");
        let with_cause = machine
            .construct_value(error_constructor, &[msg2, options])
            .expect("Error with cause construction succeeds");
        let cause_descriptor = machine
            .own_descriptor(with_cause, &PropertyKey::Named(EcmaString::encode("cause")))
            .expect("descriptor lookup succeeds")
            .expect("Error has an own cause property");
        assert!(
            matches!(
                cause_descriptor,
                Property::Data {
                    writable: true,
                    enumerable: false,
                    configurable: true,
                    ..
                }
            ),
            "cause must be a non-enumerable writable configurable data property"
        );
        assert!(
            machine.enumerable_keys(with_cause).unwrap().is_empty(),
            "Error with cause must not expose any enumerable own fields"
        );
        let aggregate_constructor = machine
            .intrinsics
            .global("AggregateError")
            .expect("AggregateError exists");
        let errors_array = machine
            .allocate(HeapEntry::Array {
                elements: vec![error],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("errors array allocation succeeds");
        let agg_message = machine
            .allocate(HeapEntry::String(EcmaString::encode("several")))
            .expect("message allocation succeeds");
        let aggregate = machine
            .construct_value(aggregate_constructor, &[errors_array, agg_message])
            .expect("AggregateError construction succeeds");
        assert!(
            machine.enumerable_keys(aggregate).unwrap().is_empty(),
            "AggregateError own fields must not appear in Object.keys / for...in"
        );
        for field in ["errors", "message"] {
            let descriptor = machine
                .own_descriptor(aggregate, &PropertyKey::Named(EcmaString::encode(field)))
                .expect("descriptor lookup succeeds")
                .expect("AggregateError has an own {field} property");
            assert!(
                matches!(
                    descriptor,
                    Property::Data {
                        writable: true,
                        enumerable: false,
                        configurable: true,
                        ..
                    }
                ),
                "{field} must be a non-enumerable writable configurable data property"
            );
        }
    }
    #[test]
    fn define_descriptor_create_delete_refunds_property_charge() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let index = machine
            .runtime_slot(object)
            .expect("object slot lookup succeeds")
            .expect("object has a runtime slot");
        let data_key = PropertyKey::Named(EcmaString::encode("data"));
        let accessor_key = PropertyKey::Named(EcmaString::encode("accessor"));
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;
        for _ in 0..3 {
            machine
                .define_descriptor(
                    object,
                    data_key.clone(),
                    Property::Data {
                        value: Value::int32(1),
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .expect("data descriptor definition succeeds");
            assert!(
                machine
                    .internal_delete(object, &data_key)
                    .expect("delete succeeds"),
                "configurable data descriptor is removed"
            );
            machine
                .define_descriptor(
                    object,
                    accessor_key.clone(),
                    Property::Accessor {
                        getter: Some(Value::int32(2)),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .expect("accessor descriptor definition succeeds");
            assert!(
                machine
                    .internal_delete(object, &accessor_key)
                    .expect("delete succeeds"),
                "configurable accessor descriptor is removed"
            );
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
            machine.assert_heap_ledger();
        }
    }
    #[test]
    fn define_descriptor_fails_before_charging_when_heap_limit_is_exhausted() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let limits = Limits {
            max_heap_bytes: 2,
            ..Limits::default()
        };
        let mut machine = Machine::new(&module, &mut host, limits);
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let index = machine
            .runtime_slot(object)
            .expect("object slot lookup succeeds")
            .expect("object has a runtime slot");
        let before_slot = machine.slot_bytes[index];
        let before_heap = machine.heap_bytes;
        let key = PropertyKey::Named(EcmaString::encode("x"));
        assert!(matches!(
            machine.define_descriptor(
                object,
                key,
                Property::Data {
                    value: Value::int32(1),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            ),
            Err(EvalFailure::Runtime(
                crate::RuntimeErrorKind::HeapByteLimitExceeded { limit: 2 }
            ))
        ));
        assert_eq!(machine.slot_bytes[index], before_slot);
        assert_eq!(machine.heap_bytes, before_heap);
        machine.assert_heap_ledger();
    }
    #[test]
    fn array_length_redefinition_failure_refunds_speculative_charge() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = machine
            .allocate(HeapEntry::Array {
                elements: vec![Value::int32(1), Value::int32(2), Value::int32(3)],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("array allocation succeeds");
        let index = machine
            .runtime_slot(array)
            .expect("array slot lookup succeeds")
            .expect("array has a runtime slot");
        let length_key = PropertyKey::Named(EcmaString::encode("length"));
        machine
            .define_descriptor(
                array,
                length_key.clone(),
                Property::Data {
                    value: Value::int32(3),
                    writable: false,
                    enumerable: false,
                    configurable: false,
                },
            )
            .expect("freezing array length succeeds");
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;
        for _ in 0..10 {
            assert!(matches!(
                machine.define_descriptor(
                    array,
                    length_key.clone(),
                    Property::Data {
                        value: Value::int32(1_000_000),
                        writable: false,
                        enumerable: false,
                        configurable: false,
                    },
                ),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(machine.slot_bytes[index], baseline_slot);
            assert_eq!(machine.heap_bytes, baseline_heap);
        }
        machine.assert_heap_ledger();
    }
    #[test]
    fn load_own_descriptor_slot_covers_absent_data_accessor_and_shape_mismatch() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let missing = allocate_string(&mut machine, EcmaString::encode("missing")).unwrap();
        let data_key = allocate_string(&mut machine, EcmaString::encode("data")).unwrap();
        let accessor_key = allocate_string(&mut machine, EcmaString::encode("accessor")).unwrap();
        let data_pk = PropertyKey::Named(EcmaString::encode("data"));
        let accessor_pk = PropertyKey::Named(EcmaString::encode("accessor"));
        let getter = Value::int32(1);
        let setter = Value::int32(2);
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, missing, DescriptorSlot::Value)
                .unwrap(),
            Value::UNDEFINED,
            "absent property yields undefined"
        );
        machine
            .define_descriptor(
                object,
                data_pk.clone(),
                Property::Data {
                    value: Value::int32(7),
                    writable: false,
                    enumerable: true,
                    configurable: false,
                },
            )
            .unwrap();
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, data_key, DescriptorSlot::Value)
                .unwrap(),
            Value::int32(7)
        );
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, data_key, DescriptorSlot::Getter)
                .unwrap(),
            Value::UNDEFINED,
            "data/getter shape mismatch yields undefined"
        );
        machine
            .define_descriptor(
                object,
                accessor_pk,
                Property::Accessor {
                    getter: Some(getter),
                    setter: Some(setter),
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, accessor_key, DescriptorSlot::Getter)
                .unwrap(),
            getter
        );
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, accessor_key, DescriptorSlot::Setter)
                .unwrap(),
            setter
        );
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, accessor_key, DescriptorSlot::Value)
                .unwrap(),
            Value::UNDEFINED,
            "accessor/value shape mismatch yields undefined"
        );
    }
    #[test]
    fn define_own_descriptor_slot_creates_absent_preserves_attrs_and_rejects_shape_mismatch() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let data_key = allocate_string(&mut machine, EcmaString::encode("data")).unwrap();
        let accessor_key = allocate_string(&mut machine, EcmaString::encode("accessor")).unwrap();
        let missing = allocate_string(&mut machine, EcmaString::encode("missing")).unwrap();
        let missing_getter =
            allocate_string(&mut machine, EcmaString::encode("missingGetter")).unwrap();
        let data_pk = PropertyKey::Named(EcmaString::encode("data"));
        let accessor_pk = PropertyKey::Named(EcmaString::encode("accessor"));
        let missing_pk = PropertyKey::Named(EcmaString::encode("missing"));
        let missing_getter_pk = PropertyKey::Named(EcmaString::encode("missingGetter"));
        let getter = Value::int32(11);
        let setter = Value::int32(22);
        let next_getter = Value::int32(33);
        let next_value = Value::int32(44);
        machine
            .define_own_descriptor_slot(object, missing, next_value, DescriptorSlot::Value)
            .unwrap();
        assert!(matches!(
            machine.own_descriptor(object, &missing_pk).unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            }) if value == next_value
        ));
        machine
            .define_own_descriptor_slot(object, missing_getter, getter, DescriptorSlot::Getter)
            .unwrap();
        assert!(matches!(
            machine.own_descriptor(object, &missing_getter_pk).unwrap(),
            Some(Property::Accessor {
                getter: Some(g),
                setter: None,
                enumerable: false,
                configurable: true,
            }) if g == getter
        ));
        machine
            .define_descriptor(
                object,
                data_pk.clone(),
                Property::Data {
                    value: Value::int32(1),
                    writable: false,
                    enumerable: true,
                    configurable: false,
                },
            )
            .unwrap();
        assert!(matches!(
            machine.define_own_descriptor_slot(object, data_key, next_value, DescriptorSlot::Value),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Cannot redefine property: cannot change value of non-writable property"
            }))
        ));
        assert!(matches!(
            machine.own_descriptor(object, &data_pk).unwrap(),
            Some(Property::Data {
                value,
                writable: false,
                enumerable: true,
                configurable: false,
            }) if value == Value::int32(1)
        ));
        assert!(matches!(
            machine.define_own_descriptor_slot(object, data_key, getter, DescriptorSlot::Getter),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "decorator replacement changes descriptor shape"
            }))
        ));
        machine
            .define_descriptor(
                object,
                accessor_pk.clone(),
                Property::Accessor {
                    getter: Some(getter),
                    setter: Some(setter),
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_own_descriptor_slot(object, accessor_key, next_getter, DescriptorSlot::Getter)
            .unwrap();
        assert!(matches!(
            machine.own_descriptor(object, &accessor_pk).unwrap(),
            Some(Property::Accessor {
                getter: Some(g),
                setter: Some(s),
                enumerable: false,
                configurable: true,
            }) if g == next_getter && s == setter
        ));
        assert!(matches!(
            machine.define_own_descriptor_slot(
                object,
                accessor_key,
                next_value,
                DescriptorSlot::Value
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "decorator replacement changes descriptor shape"
            }))
        ));
    }
    #[test]
    fn load_own_descriptor_slot_is_own_only_and_non_invoking() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let proto = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(proto),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        let inherited_key = allocate_string(&mut machine, EcmaString::encode("inherited")).unwrap();
        let accessor_key = allocate_string(&mut machine, EcmaString::encode("accessor")).unwrap();
        let inherited_pk = PropertyKey::Named(EcmaString::encode("inherited"));
        let accessor_pk = PropertyKey::Named(EcmaString::encode("accessor"));
        machine
            .define_descriptor(
                proto,
                inherited_pk,
                Property::Data {
                    value: Value::int32(99),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, inherited_key, DescriptorSlot::Value)
                .unwrap(),
            Value::UNDEFINED,
            "inherited prototype data must not be visible to own-slot load"
        );
        let getter = install_function(
            &mut machine.heap,
            &mut machine.intrinsics.builtins,
            "counting getter",
            0,
            |_machine, _this, _args, _constructing| {
                panic!("LoadOwnDescriptorSlot must not invoke accessors");
            },
        );
        machine
            .define_descriptor(
                object,
                accessor_pk,
                Property::Accessor {
                    getter: Some(getter),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, accessor_key, DescriptorSlot::Getter)
                .unwrap(),
            getter,
            "Getter slot returns the getter function without calling it"
        );
    }
    #[test]
    fn descriptor_slot_helpers_coerce_key_objects_once_to_produced_property_key() {
        fn key_to_string<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let calls = machine.get_named_property(this, "calls")?;
            let next = match calls.decode() {
                Some(Decoded::Int32(raw)) => raw.wrapping_add(1),
                _ => 1,
            };
            machine.set_data_property(this, "calls", Value::int32(next))?;
            let produced = machine.get_named_property(this, "produced")?;
            Ok(BuiltinOutcome::Value(produced))
        }
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let produced = allocate_string(&mut machine, EcmaString::encode("produced-key")).unwrap();
        let produced_pk = PropertyKey::Named(EcmaString::encode("produced-key"));
        machine
            .define_descriptor(
                object,
                produced_pk.clone(),
                Property::Data {
                    value: Value::int32(7),
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        let key_object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        machine
            .set_data_property(key_object, "calls", Value::int32(0))
            .unwrap();
        machine
            .set_data_property(key_object, "produced", produced)
            .unwrap();
        let to_string = install_function(
            &mut machine.heap,
            &mut machine.intrinsics.builtins,
            "descriptor key toString",
            0,
            key_to_string::<TestHost>,
        );
        machine
            .set_data_property(key_object, "toString", to_string)
            .unwrap();
        assert_eq!(
            machine
                .load_own_descriptor_slot(object, key_object, DescriptorSlot::Value)
                .unwrap(),
            Value::int32(7),
            "load must select the property key produced by key conversion"
        );
        assert_eq!(
            machine.get_named_property(key_object, "calls").unwrap(),
            Value::int32(1),
            "load must coerce the key object exactly once"
        );
        let define_key = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        machine
            .set_data_property(define_key, "calls", Value::int32(0))
            .unwrap();
        machine
            .set_data_property(define_key, "produced", produced)
            .unwrap();
        machine
            .set_data_property(define_key, "toString", to_string)
            .unwrap();
        machine
            .define_own_descriptor_slot(object, define_key, Value::int32(99), DescriptorSlot::Value)
            .unwrap();
        assert_eq!(
            machine.get_named_property(define_key, "calls").unwrap(),
            Value::int32(1),
            "define must coerce the key object exactly once"
        );
        assert!(
            matches!(
                machine.own_descriptor(object, &produced_pk).unwrap(),
                Some(Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                }) if value == Value::int32(99)
            ),
            "define must write through the produced property key"
        );
    }
    #[test]
    fn define_descriptor_rejects_redefinition_of_non_configurable_property() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        let index = machine
            .runtime_slot(object)
            .expect("object slot lookup succeeds")
            .expect("object has a runtime slot");
        let key = PropertyKey::Named(EcmaString::encode("x"));
        // Install a writable, configurable data property, then freeze so it
        // becomes non-writable and non-configurable.
        machine
            .define_descriptor(
                object,
                key.clone(),
                Property::Data {
                    value: Value::int32(1),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        machine.mark_frozen(object).unwrap();
        let baseline_slot = machine.slot_bytes[index];
        let baseline_heap = machine.heap_bytes;
        // Redefining the frozen property's value through the internal
        assert!(matches!(
            machine.define_descriptor(
                object,
                key.clone(),
                Property::Data {
                    value: Value::int32(2),
                    writable: false,
                    enumerable: true,
                    configurable: false,
                },
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Cannot redefine property: cannot change value of non-writable property"
            }))
        ));
        assert_eq!(machine.slot_bytes[index], baseline_slot);
        assert_eq!(machine.heap_bytes, baseline_heap);
        assert_eq!(
            machine.get_named_property(object, "x").unwrap(),
            Value::int32(1),
            "frozen value must be unchanged"
        );
        assert!(matches!(
            machine.define_descriptor(
                object,
                key.clone(),
                Property::Accessor {
                    getter: Some(Value::int32(9)),
                    setter: None,
                    enumerable: true,
                    configurable: false,
                },
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Cannot redefine property: cannot convert non-configurable data property to accessor"
            }))
        ));
        assert_eq!(machine.slot_bytes[index], baseline_slot);
        let key_value = allocate_string(&mut machine, EcmaString::encode("x")).unwrap();
        assert!(matches!(
            machine.define_own_descriptor_slot(
                object,
                key_value,
                Value::int32(5),
                DescriptorSlot::Value
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Cannot redefine property: cannot change value of non-writable property"
            }))
        ));
        assert_eq!(
            machine.get_named_property(object, "x").unwrap(),
            Value::int32(1),
            "frozen value must be unchanged after slot write"
        );
        machine.assert_heap_ledger();
    }
    #[test]
    fn bootstrap_installation_bypasses_descriptor_validation() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds");
        define_data(&mut machine.heap, object, "bootstrap", Value::int32(42));
        define_frozen_data(&mut machine.heap, object, "sealed", Value::int32(99));
        assert_eq!(
            machine.get_named_property(object, "bootstrap").unwrap(),
            Value::int32(42)
        );
        assert_eq!(
            machine.get_named_property(object, "sealed").unwrap(),
            Value::int32(99)
        );
    }
}
