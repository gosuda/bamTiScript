use std::collections::BTreeMap;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::{
    allocate_string, builtin_property, define_data, heap_index, install_function, range_error,
    to_integer_or_infinity, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey, PropertyMap,
};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    builtins.set_uint8array_prototype(prototype);
    let constructor = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "Uint8Array", length: 1, handler: constructor::<H> });
    builtins.set_constructor_prototype(heap, constructor, prototype);
    define_data(heap, atoms, shapes, prototype, "constructor", constructor);
    let length = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get length", length: 0, handler: length_getter::<H> });
    define_getter(heap, atoms, prototype, "length", length);
    let join = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "join", length: 1, handler: join::<H> as BuiltinHandler<H> });
    define_data(heap, atoms, shapes, prototype, "join", join);
    let iterator = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "[Symbol.iterator]", length: 0, handler: values::<H> as BuiltinHandler<H> });
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!("Uint8Array prototype is ordinary")
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(builtins.symbol_iterator()) as u32),
        builtin_property(iterator),
    );
    let tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("Uint8Array")));
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!("Uint8Array prototype is ordinary")
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(builtins.symbol_to_string_tag()) as u32),
        builtin_property(tag),
    );
    globals.insert(EcmaString::encode("Uint8Array"), constructor);
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("Uint8Array constructor requires 'new'"));
    }
    let (length, values, copied_bytes) = match args.first().copied() {
        None | Some(Value::UNDEFINED) => (0, None, None),
        Some(source) if !machine.is_object(source) => {
            (typed_array_length(machine, source)?, None, None)
        }
        Some(source) => {
            let copied_bytes = match machine.runtime_slot(source).map_err(EvalFailure::Runtime)? {
                Some(slot) => match &machine.heap[slot] {
                    HeapEntry::Uint8Array { bytes, .. } => Some(bytes.clone()),
                    _ => None,
                },
                None => None,
            };
            if let Some(bytes) = copied_bytes {
                (bytes.len(), None, Some(bytes))
            } else {
                let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
                let iterator_key = machine.property_key_from_value(iterator_symbol)?;
                let iterator_method = machine.get_property_key(source, &iterator_key)?;
                match iterator_method.decode() {
                    Some(Decoded::Undefined | Decoded::Null) => {
                        let values = array_like_values(machine, source)?;
                        (values.len(), Some(values), None)
                    }
                    _ if machine.is_callable(iterator_method)? => {
                        let values = machine.iterable_values(source)?;
                        (values.len(), Some(values), None)
                    }
                    _ => return Err(type_error("value is not iterable")),
                }
            }
        }
    };
    let properties = PropertyMap::default();
    let charge = properties.charge_bytes(&machine.atoms);
    machine
        .ensure_allocation_capacity(1, length.saturating_add(charge).saturating_add(1))
        .map_err(EvalFailure::Runtime)?;
    let bytes = if let Some(copied) = copied_bytes {
        copied
    } else {
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(length).map_err(|_| {
            EvalFailure::Runtime(crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            })
        })?;
        match values {
            Some(values) => {
                for value in values {
                    bytes.push(to_uint8(machine, value)?);
                }
            }
            None => bytes.resize(length, 0),
        }
        bytes
    };
    let default_prototype = machine.intrinsics.builtins.uint8array_prototype();
    let new_target = machine.current_new_target();
    let prototype = if new_target != Value::UNDEFINED {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            default_prototype
        }
    } else {
        default_prototype
    };
    let value = machine
        .allocate(HeapEntry::Uint8Array {
            bytes,
            properties,
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(value))
}

fn length_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let index = machine
        .runtime_slot(this)
        .map_err(EvalFailure::Runtime)?
        .ok_or_else(|| {
            type_error("Uint8Array.prototype.length getter called on incompatible receiver")
        })?;
    let HeapEntry::Uint8Array { bytes, .. } = &machine.heap[index] else {
        return Err(type_error(
            "Uint8Array.prototype.length getter called on incompatible receiver",
        ));
    };
    Ok(BuiltinOutcome::Value(crate::number_value(
        bytes.len() as f64
    )))
}

fn define_getter(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    object: Value,
    name: &str,
    getter: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        panic!("accessor target must be an ordinary object");
    };
    properties.insert(
        PropertyKey::Named(atoms.intern_str(name)),
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
}

/// ToIndex for the TypedArray(length) constructor: ToIntegerOrInfinity, then
/// reject negatives, infinities, and lengths beyond the runtime's heap-slot
/// ceiling before any allocation. NaN and ±0 collapse to zero.
fn typed_array_length<H: Host>(
    machine: &Machine<'_, H>,
    source: Value,
) -> Result<usize, EvalFailure> {
    let length = to_integer_or_infinity(machine, source)?;
    if length < 0.0 || length.is_infinite() || length > machine.limits.max_heap_slots as f64 {
        return Err(range_error("Invalid typed array length"));
    }
    Ok(length as usize)
}
fn array_like_values<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<Vec<Value>, EvalFailure> {
    let length_value = machine.get_named_property(source, "length")?;
    let length = array_like_length(machine, length_value)?;
    machine
        .ensure_object_property_capacity(length)
        .map_err(EvalFailure::Runtime)?;
    let mut values = Vec::with_capacity(length);
    for index in 0..length {
        let value = machine.get_named_property(source, &index.to_string())?;
        values.push(Value::int32(u32::from(to_uint8(machine, value)?)));
    }
    Ok(values)
}
fn array_like_length<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
    let number = super::value_number(machine.coerce_number_observable(value)?);
    let integer = if number.is_nan() || number == 0.0 {
        0.0
    } else {
        number.trunc()
    };
    let length = if integer <= 0.0 {
        0.0
    } else if integer.is_infinite() {
        MAX_SAFE_INTEGER
    } else {
        integer.min(MAX_SAFE_INTEGER)
    };
    if length > machine.limits.max_heap_slots as f64 {
        return Err(range_error("Invalid typed array length"));
    }
    Ok(length as usize)
}

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
fn to_uint8_from_f64(number: f64) -> u8 {
    if number.is_finite() && number != 0.0 {
        number.trunc().rem_euclid(256.0) as u8
    } else {
        0
    }
}

fn join<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(slot) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "Uint8Array.prototype.join called on incompatible receiver",
        ));
    };
    if !matches!(machine.heap[slot], HeapEntry::Uint8Array { .. }) {
        return Err(type_error(
            "Uint8Array.prototype.join called on incompatible receiver",
        ));
    }
    let separator = match args.first().copied() {
        None | Some(Value::UNDEFINED) => EcmaString::encode(","),
        Some(value) => machine.coerce_string_observable(value)?,
    };
    let HeapEntry::Uint8Array { bytes, .. } = &machine.heap[slot] else {
        return Err(type_error(
            "Uint8Array.prototype.join called on incompatible receiver",
        ));
    };
    let mut output = EcmaStringBuilder::new();
    for (index, byte) in bytes.iter().copied().enumerate() {
        if index != 0 {
            for &unit in separator.as_units() {
                output.push_unit(unit);
            }
        }
        output.push_utf8(&byte.to_string());
    }
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        output.finish(),
    )?))
}

/// `Uint8Array.prototype[Symbol.iterator]` — yields each current byte lazily in
/// index order, matching `%TypedArray%.prototype.values`.
fn values<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(slot) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "Uint8Array.prototype[Symbol.iterator] called on incompatible receiver",
        ));
    };
    if !matches!(machine.heap[slot], HeapEntry::Uint8Array { .. }) {
        return Err(type_error(
            "Uint8Array.prototype[Symbol.iterator] called on incompatible receiver",
        ));
    }
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Value,
    )?))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, NativeCallable, PropertyMap, ThrowOrigin};

    static NEXT_CALLS: AtomicUsize = AtomicUsize::new(0);
    static ITERATION_COMPLETE: AtomicBool = AtomicBool::new(false);

    static LENGTH_VALUE_OF_CALLED: AtomicBool = AtomicBool::new(false);
    static INDEX_ONE_READS: AtomicUsize = AtomicUsize::new(0);

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, id, name, 0)
    }

    fn iterator_method(
        _: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    fn throwing_iterator(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "source Symbol.iterator called",
        }))
    }

    fn iterator_next(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let done = NEXT_CALLS.fetch_add(1, Ordering::SeqCst) != 0;
        if done {
            ITERATION_COMPLETE.store(true, Ordering::SeqCst);
        }
        let result = ordinary_object(machine);
        machine.set_data_property(result, "done", Value::boolean(done))?;
        if !done {
            machine.set_data_property(result, "value", this)?;
        }
        Ok(BuiltinOutcome::Value(result))
    }

    fn iterator_next_value(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let done = machine.get_named_property(this, "_done")?;
        let result = ordinary_object(machine);
        if machine.truthy(done) {
            machine.set_data_property(result, "done", Value::TRUE)?;
        } else {
            machine.set_data_property(this, "_done", Value::TRUE)?;
            let value = machine.get_named_property(this, "_iterable_value")?;
            machine.set_data_property(result, "done", Value::FALSE)?;
            machine.set_data_property(result, "value", value)?;
        }
        Ok(BuiltinOutcome::Value(result))
    }
    fn value_of(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert!(
            ITERATION_COMPLETE.load(Ordering::SeqCst),
            "Uint8Array must finish iterable collection before coercing elements"
        );
        Ok(BuiltinOutcome::Value(Value::int32(257)))
    }

    fn array_like_length_value_of(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        LENGTH_VALUE_OF_CALLED.store(true, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(Value::int32(2)))
    }

    fn index_one_getter(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        INDEX_ONE_READS.fetch_add(1, Ordering::SeqCst);
        Ok(BuiltinOutcome::Value(Value::int32(42)))
    }

    fn abrupt_value_of(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "abrupt ToUint8 valueOf",
        }))
    }

    fn zero_getter_returns_abrupt(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let abrupt = ordinary_object(machine);
        let value_of = native(machine, "abrupt valueOf", abrupt_value_of);
        machine.set_data_property(abrupt, "valueOf", value_of)?;
        Ok(BuiltinOutcome::Value(abrupt))
    }

    fn separator_mutates_first_byte(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let target = machine
            .test_global("joinTarget")
            .expect("test installs join target");
        machine.set_data_property(target, "0", Value::int32(9))?;
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("-"),
        )?))
    }

    fn construct(machine: &mut Machine<'_, TestHost>, argument: Value) -> Value {
        let constructor = machine
            .intrinsics
            .global("Uint8Array")
            .expect("Uint8Array installs");
        let index = machine
            .runtime_slot(constructor)
            .expect("valid constructor")
            .expect("heap");
        let HeapEntry::NativeFunction {
            callable: NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("Uint8Array is native")
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, &[argument], true)
            .expect("constructor succeeds")
        else {
            panic!("constructor returns an object")
        };
        value
    }

    #[test]
    fn uint8array_length_is_an_inherited_branded_accessor() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let typed = construct(&mut machine, Value::int32(3));
        let key = PropertyKey::Named(machine.intern_str("length"));

        assert!(machine.own_descriptor(typed, &key).unwrap().is_none());
        assert_eq!(
            machine.get_named_property(typed, "length").unwrap(),
            Value::int32(3)
        );

        let prototype = machine.intrinsics.builtins.uint8array_prototype();
        let descriptor = machine
            .own_descriptor(prototype, &key)
            .unwrap()
            .expect("prototype has length accessor");
        let Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        } = descriptor
        else {
            panic!("length is a configurable, non-enumerable getter");
        };
        let plain = ordinary_object(&mut machine);
        assert!(matches!(
            machine.call_value(getter, plain, &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn uint8array_collects_before_coercion_and_exposes_bounded_surface() {
        NEXT_CALLS.store(0, Ordering::SeqCst);
        ITERATION_COMPLETE.store(false, Ordering::SeqCst);
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let source = ordinary_object(&mut machine);
        let iterator = native(&mut machine, "[Symbol.iterator]", iterator_method);
        let next = native(&mut machine, "next", iterator_next);
        let value_of = native(&mut machine, "valueOf", value_of);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol)
            .expect("symbol key");
        machine
            .set_data_property_key(source, iterator_key, iterator)
            .expect("iterator install succeeds");
        machine
            .set_data_property(source, "next", next)
            .expect("next install succeeds");
        machine
            .set_data_property(source, "valueOf", value_of)
            .expect("valueOf install succeeds");

        let typed = construct(&mut machine, source);
        assert_eq!(
            machine.get_named_property(typed, "length").unwrap(),
            Value::int32(1)
        );
        assert_eq!(
            machine.get_named_property(typed, "0").unwrap(),
            Value::int32(1)
        );
        let join = machine
            .get_named_property(typed, "join")
            .expect("join inherits");
        let joined = machine.call_value(join, typed, &[]).expect("join succeeds");
        assert!(
            machine
                .string_value(joined)
                .is_some_and(|text| text.eq_ascii("1"))
        );

        let element = ordinary_object(&mut machine);
        machine
            .set_data_property(element, "valueOf", value_of)
            .expect("valueOf install succeeds");
        let array_input = machine
            .allocate(HeapEntry::Array {
                elements: vec![element],
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("array allocation succeeds");
        let from_array = construct(&mut machine, array_input);
        let array_join = machine
            .get_named_property(from_array, "join")
            .expect("join inherits");
        let array_joined = machine
            .call_value(array_join, from_array, &[])
            .expect("join succeeds");
        assert!(
            machine
                .string_value(array_joined)
                .is_some_and(|text| text.eq_ascii("1"))
        );

        let constructor = machine.intrinsics.global("Uint8Array").unwrap();
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .unwrap();
        assert_eq!(
            machine
                .get_named_property(prototype, "constructor")
                .unwrap(),
            constructor
        );
        let array = machine.intrinsics.global("Array").unwrap();
        let is_array = machine.get_named_property(array, "isArray").unwrap();
        assert_eq!(
            machine.call_value(is_array, array, &[typed]).unwrap(),
            Value::FALSE
        );
        let plain = ordinary_object(&mut machine);
        machine
            .set_data_property(plain, "length", Value::int32(1))
            .unwrap();
        assert!(matches!(
            machine.call_value(join, plain, &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }
    fn try_construct(
        machine: &mut Machine<'_, TestHost>,
        argument: Value,
    ) -> Result<Value, EvalFailure> {
        let constructor = machine
            .intrinsics
            .global("Uint8Array")
            .expect("Uint8Array installs");
        let index = machine
            .runtime_slot(constructor)
            .expect("valid constructor")
            .expect("heap");
        let HeapEntry::NativeFunction {
            callable: NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("Uint8Array is native")
        };
        machine
            .call_builtin(id, Value::UNDEFINED, &[argument], true)
            .map(|outcome| match outcome {
                BuiltinOutcome::Value(value) => value,
                _ => panic!("constructor returns an object"),
            })
    }

    fn array_of(machine: &mut Machine<'_, TestHost>, elements: &[Value]) -> Value {
        machine
            .allocate(HeapEntry::Array {
                elements: elements.to_vec(),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .expect("array allocation succeeds")
    }

    fn int(machine: &mut Machine<'_, TestHost>, typed: Value, name: &str) -> u32 {
        machine
            .get_named_property(typed, name)
            .expect("property exists")
            .as_int32()
            .expect("property is an int32")
    }

    fn with_machine(f: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        f(&mut machine);
    }

    #[test]
    fn uint8array_noniterable_objects_use_array_like_values() {
        with_machine(|machine| {
            let plain = ordinary_object(machine);
            machine
                .set_data_property(plain, "0", Value::int32(7))
                .unwrap();
            machine
                .set_data_property(plain, "length", Value::int32(1))
                .unwrap();
            let typed = construct(machine, plain);
            assert_eq!(int(machine, typed, "length"), 1);
            assert_eq!(int(machine, typed, "0"), 7);
            let source = ordinary_object(machine);
            let boxed_like = construct(machine, source);
            assert_eq!(int(machine, boxed_like, "length"), 0);
            let nullish = ordinary_object(machine);
            machine
                .set_data_property(nullish, "0", Value::int32(8))
                .unwrap();
            machine
                .set_data_property(nullish, "length", Value::int32(1))
                .unwrap();
            let iterator_key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            machine
                .set_data_property_key(nullish, iterator_key, Value::NULL)
                .unwrap();
            let typed = construct(machine, nullish);
            assert_eq!(int(machine, typed, "0"), 8);
        });
    }
    #[test]
    fn uint8array_iterators_take_precedence_and_noncallables_throw() {
        with_machine(|machine| {
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "0", Value::int32(7))
                .unwrap();
            machine
                .set_data_property(source, "length", Value::int32(1))
                .unwrap();
            machine
                .set_data_property(source, "_done", Value::FALSE)
                .unwrap();
            machine
                .set_data_property(source, "_iterable_value", Value::int32(9))
                .unwrap();
            let iterator = native(machine, "[Symbol.iterator]", iterator_method);
            let next = native(machine, "next", iterator_next_value);
            let iterator_key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            machine
                .set_data_property_key(source, iterator_key, iterator)
                .unwrap();
            machine.set_data_property(source, "next", next).unwrap();
            let typed = construct(machine, source);
            assert_eq!(int(machine, typed, "0"), 9);
            let noncallable = ordinary_object(machine);
            let iterator_key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            machine
                .set_data_property_key(noncallable, iterator_key, Value::int32(0))
                .unwrap();
            assert!(matches!(
                try_construct(machine, noncallable),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn uint8array_copies_typed_array_without_calling_symbol_iterator() {
        with_machine(|machine| {
            let source_values = array_of(
                machine,
                &[Value::int32(3), Value::int32(17), Value::int32(255)],
            );
            let source = construct(machine, source_values);
            let iterator = native(machine, "throwing [Symbol.iterator]", throwing_iterator);
            let iterator_key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                .unwrap();
            machine
                .set_data_property_key(source, iterator_key, iterator)
                .unwrap();

            let copy = construct(machine, source);

            assert_eq!(int(machine, copy, "length"), 3);
            assert_eq!(int(machine, copy, "0"), 3);
            assert_eq!(int(machine, copy, "1"), 17);
            assert_eq!(int(machine, copy, "2"), 255);
        });
    }

    #[test]
    fn uint8array_preflights_dedicated_backing_storage() {
        let program = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let initial_bytes = machine.heap_bytes;
        try_construct(&mut machine, Value::int32(0)).unwrap();
        let base_charge = machine.heap_bytes - initial_bytes;
        let slots = machine.heap.len();
        let bytes = machine.heap_bytes;

        machine.limits.max_heap_bytes = bytes + base_charge;
        assert!(matches!(
            try_construct(&mut machine, Value::int32(1)),
            Err(EvalFailure::Runtime(
                crate::RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert_eq!(machine.heap.len(), slots);
        assert_eq!(machine.heap_bytes, bytes);

        machine.limits.max_heap_bytes = bytes + base_charge + 1;
        try_construct(&mut machine, Value::int32(1)).unwrap();
        assert_eq!(machine.heap_bytes, bytes + base_charge + 1);
    }
    #[test]
    fn uint8array_length_construction_creates_zero_bytes() {
        // Finding 1: `new Uint8Array(3)` must produce three zero bytes, not
        // dispatch the number through iterable collection (which throws
        // TypeError because a number is not iterable).
        with_machine(|machine| {
            let typed = construct(machine, Value::int32(3));
            assert_eq!(int(machine, typed, "length"), 3);
            assert_eq!(int(machine, typed, "0"), 0);
            assert_eq!(int(machine, typed, "1"), 0);
            assert_eq!(int(machine, typed, "2"), 0);
            assert_eq!(
                machine.get_named_property(typed, "3").unwrap(),
                Value::UNDEFINED
            );
        });
    }

    #[test]
    fn uint8array_length_construction_boundaries() {
        // ToIndex on primitive (non-object) arguments: NaN/±0 collapse to 0,
        // fractions truncate toward zero, booleans/null/strings coerce via
        // ToNumber. Node: U8(3.5)=3, U8(NaN)=0, U8(true)=1, U8(null)=0,
        // U8("3")=3, U8("abc")=0.
        with_machine(|machine| {
            let s3 = allocate_string(machine, EcmaString::encode("3")).unwrap();
            let sabc = allocate_string(machine, EcmaString::encode("abc")).unwrap();
            let cases: &[(Value, u32)] = &[
                (Value::int32(0), 0),
                (Value::number(3.5), 3),
                (Value::number(f64::NAN), 0),
                (Value::number(-0.0), 0),
                (Value::TRUE, 1),
                (Value::FALSE, 0),
                (Value::NULL, 0),
                (Value::UNDEFINED, 0),
                (s3, 3),
                (sabc, 0),
            ];
            for &(argument, expected) in cases {
                let typed = construct(machine, argument);
                assert_eq!(
                    int(machine, typed, "length"),
                    expected,
                    "length for {argument:?}"
                );
            }
        });
    }

    #[test]
    fn uint8array_length_construction_rejects_invalid_lengths() {
        // Negative, ±Infinity, and out-of-range primitives must throw
        // RangeError before any allocation. Node: U8(-1), U8(Infinity),
        // U8(-Infinity), U8(1e20) all throw RangeError.
        with_machine(|machine| {
            for argument in [
                Value::number(-1.0),
                Value::number(f64::INFINITY),
                Value::number(f64::NEG_INFINITY),
                Value::number(1e20),
            ] {
                assert!(
                    matches!(
                        try_construct(machine, argument),
                        Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                    ),
                    "expected RangeError for {argument:?}"
                );
            }
        });
    }

    #[test]
    fn uint8array_iterable_coercion_reduces_modulo_256() {
        // Finding 2: ToUint8 truncates toward zero then reduces modulo 256
        // for all finite values. Out-of-i64 finite values such as 1e20 and
        // 1e308 yield 0, not 255 (the saturation the `as i64 as u8` form
        // produced). Values below are Node-observable.
        with_machine(|machine| {
            let inputs: &[(Vec<Value>, Vec<u32>)] = &[
                (
                    vec![
                        Value::int32(257),
                        Value::number(1e20),
                        Value::int32(u32::MAX),
                        Value::int32(300),
                        Value::int32(256),
                        Value::int32(255),
                    ],
                    vec![1, 0, 255, 44, 0, 255],
                ),
                (
                    vec![
                        Value::number(1e308),
                        Value::number(-1e20),
                        Value::number(-1e308),
                        Value::int32(511),
                        Value::number(-257.0),
                        Value::number(-256.0),
                        Value::number(-255.0),
                        Value::number(-300.0),
                    ],
                    vec![0, 0, 0, 255, 255, 0, 1, 212],
                ),
                (
                    vec![
                        Value::number(1.5),
                        Value::number(-0.5),
                        Value::number(0.5),
                        Value::number(-0.5),
                    ],
                    vec![1, 0, 0, 0],
                ),
                (
                    vec![
                        Value::int32(0),
                        Value::number(-0.0),
                        Value::number(f64::NAN),
                        Value::number(f64::INFINITY),
                        Value::number(f64::NEG_INFINITY),
                    ],
                    vec![0, 0, 0, 0, 0],
                ),
            ];
            for (elements, expected) in inputs {
                let source = array_of(machine, elements);
                let typed = construct(machine, source);
                assert_eq!(int(machine, typed, "length"), expected.len() as u32);
                for (index, &byte) in expected.iter().enumerate() {
                    assert_eq!(
                        int(machine, typed, &index.to_string()),
                        byte,
                        "element {index}"
                    );
                }
            }
        });
    }

    #[test]
    fn uint8array_array_like_length_observes_valueof() {
        LENGTH_VALUE_OF_CALLED.store(false, Ordering::SeqCst);
        with_machine(|machine| {
            let length_box = ordinary_object(machine);
            let value_of = native(machine, "length valueOf", array_like_length_value_of);
            machine
                .set_data_property(length_box, "valueOf", value_of)
                .unwrap();

            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "0", Value::int32(257))
                .unwrap();
            machine
                .set_data_property(source, "1", Value::int32(2))
                .unwrap();
            machine
                .set_data_property(source, "length", length_box)
                .unwrap();

            let typed = construct(machine, source);
            assert!(
                LENGTH_VALUE_OF_CALLED.load(Ordering::SeqCst),
                "length valueOf must be observed"
            );
            assert_eq!(int(machine, typed, "length"), 2);
            assert_eq!(int(machine, typed, "0"), 1);
            assert_eq!(int(machine, typed, "1"), 2);
        });
    }

    #[test]
    fn uint8array_array_like_values_interleave_get_and_touint8() {
        INDEX_ONE_READS.store(0, Ordering::SeqCst);
        with_machine(|machine| {
            let source = ordinary_object(machine);
            let getter0 = native(machine, "zero getter", zero_getter_returns_abrupt);
            let getter1 = native(machine, "one getter", index_one_getter);
            machine
                .define_accessor(
                    source,
                    PropertyKey::Named(machine.intern_str("0")),
                    getter0,
                    bamts_bytecode::AccessorKind::Getter,
                )
                .unwrap();
            machine
                .define_accessor(
                    source,
                    PropertyKey::Named(machine.intern_str("1")),
                    getter1,
                    bamts_bytecode::AccessorKind::Getter,
                )
                .unwrap();
            machine
                .set_data_property(source, "length", Value::int32(2))
                .unwrap();

            assert!(matches!(
                try_construct(machine, source),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                INDEX_ONE_READS.load(Ordering::SeqCst),
                0,
                "index 1 getter must not be read after abrupt ToUint8"
            );
        });
    }

    #[test]
    fn uint8array_prototype_symbol_iterator_yields_elements_in_order() {
        // Symbol.iterator must be installed on Uint8Array.prototype so that
        // for...of and spread consume the bytes in index order. iterable_values
        // is the exact path for...of/spread take (create_iterator + next loop).
        with_machine(|machine| {
            let source = array_of(
                machine,
                &[Value::int32(10), Value::int32(20), Value::int32(255)],
            );
            let typed = construct(machine, source);
            assert_eq!(int(machine, typed, "length"), 3);
            // for...of / spread equivalent
            let collected = machine.iterable_values(typed).expect("iteration succeeds");
            assert_eq!(
                collected,
                vec![Value::int32(10), Value::int32(20), Value::int32(255)],
                "for...of yields bytes in order"
            );
            // Spread into a new array: Array.from uses the iterator too.
            let array = machine.intrinsics.global("Array").unwrap();
            let from = machine.get_named_property(array, "from").unwrap();
            let spread = machine
                .call_value(from, array, &[typed])
                .expect("Array.from succeeds");
            let elements = machine.array_elements(spread).unwrap().unwrap();
            assert_eq!(
                elements,
                vec![Value::int32(10), Value::int32(20), Value::int32(255)],
                "spread/Array.from yields bytes in order"
            );
            // Empty Uint8Array iterates zero times.
            let empty = construct(machine, Value::int32(0));
            assert!(
                machine
                    .iterable_values(empty)
                    .expect("empty iteration")
                    .is_empty()
            );
            // Incompatible receiver throws TypeError.
            let plain = ordinary_object(machine);
            let prototype = machine
                .get_named_property(
                    machine.intrinsics.global("Uint8Array").unwrap(),
                    "prototype",
                )
                .unwrap();
            let iterator_fn = machine
                .get_property_key(
                    prototype,
                    &machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                        .unwrap(),
                )
                .unwrap();
            assert!(matches!(
                machine.call_value(iterator_fn, plain, &[]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn uint8array_iterator_is_lazy_and_observes_live_bytes() {
        with_machine(|machine| {
            let prototype = machine.intrinsics.builtins.uint8array_prototype();
            let iterator_fn = machine
                .get_property_key(
                    prototype,
                    &machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
                        .unwrap(),
                )
                .unwrap();
            let empty = construct(machine, Value::int32(0));
            let before_probe = machine.heap_bytes;
            machine.call_value(iterator_fn, empty, &[]).unwrap();
            let iterator_charge = machine.heap_bytes - before_probe;

            let typed = construct(machine, Value::int32(1024));
            let before_iterator = machine.heap_bytes;
            machine.limits.max_heap_bytes = before_iterator + iterator_charge;
            let iterator = machine
                .call_value(iterator_fn, typed, &[])
                .expect("iterator creation has constant memory cost");
            assert_eq!(machine.heap_bytes, before_iterator + iterator_charge);

            machine.limits.max_heap_bytes = usize::MAX;
            machine
                .set_data_property(typed, "0", Value::int32(77))
                .unwrap();
            let next = machine.get_named_property(iterator, "next").unwrap();
            let result = machine.call_value(next, iterator, &[]).unwrap();
            assert_eq!(
                machine.get_named_property(result, "value").unwrap(),
                Value::int32(77)
            );
        });
    }

    #[test]
    fn uint8array_join_rereads_bytes_after_separator_coercion() {
        with_machine(|machine| {
            let source = array_of(machine, &[Value::int32(1), Value::int32(2)]);
            let typed = construct(machine, source);
            machine.test_set_global("joinTarget", typed);
            let separator = ordinary_object(machine);
            let to_string = native(machine, "separator toString", separator_mutates_first_byte);
            machine
                .set_data_property(separator, "toString", to_string)
                .unwrap();
            let join = machine
                .get_named_property(machine.intrinsics.builtins.uint8array_prototype(), "join")
                .unwrap();

            let output = machine.call_value(join, typed, &[separator]).unwrap();

            assert_eq!(
                machine.string_value(output),
                Some(EcmaString::encode("9-2"))
            );
        });
    }

    #[test]
    fn uint8array_prototype_is_cached_not_global_lookup() {
        // The prototype must be read from BuiltinTable, not via a mutable
        // globals map lookup, so deleting the global does not break construction.
        with_machine(|machine| {
            let ctor_before = machine
                .intrinsics
                .global("Uint8Array")
                .expect("Uint8Array global exists before removal");
            machine
                .intrinsics
                .globals
                .remove(&EcmaString::encode("Uint8Array"));
            // Construct via the saved constructor value, not via global lookup
            let idx = machine
                .runtime_slot(ctor_before)
                .expect("valid constructor")
                .expect("heap");
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } = machine.heap[idx]
            else {
                panic!("Uint8Array is native");
            };
            let BuiltinOutcome::Value(typed) = machine
                .call_builtin(id, Value::UNDEFINED, &[Value::int32(2)], true)
                .expect("constructor succeeds")
            else {
                panic!("constructor returns an object");
            };
            assert_eq!(int(machine, typed, "length"), 2);
            // Verify the typed array's internal prototype slot is the cached prototype
            let idx = machine
                .runtime_slot(typed)
                .expect("typed array has slot")
                .expect("slot exists");
            let HeapEntry::Uint8Array { prototype, .. } = &machine.heap[idx] else {
                panic!("typed array brand");
            };
            assert_eq!(
                *prototype,
                Some(machine.intrinsics.builtins.uint8array_prototype())
            );
            // And the cached prototype's "constructor" is still the Uint8Array constructor
            let proto_val = machine.intrinsics.builtins.uint8array_prototype();
            let ctor = machine
                .get_named_property(proto_val, "constructor")
                .expect("prototype has constructor");
            assert_eq!(ctor, ctor_before);
        });
    }

    #[test]
    fn uint8array_constructor_honors_new_target_for_subclass_prototype() {
        let module = blank_program("<uint8array-subclass-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let uint8array_prototype = machine.intrinsics.builtins.uint8array_prototype();

        // Build a subclass prototype that inherits from Uint8Array.prototype.
        let subclass_prototype =
            super::super::ordinary_runtime(&mut machine, Some(uint8array_prototype)).unwrap();
        machine
            .set_data_property(subclass_prototype, "myMethod", Value::int32(42))
            .unwrap();

        // Build a new_target whose .prototype is the subclass prototype.
        let new_target = super::super::ordinary_runtime(&mut machine, None).unwrap();
        machine
            .set_data_property(new_target, "prototype", subclass_prototype)
            .unwrap();

        let uint8array_id = machine.intrinsics.builtins.id_named("Uint8Array").unwrap();
        let BuiltinOutcome::Value(typed) = machine
            .call_builtin_with_new_target(
                uint8array_id,
                Value::UNDEFINED,
                &[Value::int32(4)],
                true,
                new_target,
            )
            .unwrap()
        else {
            panic!("Uint8Array construct returns a value");
        };

        // The typed array must inherit from the subclass prototype, not the intrinsic one.
        let idx = machine
            .runtime_slot(typed)
            .expect("typed array has slot")
            .expect("slot exists");
        let HeapEntry::Uint8Array { prototype, .. } = &machine.heap[idx] else {
            panic!("typed array brand");
        };
        assert_eq!(*prototype, Some(subclass_prototype));
        // Subclass methods are visible on the instance.
        assert_eq!(
            machine.get_named_property(typed, "myMethod").unwrap(),
            Value::int32(42)
        );
        assert_eq!(int(&mut machine, typed, "length"), 4);
    }

    #[test]
    fn uint8array_new_target_primitive_prototype_falls_back_to_default() {
        // When newTarget.prototype is not an object, constructed_prototype
        // must fall back to the intrinsic %Uint8Array.prototype%.
        with_machine(|machine| {
            let new_target = super::super::ordinary_runtime(machine, None).unwrap();
            machine
                .set_data_property(new_target, "prototype", Value::int32(42))
                .unwrap();
            let uint8array_id = machine.intrinsics.builtins.id_named("Uint8Array").unwrap();
            let BuiltinOutcome::Value(typed) = machine
                .call_builtin_with_new_target(
                    uint8array_id,
                    Value::UNDEFINED,
                    &[Value::int32(1)],
                    true,
                    new_target,
                )
                .unwrap()
            else {
                panic!("Uint8Array construct returns a value");
            };
            let idx = machine
                .runtime_slot(typed)
                .expect("typed array has slot")
                .expect("slot exists");
            let HeapEntry::Uint8Array { prototype, .. } = &machine.heap[idx] else {
                panic!("typed array brand");
            };
            assert_eq!(
                *prototype,
                Some(machine.intrinsics.builtins.uint8array_prototype())
            );
        });
    }
}
