//! SharedArrayBuffer over the shared data block in `arraybuffer.rs`, and the
//! Atomics operations over TypedArray views of it.

use std::collections::BTreeMap;
use std::sync::Arc;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::arraybuffer::{
    SharedBlock, grow_shared_array_buffer, species_constructor, to_clamped_index, to_index,
};
use super::bigint;
use super::typedarray_all::{
    ElementKind, TypedArraySnapshot, integer_or_infinity, storage_from_value, typed_array_snapshot,
    value_from_storage,
};
use super::{
    define_data, define_to_string_tag, heap_index, install_constructor_function, install_function,
    range_error, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    install_shared_array_buffer(heap, globals, builtins);
    install_atomics(heap, globals, builtins);
}

fn install_shared_array_buffer<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor =
        install_constructor_function(heap, builtins, "SharedArrayBuffer", 1, constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    builtins.set_sharedarraybuffer_constructor(constructor);
    builtins.set_sharedarraybuffer_prototype(prototype);
    define_data(heap, prototype, "constructor", constructor);
    for (name, length, handler) in [
        ("grow", 1, grow::<H> as BuiltinHandler<H>),
        ("slice", 2, slice::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, prototype, name, function);
    }
    for (property_name, function_name, handler) in [
        (
            "byteLength",
            "get byteLength",
            byte_length::<H> as BuiltinHandler<H>,
        ),
        ("maxByteLength", "get maxByteLength", max_byte_length::<H>),
        ("growable", "get growable", growable::<H>),
    ] {
        let getter = install_function(heap, builtins, function_name, 0, handler);
        let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
            unreachable!("SharedArrayBuffer.prototype is ordinary")
        };
        properties.insert(
            PropertyKey::Named(EcmaString::encode(property_name)),
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }
    let species = install_function(heap, builtins, "get [Symbol.species]", 0, species::<H>);
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        unreachable!("SharedArrayBuffer constructor is native")
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(builtins.symbol_species()) as u32),
        Property::Accessor {
            getter: Some(species),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    define_to_string_tag(
        heap,
        prototype,
        builtins.symbol_to_string_tag(),
        "SharedArrayBuffer",
    );
    globals.insert(EcmaString::encode("SharedArrayBuffer"), constructor);
}

fn install_atomics<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let atomics = super::super::ordinary_prototype(heap, builtins.object_prototype());
    for (name, length, handler) in [
        ("add", 3, add::<H> as BuiltinHandler<H>),
        ("and", 3, and::<H>),
        ("compareExchange", 4, compare_exchange::<H>),
        ("exchange", 3, exchange::<H>),
        ("isLockFree", 1, is_lock_free::<H>),
        ("load", 2, load::<H>),
        ("or", 3, or::<H>),
        ("pause", 0, pause::<H>),
        ("store", 3, store::<H>),
        ("sub", 3, sub::<H>),
        ("xor", 3, xor::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, atomics, name, function);
    }
    define_to_string_tag(heap, atomics, builtins.symbol_to_string_tag(), "Atomics");
    globals.insert(EcmaString::encode("Atomics"), atomics);
}

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

/// GetArrayBufferMaxByteLengthOption: anything but an object means "fixed".
fn max_byte_length_option<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Value,
) -> Result<Option<usize>, EvalFailure> {
    if !machine.is_object(options) {
        return Ok(None);
    }
    let maximum = machine.get_named_property(options, "maxByteLength")?;
    if maximum == Value::UNDEFINED {
        return Ok(None);
    }
    to_index(machine, maximum).map(Some)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _callee: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("SharedArrayBuffer constructor requires 'new'"));
    }
    let byte_length = to_index(machine, argument(args, 0))?;
    let max_byte_length = max_byte_length_option(machine, argument(args, 1))?;
    if max_byte_length.is_some_and(|maximum| byte_length > maximum) {
        return Err(range_error(
            "SharedArrayBuffer byteLength exceeds maxByteLength",
        ));
    }
    let intrinsic = machine.intrinsics.builtins.sharedarraybuffer_prototype();
    let new_target = machine.current_new_target();
    let prototype = if new_target == Value::UNDEFINED {
        intrinsic
    } else {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            intrinsic
        }
    };
    // A growable block must be able to reach its maximum, so that much is
    // required of the heap even though only the current length is charged.
    let allocation_length = max_byte_length.unwrap_or(byte_length);
    if machine
        .ensure_allocation_capacity(1, allocation_length.saturating_add(1))
        .is_err()
    {
        return Err(range_error("SharedArrayBuffer allocation failed"));
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(byte_length)
        .map_err(|_| range_error("SharedArrayBuffer allocation failed"))?;
    bytes.resize(byte_length, 0);
    let value = machine
        .allocate(HeapEntry::SharedArrayBuffer {
            data: Arc::new(SharedBlock::new(bytes, max_byte_length)),
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(|_| range_error("SharedArrayBuffer allocation failed"))?;
    Ok(BuiltinOutcome::Value(value))
}

fn shared_block<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Arc<SharedBlock>, EvalFailure> {
    let incompatible = || type_error("SharedArrayBuffer method called on incompatible receiver");
    let index = machine
        .runtime_slot(value)
        .map_err(EvalFailure::Runtime)?
        .ok_or_else(incompatible)?;
    let HeapEntry::SharedArrayBuffer { data, .. } = &machine.heap[index] else {
        return Err(incompatible());
    };
    Ok(Arc::clone(data))
}

fn byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        shared_block(machine, this)?.byte_length() as f64,
    )))
}

fn max_byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        shared_block(machine, this)?.max_byte_length() as f64,
    )))
}

fn growable<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(
        shared_block(machine, this)?.is_growable(),
    )))
}

fn grow<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    // The [[ArrayBufferMaxByteLength]] slot check precedes argument coercion.
    if !shared_block(machine, this)?.is_growable() {
        return Err(type_error("SharedArrayBuffer is not growable"));
    }
    let new_length = to_index(machine, argument(args, 0))?;
    grow_shared_array_buffer(machine, this, new_length)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn slice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = shared_block(machine, this)?;
    let length = source.byte_length();
    let first = to_clamped_index(machine, argument(args, 0), length)?;
    let end = match argument(args, 1) {
        Value::UNDEFINED => length,
        value => to_clamped_index(machine, value, length)?,
    };
    let new_length = end.saturating_sub(first);
    let default = machine.intrinsics.builtins.sharedarraybuffer_constructor();
    let constructor = species_constructor(machine, this, default)?;
    let target_value =
        machine.construct_value(constructor, &[crate::number_value(new_length as f64)])?;
    let target = shared_block(machine, target_value)?;
    if Arc::ptr_eq(&source, &target) {
        return Err(type_error(
            "SharedArrayBuffer species returned the source buffer",
        ));
    }
    if target.byte_length() < new_length {
        return Err(type_error(
            "SharedArrayBuffer species returned a buffer that is too small",
        ));
    }
    // A block only grows, so the range clamped above is still inside it.
    let copied = source.with_bytes(|bytes| bytes[first..first + new_length].to_vec());
    target.with_bytes_mut(|bytes| bytes[..new_length].copy_from_slice(&copied));
    Ok(BuiltinOutcome::Value(target_value))
}

fn species<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(this))
}

/// ValidateIntegerTypedArray. The returned snapshot's bounds are the ones every
/// later length check of this operation must use, so they are taken here,
/// before any argument coercion can run guest code.
fn validate_integer_typed_array<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
    waitable: bool,
) -> Result<TypedArraySnapshot, EvalFailure> {
    let snapshot = typed_array_snapshot(machine, view)?;
    if snapshot.bounds.out_of_bounds {
        return Err(type_error(
            "Atomics operation requires an in-bounds TypedArray",
        ));
    }
    let supported = if waitable {
        matches!(snapshot.kind, ElementKind::Int32 | ElementKind::BigInt64)
    } else {
        !matches!(
            snapshot.kind,
            ElementKind::Uint8Clamped
                | ElementKind::Float16
                | ElementKind::Float32
                | ElementKind::Float64
        )
    };
    if !supported {
        return Err(type_error(if waitable {
            "Atomics wait operations require an Int32Array or BigInt64Array"
        } else {
            "Atomics operation requires an integer TypedArray"
        }));
    }
    Ok(snapshot)
}

/// ValidateAtomicAccess: the byte position of `request` in the buffer.
fn validate_atomic_access<H: Host>(
    machine: &mut Machine<'_, H>,
    snapshot: &TypedArraySnapshot,
    request: Value,
) -> Result<usize, EvalFailure> {
    let index = to_index(machine, request)?;
    if index >= snapshot.bounds.element_length {
        return Err(range_error("Atomics index is outside the TypedArray"));
    }
    Ok(snapshot.byte_offset + index * snapshot.kind.element_size())
}

/// RevalidateAtomicAccess, for after a coercion that may have run guest code.
fn revalidate_atomic_access<H: Host>(
    machine: &Machine<'_, H>,
    view: Value,
    position: usize,
) -> Result<(), EvalFailure> {
    let snapshot = typed_array_snapshot(machine, view)?;
    if snapshot.bounds.out_of_bounds {
        return Err(type_error(
            "Atomics operation requires an in-bounds TypedArray",
        ));
    }
    if position >= snapshot.buffer.byte_length(machine)? {
        return Err(range_error("Atomics index is outside the TypedArray"));
    }
    Ok(())
}

/// The coerced operand `v` of a write, which `Atomics.store` returns as is, and
/// the element bytes it stores, which wrap to the element type.
fn coerce_operand<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: ElementKind,
    value: Value,
) -> Result<(Value, u64), EvalFailure> {
    let operand = if kind.is_bigint() {
        bigint::to_bigint(machine, value)?
    } else {
        crate::number_value(integer_or_infinity(machine, value)?)
    };
    let storage = storage_from_value(machine, kind, operand)?;
    Ok((operand, u64::from_le_bytes(storage)))
}

/// Applies `update` to one element as a single read-modify-write and returns
/// the previous element bytes. For a shared block the whole closure runs under
/// the block's lock, which every other access to those bytes also takes.
fn update_element<H: Host>(
    machine: &mut Machine<'_, H>,
    snapshot: &TypedArraySnapshot,
    position: usize,
    update: impl FnOnce(u64) -> u64,
) -> Result<[u8; 8], EvalFailure> {
    let size = snapshot.kind.element_size();
    snapshot.buffer.with_bytes_mut(machine, |bytes| {
        let element = &mut bytes[position..position + size];
        let mut old = [0_u8; 8];
        old[..size].copy_from_slice(element);
        element.copy_from_slice(&update(u64::from_le_bytes(old)).to_le_bytes()[..size]);
        old
    })
}

#[derive(Clone, Copy)]
enum Modification {
    Add,
    And,
    Exchange,
    Or,
    Sub,
    Xor,
}

impl Modification {
    /// Both inputs are element bytes in the low bits, so an overflow past the
    /// element's width is discarded when the result is written back.
    const fn apply(self, old: u64, operand: u64) -> u64 {
        match self {
            Self::Add => old.wrapping_add(operand),
            Self::And => old & operand,
            Self::Exchange => operand,
            Self::Or => old | operand,
            Self::Sub => old.wrapping_sub(operand),
            Self::Xor => old ^ operand,
        }
    }
}

/// AtomicReadModifyWrite.
fn read_modify_write<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    modification: Modification,
) -> Result<BuiltinOutcome, EvalFailure> {
    let view = argument(args, 0);
    let snapshot = validate_integer_typed_array(machine, view, false)?;
    let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
    let (_, operand) = coerce_operand(machine, snapshot.kind, argument(args, 2))?;
    revalidate_atomic_access(machine, view, position)?;
    let old = update_element(machine, &snapshot, position, |old| {
        modification.apply(old, operand)
    })?;
    value_from_storage(machine, snapshot.kind, old).map(BuiltinOutcome::Value)
}

macro_rules! read_modify_write_handlers {
    ($(($name:ident, $modification:expr)),* $(,)?) => {$(
        fn $name<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            read_modify_write(machine, args, $modification)
        }
    )*};
}

read_modify_write_handlers!(
    (add, Modification::Add),
    (and, Modification::And),
    (exchange, Modification::Exchange),
    (or, Modification::Or),
    (sub, Modification::Sub),
    (xor, Modification::Xor),
);

fn compare_exchange<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let view = argument(args, 0);
    let snapshot = validate_integer_typed_array(machine, view, false)?;
    let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
    let (_, expected) = coerce_operand(machine, snapshot.kind, argument(args, 2))?;
    let (_, replacement) = coerce_operand(machine, snapshot.kind, argument(args, 3))?;
    revalidate_atomic_access(machine, view, position)?;
    let old = update_element(machine, &snapshot, position, |old| {
        if old == expected { replacement } else { old }
    })?;
    value_from_storage(machine, snapshot.kind, old).map(BuiltinOutcome::Value)
}

fn load<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let view = argument(args, 0);
    let snapshot = validate_integer_typed_array(machine, view, false)?;
    let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
    revalidate_atomic_access(machine, view, position)?;
    let size = snapshot.kind.element_size();
    let mut storage = [0_u8; 8];
    snapshot.buffer.with_bytes(machine, |bytes| {
        storage[..size].copy_from_slice(&bytes[position..position + size]);
    })?;
    value_from_storage(machine, snapshot.kind, storage).map(BuiltinOutcome::Value)
}

fn store<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let view = argument(args, 0);
    let snapshot = validate_integer_typed_array(machine, view, false)?;
    let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
    let (operand, storage) = coerce_operand(machine, snapshot.kind, argument(args, 2))?;
    revalidate_atomic_access(machine, view, position)?;
    update_element(machine, &snapshot, position, |_| storage)?;
    Ok(BuiltinOutcome::Value(operand))
}

/// Every element size is a plain machine word on the supported targets. The
/// runtime serializes access with the block's lock, which only one agent ever
/// takes, so `true` overstates nothing a program can observe.
fn is_lock_free<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let size = integer_or_infinity(machine, argument(args, 0))?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        [1.0, 2.0, 4.0, 8.0].contains(&size),
    )))
}

fn pause<H: Host>(
    _machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let integral = match argument(args, 0).decode() {
        Some(Decoded::Undefined | Decoded::Int32(_)) => true,
        Some(Decoded::Number(number)) => number.is_finite() && number.fract() == 0.0,
        _ => false,
    };
    if !integral {
        return Err(type_error("Atomics.pause requires an integral Number"));
    }
    std::hint::spin_loop();
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::{Limits, ThrowOrigin};

    fn atomics(machine: &Machine<'_, TestHost>) -> Value {
        machine
            .intrinsics
            .global("Atomics")
            .expect("Atomics is installed")
    }

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("<atomics-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn shared_buffer(
        machine: &mut Machine<'_, TestHost>,
        length: i32,
        maximum: Option<u32>,
    ) -> Value {
        let constructor = machine
            .intrinsics
            .global("SharedArrayBuffer")
            .expect("SharedArrayBuffer is installed");
        let options = match maximum {
            None => Value::UNDEFINED,
            Some(maximum) => {
                let options = crate::builtins::ordinary_runtime(machine, None).unwrap();
                machine
                    .set_data_property(options, "maxByteLength", Value::int32(maximum))
                    .unwrap();
                options
            }
        };
        machine
            .construct_value(constructor, &[Value::int32(length as u32), options])
            .expect("SharedArrayBuffer construction succeeds")
    }

    fn view_of(machine: &mut Machine<'_, TestHost>, kind: &str, buffer: Value) -> Value {
        let constructor = machine.intrinsics.global(kind).expect("view constructor");
        machine
            .construct_value(constructor, &[buffer])
            .expect("view construction succeeds")
    }

    fn call(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        method: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let function = machine.get_named_property(receiver, method).unwrap();
        machine.call_value(function, receiver, args)
    }

    #[test]
    fn views_of_one_block_observe_each_other_through_slice_and_grow() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 4, Some(8));
            let bytes = view_of(machine, "Uint8Array", buffer);
            machine
                .set_data_property(bytes, "1", Value::int32(7))
                .unwrap();

            let sliced = call(machine, buffer, "slice", &[Value::int32(1)]).unwrap();
            assert_eq!(
                machine.get_named_property(sliced, "byteLength").unwrap(),
                Value::int32(3)
            );
            let sliced_bytes = view_of(machine, "Uint8Array", sliced);
            assert_eq!(
                machine.get_named_property(sliced_bytes, "0").unwrap(),
                Value::int32(7)
            );

            call(machine, buffer, "grow", &[Value::int32(8)]).unwrap();
            assert_eq!(
                machine.get_named_property(bytes, "length").unwrap(),
                Value::int32(8),
                "a length-tracking view follows the block"
            );
            assert_eq!(
                machine.get_named_property(bytes, "1").unwrap(),
                Value::int32(7),
                "growing keeps the existing bytes"
            );
        });
    }

    #[test]
    fn store_returns_the_coerced_operand_while_the_element_wraps() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let bytes = view_of(machine, "Int8Array", buffer);
            let namespace = atomics(machine);
            let stored = call(
                machine,
                namespace,
                "store",
                &[bytes, Value::int32(0), crate::number_value(257.75)],
            )
            .unwrap();
            assert_eq!(stored, crate::number_value(257.0));
            assert_eq!(
                machine.get_named_property(bytes, "0").unwrap(),
                Value::int32(1)
            );
            let stored = call(
                machine,
                namespace,
                "store",
                &[bytes, Value::int32(0), crate::number_value(-0.5)],
            )
            .unwrap();
            assert!(
                super::super::value_number(stored).is_sign_positive(),
                "ToIntegerOrInfinity(-0.5) is +0"
            );
        });
    }

    #[test]
    fn read_modify_write_wraps_at_the_element_width_and_returns_the_old_value() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let bytes = view_of(machine, "Uint8Array", buffer);
            machine
                .set_data_property(bytes, "1", Value::int32(9))
                .unwrap();
            machine
                .set_data_property(bytes, "0", Value::int32(255))
                .unwrap();
            let namespace = atomics(machine);
            let old = call(
                machine,
                namespace,
                "add",
                &[bytes, Value::int32(0), Value::int32(2)],
            )
            .unwrap();
            assert_eq!(old, Value::int32(255));
            assert_eq!(
                machine.get_named_property(bytes, "0").unwrap(),
                Value::int32(1)
            );
            assert_eq!(
                machine.get_named_property(bytes, "1").unwrap(),
                Value::int32(9),
                "the carry must not reach the next element"
            );
        });
    }

    #[test]
    fn compare_exchange_replaces_only_on_a_match_of_the_wrapped_bytes() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let bytes = view_of(machine, "Uint8Array", buffer);
            machine
                .set_data_property(bytes, "0", Value::int32(1))
                .unwrap();
            let namespace = atomics(machine);
            for (expected, replacement, element) in [(2, 7, 1), (257, 7, 7)] {
                call(
                    machine,
                    namespace,
                    "compareExchange",
                    &[
                        bytes,
                        Value::int32(0),
                        Value::int32(expected),
                        Value::int32(replacement),
                    ],
                )
                .unwrap();
                assert_eq!(
                    machine.get_named_property(bytes, "0").unwrap(),
                    Value::int32(element)
                );
            }
        });
    }

    #[test]
    fn floating_and_clamped_views_are_rejected_before_the_index_is_read() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            for kind in ["Float64Array", "Uint8ClampedArray"] {
                let view = view_of(machine, kind, buffer);
                let namespace = atomics(machine);
                assert!(matches!(
                    call(
                        machine,
                        namespace,
                        "load",
                        &[view, crate::number_value(-1.0)]
                    ),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ));
            }
        });
    }

    #[test]
    fn grow_rejects_shrinking_and_passing_the_maximum_and_fixed_blocks() {
        with_machine(|machine| {
            let growable = shared_buffer(machine, 4, Some(8));
            for length in [3, 9] {
                assert!(matches!(
                    call(machine, growable, "grow", &[Value::int32(length)]),
                    Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                ));
            }
            let fixed = shared_buffer(machine, 4, None);
            assert!(matches!(
                call(machine, fixed, "grow", &[Value::int32(4)]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }
}
