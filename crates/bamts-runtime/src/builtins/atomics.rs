//! SharedArrayBuffer over the shared data block in `arraybuffer.rs`, and the
//! Atomics operations over TypedArray views of it.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::arraybuffer::{
    SharedBlock, Suspension, Waiter, grow_shared_array_buffer, species_constructor,
    to_clamped_index, to_index,
};
use super::bigint;
use super::typedarray_all::{
    ElementKind, TypedArraySnapshot, ViewBuffer, integer_or_infinity, storage_from_value,
    typed_array_snapshot, value_from_storage,
};
use super::{
    allocate_string, define_data, define_to_string_tag, heap_index, install_constructor_function,
    install_function, range_error, type_error, value_number,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    install_shared_array_buffer(heap, atoms, shapes, globals, builtins);
    install_atomics(heap, atoms, shapes, globals, builtins);
}

fn install_shared_array_buffer<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "SharedArrayBuffer",
            length: 1,
            handler: constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    builtins.set_sharedarraybuffer_constructor(constructor);
    builtins.set_sharedarraybuffer_prototype(prototype);
    define_data(heap, atoms, shapes, prototype, "constructor", constructor);
    for (name, length, handler) in [
        ("grow", 1, grow::<H> as BuiltinHandler<H>),
        ("slice", 2, slice::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, prototype, name, function);
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
        let getter = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: function_name,
                length: 0,
                handler,
            },
        );
        let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
            unreachable!("SharedArrayBuffer.prototype is ordinary")
        };
        properties.insert(
            shapes,
            PropertyKey::Named(atoms.intern_str(property_name)),
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }
    let species = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get [Symbol.species]",
            length: 0,
            handler: species::<H>,
        },
    );
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        unreachable!("SharedArrayBuffer constructor is native")
    };
    properties.insert(
        shapes,
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
        shapes,
        prototype,
        builtins.symbol_to_string_tag(),
        "SharedArrayBuffer",
    );
    globals.insert(EcmaString::encode("SharedArrayBuffer"), constructor);
}

fn install_atomics<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
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
        ("notify", 3, notify::<H>),
        ("or", 3, or::<H>),
        ("pause", 0, pause::<H>),
        ("store", 3, store::<H>),
        ("sub", 3, sub::<H>),
        ("wait", 4, wait::<H>),
        ("waitAsync", 4, wait_async::<H>),
        ("xor", 3, xor::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, atomics, name, function);
    }
    let timeout = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "",
            length: 1,
            handler: wait_async_timeout::<H>,
        },
    );
    builtins.set_wait_async_timeout(timeout);
    define_to_string_tag(
        heap,
        shapes,
        atomics,
        builtins.symbol_to_string_tag(),
        "Atomics",
    );
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

/// RevalidateAtomicAccess, for after a coercion that may have run guest code. A
/// buffer can shrink to end inside the element, so the whole element must fit.
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
    let end = position + snapshot.kind.element_size();
    if end > snapshot.buffer.byte_length(machine)? {
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

/// The validated, coerced arguments of DoWait, up to the critical section.
struct WaitRequest {
    block: Arc<SharedBlock>,
    position: usize,
    size: usize,
    expected: [u8; 8],
    /// `None` is a wait with no timeout.
    timeout_ms: Option<f64>,
}

impl WaitRequest {
    fn parse<H: Host>(machine: &mut Machine<'_, H>, args: &[Value]) -> Result<Self, EvalFailure> {
        let snapshot = validate_integer_typed_array(machine, argument(args, 0), true)?;
        let ViewBuffer::Shared(block) = &snapshot.buffer else {
            return Err(type_error("Atomics wait operations require shared memory"));
        };
        let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
        let expected = storage_from_value(machine, snapshot.kind, argument(args, 2))?;
        let timeout = value_number(machine.coerce_number_observable(argument(args, 3))?);
        Ok(Self {
            block: Arc::clone(block),
            position,
            size: snapshot.kind.element_size(),
            expected,
            timeout_ms: (!timeout.is_nan() && timeout != f64::INFINITY).then(|| timeout.max(0.0)),
        })
    }

    /// Must be asked inside the waiter critical section: a writer changes the
    /// value before it notifies, so it either is seen here or finds the waiter.
    fn value_is_expected(&self) -> bool {
        self.block.with_bytes(|bytes| {
            bytes[self.position..self.position + self.size] == self.expected[..self.size]
        })
    }
}

fn wait<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let request = WaitRequest::parse(machine, args)?;
    if !machine.limits.agent_can_suspend {
        return Err(type_error("Atomics.wait cannot suspend this agent"));
    }
    let suspension = Arc::new(Suspension::default());
    let waiter = Waiter::Blocking(Arc::clone(&suspension));
    {
        let mut waiters = request.block.waiters();
        if !request.value_is_expected() {
            drop(waiters);
            return string_outcome(machine, "not-equal");
        }
        waiters.add(request.position, waiter.clone());
    }
    let deadline = request
        .timeout_ms
        .and_then(|milliseconds| Duration::try_from_secs_f64(milliseconds / 1000.0).ok())
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let woken = suspension.wait(deadline, &machine.cancel)
        || !request.block.waiters().remove(request.position, &waiter);
    if woken {
        return string_outcome(machine, "ok");
    }
    machine.check_cancel().map_err(EvalFailure::Runtime)?;
    string_outcome(machine, "timed-out")
}

fn notify<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let snapshot = validate_integer_typed_array(machine, argument(args, 0), true)?;
    let position = validate_atomic_access(machine, &snapshot, argument(args, 1))?;
    let count = match argument(args, 2) {
        Value::UNDEFINED => usize::MAX,
        // A float-to-integer cast saturates, which is what infinity asks for.
        value => integer_or_infinity(machine, value)?.max(0.0) as usize,
    };
    let ViewBuffer::Shared(block) = &snapshot.buffer else {
        return Ok(BuiltinOutcome::Value(Value::int32(0)));
    };
    let woken = block.waiters().take(position, count);
    for waiter in &woken {
        match waiter {
            Waiter::Blocking(suspension) => suspension.wake(),
            Waiter::Async(id) => settle_async_waiter(machine, *id, "ok")?,
        }
    }
    Ok(BuiltinOutcome::Value(crate::number_value(
        woken.len() as f64
    )))
}

/// A pending `Atomics.waitAsync`. The block's waiter list holds only its id,
/// because the collector cannot see a `Value` inside a block; the machine owns
/// this record and traces `promise`.
#[derive(Debug)]
pub(crate) struct AsyncWaiter {
    pub(crate) promise: Value,
    block: Arc<SharedBlock>,
    position: usize,
    /// The armed timeout's handle, when the wait has one.
    timer: Option<Value>,
    /// What is left of a timeout too long for one timer.
    remaining_ms: u64,
}

/// Arms a timer for as much of `timeout_ms` as one [`crate::TimerProvider`] delay
/// can hold, and returns its handle with the part that is left over.
fn arm_async_timeout<H: Host>(
    machine: &mut Machine<'_, H>,
    id: u64,
    timeout_ms: u64,
) -> Result<(Value, u64), EvalFailure> {
    let delay = u32::try_from(timeout_ms).unwrap_or(u32::MAX);
    let callback = machine.intrinsics.builtins.wait_async_timeout();
    let handle = machine.schedule_timeout(callback, delay, vec![crate::number_value(id as f64)])?;
    Ok((handle, timeout_ms - u64::from(delay)))
}

/// NotifyWaiter for a waiter of this agent: resolves the promise at once, so
/// its reactions run at the next microtask checkpoint.
fn settle_async_waiter<H: Host>(
    machine: &mut Machine<'_, H>,
    id: u64,
    result: &str,
) -> Result<(), EvalFailure> {
    let Some(waiter) = machine.async_waiters.remove(&id) else {
        return Ok(());
    };
    if let Some(timer) = waiter.timer {
        machine.clear_timeout(timer)?;
    }
    let value = allocate_string(machine, EcmaString::encode(result))?;
    machine
        .fulfill_promise(waiter.promise, value)
        .map_err(EvalFailure::Runtime)
}

/// The timer callback behind every timed `Atomics.waitAsync`. No script can
/// reach it: the only reference is the timer record that calls it.
fn wait_async_timeout<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let id = value_number(argument(args, 0)) as u64;
    if let Some(waiter) = machine.async_waiters.get(&id) {
        if waiter.remaining_ms == 0 {
            waiter
                .block
                .waiters()
                .remove(waiter.position, &Waiter::Async(id));
            settle_async_waiter(machine, id, "timed-out")?;
        } else {
            let remaining_ms = waiter.remaining_ms;
            let (timer, remaining_ms) = arm_async_timeout(machine, id, remaining_ms)?;
            if let Some(waiter) = machine.async_waiters.get_mut(&id) {
                waiter.timer = Some(timer);
                waiter.remaining_ms = remaining_ms;
            }
        }
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn wait_async_result<H: Host>(
    machine: &mut Machine<'_, H>,
    asynchronous: bool,
    value: Value,
) -> Result<Value, EvalFailure> {
    let prototype = machine.intrinsics.object_prototype;
    let object = super::ordinary_runtime(machine, Some(prototype))?;
    for (name, value) in [("async", Value::boolean(asynchronous)), ("value", value)] {
        let key = PropertyKey::Named(machine.intern_str(name));
        machine.create_data_property_key(object, key, value)?;
    }
    Ok(object)
}

fn wait_async_settled<H: Host>(
    machine: &mut Machine<'_, H>,
    outcome: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = allocate_string(machine, EcmaString::encode(outcome))?;
    wait_async_result(machine, false, value).map(BuiltinOutcome::Value)
}

fn wait_async<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let request = WaitRequest::parse(machine, args)?;
    let block = Arc::clone(&request.block);
    let mut waiters = block.waiters();
    if !request.value_is_expected() {
        drop(waiters);
        return wait_async_settled(machine, "not-equal");
    }
    if request.timeout_ms == Some(0.0) {
        drop(waiters);
        return wait_async_settled(machine, "timed-out");
    }
    let promise = machine.create_promise()?;
    let result = wait_async_result(machine, true, promise)?;
    let id = machine.next_async_waiter;
    machine.next_async_waiter += 1;
    let (timer, remaining_ms) = match request.timeout_ms {
        None => (None, 0),
        // A cast saturates, and a fraction of a millisecond still has to pass.
        Some(milliseconds) => {
            let (timer, remaining_ms) = arm_async_timeout(machine, id, milliseconds.ceil() as u64)?;
            (Some(timer), remaining_ms)
        }
    };
    machine.async_waiters.insert(
        id,
        AsyncWaiter {
            promise,
            block: Arc::clone(&request.block),
            position: request.position,
            timer,
            remaining_ms,
        },
    );
    waiters.add(request.position, Waiter::Async(id));
    Ok(BuiltinOutcome::Value(result))
}

fn string_outcome<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    allocate_string(machine, EcmaString::encode(text)).map(BuiltinOutcome::Value)
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{
        CancellationToken, Limits, PromiseState, RuntimeErrorKind, ThrowOrigin, TimerError,
        TimerProvider, TimerWakeup,
    };

    /// A clock that moves only when the event loop waits, straight to the next
    /// deadline, so a timeout of any length takes no real time.
    #[derive(Default)]
    struct ManualTimers {
        armed: Vec<TimerWakeup>,
        now_ms: u64,
    }

    impl TimerProvider for ManualTimers {
        fn schedule(&mut self, id: u64, delay_ms: u32) -> Result<u64, TimerError> {
            let deadline_ms = self.now_ms + u64::from(delay_ms);
            self.armed.push(TimerWakeup { id, deadline_ms });
            Ok(deadline_ms)
        }

        fn cancel(&mut self, id: u64) -> Result<bool, TimerError> {
            let armed = self.armed.len();
            self.armed.retain(|timer| timer.id != id);
            Ok(self.armed.len() != armed)
        }

        fn poll_expired(&mut self, _output: &mut Vec<TimerWakeup>) -> Result<(), TimerError> {
            Ok(())
        }

        fn wait_expired(
            &mut self,
            _cancel: &CancellationToken,
        ) -> Result<Option<TimerWakeup>, TimerError> {
            let next = (0..self.armed.len()).min_by_key(|&index| self.armed[index].deadline_ms);
            Ok(next.map(|index| {
                let wakeup = self.armed.remove(index);
                self.now_ms = wakeup.deadline_ms;
                wakeup
            }))
        }

        fn has_pending(&self) -> bool {
            !self.armed.is_empty()
        }
    }

    #[derive(Default)]
    struct TimerHost {
        timers: ManualTimers,
    }

    impl Host for TimerHost {
        fn timers(&mut self) -> Option<&mut (dyn TimerProvider + 'static)> {
            Some(&mut self.timers)
        }
    }

    fn with_timers(test: impl FnOnce(&mut Machine<'_, TimerHost>)) -> TimerHost {
        let program = blank_program("<atomics-test>");
        let mut host = TimerHost::default();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
        drop(machine);
        host
    }

    fn atomics<H: Host>(machine: &Machine<'_, H>) -> Value {
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

    fn shared_buffer<H: Host>(
        machine: &mut Machine<'_, H>,
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

    fn view_of<H: Host>(machine: &mut Machine<'_, H>, kind: &str, buffer: Value) -> Value {
        let constructor = machine.intrinsics.global(kind).expect("view constructor");
        machine
            .construct_value(constructor, &[buffer])
            .expect("view construction succeeds")
    }

    fn call<H: Host>(
        machine: &mut Machine<'_, H>,
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

    fn result_is<H: Host>(machine: &Machine<'_, H>, value: Value, expected: &str) -> bool {
        machine
            .string_value(value)
            .is_some_and(|text| text.eq_ascii(expected))
    }

    #[test]
    fn wait_compares_the_value_before_it_suspends() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let view = view_of(machine, "Int32Array", buffer);
            let namespace = atomics(machine);
            let result = call(
                machine,
                namespace,
                "wait",
                &[view, Value::int32(0), Value::int32(1)],
            )
            .unwrap();
            assert!(result_is(machine, result, "not-equal"));
        });
    }

    #[test]
    fn wait_blocks_for_its_timeout_and_leaves_no_waiter_behind() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let view = view_of(machine, "Int32Array", buffer);
            let namespace = atomics(machine);
            let started = Instant::now();
            let result = call(
                machine,
                namespace,
                "wait",
                &[view, Value::int32(0), Value::int32(0), Value::int32(30)],
            )
            .unwrap();
            assert!(result_is(machine, result, "timed-out"));
            assert!(started.elapsed() >= Duration::from_millis(30));
            let woken = call(machine, namespace, "notify", &[view, Value::int32(0)]).unwrap();
            assert_eq!(woken, Value::int32(0));
        });
    }

    #[test]
    fn a_notifier_on_another_thread_wakes_a_suspended_wait() {
        with_machine(|machine| {
            let buffer = shared_buffer(machine, 8, None);
            let view = view_of(machine, "Int32Array", buffer);
            let block = shared_block(machine, buffer).unwrap();
            let namespace = atomics(machine);
            let notifier = std::thread::spawn(move || {
                loop {
                    let woken = block.waiters().take(0, 1);
                    if let [Waiter::Blocking(suspension)] = woken.as_slice() {
                        suspension.wake();
                        return;
                    }
                    std::thread::yield_now();
                }
            });
            let result = call(
                machine,
                namespace,
                "wait",
                &[view, Value::int32(0), Value::int32(0)],
            )
            .unwrap();
            notifier.join().unwrap();
            assert!(result_is(machine, result, "ok"));
        });
    }

    #[test]
    fn cancellation_ends_an_unbounded_wait_and_withdraws_its_waiter() {
        let program = blank_program("<atomics-test>");
        let mut host = TestHost;
        let cancel = CancellationToken::new();
        let mut machine =
            Machine::new_with_cancel(&program, &mut host, Limits::default(), cancel.clone());
        let buffer = shared_buffer(&mut machine, 8, None);
        let view = view_of(&mut machine, "Int32Array", buffer);
        let block = shared_block(&machine, buffer).unwrap();
        let namespace = atomics(&machine);
        let canceller = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(10));
            cancel.cancel();
        });
        let result = call(
            &mut machine,
            namespace,
            "wait",
            &[view, Value::int32(0), Value::int32(0)],
        );
        canceller.join().unwrap();
        assert!(matches!(
            result,
            Err(EvalFailure::Runtime(RuntimeErrorKind::Cancelled))
        ));
        assert!(block.waiters().take(0, usize::MAX).is_empty());
    }

    #[test]
    fn waiters_queue_per_position_and_wake_oldest_first() {
        let block = SharedBlock::new(vec![0; 16], None);
        let mut list = block.waiters();
        list.add(0, Waiter::Async(1));
        list.add(8, Waiter::Async(2));
        list.add(0, Waiter::Async(3));
        assert!(matches!(list.take(0, 1).as_slice(), [Waiter::Async(1)]));
        assert!(!list.remove(0, &Waiter::Async(1)), "a taken waiter is gone");
        assert!(list.remove(0, &Waiter::Async(3)));
        assert!(list.take(0, usize::MAX).is_empty());
        assert!(matches!(
            list.take(8, usize::MAX).as_slice(),
            [Waiter::Async(2)]
        ));
    }

    #[test]
    fn wait_is_refused_on_unshared_memory_and_views_that_cannot_wait() {
        with_machine(|machine| {
            let namespace = atomics(machine);
            let unshared = machine.intrinsics.global("ArrayBuffer").unwrap();
            let unshared = machine
                .construct_value(unshared, &[Value::int32(8)])
                .unwrap();
            let unshared = view_of(machine, "Int32Array", unshared);
            let shared = shared_buffer(machine, 8, None);
            let bytes = view_of(machine, "Uint8Array", shared);
            for view in [unshared, bytes] {
                assert!(matches!(
                    call(
                        machine,
                        namespace,
                        "wait",
                        &[view, Value::int32(0), Value::int32(0), Value::int32(0)]
                    ),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ));
            }
            let woken = call(machine, namespace, "notify", &[unshared, Value::int32(0)]).unwrap();
            assert_eq!(
                woken,
                Value::int32(0),
                "notify on unshared memory is a no-op"
            );
        });
    }

    #[test]
    fn an_agent_that_cannot_suspend_rejects_wait_after_validating_its_arguments() {
        let program = blank_program("<atomics-test>");
        let mut host = TestHost;
        let limits = Limits {
            agent_can_suspend: false,
            ..Limits::default()
        };
        let mut machine = Machine::new(&program, &mut host, limits);
        let buffer = shared_buffer(&mut machine, 8, None);
        let view = view_of(&mut machine, "Int32Array", buffer);
        let namespace = atomics(&machine);
        assert!(matches!(
            call(
                &mut machine,
                namespace,
                "wait",
                &[view, Value::int32(0), Value::int32(0), Value::int32(0)]
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            call(
                &mut machine,
                namespace,
                "wait",
                &[view, Value::int32(99), Value::int32(0), Value::int32(0)]
            ),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }

    fn int32_view<H: Host>(machine: &mut Machine<'_, H>) -> Value {
        let buffer = shared_buffer(machine, 8, None);
        view_of(machine, "Int32Array", buffer)
    }

    /// Returns the promise of an `Atomics.waitAsync(view, 0, 0, timeout)` that
    /// went asynchronous.
    fn pending_wait<H: Host>(machine: &mut Machine<'_, H>, view: Value, timeout: Value) -> Value {
        let namespace = atomics(machine);
        let result = call(
            machine,
            namespace,
            "waitAsync",
            &[view, Value::int32(0), Value::int32(0), timeout],
        )
        .unwrap();
        assert_eq!(
            machine.get_named_property(result, "async").unwrap(),
            Value::TRUE
        );
        machine.get_named_property(result, "value").unwrap()
    }

    fn fulfilled_with<H: Host>(machine: &Machine<'_, H>, promise: Value, expected: &str) -> bool {
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise { state, .. } = &machine.heap[index] else {
            panic!("waitAsync value is a Promise");
        };
        matches!(state, PromiseState::Fulfilled { value } if result_is(machine, *value, expected))
    }

    fn notify_all<H: Host>(machine: &mut Machine<'_, H>, view: Value) -> Value {
        let namespace = atomics(machine);
        call(machine, namespace, "notify", &[view, Value::int32(0)]).unwrap()
    }

    #[test]
    fn wait_async_answers_without_a_promise_when_it_need_not_wait() {
        with_machine(|machine| {
            let view = int32_view(machine);
            let namespace = atomics(machine);
            for (expected, timeout, outcome) in [
                (Value::int32(1), Value::UNDEFINED, "not-equal"),
                (Value::int32(0), Value::int32(0), "timed-out"),
                (Value::int32(0), crate::number_value(-1.0), "timed-out"),
            ] {
                let result = call(
                    machine,
                    namespace,
                    "waitAsync",
                    &[view, Value::int32(0), expected, timeout],
                )
                .unwrap();
                assert_eq!(
                    machine.get_named_property(result, "async").unwrap(),
                    Value::FALSE
                );
                let value = machine.get_named_property(result, "value").unwrap();
                assert!(result_is(machine, value, outcome));
            }
            assert_eq!(notify_all(machine, view), Value::int32(0));
        });
    }

    #[test]
    fn notify_settles_a_timed_wait_at_once_and_disarms_its_timer() {
        with_timers(|machine| {
            let view = int32_view(machine);
            let promise = pending_wait(machine, view, Value::int32(1000));
            assert!(machine.has_pending_timers());
            assert_eq!(notify_all(machine, view), Value::int32(1));
            assert!(
                fulfilled_with(machine, promise, "ok"),
                "a waiter of this agent resolves inside notify"
            );
            assert!(!machine.has_pending_timers());
            assert_eq!(notify_all(machine, view), Value::int32(0));
        });
    }

    #[test]
    fn a_timeout_settles_through_the_host_timer_and_empties_the_list() {
        let host = with_timers(|machine| {
            let view = int32_view(machine);
            let promise = pending_wait(machine, view, crate::number_value(10.5));
            machine.run_to_quiescence().unwrap();
            assert!(fulfilled_with(machine, promise, "timed-out"));
            assert_eq!(notify_all(machine, view), Value::int32(0));
        });
        assert_eq!(host.timers.now_ms, 11, "a timeout is never cut short");
    }

    #[test]
    fn a_timeout_longer_than_one_timer_waits_out_all_of_it() {
        let timeout = 3 * (u64::from(u32::MAX) + 1);
        let host = with_timers(|machine| {
            let view = int32_view(machine);
            let promise = pending_wait(machine, view, crate::number_value(timeout as f64));
            machine.run_to_quiescence().unwrap();
            assert!(fulfilled_with(machine, promise, "timed-out"));
        });
        assert_eq!(host.timers.now_ms, timeout);
    }

    #[test]
    fn notify_wakes_async_waiters_oldest_first_up_to_its_count() {
        with_machine(|machine| {
            let view = int32_view(machine);
            let first = pending_wait(machine, view, Value::UNDEFINED);
            let second = pending_wait(machine, view, Value::UNDEFINED);
            let namespace = atomics(machine);
            let woken = call(
                machine,
                namespace,
                "notify",
                &[view, Value::int32(0), Value::int32(1)],
            )
            .unwrap();
            assert_eq!(woken, Value::int32(1));
            assert!(fulfilled_with(machine, first, "ok"));
            assert!(!fulfilled_with(machine, second, "ok"));
            assert_eq!(notify_all(machine, view), Value::int32(1));
            assert!(fulfilled_with(machine, second, "ok"));
        });
    }

    #[test]
    fn an_untimed_wait_does_not_keep_the_event_loop_alive() {
        with_machine(|machine| {
            let view = int32_view(machine);
            let promise = pending_wait(machine, view, Value::UNDEFINED);
            machine.run_to_quiescence().unwrap();
            assert!(!fulfilled_with(machine, promise, "ok"));
        });
    }

    #[test]
    fn a_pending_promise_survives_collection_with_nothing_else_holding_it() {
        with_machine(|machine| {
            let view = int32_view(machine);
            machine.test_set_global("view", view);
            let promise = pending_wait(machine, view, Value::UNDEFINED);
            machine.collect_garbage();
            assert_eq!(notify_all(machine, view), Value::int32(1));
            assert!(fulfilled_with(machine, promise, "ok"));
        });
    }

    #[test]
    fn a_script_cannot_cancel_a_wait_timeout_by_guessing_its_timer_number() {
        with_timers(|machine| {
            let view = int32_view(machine);
            let promise = pending_wait(machine, view, Value::int32(5));
            let timer = *machine.timers.keys().next().unwrap();
            machine
                .clear_timeout(Value::int32(u32::try_from(timer).unwrap()))
                .unwrap();
            machine.run_to_quiescence().unwrap();
            assert!(fulfilled_with(machine, promise, "timed-out"));
        });
    }

    #[test]
    fn a_timed_wait_fails_loudly_on_a_host_without_timers() {
        with_machine(|machine| {
            let view = int32_view(machine);
            let namespace = atomics(machine);
            assert!(matches!(
                call(
                    machine,
                    namespace,
                    "waitAsync",
                    &[view, Value::int32(0), Value::int32(0), Value::int32(5)]
                ),
                Err(EvalFailure::Runtime(
                    RuntimeErrorKind::TimerProviderFailure { .. }
                ))
            ));
            assert_eq!(
                notify_all(machine, view),
                Value::int32(0),
                "a wait that failed to arm leaves no waiter"
            );
        });
    }

    #[test]
    fn buffers_and_data_views_report_their_own_properties() {
        with_machine(|machine| {
            let shared = shared_buffer(machine, 8, None);
            let data_view = view_of(machine, "DataView", shared);
            let unshared = machine.intrinsics.global("ArrayBuffer").unwrap();
            let unshared = machine
                .construct_value(unshared, &[Value::int32(8)])
                .unwrap();
            for object in [shared, data_view, unshared] {
                machine
                    .set_data_property(object, "marker", Value::int32(1))
                    .unwrap();
                let key = PropertyKey::Named(machine.intern_str("marker"));
                assert!(machine.own_descriptor(object, &key).unwrap().is_some());
                assert_eq!(machine.enumerable_keys(object).unwrap().len(), 1);
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

    /// `valueOf` of an object: shrinks the object's `buffer` to end inside the
    /// second element of an `Int32Array`, then answers 1.
    fn shrink_buffer(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let buffer = machine.get_named_property(this, "buffer")?;
        call(machine, buffer, "resize", &[Value::int32(6)])?;
        Ok(BuiltinOutcome::Value(Value::int32(1)))
    }

    /// The arguments of one Atomics call, from the view and the shrinking operand.
    type Arguments = fn(Value, Value) -> Vec<Value>;

    #[test]
    fn a_buffer_that_shrinks_inside_the_element_is_a_range_error() {
        with_machine(|machine| {
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "valueOf",
                length: 0,
                handler: shrink_buffer,
            });
            let value_of = native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "valueOf",
                0,
            );
            let atomics = atomics(machine);
            let constructor = machine.intrinsics.global("ArrayBuffer").unwrap();
            let operations: [(&str, Arguments); 4] = [
                ("add", |view, shrinks| vec![view, Value::int32(1), shrinks]),
                ("load", |view, shrinks| vec![view, shrinks]),
                ("store", |view, shrinks| {
                    vec![view, Value::int32(1), shrinks]
                }),
                ("compareExchange", |view, shrinks| {
                    vec![view, Value::int32(1), shrinks, Value::int32(0)]
                }),
            ];
            for (method, arguments) in operations {
                let options = crate::builtins::ordinary_runtime(machine, None).unwrap();
                machine
                    .set_data_property(options, "maxByteLength", Value::int32(8))
                    .unwrap();
                let buffer = machine
                    .construct_value(constructor, &[Value::int32(8), options])
                    .unwrap();
                let view = view_of(machine, "Int32Array", buffer);
                let shrinks = crate::builtins::ordinary_runtime(machine, None).unwrap();
                machine
                    .set_data_property(shrinks, "valueOf", value_of)
                    .unwrap();
                machine
                    .set_data_property(shrinks, "buffer", buffer)
                    .unwrap();
                assert!(
                    matches!(
                        call(machine, atomics, method, &arguments(view, shrinks)),
                        Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                    ),
                    "{method}"
                );
            }
        });
    }
}
