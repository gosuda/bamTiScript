use std::collections::{BTreeMap, VecDeque};
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use bamts_bytecode::EcmaString;
use bamts_cancel::CancellationToken;
use bamts_native::{Decoded, Value};

use super::{
    builtin_property, define_data, heap_index, install_constructor_function, install_function,
    range_error, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// How often a suspended agent looks for cancellation, which has no wake signal.
const CANCELLATION_POLL: Duration = Duration::from_millis(20);

/// One agent suspended in `Atomics.wait`.
#[derive(Debug, Default)]
pub(crate) struct Suspension {
    notified: Mutex<bool>,
    ready: Condvar,
}

impl Suspension {
    pub(crate) fn wake(&self) {
        *self
            .notified
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = true;
        self.ready.notify_one();
    }

    /// Suspends until woken, past `deadline`, or until `cancel` fires, and
    /// reports whether this agent was woken.
    pub(crate) fn wait(&self, deadline: Option<Instant>, cancel: &CancellationToken) -> bool {
        let mut notified = self
            .notified
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while !*notified && !cancel.is_cancelled() {
            let remaining = deadline.map_or(CANCELLATION_POLL, |deadline| {
                deadline.saturating_duration_since(Instant::now())
            });
            if remaining.is_zero() {
                break;
            }
            (notified, _) = self
                .ready
                .wait_timeout(notified, remaining.min(CANCELLATION_POLL))
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
        *notified
    }
}

/// A Waiter Record.
#[derive(Clone, Debug)]
pub(crate) enum Waiter {
    Blocking(Arc<Suspension>),
    /// `Atomics.waitAsync`, as the id of the machine's record of it.
    Async(u64),
}

impl Waiter {
    fn is(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Blocking(left), Self::Blocking(right)) => Arc::ptr_eq(left, right),
            (Self::Async(left), Self::Async(right)) => left == right,
            _ => false,
        }
    }
}

/// The WaiterList of one shared block: a queue per byte position, oldest first.
#[derive(Debug, Default)]
pub(crate) struct WaiterList {
    queues: BTreeMap<usize, VecDeque<Waiter>>,
}

impl WaiterList {
    pub(crate) fn add(&mut self, position: usize, waiter: Waiter) {
        self.queues.entry(position).or_default().push_back(waiter);
    }

    /// Reports whether `waiter` was still queued. It is not once a notifier has
    /// taken it, which is how a timeout that lost that race learns it did.
    pub(crate) fn remove(&mut self, position: usize, waiter: &Waiter) -> bool {
        let Some(queue) = self.queues.get_mut(&position) else {
            return false;
        };
        let Some(index) = queue.iter().position(|queued| queued.is(waiter)) else {
            return false;
        };
        queue.remove(index);
        if queue.is_empty() {
            self.queues.remove(&position);
        }
        true
    }

    /// RemoveWaiters: up to `count` waiters at `position`, oldest first.
    pub(crate) fn take(&mut self, position: usize, count: usize) -> Vec<Waiter> {
        let Some(queue) = self.queues.get_mut(&position) else {
            return Vec::new();
        };
        let taken = queue.drain(..count.min(queue.len())).collect();
        if queue.is_empty() {
            self.queues.remove(&position);
        }
        taken
    }
}

#[derive(Debug)]
pub(crate) struct SharedBlock {
    state: Mutex<SharedBlockState>,
    waiters: Mutex<WaiterList>,
}

#[derive(Debug)]
struct SharedBlockState {
    bytes: Vec<u8>,
    max_byte_length: Option<usize>,
}

impl SharedBlock {
    pub(crate) fn new(bytes: Vec<u8>, max_byte_length: Option<usize>) -> Self {
        Self {
            state: Mutex::new(SharedBlockState {
                bytes,
                max_byte_length,
            }),
            waiters: Mutex::default(),
        }
    }

    /// Enters this block's waiter critical section.
    pub(crate) fn waiters(&self) -> MutexGuard<'_, WaiterList> {
        self.waiters
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub(crate) fn byte_length(&self) -> usize {
        self.state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .bytes
            .len()
    }

    pub(crate) fn max_byte_length(&self) -> usize {
        let state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        state.max_byte_length.unwrap_or(state.bytes.len())
    }

    pub(crate) fn is_growable(&self) -> bool {
        self.state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .max_byte_length
            .is_some()
    }

    pub(crate) const fn is_detached(&self) -> bool {
        false
    }

    pub(crate) fn with_bytes<R>(&self, operation: impl FnOnce(&[u8]) -> R) -> R {
        let state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        operation(&state.bytes)
    }

    pub(crate) fn with_bytes_mut<R>(&self, operation: impl FnOnce(&mut [u8]) -> R) -> R {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        operation(&mut state.bytes)
    }

    /// Mutates the shared backing store after the caller has charged the owning
    /// heap slot. Length validation belongs to [`grow_shared_array_buffer`].
    fn resize_backing(&self, new_length: usize) -> Result<(), ()> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let current = state.bytes.len();
        debug_assert!(new_length >= current);
        debug_assert!(
            state
                .max_byte_length
                .is_some_and(|maximum| new_length <= maximum)
        );
        if new_length == current {
            return Ok(());
        }
        let additional = new_length - current;
        if state.bytes.try_reserve_exact(additional).is_err() {
            return Err(());
        }
        state.bytes.resize(new_length, 0);
        Ok(())
    }
}

/// Grows a SharedArrayBuffer through its owning runtime slot so the byte delta
/// is charged exactly once, even when other heap entries alias the same
/// `Arc<SharedBlock>`.
pub(crate) fn grow_shared_array_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    buffer: Value,
    new_length: usize,
) -> Result<(), EvalFailure> {
    let Some(index) = machine.runtime_slot(buffer).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "SharedArrayBuffer method called on incompatible receiver",
        ));
    };
    let (old_length, maximum, data) = match &machine.heap[index] {
        HeapEntry::SharedArrayBuffer { data, .. } => {
            if !data.is_growable() {
                return Err(type_error("SharedArrayBuffer is not growable"));
            }
            (data.byte_length(), data.max_byte_length(), Arc::clone(data))
        }
        _ => {
            return Err(type_error(
                "SharedArrayBuffer method called on incompatible receiver",
            ));
        }
    };
    if new_length < old_length || new_length > maximum {
        return Err(range_error("Invalid SharedArrayBuffer grow length"));
    }
    if new_length == old_length {
        return Ok(());
    }
    let additional = new_length - old_length;
    if machine.charge_slot(index, additional).is_err() {
        return Err(range_error("SharedArrayBuffer allocation failed"));
    }
    if data.resize_backing(new_length).is_err() {
        machine.refund_slot(index, additional);
        return Err(range_error("SharedArrayBuffer allocation failed"));
    }
    Ok(())
}

/// The canonical backing-store state for ArrayBuffer and every view over it.
///
/// `None` is the detached state. A fixed-length buffer has no maximum; a
/// resizable buffer retains its maximum even while its current vector changes.
#[derive(Clone, Debug)]
pub(crate) struct ArrayBufferData {
    bytes: Option<Vec<u8>>,
    max_byte_length: Option<usize>,
    detach_key: Value,
}

impl ArrayBufferData {
    pub(crate) fn fixed(bytes: Vec<u8>) -> Self {
        Self {
            bytes: Some(bytes),
            max_byte_length: None,
            detach_key: Value::UNDEFINED,
        }
    }

    pub(crate) fn resizable(bytes: Vec<u8>, max_byte_length: usize) -> Self {
        Self {
            bytes: Some(bytes),
            max_byte_length: Some(max_byte_length),
            detach_key: Value::UNDEFINED,
        }
    }

    pub(crate) fn initial_bytes(&self) -> usize {
        self.bytes.as_ref().map_or(0, Vec::len)
    }

    pub(crate) fn detach_key(&self) -> Value {
        self.detach_key
    }
}

/// Stable identity used by TypedArray, DataView, Atomics, and host hooks.
///
/// The handle contains only the owning heap object. It deliberately does not
/// cache a slice, length, or detached bit: every operation re-reads the single
/// canonical `HeapEntry::ArrayBuffer` state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ArrayBufferHandle(Value);

impl ArrayBufferHandle {
    pub(crate) fn allocate<H: Host>(
        machine: &mut Machine<'_, H>,
        byte_length: usize,
        max_byte_length: Option<usize>,
    ) -> Result<Self, EvalFailure> {
        let value = allocate_buffer(machine, byte_length, max_byte_length)?;
        Ok(Self(value))
    }

    pub(crate) fn from_value<H: Host>(
        machine: &Machine<'_, H>,
        value: Value,
    ) -> Result<Self, EvalFailure> {
        let Some(index) = machine.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        if !matches!(machine.heap[index], HeapEntry::ArrayBuffer { .. }) {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        }
        Ok(Self(value))
    }

    pub(crate) fn value(self) -> Value {
        self.0
    }

    fn index<H: Host>(self, machine: &Machine<'_, H>) -> Result<usize, EvalFailure> {
        machine
            .runtime_slot(self.0)
            .map_err(EvalFailure::Runtime)?
            .ok_or_else(|| type_error("ArrayBuffer operation called on incompatible receiver"))
    }

    pub(crate) fn is_detached<H: Host>(self, machine: &Machine<'_, H>) -> bool {
        let Ok(index) = self.index(machine) else {
            return true;
        };
        matches!(
            &machine.heap[index],
            HeapEntry::ArrayBuffer {
                data: ArrayBufferData { bytes: None, .. },
                ..
            }
        )
    }

    pub(crate) fn byte_length<H: Host>(
        self,
        machine: &Machine<'_, H>,
    ) -> Result<usize, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        Ok(data.bytes.as_ref().map_or(0, Vec::len))
    }

    pub(crate) fn max_byte_length<H: Host>(
        self,
        machine: &Machine<'_, H>,
    ) -> Result<usize, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        Ok(match &data.bytes {
            None => 0,
            Some(bytes) => data.max_byte_length.unwrap_or(bytes.len()),
        })
    }

    pub(crate) fn is_resizable<H: Host>(
        self,
        machine: &Machine<'_, H>,
    ) -> Result<bool, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        Ok(data.bytes.is_some() && data.max_byte_length.is_some())
    }
    pub(crate) fn is_fixed_length<H: Host>(
        self,
        machine: &Machine<'_, H>,
    ) -> Result<bool, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        Ok(data.max_byte_length.is_none())
    }
    pub(crate) fn with_bytes<H: Host, R>(
        self,
        machine: &Machine<'_, H>,
        operation: impl FnOnce(&[u8]) -> R,
    ) -> Result<R, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        let bytes = data
            .bytes
            .as_deref()
            .ok_or_else(|| type_error("Cannot access a detached ArrayBuffer"))?;
        Ok(operation(bytes))
    }

    pub(crate) fn with_bytes_mut<H: Host, R>(
        self,
        machine: &mut Machine<'_, H>,
        operation: impl FnOnce(&mut [u8]) -> R,
    ) -> Result<R, EvalFailure> {
        let index = self.index(machine)?;
        let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[index] else {
            return Err(type_error(
                "ArrayBuffer operation called on incompatible receiver",
            ));
        };
        let bytes = data
            .bytes
            .as_deref_mut()
            .ok_or_else(|| type_error("Cannot access a detached ArrayBuffer"))?;
        Ok(operation(bytes))
    }

    pub(crate) fn resize<H: Host>(
        self,
        machine: &mut Machine<'_, H>,
        new_length: usize,
    ) -> Result<(), EvalFailure> {
        let index = self.index(machine)?;
        let (old_length, maximum) = match &machine.heap[index] {
            HeapEntry::ArrayBuffer { data, .. } => {
                let bytes = data
                    .bytes
                    .as_ref()
                    .ok_or_else(|| type_error("Cannot resize a detached ArrayBuffer"))?;
                let maximum = data
                    .max_byte_length
                    .ok_or_else(|| type_error("Cannot resize a fixed-length ArrayBuffer"))?;
                (bytes.len(), maximum)
            }
            _ => {
                return Err(type_error(
                    "ArrayBuffer operation called on incompatible receiver",
                ));
            }
        };
        if new_length > maximum {
            return Err(range_error("ArrayBuffer resize exceeds maxByteLength"));
        }
        if new_length > old_length {
            let additional = new_length - old_length;
            if machine.charge_slot(index, additional).is_err() {
                return Err(range_error("ArrayBuffer allocation failed"));
            }
            let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[index] else {
                unreachable!("ArrayBuffer brand cannot change while charging")
            };
            let bytes = data
                .bytes
                .as_mut()
                .expect("detachment cannot occur while charging");
            if bytes.try_reserve_exact(additional).is_err() {
                machine.refund_slot(index, additional);
                return Err(range_error("ArrayBuffer allocation failed"));
            }
            bytes.resize(new_length, 0);
        } else if new_length < old_length {
            let removed = old_length - new_length;
            let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[index] else {
                unreachable!("ArrayBuffer brand cannot change while shrinking")
            };
            data.bytes
                .as_mut()
                .expect("detachment cannot occur while shrinking")
                .truncate(new_length);
            machine.refund_slot(index, removed);
        }
        Ok(())
    }

    fn same_value<H: Host>(machine: &Machine<'_, H>, left: Value, right: Value) -> bool {
        let numeric = |value: Value| match value.decode() {
            Some(Decoded::Int32(value)) => Some(f64::from(value as i32)),
            Some(Decoded::Number(value)) => Some(value),
            _ => None,
        };
        match (numeric(left), numeric(right)) {
            (Some(left), Some(right)) if left.is_nan() && right.is_nan() => true,
            (Some(left), Some(right)) if left == 0.0 && right == 0.0 => {
                left.is_sign_negative() == right.is_sign_negative()
            }
            (Some(left), Some(right)) => left == right,
            _ => machine.strict_equal(left, right),
        }
    }

    pub(crate) fn detach<H: Host>(
        self,
        machine: &mut Machine<'_, H>,
        key: Value,
    ) -> Result<Vec<u8>, EvalFailure> {
        let index = self.index(machine)?;
        let (expected_key, old_length) = match &machine.heap[index] {
            HeapEntry::ArrayBuffer { data, .. } => {
                let bytes = data
                    .bytes
                    .as_ref()
                    .ok_or_else(|| type_error("Cannot detach an already detached ArrayBuffer"))?;
                (data.detach_key, bytes.len())
            }
            _ => {
                return Err(type_error(
                    "ArrayBuffer operation called on incompatible receiver",
                ));
            }
        };
        if !Self::same_value(machine, expected_key, key) {
            return Err(type_error("ArrayBuffer detach key mismatch"));
        }
        let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[index] else {
            unreachable!("ArrayBuffer brand cannot change while detaching")
        };
        let bytes = data.bytes.take().expect("detachment checked above");
        machine.refund_slot(index, old_length);
        Ok(bytes)
    }
}

#[cfg(test)]
pub(crate) fn detach_for_host<H: Host>(
    machine: &mut Machine<'_, H>,
    buffer: Value,
    key: Value,
) -> Result<(), EvalFailure> {
    ArrayBufferHandle::from_value(machine, buffer)?
        .detach(machine, key)
        .map(drop)
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let constructor =
        install_constructor_function(heap, builtins, "ArrayBuffer", 1, constructor::<H>);
    builtins.set_constructor_prototype(heap, constructor, prototype);
    builtins.set_arraybuffer_constructor(constructor);
    builtins.set_arraybuffer_prototype(prototype);
    define_data(heap, prototype, "constructor", constructor);

    for (name, length, handler) in [
        ("resize", 1, resize::<H> as BuiltinHandler<H>),
        ("slice", 2, slice::<H> as BuiltinHandler<H>),
        ("transfer", 0, transfer::<H> as BuiltinHandler<H>),
        (
            "transferToFixedLength",
            0,
            transfer_to_fixed_length::<H> as BuiltinHandler<H>,
        ),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, prototype, name, function);
    }

    for (property_name, function_name, getter) in [
        (
            "byteLength",
            "get byteLength",
            byte_length::<H> as BuiltinHandler<H>,
        ),
        (
            "maxByteLength",
            "get maxByteLength",
            max_byte_length::<H> as BuiltinHandler<H>,
        ),
        (
            "resizable",
            "get resizable",
            resizable::<H> as BuiltinHandler<H>,
        ),
        (
            "detached",
            "get detached",
            detached::<H> as BuiltinHandler<H>,
        ),
    ] {
        let getter = install_function(heap, builtins, function_name, 0, getter);
        let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
            unreachable!("ArrayBuffer prototype is ordinary")
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

    let is_view = install_function(heap, builtins, "isView", 1, is_view::<H>);
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        unreachable!("ArrayBuffer constructor is native")
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode("isView")),
        builtin_property(is_view),
    );
    let species = install_function(heap, builtins, "get [Symbol.species]", 0, species::<H>);
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        unreachable!("ArrayBuffer constructor is native")
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
    let tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("ArrayBuffer")));
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!("ArrayBuffer prototype is ordinary")
    };
    properties.insert(
        PropertyKey::Symbol(heap_index(builtins.symbol_to_string_tag()) as u32),
        Property::Data {
            value: tag,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
    globals.insert(EcmaString::encode("ArrayBuffer"), constructor);
}

pub(crate) fn to_index<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<usize, EvalFailure> {
    let number = match machine.coerce_number_observable(value)?.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => unreachable!("ToNumber produces a number"),
    };
    let integer = if number.is_nan() || number == 0.0 {
        0.0
    } else {
        number.trunc()
    };
    if !(0.0..=MAX_SAFE_INTEGER).contains(&integer) {
        return Err(range_error("Invalid ArrayBuffer length"));
    }
    Ok(integer as usize)
}

fn allocate_prepared_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    bytes: Vec<u8>,
    max_byte_length: Option<usize>,
    prototype: Value,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::ArrayBuffer {
            data: match max_byte_length {
                Some(maximum) => ArrayBufferData::resizable(bytes, maximum),
                None => ArrayBufferData::fixed(bytes),
            },
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(|_| range_error("ArrayBuffer allocation failed"))
}

fn allocate_buffer<H: Host>(
    machine: &mut Machine<'_, H>,
    byte_length: usize,
    max_byte_length: Option<usize>,
) -> Result<Value, EvalFailure> {
    if max_byte_length.is_some_and(|maximum| byte_length > maximum) {
        return Err(range_error("ArrayBuffer byteLength exceeds maxByteLength"));
    }
    let allocation_length = max_byte_length.unwrap_or(byte_length);
    if machine
        .ensure_allocation_capacity(1, allocation_length.saturating_add(1))
        .is_err()
    {
        return Err(range_error("ArrayBuffer allocation failed"));
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(byte_length)
        .map_err(|_| range_error("ArrayBuffer allocation failed"))?;
    bytes.resize(byte_length, 0);
    let prototype = machine.intrinsics.builtins.arraybuffer_prototype();
    allocate_prepared_buffer(machine, bytes, max_byte_length, prototype)
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("ArrayBuffer constructor requires 'new'"));
    }
    let byte_length = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let max_byte_length = match args.get(1).copied() {
        None | Some(Value::UNDEFINED) => None,
        Some(options) if !machine.is_object(options) => {
            return Err(type_error("ArrayBuffer options argument must be an object"));
        }
        Some(options) => {
            let maximum = machine.get_named_property(options, "maxByteLength")?;
            if maximum == Value::UNDEFINED {
                None
            } else {
                Some(to_index(machine, maximum)?)
            }
        }
    };
    let intrinsic_prototype = machine.intrinsics.builtins.arraybuffer_prototype();
    let new_target = machine.current_new_target();
    let prototype = if new_target == Value::UNDEFINED {
        intrinsic_prototype
    } else {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            intrinsic_prototype
        }
    };
    let value = allocate_buffer(machine, byte_length, max_byte_length)?;
    let index = machine
        .runtime_slot(value)
        .map_err(EvalFailure::Runtime)?
        .unwrap();
    let HeapEntry::ArrayBuffer {
        prototype: buffer_prototype,
        ..
    } = &mut machine.heap[index]
    else {
        unreachable!("AllocateArrayBuffer creates an ArrayBuffer")
    };
    *buffer_prototype = Some(prototype);
    Ok(BuiltinOutcome::Value(value))
}

fn handle<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<ArrayBufferHandle, EvalFailure> {
    ArrayBufferHandle::from_value(machine, value)
}

fn byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        handle(machine, this)?.byte_length(machine)? as f64,
    )))
}

fn max_byte_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(crate::number_value(
        handle(machine, this)?.max_byte_length(machine)? as f64,
    )))
}

fn resizable<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(
        handle(machine, this)?.is_resizable(machine)?,
    )))
}

fn detached<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(
        handle(machine, this)?.is_detached(machine),
    )))
}

fn resize<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let buffer = handle(machine, this)?;
    if buffer.is_fixed_length(machine)? {
        return Err(type_error("Cannot resize a fixed-length ArrayBuffer"));
    }
    let new_length = to_index(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if buffer.is_detached(machine) {
        return Err(type_error("Cannot resize a detached ArrayBuffer"));
    }
    buffer.resize(machine, new_length)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn clamp_index(relative: f64, length: usize) -> usize {
    if relative == f64::NEG_INFINITY {
        0
    } else if relative < 0.0 {
        (length as f64 + relative).max(0.0) as usize
    } else {
        relative.min(length as f64) as usize
    }
}
pub(super) fn to_clamped_index<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    length: usize,
) -> Result<usize, EvalFailure> {
    let number = match machine.coerce_number_observable(value)?.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => unreachable!("ToNumber produces a number"),
    };
    let integer = if number.is_nan() || number == 0.0 {
        0.0
    } else {
        number.trunc()
    };
    Ok(clamp_index(integer, length))
}

pub(super) fn species_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    default: Value,
) -> Result<Value, EvalFailure> {
    let constructor = machine.get_named_property(object, "constructor")?;
    if constructor == Value::UNDEFINED {
        return Ok(default);
    }
    if !machine.is_object(constructor) {
        return Err(type_error(
            "ArrayBuffer constructor property is not an object",
        ));
    }
    let key = machine.to_property_key(machine.intrinsics.builtins.symbol_species())?;
    let species = machine.get_property_key(constructor, &key)?;
    match species.decode() {
        Some(Decoded::Undefined | Decoded::Null) => Ok(default),
        _ if machine.is_callable(species)? => Ok(species),
        _ => Err(type_error("ArrayBuffer species is not a constructor")),
    }
}

fn slice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = handle(machine, this)?;
    if source.is_detached(machine) {
        return Err(type_error("Cannot slice a detached ArrayBuffer"));
    }
    let source_length = source.byte_length(machine)?;
    let start = to_clamped_index(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        source_length,
    )?;
    let end = match args.get(1).copied() {
        None | Some(Value::UNDEFINED) => source_length,
        Some(value) => to_clamped_index(machine, value, source_length)?,
    };
    let new_length = end.saturating_sub(start);
    let default = machine.intrinsics.builtins.arraybuffer_constructor();
    let constructor = species_constructor(machine, this, default)?;
    let target_value =
        machine.construct_value(constructor, &[crate::number_value(new_length as f64)])?;
    let target = handle(machine, target_value)?;
    if target.is_detached(machine) {
        return Err(type_error("ArrayBuffer species returned a detached buffer"));
    }
    if target == source {
        return Err(type_error("ArrayBuffer species returned the source buffer"));
    }
    if target.byte_length(machine)? < new_length {
        return Err(type_error(
            "ArrayBuffer species returned a buffer that is too small",
        ));
    }
    if source.is_detached(machine) {
        return Err(type_error(
            "ArrayBuffer source was detached during species construction",
        ));
    }
    let current_length = source.byte_length(machine)?;
    let copy_length = new_length.min(current_length.saturating_sub(start));
    if copy_length != 0 {
        let copied =
            source.with_bytes(machine, |bytes| bytes[start..start + copy_length].to_vec())?;
        target.with_bytes_mut(machine, |bytes| {
            bytes[..copy_length].copy_from_slice(&copied);
        })?;
    }
    Ok(BuiltinOutcome::Value(target_value))
}

fn copy_and_detach<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    preserve_resizability: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let source = handle(machine, this)?;
    let new_length = match args.first().copied() {
        None | Some(Value::UNDEFINED) => source.byte_length(machine)?,
        Some(value) => to_index(machine, value)?,
    };
    if source.is_detached(machine) {
        return Err(type_error("Cannot transfer a detached ArrayBuffer"));
    }
    let maximum = if preserve_resizability && source.is_resizable(machine)? {
        Some(source.max_byte_length(machine)?)
    } else {
        None
    };
    if maximum.is_some_and(|maximum| new_length > maximum) {
        return Err(range_error("ArrayBuffer transfer exceeds maxByteLength"));
    }
    let source_index = source.index(machine)?;
    let HeapEntry::ArrayBuffer { data, .. } = &machine.heap[source_index] else {
        unreachable!()
    };
    if data.detach_key != Value::UNDEFINED {
        return Err(type_error(
            "Cannot transfer an ArrayBuffer with a detach key",
        ));
    }
    let old_length = source.byte_length(machine)?;
    let growth = new_length.saturating_sub(old_length);
    if machine
        .ensure_allocation_capacity(1, growth.saturating_add(1))
        .is_err()
    {
        return Err(range_error("ArrayBuffer allocation failed"));
    }
    if growth != 0 {
        let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[source_index] else {
            unreachable!("ArrayBuffer brand was checked")
        };
        let bytes = data.bytes.as_mut().expect("detachment was checked");
        bytes
            .try_reserve_exact(growth)
            .map_err(|_| range_error("ArrayBuffer allocation failed"))?;
    }
    let mut bytes = source.detach(machine, Value::UNDEFINED)?;
    bytes.resize(new_length, 0);
    let prototype = machine.intrinsics.builtins.arraybuffer_prototype();
    let target_value = allocate_prepared_buffer(machine, bytes, maximum, prototype)?;
    Ok(BuiltinOutcome::Value(target_value))
}

fn transfer<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    copy_and_detach(machine, this, args, true)
}

fn transfer_to_fixed_length<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    copy_and_detach(machine, this, args, false)
}

fn species<H: Host>(
    _: &mut Machine<'_, H>,
    this: Value,
    _: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(this))
}

fn is_view<H: Host>(
    machine: &mut Machine<'_, H>,
    _: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let viewed = args.first().copied().is_some_and(|value| {
        machine
            .runtime_slot(value)
            .ok()
            .flatten()
            .is_some_and(|index| {
                matches!(
                    machine.heap[index],
                    HeapEntry::TypedArray { .. } | HeapEntry::DataView { .. }
                )
            })
    });
    Ok(BuiltinOutcome::Value(Value::boolean(viewed)))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};

    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, NativeCallable, ThrowOrigin};

    static SPECIES_SOURCE: AtomicU64 = AtomicU64::new(Value::UNDEFINED.to_bits());
    static SPECIES_MODE: AtomicU8 = AtomicU8::new(0);

    fn species_buffer(
        machine: &mut Machine<'_, TestHost>,
        _: Value,
        args: &[Value],
        constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        assert!(constructing);
        let source = Value::from_bits(SPECIES_SOURCE.load(Ordering::SeqCst));
        match SPECIES_MODE.load(Ordering::SeqCst) {
            1 => return Ok(BuiltinOutcome::Value(source)),
            2 => detach_for_host(machine, source, Value::UNDEFINED)?,
            4 => ArrayBufferHandle::from_value(machine, source)?.resize(machine, 0)?,
            _ => {}
        }
        let requested = match args.first().copied().and_then(Value::decode) {
            Some(Decoded::Int32(value)) => value as usize,
            Some(Decoded::Number(value)) => value as usize,
            _ => 0,
        };
        let length = if SPECIES_MODE.load(Ordering::SeqCst) == 3 {
            requested.saturating_sub(1)
        } else {
            requested
        };
        allocate_buffer(machine, length, None).map(BuiltinOutcome::Value)
    }

    fn install_species(machine: &mut Machine<'_, TestHost>, source: ArrayBufferHandle, mode: u8) {
        SPECIES_SOURCE.store(source.value().to_bits(), Ordering::SeqCst);
        SPECIES_MODE.store(mode, Ordering::SeqCst);
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "SpeciesBuffer",
            length: 1,
            handler: species_buffer,
        });
        let constructor = native_function(&mut machine.heap, id, "SpeciesBuffer", 1);
        let species_key = machine
            .to_property_key(machine.intrinsics.builtins.symbol_species())
            .expect("species key");
        machine
            .set_data_property_key(constructor, species_key, constructor)
            .expect("species property");
        machine
            .set_data_property(source.value(), "constructor", constructor)
            .expect("source constructor");
    }

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("<arraybuffer-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn buffer(
        machine: &mut Machine<'_, TestHost>,
        length: usize,
        maximum: Option<usize>,
    ) -> ArrayBufferHandle {
        ArrayBufferHandle::allocate(machine, length, maximum).expect("allocation succeeds")
    }
    fn set_detach_key(machine: &mut Machine<'_, TestHost>, buffer: ArrayBufferHandle, key: Value) {
        let index = buffer.index(machine).unwrap();
        let HeapEntry::ArrayBuffer { data, .. } = &mut machine.heap[index] else {
            unreachable!("test buffer has ArrayBuffer brand")
        };
        data.detach_key = key;
    }

    fn assert_type_error(result: Result<BuiltinOutcome, EvalFailure>) {
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn installation_has_canonical_identity_names_lengths_and_descriptors() {
        with_machine(|machine| {
            let constructor = machine
                .intrinsics
                .global("ArrayBuffer")
                .expect("ArrayBuffer installs");
            let prototype = machine.intrinsics.builtins.arraybuffer_prototype();
            assert_eq!(
                machine
                    .get_named_property(constructor, "prototype")
                    .expect("constructor prototype"),
                prototype
            );
            assert_eq!(
                machine
                    .get_named_property(constructor, "length")
                    .expect("constructor length"),
                Value::int32(1)
            );

            let prototype_index = machine.runtime_slot(prototype).unwrap().unwrap();
            let HeapEntry::Object { properties, .. } = &machine.heap[prototype_index] else {
                panic!("ArrayBuffer.prototype is ordinary")
            };
            let Property::Data {
                writable,
                enumerable,
                configurable,
                ..
            } = properties.get_ascii("resize").expect("resize method")
            else {
                panic!("resize is a data property")
            };
            assert!(*writable);
            assert!(!*enumerable);
            assert!(*configurable);
            let Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable,
                configurable,
            } = properties
                .get_ascii("byteLength")
                .expect("byteLength accessor")
            else {
                panic!("byteLength is a getter-only accessor")
            };
            assert!(!*enumerable);
            assert!(*configurable);
            let getter = *getter;
            let getter_name = machine
                .get_named_property(getter, "name")
                .expect("getter name");
            assert!(
                machine
                    .coerce_string_observable(getter_name)
                    .expect("getter name string")
                    .eq_ascii("get byteLength")
            );

            let constructor_index = machine.runtime_slot(constructor).unwrap().unwrap();
            let HeapEntry::NativeFunction { properties, .. } = &machine.heap[constructor_index]
            else {
                panic!("ArrayBuffer is native")
            };
            let species_key = PropertyKey::Symbol(heap_index(
                machine.intrinsics.builtins.symbol_species(),
            ) as u32);
            assert!(matches!(
                properties.get(&species_key),
                Some(Property::Accessor {
                    getter: Some(_),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                })
            ));
        });
    }

    #[test]
    fn resize_grows_shrinks_and_zero_fills_discarded_bytes() {
        with_machine(|machine| {
            let handle = buffer(machine, 2, Some(8));
            handle
                .with_bytes_mut(machine, |bytes| bytes.copy_from_slice(&[1, 2]))
                .unwrap();
            handle.resize(machine, 6).unwrap();
            assert_eq!(
                handle.with_bytes(machine, <[u8]>::to_vec).unwrap(),
                [1, 2, 0, 0, 0, 0]
            );
            handle
                .with_bytes_mut(machine, |bytes| bytes[4] = 9)
                .unwrap();
            handle.resize(machine, 1).unwrap();
            handle.resize(machine, 6).unwrap();
            assert_eq!(
                handle.with_bytes(machine, <[u8]>::to_vec).unwrap(),
                [1, 0, 0, 0, 0, 0]
            );
        });
    }

    #[test]
    fn transfer_detaches_source_and_preserves_or_drops_resizability() {
        with_machine(|machine| {
            let source = buffer(machine, 3, Some(9));
            source
                .with_bytes_mut(machine, |bytes| bytes.copy_from_slice(&[4, 5, 6]))
                .unwrap();
            let BuiltinOutcome::Value(transferred) =
                transfer(machine, source.value(), &[Value::int32(5)], false).unwrap()
            else {
                panic!()
            };
            let transferred = ArrayBufferHandle::from_value(machine, transferred).unwrap();
            assert!(source.is_detached(machine));
            assert!(transferred.is_resizable(machine).unwrap());
            assert_eq!(transferred.max_byte_length(machine).unwrap(), 9);
            assert_eq!(
                transferred.with_bytes(machine, <[u8]>::to_vec).unwrap(),
                [4, 5, 6, 0, 0]
            );

            let fixed_source = buffer(machine, 2, Some(7));
            let BuiltinOutcome::Value(fixed) =
                transfer_to_fixed_length(machine, fixed_source.value(), &[], false).unwrap()
            else {
                panic!()
            };
            assert!(
                !ArrayBufferHandle::from_value(machine, fixed)
                    .unwrap()
                    .is_resizable(machine)
                    .unwrap()
            );
        });
    }

    #[test]
    fn detached_buffers_reject_data_operations_but_report_zero_lengths() {
        with_machine(|machine| {
            let handle = buffer(machine, 4, None);
            detach_for_host(machine, handle.value(), Value::UNDEFINED).unwrap();
            assert!(handle.is_detached(machine));
            assert_eq!(handle.byte_length(machine).unwrap(), 0);
            assert_eq!(handle.max_byte_length(machine).unwrap(), 0);
            assert!(matches!(
                handle.with_bytes(machine, |_| ()),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                handle.with_bytes_mut(machine, |_| ()),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                handle.resize(machine, 0),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                detach_for_host(machine, handle.value(), Value::UNDEFINED),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_type_error(slice(machine, handle.value(), &[], false));
            assert_type_error(transfer(machine, handle.value(), &[], false));
            assert_type_error(transfer_to_fixed_length(
                machine,
                handle.value(),
                &[],
                false,
            ));
        });
    }

    #[test]
    fn fixed_and_resizable_bounds_are_distinct() {
        with_machine(|machine| {
            let fixed = buffer(machine, 3, None);
            assert!(!fixed.is_resizable(machine).unwrap());
            assert_eq!(fixed.max_byte_length(machine).unwrap(), 3);
            assert!(matches!(
                fixed.resize(machine, 2),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            let growable = buffer(machine, 3, Some(4));
            assert!(matches!(
                growable.resize(machine, 5),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));
        });
    }

    #[test]
    fn allocation_and_to_index_overflow_are_typed_failures() {
        with_machine(|machine| {
            assert_eq!(
                to_index(machine, Value::number(MAX_SAFE_INTEGER)).unwrap(),
                MAX_SAFE_INTEGER as usize
            );
            assert!(matches!(
                to_index(machine, Value::number(MAX_SAFE_INTEGER + 1.0)),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));
            assert!(matches!(
                allocate_buffer(machine, 5, Some(4)),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));
        });
    }

    #[test]
    fn constructor_uses_new_target_prototype() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.builtins.arraybuffer_constructor();
            let constructor_index = machine.runtime_slot(constructor).unwrap().unwrap();
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } = &machine.heap[constructor_index]
            else {
                panic!("ArrayBuffer is a native constructor")
            };
            let id = *id;
            let new_target = ordinary_object(machine);
            let custom_prototype = ordinary_object(machine);
            machine
                .set_data_property(new_target, "prototype", custom_prototype)
                .unwrap();
            let BuiltinOutcome::Value(value) = machine
                .call_builtin_with_new_target(
                    id,
                    Value::UNDEFINED,
                    &[Value::int32(2)],
                    true,
                    new_target,
                )
                .unwrap()
            else {
                panic!("constructor returns an ArrayBuffer")
            };
            let index = machine.runtime_slot(value).unwrap().unwrap();
            let HeapEntry::ArrayBuffer { prototype, .. } = &machine.heap[index] else {
                panic!("constructor returns an ArrayBuffer")
            };
            assert_eq!(*prototype, Some(custom_prototype));
        });
    }

    #[test]
    fn detach_keys_use_same_value_for_strings_nan_and_signed_zero() {
        with_machine(|machine| {
            let first = machine
                .allocate(HeapEntry::String(EcmaString::encode("key")))
                .unwrap();
            let second = machine
                .allocate(HeapEntry::String(EcmaString::encode("key")))
                .unwrap();
            let string_keyed = buffer(machine, 1, None);
            set_detach_key(machine, string_keyed, first);
            string_keyed.detach(machine, second).unwrap();

            let zero_keyed = buffer(machine, 1, None);
            set_detach_key(machine, zero_keyed, Value::number(0.0));
            assert!(matches!(
                zero_keyed.detach(machine, Value::number(-0.0)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            zero_keyed.detach(machine, Value::number(0.0)).unwrap();
        });
    }
    #[test]
    fn test262_host_detach_rejects_wrong_key_and_double_detach() {
        with_machine(|machine| {
            let buffer = buffer(machine, 3, None);
            set_detach_key(machine, buffer, Value::int32(7));

            assert!(matches!(
                detach_for_host(machine, buffer.value(), Value::int32(8)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(buffer.byte_length(machine).unwrap(), 3);
            detach_for_host(machine, buffer.value(), Value::int32(7)).unwrap();
            assert!(matches!(
                detach_for_host(machine, buffer.value(), Value::int32(7)),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn builtin_cache_and_detach_key_are_gc_roots() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.builtins.arraybuffer_constructor();
            let prototype = machine.intrinsics.builtins.arraybuffer_prototype();
            machine
                .intrinsics
                .globals
                .remove(&EcmaString::encode("ArrayBuffer"));

            let key = ordinary_object(machine);
            machine
                .set_data_property(key, "marker", Value::int32(42))
                .unwrap();
            let keyed = buffer(machine, 2, None);
            set_detach_key(machine, keyed, key);
            machine
                .intrinsics
                .globals
                .insert(EcmaString::encode("rootedArrayBuffer"), keyed.value());

            machine.collect_garbage();

            assert!(machine.runtime_slot(constructor).unwrap().is_some());
            assert!(machine.runtime_slot(prototype).unwrap().is_some());
            assert_eq!(
                machine.get_named_property(key, "marker").unwrap(),
                Value::int32(42)
            );
            detach_for_host(machine, keyed.value(), key).unwrap();
        });
    }

    #[test]
    fn transfer_reuses_storage_under_tight_heap_limit() {
        let program = blank_program("<arraybuffer-transfer-limit>");
        let mut host = TestHost;
        let limits = Limits {
            max_heap_bytes: 10,
            ..Limits::default()
        };
        let mut machine = Machine::new(&program, &mut host, limits);
        let source = buffer(&mut machine, 8, None);
        source
            .with_bytes_mut(&mut machine, |bytes| {
                bytes.copy_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
            })
            .unwrap();
        let BuiltinOutcome::Value(target) =
            transfer(&mut machine, source.value(), &[], false).unwrap()
        else {
            panic!("transfer returns an ArrayBuffer")
        };
        assert!(source.is_detached(&machine));
        assert_eq!(
            ArrayBufferHandle::from_value(&machine, target)
                .unwrap()
                .with_bytes(&machine, <[u8]>::to_vec)
                .unwrap(),
            [1, 2, 3, 4, 5, 6, 7, 8]
        );
    }

    #[test]
    fn slice_honours_species_and_post_construction_validation_order() {
        with_machine(|machine| {
            let source = buffer(machine, 5, None);
            source
                .with_bytes_mut(machine, |bytes| {
                    bytes.copy_from_slice(&[0, 1, 2, 3, 4]);
                })
                .unwrap();
            install_species(machine, source, 0);
            let BuiltinOutcome::Value(target) = slice(
                machine,
                source.value(),
                &[Value::int32(1), Value::int32(u32::MAX)],
                false,
            )
            .unwrap() else {
                panic!("slice returns an ArrayBuffer")
            };
            let target = ArrayBufferHandle::from_value(machine, target).unwrap();
            assert_eq!(
                target.with_bytes(machine, <[u8]>::to_vec).unwrap(),
                [1, 2, 3]
            );

            let same = buffer(machine, 2, None);
            install_species(machine, same, 1);
            assert_type_error(slice(machine, same.value(), &[], false));

            let detached_during_construction = buffer(machine, 2, None);
            install_species(machine, detached_during_construction, 2);
            assert_type_error(slice(
                machine,
                detached_during_construction.value(),
                &[],
                false,
            ));
            assert!(detached_during_construction.is_detached(machine));

            let too_small = buffer(machine, 2, None);
            install_species(machine, too_small, 3);
            assert_type_error(slice(machine, too_small.value(), &[], false));
            let shrunk_past_start = buffer(machine, 4, Some(4));
            install_species(machine, shrunk_past_start, 4);
            let BuiltinOutcome::Value(target) = slice(
                machine,
                shrunk_past_start.value(),
                &[Value::int32(3)],
                false,
            )
            .expect("shrinking below start yields a zero-filled target") else {
                panic!("slice returns an ArrayBuffer")
            };
            assert_eq!(
                ArrayBufferHandle::from_value(machine, target)
                    .unwrap()
                    .with_bytes(machine, <[u8]>::to_vec)
                    .unwrap(),
                [0]
            );

            assert_eq!(clamp_index(-2.0, 5), 3);
            assert_eq!(clamp_index(f64::INFINITY, 5), 5);
            assert_eq!(clamp_index(f64::NEG_INFINITY, 5), 0);
        });
    }

    fn shared_buffer(machine: &mut Machine<'_, TestHost>, length: usize, maximum: usize) -> Value {
        let bytes = vec![0; length];
        machine
            .allocate(HeapEntry::SharedArrayBuffer {
                data: Arc::new(SharedBlock::new(bytes, Some(maximum))),
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                extensible: true,
            })
            .expect("SharedArrayBuffer allocation succeeds")
    }

    fn alias_shared(machine: &mut Machine<'_, TestHost>, source: Value) -> Value {
        let index = machine.runtime_slot(source).unwrap().unwrap();
        let HeapEntry::SharedArrayBuffer {
            data, prototype, ..
        } = &machine.heap[index]
        else {
            panic!("expected SharedArrayBuffer");
        };
        let data = Arc::clone(data);
        let prototype = *prototype;
        machine
            .allocate(HeapEntry::SharedArrayBuffer {
                data,
                properties: PropertyMap::default(),
                prototype,
                extensible: true,
            })
            .expect("SharedArrayBuffer alias allocation succeeds")
    }

    #[test]
    fn constructor_options_require_object_and_preserve_max_byte_length_get() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.builtins.arraybuffer_constructor();
            for options in [
                Value::NULL,
                Value::int32(1),
                crate::number_value(1.5),
                machine
                    .allocate(HeapEntry::String(EcmaString::encode("nope")))
                    .unwrap(),
            ] {
                assert!(matches!(
                    machine.construct_value(constructor, &[Value::int32(0), options]),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ));
            }

            let options = ordinary_object(machine);
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "throwing maxByteLength",
                length: 0,
                handler: |_, _, _, _| {
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "maxByteLength getter",
                    }))
                },
            });
            let getter = native_function(&mut machine.heap, id, "get maxByteLength", 0);
            machine
                .define_accessor(
                    options,
                    PropertyKey::Named(EcmaString::encode("maxByteLength")),
                    getter,
                    bamts_bytecode::AccessorKind::Getter,
                )
                .unwrap();
            assert!(matches!(
                machine.construct_value(constructor, &[Value::int32(0), options]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "maxByteLength getter",
                    ..
                }))
            ));

            let ok = ordinary_object(machine);
            machine
                .set_data_property(ok, "maxByteLength", Value::int32(8))
                .unwrap();
            let value = machine
                .construct_value(constructor, &[Value::int32(4), ok])
                .unwrap();
            let handle = ArrayBufferHandle::from_value(machine, value).unwrap();
            assert!(handle.is_resizable(machine).unwrap());
            assert_eq!(handle.max_byte_length(machine).unwrap(), 8);
        });
    }

    #[test]
    fn shared_array_buffer_grow_charges_owning_slot_once_and_refunds() {
        let program = blank_program("<shared-grow-accounting>");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());

        let owner = shared_buffer(&mut machine, 8, 64);
        let alias = alias_shared(&mut machine, owner);
        let owner_index = machine.runtime_slot(owner).unwrap().unwrap();
        let alias_index = machine.runtime_slot(alias).unwrap().unwrap();
        let owner_before = machine.slot_bytes[owner_index];
        let alias_before = machine.slot_bytes[alias_index];
        let heap_before = machine.heap_bytes;

        // Low heap limit rejection: length is valid, charge must fail and refund.
        machine.limits.max_heap_bytes = machine.heap_bytes;
        assert!(matches!(
            grow_shared_array_buffer(&mut machine, owner, 16),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
        assert_eq!(machine.slot_bytes[owner_index], owner_before);
        assert_eq!(machine.heap_bytes, heap_before);
        assert_eq!(
            match &machine.heap[owner_index] {
                HeapEntry::SharedArrayBuffer { data, .. } => data.byte_length(),
                _ => panic!("owner brand"),
            },
            8
        );

        // Successful delta accounting on the owning slot only.
        machine.limits.max_heap_bytes = heap_before + 8;
        grow_shared_array_buffer(&mut machine, owner, 16).unwrap();
        assert_eq!(machine.slot_bytes[owner_index], owner_before + 8);
        assert_eq!(
            machine.slot_bytes[alias_index], alias_before,
            "shared aliases must not be double-charged"
        );
        assert_eq!(machine.heap_bytes, heap_before + 8);
        assert_eq!(
            match &machine.heap[owner_index] {
                HeapEntry::SharedArrayBuffer { data, .. } => data.byte_length(),
                _ => panic!("owner brand"),
            },
            16
        );
        assert_eq!(
            match &machine.heap[alias_index] {
                HeapEntry::SharedArrayBuffer { data, .. } => data.byte_length(),
                _ => panic!("alias brand"),
            },
            16
        );

        // Final refund: local Values are not GC roots, so collection sweeps both
        // wrappers and returns the charged grow delta.
        let heap_after_grow = machine.heap_bytes;
        machine.collect_garbage();
        assert!(
            machine.heap_bytes <= heap_after_grow.saturating_sub(8),
            "GC must refund the owning grow charge; before={} after={}",
            heap_after_grow,
            machine.heap_bytes
        );
        assert!(matches!(machine.heap[owner_index], HeapEntry::Vacant));
        assert!(matches!(machine.heap[alias_index], HeapEntry::Vacant));
        assert_eq!(machine.slot_bytes[owner_index], 0);
        assert_eq!(machine.slot_bytes[alias_index], 0);
    }
}
