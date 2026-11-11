//! ES2023--ES2026 with `Array.fromAsync` (current draft clause 23.1.2.2) `Array` methods whose algorithms create dense copies.
//!
//! Authority: ECMA-262 2025, clauses 23.1.3.1, 23.1.3.11--12,
//! 23.1.3.33--35, and 23.1.3.39. `Array.fromAsync` is draft-ES2026 rather than ES2025,
//! but the TypeScript ESNext compatibility target requires it.

use std::cmp::Ordering;
use std::mem::size_of;

use bamts_native::Value;

use super::array_generic::tick;
use super::{allocate_array, define_data, install_function, range_error, type_error, value_number};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, PropertyKey, RuntimeErrorKind};

const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
const MAX_ARRAY_LENGTH: usize = u32::MAX as usize;

/// Replaces the baseline implementations of `at` and `findLast`, installs the
/// ES2023 copy-by-change family on `%Array.prototype%`, and installs
/// `Array.fromAsync` plus its hidden continuation targets on `%Array%`.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
    array_prototype: Value,
    array_constructor: Value,
) {
    for (name, length, handler) in [
        ("at", 1, at::<H> as BuiltinHandler<H>),
        ("findLast", 1, find_last::<H>),
        ("findLastIndex", 1, find_last_index::<H>),
        ("toReversed", 0, to_reversed::<H>),
        ("toSorted", 1, to_sorted::<H>),
        ("toSpliced", 2, to_spliced::<H>),
        ("with", 2, with::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, array_prototype, name, function);
    }
    let from_async = install_function(heap, atoms, builtins, "fromAsync", 3, from_async::<H>);
    define_static(heap, atoms, array_constructor, "fromAsync", from_async);
    let mut targets = Vec::new();
    for (name, handler) in [
        (
            "Array.fromAsync result",
            iter_result::<H> as BuiltinHandler<H>,
        ),
        ("Array.fromAsync reject cap", reject_cap_handler::<H>),
        ("Array.fromAsync mapped", iter_mapped::<H>),
        ("Array.fromAsync mapped rejected", iter_mapped_rejected::<H>),
        ("Array.fromAsync array-like value", arraylike_value::<H>),
        ("Array.fromAsync close settled", close_settled::<H>),
        ("Array.fromAsync array-like mapped", arraylike_mapped::<H>),
    ] {
        targets.push(install_function(heap, atoms, builtins, name, 1, handler));
    }
    let target_table = crate::intrinsics::push(
        heap,
        HeapEntry::Array {
            elements: targets,
            properties: crate::PropertyMap::default(),
            prototype: None,
            extensible: true,
            length_writable: true,
        },
    );
    define_data(heap, atoms, array_prototype, TARGETS_PROPERTY, target_table);
}

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

pub(super) fn to_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Value, EvalFailure> {
    machine.value_to_object(value)
}

fn number<H: Host>(machine: &mut Machine<'_, H>, value: Value) -> Result<f64, EvalFailure> {
    machine.coerce_number_observable(value).map(value_number)
}

pub(super) fn integer_or_infinity<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<f64, EvalFailure> {
    let number = number(machine, value)?;
    Ok(if number.is_nan() || number == 0.0 {
        0.0
    } else {
        number.trunc()
    })
}

pub(super) fn length_of_array_like<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
) -> Result<usize, EvalFailure> {
    let length = machine.get_named_property(object, "length")?;
    let length = number(machine, length)?;
    if length.is_nan() || length <= 0.0 {
        return Ok(0);
    }
    if length == f64::INFINITY {
        return Ok(MAX_SAFE_INTEGER as usize);
    }
    Ok(length.trunc().min(MAX_SAFE_INTEGER) as usize)
}

pub(super) fn index_key(atoms: &mut crate::AtomTable, index: usize) -> PropertyKey {
    PropertyKey::Named(atoms.intern_str(&index.to_string()))
}

/// `ArrayCreate(length)` with a preflight before Rust allocates the backing
/// vector. Copy-by-change methods always create the intrinsic Array, never a
/// species-derived result.
pub(super) fn array_create<H: Host>(
    machine: &mut Machine<'_, H>,
    length: usize,
) -> Result<Value, EvalFailure> {
    if length > MAX_ARRAY_LENGTH {
        return Err(range_error("Invalid array length"));
    }
    let bytes = length
        .checked_mul(size_of::<Value>())
        .ok_or(EvalFailure::Runtime(
            RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ))?;
    if bytes > machine.limits.max_heap_bytes {
        return Err(EvalFailure::Runtime(
            RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ));
    }
    let mut elements = Vec::new();
    elements.try_reserve_exact(length).map_err(|_| {
        EvalFailure::Runtime(RuntimeErrorKind::HeapByteLimitExceeded {
            limit: machine.limits.max_heap_bytes,
        })
    })?;
    elements.resize(length, Value::HOLE);
    allocate_array(machine, elements)
}

pub(super) fn create_data_property<H: Host>(
    machine: &mut Machine<'_, H>,
    array: Value,
    index: usize,
    value: Value,
) -> Result<(), EvalFailure> {
    let key = index_key(&mut machine.atoms, index);
    let Some(slot) = machine.runtime_slot(array).map_err(EvalFailure::Runtime)? else {
        return machine.create_data_property_key(array, key, value);
    };
    let array_state = match &machine.heap[slot] {
        HeapEntry::Array {
            elements,
            properties,
            extensible,
            ..
        } => Some((elements.len(), properties.contains_key(&key), *extensible)),
        _ => None,
    };
    let Some((length, explicit_descriptor, extensible)) = array_state else {
        return machine.create_data_property_key(array, key, value);
    };
    if explicit_descriptor {
        return machine.create_data_property_key(array, key, value);
    }
    if index < length {
        let HeapEntry::Array { elements, .. } = &mut machine.heap[slot] else {
            unreachable!("array was matched above")
        };
        if elements[index] == Value::HOLE && !extensible {
            return Err(type_error("Cannot add property to non-extensible array"));
        }
        elements[index] = value;
        return Ok(());
    }
    while machine.array_length(array)? < index {
        machine.array_push(array, Value::HOLE)?;
    }
    machine.array_push(array, value)
}

fn relative_position(relative: f64, length: usize) -> f64 {
    if relative < 0.0 {
        length as f64 + relative
    } else {
        relative
    }
}

fn clamped_start(relative: f64, length: usize) -> usize {
    if relative == f64::NEG_INFINITY {
        0
    } else if relative < 0.0 {
        (length as f64 + relative).max(0.0) as usize
    } else {
        relative.min(length as f64) as usize
    }
}

fn at<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let relative = integer_or_infinity(machine, argument(args, 0))?;
    let index = relative_position(relative, length);
    if index < 0.0 || index >= length as f64 {
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let key = index_key(&mut machine.atoms, index as usize);
    Ok(BuiltinOutcome::Value(
        machine.get_property_key(object, &key)?,
    ))
}

fn find_via_predicate<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    length: usize,
    predicate: Value,
    this_arg: Value,
) -> Result<Option<(usize, Value)>, EvalFailure> {
    if !machine.is_callable(predicate)? {
        return Err(type_error("Array predicate is not callable"));
    }
    for index in (0..length).rev() {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, index);
        let value = machine.get_property_key(object, &key)?;
        if machine.call_truthy(
            predicate,
            this_arg,
            &[value, crate::number_value(index as f64), object],
        )? {
            return Ok(Some((index, value)));
        }
    }
    Ok(None)
}

fn find_last<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let found = find_via_predicate(
        machine,
        object,
        length,
        argument(args, 0),
        argument(args, 1),
    )?;
    Ok(BuiltinOutcome::Value(
        found.map_or(Value::UNDEFINED, |(_, value)| value),
    ))
}

fn find_last_index<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let found = find_via_predicate(
        machine,
        object,
        length,
        argument(args, 0),
        argument(args, 1),
    )?;
    Ok(BuiltinOutcome::Value(crate::number_value(
        found.map_or(-1.0, |(index, _)| index as f64),
    )))
}

fn to_reversed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let result = array_create(machine, length)?;
    for index in 0..length {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, length - index - 1);
        let value = machine.get_property_key(object, &key)?;
        create_data_property(machine, result, index, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn compare_array_elements<H: Host>(
    machine: &mut Machine<'_, H>,
    left: Value,
    right: Value,
    comparator: Option<Value>,
) -> Result<Ordering, EvalFailure> {
    if left == Value::UNDEFINED && right == Value::UNDEFINED {
        return Ok(Ordering::Equal);
    }
    if left == Value::UNDEFINED {
        return Ok(Ordering::Greater);
    }
    if right == Value::UNDEFINED {
        return Ok(Ordering::Less);
    }
    if let Some(comparator) = comparator {
        let result = machine.call_value(comparator, Value::UNDEFINED, &[left, right])?;
        let result = number(machine, result)?;
        return Ok(if result.is_nan() || result == 0.0 {
            Ordering::Equal
        } else if result < 0.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        });
    }
    let left = machine.to_string(left)?;
    let right = machine.to_string(right)?;
    Ok(left.as_units().cmp(right.as_units()))
}

/// Stable insertion sort permits comparator calls to return `Result`. Unlike a
/// `sort_by` closure that stores the first error and returns `Equal`, this stops
/// immediately after abrupt completion as SortIndexedProperties requires.
fn stable_sort<H: Host>(
    machine: &mut Machine<'_, H>,
    values: &mut [Value],
    comparator: Option<Value>,
) -> Result<(), EvalFailure> {
    // The comparator can remove these from wherever they came from.
    for value in values.iter() {
        machine.keep_temporary(*value);
    }
    for end in 1..values.len() {
        let mut index = end;
        while index > 0 {
            // This sort takes quadratic steps, and a charge for each would make a
            // short array run out of fuel. A comparator pays for its own work.
            machine.check_cancel().map_err(EvalFailure::Runtime)?;
            let order =
                compare_array_elements(machine, values[index], values[index - 1], comparator)?;
            if order != Ordering::Less {
                break;
            }
            values.swap(index, index - 1);
            index -= 1;
        }
    }
    Ok(())
}

fn to_sorted<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let comparator = match argument(args, 0) {
        Value::UNDEFINED => None,
        value if machine.is_callable(value)? => Some(value),
        _ => return Err(type_error("Array comparator is not callable")),
    };
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let result = array_create(machine, length)?;
    let mut values = Vec::new();
    values.try_reserve_exact(length).map_err(|_| {
        EvalFailure::Runtime(RuntimeErrorKind::HeapByteLimitExceeded {
            limit: machine.limits.max_heap_bytes,
        })
    })?;
    for index in 0..length {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, index);
        values.push(machine.get_property_key(object, &key)?);
    }
    stable_sort(machine, &mut values, comparator)?;
    for (index, value) in values.into_iter().enumerate() {
        create_data_property(machine, result, index, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn to_spliced<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let relative_start = integer_or_infinity(machine, argument(args, 0))?;
    let actual_start = clamped_start(relative_start, length);
    let insert_count = args.len().saturating_sub(2);
    let skip_count = if args.is_empty() {
        0
    } else if args.len() == 1 {
        length - actual_start
    } else {
        let relative = integer_or_infinity(machine, args[1])?;
        if relative <= 0.0 {
            0
        } else {
            relative.min((length - actual_start) as f64) as usize
        }
    };
    let new_length = length
        .checked_sub(skip_count)
        .and_then(|remaining| remaining.checked_add(insert_count))
        .ok_or_else(|| type_error("Array length exceeds safe integer range"))?;
    if new_length as f64 > MAX_SAFE_INTEGER {
        return Err(type_error("Array length exceeds safe integer range"));
    }
    let result = array_create(machine, new_length)?;
    let mut destination = 0;
    while destination < actual_start {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, destination);
        let value = machine.get_property_key(object, &key)?;
        create_data_property(machine, result, destination, value)?;
        destination += 1;
    }
    for value in args.iter().copied().skip(2) {
        create_data_property(machine, result, destination, value)?;
        destination += 1;
    }
    let mut source = actual_start + skip_count;
    while destination < new_length {
        tick(machine)?;
        let key = index_key(&mut machine.atoms, source);
        let value = machine.get_property_key(object, &key)?;
        create_data_property(machine, result, destination, value)?;
        destination += 1;
        source += 1;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn with<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    let relative = integer_or_infinity(machine, argument(args, 0))?;
    let actual = relative_position(relative, length);
    if actual < 0.0 || actual >= length as f64 {
        return Err(range_error("Array index is out of range"));
    }
    let actual = actual as usize;
    let result = array_create(machine, length)?;
    let replacement = argument(args, 1);
    for index in 0..length {
        tick(machine)?;
        let value = if index == actual {
            replacement
        } else {
            let key = index_key(&mut machine.atoms, index);
            machine.get_property_key(object, &key)?
        };
        create_data_property(machine, result, index, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

use bamts_native::Decoded;

// ---- Array.fromAsync ---------------------------------------------------------

/// Hidden property on `%Array.prototype%` holding the continuation targets for
/// the native `Array.fromAsync` reaction chains. Engine records only; the NUL
/// prefix keeps it out of the user-visible namespace.
const TARGETS_PROPERTY: &str = "\0array.fromAsync.targets";
const T_ITER_RESULT: usize = 0;
const T_REJECT_CAP: usize = 1;
const T_ITER_MAPPED: usize = 2;
const T_ITER_MAPPED_REJECTED: usize = 3;
const T_ARRAYLIKE_VALUE: usize = 4;
const T_CLOSE_SETTLED: usize = 5;
const T_ARRAYLIKE_MAPPED: usize = 6;

/// `this` on a call-by-name builtin cannot receive the task's record object,
/// so every `Array.fromAsync` continuation state lives on an ordinary object
/// behind NUL-prefixed own properties.
const FIELD_MODE: &str = "\0mode";
const FIELD_ITER: &str = "\0iter";
const FIELD_SOURCE: &str = "\0source";
const FIELD_ARRAY: &str = "\0array";
const FIELD_MAPPER: &str = "\0mapper";
const FIELD_THIS_ARG: &str = "\0thisArg";
const FIELD_K: &str = "\0k";
const FIELD_LEN: &str = "\0len";
const FIELD_PENDING: &str = "\0pendingReason";
const FIELD_CAP: &str = "\0cap";

/// Mirrors `array.rs`'s static-property writer: a static on the Array
/// constructor lives in a `NativeFunction` entry, which `define_data` does
/// not accept.
fn define_static(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    constructor: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("Array fromAsync attaches to a native-function constructor")
    };
    properties.insert(
        PropertyKey::Named(atoms.intern_str(name)),
        super::builtin_property(value),
    );
}

fn target<H: Host>(machine: &mut Machine<'_, H>, index: usize) -> Result<Value, EvalFailure> {
    let prototype = machine.intrinsics.builtins.array_prototype();
    let table = machine.get_named_property(prototype, TARGETS_PROPERTY)?;
    Ok(machine
        .array_elements(table)?
        .expect("fromAsync continuation table is an array")[index])
}

fn bound_target<H: Host>(
    machine: &mut Machine<'_, H>,
    index: usize,
    record: Value,
) -> Result<Value, EvalFailure> {
    let target = target(machine, index)?;
    machine.create_promise_resolver_function(target, record)
}

fn attach<H: Host>(
    machine: &mut Machine<'_, H>,
    promise: Value,
    on_fulfilled: usize,
    on_rejected: usize,
    record: Value,
) -> Result<(), EvalFailure> {
    let fulfilled = bound_target(machine, on_fulfilled, record)?;
    let rejected = bound_target(machine, on_rejected, record)?;
    machine.promise_then(promise, fulfilled, rejected)?;
    Ok(())
}

/// GetMethod: nullish reads return `None`; non-callable non-nullish reads are
/// a TypeError.
fn get_method<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    key: &PropertyKey,
) -> Result<Option<Value>, EvalFailure> {
    let method = machine.get_property_key(value, key)?;
    match method.decode() {
        Some(Decoded::Undefined | Decoded::Null) | None => Ok(None),
        _ if machine.is_callable(method)? => Ok(Some(method)),
        _ => Err(type_error(
            "Array.fromAsync iterator method is not callable",
        )),
    }
}

fn get_iterator_from_method<H: Host>(
    machine: &mut Machine<'_, H>,
    items: Value,
    method: Value,
    from_sync: bool,
) -> Result<Value, EvalFailure> {
    let iterator = machine.call_value(method, items, &[])?;
    if !machine.is_object(iterator) {
        return Err(type_error("Array.fromAsync iterator is not an object"));
    }
    let next = machine.get_named_property(iterator, "next")?;
    if from_sync {
        machine.create_async_from_sync_iterator(iterator, next)
    } else {
        machine.create_protocol_iterator(iterator, next)
    }
}

fn new_record<H: Host>(machine: &mut Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: crate::PropertyMap::default(),
            prototype: Some(machine.intrinsics.object_prototype),
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)
}

fn record_put<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    field: &'static str,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.set_data_property(record, field, value)
}

fn record_get<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    field: &'static str,
) -> Result<Value, EvalFailure> {
    machine.get_named_property(record, field)
}

fn record_number<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    field: &'static str,
) -> Result<f64, EvalFailure> {
    Ok(value_number(record_get(machine, record, field)?))
}

fn record_bump_k<H: Host>(machine: &mut Machine<'_, H>, record: Value) -> Result<(), EvalFailure> {
    let k = record_number(machine, record, FIELD_K)?;
    record_put(machine, record, FIELD_K, crate::number_value(k + 1.0))
}

fn resolve_cap<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    value: Value,
) -> Result<(), EvalFailure> {
    let cap = record_get(machine, record, FIELD_CAP)?;
    machine.resolve_promise_resolver(cap, value)
}

fn reject_cap_value<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    reason: Value,
) -> Result<(), EvalFailure> {
    let cap = record_get(machine, record, FIELD_CAP)?;
    machine.reject_promise_resolver(cap, reason)
}

fn reject_cap_failure<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    failure: EvalFailure,
) -> Result<(), EvalFailure> {
    let cap = record_get(machine, record, FIELD_CAP)?;
    machine.reject_promise_resolver_failure(cap, failure)
}

/// EvalFailure of a JS-visible throw is materialized as the exact Value a
/// rejection must carry: route it through a throwaway capability whose settled
/// state stores the engine-generated reason.
fn failure_reason_value<H: Host>(
    machine: &mut Machine<'_, H>,
    failure: EvalFailure,
) -> Result<Value, EvalFailure> {
    let probe = machine.create_promise()?;
    let probe_record = machine.create_promise_resolver(probe)?;
    machine.reject_promise_resolver_failure(probe_record, failure)?;
    let index = machine
        .runtime_slot(probe)
        .map_err(EvalFailure::Runtime)?
        .expect("throwaway promise is a heap object");
    let HeapEntry::Promise {
        state: crate::PromiseState::Rejected { reason, .. },
        ..
    } = &machine.heap[index]
    else {
        panic!("a freshly rejected promise holds its reason")
    };
    Ok(*reason)
}

fn close_then_reject<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    failure: EvalFailure,
) -> Result<(), EvalFailure> {
    let reason = failure_reason_value(machine, failure)?;
    record_put(machine, record, FIELD_PENDING, reason)?;
    start_async_close(machine, record)
}

/// AsyncIteratorClose over the loop's throw completion: notify `return`,
/// await its result, then rethrow the original completion in both schedules.
fn start_async_close<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
) -> Result<(), EvalFailure> {
    let iterator = record_get(machine, record, FIELD_ITER)?;
    let reason = record_get(machine, record, FIELD_PENDING)?;
    let (result, had_close) = machine.close_iterator_raw(iterator);
    match result {
        Err(_) => reject_cap_value(machine, record, reason),
        Ok(value) if had_close => {
            let settled = machine.promise_resolve(value)?;
            attach(machine, settled, T_CLOSE_SETTLED, T_CLOSE_SETTLED, record)
        }
        Ok(_) => reject_cap_value(machine, record, reason),
    }
}

fn iter_driver<H: Host>(machine: &mut Machine<'_, H>, record: Value) -> Result<(), EvalFailure> {
    let k = record_number(machine, record, FIELD_K)?;
    if k >= MAX_SAFE_INTEGER {
        return close_then_reject(
            machine,
            record,
            type_error("Array.fromAsync length exceeds safe integer range"),
        );
    }
    let iterator = record_get(machine, record, FIELD_ITER)?;
    let stepped = machine.iterator_step(iterator);
    match stepped {
        Err(EvalFailure::Runtime(kind)) => Err(EvalFailure::Runtime(kind)),
        Err(failure) => reject_cap_failure(machine, record, failure),
        Ok(raw) => {
            // Await(nextResult): async-from-sync stepping already returns the
            // spec continuation promise; protocol iterators resolve whatever
            // `next` returned.
            let awaited = machine.promise_resolve(raw)?;
            attach(machine, awaited, T_ITER_RESULT, T_REJECT_CAP, record)
        }
    }
}

fn define_element<H: Host>(
    machine: &mut Machine<'_, H>,
    array: Value,
    k: f64,
    value: Value,
) -> Result<(), EvalFailure> {
    create_data_property(machine, array, k as usize, value)
}

fn define_then_continue<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    value: Value,
) -> Result<(), EvalFailure> {
    let k = record_number(machine, record, FIELD_K)?;
    let array = record_get(machine, record, FIELD_ARRAY)?;
    match define_element(machine, array, k, value) {
        Err(EvalFailure::Runtime(kind)) => Err(EvalFailure::Runtime(kind)),
        Err(failure) => close_then_reject(machine, record, failure),
        Ok(()) => {
            record_bump_k(machine, record)?;
            iter_driver(machine, record)
        }
    }
}

fn iter_result<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let result = argument(args, 1);
    if !machine.is_object(result) {
        reject_cap_failure(
            machine,
            record,
            type_error("Array.fromAsync iterator result is not an object"),
        )?;
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let k = record_number(machine, record, FIELD_K)?;
    let array = record_get(machine, record, FIELD_ARRAY)?;
    match machine.get_named_property(result, "done") {
        Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
        Err(failure) => return reject_cap_failure_and_void(machine, record, failure),
        Ok(done) if machine.to_boolean(done) => {
            // Set(array, "length", F(k), true) then return array.
            match machine.set_data_property(array, "length", crate::number_value(k)) {
                Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
                Err(failure) => return reject_cap_failure_and_void(machine, record, failure),
                Ok(()) => {
                    resolve_cap(machine, record, array)?;
                    return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
                }
            }
        }
        Ok(_) => {}
    }
    let value = match machine.get_named_property(result, "value") {
        Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
        Err(failure) => return reject_cap_failure_and_void(machine, record, failure),
        Ok(value) => value,
    };
    let mapper = record_get(machine, record, FIELD_MAPPER)?;
    if mapper == Value::UNDEFINED {
        define_then_continue(machine, record, value)?;
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let this_arg = record_get(machine, record, FIELD_THIS_ARG)?;
    match machine.call_value(mapper, this_arg, &[value, crate::number_value(k)]) {
        Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
        Err(failure) => {
            close_then_reject(machine, record, failure)?;
        }
        Ok(called) => {
            // IfAbruptCloseAsyncIterator(Await(mappedValue)): a mapped
            // rejection closes the iterator with the rejection reason.
            let awaited = machine.promise_resolve(called)?;
            attach(
                machine,
                awaited,
                T_ITER_MAPPED,
                T_ITER_MAPPED_REJECTED,
                record,
            )?;
        }
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn iter_mapped<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let mapped = argument(args, 1);
    define_then_continue(machine, record, mapped)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn iter_mapped_rejected<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let reason = argument(args, 1);
    record_put(machine, record, FIELD_PENDING, reason)?;
    start_async_close(machine, record)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn reject_cap_handler<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_cap_value(machine, argument(args, 0), argument(args, 1))?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn close_settled<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let reason = record_get(machine, record, FIELD_PENDING)?;
    reject_cap_value(machine, record, reason)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn arraylike_driver<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
) -> Result<(), EvalFailure> {
    let k = record_number(machine, record, FIELD_K)?;
    let length = record_number(machine, record, FIELD_LEN)?;
    if k >= length {
        let array = record_get(machine, record, FIELD_ARRAY)?;
        machine.set_data_property(array, "length", crate::number_value(length))?;
        return resolve_cap(machine, record, array);
    }
    let source = record_get(machine, record, FIELD_SOURCE)?;
    let key = index_key(&mut machine.atoms, k as usize);
    match machine.get_property_key(source, &key) {
        Err(EvalFailure::Runtime(kind)) => Err(EvalFailure::Runtime(kind)),
        Err(failure) => reject_cap_failure(machine, record, failure),
        Ok(value) => {
            let awaited = machine.promise_resolve(value)?;
            attach(machine, awaited, T_ARRAYLIKE_VALUE, T_REJECT_CAP, record)
        }
    }
}

fn arraylike_value<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let value = argument(args, 1);
    let mapper = record_get(machine, record, FIELD_MAPPER)?;
    if mapper == Value::UNDEFINED {
        let k = record_number(machine, record, FIELD_K)?;
        let array = record_get(machine, record, FIELD_ARRAY)?;
        define_element(machine, array, k, value)?;
        record_bump_k(machine, record)?;
        arraylike_driver(machine, record)?;
        return Ok(BuiltinOutcome::Value(Value::UNDEFINED));
    }
    let k = record_number(machine, record, FIELD_K)?;
    let this_arg = record_get(machine, record, FIELD_THIS_ARG)?;
    let called = machine.call_value(mapper, this_arg, &[value, crate::number_value(k)])?;
    let awaited = machine.promise_resolve(called)?;
    attach(machine, awaited, T_ARRAYLIKE_MAPPED, T_REJECT_CAP, record)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn arraylike_mapped<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let record = argument(args, 0);
    let mapped = argument(args, 1);
    let k = record_number(machine, record, FIELD_K)?;
    let array = record_get(machine, record, FIELD_ARRAY)?;
    define_element(machine, array, k, mapped)?;
    record_bump_k(machine, record)?;
    arraylike_driver(machine, record)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn reject_cap_failure_and_void<H: Host>(
    machine: &mut Machine<'_, H>,
    record: Value,
    failure: EvalFailure,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_cap_failure(machine, record, failure)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn from_async_run<H: Host>(
    machine: &mut Machine<'_, H>,
    ctor: Value,
    args: &[Value],
    cap: Value,
) -> Result<(), EvalFailure> {
    let items = argument(args, 0);
    let mapper = argument(args, 1);
    if mapper != Value::UNDEFINED && !machine.is_callable(mapper)? {
        return Err(type_error("Array.fromAsync mapper is not callable"));
    }
    let this_arg = argument(args, 2);
    let async_key =
        machine.property_key_from_value(machine.intrinsics.builtins.symbol_async_iterator())?;
    let mut iterator_handle = None;
    if let Some(method) = get_method(machine, items, &async_key)? {
        iterator_handle = Some(get_iterator_from_method(machine, items, method, false)?);
    } else {
        let sync_key =
            machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())?;
        if let Some(method) = get_method(machine, items, &sync_key)? {
            iterator_handle = Some(get_iterator_from_method(machine, items, method, true)?);
        }
    }
    let record = new_record(machine)?;
    record_put(machine, record, FIELD_CAP, cap)?;
    record_put(machine, record, FIELD_MAPPER, mapper)?;
    record_put(machine, record, FIELD_THIS_ARG, this_arg)?;
    record_put(machine, record, FIELD_K, crate::number_value(0.0))?;
    let construct = machine.is_constructor(ctor)?;
    if let Some(handle) = iterator_handle {
        // Construct(ctor) comes after GetIteratorFromMethod per 23.1.2.2.
        let array = if construct {
            machine.construct_value(ctor, &[])?
        } else {
            allocate_array(machine, Vec::new())?
        };
        record_put(machine, record, FIELD_MODE, Value::int32(0))?;
        record_put(machine, record, FIELD_ITER, handle)?;
        record_put(machine, record, FIELD_ARRAY, array)?;
        iter_driver(machine, record)
    } else {
        let array_like = machine.value_to_object(items)?;
        let length = length_of_array_like(machine, array_like)?;
        let array = if construct {
            machine.construct_value(ctor, &[crate::number_value(length as f64)])?
        } else {
            array_create(machine, length)?
        };
        record_put(machine, record, FIELD_MODE, Value::int32(1))?;
        record_put(machine, record, FIELD_SOURCE, array_like)?;
        record_put(
            machine,
            record,
            FIELD_LEN,
            crate::number_value(length as f64),
        )?;
        record_put(machine, record, FIELD_ARRAY, array)?;
        arraylike_driver(machine, record)
    }
}

fn from_async<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let promise = machine.create_promise()?;
    let cap = machine.create_promise_resolver(promise)?;
    match from_async_run(machine, this, args, cap) {
        Err(EvalFailure::Runtime(kind)) => Err(EvalFailure::Runtime(kind)),
        Err(failure) => {
            machine.reject_promise_resolver_failure(cap, failure)?;
            Ok(BuiltinOutcome::Value(promise))
        }
        Ok(()) => Ok(BuiltinOutcome::Value(promise)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intrinsics::builtins::test_support::{TestHost, blank_program, ordinary_object};
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, Property, PropertyMap, ThrowOrigin};
    use bamts_bytecode::EcmaString;
    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("array es2023");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        test(&mut machine);
    }

    fn value(outcome: BuiltinOutcome) -> Value {
        let BuiltinOutcome::Value(value) = outcome else {
            panic!("Array builtin did not complete with a value")
        };
        value
    }

    fn array(machine: &Machine<'_, TestHost>, value: Value) -> Vec<Value> {
        machine
            .array_elements(value)
            .expect("array lookup succeeds")
            .expect("result is an array")
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        length: u32,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, id, name, length)
    }

    fn is_seven<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::boolean(
            args.first().copied() == Some(Value::int32(7)),
        )))
    }

    fn mutate_and_match<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let index = args.get(1).copied().unwrap_or(Value::UNDEFINED);
        machine.array_push(this, index)?;
        let source = args.get(2).copied().unwrap_or(Value::UNDEFINED);
        if index == Value::int32(2) {
            machine.set_data_property(source, "1", Value::int32(42))?;
            machine.set_data_property(source, "3", Value::int32(99))?;
        }
        Ok(BuiltinOutcome::Value(Value::boolean(
            args.first().copied() == Some(Value::int32(42)),
        )))
    }

    fn compare_tens<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let left = value_number(argument(args, 0));
        let right = value_number(argument(args, 1));
        Ok(BuiltinOutcome::Value(crate::number_value(
            (left / 10.0).floor() - (right / 10.0).floor(),
        )))
    }

    fn throwing<H: Host>(
        _machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("observable abrupt completion"))
    }

    fn record_length<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let log = machine.get_named_property(this, "_log")?;
        machine.array_push(log, Value::int32(0))?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "_len")?,
        ))
    }

    fn record_value_of<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let log = machine.get_named_property(this, "_log")?;
        let label = machine.get_named_property(this, "_label")?;
        machine.array_push(log, label)?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "_number")?,
        ))
    }

    #[test]
    fn sparse_and_inherited_indices_are_read_and_copies_are_dense() {
        with_machine(|machine| {
            let prototype = ordinary_object(machine);
            machine
                .set_data_property(prototype, "1", Value::int32(7))
                .unwrap();
            let source = machine
                .allocate(HeapEntry::Array {
                    elements: vec![Value::HOLE; 3],
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap();
            let predicate = native(machine, "is seven", 1, is_seven::<TestHost>);
            let found = value(find_last_index(machine, source, &[predicate], false).unwrap());
            assert_eq!(found, Value::int32(1));

            let reversed = value(to_reversed(machine, source, &[], false).unwrap());
            assert_eq!(
                array(machine, reversed),
                vec![Value::UNDEFINED, Value::int32(7), Value::UNDEFINED]
            );
            for index in 0..3 {
                let key = index_key(&mut machine.atoms, index);
                assert!(machine.own_descriptor(reversed, &key).unwrap().is_some());
            }
        });
    }

    #[test]
    fn generic_at_observes_negative_zero_and_inherited_get() {
        with_machine(|machine| {
            let prototype = ordinary_object(machine);
            machine
                .set_data_property(prototype, "0", Value::int32(5))
                .unwrap();
            let receiver = machine
                .allocate(HeapEntry::Object {
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    boxed_primitive: None,
                })
                .unwrap();
            machine
                .set_data_property(receiver, "length", Value::int32(1))
                .unwrap();
            assert_eq!(
                value(at(machine, receiver, &[Value::number(-0.0)], false).unwrap()),
                Value::int32(5)
            );
            assert_eq!(
                value(at(machine, receiver, &[Value::int32(1)], false).unwrap()),
                Value::UNDEFINED
            );
        });
    }

    #[test]
    fn find_last_snapshots_length_but_reads_mutated_values() {
        with_machine(|machine| {
            let source = allocate_array(
                machine,
                vec![Value::int32(1), Value::int32(2), Value::int32(3)],
            )
            .unwrap();
            let log = allocate_array(machine, Vec::new()).unwrap();
            let predicate = native(machine, "mutate and match", 3, mutate_and_match::<TestHost>);
            let found = value(find_last_index(machine, source, &[predicate, log], false).unwrap());
            assert_eq!(found, Value::int32(1));
            assert_eq!(array(machine, log), vec![Value::int32(2), Value::int32(1)]);
            assert_eq!(machine.array_length(source).unwrap(), 4);
        });
    }

    #[test]
    fn to_sorted_is_stable_dense_and_propagates_comparator_failure() {
        with_machine(|machine| {
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(6))
                .unwrap();
            for (index, item) in [21, 10, 20, 11, 12].into_iter().enumerate() {
                machine
                    .set_data_property(source, &index.to_string(), Value::int32(item))
                    .unwrap();
            }
            machine
                .set_data_property(source, "constructor", Value::NULL)
                .unwrap();
            let comparator = native(machine, "compare tens", 2, compare_tens::<TestHost>);
            let sorted = value(to_sorted(machine, source, &[comparator], false).unwrap());
            assert_eq!(
                array(machine, sorted),
                vec![
                    Value::int32(10),
                    Value::int32(11),
                    Value::int32(12),
                    Value::int32(21),
                    Value::int32(20),
                    Value::UNDEFINED,
                ]
            );
            assert_eq!(
                machine.internal_get_prototype_of(sorted).unwrap(),
                Some(machine.intrinsics.array_prototype)
            );

            let abrupt = native(machine, "throwing comparator", 2, throwing::<TestHost>);
            assert!(matches!(
                to_sorted(machine, source, &[abrupt], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn to_spliced_observes_length_start_skip_coercion_order() {
        with_machine(|machine| {
            let log = allocate_array(machine, Vec::new()).unwrap();
            let receiver = ordinary_object(machine);
            machine.set_data_property(receiver, "_log", log).unwrap();
            machine
                .set_data_property(receiver, "_len", Value::int32(3))
                .unwrap();
            for (index, item) in [1, 2, 3].into_iter().enumerate() {
                machine
                    .set_data_property(receiver, &index.to_string(), Value::int32(item))
                    .unwrap();
            }
            let length_getter = native(machine, "length getter", 0, record_length::<TestHost>);
            let length_key = PropertyKey::Named(machine.intern_str("length"));
            machine
                .define_descriptor(
                    receiver,
                    length_key,
                    Property::Accessor {
                        getter: Some(length_getter),
                        setter: None,
                        enumerable: false,
                        configurable: true,
                    },
                )
                .unwrap();
            let start = ordinary_object(machine);
            let skip = ordinary_object(machine);
            for (object, label, number) in [(start, 1, 1), (skip, 2, 1)] {
                machine.set_data_property(object, "_log", log).unwrap();
                machine
                    .set_data_property(object, "_label", Value::int32(label))
                    .unwrap();
                machine
                    .set_data_property(object, "_number", Value::int32(number))
                    .unwrap();
                let value_of = native(machine, "valueOf", 0, record_value_of::<TestHost>);
                machine
                    .set_data_property(object, "valueOf", value_of)
                    .unwrap();
            }
            let result = value(
                to_spliced(machine, receiver, &[start, skip, Value::int32(9)], false).unwrap(),
            );
            assert_eq!(
                array(machine, log),
                vec![Value::int32(0), Value::int32(1), Value::int32(2)]
            );
            assert_eq!(
                array(machine, result),
                vec![Value::int32(1), Value::int32(9), Value::int32(3)]
            );
        });
    }

    #[test]
    fn with_rejects_invalid_indices_and_skips_replaced_get() {
        with_machine(|machine| {
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(2))
                .unwrap();
            machine
                .set_data_property(source, "1", Value::int32(2))
                .unwrap();
            let getter = native(machine, "throwing getter", 0, throwing::<TestHost>);
            let zero = index_key(&mut machine.atoms, 0);
            machine
                .define_descriptor(
                    source,
                    zero,
                    Property::Accessor {
                        getter: Some(getter),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            let result = value(
                with(
                    machine,
                    source,
                    &[Value::number(-0.0), Value::int32(9)],
                    false,
                )
                .unwrap(),
            );
            assert_eq!(
                array(machine, result),
                vec![Value::int32(9), Value::int32(2)]
            );
            for index in [Value::int32(2), Value::number(f64::INFINITY)] {
                assert!(matches!(
                    with(machine, source, &[index, Value::UNDEFINED], false),
                    Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                ));
            }
        });
    }

    #[test]
    fn oversized_generic_length_fails_before_backing_allocation() {
        with_machine(|machine| {
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", crate::number_value(u32::MAX as f64 + 1.0))
                .unwrap();
            assert!(matches!(
                to_reversed(machine, source, &[], false),
                Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
            ));
        });
    }

    #[test]
    fn copying_methods_are_dense_ignore_species_and_do_not_mutate_source() {
        with_machine(|machine| {
            let prototype = ordinary_object(machine);
            machine
                .set_data_property(prototype, "1", Value::int32(7))
                .unwrap();
            let source = machine
                .allocate(HeapEntry::Array {
                    elements: vec![Value::HOLE; 3],
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap();
            let trap = native(
                machine,
                "unexpected constructor getter",
                0,
                throwing::<TestHost>,
            );
            let constructor_key = PropertyKey::Named(machine.intern_str("constructor"));
            machine
                .define_descriptor(
                    source,
                    constructor_key,
                    Property::Accessor {
                        getter: Some(trap),
                        setter: None,
                        enumerable: false,
                        configurable: true,
                    },
                )
                .unwrap();

            let reversed = value(to_reversed(machine, source, &[], false).unwrap());
            let sorted = value(to_sorted(machine, source, &[], false).unwrap());
            let spliced = value(
                to_spliced(machine, source, &[Value::int32(1), Value::int32(0)], false).unwrap(),
            );
            let replaced =
                value(with(machine, source, &[Value::int32(0), Value::int32(9)], false).unwrap());

            assert_eq!(
                array(machine, reversed),
                vec![Value::UNDEFINED, Value::int32(7), Value::UNDEFINED]
            );
            assert_eq!(
                array(machine, sorted),
                vec![Value::int32(7), Value::UNDEFINED, Value::UNDEFINED]
            );
            assert_eq!(
                array(machine, spliced),
                vec![Value::UNDEFINED, Value::int32(7), Value::UNDEFINED]
            );
            assert_eq!(
                array(machine, replaced),
                vec![Value::int32(9), Value::int32(7), Value::UNDEFINED]
            );
            for copy in [reversed, sorted, spliced, replaced] {
                assert_eq!(
                    machine.internal_get_prototype_of(copy).unwrap(),
                    Some(machine.intrinsics.array_prototype)
                );
                for index in 0..3 {
                    let key = index_key(&mut machine.atoms, index);
                    assert!(matches!(
                        machine.own_descriptor(copy, &key).unwrap(),
                        Some(Property::Data {
                            writable: true,
                            enumerable: true,
                            configurable: true,
                            ..
                        })
                    ));
                }
            }
            assert_eq!(array(machine, source), vec![Value::HOLE; 3]);
        });
    }

    #[test]
    fn copying_methods_bypass_inherited_result_setters() {
        with_machine(|machine| {
            let trap = native(machine, "unexpected setter", 1, throwing::<TestHost>);
            let zero = index_key(&mut machine.atoms, 0);
            machine
                .define_descriptor(
                    machine.intrinsics.array_prototype,
                    zero,
                    Property::Accessor {
                        getter: None,
                        setter: Some(trap),
                        enumerable: false,
                        configurable: true,
                    },
                )
                .unwrap();
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(1))
                .unwrap();
            machine
                .set_data_property(source, "0", Value::int32(4))
                .unwrap();

            for copy in [
                value(to_reversed(machine, source, &[], false).unwrap()),
                value(to_sorted(machine, source, &[], false).unwrap()),
                value(to_spliced(machine, source, &[], false).unwrap()),
                value(with(machine, source, &[Value::int32(0), Value::int32(4)], false).unwrap()),
            ] {
                assert_eq!(array(machine, copy), vec![Value::int32(4)]);
                let zero = index_key(&mut machine.atoms, 0);
                assert!(matches!(
                    machine.own_descriptor(copy, &zero).unwrap(),
                    Some(Property::Data { value, .. }) if value == Value::int32(4)
                ));
            }
        });
    }

    #[test]
    fn to_sorted_default_order_is_utf16_lexicographic() {
        with_machine(|machine| {
            let ten = machine
                .allocate(HeapEntry::String(EcmaString::encode("10")))
                .unwrap();
            let two = machine
                .allocate(HeapEntry::String(EcmaString::encode("2")))
                .unwrap();
            let one = machine
                .allocate(HeapEntry::String(EcmaString::encode("1")))
                .unwrap();
            let source = allocate_array(machine, vec![ten, two, one]).unwrap();

            let sorted = value(to_sorted(machine, source, &[], false).unwrap());

            assert_eq!(array(machine, sorted), vec![one, ten, two]);
            assert_eq!(array(machine, source), vec![ten, two, one]);
        });
    }

    #[test]
    fn to_spliced_distinguishes_missing_skip_and_rejects_unsafe_length() {
        with_machine(|machine| {
            let source = allocate_array(
                machine,
                vec![Value::int32(1), Value::int32(2), Value::int32(3)],
            )
            .unwrap();
            let missing = value(to_spliced(machine, source, &[Value::int32(1)], false).unwrap());
            let explicit_undefined = value(
                to_spliced(machine, source, &[Value::int32(1), Value::UNDEFINED], false).unwrap(),
            );
            assert_eq!(array(machine, missing), vec![Value::int32(1)]);
            assert_eq!(
                array(machine, explicit_undefined),
                vec![Value::int32(1), Value::int32(2), Value::int32(3)]
            );
            assert_eq!(
                array(machine, source),
                vec![Value::int32(1), Value::int32(2), Value::int32(3)]
            );

            let oversized = ordinary_object(machine);
            machine
                .set_data_property(oversized, "length", crate::number_value(f64::INFINITY))
                .unwrap();
            assert!(matches!(
                to_spliced(
                    machine,
                    oversized,
                    &[Value::int32(0), Value::int32(0), Value::int32(9)],
                    false,
                ),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn with_accepts_negative_length_boundary_and_rejects_outside() {
        with_machine(|machine| {
            let source = allocate_array(machine, vec![Value::int32(1), Value::int32(2)]).unwrap();
            let result = value(
                with(
                    machine,
                    source,
                    &[Value::number(-2.0), Value::int32(8)],
                    false,
                )
                .unwrap(),
            );
            assert_eq!(
                array(machine, result),
                vec![Value::int32(8), Value::int32(2)]
            );
            for index in [Value::number(-3.0), Value::number(f64::NEG_INFINITY)] {
                assert!(matches!(
                    with(machine, source, &[index, Value::UNDEFINED], false),
                    Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                ));
            }
        });
    }

    #[test]
    fn copying_methods_propagate_abrupt_reads_and_argument_coercions() {
        with_machine(|machine| {
            let trap = native(machine, "abrupt operation", 0, throwing::<TestHost>);
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(2))
                .unwrap();
            let zero = index_key(&mut machine.atoms, 0);
            machine
                .define_descriptor(
                    source,
                    zero,
                    Property::Accessor {
                        getter: Some(trap),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            machine
                .set_data_property(source, "1", Value::int32(2))
                .unwrap();
            assert!(matches!(
                to_reversed(machine, source, &[], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                to_sorted(machine, source, &[], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                to_spliced(machine, source, &[Value::int32(0), Value::int32(0)], false,),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                with(machine, source, &[Value::int32(1), Value::int32(9)], false,),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));

            let coercion = ordinary_object(machine);
            machine
                .set_data_property(coercion, "valueOf", trap)
                .unwrap();
            assert!(matches!(
                to_spliced(machine, source, &[coercion], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                with(machine, source, &[coercion, Value::int32(9)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn to_sorted_rejects_noncallable_comparator_before_length_get() {
        with_machine(|machine| {
            let log = allocate_array(machine, Vec::new()).unwrap();
            let source = ordinary_object(machine);
            machine.set_data_property(source, "_log", log).unwrap();
            machine
                .set_data_property(source, "_len", Value::int32(0))
                .unwrap();
            let length_getter = native(machine, "length getter", 0, record_length::<TestHost>);
            let length_key = PropertyKey::Named(machine.intern_str("length"));
            machine
                .define_descriptor(
                    source,
                    length_key,
                    Property::Accessor {
                        getter: Some(length_getter),
                        setter: None,
                        enumerable: false,
                        configurable: true,
                    },
                )
                .unwrap();

            assert!(matches!(
                to_sorted(machine, source, &[Value::int32(0)], false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(array(machine, log).is_empty());
        });
    }

    #[test]
    fn installed_methods_have_standard_descriptors_names_and_lengths() {
        with_machine(|machine| {
            let prototype = machine.intrinsics.array_prototype;
            let constructor = machine.intrinsics.global("Array").unwrap();
            install(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.intrinsics.builtins,
                prototype,
                constructor,
            );
            let from_async = machine
                .get_named_property(constructor, "fromAsync")
                .unwrap();
            let from_async_key = PropertyKey::Named(machine.intern_str("fromAsync"));
            assert!(matches!(
                machine.own_descriptor(constructor, &from_async_key).unwrap(),
                Some(Property::Data { value, writable: true, enumerable: false, configurable: true }) if value == from_async
            ));
            assert_eq!(
                machine.get_named_property(from_async, "length").unwrap(),
                crate::number_value(3.0)
            );
            for (name, length) in [
                ("at", 1),
                ("findLast", 1),
                ("findLastIndex", 1),
                ("toReversed", 0),
                ("toSorted", 1),
                ("toSpliced", 2),
                ("with", 2),
            ] {
                let method = machine.get_named_property(prototype, name).unwrap();
                let key = PropertyKey::Named(machine.intern_str(name));
                assert!(matches!(
                    machine.own_descriptor(prototype, &key).unwrap(),
                    Some(Property::Data { value, writable: true, enumerable: false, configurable: true }) if value == method
                ));
                assert_eq!(
                    machine.get_named_property(method, "length").unwrap(),
                    crate::number_value(length as f64)
                );
                let installed_name = machine.get_named_property(method, "name").unwrap();
                assert_eq!(
                    machine.string_value(installed_name).unwrap(),
                    EcmaString::encode(name)
                );
            }
        });
    }

    // ---- Array.fromAsync tests -------------------------------------------------

    fn settled<F>(machine: &Machine<'_, TestHost>, promise: Value, assertion: F)
    where
        F: FnMut(&crate::PromiseState),
    {
        let mut assertion = assertion;
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise { state, .. } = &machine.heap[index] else {
            panic!("result is a promise")
        };
        assertion(state)
    }

    fn array_ctor_and_from_async(machine: &mut Machine<'_, TestHost>) -> (Value, Value) {
        let prototype = machine.intrinsics.array_prototype;
        let constructor = machine.intrinsics.global("Array").unwrap();
        install(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.intrinsics.builtins,
            prototype,
            constructor,
        );
        let method = machine
            .get_named_property(constructor, "fromAsync")
            .unwrap();
        (constructor, method)
    }

    fn promise_of<H: Host>(
        machine: &mut Machine<'_, H>,
        value: Value,
    ) -> Result<Value, EvalFailure> {
        let promise = machine.create_promise()?;
        machine
            .fulfill_promise(promise, value)
            .map_err(EvalFailure::Runtime)?;
        Ok(promise)
    }

    fn async_next_oneshot<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let index = machine.get_named_property(this, "_i")?;
        let index = value_number(index) as usize;
        machine.set_data_property(this, "_i", crate::number_value((index + 1) as f64))?;
        let values = machine.get_named_property(this, "_values")?;
        let elements = machine.array_elements(values)?.unwrap_or_default();
        let value = elements.get(index).copied().unwrap_or(Value::UNDEFINED);
        let result = machine.iterator_result(value, index >= elements.len())?;
        promise_of(machine, result).map(BuiltinOutcome::Value)
    }

    fn custom_async_iterable(machine: &mut Machine<'_, TestHost>, values: Vec<Value>) -> Value {
        let next = native(machine, "async next", 0, async_next_oneshot::<TestHost>);
        let iterable = ordinary_object(machine);
        machine
            .set_data_property(iterable, "_i", Value::int32(0))
            .unwrap();
        let backing = allocate_array(machine, values).unwrap();
        machine
            .set_data_property(iterable, "_values", backing)
            .unwrap();
        machine.set_data_property(iterable, "next", next).unwrap();
        let iterator = machine.intrinsics.builtins.symbol_async_iterator();
        let self_target = native(machine, "iterator self", 0, iterator_self::<TestHost>);
        let key = machine.property_key_from_value(iterator).unwrap();
        machine
            .set_data_property_key(iterable, key, self_target)
            .unwrap();
        iterable
    }

    fn iterator_self<H: Host>(
        _machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    fn times_ten_promise<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let value = value_number(args.first().copied().unwrap_or(Value::UNDEFINED));
        promise_of(machine, crate::number_value(value * 10.0)).map(BuiltinOutcome::Value)
    }

    fn sync_next<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let index = value_number(machine.get_named_property(this, "_i")?) as usize;
        machine.set_data_property(this, "_i", crate::number_value((index + 1) as f64))?;
        let values = machine.get_named_property(this, "_values")?;
        let elements = machine.array_elements(values)?.unwrap_or_default();
        let value = elements.get(index).copied().unwrap_or(Value::UNDEFINED);
        machine
            .iterator_result(value, index >= elements.len())
            .map(BuiltinOutcome::Value)
    }

    fn custom_sync_iterable(machine: &mut Machine<'_, TestHost>, values: Vec<Value>) -> Value {
        let next = native(machine, "sync next", 0, sync_next::<TestHost>);
        let iterable = ordinary_object(machine);
        machine
            .set_data_property(iterable, "_i", Value::int32(0))
            .unwrap();
        let backing = allocate_array(machine, values).unwrap();
        machine
            .set_data_property(iterable, "_values", backing)
            .unwrap();
        machine.set_data_property(iterable, "next", next).unwrap();
        let self_target = native(machine, "sync iterator self", 0, iterator_self::<TestHost>);
        let key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
            .unwrap();
        machine
            .set_data_property_key(iterable, key, self_target)
            .unwrap();
        iterable
    }

    fn run_from_async(machine: &mut Machine<'_, TestHost>, args: &[Value]) -> Value {
        let (constructor, method) = array_ctor_and_from_async(machine);
        let promise = machine.call_value(method, constructor, args).unwrap();
        machine.drain_microtasks().unwrap();
        promise
    }

    fn fulfilled_array(machine: &Machine<'_, TestHost>, promise: Value) -> Vec<Value> {
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise {
            state: crate::PromiseState::Fulfilled { value },
            ..
        } = &machine.heap[index]
        else {
            panic!("fromAsync promise must be fulfilled")
        };
        machine
            .array_elements(*value)
            .unwrap()
            .expect("fulfilled value is an array")
    }

    fn rejected_reason(machine: &Machine<'_, TestHost>, promise: Value) -> Value {
        let index = machine.runtime_slot(promise).unwrap().unwrap();
        let HeapEntry::Promise {
            state: crate::PromiseState::Rejected { reason, .. },
            ..
        } = &machine.heap[index]
        else {
            panic!("fromAsync promise must be rejected")
        };
        *reason
    }

    #[test]
    fn from_async_consumes_sync_iterable_with_mapped_promises() {
        with_machine(|machine| {
            let items = custom_sync_iterable(
                machine,
                vec![Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let mapper = native(
                machine,
                "times ten promise",
                1,
                times_ten_promise::<TestHost>,
            );
            let promise = run_from_async(machine, &[items, mapper]);
            assert_eq!(
                fulfilled_array(machine, promise),
                vec![Value::int32(10), Value::int32(20), Value::int32(30)]
            );
        });
    }

    #[test]
    fn from_async_consumes_async_iterator_and_awaits_result_objects() {
        with_machine(|machine| {
            let items = custom_async_iterable(machine, vec![Value::int32(4), Value::int32(5)]);
            let promise = run_from_async(machine, &[items]);
            assert_eq!(
                fulfilled_array(machine, promise),
                vec![Value::int32(4), Value::int32(5)]
            );
        });
    }

    #[test]
    fn from_async_array_like_awaits_thenable_property_values() {
        with_machine(|machine| {
            let thenable = ordinary_object(machine);
            let then = native(machine, "thenable then", 2, then_resolve_42::<TestHost>);
            machine.set_data_property(thenable, "then", then).unwrap();
            let source = ordinary_object(machine);
            machine
                .set_data_property(source, "length", Value::int32(2))
                .unwrap();
            machine.set_data_property(source, "0", thenable).unwrap();
            machine
                .set_data_property(source, "1", Value::int32(7))
                .unwrap();
            let promise = run_from_async(machine, &[source]);
            assert_eq!(
                fulfilled_array(machine, promise),
                vec![Value::int32(42), Value::int32(7)]
            );
        });
    }

    fn then_resolve_42<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let resolve = args.first().copied().unwrap_or(Value::UNDEFINED);
        let result = machine.call_value(resolve, Value::UNDEFINED, &[Value::int32(42)])?;
        Ok(BuiltinOutcome::Value(result))
    }

    #[test]
    fn from_async_rejects_for_uncallable_mapper_without_iterating() {
        with_machine(|machine| {
            let items = custom_sync_iterable(machine, vec![Value::int32(1)]);
            let promise = run_from_async(machine, &[items, Value::int32(0)]);
            let reason = rejected_reason(machine, promise);
            assert!(machine.is_object(reason));
        });
    }

    #[test]
    fn from_async_rejects_for_nullish_items() {
        with_machine(|machine| {
            let promise = run_from_async(machine, &[Value::NULL]);
            assert!(machine.is_object(rejected_reason(machine, promise)));
        });
    }

    #[test]
    fn from_async_constructor_receiver_builds_constructed_array() {
        with_machine(|machine| {
            let items = custom_sync_iterable(machine, vec![Value::int32(9)]);
            let promise = run_from_async(machine, &[items]);
            let built = fulfilled_array(machine, promise);
            assert_eq!(built, vec![Value::int32(9)]);
        });
    }

    #[test]
    fn from_async_settles_capability_immediately_returned_for_pending_input() {
        with_machine(|machine| {
            let pending = {
                let (constructor, method) = array_ctor_and_from_async(machine);
                let iterator = custom_async_iterable(machine, vec![Value::int32(2)]);
                machine
                    .call_value(method, constructor, &[iterator])
                    .unwrap()
            };
            settled(machine, pending, |state| {
                assert!(matches!(state, crate::PromiseState::Pending { .. }));
            });
            machine.drain_microtasks().unwrap();
            assert_eq!(fulfilled_array(machine, pending), vec![Value::int32(2)]);
        });
    }
}
