//! The `Iterator` constructor, its helpers, and `Iterator.from/concat/zip`.
//!
//! The specification describes a helper as a generator closure. There is no
//! native generator here, so each helper is a `BuiltinIterator` whose `source` is
//! a hidden state array reachable only from it, and `advance` runs one step of
//! the closure per `next()`. The `status` slot carries the generator states,
//! which is what makes a helper reject re-entry while it is running.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::property_descriptor::descriptor_from_property;
use super::{
    allocate_array, allocate_string, define_data, define_frozen_data, define_symbol_property,
    heap_index, install_constructor_function, install_function, keep_root, range_error, type_error,
    value_number, with_roots,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey, PropertyMap,
};

/// What a helper does on each step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    Map,
    Filter,
    Take,
    Drop,
    FlatMap,
    Concat,
    Zip,
    ZipKeyed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ZipMode {
    Shortest,
    Longest,
    Strict,
}

const STATUS: usize = 0;
const ITERATOR: usize = 1;
const NEXT: usize = 2;
const CALLBACK: usize = 3;
const COUNTER: usize = 4;
const REMAINING: usize = 5;
const INNER: usize = 6;
const INNER_NEXT: usize = 7;
/// `Iterator.concat`'s `[method, iterable, ...]`, or `zip`'s `[iterator, next, ...]`
/// with a finished iterator's entries set to null.
const LIST: usize = 8;
const PADDING: usize = 9;
const KEYS: usize = 10;
const MODE: usize = 11;
const SLOTS: usize = 12;

const SUSPENDED_START: u32 = 0;
const SUSPENDED_YIELD: u32 = 1;
const RUNNING: u32 = 2;
const COMPLETED: u32 = 3;

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

fn is_nullish(value: Value) -> bool {
    matches!(value.decode(), Some(Decoded::Undefined | Decoded::Null))
}

fn hidden_array<H: Host>(
    machine: &mut Machine<'_, H>,
    elements: Vec<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Array {
            elements,
            properties: PropertyMap::default(),
            prototype: None,
            extensible: false,
            length_writable: false,
        })
        .map_err(EvalFailure::Runtime)
}

fn slot<H: Host>(machine: &Machine<'_, H>, state: Value, index: usize) -> Value {
    let HeapEntry::Array { elements, .. } = &machine.heap[heap_index(state)] else {
        unreachable!("helper state is a hidden array")
    };
    elements[index]
}

fn set_slot<H: Host>(machine: &mut Machine<'_, H>, state: Value, index: usize, value: Value) {
    let HeapEntry::Array { elements, .. } = &mut machine.heap[heap_index(state)] else {
        unreachable!("helper state is a hidden array")
    };
    elements[index] = value;
}

fn status<H: Host>(machine: &Machine<'_, H>, state: Value) -> u32 {
    value_number(slot(machine, state, STATUS)) as u32
}

fn set_status<H: Host>(machine: &mut Machine<'_, H>, state: Value, status: u32) {
    set_slot(machine, state, STATUS, Value::int32(status));
}

fn bump_counter<H: Host>(machine: &mut Machine<'_, H>, state: Value) {
    let next = value_number(slot(machine, state, COUNTER)) + 1.0;
    set_slot(machine, state, COUNTER, crate::number_value(next));
}

fn new_helper<H: Host>(
    machine: &mut Machine<'_, H>,
    operation: Operation,
    fields: &[(usize, Value)],
) -> Result<Value, EvalFailure> {
    let mut elements = vec![Value::UNDEFINED; SLOTS];
    elements[STATUS] = Value::int32(SUSPENDED_START);
    elements[COUNTER] = Value::int32(0);
    for &(index, value) in fields {
        elements[index] = value;
    }
    let source = hidden_array(machine, elements)?;
    machine
        .allocate(HeapEntry::BuiltinIterator {
            source,
            kind: IterationKind::IteratorHelper(operation),
            position: Some(0),
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.builtins.iterator_helper_prototype()),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

/// One `IteratorStepValue`. A failure here does not close the iterator: it is the
/// iterator that failed.
fn step_value<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    next: Value,
) -> Result<Option<Value>, EvalFailure> {
    let result = machine.call_value(next, iterator, &[])?;
    let (done, value) = machine.iterator_result_parts(result)?;
    Ok((!done).then_some(value))
}

/// One `IteratorStep`: `value` is never read, so skipping stays unobservable.
fn step<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    next: Value,
) -> Result<bool, EvalFailure> {
    let result = machine.call_value(next, iterator, &[])?;
    if !machine.is_object(result) {
        return Err(type_error("iterator result is not an object"));
    }
    let done = machine.get_named_property(result, "done")?;
    Ok(machine.to_boolean(done))
}

fn call_return<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<Option<Value>, EvalFailure> {
    let method = machine.get_named_property(iterator, "return")?;
    if is_nullish(method) {
        return Ok(None);
    }
    if !machine.is_callable(method)? {
        return Err(type_error("iterator return method is not callable"));
    }
    machine.call_value(method, iterator, &[]).map(Some)
}

fn failure_value(failure: &EvalFailure) -> Option<Value> {
    match failure {
        EvalFailure::ThrowValue(value) | EvalFailure::ThrowValueOrigin { value, .. } => {
            Some(*value)
        }
        _ => None,
    }
}

/// `IteratorClose`. An existing failure wins over anything `return` does, except
/// an engine failure, which cannot be replaced by a user throw.
fn close_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    completion: Result<(), EvalFailure>,
) -> Result<(), EvalFailure> {
    let held = completion.as_ref().err().and_then(failure_value);
    let roots: Vec<Value> = [iterator].into_iter().chain(held).collect();
    let closed = with_roots(machine, &roots, |machine, _| call_return(machine, iterator));
    match completion {
        Err(failure) => match closed {
            Err(EvalFailure::Runtime(kind)) => Err(EvalFailure::Runtime(kind)),
            _ => Err(failure),
        },
        Ok(()) => match closed? {
            Some(result) if !machine.is_object(result) => {
                Err(type_error("iterator return result is not an object"))
            }
            _ => Ok(()),
        },
    }
}

fn close_after<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    failure: EvalFailure,
) -> EvalFailure {
    match close_iterator(machine, iterator, Err(failure)) {
        Err(failure) => failure,
        Ok(()) => unreachable!("closing with a failure returns that failure"),
    }
}

fn call_closing<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    callback: Value,
    arguments: &[Value],
) -> Result<Value, EvalFailure> {
    match machine.call_callback(callback, Value::UNDEFINED, arguments) {
        Ok(value) => Ok(value),
        Err(failure) => Err(close_after(machine, iterator, failure)),
    }
}

/// `GetMethod(value, @@iterator)`.
fn iterator_method<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Option<Value>, EvalFailure> {
    let key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())?;
    let method = machine.get_property_key(value, &key)?;
    if is_nullish(method) {
        return Ok(None);
    }
    if !machine.is_callable(method)? {
        return Err(type_error("Symbol.iterator is not callable"));
    }
    Ok(Some(method))
}

/// `GetIteratorDirect`, once `iterator` is known to be an object.
fn direct_record<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<(Value, Value), EvalFailure> {
    if !machine.is_object(iterator) {
        return Err(type_error("iterator is not an object"));
    }
    let next = machine.get_named_property(iterator, "next")?;
    Ok((iterator, next))
}

/// `GetIteratorFlattenable`. A value with no `@@iterator` is taken to be an
/// iterator already, and only `Iterator.from` lets a string through.
fn flattenable<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    allow_string: bool,
) -> Result<(Value, Value), EvalFailure> {
    let is_string = machine.string_value(value).is_some();
    if !machine.is_object(value) && !(allow_string && is_string) {
        return Err(type_error("value is not iterable"));
    }
    let iterator = match iterator_method(machine, value)? {
        Some(method) => machine.call_value(method, value, &[])?,
        None => value,
    };
    direct_record(machine, iterator)
}

/// `GetIterator(value, sync)`.
fn get_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<(Value, Value), EvalFailure> {
    let Some(method) = iterator_method(machine, value)? else {
        return Err(type_error("value is not iterable"));
    };
    let iterator = machine.call_value(method, value, &[])?;
    direct_record(machine, iterator)
}

fn advance<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    operation: Operation,
    depth: usize,
) -> Result<Option<Value>, EvalFailure> {
    let iterator = slot(machine, state, ITERATOR);
    let next = slot(machine, state, NEXT);
    let callback = slot(machine, state, CALLBACK);
    match operation {
        Operation::Map => {
            let Some(value) = step_value(machine, iterator, next)? else {
                return Ok(None);
            };
            let counter = slot(machine, state, COUNTER);
            let mapped = call_closing(machine, iterator, callback, &[value, counter])?;
            bump_counter(machine, state);
            Ok(Some(mapped))
        }
        Operation::Filter => loop {
            let Some(value) = step_value(machine, iterator, next)? else {
                return Ok(None);
            };
            keep_root(machine, depth, value);
            let counter = slot(machine, state, COUNTER);
            let selected = call_closing(machine, iterator, callback, &[value, counter])?;
            bump_counter(machine, state);
            if machine.to_boolean(selected) {
                return Ok(Some(value));
            }
        },
        Operation::Take => {
            let remaining = value_number(slot(machine, state, REMAINING));
            if remaining == 0.0 {
                close_iterator(machine, iterator, Ok(()))?;
                return Ok(None);
            }
            set_slot(
                machine,
                state,
                REMAINING,
                crate::number_value(remaining - 1.0),
            );
            step_value(machine, iterator, next)
        }
        Operation::Drop => {
            let mut remaining = value_number(slot(machine, state, REMAINING));
            while remaining > 0.0 {
                remaining -= 1.0;
                set_slot(machine, state, REMAINING, crate::number_value(remaining));
                if step(machine, iterator, next)? {
                    return Ok(None);
                }
            }
            step_value(machine, iterator, next)
        }
        Operation::FlatMap => flat_map_step(machine, state, iterator, next, callback, depth),
        Operation::Concat => concat_step(machine, state),
        Operation::Zip | Operation::ZipKeyed => zip_step(machine, state, operation, depth),
    }
}

fn flat_map_step<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    iterator: Value,
    next: Value,
    callback: Value,
    depth: usize,
) -> Result<Option<Value>, EvalFailure> {
    loop {
        let inner = slot(machine, state, INNER);
        if inner != Value::UNDEFINED {
            let inner_next = slot(machine, state, INNER_NEXT);
            match step_value(machine, inner, inner_next) {
                Ok(Some(value)) => return Ok(Some(value)),
                Ok(None) => {
                    set_slot(machine, state, INNER, Value::UNDEFINED);
                    bump_counter(machine, state);
                    continue;
                }
                Err(failure) => return Err(close_after(machine, iterator, failure)),
            }
        }
        let Some(value) = step_value(machine, iterator, next)? else {
            return Ok(None);
        };
        let counter = slot(machine, state, COUNTER);
        let mapped = call_closing(machine, iterator, callback, &[value, counter])?;
        keep_root(machine, depth, mapped);
        match flattenable(machine, mapped, false) {
            Ok((inner, inner_next)) => {
                set_slot(machine, state, INNER, inner);
                set_slot(machine, state, INNER_NEXT, inner_next);
            }
            Err(failure) => return Err(close_after(machine, iterator, failure)),
        }
    }
}

fn concat_step<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
) -> Result<Option<Value>, EvalFailure> {
    loop {
        let iterator = slot(machine, state, ITERATOR);
        if iterator != Value::UNDEFINED {
            let next = slot(machine, state, NEXT);
            if let Some(value) = step_value(machine, iterator, next)? {
                return Ok(Some(value));
            }
            set_slot(machine, state, ITERATOR, Value::UNDEFINED);
        }
        let list = slot(machine, state, LIST);
        let index = value_number(slot(machine, state, COUNTER)) as usize;
        let items = machine.array_elements(list)?.unwrap_or_default();
        let (Some(method), Some(iterable)) = (items.get(index * 2), items.get(index * 2 + 1))
        else {
            return Ok(None);
        };
        bump_counter(machine, state);
        let opened = machine.call_value(*method, *iterable, &[])?;
        let (iterator, next) = direct_record(machine, opened)?;
        set_slot(machine, state, ITERATOR, iterator);
        set_slot(machine, state, NEXT, next);
    }
}

/// `IteratorCloseAll` over the open entries of a flat `[iterator, next, ...]`
/// list, last first.
fn close_list<H: Host>(
    machine: &mut Machine<'_, H>,
    list: &[Value],
    mut completion: Result<(), EvalFailure>,
) -> Result<(), EvalFailure> {
    for pair in list.chunks_exact(2).rev() {
        if pair[0] != Value::NULL {
            completion = close_iterator(machine, pair[0], completion);
        }
    }
    completion
}

fn close_open_iterators<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    completion: Result<(), EvalFailure>,
) -> Result<(), EvalFailure> {
    let list = slot(machine, state, LIST);
    let open = machine.array_elements(list)?.unwrap_or_default();
    close_list(machine, &open, completion)
}

fn mark_finished<H: Host>(machine: &mut Machine<'_, H>, state: Value, index: usize) {
    let list = slot(machine, state, LIST);
    let HeapEntry::Array { elements, .. } = &mut machine.heap[heap_index(list)] else {
        unreachable!("zip list is a hidden array")
    };
    elements[index * 2] = Value::NULL;
}

fn zip_mode<H: Host>(machine: &Machine<'_, H>, state: Value) -> ZipMode {
    match value_number(slot(machine, state, MODE)) as u32 {
        0 => ZipMode::Shortest,
        1 => ZipMode::Longest,
        _ => ZipMode::Strict,
    }
}

/// The strict-mode tail of a zip whose first iterator ended: every other one must
/// end on this same step.
fn finish_strict_zip<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    count: usize,
) -> Result<Option<Value>, EvalFailure> {
    let list = slot(machine, state, LIST);
    for index in 1..count {
        let pairs = machine.array_elements(list)?.unwrap_or_default();
        let (iterator, next) = (pairs[index * 2], pairs[index * 2 + 1]);
        match step(machine, iterator, next) {
            Err(failure) => {
                mark_finished(machine, state, index);
                close_open_iterators(machine, state, Err(failure))?;
            }
            Ok(true) => mark_finished(machine, state, index),
            Ok(false) => {
                let mismatch = type_error("Iterator.zip iterators have different lengths");
                close_open_iterators(machine, state, Err(mismatch))?;
            }
        }
    }
    Ok(None)
}

fn zip_step<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    operation: Operation,
    depth: usize,
) -> Result<Option<Value>, EvalFailure> {
    let mode = zip_mode(machine, state);
    let list = slot(machine, state, LIST);
    let count = machine.array_elements(list)?.unwrap_or_default().len() / 2;
    if count == 0 {
        return Ok(None);
    }
    let mut results = Vec::with_capacity(count);
    for index in 0..count {
        let pairs = machine.array_elements(list)?.unwrap_or_default();
        let (iterator, next) = (pairs[index * 2], pairs[index * 2 + 1]);
        let padding = slot(machine, state, PADDING);
        let value = if iterator == Value::NULL {
            machine.array_elements(padding)?.unwrap_or_default()[index]
        } else {
            match step_value(machine, iterator, next) {
                Err(failure) => {
                    mark_finished(machine, state, index);
                    close_open_iterators(machine, state, Err(failure))?;
                    unreachable!("closing with a failure returns that failure")
                }
                Ok(Some(value)) => value,
                Ok(None) => {
                    mark_finished(machine, state, index);
                    match mode {
                        ZipMode::Shortest => {
                            close_open_iterators(machine, state, Ok(()))?;
                            return Ok(None);
                        }
                        ZipMode::Strict if index != 0 => {
                            let mismatch =
                                type_error("Iterator.zip iterators have different lengths");
                            close_open_iterators(machine, state, Err(mismatch))?;
                            unreachable!("closing with a failure returns that failure")
                        }
                        ZipMode::Strict => return finish_strict_zip(machine, state, count),
                        ZipMode::Longest => {
                            let open = machine.array_elements(list)?.unwrap_or_default();
                            if open.chunks_exact(2).all(|pair| pair[0] == Value::NULL) {
                                return Ok(None);
                            }
                            machine.array_elements(padding)?.unwrap_or_default()[index]
                        }
                    }
                }
            }
        };
        keep_root(machine, depth, value);
        results.push(value);
    }
    if operation == Operation::Zip {
        return allocate_array(machine, results).map(Some);
    }
    let keys = slot(machine, state, KEYS);
    let keys = machine.array_elements(keys)?.unwrap_or_default();
    let object = super::ordinary_runtime(machine, None)?;
    for (key, value) in keys.into_iter().zip(results) {
        let key = machine.property_key_from_value(key)?;
        machine.create_data_property_key(object, key, value)?;
    }
    Ok(Some(object))
}

fn helper_state<H: Host>(
    machine: &Machine<'_, H>,
    this: Value,
) -> Result<(Value, Operation), EvalFailure> {
    let index = machine.runtime_slot(this).map_err(EvalFailure::Runtime)?;
    match index.map(|index| &machine.heap[index]) {
        Some(HeapEntry::BuiltinIterator {
            source,
            kind: IterationKind::IteratorHelper(operation),
            ..
        }) => Ok((*source, *operation)),
        _ => Err(type_error(
            "Iterator helper method on incompatible receiver",
        )),
    }
}

fn iterator_result<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    done: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .iterator_result(value, done)
        .map(BuiltinOutcome::Value)
}

/// `%IteratorHelperPrototype%.next`.
fn helper_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (state, operation) = helper_state(machine, this)?;
    match status(machine, state) {
        RUNNING => return Err(type_error("Iterator helper is already running")),
        COMPLETED => return iterator_result(machine, Value::UNDEFINED, true),
        _ => {}
    }
    set_status(machine, state, RUNNING);
    let advanced = with_roots(machine, &[this], |machine, depth| {
        advance(machine, state, operation, depth)
    });
    match advanced {
        Ok(Some(value)) => {
            set_status(machine, state, SUSPENDED_YIELD);
            iterator_result(machine, value, false)
        }
        Ok(None) => {
            set_status(machine, state, COMPLETED);
            iterator_result(machine, Value::UNDEFINED, true)
        }
        Err(failure) => {
            set_status(machine, state, COMPLETED);
            Err(failure)
        }
    }
}

/// Closes whatever a helper holds open, as a return completion would.
fn close_helper<H: Host>(
    machine: &mut Machine<'_, H>,
    state: Value,
    operation: Operation,
    started: bool,
) -> Result<(), EvalFailure> {
    let iterator = slot(machine, state, ITERATOR);
    match operation {
        Operation::Map | Operation::Filter | Operation::Take | Operation::Drop => {
            close_iterator(machine, iterator, Ok(()))
        }
        Operation::FlatMap => {
            let inner = slot(machine, state, INNER);
            if started
                && inner != Value::UNDEFINED
                && let Err(failure) = close_iterator(machine, inner, Ok(()))
            {
                return Err(close_after(machine, iterator, failure));
            }
            close_iterator(machine, iterator, Ok(()))
        }
        Operation::Concat if started && iterator != Value::UNDEFINED => {
            close_iterator(machine, iterator, Ok(()))
        }
        Operation::Concat => Ok(()),
        Operation::Zip | Operation::ZipKeyed => close_open_iterators(machine, state, Ok(())),
    }
}

/// `%IteratorHelperPrototype%.return`.
fn helper_return<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (state, operation) = helper_state(machine, this)?;
    let current = status(machine, state);
    match current {
        RUNNING => return Err(type_error("Iterator helper is already running")),
        COMPLETED => return iterator_result(machine, Value::UNDEFINED, true),
        _ => {}
    }
    let started = current == SUSPENDED_YIELD;
    set_status(machine, state, if started { RUNNING } else { COMPLETED });
    let closed = with_roots(machine, &[this], |machine, _| {
        close_helper(machine, state, operation, started)
    });
    set_status(machine, state, COMPLETED);
    closed?;
    iterator_result(machine, Value::UNDEFINED, true)
}

fn require_object<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
    operation: &'static str,
) -> Result<(), EvalFailure> {
    if machine.is_object(value) {
        Ok(())
    } else {
        Err(type_error(operation))
    }
}

/// The shared opening of the callback helpers: a bad argument closes the receiver
/// before `next` is read.
fn checked_callback<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    callback: Value,
) -> Result<(), EvalFailure> {
    require_object(machine, this, "Iterator helper requires an object receiver")?;
    if machine.is_callable(callback)? {
        return Ok(());
    }
    let failure = type_error("Iterator helper callback is not callable");
    Err(close_after(machine, this, failure))
}

fn callback_helper<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    operation: Operation,
) -> Result<BuiltinOutcome, EvalFailure> {
    let callback = argument(args, 0);
    checked_callback(machine, this, callback)?;
    let (iterator, next) = direct_record(machine, this)?;
    new_helper(
        machine,
        operation,
        &[(ITERATOR, iterator), (NEXT, next), (CALLBACK, callback)],
    )
    .map(BuiltinOutcome::Value)
}

fn map<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    callback_helper(machine, this, args, Operation::Map)
}

fn filter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    callback_helper(machine, this, args, Operation::Filter)
}

fn flat_map<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    callback_helper(machine, this, args, Operation::FlatMap)
}

/// The shared opening of `take` and `drop`. Each failure closes the receiver, and
/// `next` is read only once the limit is known to be valid.
fn limit_helper<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    operation: Operation,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(machine, this, "Iterator helper requires an object receiver")?;
    let limit = match machine.coerce_number_observable(argument(args, 0)) {
        Ok(limit) => value_number(limit),
        Err(failure) => return Err(close_after(machine, this, failure)),
    };
    if limit.is_nan() {
        let failure = range_error("Iterator helper limit is NaN");
        return Err(close_after(machine, this, failure));
    }
    let limit = limit.trunc();
    if limit < 0.0 {
        let failure = range_error("Iterator helper limit is negative");
        return Err(close_after(machine, this, failure));
    }
    let (iterator, next) = direct_record(machine, this)?;
    let remaining = crate::number_value(limit);
    new_helper(
        machine,
        operation,
        &[(ITERATOR, iterator), (NEXT, next), (REMAINING, remaining)],
    )
    .map(BuiltinOutcome::Value)
}

fn take<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    limit_helper(machine, this, args, Operation::Take)
}

fn drop<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    limit_helper(machine, this, args, Operation::Drop)
}

fn to_array<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_object(machine, this, "Iterator helper requires an object receiver")?;
    let (iterator, next) = direct_record(machine, this)?;
    with_roots(machine, &[iterator, next], |machine, depth| {
        let mut values = Vec::new();
        while let Some(value) = step_value(machine, iterator, next)? {
            keep_root(machine, depth, value);
            values.push(value);
        }
        allocate_array(machine, values)
    })
    .map(BuiltinOutcome::Value)
}

/// How a consumer treats each callback result.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Consumer {
    ForEach,
    Some,
    Every,
    Find,
}

fn consume<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    consumer: Consumer,
) -> Result<BuiltinOutcome, EvalFailure> {
    let callback = argument(args, 0);
    checked_callback(machine, this, callback)?;
    let (iterator, next) = direct_record(machine, this)?;
    with_roots(machine, &[iterator, next, callback], |machine, _| {
        let mut counter = 0.0;
        loop {
            let Some(value) = step_value(machine, iterator, next)? else {
                return Ok(match consumer {
                    Consumer::ForEach | Consumer::Find => Value::UNDEFINED,
                    Consumer::Some => Value::FALSE,
                    Consumer::Every => Value::TRUE,
                });
            };
            let arguments = [value, crate::number_value(counter)];
            let result = call_closing(machine, iterator, callback, &arguments)?;
            let truthy = machine.to_boolean(result);
            let finished = match consumer {
                Consumer::ForEach => None,
                Consumer::Some => truthy.then_some(Value::TRUE),
                Consumer::Every => (!truthy).then_some(Value::FALSE),
                Consumer::Find => truthy.then_some(value),
            };
            if let Some(answer) = finished {
                close_iterator(machine, iterator, Ok(()))?;
                return Ok(answer);
            }
            counter += 1.0;
        }
    })
    .map(BuiltinOutcome::Value)
}

fn for_each<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    consume(machine, this, args, Consumer::ForEach)
}

fn some<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    consume(machine, this, args, Consumer::Some)
}

fn every<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    consume(machine, this, args, Consumer::Every)
}

fn find<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    consume(machine, this, args, Consumer::Find)
}

fn reduce<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let reducer = argument(args, 0);
    checked_callback(machine, this, reducer)?;
    let (iterator, next) = direct_record(machine, this)?;
    with_roots(machine, &[iterator, next, reducer], |machine, depth| {
        let (mut accumulator, mut counter) = match args.get(1) {
            Some(initial) => (*initial, 0.0),
            None => match step_value(machine, iterator, next)? {
                Some(first) => (first, 1.0),
                None => {
                    return Err(type_error(
                        "Iterator.prototype.reduce of an empty iterator with no initial value",
                    ));
                }
            },
        };
        machine.refresh_native_roots(depth, &[iterator, next, reducer, accumulator]);
        while let Some(value) = step_value(machine, iterator, next)? {
            let arguments = [accumulator, value, crate::number_value(counter)];
            accumulator = call_closing(machine, iterator, reducer, &arguments)?;
            machine.refresh_native_roots(depth, &[iterator, next, reducer, accumulator]);
            counter += 1.0;
        }
        Ok(accumulator)
    })
    .map(BuiltinOutcome::Value)
}

/// `Iterator.prototype[@@dispose]`.
fn dispose<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    call_return(machine, this)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

/// `new Iterator()` is abstract: only a subclass may construct it.
fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let new_target = machine.current_new_target();
    let active = machine
        .intrinsics
        .global("Iterator")
        .expect("Iterator is installed");
    if new_target == Value::UNDEFINED || new_target == active {
        return Err(type_error("Iterator is an abstract class"));
    }
    let candidate = machine.get_named_property(new_target, "prototype")?;
    let prototype = if machine.is_object(candidate) {
        candidate
    } else {
        machine.intrinsics.builtins.iterator_prototype()
    };
    machine
        .allocate_constructed_receiver_with(prototype)
        .map(BuiltinOutcome::Value)
        .map_err(EvalFailure::Runtime)
}

/// `Iterator.from`: an iterator that already inherits from `Iterator.prototype`
/// comes back as it is, and anything else gets a wrapper with the helpers.
fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (iterator, next) = flattenable(machine, argument(args, 0), true)?;
    let active = machine
        .intrinsics
        .global("Iterator")
        .expect("Iterator is installed");
    let inherits = with_roots(machine, &[iterator, next], |machine, _| {
        machine.ordinary_has_instance(iterator, active)
    })?;
    if inherits {
        return Ok(BuiltinOutcome::Value(iterator));
    }
    let source = hidden_array(machine, vec![iterator, next])?;
    machine
        .allocate(HeapEntry::BuiltinIterator {
            source,
            kind: IterationKind::WrapForValid,
            position: Some(0),
            properties: PropertyMap::default(),
            prototype: Some(
                machine
                    .intrinsics
                    .builtins
                    .wrap_for_valid_iterator_prototype(),
            ),
            extensible: true,
        })
        .map(BuiltinOutcome::Value)
        .map_err(EvalFailure::Runtime)
}

fn wrapped_record<H: Host>(
    machine: &Machine<'_, H>,
    this: Value,
) -> Result<(Value, Value), EvalFailure> {
    let index = machine.runtime_slot(this).map_err(EvalFailure::Runtime)?;
    let Some(HeapEntry::BuiltinIterator {
        source,
        kind: IterationKind::WrapForValid,
        ..
    }) = index.map(|index| &machine.heap[index])
    else {
        return Err(type_error(
            "%WrapForValidIteratorPrototype% method on incompatible receiver",
        ));
    };
    Ok((slot(machine, *source, 0), slot(machine, *source, 1)))
}

fn wrap_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (iterator, next) = wrapped_record(machine, this)?;
    machine
        .call_value(next, iterator, &[])
        .map(BuiltinOutcome::Value)
}

fn wrap_return<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (iterator, _) = wrapped_record(machine, this)?;
    match call_return(machine, iterator)? {
        Some(result) => Ok(BuiltinOutcome::Value(result)),
        None => iterator_result(machine, Value::UNDEFINED, true),
    }
}

/// `Iterator.concat`: every argument is checked before anything is opened.
fn concat<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    with_roots(machine, args, |machine, depth| {
        let mut list = Vec::with_capacity(args.len() * 2);
        for &item in args {
            require_object(machine, item, "Iterator.concat requires objects")?;
            let Some(method) = iterator_method(machine, item)? else {
                return Err(type_error("Iterator.concat requires iterables"));
            };
            keep_root(machine, depth, method);
            list.extend([method, item]);
        }
        let list = hidden_array(machine, list)?;
        new_helper(machine, Operation::Concat, &[(LIST, list)])
    })
    .map(BuiltinOutcome::Value)
}

/// `GetOptionsObject`, then the `mode` and `padding` options shared by the zips.
fn zip_options<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Value,
) -> Result<(ZipMode, Value), EvalFailure> {
    if options == Value::UNDEFINED {
        return Ok((ZipMode::Shortest, Value::UNDEFINED));
    }
    require_object(machine, options, "Iterator.zip options must be an object")?;
    let mode = machine.get_named_property(options, "mode")?;
    let mode = if mode == Value::UNDEFINED {
        ZipMode::Shortest
    } else {
        match machine.string_value(mode) {
            Some(text) if text.eq_ascii("shortest") => ZipMode::Shortest,
            Some(text) if text.eq_ascii("longest") => ZipMode::Longest,
            Some(text) if text.eq_ascii("strict") => ZipMode::Strict,
            _ => return Err(type_error("Iterator.zip mode is not recognized")),
        }
    };
    if mode != ZipMode::Longest {
        return Ok((mode, Value::UNDEFINED));
    }
    let padding = machine.get_named_property(options, "padding")?;
    if padding != Value::UNDEFINED && !machine.is_object(padding) {
        return Err(type_error("Iterator.zip padding must be an object"));
    }
    Ok((mode, padding))
}

fn new_zip<H: Host>(
    machine: &mut Machine<'_, H>,
    operation: Operation,
    mode: ZipMode,
    iterators: Vec<Value>,
    padding: Vec<Value>,
    keys: Vec<Value>,
) -> Result<Value, EvalFailure> {
    let list = hidden_array(machine, iterators)?;
    let padding = hidden_array(machine, padding)?;
    let keys = hidden_array(machine, keys)?;
    let mode = Value::int32(match mode {
        ZipMode::Shortest => 0,
        ZipMode::Longest => 1,
        ZipMode::Strict => 2,
    });
    new_helper(
        machine,
        operation,
        &[(LIST, list), (PADDING, padding), (KEYS, keys), (MODE, mode)],
    )
}

/// Reads the padding iterable for `Iterator.zip`'s longest mode. A short one pads
/// with `undefined`, and one that still has values left is closed.
fn zip_padding<H: Host>(
    machine: &mut Machine<'_, H>,
    depth: usize,
    padding_option: Value,
    count: usize,
) -> Result<Vec<Value>, EvalFailure> {
    if padding_option == Value::UNDEFINED {
        return Ok(vec![Value::UNDEFINED; count]);
    }
    let (iterator, next) = get_iterator(machine, padding_option)?;
    keep_root(machine, depth, iterator);
    keep_root(machine, depth, next);
    let mut padding = Vec::with_capacity(count);
    let mut exhausted = false;
    for _ in 0..count {
        let value = if exhausted {
            None
        } else {
            step_value(machine, iterator, next)?
        };
        exhausted = value.is_none();
        let value = value.unwrap_or(Value::UNDEFINED);
        keep_root(machine, depth, value);
        padding.push(value);
    }
    if !exhausted {
        close_iterator(machine, iterator, Ok(()))?;
    }
    Ok(padding)
}

fn close_on_failure<H: Host, T>(
    machine: &mut Machine<'_, H>,
    iterators: &[Value],
    result: Result<T, EvalFailure>,
) -> Result<T, EvalFailure> {
    match result {
        Ok(value) => Ok(value),
        Err(failure) => {
            close_list(machine, iterators, Err(failure))?;
            unreachable!("closing with a failure returns that failure")
        }
    }
}

/// `Iterator.zip(iterables, options)`.
fn zip<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (iterables, options) = (argument(args, 0), argument(args, 1));
    require_object(machine, iterables, "Iterator.zip requires an object")?;
    with_roots(machine, &[iterables, options], |machine, depth| {
        let (mode, padding_option) = zip_options(machine, options)?;
        keep_root(machine, depth, padding_option);
        let (input, input_next) = get_iterator(machine, iterables)?;
        keep_root(machine, depth, input);
        keep_root(machine, depth, input_next);
        let mut iterators = Vec::new();
        loop {
            let stepped = step_value(machine, input, input_next);
            let Some(value) = close_on_failure(machine, &iterators, stepped)? else {
                break;
            };
            keep_root(machine, depth, value);
            match flattenable(machine, value, false) {
                Ok((iterator, next)) => {
                    keep_root(machine, depth, iterator);
                    keep_root(machine, depth, next);
                    iterators.extend([iterator, next]);
                }
                Err(failure) => {
                    let failure = match close_list(machine, &iterators, Err(failure)) {
                        Err(failure) => failure,
                        Ok(()) => unreachable!("closing with a failure returns that failure"),
                    };
                    return Err(close_after(machine, input, failure));
                }
            }
        }
        let count = iterators.len() / 2;
        let padding = if mode == ZipMode::Longest {
            let read = zip_padding(machine, depth, padding_option, count);
            close_on_failure(machine, &iterators, read)?
        } else {
            vec![Value::UNDEFINED; count]
        };
        new_zip(
            machine,
            Operation::Zip,
            mode,
            iterators,
            padding,
            Vec::new(),
        )
    })
    .map(BuiltinOutcome::Value)
}

fn key_value<H: Host>(
    machine: &mut Machine<'_, H>,
    key: &PropertyKey,
) -> Result<Value, EvalFailure> {
    match key {
        PropertyKey::Named(name) => {
            let text = machine.atoms.resolve(*name).clone();
            allocate_string(machine, text)
        }
        PropertyKey::Symbol(index) | PropertyKey::Private(index) => Ok(Value::heap_ref(
            bamts_native::SlotId::from_parts(crate::RUNTIME_HEAP_SEGMENT, index + 1)
                .expect("property-key heap slots are nonzero"),
        )),
    }
}

/// `Iterator.zipKeyed(iterables, options)`: `iterables` is read by own enumerable
/// key, and each result object is keyed the same way.
fn zip_keyed<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (iterables, options) = (argument(args, 0), argument(args, 1));
    require_object(machine, iterables, "Iterator.zipKeyed requires an object")?;
    with_roots(machine, &[iterables, options], |machine, depth| {
        let (mode, padding_option) = zip_options(machine, options)?;
        keep_root(machine, depth, padding_option);
        let all_keys = machine.internal_own_property_keys(iterables)?;
        let mut iterators = Vec::new();
        let mut keys = Vec::new();
        let mut key_values = Vec::new();
        for key in all_keys {
            let descriptor = machine.internal_get_own_property(iterables, &key);
            let descriptor = close_on_failure(machine, &iterators, descriptor)?;
            if !descriptor.is_some_and(|descriptor| descriptor.enumerable == Some(true)) {
                continue;
            }
            let value = machine.get_property_key(iterables, &key);
            let value = close_on_failure(machine, &iterators, value)?;
            if value == Value::UNDEFINED {
                continue;
            }
            keep_root(machine, depth, value);
            let key_handle = key_value(machine, &key)?;
            keep_root(machine, depth, key_handle);
            let record = flattenable(machine, value, false);
            let (iterator, next) = close_on_failure(machine, &iterators, record)?;
            keep_root(machine, depth, iterator);
            keep_root(machine, depth, next);
            iterators.extend([iterator, next]);
            key_values.push(key_handle);
            keys.push(key);
        }
        let mut padding = Vec::with_capacity(keys.len());
        for key in &keys {
            let value = if mode == ZipMode::Longest && padding_option != Value::UNDEFINED {
                let read = machine.get_property_key(padding_option, key);
                close_on_failure(machine, &iterators, read)?
            } else {
                Value::UNDEFINED
            };
            keep_root(machine, depth, value);
            padding.push(value);
        }
        new_zip(
            machine,
            Operation::ZipKeyed,
            mode,
            iterators,
            padding,
            key_values,
        )
    })
    .map(BuiltinOutcome::Value)
}

/// `SetterThatIgnoresPrototypeProperties`: a write through an inheriting object
/// defines an own property instead of failing on the accessor it found.
fn set_ignoring_prototype<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    key: PropertyKey,
    value: Value,
) -> Result<(), EvalFailure> {
    require_object(
        machine,
        this,
        "Iterator.prototype setter requires an object",
    )?;
    if this == machine.intrinsics.builtins.iterator_prototype() {
        return Err(type_error("Iterator.prototype property cannot be assigned"));
    }
    if machine.internal_get_own_property(this, &key)?.is_some() {
        return machine.set_data_property_key(this, key, value);
    }
    let descriptor = descriptor_from_property(Property::Data {
        value,
        writable: true,
        enumerable: true,
        configurable: true,
    });
    if machine.internal_define_own_property(this, key, descriptor)? {
        Ok(())
    } else {
        Err(type_error("Cannot define property"))
    }
}

fn constructor_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(
        machine
            .intrinsics
            .global("Iterator")
            .expect("Iterator is installed"),
    ))
}

fn constructor_setter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let key = PropertyKey::Named(machine.intern_str("constructor"));
    set_ignoring_prototype(machine, this, key, argument(args, 0))?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn tag_getter<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    allocate_string(machine, EcmaString::encode("Iterator")).map(BuiltinOutcome::Value)
}

fn tag_setter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let key =
        machine.property_key_from_value(machine.intrinsics.builtins.symbol_to_string_tag())?;
    set_ignoring_prototype(machine, this, key, argument(args, 0))?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn accessor(getter: Value, setter: Value) -> Property {
    Property::Accessor {
        getter: Some(getter),
        setter: Some(setter),
        enumerable: false,
        configurable: true,
    }
}

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.iterator_prototype();
    let constructor_function =
        install_constructor_function(heap, atoms, builtins, "Iterator", 0, constructor::<H>);
    define_frozen_data(heap, atoms, constructor_function, "prototype", prototype);
    globals.insert(EcmaString::encode("Iterator"), constructor_function);
    for (name, length, handler) in [
        ("from", 1, from::<H> as BuiltinHandler<H>),
        ("concat", 0, concat::<H>),
        ("zip", 1, zip::<H>),
        ("zipKeyed", 1, zip_keyed::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, constructor_function, name, function);
    }
    for (name, length, handler) in [
        ("map", 1, map::<H> as BuiltinHandler<H>),
        ("filter", 1, filter::<H>),
        ("take", 1, take::<H>),
        ("drop", 1, drop::<H>),
        ("flatMap", 1, flat_map::<H>),
        ("reduce", 1, reduce::<H>),
        ("toArray", 0, to_array::<H>),
        ("forEach", 1, for_each::<H>),
        ("some", 1, some::<H>),
        ("every", 1, every::<H>),
        ("find", 1, find::<H>),
    ] {
        let function = install_function(heap, atoms, builtins, name, length, handler);
        define_data(heap, atoms, prototype, name, function);
    }
    let dispose_function =
        install_function(heap, atoms, builtins, "[Symbol.dispose]", 0, dispose::<H>);
    define_symbol_property(
        heap,
        prototype,
        builtins.symbol_dispose(),
        super::builtin_property(dispose_function),
    );
    let get_constructor = install_function(
        heap,
        atoms,
        builtins,
        "get constructor",
        0,
        constructor_getter::<H>,
    );
    let set_constructor = install_function(
        heap,
        atoms,
        builtins,
        "set constructor",
        1,
        constructor_setter::<H>,
    );
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        panic!("%Iterator.prototype% is an ordinary object");
    };
    properties.insert(
        PropertyKey::Named(atoms.intern(EcmaString::encode("constructor"))),
        accessor(get_constructor, set_constructor),
    );
    let get_tag = install_function(
        heap,
        atoms,
        builtins,
        "get [Symbol.toStringTag]",
        0,
        tag_getter::<H>,
    );
    let set_tag = install_function(
        heap,
        atoms,
        builtins,
        "set [Symbol.toStringTag]",
        1,
        tag_setter::<H>,
    );
    define_symbol_property(
        heap,
        prototype,
        builtins.symbol_to_string_tag(),
        accessor(get_tag, set_tag),
    );

    let helper_prototype = super::collections::ordinary_intrinsic(heap, prototype);
    let next = install_function(heap, atoms, builtins, "next", 0, helper_next::<H>);
    define_data(heap, atoms, helper_prototype, "next", next);
    let return_method = install_function(heap, atoms, builtins, "return", 0, helper_return::<H>);
    define_data(heap, atoms, helper_prototype, "return", return_method);
    super::define_to_string_tag(
        heap,
        helper_prototype,
        builtins.symbol_to_string_tag(),
        "Iterator Helper",
    );
    let wrap_prototype = super::collections::ordinary_intrinsic(heap, prototype);
    let next = install_function(heap, atoms, builtins, "next", 0, wrap_next::<H>);
    define_data(heap, atoms, wrap_prototype, "next", next);
    let return_method = install_function(heap, atoms, builtins, "return", 0, wrap_return::<H>);
    define_data(heap, atoms, wrap_prototype, "return", return_method);
    builtins.set_iterator_helper_prototypes(helper_prototype, wrap_prototype);
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, ThrowOrigin};

    fn is_type_error<T>(result: Result<T, EvalFailure>) -> bool {
        matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        )
    }

    fn invoke(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let method = machine.get_named_property(receiver, name)?;
        machine.call_value(method, receiver, args)
    }

    fn numbers(machine: &mut Machine<'_, TestHost>, values: &[i32]) -> Value {
        let elements = values.iter().map(|value| Value::int32(*value as u32));
        let array = allocate_array(machine, elements.collect()).unwrap();
        invoke(machine, array, "values", &[]).unwrap()
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 1,
            handler,
        });
        native_function(&mut machine.heap, &mut machine.atoms, id, name, 1)
    }

    fn collected(machine: &mut Machine<'_, TestHost>, iterator: Value) -> Vec<Value> {
        let array = invoke(machine, iterator, "toArray", &[]).unwrap();
        machine.array_elements(array).unwrap().unwrap()
    }

    fn double(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let value = value_number(machine.to_number(args[0])?);
        Ok(BuiltinOutcome::Value(crate::number_value(value * 2.0)))
    }

    fn is_even(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let value = value_number(machine.to_number(args[0])?);
        Ok(BuiltinOutcome::Value(Value::boolean(value % 2.0 == 0.0)))
    }

    /// `next` of an object whose `helper` property is the helper consuming it.
    fn reenter(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let helper = machine.get_named_property(this, "helper")?;
        let result = invoke(machine, helper, "next", &[]);
        assert!(is_type_error(result), "a running helper rejects next");
        Ok(BuiltinOutcome::Value(
            machine.iterator_result(Value::UNDEFINED, true)?,
        ))
    }

    fn record_return(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "closed", Value::TRUE)?;
        Ok(BuiltinOutcome::Value(this))
    }

    #[test]
    fn iterator_is_abstract_and_only_a_subclass_constructs_it() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let iterator = machine.intrinsics.global("Iterator").unwrap();
        assert!(is_type_error(machine.construct_value(iterator, &[])));
        assert!(is_type_error(machine.call_value(
            iterator,
            Value::UNDEFINED,
            &[]
        )));
        let subclass_prototype = ordinary_object(&mut machine);
        let subclass = ordinary_object(&mut machine);
        machine
            .set_data_property(subclass, "prototype", subclass_prototype)
            .unwrap();
        let instance = machine.internal_construct(iterator, &[], subclass).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(instance).unwrap(),
            Some(subclass_prototype)
        );
    }

    #[test]
    fn helpers_compose_and_produce_nothing_until_asked() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = numbers(&mut machine, &[1, 2, 3, 4, 5, 6]);
        let predicate = native(&mut machine, "is even", is_even);
        let filtered = invoke(&mut machine, source, "filter", &[predicate]).unwrap();
        let mapper = native(&mut machine, "double", double);
        let mapped = invoke(&mut machine, filtered, "map", &[mapper]).unwrap();
        let dropped = invoke(&mut machine, mapped, "drop", &[Value::int32(1)]).unwrap();
        let taken = invoke(&mut machine, dropped, "take", &[Value::int32(1)]).unwrap();
        assert_eq!(collected(&mut machine, taken), [Value::int32(8)]);
    }

    #[test]
    fn a_running_helper_rejects_reentry() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let prototype = machine.intrinsics.builtins.iterator_prototype();
        let underlying = ordinary_object(&mut machine);
        machine
            .internal_set_prototype_of(underlying, Some(prototype))
            .unwrap();
        let next = native(&mut machine, "reenter", reenter);
        machine.set_data_property(underlying, "next", next).unwrap();
        let mapper = native(&mut machine, "double", double);
        let helper = invoke(&mut machine, underlying, "map", &[mapper]).unwrap();
        machine
            .set_data_property(underlying, "helper", helper)
            .unwrap();
        let result = invoke(&mut machine, helper, "next", &[]).unwrap();
        assert_eq!(
            machine.get_named_property(result, "done").unwrap(),
            Value::TRUE
        );
    }

    #[test]
    fn return_closes_the_underlying_iterator_once() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let prototype = machine.intrinsics.builtins.iterator_prototype();
        let underlying = ordinary_object(&mut machine);
        machine
            .internal_set_prototype_of(underlying, Some(prototype))
            .unwrap();
        let close = native(&mut machine, "record return", record_return);
        machine
            .set_data_property(underlying, "return", close)
            .unwrap();
        let mapper = native(&mut machine, "double", double);
        let helper = invoke(&mut machine, underlying, "map", &[mapper]).unwrap();
        invoke(&mut machine, helper, "return", &[]).unwrap();
        assert_eq!(
            machine.get_named_property(underlying, "closed").unwrap(),
            Value::TRUE
        );
        machine
            .set_data_property(underlying, "closed", Value::FALSE)
            .unwrap();
        invoke(&mut machine, helper, "return", &[]).unwrap();
        assert_eq!(
            machine.get_named_property(underlying, "closed").unwrap(),
            Value::FALSE,
            "a completed helper does not close again"
        );
    }

    #[test]
    fn a_bad_argument_closes_the_receiver_before_reading_next() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let prototype = machine.intrinsics.builtins.iterator_prototype();
        let underlying = ordinary_object(&mut machine);
        machine
            .internal_set_prototype_of(underlying, Some(prototype))
            .unwrap();
        let close = native(&mut machine, "record return", record_return);
        machine
            .set_data_property(underlying, "return", close)
            .unwrap();
        assert!(is_type_error(invoke(
            &mut machine,
            underlying,
            "map",
            &[Value::int32(1)]
        )));
        assert_eq!(
            machine.get_named_property(underlying, "closed").unwrap(),
            Value::TRUE
        );
    }

    #[test]
    fn zip_stops_at_the_shortest_and_pads_to_the_longest() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let iterator = machine.intrinsics.global("Iterator").unwrap();
        let (one, two) = (numbers(&mut machine, &[1]), numbers(&mut machine, &[2, 3]));
        let inputs = allocate_array(&mut machine, vec![one, two]).unwrap();
        let zipped = invoke(&mut machine, iterator, "zip", &[inputs]).unwrap();
        assert_eq!(collected(&mut machine, zipped).len(), 1);

        let (one, two) = (numbers(&mut machine, &[1]), numbers(&mut machine, &[2, 3]));
        let inputs = allocate_array(&mut machine, vec![one, two]).unwrap();
        let options = ordinary_object(&mut machine);
        let longest = allocate_string(&mut machine, EcmaString::encode("longest")).unwrap();
        machine.set_data_property(options, "mode", longest).unwrap();
        let zipped = invoke(&mut machine, iterator, "zip", &[inputs, options]).unwrap();
        let rows = collected(&mut machine, zipped);
        assert_eq!(rows.len(), 2);
        assert_eq!(
            machine.array_elements(rows[1]).unwrap().unwrap(),
            [Value::UNDEFINED, Value::int32(3)]
        );
    }
}
