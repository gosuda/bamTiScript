//! The generic `Array.prototype` algorithms.
//!
//! These methods work on any object with a length, and each step is observable:
//! `length` is read once, then every element goes through `HasProperty`, `Get`
//! and `Set`, so callbacks and proxies see them in specification order.
//!
//! Stringifying an index for every step would dominate on a plain array, so the
//! element accessors below take a shortcut when it is unobservable. A non-hole
//! entry in `elements` is always a plain writable data property, because
//! `define_descriptor` moves any other kind of index into `properties` and leaves
//! a hole behind. Holes take the full path, which reaches the prototype chain.

use std::cmp::Ordering;

use bamts_bytecode::{EcmaString, EcmaStringBuilder};
use bamts_native::{Decoded, Value};

use super::array_es2023::{
    array_create, create_data_property, index_key, integer_or_infinity, length_of_array_like,
    to_object,
};
use super::property_descriptor::descriptor_from_property;
use super::{allocate_string, keep_root, range_error, type_error, value_number, with_roots};
use crate::intrinsics::BuiltinOutcome;
use crate::{EvalFailure, HeapEntry, Host, Machine, Property};

const MAX_SAFE_INTEGER: usize = 9_007_199_254_740_991;
/// How deeply `flat` follows nested arrays before treating the input as cyclic.
const MAX_FLATTEN_DEPTH: usize = 4096;

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

/// Charges one step, so a claimed length of 2^53 - 1 ends in fuel exhaustion
/// rather than a loop nothing can interrupt.
pub(super) fn tick<H: Host>(machine: &mut Machine<'_, H>) -> Result<(), EvalFailure> {
    machine.consume_fuel(1).map_err(EvalFailure::Runtime)
}

fn dense_element<H: Host>(machine: &Machine<'_, H>, object: Value, index: usize) -> Option<Value> {
    let slot = machine.runtime_slot(object).ok().flatten()?;
    let HeapEntry::Array { elements, .. } = &machine.heap[slot] else {
        return None;
    };
    elements
        .get(index)
        .copied()
        .filter(|element| *element != Value::HOLE)
}

fn has_index<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    index: usize,
) -> Result<bool, EvalFailure> {
    if dense_element(machine, object, index).is_some() {
        return Ok(true);
    }
    let key = index_key(&mut machine.atoms, index);
    machine.internal_has_property(object, &key)
}

fn get_index<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    index: usize,
) -> Result<Value, EvalFailure> {
    if let Some(value) = dense_element(machine, object, index) {
        return Ok(value);
    }
    let key = index_key(&mut machine.atoms, index);
    machine.get_property_key(object, &key)
}

fn set_index<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    index: usize,
    value: Value,
) -> Result<(), EvalFailure> {
    if dense_element(machine, object, index).is_some() {
        let slot = machine
            .runtime_slot(object)
            .map_err(EvalFailure::Runtime)?
            .expect("a dense element belongs to a runtime array");
        if let HeapEntry::Array { elements, .. } = &mut machine.heap[slot] {
            elements[index] = value;
        }
        return Ok(());
    }
    let key = index_key(&mut machine.atoms, index);
    machine.set_data_property_key(object, key, value)
}

fn delete_index<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    index: usize,
) -> Result<(), EvalFailure> {
    let key = index_key(&mut machine.atoms, index);
    if machine.internal_delete(object, &key)? {
        Ok(())
    } else {
        Err(type_error("Cannot delete array element"))
    }
}

/// `CreateDataPropertyOrThrow`. A species can construct anything, proxies
/// included, so only a real Array takes the direct path.
fn create_index<H: Host>(
    machine: &mut Machine<'_, H>,
    target: Value,
    index: usize,
    value: Value,
) -> Result<(), EvalFailure> {
    if machine.array_len(target)?.is_some() {
        return create_data_property(machine, target, index, value);
    }
    let descriptor = descriptor_from_property(Property::Data {
        value,
        writable: true,
        enumerable: true,
        configurable: true,
    });
    let key = index_key(&mut machine.atoms, index);
    if machine.internal_define_own_property(target, key, descriptor)? {
        Ok(())
    } else {
        Err(type_error("Cannot define array element"))
    }
}

fn set_length<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    length: usize,
) -> Result<(), EvalFailure> {
    machine.set_data_property(object, "length", crate::number_value(length as f64))
}

/// `IsArray`, which sees through proxies and throws on a revoked one.
pub(crate) fn is_array<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    let mut current = value;
    loop {
        let index = machine
            .runtime_slot(current)
            .map_err(EvalFailure::Runtime)?;
        match index.map(|index| &machine.heap[index]) {
            Some(HeapEntry::Array { .. }) => return Ok(true),
            Some(HeapEntry::Proxy { record }) => match record.live_target() {
                Some(target) => current = target,
                None => return Err(type_error("IsArray on a revoked proxy")),
            },
            _ => return Ok(false),
        }
    }
}

/// `ArraySpeciesCreate`.
fn array_species_create<H: Host>(
    machine: &mut Machine<'_, H>,
    original: Value,
    length: usize,
) -> Result<Value, EvalFailure> {
    if !is_array(machine, original)? {
        return array_create(machine, length);
    }
    let mut constructor = machine.get_named_property(original, "constructor")?;
    if machine.is_object(constructor) {
        let key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_species())?;
        constructor = machine.get_property_key(constructor, &key)?;
        if constructor == Value::NULL {
            constructor = Value::UNDEFINED;
        }
    }
    if constructor == Value::UNDEFINED {
        return array_create(machine, length);
    }
    if !machine.is_constructor(constructor)? {
        return Err(type_error("Array species is not a constructor"));
    }
    machine.construct_value(constructor, &[crate::number_value(length as f64)])
}

fn require_callable<H: Host>(machine: &Machine<'_, H>, callback: Value) -> Result<(), EvalFailure> {
    if machine.is_callable(callback)? {
        Ok(())
    } else {
        Err(type_error("Array callback is not callable"))
    }
}

/// The clamped position a relative argument names, with user conversion running
/// in specification order.
pub(super) fn relative_position<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
    length: usize,
) -> Result<usize, EvalFailure> {
    let relative = integer_or_infinity(machine, value)?;
    let length = length as f64;
    Ok(if relative < 0.0 {
        (length + relative).max(0.0) as usize
    } else {
        relative.min(length) as usize
    })
}

pub(super) fn push<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, _| {
        let mut length = length_of_array_like(machine, object)?;
        if length.saturating_add(args.len()) > MAX_SAFE_INTEGER {
            return Err(type_error("Array length exceeds the safe integer limit"));
        }
        for &value in args {
            let key = index_key(&mut machine.atoms, length);
            machine.set_data_property_key(object, key, value)?;
            length += 1;
        }
        set_length(machine, object, length)?;
        Ok(crate::number_value(length as f64))
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn pop<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        if length == 0 {
            set_length(machine, object, 0)?;
            return Ok(Value::UNDEFINED);
        }
        let index = length - 1;
        let element = get_index(machine, object, index)?;
        keep_root(machine, depth, element);
        delete_index(machine, object, index)?;
        set_length(machine, object, index)?;
        Ok(element)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn shift<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        if length == 0 {
            set_length(machine, object, 0)?;
            return Ok(Value::UNDEFINED);
        }
        let first = get_index(machine, object, 0)?;
        keep_root(machine, depth, first);
        for from in 1..length {
            tick(machine)?;
            move_element(machine, object, from, from - 1)?;
        }
        delete_index(machine, object, length - 1)?;
        set_length(machine, object, length - 1)?;
        Ok(first)
    })
    .map(BuiltinOutcome::Value)
}

/// One step of a shifting loop: the destination takes the source's value, or is
/// deleted when the source is absent.
fn move_element<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    from: usize,
    to: usize,
) -> Result<(), EvalFailure> {
    if has_index(machine, object, from)? {
        let value = get_index(machine, object, from)?;
        set_index(machine, object, to, value)
    } else {
        delete_index(machine, object, to)
    }
}

pub(super) fn unshift<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        let count = args.len();
        if count > 0 {
            if length.saturating_add(count) > MAX_SAFE_INTEGER {
                return Err(type_error("Array length exceeds the safe integer limit"));
            }
            for index in (0..length).rev() {
                tick(machine)?;
                move_element(machine, object, index, index + count)?;
            }
            for (index, &value) in args.iter().enumerate() {
                set_index(machine, object, index, value)?;
            }
        }
        set_length(machine, object, length + count)?;
        Ok(crate::number_value((length + count) as f64))
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn slice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        let start = relative_position(machine, argument(args, 0), length)?;
        let end = match argument(args, 1) {
            Value::UNDEFINED => length,
            end => relative_position(machine, end, length)?,
        };
        let count = end.saturating_sub(start);
        let target = array_species_create(machine, object, count)?;
        keep_root(machine, depth, target);
        let mut to = 0;
        for from in start..end {
            tick(machine)?;
            if has_index(machine, object, from)? {
                let value = get_index(machine, object, from)?;
                create_index(machine, target, to, value)?;
            }
            to += 1;
        }
        set_length(machine, target, to)?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn splice<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        let start = relative_position(machine, argument(args, 0), length)?;
        let items = args.get(2..).unwrap_or_default();
        let delete_count = match args.len() {
            0 => 0,
            1 => length - start,
            _ => {
                let requested = integer_or_infinity(machine, args[1])?;
                requested.clamp(0.0, (length - start) as f64) as usize
            }
        };
        if (length + items.len()).saturating_sub(delete_count) > MAX_SAFE_INTEGER {
            return Err(type_error("Array length exceeds the safe integer limit"));
        }
        let removed = array_species_create(machine, object, delete_count)?;
        keep_root(machine, depth, removed);
        for offset in 0..delete_count {
            tick(machine)?;
            let from = start + offset;
            if has_index(machine, object, from)? {
                let value = get_index(machine, object, from)?;
                create_index(machine, removed, offset, value)?;
            }
        }
        set_length(machine, removed, delete_count)?;
        let new_length = length - delete_count + items.len();
        if items.len() < delete_count {
            for index in start..length - delete_count {
                tick(machine)?;
                move_element(machine, object, index + delete_count, index + items.len())?;
            }
            for index in (new_length..length).rev() {
                tick(machine)?;
                delete_index(machine, object, index)?;
            }
        } else if items.len() > delete_count {
            for index in (start..length - delete_count).rev() {
                tick(machine)?;
                move_element(machine, object, index + delete_count, index + items.len())?;
            }
        }
        for (offset, &value) in items.iter().enumerate() {
            set_index(machine, object, start + offset, value)?;
        }
        set_length(machine, object, new_length)?;
        Ok(removed)
    })
    .map(BuiltinOutcome::Value)
}

/// `IsConcatSpreadable`: the symbol wins, and an array spreads by default.
fn is_concat_spreadable<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<bool, EvalFailure> {
    if !machine.is_object(value) {
        return Ok(false);
    }
    let symbol = machine.intrinsics.builtins.symbol_is_concat_spreadable();
    let key = machine.property_key_from_value(symbol)?;
    let spreadable = machine.get_property_key(value, &key)?;
    if spreadable != Value::UNDEFINED {
        return Ok(machine.to_boolean(spreadable));
    }
    is_array(machine, value)
}

pub(super) fn concat<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let target = array_species_create(machine, object, 0)?;
        keep_root(machine, depth, target);
        let mut to: usize = 0;
        for item in std::iter::once(object).chain(args.iter().copied()) {
            if is_concat_spreadable(machine, item)? {
                let length = length_of_array_like(machine, item)?;
                if to.saturating_add(length) > MAX_SAFE_INTEGER {
                    return Err(type_error("Array length exceeds the safe integer limit"));
                }
                for from in 0..length {
                    tick(machine)?;
                    if has_index(machine, item, from)? {
                        let value = get_index(machine, item, from)?;
                        create_index(machine, target, to, value)?;
                    }
                    to += 1;
                }
            } else {
                if to >= MAX_SAFE_INTEGER {
                    return Err(type_error("Array length exceeds the safe integer limit"));
                }
                create_index(machine, target, to, item)?;
                to += 1;
            }
        }
        set_length(machine, target, to)?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

fn append(output: &mut EcmaStringBuilder, text: &EcmaString) {
    for &unit in text.as_units() {
        output.push_unit(unit);
    }
}

/// Runs a join over `object`, which an array reached again through its own
/// elements contributes nothing to. Nothing else stops that recursion: it passes
/// through native code, so no activation limit applies.
pub(super) fn guarded_join<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    body: impl FnOnce(&mut Machine<'_, H>) -> Result<EcmaString, EvalFailure>,
) -> Result<EcmaString, EvalFailure> {
    if machine.array_join_stack.contains(&object) {
        return Ok(EcmaString::default());
    }
    machine.array_join_stack.push(object);
    let result = body(machine);
    machine.array_join_stack.pop();
    result
}

pub(super) fn join<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let joined = with_roots(machine, &[object], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        let separator = match argument(args, 0) {
            Value::UNDEFINED => EcmaString::encode(","),
            separator => machine.coerce_string_observable(separator)?,
        };
        guarded_join(machine, object, |machine| {
            let mut output = EcmaStringBuilder::new();
            for index in 0..length {
                tick(machine)?;
                if index != 0 {
                    append(&mut output, &separator);
                }
                let element = get_index(machine, object, index)?;
                if !matches!(element.decode(), Some(Decoded::Undefined | Decoded::Null)) {
                    append(&mut output, &machine.coerce_string_observable(element)?);
                }
            }
            Ok(output.finish())
        })
    })?;
    Ok(BuiltinOutcome::Value(allocate_string(machine, joined)?))
}

/// The first position `fromIndex` selects, or `None` when it is past the end.
fn start_index<H: Host>(
    machine: &mut Machine<'_, H>,
    from_index: Value,
    length: usize,
) -> Result<Option<usize>, EvalFailure> {
    let relative = integer_or_infinity(machine, from_index)?;
    if relative == f64::INFINITY {
        return Ok(None);
    }
    Ok(Some(if relative >= 0.0 {
        relative as usize
    } else {
        (length as f64 + relative).max(0.0) as usize
    }))
}

pub(super) fn index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let needle = argument(args, 0);
    with_roots(machine, &[object, needle], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        if length == 0 {
            return Ok(-1.0);
        }
        let Some(start) = start_index(machine, argument(args, 1), length)? else {
            return Ok(-1.0);
        };
        for index in start..length {
            tick(machine)?;
            if has_index(machine, object, index)? {
                let element = get_index(machine, object, index)?;
                if machine.strict_equal(element, needle) {
                    return Ok(index as f64);
                }
            }
        }
        Ok(-1.0)
    })
    .map(|found| BuiltinOutcome::Value(crate::number_value(found)))
}

pub(super) fn last_index_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let needle = argument(args, 0);
    with_roots(machine, &[object, needle], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        if length == 0 {
            return Ok(-1.0);
        }
        let relative = if args.len() > 1 {
            integer_or_infinity(machine, args[1])?
        } else {
            (length - 1) as f64
        };
        let position = if relative >= 0.0 {
            relative.min((length - 1) as f64)
        } else {
            length as f64 + relative
        };
        if position < 0.0 {
            return Ok(-1.0);
        }
        let mut index = position as usize;
        loop {
            tick(machine)?;
            if has_index(machine, object, index)? {
                let element = get_index(machine, object, index)?;
                if machine.strict_equal(element, needle) {
                    return Ok(index as f64);
                }
            }
            if index == 0 {
                return Ok(-1.0);
            }
            index -= 1;
        }
    })
    .map(|found| BuiltinOutcome::Value(crate::number_value(found)))
}

pub(super) fn includes<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let needle = argument(args, 0);
    with_roots(machine, &[object, needle], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        if length == 0 {
            return Ok(false);
        }
        let Some(start) = start_index(machine, argument(args, 1), length)? else {
            return Ok(false);
        };
        for index in start..length {
            tick(machine)?;
            let element = get_index(machine, object, index)?;
            if machine.same_value_zero(element, needle) {
                return Ok(true);
            }
        }
        Ok(false)
    })
    .map(|found| BuiltinOutcome::Value(Value::boolean(found)))
}

/// Which element-wise method is running. The loop is one algorithm with a
/// different reaction to each callback result.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Iteration {
    ForEach,
    Map,
    Filter,
    Some,
    Every,
}

fn iterate<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    iteration: Iteration,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let (callback, this_arg) = (argument(args, 0), argument(args, 1));
    with_roots(machine, &[object, callback, this_arg], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        require_callable(machine, callback)?;
        let target = match iteration {
            Iteration::Map => array_species_create(machine, object, length)?,
            Iteration::Filter => array_species_create(machine, object, 0)?,
            _ => Value::UNDEFINED,
        };
        keep_root(machine, depth, target);
        let mut selected = 0;
        for index in 0..length {
            // A present element is real storage or runs user code, and its callback
            // is charged for itself. Only a gap can spin on a claimed length.
            if !has_index(machine, object, index)? {
                tick(machine)?;
                continue;
            }
            let value = get_index(machine, object, index)?;
            machine.refresh_native_roots(depth, &[object, callback, this_arg, target, value]);
            let position = crate::number_value(index as f64);
            let result = machine.call_callback(callback, this_arg, &[value, position, object])?;
            match iteration {
                Iteration::ForEach => {}
                Iteration::Map => create_index(machine, target, index, result)?,
                Iteration::Filter => {
                    if machine.to_boolean(result) {
                        create_index(machine, target, selected, value)?;
                        selected += 1;
                    }
                }
                Iteration::Some => {
                    if machine.to_boolean(result) {
                        return Ok(Value::TRUE);
                    }
                }
                Iteration::Every => {
                    if !machine.to_boolean(result) {
                        return Ok(Value::FALSE);
                    }
                }
            }
        }
        Ok(match iteration {
            Iteration::ForEach => Value::UNDEFINED,
            Iteration::Map | Iteration::Filter => target,
            Iteration::Some => Value::FALSE,
            Iteration::Every => Value::TRUE,
        })
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn for_each<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterate(machine, this, args, Iteration::ForEach)
}

pub(super) fn map<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterate(machine, this, args, Iteration::Map)
}

pub(super) fn filter<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterate(machine, this, args, Iteration::Filter)
}

pub(super) fn some<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterate(machine, this, args, Iteration::Some)
}

pub(super) fn every<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterate(machine, this, args, Iteration::Every)
}

/// `find` and `findIndex` visit holes, unlike the methods above.
fn find_from<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    want_index: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let (callback, this_arg) = (argument(args, 0), argument(args, 1));
    with_roots(machine, &[object, callback, this_arg], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        require_callable(machine, callback)?;
        for index in 0..length {
            tick(machine)?;
            let value = get_index(machine, object, index)?;
            machine.refresh_native_roots(depth, &[object, callback, this_arg, value]);
            let position = crate::number_value(index as f64);
            let result = machine.call_callback(callback, this_arg, &[value, position, object])?;
            if machine.to_boolean(result) {
                return Ok(if want_index { position } else { value });
            }
        }
        Ok(if want_index {
            crate::number_value(-1.0)
        } else {
            Value::UNDEFINED
        })
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn find<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    find_from(machine, this, args, false)
}

pub(super) fn find_index<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    find_from(machine, this, args, true)
}

fn reduce_from<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    reverse: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let callback = argument(args, 0);
    with_roots(machine, &[object, callback], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        require_callable(machine, callback)?;
        let mut indices: Box<dyn Iterator<Item = usize>> = if reverse {
            Box::new((0..length).rev())
        } else {
            Box::new(0..length)
        };
        let mut accumulator = args.get(1).copied();
        while accumulator.is_none() {
            let Some(index) = indices.next() else {
                return Err(type_error("Reduce of an empty array with no initial value"));
            };
            tick(machine)?;
            if has_index(machine, object, index)? {
                accumulator = Some(get_index(machine, object, index)?);
            }
        }
        let mut accumulator = accumulator.expect("the loop above found an initial value");
        for index in indices {
            tick(machine)?;
            machine.refresh_native_roots(depth, &[object, callback, accumulator]);
            if has_index(machine, object, index)? {
                let value = get_index(machine, object, index)?;
                let position = crate::number_value(index as f64);
                accumulator = machine.call_callback(
                    callback,
                    Value::UNDEFINED,
                    &[accumulator, value, position, object],
                )?;
            }
        }
        Ok(accumulator)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn reduce<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reduce_from(machine, this, args, false)
}

pub(super) fn reduce_right<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reduce_from(machine, this, args, true)
}

/// `SortCompare`. `undefined` sorts last without reaching the comparator.
fn sort_compare<H: Host>(
    machine: &mut Machine<'_, H>,
    comparator: Value,
    left: Value,
    right: Value,
) -> Result<Ordering, EvalFailure> {
    match (left == Value::UNDEFINED, right == Value::UNDEFINED) {
        (true, true) => return Ok(Ordering::Equal),
        (true, false) => return Ok(Ordering::Greater),
        (false, true) => return Ok(Ordering::Less),
        (false, false) => {}
    }
    if comparator != Value::UNDEFINED {
        let result = machine.call_value(comparator, Value::UNDEFINED, &[left, right])?;
        let order = value_number(machine.coerce_number_observable(result)?);
        return Ok(order.partial_cmp(&0.0).unwrap_or(Ordering::Equal));
    }
    let left = machine.coerce_string_observable(left)?;
    let right = machine.coerce_string_observable(right)?;
    Ok(left.as_units().cmp(right.as_units()))
}

/// A stable bottom-up merge sort. A user comparator can be inconsistent or throw,
/// which the standard library's sort does not tolerate.
fn merge_sort<H: Host>(
    machine: &mut Machine<'_, H>,
    mut items: Vec<Value>,
    comparator: Value,
) -> Result<Vec<Value>, EvalFailure> {
    let length = items.len();
    let mut width = 1;
    while width < length {
        let mut merged = Vec::with_capacity(length);
        for start in (0..length).step_by(width * 2) {
            let middle = (start + width).min(length);
            let end = (start + width * 2).min(length);
            let (mut left, mut right) = (start, middle);
            while left < middle && right < end {
                let order = sort_compare(machine, comparator, items[left], items[right])?;
                if order == Ordering::Greater {
                    merged.push(items[right]);
                    right += 1;
                } else {
                    merged.push(items[left]);
                    left += 1;
                }
            }
            merged.extend_from_slice(&items[left..middle]);
            merged.extend_from_slice(&items[right..end]);
        }
        items = merged;
        width *= 2;
    }
    Ok(items)
}

pub(super) fn sort<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let comparator = argument(args, 0);
    if comparator != Value::UNDEFINED && !machine.is_callable(comparator)? {
        return Err(type_error("Array sort comparator is not callable"));
    }
    let object = to_object(machine, this)?;
    with_roots(machine, &[object, comparator], |machine, depth| {
        let values = super::array::elements(machine, object)?;
        let length = values.len();
        let present: Vec<Value> = values
            .into_iter()
            .filter(|value| *value != Value::HOLE)
            .collect();
        for &value in &present {
            keep_root(machine, depth, value);
        }
        let count = present.len();
        let sorted = merge_sort(machine, present, comparator)?;
        for (index, value) in sorted.into_iter().enumerate() {
            set_index(machine, object, index, value)?;
        }
        // An array holds these slots already, so its length is no claim that fuel
        // has to bound, and most of them are holes that cost nothing to move past.
        let is_array = machine.array_len(object)?.is_some();
        for index in count..length {
            if is_array {
                machine.check_cancel().map_err(EvalFailure::Runtime)?;
            } else {
                tick(machine)?;
            }
            delete_index(machine, object, index)?;
        }
        Ok(object)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn reverse<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        for lower in 0..length / 2 {
            tick(machine)?;
            let upper = length - lower - 1;
            let lower_exists = has_index(machine, object, lower)?;
            let lower_value = if lower_exists {
                get_index(machine, object, lower)?
            } else {
                Value::UNDEFINED
            };
            keep_root(machine, depth, lower_value);
            let upper_exists = has_index(machine, object, upper)?;
            let upper_value = if upper_exists {
                get_index(machine, object, upper)?
            } else {
                Value::UNDEFINED
            };
            keep_root(machine, depth, upper_value);
            match (lower_exists, upper_exists) {
                (true, true) => {
                    set_index(machine, object, lower, upper_value)?;
                    set_index(machine, object, upper, lower_value)?;
                }
                (false, true) => {
                    set_index(machine, object, lower, upper_value)?;
                    delete_index(machine, object, upper)?;
                }
                (true, false) => {
                    delete_index(machine, object, lower)?;
                    set_index(machine, object, upper, lower_value)?;
                }
                (false, false) => {}
            }
            machine.native_roots[depth].truncate(1);
        }
        Ok(object)
    })
    .map(BuiltinOutcome::Value)
}

/// One array that `FlattenIntoArray` is part way through.
struct FlattenLevel {
    source: Value,
    length: usize,
    index: usize,
    remaining: Option<usize>,
}

/// `FlattenIntoArray` with an explicit stack, because the script controls how
/// deeply arrays nest. `remaining` is `None` for an infinite depth, and `mapper`
/// applies to the top level only.
fn flatten_into<H: Host>(
    machine: &mut Machine<'_, H>,
    target: Value,
    source: Value,
    length: usize,
    remaining: Option<usize>,
    mapper: Option<(Value, Value)>,
) -> Result<(), EvalFailure> {
    with_roots(machine, &[source], |machine, depth| {
        let mut levels = vec![FlattenLevel {
            source,
            length,
            index: 0,
            remaining,
        }];
        let mut to = 0;
        while let Some(level) = levels.last_mut() {
            tick(machine)?;
            if level.index >= level.length {
                levels.pop();
                machine.native_roots[depth].pop();
                continue;
            }
            let (source, index, remaining) = (level.source, level.index, level.remaining);
            level.index += 1;
            if !has_index(machine, source, index)? {
                continue;
            }
            let mut element = get_index(machine, source, index)?;
            if let Some((mapper, this_arg)) = mapper.filter(|_| levels.len() == 1) {
                let position = crate::number_value(index as f64);
                element = machine.call_value(mapper, this_arg, &[element, position, source])?;
            }
            if remaining != Some(0) && is_array(machine, element)? {
                if levels.len() > MAX_FLATTEN_DEPTH {
                    return Err(range_error("Array is nested too deeply to flatten"));
                }
                keep_root(machine, depth, element);
                let length = length_of_array_like(machine, element)?;
                levels.push(FlattenLevel {
                    source: element,
                    length,
                    index: 0,
                    remaining: remaining.map(|remaining| remaining - 1),
                });
            } else {
                if to >= MAX_SAFE_INTEGER {
                    return Err(type_error("Array length exceeds the safe integer limit"));
                }
                create_index(machine, target, to, element)?;
                to += 1;
            }
        }
        Ok(())
    })
}

pub(super) fn flat<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    with_roots(machine, &[object], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        let requested = match argument(args, 0) {
            Value::UNDEFINED => 1.0,
            requested => integer_or_infinity(machine, requested)?.max(0.0),
        };
        let remaining = requested.is_finite().then_some(requested as usize);
        let target = array_species_create(machine, object, 0)?;
        keep_root(machine, depth, target);
        flatten_into(machine, target, object, length, remaining, None)?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn flat_map<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let (mapper, this_arg) = (argument(args, 0), argument(args, 1));
    with_roots(machine, &[object, mapper, this_arg], |machine, depth| {
        let length = length_of_array_like(machine, object)?;
        require_callable(machine, mapper)?;
        let target = array_species_create(machine, object, 0)?;
        keep_root(machine, depth, target);
        flatten_into(
            machine,
            target,
            object,
            length,
            Some(1),
            Some((mapper, this_arg)),
        )?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

pub(super) fn fill<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let value = argument(args, 0);
    with_roots(machine, &[object, value], |machine, _| {
        let length = length_of_array_like(machine, object)?;
        let start = relative_position(machine, argument(args, 1), length)?;
        let end = match argument(args, 2) {
            Value::UNDEFINED => length,
            end => relative_position(machine, end, length)?,
        };
        for index in start..end {
            tick(machine)?;
            set_index(machine, object, index, value)?;
        }
        Ok(object)
    })
    .map(BuiltinOutcome::Value)
}

/// `Array(...)`. A single Number argument is a length, which must be a valid one;
/// any other single argument is an element.
pub(super) fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let new_target = machine.current_new_target();
    let default = machine.intrinsics.array_prototype;
    let prototype = if new_target == Value::UNDEFINED {
        default
    } else {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            default
        }
    };
    let array = match args {
        [length]
            if matches!(
                length.decode(),
                Some(Decoded::Int32(_) | Decoded::Number(_))
            ) =>
        {
            let length = value_number(*length);
            let integer = crate::to_uint32(length);
            if f64::from(integer) != length {
                return Err(range_error("Invalid array length"));
            }
            array_create(machine, integer as usize)?
        }
        _ => super::allocate_array(machine, args.to_vec())?,
    };
    if prototype != default {
        machine.set_prototype(array, prototype)?;
    }
    Ok(BuiltinOutcome::Value(array))
}

pub(super) fn is_array_method<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(Value::boolean(is_array(
        machine,
        argument(args, 0),
    )?)))
}

/// The receiver a static `Array` method builds into: `C` when it is a
/// constructor, and an intrinsic array otherwise.
fn construct_from_receiver<H: Host>(
    machine: &mut Machine<'_, H>,
    receiver: Value,
    length: Option<usize>,
) -> Result<Value, EvalFailure> {
    if machine.is_constructor(receiver)? {
        return match length {
            Some(length) => {
                machine.construct_value(receiver, &[crate::number_value(length as f64)])
            }
            None => machine.construct_value(receiver, &[]),
        };
    }
    array_create(machine, length.unwrap_or(0))
}

pub(super) fn of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    with_roots(machine, args, |machine, depth| {
        let target = construct_from_receiver(machine, this, Some(args.len()))?;
        keep_root(machine, depth, target);
        for (index, &value) in args.iter().enumerate() {
            create_index(machine, target, index, value)?;
        }
        set_length(machine, target, args.len())?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

fn iterator_method<H: Host>(
    machine: &mut Machine<'_, H>,
    items: Value,
) -> Result<Option<Value>, EvalFailure> {
    let key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())?;
    let method = machine.get_property_key(items, &key)?;
    if matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Ok(None);
    }
    if !machine.is_callable(method)? {
        return Err(type_error("value is not iterable"));
    }
    Ok(Some(method))
}

fn close_and_fail<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    failure: EvalFailure,
) -> EvalFailure {
    let (closed, _) = machine.close_iterator_raw(iterator);
    match closed {
        Err(EvalFailure::Runtime(kind)) => EvalFailure::Runtime(kind),
        _ => failure,
    }
}

pub(super) fn from<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (items, mapper, this_arg) = (argument(args, 0), argument(args, 1), argument(args, 2));
    if mapper != Value::UNDEFINED && !machine.is_callable(mapper)? {
        return Err(type_error("Array.from mapper is not callable"));
    }
    with_roots(machine, &[items, mapper, this_arg], |machine, depth| {
        if let Some(method) = iterator_method(machine, items)? {
            let target = construct_from_receiver(machine, this, None)?;
            keep_root(machine, depth, target);
            let opened = machine.call_value(method, items, &[])?;
            if !machine.is_object(opened) {
                return Err(type_error("iterator method returned a non-object"));
            }
            let next = machine.get_named_property(opened, "next")?;
            let iterator = machine.create_protocol_iterator(opened, next)?;
            keep_root(machine, depth, iterator);
            let mut index = 0;
            loop {
                let (done, value) = machine.iterator_next(iterator)?;
                if done {
                    set_length(machine, target, index)?;
                    return Ok(target);
                }
                let mapped = if mapper == Value::UNDEFINED {
                    value
                } else {
                    let position = crate::number_value(index as f64);
                    match machine.call_value(mapper, this_arg, &[value, position]) {
                        Ok(mapped) => mapped,
                        Err(failure) => return Err(close_and_fail(machine, iterator, failure)),
                    }
                };
                if let Err(failure) = create_index(machine, target, index, mapped) {
                    return Err(close_and_fail(machine, iterator, failure));
                }
                index += 1;
            }
        }
        let source = to_object(machine, items)?;
        keep_root(machine, depth, source);
        let length = length_of_array_like(machine, source)?;
        let target = construct_from_receiver(machine, this, Some(length))?;
        keep_root(machine, depth, target);
        for index in 0..length {
            tick(machine)?;
            let value = get_index(machine, source, index)?;
            let mapped = if mapper == Value::UNDEFINED {
                value
            } else {
                let position = crate::number_value(index as f64);
                machine.call_value(mapper, this_arg, &[value, position])?
            };
            create_index(machine, target, index, mapped)?;
        }
        set_length(machine, target, length)?;
        Ok(target)
    })
    .map(BuiltinOutcome::Value)
}

#[cfg(test)]
mod tests {
    use super::super::allocate_array;
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, BuiltinHandler, native_function};
    use crate::{Limits, ThrowOrigin};

    fn numbers(machine: &mut Machine<'_, TestHost>, values: &[i32]) -> Value {
        let elements = values.iter().map(|value| Value::int32(*value as u32));
        allocate_array(machine, elements.collect()).unwrap()
    }

    fn invoke(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let prototype = machine.intrinsics.array_prototype;
        let method = machine.get_named_property(prototype, name)?;
        machine.call_value(method, receiver, args)
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
        native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, id, name, 1)
    }

    fn return_this(
        _machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    /// Answers "less" whatever it is given, which is no consistent order at all.
    fn always_less(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::int32(-1i32 as u32)))
    }

    fn wrap_in_array(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let inner = allocate_array(machine, vec![args[0]])?;
        let outer = allocate_array(machine, vec![inner])?;
        Ok(BuiltinOutcome::Value(outer))
    }

    #[test]
    fn callbacks_receive_this_arg() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = numbers(&mut machine, &[1]);
        let callback = native(&mut machine, "return this", return_this);
        let this_arg = ordinary_object(&mut machine);
        let mapped = invoke(&mut machine, array, "map", &[callback, this_arg]).unwrap();
        assert_eq!(machine.array_elements(mapped).unwrap().unwrap(), [this_arg]);
    }

    #[test]
    fn concat_honours_is_concat_spreadable_in_both_directions() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_is_concat_spreadable())
            .unwrap();
        let spreadable_object = ordinary_object(&mut machine);
        machine
            .set_data_property(spreadable_object, "length", Value::int32(1))
            .unwrap();
        machine
            .set_data_property(spreadable_object, "0", Value::int32(5))
            .unwrap();
        machine
            .set_data_property_key(spreadable_object, key.clone(), Value::TRUE)
            .unwrap();
        let unspread_array = numbers(&mut machine, &[6]);
        machine
            .set_data_property_key(unspread_array, key, Value::FALSE)
            .unwrap();
        let receiver = numbers(&mut machine, &[4]);
        let result = invoke(
            &mut machine,
            receiver,
            "concat",
            &[spreadable_object, unspread_array],
        )
        .unwrap();
        assert_eq!(
            machine.array_elements(result).unwrap().unwrap(),
            [Value::int32(4), Value::int32(5), unspread_array]
        );
    }

    #[test]
    fn a_cyclic_array_joins_without_overflowing_the_stack() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = numbers(&mut machine, &[1]);
        invoke(&mut machine, array, "push", &[array]).unwrap();
        let joined = invoke(&mut machine, array, "join", &[]).unwrap();
        assert!(machine.string_value(joined).unwrap().eq_ascii("1,"));
        assert!(machine.array_join_stack.is_empty());
    }

    #[test]
    fn flattening_a_cyclic_array_is_a_range_error_rather_than_a_crash() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = numbers(&mut machine, &[]);
        invoke(&mut machine, array, "push", &[array]).unwrap();
        let depth = Value::number(f64::INFINITY);
        assert!(matches!(
            invoke(&mut machine, array, "flat", &[depth]),
            Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
        ));
    }

    #[test]
    fn flat_map_applies_its_mapper_once_and_flattens_one_level() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = numbers(&mut machine, &[7]);
        let mapper = native(&mut machine, "wrap in array", wrap_in_array);
        let result = invoke(&mut machine, array, "flatMap", &[mapper]).unwrap();
        let items = machine.array_elements(result).unwrap().unwrap();
        assert_eq!(items.len(), 1, "one level is flattened");
        assert_eq!(
            machine.array_elements(items[0]).unwrap().unwrap(),
            [Value::int32(7)],
            "the nested array keeps its element, unmapped"
        );
    }

    #[test]
    fn an_inconsistent_comparator_cannot_panic_the_sort() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = numbers(&mut machine, &(0..64).rev().collect::<Vec<_>>());
        let comparator = native(&mut machine, "always less", always_less);
        invoke(&mut machine, array, "sort", &[comparator]).unwrap();
        assert_eq!(machine.array_elements(array).unwrap().unwrap().len(), 64);
    }

    #[test]
    fn a_holey_array_past_the_array_like_limit_still_sorts() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let length = (1 << 20) + 1;
        let mut elements = vec![Value::HOLE; length];
        elements[0] = Value::int32(2);
        elements[length - 1] = Value::int32(1);
        let array = allocate_array(&mut machine, elements).unwrap();
        invoke(&mut machine, array, "sort", &[]).unwrap();
        let sorted = machine.array_elements(array).unwrap().unwrap();
        assert_eq!(sorted.len(), length);
        assert_eq!(sorted[..2], [Value::int32(1), Value::int32(2)]);
        assert!(sorted[2..].iter().all(|element| *element == Value::HOLE));
    }

    #[test]
    fn a_sort_comparator_must_be_callable_before_anything_else_happens() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        assert!(matches!(
            invoke(&mut machine, Value::UNDEFINED, "sort", &[Value::int32(1)]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Array sort comparator is not callable"
            }))
        ));
    }
}
