use crate::heap::Heap;
use std::collections::BTreeMap;

use bamts_native::{Decoded, Value};

use std::cmp::Ordering;
use std::mem::size_of;

use super::property_descriptor::descriptor_from_property;
use super::{
    allocate_array, allocate_string, argument, define_data, install_constructor_function,
    install_function, keep_root, length_of_array_like, number, range_error, to_integer_or_infinity,
    type_error, value_number, with_roots,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable, IteratorFamily};
use crate::{
    ArrayElementKind, EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey,
    PropertyMap, RuntimeErrorKind,
};
use bamts_bytecode::{EcmaString, EcmaStringBuilder};

pub(super) fn install<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.array_prototype();
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "Array",
            length: 1,
            handler: constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    globals.insert(EcmaString::encode("Array"), constructor);
    for (name, length, handler) in [
        ("isArray", 1, is_array_method::<H> as BuiltinHandler<H>),
        ("from", 1, from::<H>),
        ("of", 0, of::<H>),
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
        define_static(heap, atoms, shapes, constructor, name, function);
    }
    for (name, length, handler) in [
        ("toString", 0, to_string::<H> as BuiltinHandler<H>),
        ("toLocaleString", 0, to_locale_string::<H>),
        ("copyWithin", 2, copy_within::<H>),
        ("push", 1, push::<H>),
        ("pop", 0, pop::<H>),
        ("shift", 0, shift::<H>),
        ("unshift", 1, unshift::<H>),
        ("slice", 2, slice::<H>),
        ("splice", 2, splice::<H>),
        ("concat", 1, concat::<H>),
        ("join", 1, join::<H>),
        ("indexOf", 1, index_of::<H>),
        ("lastIndexOf", 1, last_index_of::<H>),
        ("includes", 1, includes::<H>),
        ("find", 1, find::<H>),
        ("findIndex", 1, find_index::<H>),
        ("filter", 1, filter::<H>),
        ("map", 1, map::<H>),
        ("forEach", 1, for_each::<H>),
        ("reduce", 1, reduce::<H>),
        ("reduceRight", 1, reduce_right::<H>),
        ("some", 1, some::<H>),
        ("every", 1, every::<H>),
        ("sort", 1, sort::<H>),
        ("reverse", 0, reverse::<H>),
        ("flat", 0, flat::<H>),
        ("flatMap", 1, flat_map::<H>),
        ("fill", 1, fill::<H>),
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
    let species = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get [Symbol.species]",
            length: 0,
            handler: super::regexp::species_getter::<H>,
        },
    );
    super::define_symbol_property(
        heap,
        shapes,
        constructor,
        builtins.symbol_species(),
        Property::Accessor {
            getter: Some(species),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    let keys = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "keys",
            length: 0,
            handler: keys_iterator::<H>,
        },
    );
    let values = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "values",
            length: 0,
            handler: values_iterator::<H>,
        },
    );
    let entries = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "entries",
            length: 0,
            handler: entries_iterator::<H>,
        },
    );
    define_data(heap, atoms, shapes, prototype, "keys", keys);
    define_data(heap, atoms, shapes, prototype, "values", values);
    define_data(heap, atoms, shapes, prototype, "entries", entries);
    let unscopables = super::super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: None,
            extensible: true,
            boxed_primitive: None,
        },
    );
    {
        let HeapEntry::Object { properties, .. } = &mut heap[super::heap_index(unscopables)] else {
            unreachable!()
        };
        for name in [
            "at",
            "copyWithin",
            "entries",
            "fill",
            "find",
            "findIndex",
            "findLast",
            "findLastIndex",
            "flat",
            "flatMap",
            "includes",
            "keys",
            "toReversed",
            "toSorted",
            "toSpliced",
            "values",
        ] {
            properties.insert(
                shapes,
                PropertyKey::Named(atoms.intern_str(name)),
                Property::Data {
                    value: Value::TRUE,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            );
        }
    }
    let HeapEntry::Array { properties, .. } = &mut heap[super::heap_index(prototype)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(super::heap_index(builtins.symbol_iterator()) as u32),
        super::builtin_property(values),
    );
    properties.insert(
        shapes,
        PropertyKey::Symbol(super::heap_index(builtins.symbol_unscopables()) as u32),
        Property::Data {
            value: unscopables,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
    install_change_by_copy_and_from_async(heap, atoms, shapes, builtins, prototype, constructor);
}

fn define_static(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    constructor: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("Array constructor must be native")
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        super::builtin_property(value),
    );
}

/// The most elements a non-array receiver is read into a list for. A receiver may
/// claim a length of 2^53 - 1.
const MAX_ARRAY_LIKE_ELEMENTS: usize = 1 << 20;

/// Reads `this` as a list. Array methods are generic, so any object with a length
/// works; one that is not an array is read once, up front, with a missing index
/// kept as a hole.
pub(super) fn elements<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
) -> Result<Vec<Value>, EvalFailure> {
    let array = machine.array_elements(this)?;
    let is_array = array.is_some();
    if let Some(values) = array
        && !values.contains(&Value::HOLE)
    {
        return Ok(values);
    }
    let object = to_object(machine, this)?;
    let length = length_of_array_like(machine, object)?;
    // An array's length is what it already holds, however many of those are holes.
    if !is_array && length > MAX_ARRAY_LIKE_ELEMENTS {
        return Err(type_error("Array method received too long an array-like"));
    }
    let mut values = Vec::with_capacity(length);
    for index in 0..length {
        let key = index_key(&mut machine.atoms, index);
        values.push(if machine.internal_has_property(object, &key)? {
            machine.get_property_key(object, &key)?
        } else {
            Value::HOLE
        });
    }
    Ok(values)
}
fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = machine.value_to_object(this)?;
    let join = machine.get_named_property(object, "join")?;
    let function = if machine.is_callable(join)? {
        join
    } else {
        machine.intrinsics.object_to_string()
    };
    Ok(BuiltinOutcome::Value(machine.call_value(
        function,
        object,
        &[],
    )?))
}
/// `Array.prototype.toLocaleString`: each element's own `toLocaleString`,
/// joined with a comma. ECMA-402 passes `locales` and `options` on to every
/// element. `object` stays rooted because every element can run user code.
fn to_locale_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let argument = |index: usize| args.get(index).copied().unwrap_or(Value::UNDEFINED);
    let forwarded = [argument(0), argument(1)];
    let joined = super::with_roots(machine, &[object], |machine, _| {
        guarded_join(machine, object, |machine| {
            locale_join(machine, object, &forwarded)
        })
    })?;
    Ok(BuiltinOutcome::Value(allocate_string(machine, joined)?))
}
fn locale_join<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    forwarded: &[Value],
) -> Result<EcmaString, EvalFailure> {
    let length = length_of_array_like(machine, object)?;
    let mut output = bamts_bytecode::EcmaStringBuilder::new();
    for index in 0..length {
        tick(machine)?;
        if index != 0 {
            output.push_unit(u16::from(b','));
        }
        let key = index_key(&mut machine.atoms, index);
        let element = machine.get_property_key(object, &key)?;
        if matches!(element.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            continue;
        }
        let method = machine.get_named_property(element, "toLocaleString")?;
        let text = machine.call_value(method, element, forwarded)?;
        for &unit in machine.coerce_string_observable(text)?.as_units() {
            output.push_unit(unit);
        }
    }
    Ok(output.finish())
}
/// `Array.prototype.copyWithin`. Each step reads and writes through the
/// object's own internal methods, so a hole deletes its destination and a
/// proxy or accessor observes every step in specification order.
fn copy_within<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[object]);
    let copied = copy_within_steps(machine, object, args);
    machine.pop_native_roots(depth);
    copied?;
    Ok(BuiltinOutcome::Value(object))
}
fn copy_within_steps<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    args: &[Value],
) -> Result<(), EvalFailure> {
    let length = length_of_array_like(machine, object)?;
    let target = args.first().copied().unwrap_or(Value::UNDEFINED);
    let mut to = relative_position(machine, target, length)?;
    let start = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let mut from = relative_position(machine, start, length)?;
    let end = match args.get(2).copied() {
        None | Some(Value::UNDEFINED) => length,
        Some(end) => relative_position(machine, end, length)?,
    };
    let mut count = end.saturating_sub(from).min(length - to);
    let backward = from < to && to < from + count;
    if backward && count > 0 {
        from += count - 1;
        to += count - 1;
    }
    while count > 0 {
        tick(machine)?;
        let from_key = index_key(&mut machine.atoms, from);
        let to_key = index_key(&mut machine.atoms, to);
        if machine.internal_has_property(object, &from_key)? {
            let value = machine.get_property_key(object, &from_key)?;
            machine.set_data_property_key(object, to_key, value)?;
        } else if !machine.internal_delete(object, &to_key)? {
            return Err(type_error("Cannot delete property during copyWithin"));
        }
        count -= 1;
        if count > 0 {
            if backward {
                from -= 1;
                to -= 1;
            } else {
                from += 1;
                to += 1;
            }
        }
    }
    Ok(())
}

fn keys_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        object,
        IterationKind::Key(IteratorFamily::Array),
    )?))
}

fn values_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        object,
        IterationKind::Value(IteratorFamily::Array),
    )?))
}

fn entries_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let object = to_object(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        object,
        IterationKind::Entry(IteratorFamily::Array),
    )?))
}
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;
const MAX_ARRAY_LENGTH: usize = u32::MAX as usize;

/// Replaces the baseline implementations of `at` and `findLast`, installs the
/// ES2023 copy-by-change family on `%Array.prototype%`, and installs
/// `Array.fromAsync` plus its hidden continuation targets on `%Array%`.
pub(super) fn install_change_by_copy_and_from_async<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
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
        define_data(heap, atoms, shapes, array_prototype, name, function);
    }
    let from_async = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "fromAsync",
            length: 3,
            handler: from_async::<H>,
        },
    );
    define_from_async_static(
        heap,
        atoms,
        shapes,
        array_constructor,
        "fromAsync",
        from_async,
    );
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
        targets.push(install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length: 1,
                handler,
            },
        ));
    }
    let target_table = crate::intrinsics::push(
        heap,
        HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&targets),
            elements: targets,
            properties: crate::PropertyMap::default(),
            prototype: None,
            extensible: true,
            length_writable: true,
        },
    );
    define_data(
        heap,
        atoms,
        shapes,
        array_prototype,
        TARGETS_PROPERTY,
        target_table,
    );
}

pub(super) fn to_object<H: Host>(
    machine: &mut Machine<'_, H>,
    value: Value,
) -> Result<Value, EvalFailure> {
    machine.value_to_object(value)
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
        } => Some((
            elements.len(),
            properties.contains_key(&machine.shapes, &key),
            *extensible,
        )),
        _ => None,
    };
    let Some((length, explicit_descriptor, extensible)) = array_state else {
        return machine.create_data_property_key(array, key, value);
    };
    if explicit_descriptor {
        return machine.create_data_property_key(array, key, value);
    }
    if index < length {
        let replacing_hole = match &machine.heap[slot] {
            HeapEntry::Array { elements, .. } => elements[index] == Value::HOLE,
            _ => unreachable!("array was matched above"),
        };
        if replacing_hole && !extensible {
            return Err(type_error("Cannot add property to non-extensible array"));
        }
        machine.store_element(slot, index, value);
        return Ok(());
    }
    while machine.array_length(array)? < index {
        machine.array_push(array, Value::HOLE)?;
    }
    machine.array_push(array, value)
}

fn relative_position_float(relative: f64, length: usize) -> f64 {
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
    let relative = to_integer_or_infinity(machine, argument(args, 0))?;
    let index = relative_position_float(relative, length);
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
    let relative_start = to_integer_or_infinity(machine, argument(args, 0))?;
    let actual_start = clamped_start(relative_start, length);
    let insert_count = args.len().saturating_sub(2);
    let skip_count = if args.is_empty() {
        0
    } else if args.len() == 1 {
        length - actual_start
    } else {
        let relative = to_integer_or_infinity(machine, args[1])?;
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
    let relative = to_integer_or_infinity(machine, argument(args, 0))?;
    let actual = relative_position_float(relative, length);
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
fn define_from_async_static(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    constructor: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[super::heap_index(constructor)]
    else {
        panic!("Array fromAsync attaches to a native-function constructor")
    };
    properties.insert(
        shapes,
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
const MAX_SAFE_ARRAY_LENGTH: usize = 9_007_199_254_740_991;
/// How deeply `flat` follows nested arrays before treating the input as cyclic.
const MAX_FLATTEN_DEPTH: usize = 4096;

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

pub(super) fn get_index<H: Host>(
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
        machine.store_element(slot, index, value);
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
    let relative = to_integer_or_infinity(machine, value)?;
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
        if length.saturating_add(args.len()) > MAX_SAFE_ARRAY_LENGTH {
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
            if length.saturating_add(count) > MAX_SAFE_ARRAY_LENGTH {
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
                let requested = to_integer_or_infinity(machine, args[1])?;
                requested.clamp(0.0, (length - start) as f64) as usize
            }
        };
        if (length + items.len()).saturating_sub(delete_count) > MAX_SAFE_ARRAY_LENGTH {
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
                if to.saturating_add(length) > MAX_SAFE_ARRAY_LENGTH {
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
                if to >= MAX_SAFE_ARRAY_LENGTH {
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
    let relative = to_integer_or_infinity(machine, from_index)?;
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
            to_integer_or_infinity(machine, args[1])?
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
            tick(machine)?;
            if !has_index(machine, object, index)? {
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
                if to >= MAX_SAFE_ARRAY_LENGTH {
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
            requested => to_integer_or_infinity(machine, requested)?.max(0.0),
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
mod fuel_tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, RuntimeErrorKind};

    #[test]
    fn to_sorted_pays_for_its_elements_and_not_for_its_comparisons() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let limits = Limits {
            fuel: 2100,
            ..Limits::default()
        };
        let mut machine = Machine::new(&module, &mut host, limits);
        let elements = (0..2000).rev().map(Value::int32).collect();
        let array = super::super::allocate_array(&mut machine, elements).unwrap();
        let method = machine.get_named_property(array, "toSorted").unwrap();
        machine.call_value(method, array, &[]).unwrap();
    }

    fn cancel_and_keep_order(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.cancel.cancel();
        Ok(BuiltinOutcome::Value(Value::int32(0)))
    }

    #[test]
    fn a_cancelled_to_sorted_stops_at_the_next_comparison() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "cancel",
            length: 2,
            handler: cancel_and_keep_order,
        });
        let comparator = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "cancel",
            2,
        );
        let elements = (0..4).rev().map(Value::int32).collect();
        let array = super::super::allocate_array(&mut machine, elements).unwrap();
        let method = machine.get_named_property(array, "toSorted").unwrap();
        assert!(matches!(
            machine.call_value(method, array, &[comparator]),
            Err(EvalFailure::Runtime(RuntimeErrorKind::Cancelled))
        ));
    }

    #[test]
    fn a_loop_over_a_long_array_like_runs_out_of_fuel() {
        for (method, arguments) in [
            ("copyWithin", vec![Value::int32(0), Value::int32(1)]),
            ("toLocaleString", Vec::new()),
            ("toReversed", Vec::new()),
            ("toSorted", Vec::new()),
            ("toSpliced", Vec::new()),
            ("with", vec![Value::int32(0), Value::int32(0)]),
            ("findLast", Vec::new()),
        ] {
            let module = blank_program("<test>");
            let mut host = TestHost;
            let limits = Limits {
                fuel: 16,
                ..Limits::default()
            };
            let mut machine = Machine::new(&module, &mut host, limits);
            let object = ordinary_object(&mut machine);
            machine
                .set_data_property(object, "length", Value::int32(1000))
                .unwrap();
            let constructor = machine.intrinsics.global("Array").unwrap();
            let prototype = machine
                .get_named_property(constructor, "prototype")
                .unwrap();
            let function = machine.get_named_property(prototype, method).unwrap();
            let predicate = machine.intrinsics.global("Boolean").unwrap();
            let arguments = if method == "findLast" {
                vec![predicate]
            } else {
                arguments
            };
            assert!(
                matches!(
                    machine.call_value(function, object, &arguments),
                    Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted { .. }))
                ),
                "{method}"
            );
        }
    }

    /// The same holds outside `Array.prototype`: each of these builtins walks a
    /// length that the program states.
    #[test]
    fn a_loop_over_a_claimed_length_runs_out_of_fuel_outside_array() {
        for case in [
            "Intl.getCanonicalLocales",
            "String.raw",
            "JSON.stringify array",
            "JSON.stringify replacer",
            "JSON.parse reviver",
        ] {
            let module = blank_program("<test>");
            let mut host = TestHost;
            let limits = Limits {
                fuel: 16,
                ..Limits::default()
            };
            let mut machine = Machine::new(&module, &mut host, limits);
            let claimed = ordinary_object(&mut machine);
            machine
                .set_data_property(claimed, "length", Value::int32(1000))
                .unwrap();
            let long =
                super::super::allocate_array(&mut machine, vec![Value::int32(0); 1000]).unwrap();
            let (owner, method, arguments) = match case {
                "Intl.getCanonicalLocales" => ("Intl", "getCanonicalLocales", vec![claimed]),
                "String.raw" => {
                    let template = ordinary_object(&mut machine);
                    machine.set_data_property(template, "raw", claimed).unwrap();
                    ("String", "raw", vec![template])
                }
                "JSON.stringify array" => ("JSON", "stringify", vec![long]),
                "JSON.stringify replacer" => ("JSON", "stringify", vec![claimed, long]),
                _ => {
                    let text = format!("[{}]", vec!["0"; 1000].join(","));
                    let text = super::super::allocate_string(
                        &mut machine,
                        bamts_bytecode::EcmaString::encode(&text),
                    )
                    .unwrap();
                    let reviver = machine.intrinsics.global("Boolean").unwrap();
                    ("JSON", "parse", vec![text, reviver])
                }
            };
            let owner = machine.intrinsics.global(owner).unwrap();
            let function = machine.get_named_property(owner, method).unwrap();
            assert!(
                matches!(
                    machine.call_value(function, owner, &arguments),
                    Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted { .. }))
                ),
                "{case}"
            );
        }
    }
}
#[cfg(test)]
mod copy_within_tests {
    use super::super::allocate_array;
    use super::super::test_support::{TestHost, blank_program};
    use super::*;
    use crate::Limits;

    fn array_of(machine: &mut Machine<'_, TestHost>, values: &[i32]) -> Value {
        let elements = values.iter().map(|value| Value::int32(*value as u32));
        allocate_array(machine, elements.collect()).unwrap()
    }

    fn copy(machine: &mut Machine<'_, TestHost>, array: Value, args: &[Value]) -> Vec<Value> {
        let method = machine
            .get_named_property(array, "copyWithin")
            .expect("copyWithin is installed");
        let result = machine.call_value(method, array, args).unwrap();
        assert_eq!(result, array, "copyWithin returns its receiver");
        machine.array_elements(array).unwrap().unwrap()
    }

    #[test]
    fn overlapping_ranges_copy_as_if_through_a_temporary() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let forward = array_of(&mut machine, &[1, 2, 3, 4, 5]);
        assert_eq!(
            copy(&mut machine, forward, &[Value::int32(0), Value::int32(1)]),
            [2, 3, 4, 5, 5].map(Value::int32)
        );
        let backward = array_of(&mut machine, &[1, 2, 3, 4, 5]);
        assert_eq!(
            copy(&mut machine, backward, &[Value::int32(1), Value::int32(0)]),
            [1, 1, 2, 3, 4].map(Value::int32)
        );
    }

    #[test]
    fn a_hole_at_the_source_deletes_the_destination() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = allocate_array(
            &mut machine,
            vec![Value::HOLE, Value::int32(2), Value::int32(3)],
        )
        .unwrap();
        assert_eq!(
            copy(
                &mut machine,
                array,
                &[Value::int32(2), Value::int32(0), Value::int32(1)]
            ),
            [Value::HOLE, Value::int32(2), Value::HOLE]
        );
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use bamts_bytecode::{
        BinaryOp, Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId,
        Instruction, Module, ModuleId, Program, ProgramModule, Register, Verified,
    };
    use bamts_native::Decoded;

    use super::super::allocate_array;
    use super::super::test_support::{TestHost, blank_program, custom_iterable, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, BuiltinHandler, native_function};
    use crate::{Limits, Property, PropertyMap, RuntimeErrorKind, ThrowOrigin};

    fn call_array(
        machine: &mut Machine<'_, TestHost>,
        method_name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let constructor = machine.intrinsics.global("Array").unwrap();
        let method = machine.get_named_property(constructor, method_name)?;
        machine.call_value(method, constructor, args)
    }

    // ---- custom iterable helpers -------------------------------------------

    /// Builds an object with a custom `Symbol.iterator` that yields `values`
    /// in order, bypassing any structural shortcuts.

    // ---- tests -------------------------------------------------------------

    #[test]
    fn array_from_observes_custom_iterator_override() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // An array with real elements [1, 2, 3] but a custom Symbol.iterator
        // that yields [10, 20, 30]. Array.from must observe the override.
        let backing = allocate_array(
            &mut machine,
            vec![Value::int32(1), Value::int32(2), Value::int32(3)],
        )
        .unwrap();
        let source = custom_iterable(
            &mut machine,
            vec![Value::int32(10), Value::int32(20), Value::int32(30)],
        );
        // Copy the fixture state the custom iterator needs from `source` onto
        // `backing` before installing the custom Symbol.iterator.
        let values = machine.get_named_property(source, "_values").unwrap();
        let next = machine.get_named_property(source, "_next").unwrap();
        machine
            .set_data_property(backing, "_values", values)
            .unwrap();
        machine.set_data_property(backing, "_next", next).unwrap();

        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
        let custom_iter_fn = machine.get_property_key(source, &iterator_key).unwrap();
        machine
            .set_data_property_key(backing, iterator_key, custom_iter_fn)
            .unwrap();

        let result = call_array(&mut machine, "from", &[backing]).unwrap();
        let elements = machine.array_elements(result).unwrap().unwrap();
        assert_eq!(
            elements,
            vec![Value::int32(10), Value::int32(20), Value::int32(30)]
        );
    }

    #[test]
    fn array_from_preserves_mapper_order_and_thisarg() {
        fn mapper<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let element = args.first().copied().unwrap_or(Value::int32(0));
            let index = args.get(1).copied().unwrap_or(Value::int32(0));
            let offset = machine.get_named_property(this, "offset")?;
            let e = match element.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => 0,
            };
            let i = match index.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => 0,
            };
            let o = match offset.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => 0,
            };
            Ok(BuiltinOutcome::Value(Value::int32(e * 100 + i + o)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let source = custom_iterable(
            &mut machine,
            vec![Value::int32(1), Value::int32(2), Value::int32(3)],
        );
        let mapper_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "mapper",
            length: 1,
            handler: mapper::<TestHost>,
        });
        let mapper_fn = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            mapper_id,
            "mapper",
            1,
        );
        let this_arg = ordinary_object(&mut machine);
        machine
            .set_data_property(this_arg, "offset", Value::int32(1000))
            .unwrap();

        let result = call_array(&mut machine, "from", &[source, mapper_fn, this_arg]).unwrap();
        let elements = machine.array_elements(result).unwrap().unwrap();
        // element*100 + index + offset(1000)
        assert_eq!(
            elements,
            vec![
                Value::int32(1100), // 1*100 + 0 + 1000
                Value::int32(1201), // 2*100 + 1 + 1000
                Value::int32(1302), // 3*100 + 2 + 1000
            ]
        );
    }

    #[test]
    fn array_from_consumes_string_through_protocol() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let text = allocate_string(&mut machine, EcmaString::encode("abc")).unwrap();
        let result = call_array(&mut machine, "from", &[text]).unwrap();
        let elements = machine.array_elements(result).unwrap().unwrap();
        assert_eq!(elements.len(), 3);
        assert!(
            machine
                .string_value(elements[0])
                .is_some_and(|s| s.eq_ascii("a"))
        );
        assert!(
            machine
                .string_value(elements[1])
                .is_some_and(|s| s.eq_ascii("b"))
        );
        assert!(
            machine
                .string_value(elements[2])
                .is_some_and(|s| s.eq_ascii("c"))
        );
    }

    #[test]
    fn array_from_rejects_non_iterable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let source = ordinary_object(&mut machine);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
        machine
            .set_data_property_key(source, iterator_key, Value::int32(123))
            .unwrap();
        let result = call_array(&mut machine, "from", &[source]);
        assert!(result.is_err());
    }

    // ---- Array.from protocol regressions -----------------------------------

    thread_local! {
        static LOG: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
    }

    fn clear_log() {
        LOG.with(|log| log.borrow_mut().clear());
    }

    fn log_event(event: impl Into<String>) {
        LOG.with(|log| log.borrow_mut().push(event.into()));
    }

    fn get_log() -> Vec<String> {
        LOG.with(|log| log.borrow().clone())
    }

    fn make_test_iterable<H: Host>(machine: &mut Machine<'_, H>, iter_obj: Value) -> Value {
        fn create_fn<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let iter_obj = machine.get_named_property(this, "_iter_obj")?;
            Ok(BuiltinOutcome::Value(iter_obj))
        }

        let iterable = ordinary_object(machine);
        machine
            .set_data_property(iterable, "_iter_obj", iter_obj)
            .unwrap();

        let create_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "test_symbol_iterator",
            length: 0,
            handler: create_fn::<H>,
        });
        let create_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            create_id,
            "test_symbol_iterator",
            0,
        );

        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
        machine
            .set_data_property_key(iterable, iterator_key, create_func)
            .unwrap();
        iterable
    }

    #[test]
    fn array_from_interleaves_iterator_and_mapper() {
        fn next_fn<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let index_val = machine.get_named_property(this, "_index")?;
            let index = match index_val.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => 0,
            };
            log_event(format!("next:{}", index));

            let res = ordinary_object(machine);
            if index == 0 {
                machine.set_data_property(res, "done", Value::FALSE)?;
                machine.set_data_property(res, "value", Value::int32(10))?;
                machine.set_data_property(this, "_index", Value::int32(1))?;
            } else if index == 1 {
                machine.set_data_property(res, "done", Value::FALSE)?;
                machine.set_data_property(res, "value", Value::int32(20))?;
                machine.set_data_property(this, "_index", Value::int32(2))?;
            } else {
                machine.set_data_property(res, "done", Value::TRUE)?;
                machine.set_data_property(res, "value", Value::UNDEFINED)?;
            }
            Ok(BuiltinOutcome::Value(res))
        }

        fn map_fn<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let val = args.first().copied().unwrap_or(Value::UNDEFINED);
            let idx = args.get(1).copied().unwrap_or(Value::UNDEFINED);
            let v = match val.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => u32::MAX,
            };
            let i = match idx.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => u32::MAX,
            };
            log_event(format!("map:v={}:i={}", v, i));
            Ok(BuiltinOutcome::Value(Value::int32(v * 10)))
        }

        clear_log();
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let next_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "next",
            length: 0,
            handler: next_fn::<TestHost>,
        });
        let next_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            next_id,
            "next",
            0,
        );

        let iter_obj = ordinary_object(&mut machine);
        machine
            .set_data_property(iter_obj, "_index", Value::int32(0))
            .unwrap();
        machine
            .set_data_property(iter_obj, "next", next_func)
            .unwrap();

        let iterable = make_test_iterable(&mut machine, iter_obj);

        let map_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "mapper",
            length: 2,
            handler: map_fn::<TestHost>,
        });
        let mapper_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            map_id,
            "mapper",
            2,
        );

        let result = call_array(&mut machine, "from", &[iterable, mapper_func]).unwrap();
        let elements = machine.array_elements(result).unwrap().unwrap();
        assert_eq!(elements, vec![Value::int32(100), Value::int32(200)]);

        assert_eq!(
            get_log(),
            vec!["next:0", "map:v=10:i=0", "next:1", "map:v=20:i=1", "next:2"]
        );
    }

    #[test]
    fn array_from_mapper_failure_closes_iterator() {
        fn next_fn<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let index_val = machine.get_named_property(this, "_index")?;
            let index = match index_val.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => 0,
            };
            log_event(format!("next:{}", index));

            let res = ordinary_object(machine);
            if index == 0 {
                machine.set_data_property(res, "done", Value::FALSE)?;
                machine.set_data_property(res, "value", Value::int32(10))?;
                machine.set_data_property(this, "_index", Value::int32(1))?;
            } else if index == 1 {
                machine.set_data_property(res, "done", Value::FALSE)?;
                machine.set_data_property(res, "value", Value::int32(20))?;
                machine.set_data_property(this, "_index", Value::int32(2))?;
            } else {
                machine.set_data_property(res, "done", Value::TRUE)?;
                machine.set_data_property(res, "value", Value::UNDEFINED)?;
            }
            Ok(BuiltinOutcome::Value(res))
        }

        fn return_fn<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            log_event("return");
            let res = ordinary_object(machine);
            machine.set_data_property(res, "done", Value::TRUE)?;
            machine.set_data_property(res, "value", Value::UNDEFINED)?;
            Ok(BuiltinOutcome::Value(res))
        }

        fn failing_map_fn<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let val = args.first().copied().unwrap_or(Value::UNDEFINED);
            let v = match val.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => u32::MAX,
            };
            if v == 20 {
                log_event("map:throws");
                Err(type_error("mapper failure"))
            } else {
                log_event(format!("map:v={}", v));
                Ok(BuiltinOutcome::Value(Value::int32(v * 10)))
            }
        }

        clear_log();
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let next_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "next",
            length: 0,
            handler: next_fn::<TestHost>,
        });
        let next_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            next_id,
            "next",
            0,
        );

        let return_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "return",
            length: 0,
            handler: return_fn::<TestHost>,
        });
        let return_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            return_id,
            "return",
            0,
        );

        let iter_obj = ordinary_object(&mut machine);
        machine
            .set_data_property(iter_obj, "_index", Value::int32(0))
            .unwrap();
        machine
            .set_data_property(iter_obj, "next", next_func)
            .unwrap();
        machine
            .set_data_property(iter_obj, "return", return_func)
            .unwrap();

        let iterable = make_test_iterable(&mut machine, iter_obj);

        let map_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "failing_mapper",
            length: 2,
            handler: failing_map_fn::<TestHost>,
        });
        let mapper_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            map_id,
            "failing_mapper",
            2,
        );

        let result = call_array(&mut machine, "from", &[iterable, mapper_func]);
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "mapper failure"
            }))
        ));

        assert_eq!(
            get_log(),
            vec!["next:0", "map:v=10", "next:1", "map:throws", "return"]
        );
    }

    #[test]
    fn array_from_next_failure_does_not_close_iterator() {
        fn next_throws_fn<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            log_event("next_throws");
            Err(type_error("next failure"))
        }

        fn return_fn<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            log_event("return");
            let res = ordinary_object(machine);
            machine.set_data_property(res, "done", Value::TRUE)?;
            machine.set_data_property(res, "value", Value::UNDEFINED)?;
            Ok(BuiltinOutcome::Value(res))
        }

        clear_log();
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let next_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "next_throws",
            length: 0,
            handler: next_throws_fn::<TestHost>,
        });
        let next_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            next_id,
            "next_throws",
            0,
        );

        let return_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "return",
            length: 0,
            handler: return_fn::<TestHost>,
        });
        let return_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            return_id,
            "return",
            0,
        );

        let iter_obj = ordinary_object(&mut machine);
        machine
            .set_data_property(iter_obj, "next", next_func)
            .unwrap();
        machine
            .set_data_property(iter_obj, "return", return_func)
            .unwrap();

        let iterable = make_test_iterable(&mut machine, iter_obj);

        let result = call_array(&mut machine, "from", &[iterable]);
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "next failure"
            }))
        ));

        assert_eq!(get_log(), vec!["next_throws"]);
    }

    #[test]
    fn array_from_null_or_undefined_iterator_falls_back_to_array_like() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();

        // Null iterator
        let source_null = ordinary_object(&mut machine);
        machine
            .set_data_property_key(source_null, iterator_key.clone(), Value::NULL)
            .unwrap();
        machine
            .set_data_property(source_null, "length", Value::int32(2))
            .unwrap();
        machine
            .set_data_property(source_null, "0", Value::int32(10))
            .unwrap();
        machine
            .set_data_property(source_null, "1", Value::int32(20))
            .unwrap();

        let res_null = call_array(&mut machine, "from", &[source_null]).unwrap();
        let elems_null = machine.array_elements(res_null).unwrap().unwrap();
        assert_eq!(elems_null, vec![Value::int32(10), Value::int32(20)]);

        // Undefined iterator
        let source_undef = ordinary_object(&mut machine);
        machine
            .set_data_property_key(source_undef, iterator_key, Value::UNDEFINED)
            .unwrap();
        machine
            .set_data_property(source_undef, "length", Value::int32(2))
            .unwrap();
        machine
            .set_data_property(source_undef, "0", Value::int32(30))
            .unwrap();
        machine
            .set_data_property(source_undef, "1", Value::int32(40))
            .unwrap();

        let res_undef = call_array(&mut machine, "from", &[source_undef]).unwrap();
        let elems_undef = machine.array_elements(res_undef).unwrap().unwrap();
        assert_eq!(elems_undef, vec![Value::int32(30), Value::int32(40)]);
    }

    #[test]
    fn array_from_rejects_non_callable_mapper_and_iterator() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let source = custom_iterable(&mut machine, vec![Value::int32(1)]);
        let not_callable_mapper = Value::int32(42);
        let res_mapper = call_array(&mut machine, "from", &[source, not_callable_mapper]);
        assert!(matches!(
            res_mapper,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Array.from mapper is not callable"
            }))
        ));

        let source_bad_iter = ordinary_object(&mut machine);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.property_key_from_value(iterator_symbol).unwrap();
        machine
            .set_data_property_key(source_bad_iter, iterator_key, Value::int32(123))
            .unwrap();

        let res_iter = call_array(&mut machine, "from", &[source_bad_iter]);
        assert!(matches!(
            res_iter,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "value is not iterable"
            }))
        ));
    }

    #[test]
    fn array_from_array_like_mapper_sees_indices_in_order() {
        fn array_like_map_fn<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let val = args.first().copied().unwrap_or(Value::UNDEFINED);
            let idx = args.get(1).copied().unwrap_or(Value::UNDEFINED);
            let v = match val.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => u32::MAX,
            };
            let i = match idx.decode() {
                Some(Decoded::Int32(i)) => i,
                _ => u32::MAX,
            };
            log_event(format!("array_like_map:v={}:i={}", v, i));
            Ok(BuiltinOutcome::Value(Value::int32(v + i)))
        }

        clear_log();
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let source = ordinary_object(&mut machine);
        machine
            .set_data_property(source, "length", Value::int32(3))
            .unwrap();
        machine
            .set_data_property(source, "0", Value::int32(100))
            .unwrap();
        machine
            .set_data_property(source, "1", Value::int32(200))
            .unwrap();
        machine
            .set_data_property(source, "2", Value::int32(300))
            .unwrap();

        let map_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "array_like_mapper",
            length: 2,
            handler: array_like_map_fn::<TestHost>,
        });
        let mapper_func = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            map_id,
            "array_like_mapper",
            2,
        );

        let result = call_array(&mut machine, "from", &[source, mapper_func]).unwrap();
        let elements = machine.array_elements(result).unwrap().unwrap();
        assert_eq!(
            elements,
            vec![Value::int32(100), Value::int32(201), Value::int32(302)]
        );

        assert_eq!(
            get_log(),
            vec![
                "array_like_map:v=100:i=0",
                "array_like_map:v=200:i=1",
                "array_like_map:v=300:i=2"
            ]
        );
    }

    #[test]
    fn array_prototype_unscopables_descriptor_and_entries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array_prototype = machine.intrinsics.array_prototype;
        let unscopables_symbol = machine.intrinsics.builtins.symbol_unscopables();
        let key = machine.property_key_from_value(unscopables_symbol).unwrap();
        let descriptor = machine
            .own_descriptor(array_prototype, &key)
            .expect("descriptor lookup succeeds")
            .expect("Array.prototype[Symbol.unscopables] is defined");
        let Property::Data {
            value: unscopables,
            writable,
            enumerable,
            configurable,
        } = descriptor
        else {
            panic!("Array.prototype[Symbol.unscopables] must be a data property");
        };
        assert!(
            !writable,
            "Array.prototype[Symbol.unscopables] must be non-writable"
        );
        assert!(
            !enumerable,
            "Array.prototype[Symbol.unscopables] must be non-enumerable"
        );
        assert!(
            configurable,
            "Array.prototype[Symbol.unscopables] must be configurable"
        );
        assert_eq!(
            machine.internal_get_prototype_of(unscopables).unwrap(),
            None,
            "unscopables object must have a null prototype"
        );
        let names = [
            "at",
            "copyWithin",
            "entries",
            "fill",
            "find",
            "findIndex",
            "findLast",
            "findLastIndex",
            "flat",
            "flatMap",
            "includes",
            "keys",
            "toReversed",
            "toSorted",
            "toSpliced",
            "values",
        ];
        for name in names {
            let entry = machine
                .get_named_property(unscopables, name)
                .unwrap_or_else(|_| panic!("{name} must be present on unscopables"));
            assert_eq!(entry, Value::TRUE, "{name} must be true");
            let entry_key = PropertyKey::Named(machine.intern_str(name));
            let entry_descriptor = machine
                .own_descriptor(unscopables, &entry_key)
                .expect("entry descriptor lookup succeeds")
                .unwrap_or_else(|| panic!("{name} must have an own descriptor"));
            assert!(
                matches!(
                    entry_descriptor,
                    Property::Data {
                        value: Value::TRUE,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    }
                ),
                "{name} must be a CreateDataProperty true entry"
            );
        }
        let expected: Vec<_> = names
            .into_iter()
            .map(|name| PropertyKey::Named(machine.intern_str(name)))
            .collect();
        assert_eq!(
            machine.own_property_keys(unscopables).unwrap(),
            expected,
            "unscopables own keys must be exactly the standard entry set"
        );
    }

    // ---- iterator factory regression tests --------------------------------

    /// Calls an `Array.prototype` method (e.g. `keys`, `values`, `entries`)
    /// on `this_array` and returns the result.
    fn call_proto(
        machine: &mut Machine<'_, TestHost>,
        method_name: &str,
        this_array: Value,
    ) -> Value {
        let proto = machine.intrinsics.array_prototype;
        let method = machine.get_named_property(proto, method_name).unwrap();
        machine.call_value(method, this_array, &[]).unwrap()
    }

    /// Drives `iterator`'s `next()` once and returns `(done, value)`.
    fn iter_next(machine: &mut Machine<'_, TestHost>, iterator: Value) -> (bool, Value) {
        let next_fn = machine.get_named_property(iterator, "next").unwrap();
        let result = machine.call_value(next_fn, iterator, &[]).unwrap();
        let done = machine.get_named_property(result, "done").unwrap();
        let value = machine.get_named_property(result, "value").unwrap();
        let is_done = matches!(done.decode(), Some(Decoded::Boolean(true)));
        (is_done, value)
    }

    #[test]
    fn keys_iterator_order_and_holes() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // [1, <hole>, 3] — holes still produce a key index.
        let array = allocate_array(
            &mut machine,
            vec![Value::int32(1), Value::HOLE, Value::int32(3)],
        )
        .unwrap();

        let iter = call_proto(&mut machine, "keys", array);
        let (done, v0) = iter_next(&mut machine, iter);
        assert!(!done);
        assert!(matches!(v0.decode(), Some(Decoded::Int32(n)) if n == 0));
        let (done, v1) = iter_next(&mut machine, iter);
        assert!(!done);
        assert!(matches!(v1.decode(), Some(Decoded::Int32(n)) if n == 1));
        let (done, v2) = iter_next(&mut machine, iter);
        assert!(!done);
        assert!(matches!(v2.decode(), Some(Decoded::Int32(n)) if n == 2));
        let (done, _) = iter_next(&mut machine, iter);
        assert!(done);
    }

    #[test]
    fn values_iterator_order_and_holes() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // [1, <hole>, 3] — the hole yields `undefined`, not skipped.
        let array = allocate_array(
            &mut machine,
            vec![Value::int32(1), Value::HOLE, Value::int32(3)],
        )
        .unwrap();

        let iter = call_proto(&mut machine, "values", array);
        let (done, v0) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v0, Value::int32(1));
        let (done, v1) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v1, Value::UNDEFINED);
        let (done, v2) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v2, Value::int32(3));
        let (done, _) = iter_next(&mut machine, iter);
        assert!(done);
    }

    #[test]
    fn entries_iterator_order_and_holes() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // [1, <hole>, 3] — entries yield [index, value] including the hole.
        let array = allocate_array(
            &mut machine,
            vec![Value::int32(1), Value::HOLE, Value::int32(3)],
        )
        .unwrap();

        let iter = call_proto(&mut machine, "entries", array);

        let (done, entry) = iter_next(&mut machine, iter);
        assert!(!done);
        let pair = machine.array_elements(entry).unwrap().unwrap();
        assert!(matches!(pair[0].decode(), Some(Decoded::Int32(n)) if n == 0));
        assert_eq!(pair[1], Value::int32(1));

        let (done, entry) = iter_next(&mut machine, iter);
        assert!(!done);
        let pair = machine.array_elements(entry).unwrap().unwrap();
        assert!(matches!(pair[0].decode(), Some(Decoded::Int32(n)) if n == 1));
        assert_eq!(pair[1], Value::UNDEFINED);

        let (done, entry) = iter_next(&mut machine, iter);
        assert!(!done);
        let pair = machine.array_elements(entry).unwrap().unwrap();
        assert!(matches!(pair[0].decode(), Some(Decoded::Int32(n)) if n == 2));
        assert_eq!(pair[1], Value::int32(3));

        let (done, _) = iter_next(&mut machine, iter);
        assert!(done);
    }

    fn call_prototype(
        machine: &mut Machine<'_, TestHost>,
        name: &str,
        this: Value,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let proto = machine.intrinsics.array_prototype;
        let method = machine.get_named_property(proto, name)?;
        machine.call_value(method, this, args)
    }

    #[test]
    fn array_methods_read_any_object_with_a_length() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let like = ordinary_object(&mut machine);
        machine
            .set_data_property(like, "0", Value::int32(7))
            .unwrap();
        machine
            .set_data_property(like, "2", Value::int32(9))
            .unwrap();
        machine
            .set_data_property(like, "length", Value::int32(3))
            .unwrap();

        assert_eq!(
            elements(&mut machine, like).unwrap(),
            [Value::int32(7), Value::HOLE, Value::int32(9)],
            "a missing index is a hole, not undefined"
        );
        assert_eq!(
            call_prototype(&mut machine, "indexOf", like, &[Value::int32(9)]).unwrap(),
            Value::int32(2)
        );
    }

    #[test]
    fn array_mutators_write_back_to_any_object_with_a_length() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let like = ordinary_object(&mut machine);
        machine
            .set_data_property(like, "0", Value::int32(1))
            .unwrap();
        machine
            .set_data_property(like, "1", Value::int32(2))
            .unwrap();
        machine
            .set_data_property(like, "length", Value::int32(2))
            .unwrap();

        call_prototype(&mut machine, "push", like, &[Value::int32(3)]).unwrap();
        assert_eq!(
            machine.get_named_property(like, "2").unwrap(),
            Value::int32(3)
        );
        assert_eq!(
            machine.get_named_property(like, "length").unwrap(),
            Value::int32(3)
        );

        let popped = call_prototype(&mut machine, "pop", like, &[]).unwrap();
        assert_eq!(popped, Value::int32(3));
        let key = index_key(&mut machine.atoms, 2);
        assert!(
            !machine.internal_has_property(like, &key).unwrap(),
            "a removed element is deleted"
        );
        assert_eq!(
            machine.get_named_property(like, "length").unwrap(),
            Value::int32(2)
        );
    }

    #[test]
    fn an_absurd_array_like_length_is_refused_before_allocating() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let like = ordinary_object(&mut machine);
        machine
            .set_data_property(like, "length", crate::number_value(9_007_199_254_740_991.0))
            .unwrap();
        assert!(elements(&mut machine, like).is_err());
    }

    #[test]
    fn iterators_accept_array_like_receivers_and_read_live_length() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for method in ["keys", "values", "entries"] {
            let source = ordinary_object(&mut machine);
            machine
                .set_data_property(source, "length", Value::int32(1))
                .unwrap();
            machine
                .set_data_property(source, "0", Value::int32(7))
                .unwrap();
            let iterator = call_proto(&mut machine, method, source);
            for (index, expected) in [(0, 7), (1, 9)] {
                let (done, value) = iter_next(&mut machine, iterator);
                assert!(!done, "{method} must visit index {index}");
                match method {
                    "keys" => assert_eq!(value, Value::int32(index)),
                    "values" => assert_eq!(value, Value::int32(expected)),
                    "entries" => assert_eq!(
                        machine.array_elements(value).unwrap().unwrap(),
                        [Value::int32(index), Value::int32(expected)]
                    ),
                    _ => unreachable!(),
                }
                machine
                    .set_data_property(source, "length", Value::int32(2))
                    .unwrap();
                machine
                    .set_data_property(source, "1", Value::int32(9))
                    .unwrap();
            }
            assert!(iter_next(&mut machine, iterator).0);
            machine
                .set_data_property(source, "length", Value::int32(3))
                .unwrap();
            assert!(
                iter_next(&mut machine, iterator).0,
                "exhaustion is permanent"
            );
        }
    }

    #[test]
    fn iterators_box_primitives_and_reject_nullish_receivers() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for method in ["keys", "values", "entries"] {
            for receiver in [Value::NULL, Value::UNDEFINED] {
                assert!(matches!(
                    call_prototype(&mut machine, method, receiver, &[]),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
                ));
            }
            let iterator = call_proto(&mut machine, method, Value::int32(7));
            assert!(iter_next(&mut machine, iterator).0);
        }

        let string =
            allocate_string(&mut machine, EcmaString::from_units(&[0xd83d, 0xde00])).unwrap();
        let iterator = call_proto(&mut machine, "values", string);
        for unit in [0xd83d, 0xde00] {
            let (done, value) = iter_next(&mut machine, iterator);
            assert!(!done);
            assert_eq!(machine.string_value(value).unwrap().as_units(), [unit]);
        }
        assert!(iter_next(&mut machine, iterator).0);
    }

    #[test]
    fn iterators_read_array_accessors_and_inherited_indices() {
        fn getter(
            _machine: &mut Machine<'_, TestHost>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            log_event("index");
            Ok(BuiltinOutcome::Value(Value::int32(9)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = allocate_array(&mut machine, vec![Value::HOLE; 2]).unwrap();
        let prototype = ordinary_object(&mut machine);
        machine
            .set_data_property(prototype, "0", Value::int32(7))
            .unwrap();
        machine.set_prototype(source, prototype).unwrap();
        let getter = native(&mut machine, "iterator index", getter);
        let key = index_key(&mut machine.atoms, 1);
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();

        clear_log();
        let keys = call_proto(&mut machine, "keys", source);
        assert_eq!(iter_next(&mut machine, keys), (false, Value::int32(0)));
        assert_eq!(iter_next(&mut machine, keys), (false, Value::int32(1)));
        assert!(
            get_log().is_empty(),
            "keys must not read an indexed property"
        );
        let values = call_proto(&mut machine, "values", source);
        assert_eq!(iter_next(&mut machine, values), (false, Value::int32(7)));
        assert_eq!(iter_next(&mut machine, values), (false, Value::int32(9)));
        assert_eq!(get_log(), ["index"]);
    }

    #[test]
    fn array_iterators_keep_their_brand_on_map_and_proxy_receivers() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map_constructor = machine.intrinsics.global("Map").unwrap();
        let map = machine.construct_value(map_constructor, &[]).unwrap();
        machine
            .set_data_property(map, "length", Value::int32(1))
            .unwrap();
        machine
            .set_data_property(map, "0", Value::int32(7))
            .unwrap();
        let handler = ordinary_object(&mut machine);
        let proxy_constructor = machine.intrinsics.global("Proxy").unwrap();
        let proxy = machine
            .construct_value(proxy_constructor, &[map, handler])
            .unwrap();
        let array_prototype = machine
            .intrinsics
            .builtins
            .iterator_family_prototype(crate::intrinsics::IteratorFamily::Array);
        let array_next = machine.get_named_property(array_prototype, "next").unwrap();
        for source in [map, proxy] {
            let iterator = call_proto(&mut machine, "values", source);
            assert_eq!(
                machine.get_named_property(iterator, "next").unwrap(),
                array_next
            );
            assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
            assert!(iter_next(&mut machine, iterator).0);
        }
    }

    #[test]
    fn iterator_advances_before_an_index_getter_throws() {
        fn getter(
            _machine: &mut Machine<'_, TestHost>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            Err(EvalFailure::ThrowValue(Value::int32(99)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = allocate_array(&mut machine, vec![Value::HOLE, Value::int32(7)]).unwrap();
        let getter = native(&mut machine, "throwing iterator index", getter);
        let key = index_key(&mut machine.atoms, 0);
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();
        let iterator = call_proto(&mut machine, "values", source);
        let next = machine.get_named_property(iterator, "next").unwrap();
        assert!(matches!(
            machine.call_value(next, iterator, &[]),
            Err(EvalFailure::ThrowValue(value)) if value == Value::int32(99)
        ));
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
        assert!(iter_next(&mut machine, iterator).0);
    }

    #[test]
    fn iterator_retries_a_throwing_length_getter_without_advancing() {
        fn length(
            _machine: &mut Machine<'_, TestHost>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            log_event("length");
            if get_log().len() == 1 {
                return Err(EvalFailure::ThrowValue(Value::int32(99)));
            }
            Ok(BuiltinOutcome::Value(Value::int32(1)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = ordinary_object(&mut machine);
        machine
            .set_data_property(source, "0", Value::int32(7))
            .unwrap();
        let getter = native(&mut machine, "throwing iterator length", length);
        let key = PropertyKey::Named(machine.intern_str("length"));
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();
        clear_log();
        let iterator = call_proto(&mut machine, "values", source);
        assert!(
            get_log().is_empty(),
            "creating an iterator must not read length"
        );
        let next = machine.get_named_property(iterator, "next").unwrap();
        assert!(matches!(
            machine.call_value(next, iterator, &[]),
            Err(EvalFailure::ThrowValue(value)) if value == Value::int32(99)
        ));
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
        assert!(iter_next(&mut machine, iterator).0);
        assert!(iter_next(&mut machine, iterator).0);
        assert_eq!(get_log(), ["length", "length", "length"]);
    }

    #[test]
    fn iterator_captures_the_cursor_before_a_reentrant_length_getter() {
        fn length(
            machine: &mut Machine<'_, TestHost>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            if machine.get_named_property(this, "entered")? != Value::TRUE {
                machine.set_data_property(this, "entered", Value::TRUE)?;
                let iterator = machine.get_named_property(this, "iterator")?;
                let next = machine.get_named_property(iterator, "next")?;
                machine.call_value(next, iterator, &[])?;
            }
            Ok(BuiltinOutcome::Value(Value::int32(2)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = ordinary_object(&mut machine);
        machine
            .set_data_property(source, "0", Value::int32(7))
            .unwrap();
        machine
            .set_data_property(source, "1", Value::int32(9))
            .unwrap();
        let getter = native(&mut machine, "reentrant iterator length", length);
        let key = PropertyKey::Named(machine.intern_str("length"));
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();
        let iterator = call_proto(&mut machine, "values", source);
        machine
            .set_data_property(source, "iterator", iterator)
            .unwrap();
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(9)));
        assert!(iter_next(&mut machine, iterator).0);
    }

    #[test]
    fn iterator_preserves_reentrant_advancement_and_gc_roots() {
        fn getter(
            machine: &mut Machine<'_, TestHost>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            machine.collect_garbage();
            let iterator = machine.get_named_property(this, "iterator")?;
            let next = machine.get_named_property(iterator, "next")?;
            let result = machine.call_value(next, iterator, &[])?;
            Ok(BuiltinOutcome::Value(
                machine.get_named_property(result, "value")?,
            ))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = allocate_array(&mut machine, vec![Value::HOLE, Value::int32(7)]).unwrap();
        let getter = native(&mut machine, "reentrant iterator index", getter);
        let key = index_key(&mut machine.atoms, 0);
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();
        let iterator = call_proto(&mut machine, "values", source);
        machine
            .set_data_property(source, "iterator", iterator)
            .unwrap();
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
        assert!(
            iter_next(&mut machine, iterator).0,
            "the inner next consumed index 1"
        );
    }

    #[test]
    fn iterator_stays_exhausted_after_a_reentrant_length_getter() {
        fn length(
            machine: &mut Machine<'_, TestHost>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            if machine.get_named_property(this, "entered")? == Value::TRUE {
                return Ok(BuiltinOutcome::Value(Value::int32(0)));
            }
            machine.set_data_property(this, "entered", Value::TRUE)?;
            let iterator = machine.get_named_property(this, "iterator")?;
            let next = machine.get_named_property(iterator, "next")?;
            let result = machine.call_value(next, iterator, &[])?;
            assert_eq!(machine.get_named_property(result, "done")?, Value::TRUE);
            machine.collect_garbage();
            Ok(BuiltinOutcome::Value(Value::int32(2)))
        }

        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let source = ordinary_object(&mut machine);
        machine
            .set_data_property(source, "0", Value::int32(7))
            .unwrap();
        let getter = native(&mut machine, "exhausting iterator length", length);
        let key = PropertyKey::Named(machine.intern_str("length"));
        machine
            .define_accessor(source, key, getter, crate::AccessorKind::Getter)
            .unwrap();
        let iterator = call_proto(&mut machine, "values", source);
        machine
            .set_data_property(source, "iterator", iterator)
            .unwrap();
        assert_eq!(iter_next(&mut machine, iterator), (false, Value::int32(7)));
        assert!(iter_next(&mut machine, iterator).0);
        assert!(iter_next(&mut machine, iterator).0);
    }

    #[test]
    fn values_iterator_observes_mutation_during_iteration() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let array = allocate_array(
            &mut machine,
            vec![Value::int32(10), Value::int32(20), Value::int32(30)],
        )
        .unwrap();

        let iter = call_proto(&mut machine, "values", array);

        // Consume first element (10).
        let (done, v0) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v0, Value::int32(10));

        // Mutate index 1 from 20 to 99 — the iterator must see 99, not 20.
        machine
            .set_data_property(array, "1", Value::int32(99))
            .unwrap();

        let (done, v1) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v1, Value::int32(99));

        let (done, v2) = iter_next(&mut machine, iter);
        assert!(!done);
        assert_eq!(v2, Value::int32(30));

        let (done, _) = iter_next(&mut machine, iter);
        assert!(done);
    }

    fn custom_join<H: Host>(
        machine: &mut Machine<'_, H>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("custom"),
        )?))
    }

    fn join_length_getter<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "length", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("mutated"),
        )?))
    }

    #[test]
    fn join_snapshots_length_and_reads_each_index_dynamically() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let array = allocate_array(
            &mut machine,
            vec![Value::int32(1), Value::HOLE, Value::int32(3)],
        )
        .unwrap();

        let getter_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "join length getter",
            length: 0,
            handler: join_length_getter::<TestHost>,
        });
        let getter = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            getter_id,
            "join length getter",
            0,
        );

        let key = PropertyKey::Named(machine.intern_str("1"));
        machine
            .define_accessor(array, key, getter, crate::AccessorKind::Getter)
            .unwrap();

        let result = call_proto(&mut machine, "join", array);
        let text = machine.string_value(result).expect("join returns a string");
        assert_eq!(text, EcmaString::encode("1,mutated,"));
    }

    #[test]
    fn to_string_uses_dynamic_join_and_object_fallback() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let array = allocate_array(&mut machine, vec![Value::int32(1), Value::int32(2)]).unwrap();

        let result = call_proto(&mut machine, "toString", array);
        assert!(
            machine
                .string_value(result)
                .is_some_and(|text| text.eq_ascii("1,2"))
        );

        let custom_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "custom join",
            length: 0,
            handler: custom_join::<TestHost>,
        });
        let custom = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            custom_id,
            "custom join",
            0,
        );
        machine.set_data_property(array, "join", custom).unwrap();
        let result = call_proto(&mut machine, "toString", array);
        assert!(
            machine
                .string_value(result)
                .is_some_and(|text| text.eq_ascii("custom"))
        );

        machine
            .set_data_property(array, "join", Value::int32(0))
            .unwrap();
        let result = call_proto(&mut machine, "toString", array);
        assert!(
            machine
                .string_value(result)
                .is_some_and(|text| text.eq_ascii("[object Array]"))
        );
    }
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

    fn native_with_length(
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
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            length,
        )
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
                    kind: ArrayElementKind::for_elements(&[Value::HOLE; 3]),
                    elements: vec![Value::HOLE; 3],
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap();
            let predicate = native_with_length(machine, "is seven", 1, is_seven::<TestHost>);
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
            let predicate =
                native_with_length(machine, "mutate and match", 3, mutate_and_match::<TestHost>);
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
            let comparator =
                native_with_length(machine, "compare tens", 2, compare_tens::<TestHost>);
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

            let abrupt =
                native_with_length(machine, "throwing comparator", 2, throwing::<TestHost>);
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
            let length_getter =
                native_with_length(machine, "length getter", 0, record_length::<TestHost>);
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
                let value_of =
                    native_with_length(machine, "valueOf", 0, record_value_of::<TestHost>);
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
            let getter = native_with_length(machine, "throwing getter", 0, throwing::<TestHost>);
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
                    kind: ArrayElementKind::for_elements(&[Value::HOLE; 3]),
                    elements: vec![Value::HOLE; 3],
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap();
            let trap = native_with_length(
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
            let trap = native_with_length(machine, "unexpected setter", 1, throwing::<TestHost>);
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
            let trap = native_with_length(machine, "abrupt operation", 0, throwing::<TestHost>);
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
            let length_getter =
                native_with_length(machine, "length getter", 0, record_length::<TestHost>);
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
            install_change_by_copy_and_from_async(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
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
        install_change_by_copy_and_from_async(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
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
        let next = native_with_length(machine, "async next", 0, async_next_oneshot::<TestHost>);
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
        let self_target =
            native_with_length(machine, "iterator self", 0, iterator_self::<TestHost>);
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
        let next = native_with_length(machine, "sync next", 0, sync_next::<TestHost>);
        let iterable = ordinary_object(machine);
        machine
            .set_data_property(iterable, "_i", Value::int32(0))
            .unwrap();
        let backing = allocate_array(machine, values).unwrap();
        machine
            .set_data_property(iterable, "_values", backing)
            .unwrap();
        machine.set_data_property(iterable, "next", next).unwrap();
        let self_target =
            native_with_length(machine, "sync iterator self", 0, iterator_self::<TestHost>);
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
            let mapper = native_with_length(
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
            let then = native_with_length(machine, "thenable then", 2, then_resolve_42::<TestHost>);
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
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            1,
        )
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

    fn array_like_with_length(machine: &mut Machine<'_, TestHost>, length: Value) -> Value {
        let target = ordinary_object(machine);
        machine.set_data_property(target, "length", length).unwrap();
        target
    }

    fn proxy_with_has_trap(
        machine: &mut Machine<'_, TestHost>,
        target: Value,
        trap: Value,
    ) -> Value {
        let handler = ordinary_object(machine);
        machine.set_data_property(handler, "has", trap).unwrap();
        super::super::proxy::create(machine, target, handler).unwrap()
    }

    fn cancel_on_call(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.cancel.cancel();
        Ok(BuiltinOutcome::Value(Value::TRUE))
    }

    /// A claimed length with a native `has` trap and a native callback: no user
    /// code runs, so the loop itself is the only thing that can stop it.
    #[test]
    fn a_present_element_with_a_native_callback_still_charges_fuel() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let limits = Limits {
            fuel: 4,
            ..Limits::default()
        };
        let mut machine = Machine::new(&module, &mut host, limits);
        let target = array_like_with_length(&mut machine, Value::int32(8));
        let has = machine.intrinsics.global("Boolean").unwrap();
        let proxy = proxy_with_has_trap(&mut machine, target, has);
        let math = machine.intrinsics.global("Math").unwrap();
        let abs = machine.get_named_property(math, "abs").unwrap();
        assert!(matches!(
            invoke(&mut machine, proxy, "forEach", &[abs]),
            Err(EvalFailure::Runtime(RuntimeErrorKind::FuelExhausted {
                limit: 4
            }))
        ));
    }

    #[test]
    fn a_cancelled_iteration_stops_at_the_next_index() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let token = crate::CancellationToken::new();
        let mut machine =
            Machine::new_with_cancel(&module, &mut host, Limits::default(), token.clone());
        let target = array_like_with_length(&mut machine, Value::int32(8));
        let has = native(&mut machine, "cancel", cancel_on_call);
        let proxy = proxy_with_has_trap(&mut machine, target, has);
        let math = machine.intrinsics.global("Math").unwrap();
        let abs = machine.get_named_property(math, "abs").unwrap();
        assert!(matches!(
            invoke(&mut machine, proxy, "forEach", &[abs]),
            Err(EvalFailure::Runtime(RuntimeErrorKind::Cancelled))
        ));
    }

    fn summing_callback_program() -> Program<Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("acc")),
            Constant::String(EcmaString::encode("<test>")),
        ];
        let entry = Function::new(
            None,
            0,
            0,
            0,
            FunctionFlags::default(),
            vec![Instruction::Halt],
            Vec::new(),
        );
        let callback = Function::new(
            None,
            0,
            3,
            4,
            FunctionFlags::default(),
            vec![
                Instruction::LoadGlobal {
                    dst: Register::new(3),
                    name: ConstantId::new(0),
                },
                Instruction::Binary {
                    dst: Register::new(3),
                    op: BinaryOp::Add,
                    left: Register::new(3),
                    right: Register::new(0),
                },
                Instruction::StoreGlobal {
                    name: ConstantId::new(0),
                    value: Register::new(3),
                },
                Instruction::Return {
                    value: Register::new(3),
                },
            ],
            Vec::new(),
        );
        let code = Module::new(constants, vec![entry, callback], FunctionId::new(0))
            .verify()
            .expect("valid summing callback module");
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(1),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("valid summing callback program")
    }

    #[test]
    fn a_guest_callback_over_a_thousand_elements_completes_unchanged() {
        let program = summing_callback_program();
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.test_set_global("acc", Value::int32(0));
        let elements = (1..=1000).map(Value::int32).collect();
        let array = allocate_array(&mut machine, elements).unwrap();
        let callback = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
                captures: Vec::new(),
                context: None,
                properties: crate::PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap();
        invoke(&mut machine, array, "forEach", &[callback]).unwrap();
        assert_eq!(machine.test_global("acc"), Some(Value::int32(500_500)));
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
