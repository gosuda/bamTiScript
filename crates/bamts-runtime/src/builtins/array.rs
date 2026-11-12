use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::array_generic as generic;
use super::{allocate_string, array_es2023};
use super::{define_data, install_constructor_function, install_function, type_error};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey, PropertyMap,
};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = builtins.array_prototype();
    let constructor =
        install_constructor_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "Array", length: 1, handler: generic::constructor::<H> });
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    globals.insert(EcmaString::encode("Array"), constructor);
    for (name, length, handler) in [
        (
            "isArray",
            1,
            generic::is_array_method::<H> as BuiltinHandler<H>,
        ),
        ("from", 1, generic::from::<H>),
        ("of", 0, generic::of::<H>),
    ] {
        let function = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: name, length: length, handler: handler });
        define_static(heap, atoms, shapes, constructor, name, function);
    }
    for (name, length, handler) in [
        ("toString", 0, to_string::<H> as BuiltinHandler<H>),
        ("toLocaleString", 0, to_locale_string::<H>),
        ("copyWithin", 2, copy_within::<H>),
        ("push", 1, generic::push::<H>),
        ("pop", 0, generic::pop::<H>),
        ("shift", 0, generic::shift::<H>),
        ("unshift", 1, generic::unshift::<H>),
        ("slice", 2, generic::slice::<H>),
        ("splice", 2, generic::splice::<H>),
        ("concat", 1, generic::concat::<H>),
        ("join", 1, generic::join::<H>),
        ("indexOf", 1, generic::index_of::<H>),
        ("lastIndexOf", 1, generic::last_index_of::<H>),
        ("includes", 1, generic::includes::<H>),
        ("find", 1, generic::find::<H>),
        ("findIndex", 1, generic::find_index::<H>),
        ("filter", 1, generic::filter::<H>),
        ("map", 1, generic::map::<H>),
        ("forEach", 1, generic::for_each::<H>),
        ("reduce", 1, generic::reduce::<H>),
        ("reduceRight", 1, generic::reduce_right::<H>),
        ("some", 1, generic::some::<H>),
        ("every", 1, generic::every::<H>),
        ("sort", 1, generic::sort::<H>),
        ("reverse", 0, generic::reverse::<H>),
        ("flat", 0, generic::flat::<H>),
        ("flatMap", 1, generic::flat_map::<H>),
        ("fill", 1, generic::fill::<H>),
    ] {
        let function = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: name, length: length, handler: handler });
        define_data(heap, atoms, shapes, prototype, name, function);
    }
    let species = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get [Symbol.species]", length: 0, handler: super::regexp_protocol::species_getter::<H> });
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
    let keys = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "keys", length: 0, handler: keys_iterator::<H> });
    let values = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "values", length: 0, handler: values_iterator::<H> });
    let entries = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "entries", length: 0, handler: entries_iterator::<H> });
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
    super::array_es2023::install(heap, atoms, shapes, builtins, prototype, constructor);
}

fn define_static(
    heap: &mut [HeapEntry],
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
    let object = array_es2023::to_object(machine, this)?;
    let length = array_es2023::length_of_array_like(machine, object)?;
    // An array's length is what it already holds, however many of those are holes.
    if !is_array && length > MAX_ARRAY_LIKE_ELEMENTS {
        return Err(type_error("Array method received too long an array-like"));
    }
    let mut values = Vec::with_capacity(length);
    for index in 0..length {
        let key = array_es2023::index_key(&mut machine.atoms, index);
        values.push(if machine.internal_has_property(object, &key)? {
            machine.get_property_key(object, &key)?
        } else {
            Value::HOLE
        });
    }
    Ok(values)
}
/// Validates that `this` is an Array receiver without materializing its
/// elements. The iterator factories only need receiver validation — the
/// actual elements are read lazily by `iterator_next` — so cloning the
/// whole `Vec<Value>` (as `elements` does) is wasted allocation. Mirrors
/// `collection_slot` in `collections.rs`.
fn array_slot<H: Host>(machine: &Machine<'_, H>, object: Value) -> Result<(), EvalFailure> {
    let Some(index) = machine.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Array method called on incompatible receiver"));
    };
    if !matches!(
        machine.heap[index],
        HeapEntry::Array { .. } | HeapEntry::TypedArray { .. }
    ) {
        return Err(type_error("Array method called on incompatible receiver"));
    }
    Ok(())
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
    let object = array_es2023::to_object(machine, this)?;
    let argument = |index: usize| args.get(index).copied().unwrap_or(Value::UNDEFINED);
    let forwarded = [argument(0), argument(1)];
    let joined = super::with_roots(machine, &[object], |machine, _| {
        generic::guarded_join(machine, object, |machine| {
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
    let length = array_es2023::length_of_array_like(machine, object)?;
    let mut output = bamts_bytecode::EcmaStringBuilder::new();
    for index in 0..length {
        generic::tick(machine)?;
        if index != 0 {
            output.push_unit(u16::from(b','));
        }
        let key = array_es2023::index_key(&mut machine.atoms, index);
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
    let object = array_es2023::to_object(machine, this)?;
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
    let length = array_es2023::length_of_array_like(machine, object)?;
    let target = args.first().copied().unwrap_or(Value::UNDEFINED);
    let mut to = super::array_generic::relative_position(machine, target, length)?;
    let start = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let mut from = super::array_generic::relative_position(machine, start, length)?;
    let end = match args.get(2).copied() {
        None | Some(Value::UNDEFINED) => length,
        Some(end) => super::array_generic::relative_position(machine, end, length)?,
    };
    let mut count = end.saturating_sub(from).min(length - to);
    let backward = from < to && to < from + count;
    if backward && count > 0 {
        from += count - 1;
        to += count - 1;
    }
    while count > 0 {
        generic::tick(machine)?;
        let from_key = array_es2023::index_key(&mut machine.atoms, from);
        let to_key = array_es2023::index_key(&mut machine.atoms, to);
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
    array_slot(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Key,
    )?))
}

fn values_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    array_slot(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Value,
    )?))
}

fn entries_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    array_slot(machine, this)?;
    Ok(BuiltinOutcome::Value(super::collections::iterator(
        machine,
        this,
        IterationKind::Entry,
    )?))
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
        let comparator = native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, id, "cancel", 2);
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

    use bamts_native::Decoded;

    use super::super::allocate_array;
    use super::super::test_support::{TestHost, blank_program, custom_iterable, ordinary_object};
    use super::*;
    use crate::Limits;
    use crate::ThrowOrigin;
    use crate::intrinsics::BuiltinDef;

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
        let key = array_es2023::index_key(&mut machine.atoms, 2);
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
    fn iterator_rejects_non_array_receiver() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let obj = ordinary_object(&mut machine);
        let proto = machine.intrinsics.array_prototype;
        let method = machine.get_named_property(proto, "keys").unwrap();
        let result = machine.call_value(method, obj, &[]);
        assert!(result.is_err(), "keys() on a non-array must throw");
    }

    /// Spec: `%ArrayIteratorPrototype%.next` reads the source array live on
    /// each call, so mutations between `next()` calls are visible. The
    /// iterator captures the original length at creation time; elements
    /// added beyond that length are not visited, but in-bounds mutations
    /// are observed. Our `BuiltinIterator` reads `elements` by cursor each
    /// step, so in-bounds replacement is visible immediately.
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
}
