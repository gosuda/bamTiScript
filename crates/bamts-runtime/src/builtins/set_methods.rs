use bamts_native::{Decoded, Value};

use super::collections::append_collection_entry;
use super::{define_data, install_function, range_error, type_error};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{CollectionIndex, CollectionKind, EvalFailure, HeapEntry, Host, Machine, PropertyMap};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    set_prototype: Value,
) {
    for (name, handler) in [
        ("union", union::<H> as BuiltinHandler<H>),
        ("intersection", intersection::<H>),
        ("difference", difference::<H>),
        ("symmetricDifference", symmetric_difference::<H>),
        ("isSubsetOf", is_subset_of::<H>),
        ("isSupersetOf", is_superset_of::<H>),
        ("isDisjointFrom", is_disjoint_from::<H>),
    ] {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length: 1,
                handler,
            },
        );
        define_data(heap, atoms, shapes, set_prototype, name, function);
    }
}

#[derive(Clone, Copy)]
struct SetRecord {
    object: Value,
    size: f64,
    has: Value,
    keys: Value,
}

fn get_set_record<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
) -> Result<SetRecord, EvalFailure> {
    if !machine.is_object(object) {
        return Err(type_error("Set-like value is not an object"));
    }

    // GetSetRecord deliberately reads and validates these in this order.
    let raw_size = machine.get_named_property(object, "size")?;
    let number_size = machine.coerce_number_observable(raw_size)?;
    let number_size = match number_size.decode() {
        Some(Decoded::Int32(value)) => f64::from(value as i32),
        Some(Decoded::Number(value)) => value,
        _ => unreachable!("ToNumber returns a numeric Value"),
    };
    if number_size.is_nan() {
        return Err(type_error("Set-like size is NaN"));
    }
    let size = number_size.trunc();
    if size < 0.0 {
        return Err(range_error("Set-like size is negative"));
    }

    let has = machine.get_named_property(object, "has")?;
    if !machine.is_callable(has)? {
        return Err(type_error("Set-like has is not callable"));
    }
    let keys = machine.get_named_property(object, "keys")?;
    if !machine.is_callable(keys)? {
        return Err(type_error("Set-like keys is not callable"));
    }

    Ok(SetRecord {
        object,
        size,
        has,
        keys,
    })
}

fn require_set_slot<H: Host>(
    machine: &Machine<'_, H>,
    object: Value,
) -> Result<usize, EvalFailure> {
    let Some(slot) = machine.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Set method called on incompatible receiver"));
    };
    if !matches!(
        machine.heap[slot],
        HeapEntry::Collection {
            kind: CollectionKind::Set,
            ..
        }
    ) {
        return Err(type_error("Set method called on incompatible receiver"));
    }
    Ok(slot)
}

fn set_data_size(machine: &Machine<'_, impl Host>, set: Value) -> Result<usize, EvalFailure> {
    let slot = require_set_slot(machine, set)?;
    let HeapEntry::Collection { size, .. } = &machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    Ok(*size)
}

fn set_data_has(
    machine: &Machine<'_, impl Host>,
    set: Value,
    value: Value,
) -> Result<bool, EvalFailure> {
    let slot = require_set_slot(machine, set)?;
    let HeapEntry::Collection { entries, index, .. } = &machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    Ok(index
        .get(machine, entries, canonicalize_key(value))
        .is_some())
}

fn next_set_value(
    machine: &Machine<'_, impl Host>,
    set: Value,
    cursor: u64,
) -> Result<Option<(u64, Value)>, EvalFailure> {
    let slot = require_set_slot(machine, set)?;
    let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    let index = entries.partition_point(|entry| entry.order < cursor);
    Ok(entries[index..]
        .iter()
        .find(|entry| entry.live)
        .map(|entry| {
            (
                entry
                    .order
                    .checked_add(1)
                    .expect("heap limits keep collection order below u64::MAX"),
                entry.key,
            )
        }))
}

fn canonicalize_key(value: Value) -> Value {
    match value.decode() {
        Some(Decoded::Number(0.0)) => Value::number(0.0),
        _ => value,
    }
}

fn create_result_set<H: Host>(machine: &mut Machine<'_, H>) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Collection {
            kind: CollectionKind::Set,
            entries: Vec::new(),
            index: CollectionIndex::default(),
            size: 0,
            next_order: 0,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.builtins.set_prototype()),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

fn copy_set_data<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
) -> Result<Value, EvalFailure> {
    let result = create_result_set(machine)?;
    let result_slot = require_set_slot(machine, result)?;
    let mut cursor = 0;
    while let Some((next, value)) = next_set_value(machine, source, cursor)? {
        cursor = next;
        let value = canonicalize_key(value);
        append_collection_entry(machine, result_slot, value, value)?;
    }
    Ok(result)
}

fn add_to_set<H: Host>(
    machine: &mut Machine<'_, H>,
    set: Value,
    value: Value,
) -> Result<(), EvalFailure> {
    let value = canonicalize_key(value);
    let slot = require_set_slot(machine, set)?;
    let exists = {
        let HeapEntry::Collection { entries, index, .. } = &machine.heap[slot] else {
            unreachable!("Set brand was checked")
        };
        index.get(machine, entries, value).is_some()
    };
    if !exists {
        append_collection_entry(machine, slot, value, value)?;
    }
    Ok(())
}

fn delete_from_set<H: Host>(
    machine: &mut Machine<'_, H>,
    set: Value,
    value: Value,
) -> Result<bool, EvalFailure> {
    let slot = require_set_slot(machine, set)?;
    let value = canonicalize_key(value);
    let entry_index = {
        let HeapEntry::Collection { entries, index, .. } = &machine.heap[slot] else {
            unreachable!("Set brand was checked")
        };
        index.get(machine, entries, value)
    };
    let Some(entry_index) = entry_index else {
        return Ok(false);
    };

    let HeapEntry::Collection { entries, size, .. } = &mut machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    entries.remove(entry_index);
    *size -= 1;

    let mut rebuilt = CollectionIndex::default();
    let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    for (index, entry) in entries.iter().enumerate() {
        rebuilt.insert(crate::collection_key_hash(machine, entry.key), index);
    }
    let HeapEntry::Collection { index, .. } = &mut machine.heap[slot] else {
        unreachable!("Set brand was checked")
    };
    *index = rebuilt;
    machine.refund_slot(
        slot,
        crate::CollectionEntry::BYTES + crate::CollectionIndex::ENTRY_BYTES,
    );
    Ok(true)
}

fn call_has<H: Host>(
    machine: &mut Machine<'_, H>,
    record: SetRecord,
    value: Value,
) -> Result<bool, EvalFailure> {
    let result = machine.call_value(record.has, record.object, &[value])?;
    Ok(machine.truthy(result))
}

fn keys_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    record: SetRecord,
) -> Result<Value, EvalFailure> {
    let iterator = machine.call_value(record.keys, record.object, &[])?;
    if !machine.is_object(iterator) {
        return Err(type_error("Set-like keys returned a non-object"));
    }
    let next = machine.get_named_property(iterator, "next")?;
    machine.create_protocol_iterator(iterator, next)
}

fn iterator_step_value<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<Option<Value>, EvalFailure> {
    let result = machine.iterator_step(iterator)?;
    let (done, value) = machine.iterator_result_parts(result)?;
    Ok((!done).then_some(value))
}

fn close_iterator_for_early_return<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
) -> Result<(), EvalFailure> {
    let Some(target) = machine.iterator_close_target(iterator)? else {
        return Ok(());
    };
    let close = machine.get_named_property(target, "return")?;
    if matches!(close.decode(), Some(Decoded::Undefined | Decoded::Null)) {
        return Ok(());
    }
    if !machine.is_callable(close)? {
        return Err(type_error("Iterator return is not callable"));
    }
    let result = machine.call_value(close, target, &[])?;
    if !machine.is_object(result) {
        return Err(type_error("Iterator return returned a non-object"));
    }
    Ok(())
}

fn union<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let iterator = keys_iterator(machine, other)?;
    let result = copy_set_data(machine, this)?;
    while let Some(value) = iterator_step_value(machine, iterator)? {
        add_to_set(machine, result, value)?;
    }
    Ok(BuiltinOutcome::Value(result))
}

fn intersection<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let result = create_result_set(machine)?;
    if (set_data_size(machine, this)? as f64) <= other.size {
        let mut cursor = 0;
        while let Some((next, value)) = next_set_value(machine, this, cursor)? {
            cursor = next;
            if call_has(machine, other, value)? {
                add_to_set(machine, result, value)?;
            }
        }
    } else {
        let iterator = keys_iterator(machine, other)?;
        while let Some(value) = iterator_step_value(machine, iterator)? {
            let value = canonicalize_key(value);
            if set_data_has(machine, this, value)? {
                add_to_set(machine, result, value)?;
            }
        }
    }
    Ok(BuiltinOutcome::Value(result))
}

fn difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let result = copy_set_data(machine, this)?;
    if (set_data_size(machine, this)? as f64) <= other.size {
        let mut cursor = 0;
        while let Some((next, value)) = next_set_value(machine, result, cursor)? {
            cursor = next;
            if call_has(machine, other, value)? {
                delete_from_set(machine, result, value)?;
            }
        }
    } else {
        let iterator = keys_iterator(machine, other)?;
        while let Some(value) = iterator_step_value(machine, iterator)? {
            delete_from_set(machine, result, canonicalize_key(value))?;
        }
    }
    Ok(BuiltinOutcome::Value(result))
}

fn symmetric_difference<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    let iterator = keys_iterator(machine, other)?;
    let result = copy_set_data(machine, this)?;
    while let Some(value) = iterator_step_value(machine, iterator)? {
        let value = canonicalize_key(value);
        let already_in_result = set_data_has(machine, result, value)?;
        if set_data_has(machine, this, value)? {
            if already_in_result {
                delete_from_set(machine, result, value)?;
            }
        } else if !already_in_result {
            add_to_set(machine, result, value)?;
        }
    }
    Ok(BuiltinOutcome::Value(result))
}

fn is_subset_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if (set_data_size(machine, this)? as f64) > other.size {
        return Ok(BuiltinOutcome::Value(Value::FALSE));
    }
    let mut cursor = 0;
    while let Some((next, value)) = next_set_value(machine, this, cursor)? {
        cursor = next;
        if !call_has(machine, other, value)? {
            return Ok(BuiltinOutcome::Value(Value::FALSE));
        }
    }
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn is_superset_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if (set_data_size(machine, this)? as f64) < other.size {
        return Ok(BuiltinOutcome::Value(Value::FALSE));
    }
    let iterator = keys_iterator(machine, other)?;
    while let Some(value) = iterator_step_value(machine, iterator)? {
        if !set_data_has(machine, this, canonicalize_key(value))? {
            close_iterator_for_early_return(machine, iterator)?;
            return Ok(BuiltinOutcome::Value(Value::FALSE));
        }
    }
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn is_disjoint_from<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    require_set_slot(machine, this)?;
    let other = get_set_record(machine, args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if (set_data_size(machine, this)? as f64) <= other.size {
        let mut cursor = 0;
        while let Some((next, value)) = next_set_value(machine, this, cursor)? {
            cursor = next;
            if call_has(machine, other, value)? {
                return Ok(BuiltinOutcome::Value(Value::FALSE));
            }
        }
    } else {
        let iterator = keys_iterator(machine, other)?;
        while let Some(value) = iterator_step_value(machine, iterator)? {
            if set_data_has(machine, this, canonicalize_key(value))? {
                close_iterator_for_early_return(machine, iterator)?;
                return Ok(BuiltinOutcome::Value(Value::FALSE));
            }
        }
    }
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{NativeCallable, Property, PropertyKey, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = blank_program("set-methods");
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, crate::Limits::default());
        test(&mut machine);
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
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            length,
        )
    }

    fn make_set(machine: &mut Machine<'_, TestHost>, values: &[Value]) -> Value {
        let set = create_result_set(machine).unwrap();
        for value in values {
            add_to_set(machine, set, *value).unwrap();
        }
        set
    }

    fn set_values(machine: &Machine<'_, TestHost>, set: Value) -> Vec<Value> {
        let slot = require_set_slot(machine, set).unwrap();
        let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
            unreachable!()
        };
        entries
            .iter()
            .filter(|entry| entry.live)
            .map(|entry| entry.key)
            .collect()
    }

    fn call_method(
        machine: &mut Machine<'_, TestHost>,
        set: Value,
        name: &str,
        other: Value,
    ) -> Result<Value, EvalFailure> {
        let method = machine.get_named_property(set, name)?;
        machine.call_value(method, set, &[other])
    }

    fn counter(machine: &mut Machine<'_, TestHost>, object: Value, name: &str) -> u32 {
        match machine.get_named_property(object, name).unwrap().decode() {
            Some(Decoded::Int32(value)) => value,
            _ => panic!("{name} is an integer counter"),
        }
    }

    fn increment(
        machine: &mut Machine<'_, TestHost>,
        object: Value,
        name: &str,
    ) -> Result<(), EvalFailure> {
        let next = match machine.get_named_property(object, name)?.decode() {
            Some(Decoded::Int32(value)) => value + 1,
            _ => 1,
        };
        machine.set_data_property(object, name, Value::int32(next))
    }

    fn test_has(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        increment(machine, this, "_hasCalls")?;
        let mutated = machine.get_named_property(this, "_mutated")?;
        if !machine.truthy(mutated) {
            let target = machine.get_named_property(this, "_mutateTarget")?;
            let value = machine.get_named_property(this, "_mutateValue")?;
            if target != Value::UNDEFINED {
                add_to_set(machine, target, value)?;
                machine.set_data_property(this, "_mutated", Value::TRUE)?;
            }
        }
        let members = machine.get_named_property(this, "_members")?;
        let value = args.first().copied().unwrap_or(Value::UNDEFINED);
        Ok(BuiltinOutcome::Value(Value::boolean(set_data_has(
            machine, members, value,
        )?)))
    }

    fn test_keys(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        increment(machine, this, "_keysCalls")?;
        let iterator = ordinary_object(machine);
        for (name, value) in [
            ("_owner", this),
            ("_values", machine.get_named_property(this, "_values")?),
            ("_index", Value::int32(0)),
            ("next", machine.get_named_property(this, "_next")?),
            ("return", machine.get_named_property(this, "_return")?),
        ] {
            machine.set_data_property(iterator, name, value)?;
        }
        Ok(BuiltinOutcome::Value(iterator))
    }

    fn test_next(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let index = match machine.get_named_property(this, "_index")?.decode() {
            Some(Decoded::Int32(value)) => value as usize,
            _ => 0,
        };
        let values = machine.get_named_property(this, "_values")?;
        let value = machine
            .array_elements(values)?
            .unwrap_or_default()
            .get(index)
            .copied();
        let Some(value) = value else {
            return Ok(BuiltinOutcome::Value(
                machine.iterator_result(Value::UNDEFINED, true)?,
            ));
        };
        machine.set_data_property(this, "_index", Value::int32((index + 1) as u32))?;
        Ok(BuiltinOutcome::Value(
            machine.iterator_result(value, false)?,
        ))
    }

    fn test_return(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_returnCalls")?;
        machine.set_data_property(owner, "_closed", Value::TRUE)?;
        Ok(BuiltinOutcome::Value(ordinary_object(machine)))
    }

    fn abrupt_next(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("abrupt iterator next"))
    }

    fn abrupt_return(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_returnCalls")?;
        Err(type_error("abrupt iterator return"))
    }

    fn primitive_return(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_returnCalls")?;
        Ok(BuiltinOutcome::Value(Value::int32(0)))
    }
    fn ordered_iterator_keys(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        increment(machine, this, "_keysCalls")?;
        let iterator = ordinary_object(machine);
        for (name, value) in [
            ("_owner", this),
            ("_values", machine.get_named_property(this, "_values")?),
            ("_index", Value::int32(0)),
        ] {
            machine.set_data_property(iterator, name, value)?;
        }
        let next_getter = machine.get_named_property(this, "_nextGetter")?;
        define_getter(machine, iterator, "next", next_getter);
        Ok(BuiltinOutcome::Value(iterator))
    }

    fn ordered_iterator_next_getter(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_iteratorStage")?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(owner, "_orderedNext")?,
        ))
    }

    fn ordered_iterator_next(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_iteratorStage")?;
        let index = match machine.get_named_property(this, "_index")?.decode() {
            Some(Decoded::Int32(value)) => value as usize,
            _ => 0,
        };
        let values = machine.get_named_property(this, "_values")?;
        let value = machine
            .array_elements(values)?
            .unwrap_or_default()
            .get(index)
            .copied();
        if value.is_some() {
            machine.set_data_property(this, "_index", Value::int32((index + 1) as u32))?;
        }

        let result = ordinary_object(machine);
        for (name, property) in [
            ("_owner", owner),
            ("_done", Value::boolean(value.is_none())),
            ("_value", value.unwrap_or(Value::UNDEFINED)),
        ] {
            machine.set_data_property(result, name, property)?;
        }
        let done_getter = machine.get_named_property(owner, "_doneGetter")?;
        let value_getter = machine.get_named_property(owner, "_valueGetter")?;
        define_getter(machine, result, "done", done_getter);
        define_getter(machine, result, "value", value_getter);
        Ok(BuiltinOutcome::Value(result))
    }

    fn ordered_iterator_done_getter(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_iteratorStage")?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "_done")?,
        ))
    }

    fn ordered_iterator_value_getter(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        increment(machine, owner, "_iteratorStage")?;
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, "_value")?,
        ))
    }
    fn ordered_size_value_of(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let owner = machine.get_named_property(this, "_owner")?;
        if counter(machine, owner, "_stage") != 1 {
            return Err(type_error("size was coerced out of order"));
        }
        increment(machine, owner, "_coercions")?;
        Ok(BuiltinOutcome::Value(Value::number(1.9)))
    }
    fn make_set_like(
        machine: &mut Machine<'_, TestHost>,
        reported_size: f64,
        keys: &[Value],
        members: &[Value],
    ) -> Value {
        let object = ordinary_object(machine);
        let values = super::super::allocate_array(machine, keys.to_vec()).unwrap();
        let member_set = make_set(machine, members);
        let has = native(machine, "test has", 1, test_has);
        let keys = native(machine, "test keys", 0, test_keys);
        let next = native(machine, "test next", 0, test_next);
        let close = native(machine, "test return", 0, test_return);
        for (name, value) in [
            ("size", Value::number(reported_size)),
            ("has", has),
            ("keys", keys),
            ("_values", values),
            ("_members", member_set),
            ("_next", next),
            ("_return", close),
            ("_hasCalls", Value::int32(0)),
            ("_keysCalls", Value::int32(0)),
            ("_closed", Value::FALSE),
            ("_returnCalls", Value::int32(0)),
            ("_mutated", Value::FALSE),
            ("_mutateTarget", Value::UNDEFINED),
            ("_mutateValue", Value::UNDEFINED),
        ] {
            machine.set_data_property(object, name, value).unwrap();
        }
        object
    }

    fn assert_order(machine: &Machine<'_, TestHost>, set: Value, expected: &[Value]) {
        let actual = set_values(machine, set);
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert!(
                actual == *expected
                    || matches!(
                        (actual.decode(), expected.decode()),
                        (Some(Decoded::Number(left)), Some(Decoded::Number(right)))
                            if left.is_nan() && right.is_nan()
                    ),
                "expected {expected:?}, got {actual:?}"
            );
        }
    }

    #[test]
    fn custom_set_like_objects_cover_every_method_and_ordering() {
        with_machine(|machine| {
            let this = make_set(machine, &[Value::int32(1), Value::int32(2)]);
            let other = make_set_like(
                machine,
                2.0,
                &[Value::int32(2), Value::int32(3)],
                &[Value::int32(2), Value::int32(3)],
            );

            let union = call_method(machine, this, "union", other).unwrap();
            assert_order(
                machine,
                union,
                &[Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let intersection = call_method(machine, this, "intersection", other).unwrap();
            assert_order(machine, intersection, &[Value::int32(2)]);
            let difference = call_method(machine, this, "difference", other).unwrap();
            assert_order(machine, difference, &[Value::int32(1)]);
            let symmetric = call_method(machine, this, "symmetricDifference", other).unwrap();
            assert_order(machine, symmetric, &[Value::int32(1), Value::int32(3)]);
            assert_eq!(
                call_method(machine, this, "isSubsetOf", other).unwrap(),
                Value::FALSE
            );
            assert_eq!(
                call_method(machine, this, "isSupersetOf", other).unwrap(),
                Value::FALSE
            );
            assert_eq!(
                call_method(machine, this, "isDisjointFrom", other).unwrap(),
                Value::FALSE
            );
            assert!(counter(machine, other, "_hasCalls") > 0);
            assert!(counter(machine, other, "_keysCalls") > 0);
        });
    }

    #[test]
    fn intersection_uses_live_set_data_when_has_mutates_receiver() {
        with_machine(|machine| {
            let this = make_set(machine, &[Value::int32(1), Value::int32(2)]);
            let other = make_set_like(
                machine,
                10.0,
                &[],
                &[Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            machine
                .set_data_property(other, "_mutateTarget", this)
                .unwrap();
            machine
                .set_data_property(other, "_mutateValue", Value::int32(3))
                .unwrap();

            let result = call_method(machine, this, "intersection", other).unwrap();
            assert_order(
                machine,
                result,
                &[Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            assert_eq!(counter(machine, other, "_hasCalls"), 3);
        });
    }

    #[test]
    fn same_value_zero_canonicalizes_nan_and_negative_zero() {
        with_machine(|machine| {
            let nan = Value::number(f64::NAN);
            let negative_zero = Value::number(-0.0);
            let positive_zero = Value::number(0.0);
            let this = make_set(machine, &[nan, negative_zero]);
            let other = make_set_like(
                machine,
                3.0,
                &[positive_zero, nan, Value::int32(5)],
                &[positive_zero, nan, Value::int32(5)],
            );
            let result = call_method(machine, this, "union", other).unwrap();
            let values = set_values(machine, result);
            assert_eq!(values.len(), 3);
            assert!(set_data_has(machine, result, nan).unwrap());
            assert!(set_data_has(machine, result, negative_zero).unwrap());
            assert!(set_data_has(machine, result, Value::int32(5)).unwrap());
            let stored_zero = values
                .into_iter()
                .find_map(|value| match value.decode() {
                    Some(Decoded::Number(number)) if number == 0.0 => Some(number),
                    _ => None,
                })
                .unwrap();
            assert!(stored_zero.is_sign_positive());
        });
    }

    #[test]
    fn size_choice_controls_iteration_source_and_result_order() {
        with_machine(|machine| {
            let this = make_set(
                machine,
                &[Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let smaller = make_set_like(
                machine,
                2.0,
                &[Value::int32(3), Value::int32(1)],
                &[Value::int32(3), Value::int32(1)],
            );
            let result = call_method(machine, this, "intersection", smaller).unwrap();
            assert_order(machine, result, &[Value::int32(3), Value::int32(1)]);
            assert_eq!(counter(machine, smaller, "_hasCalls"), 0);
            assert_eq!(counter(machine, smaller, "_keysCalls"), 1);

            let difference_other =
                make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            let result = call_method(machine, this, "difference", difference_other).unwrap();
            assert_order(machine, result, &[Value::int32(1), Value::int32(3)]);
            assert_eq!(counter(machine, difference_other, "_hasCalls"), 0);
            assert_eq!(counter(machine, difference_other, "_keysCalls"), 1);

            let disjoint_other =
                make_set_like(machine, 1.0, &[Value::int32(4)], &[Value::int32(4)]);
            assert_eq!(
                call_method(machine, this, "isDisjointFrom", disjoint_other).unwrap(),
                Value::TRUE
            );
            assert_eq!(counter(machine, disjoint_other, "_hasCalls"), 0);
            assert_eq!(counter(machine, disjoint_other, "_keysCalls"), 1);

            let small_this = make_set(machine, &[Value::int32(1)]);
            let larger = make_set_like(machine, 10.0, &[], &[Value::int32(2)]);
            let result = call_method(machine, small_this, "difference", larger).unwrap();
            assert_order(machine, result, &[Value::int32(1)]);
            assert_eq!(counter(machine, larger, "_hasCalls"), 1);
            assert_eq!(counter(machine, larger, "_keysCalls"), 0);
        });
    }

    #[test]
    fn early_false_closes_keys_iterators() {
        with_machine(|machine| {
            let superset = make_set(machine, &[Value::int32(1)]);
            let missing = make_set_like(
                machine,
                1.0,
                &[Value::int32(2), Value::int32(3)],
                &[Value::int32(2), Value::int32(3)],
            );
            assert_eq!(
                call_method(machine, superset, "isSupersetOf", missing).unwrap(),
                Value::FALSE
            );
            let closed = machine.get_named_property(missing, "_closed").unwrap();
            assert!(machine.truthy(closed));
            assert_eq!(counter(machine, missing, "_returnCalls"), 1);

            let disjoint = make_set(machine, &[Value::int32(1), Value::int32(2)]);
            let overlapping = make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            assert_eq!(
                call_method(machine, disjoint, "isDisjointFrom", overlapping).unwrap(),
                Value::FALSE
            );
            let closed = machine.get_named_property(overlapping, "_closed").unwrap();
            assert!(machine.truthy(closed));
            assert_eq!(counter(machine, overlapping, "_returnCalls"), 1);
        });
    }
    #[test]
    fn receiver_validation_precedes_other_observation_for_every_method() {
        with_machine(|machine| {
            let method_source = make_set(machine, &[]);
            let incompatible_receiver = ordinary_object(machine);
            for name in [
                "union",
                "intersection",
                "difference",
                "symmetricDifference",
                "isSubsetOf",
                "isSupersetOf",
                "isDisjointFrom",
            ] {
                let other = ordered_set_like(machine, 0);
                let method = machine.get_named_property(method_source, name).unwrap();
                assert!(matches!(
                    machine.call_value(method, incompatible_receiver, &[other]),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "Set method called on incompatible receiver"
                    }))
                ));
                assert_eq!(counter(machine, other, "_stage"), 0, "{name}");
            }
        });
    }

    #[test]
    fn set_record_observes_size_coercion_and_integer_or_infinity() {
        with_machine(|machine| {
            let this = make_set(machine, &[Value::int32(1)]);
            let other = ordered_set_like(machine, 0);
            let size = ordinary_object(machine);
            let value_of = native(machine, "size valueOf", 0, ordered_size_value_of);
            machine.set_data_property(size, "_owner", other).unwrap();
            machine
                .set_data_property(size, "valueOf", value_of)
                .unwrap();
            machine.set_data_property(other, "_size", size).unwrap();
            machine
                .set_data_property(other, "_coercions", Value::int32(0))
                .unwrap();

            let result = call_method(machine, this, "intersection", other).unwrap();
            assert_order(machine, result, &[]);
            assert_eq!(counter(machine, other, "_stage"), 3);
            assert_eq!(counter(machine, other, "_coercions"), 1);
            assert_eq!(counter(machine, other, "_hasCalls"), 1);
            assert_eq!(counter(machine, other, "_keysCalls"), 0);

            let nan = make_set_like(machine, f64::NAN, &[], &[]);
            assert!(matches!(
                call_method(machine, this, "union", nan),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Set-like size is NaN"
                }))
            ));

            for size in [-1.0, f64::NEG_INFINITY] {
                let negative = make_set_like(machine, size, &[], &[]);
                assert!(matches!(
                    call_method(machine, this, "union", negative),
                    Err(EvalFailure::Throw(ThrowOrigin::RangeError { .. }))
                ));
            }

            let infinity = make_set_like(machine, f64::INFINITY, &[], &[Value::int32(1)]);
            assert_eq!(
                call_method(machine, this, "isSubsetOf", infinity).unwrap(),
                Value::TRUE
            );
        });
    }

    #[test]
    fn keys_iterator_observes_next_done_and_value_in_protocol_order() {
        with_machine(|machine| {
            let this = make_set(machine, &[Value::int32(1)]);
            let other = make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            let keys = native(machine, "ordered keys", 0, ordered_iterator_keys);
            let next_getter = native(machine, "get ordered next", 0, ordered_iterator_next_getter);
            let next = native(machine, "ordered next", 0, ordered_iterator_next);
            let done_getter = native(machine, "get ordered done", 0, ordered_iterator_done_getter);
            let value_getter = native(
                machine,
                "get ordered value",
                0,
                ordered_iterator_value_getter,
            );
            for (name, value) in [
                ("keys", keys),
                ("_nextGetter", next_getter),
                ("_orderedNext", next),
                ("_doneGetter", done_getter),
                ("_valueGetter", value_getter),
                ("_iteratorStage", Value::int32(0)),
            ] {
                machine.set_data_property(other, name, value).unwrap();
            }

            let result = call_method(machine, this, "union", other).unwrap();
            assert_order(machine, result, &[Value::int32(1), Value::int32(2)]);
            assert_eq!(counter(machine, other, "_keysCalls"), 1);
            assert_eq!(counter(machine, other, "_iteratorStage"), 6);
        });
    }
    #[test]
    fn iterator_abruptions_propagate_with_specified_close_behavior() {
        with_machine(|machine| {
            let this = make_set(machine, &[Value::int32(1)]);
            let abrupt_step = make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            let next = native(machine, "abrupt next", 0, abrupt_next);
            machine
                .set_data_property(abrupt_step, "_next", next)
                .unwrap();
            assert!(matches!(
                call_method(machine, this, "union", abrupt_step),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "abrupt iterator next"
                }))
            ));
            assert_eq!(counter(machine, abrupt_step, "_returnCalls"), 0);

            let abrupt_close = make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            let close = native(machine, "abrupt return", 0, abrupt_return);
            machine
                .set_data_property(abrupt_close, "_return", close)
                .unwrap();
            assert!(matches!(
                call_method(machine, this, "isSupersetOf", abrupt_close),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "abrupt iterator return"
                }))
            ));
            assert_eq!(counter(machine, abrupt_close, "_returnCalls"), 1);

            let primitive_close =
                make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            let close = native(machine, "primitive return", 0, primitive_return);
            machine
                .set_data_property(primitive_close, "_return", close)
                .unwrap();
            assert!(matches!(
                call_method(machine, this, "isSupersetOf", primitive_close),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Iterator return returned a non-object"
                }))
            ));
            assert_eq!(counter(machine, primitive_close, "_returnCalls"), 1);

            let non_callable_close =
                make_set_like(machine, 1.0, &[Value::int32(2)], &[Value::int32(2)]);
            machine
                .set_data_property(non_callable_close, "_return", Value::int32(0))
                .unwrap();
            assert!(matches!(
                call_method(machine, this, "isSupersetOf", non_callable_close),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Iterator return is not callable"
                }))
            ));
            assert_eq!(counter(machine, non_callable_close, "_returnCalls"), 0);
        });
    }

    #[test]
    fn duplicate_keys_preserve_composition_membership_and_order() {
        with_machine(|machine| {
            let this = make_set(
                machine,
                &[
                    Value::int32(3),
                    Value::int32(1),
                    Value::int32(2),
                    Value::int32(0),
                ],
            );
            let other = make_set_like(
                machine,
                2.0,
                &[
                    Value::int32(2),
                    Value::int32(2),
                    Value::int32(1),
                    Value::int32(4),
                    Value::int32(4),
                ],
                &[],
            );

            let union = call_method(machine, this, "union", other).unwrap();
            assert_order(
                machine,
                union,
                &[
                    Value::int32(3),
                    Value::int32(1),
                    Value::int32(2),
                    Value::int32(0),
                    Value::int32(4),
                ],
            );
            let intersection = call_method(machine, this, "intersection", other).unwrap();
            assert_order(machine, intersection, &[Value::int32(2), Value::int32(1)]);
            let difference = call_method(machine, this, "difference", other).unwrap();
            assert_order(machine, difference, &[Value::int32(3), Value::int32(0)]);
            let symmetric = call_method(machine, this, "symmetricDifference", other).unwrap();
            assert_order(
                machine,
                symmetric,
                &[Value::int32(3), Value::int32(0), Value::int32(4)],
            );
        });
    }

    #[test]
    fn predicate_has_branches_observe_live_receiver_growth() {
        with_machine(|machine| {
            let subset = make_set(machine, &[Value::int32(1)]);
            let other = make_set_like(machine, 10.0, &[], &[Value::int32(1), Value::int32(2)]);
            machine
                .set_data_property(other, "_mutateTarget", subset)
                .unwrap();
            machine
                .set_data_property(other, "_mutateValue", Value::int32(2))
                .unwrap();
            assert_eq!(
                call_method(machine, subset, "isSubsetOf", other).unwrap(),
                Value::TRUE
            );
            assert_eq!(counter(machine, other, "_hasCalls"), 2);

            let disjoint = make_set(machine, &[Value::int32(1)]);
            let other = make_set_like(machine, 10.0, &[], &[Value::int32(2)]);
            machine
                .set_data_property(other, "_mutateTarget", disjoint)
                .unwrap();
            machine
                .set_data_property(other, "_mutateValue", Value::int32(2))
                .unwrap();
            assert_eq!(
                call_method(machine, disjoint, "isDisjointFrom", other).unwrap(),
                Value::FALSE
            );
            assert_eq!(counter(machine, other, "_hasCalls"), 2);
        });
    }

    fn ordered_size(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        ordered_get(machine, this, 1, "_size")
    }

    fn ordered_has(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        ordered_get(machine, this, 2, "_has")
    }

    fn ordered_keys(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        ordered_get(machine, this, 3, "_keys")
    }

    fn ordered_get(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        expected: u32,
        backing: &str,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let stage = counter(machine, this, "_stage");
        if stage + 1 != expected {
            return Err(type_error("Set-like methods were read out of order"));
        }
        machine.set_data_property(this, "_stage", Value::int32(expected))?;
        if counter(machine, this, "_abruptAt") == expected {
            return Err(type_error("abrupt Set-like getter"));
        }
        Ok(BuiltinOutcome::Value(
            machine.get_named_property(this, backing)?,
        ))
    }

    fn define_getter(
        machine: &mut Machine<'_, TestHost>,
        object: Value,
        name: &str,
        getter: Value,
    ) {
        let slot = machine.runtime_slot(object).unwrap().unwrap();
        let key = PropertyKey::Named(machine.intern_str(name));
        let HeapEntry::Object { properties, .. } = &mut machine.heap[slot] else {
            unreachable!()
        };
        properties.insert(
            &mut machine.shapes,
            key,
            Property::Accessor {
                getter: Some(getter),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }

    fn ordered_set_like(machine: &mut Machine<'_, TestHost>, abrupt_at: u32) -> Value {
        let object = make_set_like(machine, 0.0, &[], &[]);
        let size = machine.get_named_property(object, "size").unwrap();
        let has = machine.get_named_property(object, "has").unwrap();
        let keys = machine.get_named_property(object, "keys").unwrap();
        for (name, value) in [
            ("_size", size),
            ("_has", has),
            ("_keys", keys),
            ("_stage", Value::int32(0)),
            ("_abruptAt", Value::int32(abrupt_at)),
        ] {
            machine.set_data_property(object, name, value).unwrap();
        }
        let size_getter = native(machine, "get size", 0, ordered_size);
        let has_getter = native(machine, "get has", 0, ordered_has);
        let keys_getter = native(machine, "get keys", 0, ordered_keys);
        define_getter(machine, object, "size", size_getter);
        define_getter(machine, object, "has", has_getter);
        define_getter(machine, object, "keys", keys_getter);
        object
    }

    #[test]
    fn set_record_reads_size_has_keys_in_order_and_stops_on_abrupt_getter() {
        with_machine(|machine| {
            let this = make_set(machine, &[]);
            let ordered = ordered_set_like(machine, 0);
            assert_eq!(
                call_method(machine, this, "isSubsetOf", ordered).unwrap(),
                Value::TRUE
            );
            assert_eq!(counter(machine, ordered, "_stage"), 3);

            for abrupt_at in 1..=3 {
                let abrupt = ordered_set_like(machine, abrupt_at);
                assert!(matches!(
                    call_method(machine, this, "isSubsetOf", abrupt),
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "abrupt Set-like getter"
                    }))
                ));
                assert_eq!(counter(machine, abrupt, "_stage"), abrupt_at);
            }
        });
    }

    #[test]
    fn installation_has_standard_descriptors_and_results_use_set_prototype() {
        with_machine(|machine| {
            let constructor = machine.intrinsics.global("Set").unwrap();
            let prototype = machine
                .get_named_property(constructor, "prototype")
                .unwrap();
            let slot = machine.runtime_slot(prototype).unwrap().unwrap();
            for name in [
                "union",
                "intersection",
                "difference",
                "symmetricDifference",
                "isSubsetOf",
                "isSupersetOf",
                "isDisjointFrom",
            ] {
                let HeapEntry::Object { properties, .. } = &machine.heap[slot] else {
                    unreachable!()
                };
                let Some(Property::Data {
                    value,
                    writable,
                    enumerable,
                    configurable,
                }) = properties.get_ascii(&machine.shapes, &machine.atoms, name)
                else {
                    panic!("{name} is installed as data property")
                };
                let (function, writable, enumerable, configurable) =
                    (*value, *writable, *enumerable, *configurable);
                assert!(writable);
                assert!(!enumerable);
                assert!(configurable);
                let function_slot = machine.runtime_slot(function).unwrap().unwrap();
                assert!(matches!(
                    machine.heap[function_slot],
                    HeapEntry::NativeFunction {
                        callable: NativeCallable::Builtin(_),
                        ..
                    }
                ));
                let installed_name = machine.get_named_property(function, "name").unwrap();
                assert!(machine.string_value(installed_name).unwrap().eq_ascii(name));
                assert_eq!(
                    machine.get_named_property(function, "length").unwrap(),
                    Value::int32(1)
                );
            }

            let left = make_set(machine, &[Value::int32(1)]);
            let right = make_set_like(machine, 0.0, &[], &[]);
            let result = call_method(machine, left, "union", right).unwrap();
            let result_slot = require_set_slot(machine, result).unwrap();
            let HeapEntry::Collection {
                prototype: result_prototype,
                ..
            } = &machine.heap[result_slot]
            else {
                unreachable!()
            };
            assert_eq!(*result_prototype, Some(prototype));
        });
    }
}
