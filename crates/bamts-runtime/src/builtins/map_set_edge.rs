use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::{
    allocate_array, define_data, heap_index, install_constructor_function, install_function,
    type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    CollectionKind, EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap,
    ShapeTable,
};

/// Installs the collection algorithms whose observable ordering and iterator-close
/// requirements cannot be expressed by the baseline eager constructors.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let map = replace_constructor(heap, atoms, shapes, globals, builtins, "Map", map_constructor::<H>);
    let set = replace_constructor(heap, atoms, shapes, globals, builtins, "Set", set_constructor::<H>);
    let weak_map = replace_constructor(
        heap,
        atoms,
        shapes,
        globals,
        builtins,
        "WeakMap",
        weak_map_constructor::<H>,
    );
    let weak_set = replace_constructor(
        heap,
        atoms,
        shapes,
        globals,
        builtins,
        "WeakSet",
        weak_set_constructor::<H>,
    );

    for constructor in [map.constructor, set.constructor] {
        let species = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "get [Symbol.species]", length: 0, handler: super::regexp_protocol::species_getter::<H> });
        super::define_symbol_property(heap, shapes, constructor,
        builtins.symbol_species(),
        crate::Property::Accessor {
            getter: Some(species),
            setter: None,
            enumerable: false,
            configurable: true,
        },);
    }

    let group_by = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "groupBy", length: 2, handler: map_group_by::<H> });
    define_constructor_data(heap, atoms, shapes, map.constructor, "groupBy", group_by);
    let map_set = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "set", length: 2, handler: strong_map_set::<H> });
    define_data(heap, atoms, shapes, map.prototype, "set", map_set);
    for (target, name, handler) in [
        (
            map.prototype,
            "getOrInsert",
            map_get_or_insert::<H> as BuiltinHandler<H>,
        ),
        (
            map.prototype,
            "getOrInsertComputed",
            map_get_or_insert_computed::<H>,
        ),
        (
            weak_map.prototype,
            "getOrInsert",
            weak_map_get_or_insert::<H>,
        ),
        (
            weak_map.prototype,
            "getOrInsertComputed",
            weak_map_get_or_insert_computed::<H>,
        ),
    ] {
        let function = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: name, length: 2, handler: handler });
        define_data(heap, atoms, shapes, target, name, function);
    }
    let set_add = install_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: "add", length: 1, handler: strong_set_add::<H> });
    define_data(heap, atoms, shapes, set.prototype, "add", set_add);

    // Set.prototype.keys and Set.prototype.values are the same function object.
    let set_prototype = prototype_of(heap, atoms, shapes, "Set", globals);
    let values = own_data_property(heap, atoms, shapes, set_prototype, "values");
    define_data(heap, atoms, shapes, set_prototype, "keys", values);

    define_collection_tag(
        heap,
        shapes,
        weak_map.prototype,
        builtins.symbol_to_string_tag(),
        "WeakMap",
    );
    define_collection_tag(
        heap,
        shapes,
        weak_set.prototype,
        builtins.symbol_to_string_tag(),
        "WeakSet",
    );
}

#[derive(Clone, Copy)]
struct InstalledConstructor {
    constructor: Value,
    prototype: Value,
}

fn replace_constructor<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    handler: BuiltinHandler<H>,
) -> InstalledConstructor {
    let prototype = prototype_of(heap, atoms, shapes, name, globals);
    let constructor = install_constructor_function(heap, atoms, shapes, builtins, crate::intrinsics::BuiltinDef { name: name, length: 0, handler: handler });
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    globals.insert(EcmaString::encode(name), constructor);
    InstalledConstructor {
        constructor,
        prototype,
    }
}
fn prototype_of(
    heap: &[HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &ShapeTable,
    name: &str,
    globals: &BTreeMap<EcmaString, Value>,
) -> Value {
    let constructor = globals
        .get(&EcmaString::encode(name))
        .copied()
        .expect("baseline collection constructor is installed first");
    own_data_property(heap, atoms, shapes, constructor, "prototype")
}

fn own_data_property(
    heap: &[HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &ShapeTable,
    object: Value,
    name: &str,
) -> Value {
    let properties = match &heap[heap_index(object)] {
        HeapEntry::Object { properties, .. }
        | HeapEntry::Array { properties, .. }
        | HeapEntry::NativeFunction { properties, .. } => properties,
        _ => panic!("collection intrinsic property owner must be an object"),
    };
    match properties.get(shapes, &PropertyKey::Named(atoms.intern(EcmaString::encode(name)))) {
        Some(Property::Data { value, .. }) => *value,
        _ => panic!("collection intrinsic data property must exist"),
    }
}

fn define_constructor_data(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    constructor: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        panic!("collection constructor must be a native function")
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern(EcmaString::encode(name))),
        Property::Data {
            value,
            writable: true,
            enumerable: false,
            configurable: true,
        },
    );
}

fn define_collection_tag(
    heap: &mut Vec<HeapEntry>,
    shapes: &mut crate::ShapeTable,
    prototype: Value,
    tag_symbol: Value,
    name: &str,
) {
    let value = super::super::push(heap, HeapEntry::String(EcmaString::encode(name)));
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        panic!("collection prototype must be an ordinary object")
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(tag_symbol) as u32),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
}

fn map_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_constructor(machine, args, constructing, CollectionKind::Map, "set")
}

fn set_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_constructor(machine, args, constructing, CollectionKind::Set, "add")
}

fn weak_map_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_constructor(machine, args, constructing, CollectionKind::WeakMap, "set")
}

fn weak_set_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_constructor(machine, args, constructing, CollectionKind::WeakSet, "add")
}

fn strong_map_set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let key = canonical_collection_key(args.first().copied().unwrap_or(Value::UNDEFINED));
    let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    put_strong_entry(machine, this, key, value, CollectionKind::Map)?;
    Ok(BuiltinOutcome::Value(this))
}

fn strong_set_add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = canonical_collection_key(args.first().copied().unwrap_or(Value::UNDEFINED));
    put_strong_entry(machine, this, value, value, CollectionKind::Set)?;
    Ok(BuiltinOutcome::Value(this))
}

/// The key `getOrInsert*` stores: `Map` canonicalizes `-0`, and `WeakMap`
/// refuses anything that cannot be held weakly.
fn upsert_key<H: Host>(
    machine: &Machine<'_, H>,
    key: Value,
    kind: CollectionKind,
) -> Result<Value, EvalFailure> {
    if kind == CollectionKind::WeakMap {
        super::collections::require_weak_key(machine, key)?;
        return Ok(key);
    }
    Ok(canonical_collection_key(key))
}

fn existing_value<H: Host>(machine: &Machine<'_, H>, slot: usize, key: Value) -> Option<Value> {
    let HeapEntry::Collection { entries, index, .. } = &machine.heap[slot] else {
        unreachable!("collection brand was checked")
    };
    index
        .get(machine, entries, key)
        .map(|entry_index| entries[entry_index].value)
}

fn get_or_insert<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    kind: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = super::collections::collection_slot(machine, this, kind)?;
    let key = upsert_key(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        kind,
    )?;
    if let Some(existing) = existing_value(machine, slot, key) {
        return Ok(BuiltinOutcome::Value(existing));
    }
    let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    super::collections::append_collection_entry(machine, slot, key, value)?;
    Ok(BuiltinOutcome::Value(value))
}

/// The callback may change the collection, so its result is stored by a fresh
/// lookup rather than at a position found before the call.
fn get_or_insert_computed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    kind: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = super::collections::collection_slot(machine, this, kind)?;
    let key = args.first().copied().unwrap_or(Value::UNDEFINED);
    let key = upsert_key(machine, key, kind)?;
    let callback = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(type_error("getOrInsertComputed callback is not callable"));
    }
    if let Some(existing) = existing_value(machine, slot, key) {
        return Ok(BuiltinOutcome::Value(existing));
    }
    let depth = machine.native_roots.len();
    machine.push_native_roots(depth, &[this, key, callback]);
    let value = machine.call_value(callback, Value::UNDEFINED, &[key]);
    machine.pop_native_roots(depth);
    let value = value?;
    super::collections::map_put(machine, this, key, value, kind)?;
    Ok(BuiltinOutcome::Value(value))
}

fn map_get_or_insert<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    get_or_insert(machine, this, args, CollectionKind::Map)
}

fn map_get_or_insert_computed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    get_or_insert_computed(machine, this, args, CollectionKind::Map)
}

fn weak_map_get_or_insert<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    get_or_insert(machine, this, args, CollectionKind::WeakMap)
}

fn weak_map_get_or_insert_computed<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    get_or_insert_computed(machine, this, args, CollectionKind::WeakMap)
}

fn canonical_collection_key(value: Value) -> Value {
    match value.decode() {
        Some(Decoded::Number(number)) if number == 0.0 && number.is_sign_negative() => {
            Value::number(0.0)
        }
        _ => value,
    }
}

fn put_strong_entry<H: Host>(
    machine: &mut Machine<'_, H>,
    collection: Value,
    key: Value,
    value: Value,
    expected: CollectionKind,
) -> Result<(), EvalFailure> {
    let slot = machine
        .runtime_slot(collection)
        .map_err(EvalFailure::Runtime)?
        .ok_or_else(|| type_error("collection method called on incompatible receiver"))?;
    let existing = match &machine.heap[slot] {
        HeapEntry::Collection { kind, entries, .. } if *kind == expected => entries
            .iter()
            .position(|entry| entry.live && machine.same_value_zero(entry.key, key)),
        _ => {
            return Err(type_error(
                "collection method called on incompatible receiver",
            ));
        }
    };
    if let Some(entry_index) = existing {
        let HeapEntry::Collection { entries, .. } = &mut machine.heap[slot] else {
            unreachable!("collection brand checked above")
        };
        entries[entry_index].value = value;
        return Ok(());
    }
    super::collections::append_collection_entry(machine, slot, key, value)
}

fn collection_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    constructing: bool,
    kind: CollectionKind,
    adder_name: &'static str,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error("collection constructor requires 'new'"));
    }
    let prototype = collection_prototype_from_constructor(machine, kind)?;
    let iterable = args
        .first()
        .copied()
        .filter(|value| !matches!(value.decode(), Some(Decoded::Null | Decoded::Undefined)));
    let depth = machine.native_roots.len();
    if let Some(iterable) = iterable {
        machine.push_native_roots(depth, &[iterable]);
    }
    let collection = match allocate_collection(machine, prototype, kind) {
        Ok(collection) => collection,
        Err(failure) => {
            if iterable.is_some() {
                machine.pop_native_roots(depth);
            }
            return Err(failure);
        }
    };
    let Some(iterable) = iterable else {
        return Ok(BuiltinOutcome::Value(collection));
    };

    machine.refresh_native_roots(depth, &[collection, iterable]);
    let result: Result<(), EvalFailure> = (|| {
        // The adder is observable and must be read once before GetIterator.
        let adder = machine.get_named_property(collection, adder_name)?;
        if !machine.is_callable(adder)? {
            return Err(type_error("collection adder is not callable"));
        }
        machine.refresh_native_roots(depth, &[collection, iterable, adder]);
        let iterator = machine.create_iterator(iterable, bamts_bytecode::IteratorKind::Sync)?;
        loop {
            machine.refresh_native_roots(depth, &[collection, adder, iterator]);
            // IteratorStep failures propagate directly. Closing starts only after
            // a step has produced a result for the constructor body.
            let next = machine.iterator_step(iterator)?;
            machine.refresh_native_roots(depth, &[collection, adder, iterator, next]);
            let (done, value) = match machine.iterator_result_parts(next) {
                Ok(parts) => parts,
                Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
            };
            if done {
                return Ok(());
            }
            machine.refresh_native_roots(depth, &[collection, adder, iterator, value]);
            let arguments = match kind {
                CollectionKind::Map | CollectionKind::WeakMap => {
                    if !machine.is_object(value) {
                        return Err(close_after_abrupt(
                            machine,
                            iterator,
                            type_error("Iterator value is not an entry object"),
                        ));
                    }
                    let key = match machine.get_named_property(value, "0") {
                        Ok(key) => key,
                        Err(failure) => {
                            return Err(close_after_abrupt(machine, iterator, failure));
                        }
                    };
                    machine.refresh_native_roots(depth, &[collection, adder, iterator, value, key]);
                    let mapped = match machine.get_named_property(value, "1") {
                        Ok(mapped) => mapped,
                        Err(failure) => {
                            return Err(close_after_abrupt(machine, iterator, failure));
                        }
                    };
                    machine.refresh_native_roots(
                        depth,
                        &[collection, adder, iterator, value, key, mapped],
                    );
                    [key, mapped]
                }
                CollectionKind::Set | CollectionKind::WeakSet => [value, Value::UNDEFINED],
            };
            let argument_count = usize::from(matches!(
                kind,
                CollectionKind::Map | CollectionKind::WeakMap
            )) + 1;
            if let Err(failure) =
                machine.call_value(adder, collection, &arguments[..argument_count])
            {
                return Err(close_after_abrupt(machine, iterator, failure));
            }
        }
    })();
    machine.pop_native_roots(depth);
    result?;
    Ok(BuiltinOutcome::Value(collection))
}

fn collection_prototype_from_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    kind: CollectionKind,
) -> Result<Value, EvalFailure> {
    let name = match kind {
        CollectionKind::Map => "Map",
        CollectionKind::Set => "Set",
        CollectionKind::WeakMap => "WeakMap",
        CollectionKind::WeakSet => "WeakSet",
    };
    let constructor = machine
        .intrinsics
        .global(name)
        .ok_or_else(|| type_error("missing collection constructor"))?;
    let default = machine.get_named_property(constructor, "prototype")?;
    let new_target = machine.current_new_target();
    if new_target == Value::UNDEFINED {
        return Ok(default);
    }
    let candidate = machine.get_named_property(new_target, "prototype")?;
    Ok(if machine.is_object(candidate) {
        candidate
    } else {
        default
    })
}

fn allocate_collection<H: Host>(
    machine: &mut Machine<'_, H>,
    prototype: Value,
    kind: CollectionKind,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Collection {
            kind,
            entries: Vec::new(),
            index: crate::CollectionIndex::default(),
            size: 0,
            next_order: 0,
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

fn get_sync_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    iterable: Value,
) -> Result<Value, EvalFailure> {
    let key = machine.property_key_from_value(machine.intrinsics.builtins.symbol_iterator())?;
    let method = machine.get_property_key(iterable, &key)?;
    if !machine.is_callable(method)? {
        return Err(type_error("value is not iterable"));
    }
    let target = machine.call_value(method, iterable, &[])?;
    if !machine.is_object(target) {
        return Err(type_error("iterator method returned a non-object"));
    }
    let next = machine.get_named_property(target, "next")?;
    if !machine.is_callable(next)? {
        return Err(type_error("iterator next is not callable"));
    }
    machine.create_protocol_iterator(target, next)
}

fn close_after_abrupt<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator: Value,
    failure: EvalFailure,
) -> EvalFailure {
    // IteratorClose preserves an already-abrupt completion even if looking up or
    // calling `return` itself fails. Keep both the iterator and abrupt value live.
    let depth = machine.native_roots.len();
    match &failure {
        EvalFailure::ThrowValue(value) | EvalFailure::ThrowValueOrigin { value, .. } => {
            machine.push_native_roots(depth, &[iterator, *value]);
        }
        EvalFailure::Throw(_) | EvalFailure::Runtime(_) => {
            machine.push_native_roots(depth, &[iterator]);
        }
    }
    let _ = machine.close_iterator_raw(iterator);
    machine.pop_native_roots(depth);
    failure
}

fn map_group_by<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let items = args.first().copied().unwrap_or(Value::UNDEFINED);
    let callback = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(type_error("Map.groupBy callback is not callable"));
    }
    let map_constructor = machine
        .intrinsics
        .global("Map")
        .ok_or_else(|| type_error("missing Map constructor"))?;
    let prototype = machine.get_named_property(map_constructor, "prototype")?;
    let result = allocate_collection(machine, prototype, CollectionKind::Map)?;
    let iterator = get_sync_iterator(machine, items)?;
    let mut index = 0_u64;
    loop {
        let next = match machine.iterator_step(iterator) {
            Ok(next) => next,
            Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
        };
        let (done, value) = match machine.iterator_result_parts(next) {
            Ok(parts) => parts,
            Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
        };
        if done {
            return Ok(BuiltinOutcome::Value(result));
        }
        if index >= 9_007_199_254_740_991 {
            return Err(close_after_abrupt(
                machine,
                iterator,
                type_error("Map.groupBy iteration count exceeds safe integer range"),
            ));
        }
        let key = match machine.call_value(
            callback,
            Value::UNDEFINED,
            &[value, crate::number_value(index as f64)],
        ) {
            Ok(key) => key,
            Err(failure) => return Err(close_after_abrupt(machine, iterator, failure)),
        };
        if let Err(failure) = add_group(machine, result, key, value) {
            return Err(close_after_abrupt(machine, iterator, failure));
        }
        index += 1;
    }
}

fn add_group<H: Host>(
    machine: &mut Machine<'_, H>,
    map: Value,
    key: Value,
    value: Value,
) -> Result<(), EvalFailure> {
    let key = canonical_collection_key(key);
    let slot = machine
        .runtime_slot(map)
        .map_err(EvalFailure::Runtime)?
        .ok_or_else(|| type_error("Map.groupBy result is not a Map"))?;
    let existing = match &machine.heap[slot] {
        HeapEntry::Collection { entries, .. } => entries
            .iter()
            .position(|entry| entry.live && machine.same_value_zero(entry.key, key)),
        _ => return Err(type_error("Map.groupBy result is not a Map")),
    };
    if let Some(entry_index) = existing {
        let group = match &machine.heap[slot] {
            HeapEntry::Collection { entries, .. } => entries[entry_index].value,
            _ => unreachable!("Map brand checked above"),
        };
        machine.array_push(group, value)?;
        return Ok(());
    }
    let group = allocate_array(machine, vec![value])?;
    super::collections::append_collection_entry(machine, slot, key, group)
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, custom_iterable, ordinary_object};
    use super::*;
    use crate::intrinsics::BuiltinDef;
    use crate::{Limits, NativeCallable, RuntimeErrorKind, ThrowOrigin};

    fn with_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let module = blank_program("<map-set-edge-test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        test(&mut machine);
    }

    fn invoke(
        machine: &mut Machine<'_, TestHost>,
        receiver: Value,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let method = machine.get_named_property(receiver, name).unwrap();
        machine.call_value(method, receiver, args)
    }

    fn compute_seven(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::int32(7)))
    }

    /// Stores into the map before returning, as a user callback may.
    fn insert_during_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let global = machine.intrinsics.global("globalThis").unwrap();
        let map = machine.get_named_property(global, "upsertTarget").unwrap();
        invoke(machine, map, "set", &[args[0], Value::int32(1)])?;
        Ok(BuiltinOutcome::Value(Value::int32(2)))
    }

    fn native_callback(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: crate::intrinsics::BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 1,
            handler,
        });
        crate::intrinsics::native_function(&mut machine.heap, &mut machine.atoms, &mut machine.shapes, id, name, 1)
    }

    fn new_collection(machine: &mut Machine<'_, TestHost>, name: &str) -> Value {
        let constructor = machine.intrinsics.global(name).unwrap();
        machine.construct_value(constructor, &[]).unwrap()
    }

    #[test]
    fn get_or_insert_keeps_an_existing_value_and_canonicalizes_negative_zero() {
        with_machine(|machine| {
            let map = new_collection(machine, "Map");
            let negative_zero = Value::number(-0.0);
            assert_eq!(
                invoke(
                    machine,
                    map,
                    "getOrInsert",
                    &[negative_zero, Value::int32(1)]
                )
                .unwrap(),
                Value::int32(1)
            );
            assert_eq!(
                invoke(
                    machine,
                    map,
                    "getOrInsert",
                    &[Value::int32(0), Value::int32(2)]
                )
                .unwrap(),
                Value::int32(1),
                "-0 and +0 are one key"
            );
            let keys = invoke(machine, map, "keys", &[]).unwrap();
            let first = invoke(machine, keys, "next", &[]).unwrap();
            let key = machine.get_named_property(first, "value").unwrap();
            assert!(
                matches!(key.decode(), Some(Decoded::Number(zero)) if zero.is_sign_positive())
                    || key == Value::int32(0),
                "the stored key is +0"
            );
        });
    }

    #[test]
    fn get_or_insert_computed_calls_back_only_for_a_missing_key() {
        with_machine(|machine| {
            let map = new_collection(machine, "Map");
            let compute = native_callback(machine, "compute seven", compute_seven);
            assert_eq!(
                invoke(
                    machine,
                    map,
                    "getOrInsertComputed",
                    &[Value::int32(1), compute]
                )
                .unwrap(),
                Value::int32(7)
            );
            let non_callable = Value::int32(0);
            assert!(matches!(
                invoke(
                    machine,
                    map,
                    "getOrInsertComputed",
                    &[Value::int32(1), non_callable]
                ),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn a_key_stored_by_the_callback_is_overwritten_not_duplicated() {
        with_machine(|machine| {
            let map = new_collection(machine, "Map");
            let global = machine.intrinsics.global("globalThis").unwrap();
            machine
                .set_data_property(global, "upsertTarget", map)
                .unwrap();
            let callback =
                native_callback(machine, "insert during callback", insert_during_callback);
            assert_eq!(
                invoke(
                    machine,
                    map,
                    "getOrInsertComputed",
                    &[Value::int32(5), callback]
                )
                .unwrap(),
                Value::int32(2)
            );
            assert_eq!(
                invoke(machine, map, "get", &[Value::int32(5)]).unwrap(),
                Value::int32(2)
            );
            assert_eq!(
                machine.get_named_property(map, "size").unwrap(),
                Value::int32(1)
            );
        });
    }

    #[test]
    fn weak_map_get_or_insert_rejects_keys_that_cannot_be_held_weakly() {
        with_machine(|machine| {
            let weak_map = new_collection(machine, "WeakMap");
            let key = ordinary_object(machine);
            assert_eq!(
                invoke(machine, weak_map, "getOrInsert", &[key, Value::int32(1)]).unwrap(),
                Value::int32(1)
            );
            assert!(matches!(
                invoke(machine, weak_map, "getOrInsert", &[Value::int32(1), key]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            let compute = native_callback(machine, "compute seven", compute_seven);
            assert!(matches!(
                invoke(
                    machine,
                    weak_map,
                    "getOrInsertComputed",
                    &[Value::int32(1), compute]
                ),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    fn builtin_id(machine: &Machine<'_, TestHost>, value: Value) -> crate::intrinsics::BuiltinId {
        let slot = machine.runtime_slot(value).unwrap().unwrap();
        match machine.heap[slot] {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => id,
            _ => panic!("expected builtin function"),
        }
    }

    #[test]
    fn install_exposes_callable_map_group_by_static() {
        with_machine(|machine| {
            let map = machine.intrinsics.global("Map").expect("Map is installed");
            let group_by = machine
                .get_named_property(map, "groupBy")
                .expect("Map.groupBy is readable");
            assert!(machine.is_callable(group_by).unwrap());
            let length_key = PropertyKey::Named(machine.intern_str("length"));
            let slot = machine.runtime_slot(group_by).unwrap().unwrap();
            let HeapEntry::NativeFunction { properties, .. } = &machine.heap[slot] else {
                panic!("Map.groupBy is a native function")
            };
            assert!(matches!(
                properties.get(&machine.shapes, &length_key),
                Some(Property::Data {
                    value,
                    writable: false,
                    enumerable: false,
                    configurable: true,
                }) if *value == Value::int32(2)
            ));
        });
    }

    fn construct(
        machine: &mut Machine<'_, TestHost>,
        name: &str,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        let constructor = machine.intrinsics.global(name).unwrap();
        let id = builtin_id(machine, constructor);
        let BuiltinOutcome::Value(value) = machine.call_builtin_with_new_target(
            id,
            Value::UNDEFINED,
            arguments,
            true,
            constructor,
        )?
        else {
            panic!("constructor must return a value")
        };
        Ok(value)
    }

    fn method(machine: &mut Machine<'_, TestHost>, constructor: &str, name: &str) -> Value {
        let constructor = machine.intrinsics.global(constructor).unwrap();
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .unwrap();
        machine.get_named_property(prototype, name).unwrap()
    }

    fn call_method(
        machine: &mut Machine<'_, TestHost>,
        constructor: &str,
        name: &str,
        this: Value,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let function = method(machine, constructor, name);
        machine.call_value(function, this, args)
    }

    fn entry(machine: &mut Machine<'_, TestHost>, key: Value, value: Value) -> Value {
        let pair = ordinary_object(machine);
        machine.set_data_property(pair, "0", key).unwrap();
        machine.set_data_property(pair, "1", value).unwrap();
        pair
    }

    fn close_marker(machine: &mut Machine<'_, TestHost>, yielded: Value) -> (Value, Value) {
        fn next<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let used = machine.get_named_property(this, "used")?;
            let result = super::super::collections::ordinary_runtime(machine, None)?;
            if used == Value::FALSE {
                machine.set_data_property(this, "used", Value::TRUE)?;
                let value = machine.get_named_property(this, "yielded")?;
                machine.set_data_property(result, "done", Value::FALSE)?;
                machine.set_data_property(result, "value", value)?;
            } else {
                machine.set_data_property(result, "done", Value::TRUE)?;
            }
            Ok(BuiltinOutcome::Value(result))
        }
        fn close<H: Host>(
            machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            machine.set_data_property(this, "closed", Value::TRUE)?;
            Ok(BuiltinOutcome::Value(
                super::super::collections::ordinary_runtime(machine, None)?,
            ))
        }
        fn iterator<H: Host>(
            _machine: &mut Machine<'_, H>,
            this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            Ok(BuiltinOutcome::Value(this))
        }

        let next_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "edge next",
            length: 0,
            handler: next::<TestHost>,
        });
        let close_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "edge return",
            length: 0,
            handler: close::<TestHost>,
        });
        let iterator_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "edge iterator",
            length: 0,
            handler: iterator::<TestHost>,
        });
        let next = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            next_id,
            "edge next",
            0,
        );
        let close = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            close_id,
            "edge return",
            0,
        );
        let iterator_fn = crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            iterator_id,
            "edge iterator",
            0,
        );
        let source = ordinary_object(machine);
        machine
            .set_data_property(source, "used", Value::FALSE)
            .unwrap();
        machine
            .set_data_property(source, "closed", Value::FALSE)
            .unwrap();
        machine
            .set_data_property(source, "yielded", yielded)
            .unwrap();
        machine.set_data_property(source, "next", next).unwrap();
        machine.set_data_property(source, "return", close).unwrap();
        let key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_iterator())
            .unwrap();
        machine
            .set_data_property_key(source, key, iterator_fn)
            .unwrap();
        (source, source)
    }

    #[test]
    fn constructor_closes_hostile_iterator_on_non_entry() {
        with_machine(|machine| {
            let (source, marker) = close_marker(machine, Value::int32(1));
            assert!(matches!(
                construct(machine, "Map", &[source]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                machine.get_named_property(marker, "closed").unwrap(),
                Value::TRUE
            );
        });
    }

    #[test]
    fn constructor_closes_iterator_when_observable_adder_throws() {
        fn reject<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            _args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            Err(type_error("hostile Map.prototype.set"))
        }

        with_machine(|machine| {
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "reject set",
                length: 2,
                handler: reject::<TestHost>,
            });
            let reject = crate::intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "reject set",
                2,
            );
            let constructor = machine.intrinsics.global("Map").unwrap();
            let prototype = machine
                .get_named_property(constructor, "prototype")
                .unwrap();
            machine.set_data_property(prototype, "set", reject).unwrap();
            let pair = entry(machine, Value::int32(1), Value::int32(2));
            let (source, marker) = close_marker(machine, pair);
            assert!(matches!(
                construct(machine, "Map", &[source]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert_eq!(
                machine.get_named_property(marker, "closed").unwrap(),
                Value::TRUE
            );
        });
    }

    #[test]
    fn for_each_observes_delete_clear_and_append_mutation_in_order() {
        fn mutate<H: Host>(
            machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let map = args.get(2).copied().unwrap_or(Value::UNDEFINED);
            let count = machine.get_named_property(map, "visits")?;
            let count = match count.decode() {
                Some(Decoded::Int32(count)) => count,
                _ => 0,
            };
            machine.set_data_property(map, "visits", Value::int32(count + 1))?;
            if count == 0 {
                let constructor = machine.intrinsics.global("Map").expect("Map exists");
                let prototype = machine.get_named_property(constructor, "prototype")?;
                let delete = machine.get_named_property(prototype, "delete")?;
                let clear = machine.get_named_property(prototype, "clear")?;
                let set = machine.get_named_property(prototype, "set")?;
                machine.call_value(delete, map, &[Value::int32(2)])?;
                machine.call_value(clear, map, &[])?;
                machine.call_value(set, map, &[Value::int32(3), Value::int32(30)])?;
            }
            Ok(BuiltinOutcome::Value(Value::UNDEFINED))
        }

        with_machine(|machine| {
            let first = entry(machine, Value::int32(1), Value::int32(10));
            let second = entry(machine, Value::int32(2), Value::int32(20));
            let source = custom_iterable(machine, vec![first, second]);
            let map = construct(machine, "Map", &[source]).unwrap();
            machine
                .set_data_property(map, "visits", Value::int32(0))
                .unwrap();
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "mutate map",
                length: 3,
                handler: mutate::<TestHost>,
            });
            let callback = crate::intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "mutate map",
                3,
            );
            call_method(machine, "Map", "forEach", map, &[callback]).unwrap();
            assert_eq!(
                machine.get_named_property(map, "visits").unwrap(),
                Value::int32(2)
            );
            assert_eq!(
                call_method(machine, "Map", "has", map, &[Value::int32(2)]).unwrap(),
                Value::FALSE
            );
            assert_eq!(
                call_method(machine, "Map", "has", map, &[Value::int32(1)]).unwrap(),
                Value::FALSE
            );
            assert_eq!(
                call_method(machine, "Map", "get", map, &[Value::int32(3)]).unwrap(),
                Value::int32(30)
            );
        });
    }

    #[test]
    fn duplicate_keys_use_same_value_zero_and_keep_first_order() {
        with_machine(|machine| {
            let first = entry(machine, Value::number(f64::NAN), Value::int32(1));
            let second = entry(machine, Value::number(f64::NAN), Value::int32(2));
            let zero = entry(machine, Value::number(-0.0), Value::int32(3));
            let source = custom_iterable(machine, vec![first, second, zero]);
            let map = construct(machine, "Map", &[source]).unwrap();
            assert_eq!(
                call_method(machine, "Map", "get", map, &[Value::number(f64::NAN)]).unwrap(),
                Value::int32(2)
            );
            assert_eq!(
                call_method(machine, "Map", "get", map, &[Value::number(0.0)]).unwrap(),
                Value::int32(3)
            );
            let slot = machine.runtime_slot(map).unwrap().unwrap();
            let HeapEntry::Collection { entries, size, .. } = &machine.heap[slot] else {
                panic!("Map has collection storage")
            };
            assert_eq!(*size, 2);
            assert!(
                entries[0]
                    .key
                    .decode()
                    .is_some_and(|decoded| match decoded {
                        Decoded::Number(number) => number.is_nan(),
                        _ => false,
                    })
            );
            assert!(
                entries[1]
                    .key
                    .decode()
                    .is_some_and(|decoded| match decoded {
                        Decoded::Number(number) => number == 0.0 && number.is_sign_positive(),
                        _ => false,
                    })
            );
        });
    }

    #[test]
    fn cross_prototype_calls_reject_incompatible_receivers() {
        with_machine(|machine| {
            let map = construct(machine, "Map", &[]).unwrap();
            let set = construct(machine, "Set", &[]).unwrap();
            assert!(matches!(
                call_method(machine, "Map", "get", set, &[Value::int32(1)]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
            assert!(matches!(
                call_method(machine, "Set", "has", map, &[Value::int32(1)]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        });
    }

    #[test]
    fn weak_keys_are_purged_without_relocating_live_collection() {
        with_machine(|machine| {
            let weak_map = construct(machine, "WeakMap", &[]).unwrap();
            let key = ordinary_object(machine);
            call_method(machine, "WeakMap", "set", weak_map, &[key, Value::int32(7)]).unwrap();
            machine
                .intrinsics
                .globals
                .insert(EcmaString::encode("rootWeakMap"), weak_map);
            let weak_map_slot = machine.runtime_slot(weak_map).unwrap().unwrap();
            machine.collect_garbage();
            assert_eq!(machine.runtime_slot(weak_map).unwrap(), Some(weak_map_slot));
            assert!(matches!(
                machine.runtime_slot(key),
                Err(RuntimeErrorKind::InvalidRuntimeHeapReference { .. })
            ));
            let HeapEntry::Collection { entries, .. } = &machine.heap[weak_map_slot] else {
                panic!("WeakMap remains a collection")
            };
            assert!(entries.is_empty());
        });
    }

    #[test]
    fn map_group_by_preserves_group_and_member_order() {
        fn parity<H: Host>(
            _machine: &mut Machine<'_, H>,
            _this: Value,
            args: &[Value],
            _constructing: bool,
        ) -> Result<BuiltinOutcome, EvalFailure> {
            let Some(Decoded::Int32(value)) = args.first().copied().and_then(Value::decode) else {
                return Err(type_error("test value must be an integer"));
            };
            Ok(BuiltinOutcome::Value(Value::int32(value % 2)))
        }

        with_machine(|machine| {
            let id = machine.intrinsics.builtins.register(BuiltinDef {
                name: "parity",
                length: 2,
                handler: parity::<TestHost>,
            });
            let callback = crate::intrinsics::native_function(
                &mut machine.heap,
                &mut machine.atoms,
                &mut machine.shapes,
                id,
                "parity",
                2,
            );
            let items = custom_iterable(
                machine,
                vec![Value::int32(1), Value::int32(2), Value::int32(3)],
            );
            let constructor = machine.intrinsics.global("Map").unwrap();
            let group_by = machine.get_named_property(constructor, "groupBy").unwrap();
            let grouped = machine
                .call_value(group_by, constructor, &[items, callback])
                .unwrap();
            let odd = call_method(machine, "Map", "get", grouped, &[Value::int32(1)]).unwrap();
            let even = call_method(machine, "Map", "get", grouped, &[Value::int32(0)]).unwrap();
            assert_eq!(
                machine.array_elements(odd).unwrap().unwrap(),
                vec![Value::int32(1), Value::int32(3)]
            );
            assert_eq!(
                machine.array_elements(even).unwrap().unwrap(),
                vec![Value::int32(2)]
            );
        });
    }

    #[test]
    fn set_keys_and_values_share_identity_and_weak_tags_exist() {
        with_machine(|machine| {
            assert_eq!(
                method(machine, "Set", "keys"),
                method(machine, "Set", "values")
            );
            for (name, expected) in [("WeakMap", "WeakMap"), ("WeakSet", "WeakSet")] {
                let constructor = machine.intrinsics.global(name).unwrap();
                let prototype = machine
                    .get_named_property(constructor, "prototype")
                    .unwrap();
                let key = machine
                    .property_key_from_value(machine.intrinsics.builtins.symbol_to_string_tag())
                    .unwrap();
                let tag = machine.get_property_key(prototype, &key).unwrap();
                let slot = machine.runtime_slot(tag).unwrap().unwrap();
                assert!(
                    matches!(&machine.heap[slot], HeapEntry::String(text) if text == &EcmaString::encode(expected))
                );
            }
        });
    }
}
