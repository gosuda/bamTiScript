use crate::heap::Heap;
use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use super::{
    allocate_array, builtin_property, define_data, heap_index, install_constructor_function,
    install_function, type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable, IteratorFamily};
use crate::vm::async_iterators::{ASYNC_FROM_SYNC_METHODS, ASYNC_GENERATOR_METHODS};
use crate::vm::generator_async::{GENERATOR_METHODS, GeneratorCompletion, GeneratorOperation};
use crate::{
    CollectionKind, EvalFailure, HeapEntry, Host, IterationKind, Machine, Property, PropertyKey,
    PropertyMap, ShapeTable, ThrowOrigin,
};

pub(super) fn install<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    install_map(heap, atoms, shapes, globals, builtins);
    install_set(heap, atoms, shapes, globals, builtins);
    install_weak_map(heap, atoms, shapes, globals, builtins);
    install_weak_set(heap, atoms, shapes, globals, builtins);
}

fn install_map<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "Map",
            length: 0,
            handler: map_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    for (name, length, handler) in [
        ("set", 2, map_set::<H> as BuiltinHandler<H>),
        ("get", 1, map_get::<H>),
        ("has", 1, map_has::<H>),
        ("delete", 1, map_delete::<H>),
        ("clear", 0, map_clear::<H>),
        ("keys", 0, map_keys::<H>),
        ("values", 0, map_values::<H>),
        ("entries", 0, map_entries::<H>),
        ("forEach", 1, map_for_each::<H>),
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
    let size = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get size",
            length: 0,
            handler: map_size::<H>,
        },
    );
    define_getter(heap, atoms, shapes, prototype, "size", size);
    let entries = named_property(heap, atoms, shapes, prototype, "entries");
    define_symbol(heap, shapes, prototype, builtins.symbol_iterator(), entries);
    let map_tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("Map")));
    define_to_string_tag(
        heap,
        shapes,
        prototype,
        builtins.symbol_to_string_tag(),
        map_tag,
    );
    globals.insert(EcmaString::encode("Map"), constructor);
}

fn install_set<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    builtins.set_set_prototype(prototype);
    super::set_methods::install(heap, atoms, shapes, builtins, prototype);
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "Set",
            length: 0,
            handler: set_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    for (name, length, handler) in [
        ("add", 1, set_add::<H> as BuiltinHandler<H>),
        ("has", 1, set_has::<H>),
        ("delete", 1, set_delete::<H>),
        ("clear", 0, set_clear::<H>),
        ("keys", 0, set_values::<H>),
        ("values", 0, set_values::<H>),
        ("entries", 0, set_entries::<H>),
        ("forEach", 1, set_for_each::<H>),
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
    let size = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get size",
            length: 0,
            handler: set_size::<H>,
        },
    );
    define_getter(heap, atoms, shapes, prototype, "size", size);
    let values = named_property(heap, atoms, shapes, prototype, "values");
    define_symbol(heap, shapes, prototype, builtins.symbol_iterator(), values);
    let set_tag = super::super::push(heap, HeapEntry::String(EcmaString::encode("Set")));
    define_to_string_tag(
        heap,
        shapes,
        prototype,
        builtins.symbol_to_string_tag(),
        set_tag,
    );
    globals.insert(EcmaString::encode("Set"), constructor);
}

fn install_weak_map<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "WeakMap",
            length: 0,
            handler: weak_map_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    for (name, length, handler) in [
        ("set", 2, weak_map_set::<H> as BuiltinHandler<H>),
        ("get", 1, weak_map_get::<H>),
        ("has", 1, weak_map_has::<H>),
        ("delete", 1, weak_map_delete::<H>),
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
    globals.insert(EcmaString::encode("WeakMap"), constructor);
}

fn install_weak_set<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "WeakSet",
            length: 0,
            handler: weak_set_constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    for (name, length, handler) in [
        ("add", 1, weak_set_add::<H> as BuiltinHandler<H>),
        ("has", 1, weak_set_has::<H>),
        ("delete", 1, weak_set_delete::<H>),
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
    globals.insert(EcmaString::encode("WeakSet"), constructor);
}

pub(super) fn install_iterator_prototype<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    let identity = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "[Symbol.iterator]",
            length: 0,
            handler: iterator_identity::<H>,
        },
    );
    define_symbol(
        heap,
        shapes,
        prototype,
        builtins.symbol_iterator(),
        identity,
    );
    builtins.set_iterator_prototype(prototype);
    let family_prototypes = [
        (
            "Array Iterator",
            array_iterator_next::<H> as BuiltinHandler<H>,
        ),
        ("Map Iterator", map_iterator_next::<H>),
        ("Set Iterator", set_iterator_next::<H>),
        ("String Iterator", string_iterator_next::<H>),
    ]
    .map(|(tag, handler)| {
        let family = ordinary(heap, Some(prototype));
        let next = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: "next",
                length: 0,
                handler,
            },
        );
        define_data(heap, atoms, shapes, family, "next", next);
        super::define_to_string_tag(heap, shapes, family, builtins.symbol_to_string_tag(), tag);
        family
    });
    builtins.set_iterator_family_prototypes(family_prototypes);
}

pub(super) fn install_async_iterator_prototype<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.object_prototype()));
    let identity = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "[Symbol.asyncIterator]",
            length: 0,
            handler: iterator_identity::<H>,
        },
    );
    define_symbol(
        heap,
        shapes,
        prototype,
        builtins.symbol_async_iterator(),
        identity,
    );
    builtins.set_async_iterator_prototype(prototype);
}

pub(super) fn install_generator_prototype<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.iterator_prototype()));
    let handlers = [
        generator_next::<H> as BuiltinHandler<H>,
        generator_return::<H> as BuiltinHandler<H>,
        generator_throw::<H> as BuiltinHandler<H>,
    ];
    for (method, handler) in GENERATOR_METHODS.into_iter().zip(handlers) {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: method.name,
                length: method.length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, prototype, method.name, function);
    }
    builtins.set_generator_prototype(prototype);
}

pub(super) fn install_async_generator_prototype<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = ordinary(heap, Some(builtins.async_iterator_prototype()));
    let handlers = [
        async_generator_next::<H> as BuiltinHandler<H>,
        async_generator_return::<H> as BuiltinHandler<H>,
        async_generator_throw::<H> as BuiltinHandler<H>,
    ];
    for (method, handler) in ASYNC_GENERATOR_METHODS.into_iter().zip(handlers) {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: method.name,
                length: method.length,
                handler,
            },
        );
        define_data(heap, atoms, shapes, prototype, method.name, function);
    }
    let adapter_prototype = ordinary(heap, Some(builtins.async_iterator_prototype()));
    let adapter_handlers = [
        async_from_sync_next::<H> as BuiltinHandler<H>,
        async_from_sync_return::<H> as BuiltinHandler<H>,
        async_from_sync_throw::<H> as BuiltinHandler<H>,
    ];
    for (method, handler) in ASYNC_FROM_SYNC_METHODS.into_iter().zip(adapter_handlers) {
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name: method.name,
                length: method.length,
                handler,
            },
        );
        define_data(
            heap,
            atoms,
            shapes,
            adapter_prototype,
            method.name,
            function,
        );
    }
    builtins.set_async_from_sync_iterator_prototype(adapter_prototype);
    builtins.set_async_generator_prototype(prototype);
}

fn resume_value(args: &[Value]) -> Value {
    args.first().copied().unwrap_or(Value::UNDEFINED)
}

fn async_generator_next<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::AsyncGeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Normal(resume_value(args)),
    })
}

fn async_generator_return<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::AsyncGeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Return(resume_value(args)),
    })
}

fn async_generator_throw<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::AsyncGeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Throw {
            value: resume_value(args),
            origin: ThrowOrigin::Bytecode,
        },
    })
}
fn async_from_sync_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .async_from_sync_iterator_method(this, GeneratorOperation::Next, resume_value(args))
        .map(BuiltinOutcome::Value)
}

fn async_from_sync_return<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .async_from_sync_iterator_method(this, GeneratorOperation::Return, resume_value(args))
        .map(BuiltinOutcome::Value)
}

fn async_from_sync_throw<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    machine
        .async_from_sync_iterator_method(this, GeneratorOperation::Throw, resume_value(args))
        .map(BuiltinOutcome::Value)
}

fn generator_next<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::GeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Normal(resume_value(args)),
    })
}

fn generator_return<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::GeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Return(resume_value(args)),
    })
}

fn generator_throw<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::GeneratorResume {
        generator: this,
        completion: GeneratorCompletion::Throw {
            value: resume_value(args),
            origin: ThrowOrigin::Bytecode,
        },
    })
}

fn iterator_family(kind: IterationKind) -> Option<IteratorFamily> {
    match kind {
        IterationKind::Key(family)
        | IterationKind::Value(family)
        | IterationKind::Entry(family) => Some(family),
        IterationKind::StringCodePoint => Some(IteratorFamily::String),
        IterationKind::RegExpString
        | IterationKind::IteratorHelper(_)
        | IterationKind::WrapForValid => None,
    }
}

pub(super) fn iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    source: Value,
    kind: IterationKind,
) -> Result<Value, EvalFailure> {
    let family = iterator_family(kind).expect("builtin iterator kind identifies its family");
    machine
        .allocate(HeapEntry::BuiltinIterator {
            source,
            kind,
            position: Some(0),
            properties: PropertyMap::default(),
            prototype: Some(
                machine
                    .intrinsics
                    .builtins
                    .iterator_family_prototype(family),
            ),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
}

fn iterator_identity<H: Host>(
    _machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(this))
}

fn array_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterator_next(machine, this, IteratorFamily::Array)
}

fn map_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterator_next(machine, this, IteratorFamily::Map)
}

fn set_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterator_next(machine, this, IteratorFamily::Set)
}

fn string_iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    iterator_next(machine, this, IteratorFamily::String)
}

fn iterator_next<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    family: IteratorFamily,
) -> Result<BuiltinOutcome, EvalFailure> {
    let Some(iterator_index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("iterator next called on incompatible receiver"));
    };
    let HeapEntry::BuiltinIterator {
        source,
        kind,
        position,
        ..
    } = machine.heap[iterator_index]
    else {
        return Err(type_error("iterator next called on incompatible receiver"));
    };
    if iterator_family(kind) != Some(family) {
        return Err(type_error("iterator next called on incompatible receiver"));
    }
    let (done, value) = machine.with_native_roots(&[this, source], |machine| {
        let Some(cursor) = position else {
            return Ok((true, Value::UNDEFINED));
        };
        let item = if family == IteratorFamily::Array {
            array_iterator_item(machine, iterator_index, source, kind, cursor)?
        } else {
            let source_index = machine
                .runtime_slot(source)
                .map_err(EvalFailure::Runtime)?
                .ok_or_else(|| type_error("iterator next called on incompatible receiver"))?;
            let item = match &machine.heap[source_index] {
                HeapEntry::Array { elements, .. } => {
                    usize::try_from(cursor).ok().and_then(|index| {
                        elements.get(index).map(|element| {
                            let next = cursor
                                .checked_add(1)
                                .expect("string bounds keep iterator positions below u64::MAX");
                            (next, crate::number_value(index as f64), *element)
                        })
                    })
                }
                HeapEntry::Collection { entries, .. } => {
                    debug_assert!(
                        entries.windows(2).all(|w| w[0].order <= w[1].order),
                        "collection entries must stay sorted ascending by order"
                    );
                    let index = entries.partition_point(|entry| entry.order < cursor);
                    entries[index..]
                        .iter()
                        .find(|entry| entry.live)
                        .map(|entry| {
                            let next = entry
                                .order
                                .checked_add(1)
                                .expect("heap limits keep collection order below u64::MAX");
                            (next, entry.key, entry.value)
                        })
                }
                _ => return Err(type_error("iterator next called on incompatible receiver")),
            };
            item.map(|(next, key, value)| {
                set_iterator_position(machine, iterator_index, Some(next));
                (key, value)
            })
        };
        match item {
            None => {
                set_iterator_position(machine, iterator_index, None);
                Ok((true, Value::UNDEFINED))
            }
            Some((key, item_value)) => {
                let value = match kind {
                    IterationKind::Key(_) => key,
                    IterationKind::Value(_) | IterationKind::StringCodePoint => item_value,
                    IterationKind::Entry(_) => allocate_array(machine, vec![key, item_value])?,
                    IterationKind::RegExpString
                    | IterationKind::IteratorHelper(_)
                    | IterationKind::WrapForValid => {
                        unreachable!("the family check admits only the four families")
                    }
                };
                Ok((false, value))
            }
        }
    })?;
    machine.with_native_roots(&[value], |machine| {
        machine
            .iterator_result(value, done)
            .map(BuiltinOutcome::Value)
    })
}

fn array_iterator_item<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator_index: usize,
    source: Value,
    kind: IterationKind,
    cursor: u64,
) -> Result<Option<(Value, Value)>, EvalFailure> {
    let source_index = machine.runtime_slot(source).map_err(EvalFailure::Runtime)?;
    let length = if source_index
        .is_some_and(|index| matches!(machine.heap[index], HeapEntry::TypedArray { .. }))
    {
        let bounds = super::typedarray::typed_array_bounds(machine, source)?;
        if bounds.out_of_bounds {
            return Err(type_error("iterated typed array is out of bounds"));
        }
        bounds.element_length
    } else {
        super::length_of_array_like(machine, source)?
    };
    if cursor >= length as u64 {
        return Ok(None);
    }

    set_iterator_position(machine, iterator_index, Some(cursor + 1));
    let key = crate::number_value(cursor as f64);
    let value = if matches!(kind, IterationKind::Key(_)) {
        Value::UNDEFINED
    } else {
        super::array::get_index(machine, source, cursor as usize)?
    };
    Ok(Some((key, value)))
}

fn set_iterator_position<H: Host>(
    machine: &mut Machine<'_, H>,
    iterator_index: usize,
    next: Option<u64>,
) {
    let HeapEntry::BuiltinIterator {
        source, position, ..
    } = &mut machine.heap[iterator_index]
    else {
        unreachable!("iterator brand was checked")
    };
    match next {
        Some(next) => {
            if let Some(position) = position {
                *position = next;
            }
        }
        None => {
            *position = None;
            *source = Value::UNDEFINED;
        }
    }
}

fn weak_map_set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_slot(machine, this, CollectionKind::WeakMap)?;
    let key = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_weak_key(machine, key)?;
    map_put(
        machine,
        this,
        key,
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
        CollectionKind::WeakMap,
    )?;
    Ok(BuiltinOutcome::Value(this))
}

fn map_get<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_get_for(machine, this, args, CollectionKind::Map)
}

fn weak_map_get<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_get_for(machine, this, args, CollectionKind::WeakMap)
}

fn map_get_for<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    expected: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, expected)?;
    let key = args.first().copied().unwrap_or(Value::UNDEFINED);
    let found =
        crate::collection_lookup(machine, slot, key).map_or(Value::UNDEFINED, |entry_index| {
            match &machine.heap[slot] {
                HeapEntry::Collection { entries, .. } => entries[entry_index].value,
                _ => unreachable!("collection brand was checked"),
            }
        });
    Ok(BuiltinOutcome::Value(found))
}

fn map_has<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_has_for(machine, this, args, CollectionKind::Map)
}

fn weak_map_has<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_has_for(machine, this, args, CollectionKind::WeakMap)
}

fn map_has_for<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    expected: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, expected)?;
    let key = args.first().copied().unwrap_or(Value::UNDEFINED);
    Ok(BuiltinOutcome::Value(Value::boolean(
        crate::collection_lookup(machine, slot, key).is_some(),
    )))
}

fn map_delete<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_delete_for(machine, this, args, CollectionKind::Map)
}

fn weak_map_delete<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_delete_for(machine, this, args, CollectionKind::WeakMap)
}

fn map_delete_for<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    expected: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, expected)?;
    let key = args.first().copied().unwrap_or(Value::UNDEFINED);
    let entry_index = crate::collection_lookup(machine, slot, key);
    let Some(entry_index) = entry_index else {
        return Ok(BuiltinOutcome::Value(Value::FALSE));
    };
    // Extract the entry key and tombstone in one mutable pass, then compute
    // the hash outside the mutable borrow to satisfy the borrow checker.
    let entry_key;
    {
        let HeapEntry::Collection { entries, size, .. } = &mut machine.heap[slot] else {
            unreachable!("collection brand was checked")
        };
        // Tombstone the entry rather than removing it: the `live` flag keeps
        // index positions stable so live iterators keep valid order cursors,
        // and only this one hash bucket needs pruning instead of a full rebuild.
        entries[entry_index].live = false;
        entry_key = entries[entry_index].key;
        *size = size
            .checked_sub(1)
            .expect("delete found a live entry so size is at least one");
    }
    let hash = crate::collection_key_hash(machine, entry_key);
    {
        let HeapEntry::Collection { index, .. } = &mut machine.heap[slot] else {
            unreachable!("collection brand was checked")
        };
        if let Some(bucket) = index.buckets.get_mut(&hash) {
            bucket.retain(|&idx| idx != entry_index);
            if bucket.is_empty() {
                index.buckets.remove(&hash);
            }
        }
    }
    machine.refund_slot(
        slot,
        crate::CollectionEntry::BYTES + crate::CollectionIndex::ENTRY_BYTES,
    );
    Ok(BuiltinOutcome::Value(Value::TRUE))
}

fn collection_clear<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    expected: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, expected)?;
    let removed = {
        let HeapEntry::Collection {
            entries,
            index,
            size,
            ..
        } = &mut machine.heap[slot]
        else {
            unreachable!("collection brand was checked")
        };
        let removed = *size;
        entries.clear();
        index.clear();
        *size = 0;
        removed
    };
    machine.refund_slot(
        slot,
        removed
            .checked_mul(crate::CollectionEntry::BYTES + crate::CollectionIndex::ENTRY_BYTES)
            .expect("collection entry charge fits heap limits"),
    );
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn map_clear<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_clear(machine, this, CollectionKind::Map)
}

fn map_size<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, CollectionKind::Map)?;
    let HeapEntry::Collection { size, .. } = &machine.heap[slot] else {
        unreachable!("collection brand was checked")
    };
    Ok(BuiltinOutcome::Value(crate::number_value(*size as f64)))
}

fn map_keys<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_iterator(
        machine,
        this,
        CollectionKind::Map,
        IterationKind::Key(IteratorFamily::Map),
    )
}

fn map_values<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_iterator(
        machine,
        this,
        CollectionKind::Map,
        IterationKind::Value(IteratorFamily::Map),
    )
}

fn map_entries<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_iterator(
        machine,
        this,
        CollectionKind::Map,
        IterationKind::Entry(IteratorFamily::Map),
    )
}

fn map_for_each<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_slot(machine, this, CollectionKind::Map)?;
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(type_error("Map.forEach callback is not callable"));
    }
    let mut cursor = 0;
    while let Some((next, key, value)) =
        collection_next(machine, this, CollectionKind::Map, cursor)?
    {
        cursor = next;
        machine.call_callback(
            callback,
            args.get(1).copied().unwrap_or(Value::UNDEFINED),
            &[value, key, this],
        )?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn weak_set_add<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_slot(machine, this, CollectionKind::WeakSet)?;
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    require_weak_key(machine, value)?;
    set_put(machine, this, value, CollectionKind::WeakSet)?;
    Ok(BuiltinOutcome::Value(this))
}

fn set_has<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_has_for(machine, this, args, CollectionKind::Set)
}

fn weak_set_has<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_has_for(machine, this, args, CollectionKind::WeakSet)
}

fn set_delete<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_delete_for(machine, this, args, CollectionKind::Set)
}

fn weak_set_delete<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    map_delete_for(machine, this, args, CollectionKind::WeakSet)
}

fn set_clear<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_clear(machine, this, CollectionKind::Set)
}

fn set_size<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, CollectionKind::Set)?;
    let HeapEntry::Collection { size, .. } = &machine.heap[slot] else {
        unreachable!("collection brand was checked")
    };
    Ok(BuiltinOutcome::Value(crate::number_value(*size as f64)))
}

fn set_values<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_iterator(
        machine,
        this,
        CollectionKind::Set,
        IterationKind::Value(IteratorFamily::Set),
    )
}

fn set_entries<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_iterator(
        machine,
        this,
        CollectionKind::Set,
        IterationKind::Entry(IteratorFamily::Set),
    )
}

fn set_for_each<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_slot(machine, this, CollectionKind::Set)?;
    let callback = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_callable(callback)? {
        return Err(type_error("Set.forEach callback is not callable"));
    }
    let mut cursor = 0;
    while let Some((next, _, value)) = collection_next(machine, this, CollectionKind::Set, cursor)?
    {
        cursor = next;
        machine.call_callback(
            callback,
            args.get(1).copied().unwrap_or(Value::UNDEFINED),
            &[value, value, this],
        )?;
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

pub(super) fn map_put<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    key: Value,
    value: Value,
    expected: CollectionKind,
) -> Result<(), EvalFailure> {
    let slot = collection_slot(machine, object, expected)?;
    let existing = crate::collection_lookup(machine, slot, key);
    if let Some(entry_index) = existing {
        let HeapEntry::Collection { entries, .. } = &mut machine.heap[slot] else {
            unreachable!("collection brand was checked")
        };
        entries[entry_index].value = value;
        return Ok(());
    }
    append_collection_entry(machine, slot, key, value)
}

fn set_put<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    value: Value,
    expected: CollectionKind,
) -> Result<(), EvalFailure> {
    let slot = collection_slot(machine, object, expected)?;
    let exists = crate::collection_lookup(machine, slot, value).is_some();
    if exists {
        return Ok(());
    }
    append_collection_entry(machine, slot, value, value)
}

pub(super) fn append_collection_entry<H: Host>(
    machine: &mut Machine<'_, H>,
    slot: usize,
    key: Value,
    value: Value,
) -> Result<(), EvalFailure> {
    let order = match machine.heap[slot] {
        HeapEntry::Collection { next_order, .. } => next_order,
        _ => unreachable!("collection slot owns collection storage"),
    };
    let next_order = order
        .checked_add(1)
        .expect("heap limits keep collection order below u64::MAX");
    let hash = crate::collection_key_hash(machine, key);
    machine
        .charge_slot(
            slot,
            crate::CollectionEntry::BYTES + crate::CollectionIndex::ENTRY_BYTES,
        )
        .map_err(EvalFailure::Runtime)?;
    // Push-only insertion keeps `entries` sorted ascending by `order`, which
    // `collection_next`/`iterator_next` rely on for their binary-search cursor
    // (`partition_point(|e| e.order < cursor)`). Reusing a tombstoned slot
    // would write the largest order so far into an early position and break
    // that, silently skipping live entries during iteration.
    let needs_compact = {
        let HeapEntry::Collection {
            entries,
            index,
            size,
            next_order: stored_next_order,
            ..
        } = &mut machine.heap[slot]
        else {
            unreachable!("collection slot owns collection storage")
        };
        entries.push(crate::CollectionEntry {
            order,
            key,
            value,
            live: true,
        });
        let entry_index = entries.len() - 1;
        index.insert(hash, entry_index);
        *size += 1;
        *stored_next_order = next_order;
        entries.len() > size.saturating_mul(2)
    };
    if needs_compact {
        compact_collection(machine, slot);
    }
    Ok(())
}

/// Drop tombstoned entries and rebuild the hash index, bounding the entries
/// vector under churn. Live entries retain their `order` values, preserving
/// the sorted-by-order invariant and any outstanding iterator cursor. Mirrors
/// the rebuild pattern used by GC weak-collection purging.
fn compact_collection<H: Host>(machine: &mut Machine<'_, H>, slot: usize) {
    let (retained, rebuilt) = {
        let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
            unreachable!("collection slot owns collection storage")
        };
        let retained: Vec<_> = entries.iter().copied().filter(|e| e.live).collect();
        let mut rebuilt = crate::CollectionIndex::default();
        for (i, entry) in retained.iter().enumerate() {
            rebuilt.insert(crate::collection_key_hash(machine, entry.key), i);
        }
        (retained, rebuilt)
    };
    let HeapEntry::Collection { entries, index, .. } = &mut machine.heap[slot] else {
        unreachable!("collection slot owns collection storage")
    };
    *entries = retained;
    *index = rebuilt;
}

pub(super) fn collection_slot<H: Host>(
    machine: &Machine<'_, H>,
    object: Value,
    expected: CollectionKind,
) -> Result<usize, EvalFailure> {
    let Some(index) = machine.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "collection method called on incompatible receiver",
        ));
    };
    if !matches!(machine.heap[index], HeapEntry::Collection { kind, .. } if kind == expected) {
        return Err(type_error(
            "collection method called on incompatible receiver",
        ));
    }
    Ok(index)
}

fn collection_next<H: Host>(
    machine: &Machine<'_, H>,
    object: Value,
    expected: CollectionKind,
    cursor: u64,
) -> Result<Option<(u64, Value, Value)>, EvalFailure> {
    let slot = collection_slot(machine, object, expected)?;
    let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
        unreachable!("collection brand was checked")
    };
    debug_assert!(
        entries.windows(2).all(|w| w[0].order <= w[1].order),
        "collection entries must stay sorted ascending by order"
    );
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
                entry.value,
            )
        }))
}

fn collection_iterator<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    expected: CollectionKind,
    kind: IterationKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    collection_slot(machine, object, expected)?;
    Ok(BuiltinOutcome::Value(iterator(machine, object, kind)?))
}

pub(super) fn require_weak_key<H: Host>(
    machine: &Machine<'_, H>,
    key: Value,
) -> Result<(), EvalFailure> {
    let Some(index) = machine.runtime_slot(key).map_err(EvalFailure::Runtime)? else {
        return Err(type_error("Invalid value used as weak collection key"));
    };
    // Exhaustive match: every HeapEntry variant is listed so adding a new
    // one forces a decision here instead of silently rejecting it via `_`.
    let valid = match &machine.heap[index] {
        HeapEntry::Symbol { description } => {
            // O(log n) registry lookup by description instead of scanning
            // every registered symbol value on each weak-key validation.
            !machine
                .intrinsics
                .symbol_registry
                .get(description)
                .is_some_and(|registered| *registered == key)
        }
        HeapEntry::Object { .. }
        | HeapEntry::Array { .. }
        | HeapEntry::Function { .. }
        | HeapEntry::Script { .. }
        | HeapEntry::ModuleNamespace { .. }
        | HeapEntry::ExternalModuleNamespace { .. }
        | HeapEntry::HashState { .. }
        | HeapEntry::RegExp { .. }
        | HeapEntry::Date { .. }
        | HeapEntry::Temporal { .. }
        | HeapEntry::Intl { .. }
        | HeapEntry::Collection { .. }
        | HeapEntry::TypedArray { .. }
        | HeapEntry::ArrayBuffer { .. }
        | HeapEntry::SharedArrayBuffer { .. }
        | HeapEntry::DataView { .. }
        | HeapEntry::BuiltinIterator { .. }
        | HeapEntry::Generator { .. }
        | HeapEntry::AsyncGenerator { .. }
        | HeapEntry::AsyncFromSync { .. }
        | HeapEntry::ProcessEnv { .. }
        | HeapEntry::Promise { .. }
        | HeapEntry::DisposableStack { .. }
        | HeapEntry::Timeout { .. }
        | HeapEntry::WeakRef { .. }
        | HeapEntry::FinalizationRegistry { .. }
        | HeapEntry::Proxy { .. }
        | HeapEntry::ProxyRevoker { .. }
        | HeapEntry::NativeFunction { .. } => true,
        // Primitives and internal bookkeeping entries are not valid keys.
        HeapEntry::Vacant
        | HeapEntry::String(_)
        | HeapEntry::Rope { .. }
        | HeapEntry::BigInt(_)
        | HeapEntry::PrivateName { .. }
        | HeapEntry::Iterator { .. }
        | HeapEntry::PromiseResolver { .. }
        | HeapEntry::PromiseAll { .. }
        | HeapEntry::PromiseAllElement { .. }
        | HeapEntry::AsyncActivation { .. } => false,
    };
    if valid {
        Ok(())
    } else {
        Err(type_error("Invalid value used as weak collection key"))
    }
}

pub(super) fn ordinary_intrinsic(heap: &mut Heap, prototype: Value) -> Value {
    ordinary(heap, Some(prototype))
}
fn ordinary(heap: &mut Heap, prototype: Option<Value>) -> Value {
    super::super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            extensible: true,
            boxed_primitive: None,
        },
    )
}
pub(crate) fn ordinary_runtime<H: Host>(
    machine: &mut Machine<'_, H>,
    prototype: Option<Value>,
) -> Result<Value, EvalFailure> {
    machine
        .allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype,
            extensible: true,
            boxed_primitive: None,
        })
        .map_err(EvalFailure::Runtime)
}
fn define_getter(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    getter: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        Property::Accessor {
            getter: Some(getter),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
}
fn define_symbol(
    heap: &mut Heap,
    shapes: &mut crate::ShapeTable,
    object: Value,
    symbol: Value,
    value: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(symbol) as u32),
        builtin_property(value),
    );
}
fn define_to_string_tag(
    heap: &mut Heap,
    shapes: &mut crate::ShapeTable,
    object: Value,
    symbol: Value,
    value: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(symbol) as u32),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
}
fn named_property(
    heap: &Heap,
    atoms: &mut crate::AtomTable,
    shapes: &crate::ShapeTable,
    object: Value,
    name: &str,
) -> Value {
    let HeapEntry::Object { properties, .. } = &heap[heap_index(object)] else {
        unreachable!()
    };
    match properties.get(shapes, &PropertyKey::Named(atoms.intern_str(name))) {
        Some(Property::Data { value, .. }) => *value,
        _ => unreachable!(),
    }
}

/// Layers the collection extras over the base installs: species getters,
/// `Map.groupBy`, the `getOrInsert` variants, the shared Set `keys` object,
/// and the weak-collection tags.
pub(super) fn install_collection_edge<H: Host>(
    heap: &mut Heap,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let map = installed_constructor(heap, atoms, shapes, globals, "Map");
    let set = installed_constructor(heap, atoms, shapes, globals, "Set");
    let weak_map = installed_constructor(heap, atoms, shapes, globals, "WeakMap");
    let weak_set = installed_constructor(heap, atoms, shapes, globals, "WeakSet");

    for constructor in [map.constructor, set.constructor] {
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
            crate::Property::Accessor {
                getter: Some(species),
                setter: None,
                enumerable: false,
                configurable: true,
            },
        );
    }

    let group_by = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "groupBy",
            length: 2,
            handler: map_group_by::<H>,
        },
    );
    define_constructor_data(heap, atoms, shapes, map.constructor, "groupBy", group_by);
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
        let function = install_function(
            heap,
            atoms,
            shapes,
            builtins,
            crate::intrinsics::BuiltinDef {
                name,
                length: 2,
                handler,
            },
        );
        define_data(heap, atoms, shapes, target, name, function);
    }
    // Set.prototype.keys and Set.prototype.values are the same function object.
    let values = own_data_property(heap, atoms, shapes, set.prototype, "values");
    define_data(heap, atoms, shapes, set.prototype, "keys", values);

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

fn installed_constructor(
    heap: &Heap,
    atoms: &mut crate::AtomTable,
    shapes: &ShapeTable,
    globals: &BTreeMap<EcmaString, Value>,
    name: &'static str,
) -> InstalledConstructor {
    let constructor = globals
        .get(&EcmaString::encode(name))
        .copied()
        .expect("base collection constructor is installed first");
    let prototype = own_data_property(heap, atoms, shapes, constructor, "prototype");
    InstalledConstructor {
        constructor,
        prototype,
    }
}

fn own_data_property(
    heap: &Heap,
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
    match properties.get(
        shapes,
        &PropertyKey::Named(atoms.intern(EcmaString::encode(name))),
    ) {
        Some(Property::Data { value, .. }) => *value,
        _ => panic!("collection intrinsic data property must exist"),
    }
}

fn define_constructor_data(
    heap: &mut Heap,
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
    heap: &mut Heap,
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

fn map_set<H: Host>(
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

fn set_add<H: Host>(
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
        require_weak_key(machine, key)?;
        return Ok(key);
    }
    Ok(canonical_collection_key(key))
}

fn existing_value<H: Host>(machine: &mut Machine<'_, H>, slot: usize, key: Value) -> Option<Value> {
    let entry_index = crate::collection_lookup(machine, slot, key)?;
    match &machine.heap[slot] {
        HeapEntry::Collection { entries, .. } => Some(entries[entry_index].value),
        _ => unreachable!("collection brand was checked"),
    }
}

fn get_or_insert<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    kind: CollectionKind,
) -> Result<BuiltinOutcome, EvalFailure> {
    let slot = collection_slot(machine, this, kind)?;
    let key = upsert_key(
        machine,
        args.first().copied().unwrap_or(Value::UNDEFINED),
        kind,
    )?;
    if let Some(existing) = existing_value(machine, slot, key) {
        return Ok(BuiltinOutcome::Value(existing));
    }
    let value = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    append_collection_entry(machine, slot, key, value)?;
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
    let slot = collection_slot(machine, this, kind)?;
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
    map_put(machine, this, key, value, kind)?;
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
    let kind_matches = matches!(
        &machine.heap[slot],
        HeapEntry::Collection { kind, .. } if *kind == expected
    );
    let existing = if kind_matches {
        crate::collection_lookup(machine, slot, key)
    } else {
        return Err(type_error(
            "collection method called on incompatible receiver",
        ));
    };
    if let Some(entry_index) = existing {
        let HeapEntry::Collection { entries, .. } = &mut machine.heap[slot] else {
            unreachable!("collection brand checked above")
        };
        entries[entry_index].value = value;
        return Ok(());
    }
    append_collection_entry(machine, slot, key, value)
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
    let is_map = matches!(&machine.heap[slot], HeapEntry::Collection { .. });
    if !is_map {
        return Err(type_error("Map.groupBy result is not a Map"));
    }
    if let Some(entry_index) = crate::collection_lookup(machine, slot, key) {
        let group = match &machine.heap[slot] {
            HeapEntry::Collection { entries, .. } => entries[entry_index].value,
            _ => unreachable!("Map brand checked above"),
        };
        machine.array_push(group, value)?;
        return Ok(());
    }
    let group = allocate_array(machine, vec![value])?;
    append_collection_entry(machine, slot, key, group)
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, custom_iterable, ordinary_object};
    use super::*;
    use crate::{
        CollectionEntry, CollectionIndex, Limits, NativeCallable, RuntimeErrorKind, ThrowOrigin,
    };

    fn construct_builtin(
        machine: &mut Machine<'_, TestHost>,
        name: &str,
        arguments: &[Value],
    ) -> Value {
        let constructor = machine.intrinsics.global(name).expect("global exists");
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("constructor is native")
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, arguments, true)
            .unwrap()
        else {
            panic!("constructor returns a value")
        };
        value
    }

    fn builtin_id(machine: &Machine<'_, TestHost>, name: &str) -> crate::intrinsics::BuiltinId {
        let constructor = machine.intrinsics.global(name).expect("global exists");
        let index = machine.runtime_slot(constructor).unwrap().unwrap();
        match machine.heap[index] {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => id,
            _ => panic!("not a builtin constructor"),
        }
    }

    // ---- custom iterable helpers -------------------------------------------

    /// Creates an object-shaped entry with properties "0" and "1" (not an array).
    fn entry_pair(machine: &mut Machine<'_, TestHost>, key: Value, value: Value) -> Value {
        let entry = ordinary_object(machine);
        machine.set_data_property(entry, "0", key).unwrap();
        machine.set_data_property(entry, "1", value).unwrap();
        entry
    }

    fn collection_entries(machine: &Machine<'_, TestHost>, obj: Value) -> Vec<(Value, Value)> {
        let slot = machine
            .runtime_slot(obj)
            .unwrap()
            .expect("runtime collection");
        let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
            panic!("not a collection")
        };
        entries
            .iter()
            .filter(|entry| entry.live)
            .map(|entry| (entry.key, entry.value))
            .collect()
    }

    fn prototype_method_id(
        machine: &mut Machine<'_, TestHost>,
        constructor_name: &str,
        method_name: &str,
    ) -> crate::intrinsics::BuiltinId {
        let constructor = machine
            .intrinsics
            .global(constructor_name)
            .expect("global exists");
        let prototype = machine
            .get_named_property(constructor, "prototype")
            .expect("constructor has prototype");
        let function = machine
            .get_named_property(prototype, method_name)
            .expect("prototype method exists");
        let index = machine.runtime_slot(function).unwrap().unwrap();
        match machine.heap[index] {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => id,
            _ => panic!("prototype method is builtin"),
        }
    }

    fn call_prototype_method(
        machine: &mut Machine<'_, TestHost>,
        constructor_name: &str,
        method_name: &str,
        receiver: Value,
        arguments: &[Value],
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let id = prototype_method_id(machine, constructor_name, method_name);
        machine.call_builtin(id, receiver, arguments, false)
    }

    fn assert_type_error(result: Result<BuiltinOutcome, EvalFailure>) {
        assert!(matches!(
            result,
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    fn symbol_for(machine: &mut Machine<'_, TestHost>, key: Value) -> Value {
        let symbol = machine.intrinsics.global("Symbol").expect("Symbol exists");
        let function = machine
            .get_named_property(symbol, "for")
            .expect("Symbol.for exists");
        let index = machine.runtime_slot(function).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            callable: NativeCallable::Builtin(id),
            ..
        } = machine.heap[index]
        else {
            panic!("Symbol.for is builtin")
        };
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, &[key], false)
            .expect("Symbol.for returns a symbol")
        else {
            panic!("Symbol.for returns a value")
        };
        value
    }

    fn local_symbol(machine: &mut Machine<'_, TestHost>) -> Value {
        let id = builtin_id(machine, "Symbol");
        let BuiltinOutcome::Value(value) = machine
            .call_builtin(id, Value::UNDEFINED, &[], false)
            .expect("Symbol returns a symbol")
        else {
            panic!("Symbol returns a value")
        };
        value
    }

    // ---- tests -------------------------------------------------------------

    #[test]
    fn map_consumes_generic_iterable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let e1 = allocate_array(&mut machine, vec![Value::int32(1), Value::int32(10)]).unwrap();
        let e2 = allocate_array(&mut machine, vec![Value::int32(2), Value::int32(20)]).unwrap();
        let source = custom_iterable(&mut machine, vec![e1, e2]);

        let map = construct_builtin(&mut machine, "Map", &[source]);
        let entries = collection_entries(&machine, map);
        assert_eq!(
            entries,
            vec![
                (Value::int32(1), Value::int32(10)),
                (Value::int32(2), Value::int32(20)),
            ]
        );
    }

    #[test]
    fn map_accepts_object_shaped_entries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let e1 = entry_pair(&mut machine, Value::int32(1), Value::int32(10));
        let e2 = entry_pair(&mut machine, Value::int32(2), Value::int32(20));
        let source = custom_iterable(&mut machine, vec![e1, e2]);

        let map = construct_builtin(&mut machine, "Map", &[source]);
        let entries = collection_entries(&machine, map);
        assert_eq!(
            entries,
            vec![
                (Value::int32(1), Value::int32(10)),
                (Value::int32(2), Value::int32(20)),
            ]
        );
    }

    #[test]
    fn map_rejects_primitive_entries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // Iterator yields a primitive number, not an object-shaped entry.
        let source = custom_iterable(&mut machine, vec![Value::int32(42)]);
        let id = builtin_id(&machine, "Map");
        let result = machine.call_builtin(id, Value::UNDEFINED, &[source], true);
        assert!(result.is_err(), "Map with primitive entry must fail");
    }

    #[test]
    fn set_consumes_generic_iterable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let source = custom_iterable(
            &mut machine,
            vec![Value::int32(10), Value::int32(20), Value::int32(30)],
        );

        let set = construct_builtin(&mut machine, "Set", &[source]);
        let entries = collection_entries(&machine, set);
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[0].1, Value::int32(10));
        assert_eq!(entries[1].1, Value::int32(20));
        assert_eq!(entries[2].1, Value::int32(30));
    }

    #[test]
    fn weak_map_preserves_weak_key_check_from_iterable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // Entry with a primitive key — WeakMap must reject it even though the
        // entry comes through the iterator protocol.
        let e1 = entry_pair(&mut machine, Value::int32(1), Value::int32(10));
        let source = custom_iterable(&mut machine, vec![e1]);

        let id = builtin_id(&machine, "WeakMap");
        assert_type_error(machine.call_builtin(id, Value::UNDEFINED, &[source], true));
    }
    #[test]
    fn collection_methods_reject_every_other_collection_brand() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        let set = construct_builtin(&mut machine, "Set", &[]);
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let weak_set = construct_builtin(&mut machine, "WeakSet", &[]);
        let key = ordinary_object(&mut machine);

        for receiver in [set, weak_map, weak_set] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "Map",
                "set",
                receiver,
                &[key, Value::int32(1)],
            ));
        }
        for receiver in [map, weak_map, weak_set] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "Set",
                "add",
                receiver,
                &[key],
            ));
        }
        for receiver in [map, set, weak_set] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "WeakMap",
                "set",
                receiver,
                &[key, Value::int32(1)],
            ));
        }
        for receiver in [map, set, weak_map] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "WeakSet",
                "add",
                receiver,
                &[key],
            ));
        }
        for receiver in [set, weak_map, weak_set] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "Map",
                "keys",
                receiver,
                &[],
            ));
        }
        for receiver in [map, weak_map, weak_set] {
            assert_type_error(call_prototype_method(
                &mut machine,
                "Set",
                "values",
                receiver,
                &[],
            ));
        }

        for (constructor, receiver) in [
            ("Map", map),
            ("Set", set),
            ("WeakMap", weak_map),
            ("WeakSet", weak_set),
        ] {
            assert!(matches!(
                call_prototype_method(&mut machine, constructor, "has", receiver, &[key]),
                Ok(BuiltinOutcome::Value(Value::FALSE))
            ));
        }
    }

    #[test]
    fn weak_collections_accept_local_symbol_keys() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol = local_symbol(&mut machine);
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let weak_set = construct_builtin(&mut machine, "WeakSet", &[]);

        assert!(matches!(
            call_prototype_method(
                &mut machine,
                "WeakMap",
                "set",
                weak_map,
                &[symbol, Value::int32(7)],
            ),
            Ok(BuiltinOutcome::Value(value)) if value == weak_map
        ));
        assert!(matches!(
            call_prototype_method(&mut machine, "WeakMap", "get", weak_map, &[symbol]),
            Ok(BuiltinOutcome::Value(value)) if value == Value::int32(7)
        ));
        assert!(matches!(
            call_prototype_method(&mut machine, "WeakSet", "add", weak_set, &[symbol]),
            Ok(BuiltinOutcome::Value(value)) if value == weak_set
        ));
        assert!(matches!(
            call_prototype_method(&mut machine, "WeakSet", "has", weak_set, &[symbol]),
            Ok(BuiltinOutcome::Value(Value::TRUE))
        ));
    }

    #[test]
    fn weak_collections_reject_registered_symbol_keys() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol = symbol_for(&mut machine, Value::int32(1));
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);

        assert_type_error(call_prototype_method(
            &mut machine,
            "WeakMap",
            "set",
            weak_map,
            &[symbol, Value::int32(7)],
        ));
        let entry = entry_pair(&mut machine, symbol, Value::int32(7));
        let source = custom_iterable(&mut machine, vec![entry]);
        let id = builtin_id(&machine, "WeakMap");
        assert_type_error(machine.call_builtin(id, Value::UNDEFINED, &[source], true));
    }

    #[test]
    fn weak_collection_mutators_reject_primitive_keys() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let weak_set = construct_builtin(&mut machine, "WeakSet", &[]);

        assert_type_error(call_prototype_method(
            &mut machine,
            "WeakMap",
            "set",
            weak_map,
            &[Value::int32(1), Value::int32(7)],
        ));
        assert_type_error(call_prototype_method(
            &mut machine,
            "WeakSet",
            "add",
            weak_set,
            &[Value::int32(1)],
        ));
    }

    #[test]
    fn map_consumes_array_through_protocol() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let e1 = allocate_array(&mut machine, vec![Value::int32(1), Value::int32(10)]).unwrap();
        let e2 = allocate_array(&mut machine, vec![Value::int32(2), Value::int32(20)]).unwrap();
        let source = allocate_array(&mut machine, vec![e1, e2]).unwrap();

        let map = construct_builtin(&mut machine, "Map", &[source]);
        let entries = collection_entries(&machine, map);
        assert_eq!(
            entries,
            vec![
                (Value::int32(1), Value::int32(10)),
                (Value::int32(2), Value::int32(20)),
            ]
        );
    }

    // ---- %GeneratorPrototype% tests ----------------------------------------

    #[test]
    fn each_iterator_family_owns_next_and_rejects_the_others() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let iterator_prototype = machine.intrinsics.builtins.iterator_prototype();
        assert_eq!(
            machine
                .get_named_property(iterator_prototype, "next")
                .unwrap(),
            Value::UNDEFINED,
            "a subclass of Iterator must not inherit a builtin next"
        );
        let array = allocate_array(&mut machine, Vec::new()).unwrap();
        let array_iterator = iterator(
            &mut machine,
            array,
            IterationKind::Value(IteratorFamily::Array),
        )
        .unwrap();
        let map_constructor = machine.intrinsics.global("Map").unwrap();
        let map = machine.construct_value(map_constructor, &[]).unwrap();
        let map_iterator =
            iterator(&mut machine, map, IterationKind::Entry(IteratorFamily::Map)).unwrap();

        let array_next = machine.get_named_property(array_iterator, "next").unwrap();
        let map_next = machine.get_named_property(map_iterator, "next").unwrap();
        assert_ne!(array_next, map_next);
        assert!(machine.call_value(array_next, array_iterator, &[]).is_ok());
        assert!(matches!(
            machine.call_value(array_next, map_iterator, &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn generator_prototype_chains_to_iterator_prototype() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let machine = Machine::new(&module, &mut host, Limits::default());

        let gen_proto = machine.intrinsics.builtins.generator_prototype();
        let iter_proto = machine.intrinsics.builtins.iterator_prototype();
        assert!(
            machine
                .inherits_from_prototype(gen_proto, iter_proto)
                .unwrap(),
            "%GeneratorPrototype% must inherit from %IteratorPrototype%"
        );
    }

    #[test]
    fn async_generator_prototype_chains_to_async_iterator_prototype() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let machine = Machine::new(&module, &mut host, Limits::default());

        let async_gen_proto = machine.intrinsics.builtins.async_generator_prototype();
        let async_iter_proto = machine.intrinsics.builtins.async_iterator_prototype();
        assert!(
            machine
                .inherits_from_prototype(async_gen_proto, async_iter_proto)
                .unwrap(),
            "%AsyncGeneratorPrototype% must inherit from %AsyncIteratorPrototype%"
        );
    }

    #[test]
    fn generator_method_surface_has_expected_metadata_and_descriptors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for (label, prototype) in [
            (
                "Generator",
                machine.intrinsics.builtins.generator_prototype(),
            ),
            (
                "AsyncGenerator",
                machine.intrinsics.builtins.async_generator_prototype(),
            ),
        ] {
            for name in ["next", "return", "throw"] {
                let key = PropertyKey::Named(machine.intern_str(name));
                let method_descriptor = machine
                    .own_descriptor(prototype, &key)
                    .unwrap()
                    .unwrap_or_else(|| panic!("{label}.prototype.{name} must be an own property"));
                let Property::Data {
                    value: method,
                    writable,
                    enumerable,
                    configurable,
                } = method_descriptor
                else {
                    panic!("{label}.prototype.{name} must be a data property");
                };
                assert!(writable, "{label}.prototype.{name} must be writable");
                assert!(
                    !enumerable,
                    "{label}.prototype.{name} must not be enumerable"
                );
                assert!(
                    configurable,
                    "{label}.prototype.{name} must be configurable"
                );

                let index = machine.runtime_slot(method).unwrap().unwrap();
                let HeapEntry::NativeFunction {
                    callable: NativeCallable::Builtin(id),
                    ..
                } = machine.heap[index]
                else {
                    panic!("{label}.prototype.{name} must be a native function");
                };
                let definition = machine.intrinsics.builtins.get(id);
                assert_eq!(definition.name, name, "{label}.prototype.{name} name");
                assert_eq!(definition.length, 1, "{label}.prototype.{name} length");

                for metadata in ["name", "length"] {
                    let metadata_key = PropertyKey::Named(machine.intern_str(metadata));
                    let descriptor = machine
                        .own_descriptor(method, &metadata_key)
                        .unwrap()
                        .unwrap_or_else(|| {
                            panic!("{label}.prototype.{name}.{metadata} must exist")
                        });
                    assert!(
                        matches!(
                            descriptor,
                            Property::Data {
                                writable: false,
                                enumerable: false,
                                configurable: true,
                                ..
                            }
                        ),
                        "{label}.prototype.{name}.{metadata} has the wrong descriptor: {descriptor:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn generator_methods_use_operation_specific_brand_errors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let prototype = machine.intrinsics.builtins.generator_prototype();
        let receiver = ordinary_object(&mut machine);

        for name in ["next", "return", "throw"] {
            let method = machine.get_named_property(prototype, name).unwrap();
            let error = machine.call_value(method, receiver, &[]).unwrap_err();
            assert!(matches!(
                error,
                EvalFailure::Throw(ThrowOrigin::TypeError { operation })
                    if operation == match name {
                        "next" => "Generator.prototype.next called on incompatible receiver",
                        "return" => "Generator.prototype.return called on incompatible receiver",
                        "throw" => "Generator.prototype.throw called on incompatible receiver",
                        _ => unreachable!(),
                    }
            ));
        }
    }

    #[test]
    fn async_generator_methods_reject_bad_receivers_without_throwing() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let prototype = machine.intrinsics.builtins.async_generator_prototype();
        let receiver = ordinary_object(&mut machine);

        for name in ["next", "return", "throw"] {
            let method = machine.get_named_property(prototype, name).unwrap();
            let promise = machine
                .call_value(method, receiver, &[])
                .unwrap_or_else(|error| panic!("AsyncGenerator.prototype.{name} threw: {error:?}"));
            let index = machine.runtime_slot(promise).unwrap().unwrap();
            assert!(
                matches!(
                    &machine.heap[index],
                    HeapEntry::Promise {
                        state: crate::PromiseState::Rejected {
                            origin: ThrowOrigin::TypeError { operation },
                            ..
                        },
                        ..
                    } if *operation == match name {
                        "next" => "AsyncGenerator.prototype.next called on incompatible receiver",
                        "return" => "AsyncGenerator.prototype.return called on incompatible receiver",
                        "throw" => "AsyncGenerator.prototype.throw called on incompatible receiver",
                        _ => unreachable!(),
                    }
                ),
                "AsyncGenerator.prototype.{name} must return an operation-specific rejected promise"
            );
        }
    }

    #[test]
    fn generator_resume_outcomes_package_receiver_completion_and_default_value() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let receiver = ordinary_object(&mut machine);
        let resume = Value::int32(42);

        for (name, expected) in [
            ("next", GeneratorCompletion::Normal(resume)),
            ("return", GeneratorCompletion::Return(resume)),
            (
                "throw",
                GeneratorCompletion::Throw {
                    value: resume,
                    origin: ThrowOrigin::Bytecode,
                },
            ),
        ] {
            let method = machine
                .get_named_property(machine.intrinsics.builtins.generator_prototype(), name)
                .unwrap();
            let index = machine.runtime_slot(method).unwrap().unwrap();
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } = machine.heap[index]
            else {
                panic!("{name} must be a native function");
            };
            let outcome = machine
                .call_builtin(id, receiver, &[resume], false)
                .unwrap();
            match outcome {
                BuiltinOutcome::GeneratorResume {
                    generator,
                    completion,
                } => {
                    assert_eq!(generator, receiver);
                    assert_eq!(completion, expected);
                }
                other => panic!("expected GeneratorResume, got {other:?}"),
            }

            let outcome = machine.call_builtin(id, receiver, &[], false).unwrap();
            let BuiltinOutcome::GeneratorResume { completion, .. } = outcome else {
                panic!("expected GeneratorResume");
            };
            assert_eq!(completion.value(), Value::UNDEFINED);
        }
    }

    #[test]
    fn async_generator_resume_outcomes_package_receiver_completion_and_default_value() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let receiver = ordinary_object(&mut machine);
        let resume = Value::int32(42);

        for (name, expected) in [
            ("next", GeneratorCompletion::Normal(resume)),
            ("return", GeneratorCompletion::Return(resume)),
            (
                "throw",
                GeneratorCompletion::Throw {
                    value: resume,
                    origin: ThrowOrigin::Bytecode,
                },
            ),
        ] {
            let method = machine
                .get_named_property(
                    machine.intrinsics.builtins.async_generator_prototype(),
                    name,
                )
                .unwrap();
            let index = machine.runtime_slot(method).unwrap().unwrap();
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } = machine.heap[index]
            else {
                panic!("{name} must be a native function");
            };
            let outcome = machine
                .call_builtin(id, receiver, &[resume], false)
                .unwrap();
            match outcome {
                BuiltinOutcome::AsyncGeneratorResume {
                    generator,
                    completion,
                } => {
                    assert_eq!(generator, receiver);
                    assert_eq!(completion, expected);
                }
                other => panic!("expected AsyncGeneratorResume, got {other:?}"),
            }

            let outcome = machine.call_builtin(id, receiver, &[], false).unwrap();
            let BuiltinOutcome::AsyncGeneratorResume { completion, .. } = outcome else {
                panic!("expected AsyncGeneratorResume");
            };
            assert_eq!(completion.value(), Value::UNDEFINED);
        }
    }

    #[test]
    fn iterator_result_completed_shape() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let value = Value::int32(99);
        let result = machine.iterator_result(value, true).unwrap();
        let result_value = machine.get_named_property(result, "value").unwrap();
        let done = machine.get_named_property(result, "done").unwrap();
        assert_eq!(result_value, value);
        assert_eq!(done, Value::TRUE);
    }

    #[test]
    fn builtin_iterator_results_have_own_data_properties_and_object_prototype() {
        fn inherited_setter(
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
        let array = allocate_array(&mut machine, vec![Value::int32(7)]).unwrap();
        let map = construct_builtin(&mut machine, "Map", &[]);
        map_set(
            &mut machine,
            map,
            &[Value::int32(0), Value::int32(7)],
            false,
        )
        .unwrap();
        let set = construct_builtin(&mut machine, "Set", &[]);
        set_add(&mut machine, set, &[Value::int32(7)], false).unwrap();
        let letter = machine
            .allocate(HeapEntry::String(EcmaString::encode("a")))
            .unwrap();
        let string_elements = allocate_array(&mut machine, vec![letter]).unwrap();
        let typed_array = construct_builtin(&mut machine, "Uint8Array", &[Value::int32(1)]);
        let setter = install_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            &mut machine.intrinsics.builtins,
            crate::intrinsics::BuiltinDef {
                name: "inherited iterator result setter",
                length: 1,
                handler: inherited_setter,
            },
        );
        let prototype = machine.intrinsics.object_prototype;
        for name in ["value", "done"] {
            let key = PropertyKey::Named(machine.intern_str(name));
            machine
                .define_accessor(prototype, key, setter, crate::AccessorKind::Setter)
                .unwrap();
        }

        for (source, kind, expected) in [
            (
                array,
                IterationKind::Value(IteratorFamily::Array),
                Value::int32(7),
            ),
            (
                map,
                IterationKind::Value(IteratorFamily::Map),
                Value::int32(7),
            ),
            (
                set,
                IterationKind::Value(IteratorFamily::Set),
                Value::int32(7),
            ),
            (string_elements, IterationKind::StringCodePoint, letter),
            (
                typed_array,
                IterationKind::Value(IteratorFamily::Array),
                Value::int32(0),
            ),
        ] {
            let iterator = iterator(&mut machine, source, kind).unwrap();
            let next = machine.get_named_property(iterator, "next").unwrap();
            for (expected, done) in [(expected, false), (Value::UNDEFINED, true)] {
                let result = machine.call_value(next, iterator, &[]).unwrap();
                assert_eq!(
                    machine.internal_get_prototype_of(result).unwrap(),
                    Some(prototype)
                );
                for (name, expected) in [("value", expected), ("done", Value::boolean(done))] {
                    let key = PropertyKey::Named(machine.intern_str(name));
                    assert!(matches!(
                        machine.own_descriptor(result, &key).unwrap(),
                        Some(Property::Data {
                            value,
                            writable: true,
                            enumerable: true,
                            configurable: true,
                        }) if value == expected
                    ));
                }
            }
        }
    }

    #[test]
    fn map_and_set_to_string_tags() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object_to_string = machine.intrinsics.object_to_string();

        let map = construct_builtin(&mut machine, "Map", &[]);
        let map_tag = machine
            .call_value(object_to_string, map, &[])
            .expect("Object.prototype.toString.call(new Map()) succeeds");
        assert!(
            machine
                .string_value(map_tag)
                .is_some_and(|text| text.eq_ascii("[object Map]")),
            "Map instances expose the Map toStringTag"
        );

        let set = construct_builtin(&mut machine, "Set", &[]);
        let set_tag = machine
            .call_value(object_to_string, set, &[])
            .expect("Object.prototype.toString.call(new Set()) succeeds");
        assert!(
            machine
                .string_value(set_tag)
                .is_some_and(|text| text.eq_ascii("[object Set]")),
            "Set instances expose the Set toStringTag"
        );

        let tag_symbol = machine.intrinsics.builtins.symbol_to_string_tag();
        let tag_key =
            PropertyKey::Symbol(machine.runtime_slot(tag_symbol).unwrap().unwrap() as u32);
        for name in ["Map", "Set"] {
            let constructor = machine.intrinsics.global(name).unwrap();
            let prototype = machine
                .get_named_property(constructor, "prototype")
                .unwrap();
            let prototype_index = machine.runtime_slot(prototype).unwrap().unwrap();
            let HeapEntry::Object { properties, .. } = &machine.heap[prototype_index] else {
                panic!("{name}.prototype must be an object");
            };
            let Some(Property::Data {
                writable,
                enumerable,
                configurable,
                ..
            }) = properties.get(&machine.shapes, &tag_key)
            else {
                panic!("{name}.prototype must own Symbol.toStringTag");
            };
            assert_eq!(
                (*writable, *enumerable, *configurable),
                (false, false, true)
            );
        }
    }
    #[test]
    fn collection_mutations_refund_exact_entry_and_index_charges() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let entry_charge = CollectionEntry::BYTES + CollectionIndex::ENTRY_BYTES;
        let assert_ledger = |machine: &Machine<'_, TestHost>| {
            assert_eq!(
                machine.heap_bytes,
                machine.machine_bytes + machine.slot_bytes.iter().sum::<usize>()
            );
        };

        let map = construct_builtin(&mut machine, "Map", &[]);
        let map_slot = slot(&machine, map);
        let map_before = machine.slot_bytes[map_slot];
        map_put(
            &mut machine,
            map,
            Value::int32(1),
            Value::int32(2),
            CollectionKind::Map,
        )
        .unwrap();
        assert_eq!(machine.slot_bytes[map_slot], map_before + entry_charge);
        assert_ledger(&machine);
        assert!(matches!(
            map_delete_for(&mut machine, map, &[Value::int32(9)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::FALSE))
        ));
        assert_eq!(machine.slot_bytes[map_slot], map_before + entry_charge);
        assert_ledger(&machine);
        assert!(matches!(
            map_delete_for(&mut machine, map, &[Value::int32(1)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::TRUE))
        ));
        assert_eq!(machine.slot_bytes[map_slot], map_before);
        assert_ledger(&machine);

        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let weak_map_slot = slot(&machine, weak_map);
        let weak_map_before = machine.slot_bytes[weak_map_slot];
        let weak_map_key = ordinary_object(&mut machine);
        map_put(
            &mut machine,
            weak_map,
            weak_map_key,
            Value::int32(2),
            CollectionKind::WeakMap,
        )
        .unwrap();
        assert_eq!(
            machine.slot_bytes[weak_map_slot],
            weak_map_before + entry_charge
        );
        assert_ledger(&machine);
        map_delete_for(
            &mut machine,
            weak_map,
            &[weak_map_key],
            CollectionKind::WeakMap,
        )
        .unwrap();
        assert_eq!(machine.slot_bytes[weak_map_slot], weak_map_before);
        assert_ledger(&machine);

        let set = construct_builtin(&mut machine, "Set", &[]);
        let set_slot = slot(&machine, set);
        let set_before = machine.slot_bytes[set_slot];
        set_put(&mut machine, set, Value::int32(3), CollectionKind::Set).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before + entry_charge);
        assert_ledger(&machine);
        map_delete_for(&mut machine, set, &[Value::int32(3)], CollectionKind::Set).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before);
        assert_ledger(&machine);

        let weak_set = construct_builtin(&mut machine, "WeakSet", &[]);
        let weak_set_slot = slot(&machine, weak_set);
        let weak_set_before = machine.slot_bytes[weak_set_slot];
        let weak_set_key = ordinary_object(&mut machine);
        set_put(
            &mut machine,
            weak_set,
            weak_set_key,
            CollectionKind::WeakSet,
        )
        .unwrap();
        assert_eq!(
            machine.slot_bytes[weak_set_slot],
            weak_set_before + entry_charge
        );
        assert_ledger(&machine);
        map_delete_for(
            &mut machine,
            weak_set,
            &[weak_set_key],
            CollectionKind::WeakSet,
        )
        .unwrap();
        assert_eq!(machine.slot_bytes[weak_set_slot], weak_set_before);
        assert_ledger(&machine);

        map_put(
            &mut machine,
            map,
            Value::int32(4),
            Value::int32(5),
            CollectionKind::Map,
        )
        .unwrap();
        assert_eq!(machine.slot_bytes[map_slot], map_before + entry_charge);
        assert_ledger(&machine);
        map_put(
            &mut machine,
            map,
            Value::int32(6),
            Value::int32(7),
            CollectionKind::Map,
        )
        .unwrap();
        assert_eq!(machine.slot_bytes[map_slot], map_before + 2 * entry_charge);
        assert_ledger(&machine);
        map_clear(&mut machine, map, &[], false).unwrap();
        assert_eq!(machine.slot_bytes[map_slot], map_before);
        assert_ledger(&machine);
        map_clear(&mut machine, map, &[], false).unwrap();
        assert_eq!(machine.slot_bytes[map_slot], map_before);
        assert_ledger(&machine);

        set_put(&mut machine, set, Value::int32(8), CollectionKind::Set).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before + entry_charge);
        assert_ledger(&machine);
        set_put(&mut machine, set, Value::int32(9), CollectionKind::Set).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before + 2 * entry_charge);
        assert_ledger(&machine);
        set_clear(&mut machine, set, &[], false).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before);
        assert_ledger(&machine);
        set_clear(&mut machine, set, &[], false).unwrap();
        assert_eq!(machine.slot_bytes[set_slot], set_before);
        assert_ledger(&machine);
    }

    fn root(machine: &mut Machine<'_, TestHost>, name: &str, value: Value) {
        machine.test_set_global(name, value);
    }

    fn slot(machine: &Machine<'_, TestHost>, value: Value) -> usize {
        machine
            .runtime_slot(value)
            .unwrap()
            .expect("live runtime slot")
    }

    #[test]
    fn collector_vacates_dead_slots_without_moving_survivors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let dead = ordinary_object(&mut machine);
        let survivor = ordinary_object(&mut machine);
        let survivor_slot = slot(&machine, survivor);
        let dead_slot = slot(&machine, dead);
        root(&mut machine, "survivor", survivor);

        machine.collect_garbage();

        assert!(matches!(machine.heap[dead_slot], HeapEntry::Vacant));
        assert_eq!(slot(&machine, survivor), survivor_slot);
        assert_eq!(machine.test_global("survivor"), Some(survivor));
        assert!(matches!(
            machine.runtime_slot(dead),
            Err(RuntimeErrorKind::InvalidRuntimeHeapReference { .. })
        ));
    }

    #[test]
    fn collector_traces_map_and_set_entries_strongly() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        let set = construct_builtin(&mut machine, "Set", &[]);
        let map_key = ordinary_object(&mut machine);
        let map_value = ordinary_object(&mut machine);
        let set_value = ordinary_object(&mut machine);
        map_put(&mut machine, map, map_key, map_value, CollectionKind::Map).unwrap();
        set_put(&mut machine, set, set_value, CollectionKind::Set).unwrap();
        root(&mut machine, "map", map);
        root(&mut machine, "set", set);

        machine.collect_garbage();

        assert!(machine.runtime_slot(map_key).unwrap().is_some());
        assert!(machine.runtime_slot(map_value).unwrap().is_some());
        assert!(machine.runtime_slot(set_value).unwrap().is_some());
        assert_eq!(
            collection_entries(&machine, map),
            vec![(map_key, map_value)]
        );
        assert_eq!(
            collection_entries(&machine, set),
            vec![(set_value, set_value)]
        );
    }

    #[test]
    fn collector_purges_dead_weak_keys_and_refunds_entry_and_index_charges() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let entry_charge = CollectionEntry::BYTES + CollectionIndex::ENTRY_BYTES;
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let weak_set = construct_builtin(&mut machine, "WeakSet", &[]);
        let weak_map_slot = slot(&machine, weak_map);
        let weak_set_slot = slot(&machine, weak_set);
        let weak_map_before = machine.slot_bytes[weak_map_slot];
        let weak_set_before = machine.slot_bytes[weak_set_slot];
        let map_key = ordinary_object(&mut machine);
        let map_value = ordinary_object(&mut machine);
        let set_key = ordinary_object(&mut machine);
        map_put(
            &mut machine,
            weak_map,
            map_key,
            map_value,
            CollectionKind::WeakMap,
        )
        .unwrap();
        set_put(&mut machine, weak_set, set_key, CollectionKind::WeakSet).unwrap();
        assert_eq!(
            machine.slot_bytes[weak_map_slot],
            weak_map_before + entry_charge
        );
        assert_eq!(
            machine.slot_bytes[weak_set_slot],
            weak_set_before + entry_charge
        );
        assert_eq!(
            machine.heap_bytes,
            machine.machine_bytes + machine.slot_bytes.iter().sum::<usize>()
        );
        root(&mut machine, "weakMap", weak_map);
        root(&mut machine, "weakSet", weak_set);
        let dead_slot_bytes = [map_key, map_value, set_key]
            .into_iter()
            .map(|value| machine.slot_bytes[slot(&machine, value)])
            .sum::<usize>();
        let before = machine.heap_bytes;

        machine.collect_garbage();

        assert!(collection_entries(&machine, weak_map).is_empty());
        assert!(collection_entries(&machine, weak_set).is_empty());
        assert_eq!(machine.slot_bytes[weak_map_slot], weak_map_before);
        assert_eq!(machine.slot_bytes[weak_set_slot], weak_set_before);
        assert_eq!(
            machine.heap_bytes,
            before - dead_slot_bytes - 2 * entry_charge
        );
        assert_eq!(
            machine.heap_bytes,
            machine.machine_bytes + machine.slot_bytes.iter().sum::<usize>()
        );
    }

    #[test]
    fn collector_keeps_weak_map_value_when_key_is_live() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let key = ordinary_object(&mut machine);
        let value = ordinary_object(&mut machine);
        map_put(&mut machine, weak_map, key, value, CollectionKind::WeakMap).unwrap();
        root(&mut machine, "weakMap", weak_map);
        root(&mut machine, "key", key);

        machine.collect_garbage();

        assert!(machine.runtime_slot(value).unwrap().is_some());
        assert_eq!(collection_entries(&machine, weak_map), vec![(key, value)]);
    }

    #[test]
    fn collector_reaches_cross_weak_map_ephemeron_fixed_point() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let first = construct_builtin(&mut machine, "WeakMap", &[]);
        let second = construct_builtin(&mut machine, "WeakMap", &[]);
        let first_key = ordinary_object(&mut machine);
        let second_key = ordinary_object(&mut machine);
        let value = ordinary_object(&mut machine);
        map_put(
            &mut machine,
            first,
            first_key,
            second_key,
            CollectionKind::WeakMap,
        )
        .unwrap();
        map_put(
            &mut machine,
            second,
            second_key,
            value,
            CollectionKind::WeakMap,
        )
        .unwrap();
        root(&mut machine, "first", first);
        root(&mut machine, "second", second);
        root(&mut machine, "firstKey", first_key);

        machine.collect_garbage();

        assert!(machine.runtime_slot(second_key).unwrap().is_some());
        assert!(machine.runtime_slot(value).unwrap().is_some());
        assert_eq!(
            collection_entries(&machine, second),
            vec![(second_key, value)]
        );
    }

    #[test]
    fn collector_drops_weak_only_key_value_cycle() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let key = ordinary_object(&mut machine);
        let value = ordinary_object(&mut machine);
        machine.set_data_property(value, "key", key).unwrap();
        map_put(&mut machine, weak_map, key, value, CollectionKind::WeakMap).unwrap();
        root(&mut machine, "weakMap", weak_map);

        machine.collect_garbage();

        assert!(collection_entries(&machine, weak_map).is_empty());
        assert!(machine.runtime_slot(key).is_err());
        assert!(machine.runtime_slot(value).is_err());
    }

    #[test]
    fn collector_allows_local_symbol_weak_keys_to_die() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);
        let symbol = local_symbol(&mut machine);
        let value = ordinary_object(&mut machine);
        map_put(
            &mut machine,
            weak_map,
            symbol,
            value,
            CollectionKind::WeakMap,
        )
        .unwrap();
        root(&mut machine, "weakMap", weak_map);

        machine.collect_garbage();

        assert!(collection_entries(&machine, weak_map).is_empty());
        assert!(machine.runtime_slot(symbol).is_err());
        assert!(machine.runtime_slot(value).is_err());
    }

    #[test]
    fn collector_preserves_registered_symbol_roots() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol = symbol_for(&mut machine, Value::int32(17));
        let symbol_slot = slot(&machine, symbol);

        machine.collect_garbage();

        assert_eq!(slot(&machine, symbol), symbol_slot);
    }

    fn raw_entries_len(machine: &Machine<'_, TestHost>, obj: Value) -> usize {
        let slot = machine
            .runtime_slot(obj)
            .unwrap()
            .expect("runtime collection");
        let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
            panic!("not a collection")
        };
        entries.len()
    }

    #[test]
    fn delete_tombstones_entry_without_shrinking_vector() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        map_put(
            &mut machine,
            map,
            Value::int32(1),
            Value::int32(10),
            CollectionKind::Map,
        )
        .unwrap();
        map_put(
            &mut machine,
            map,
            Value::int32(2),
            Value::int32(20),
            CollectionKind::Map,
        )
        .unwrap();
        assert_eq!(raw_entries_len(&machine, map), 2);

        // Delete key 1 — the entry must be tombstoned, not removed.
        assert!(matches!(
            map_delete_for(&mut machine, map, &[Value::int32(1)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::TRUE))
        ));
        assert_eq!(
            raw_entries_len(&machine, map),
            2,
            "tombstone must not shrink"
        );
        assert_eq!(
            collection_entries(&machine, map),
            vec![(Value::int32(2), Value::int32(20))],
            "tombstoned entry must be invisible to collection_entries"
        );

        // has/get must not find the deleted key.
        assert!(matches!(
            map_has_for(&mut machine, map, &[Value::int32(1)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::FALSE))
        ));
        assert!(matches!(
            map_get_for(&mut machine, map, &[Value::int32(1)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::UNDEFINED))
        ));
        // Re-inserting key 1 pushes a new entry (the tombstone stays until
        // compaction); insertion order is now key 2, then the re-added key 1.
        map_put(
            &mut machine,
            map,
            Value::int32(1),
            Value::int32(99),
            CollectionKind::Map,
        )
        .unwrap();
        assert_eq!(
            raw_entries_len(&machine, map),
            3,
            "push-only re-insert appends; the tombstone remains until compaction"
        );
        assert_eq!(
            collection_entries(&machine, map),
            vec![
                (Value::int32(2), Value::int32(20)),
                (Value::int32(1), Value::int32(99))
            ],
        );
    }

    #[test]
    fn delete_during_iteration_skips_tombstoned_entries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        for n in 1..=3 {
            map_put(
                &mut machine,
                map,
                Value::int32(n),
                Value::int32(n * 10),
                CollectionKind::Map,
            )
            .unwrap();
        }
        // Delete key 2 before iterating; the iterator must skip the tombstone.
        assert!(matches!(
            map_delete_for(&mut machine, map, &[Value::int32(2)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::TRUE))
        ));
        let mut visited = Vec::new();
        let mut cursor = 0;
        while let Some((next, key, value)) =
            collection_next(&machine, map, CollectionKind::Map, cursor).unwrap()
        {
            cursor = next;
            visited.push((key, value));
        }
        assert_eq!(
            visited,
            vec![
                (Value::int32(1), Value::int32(10)),
                (Value::int32(3), Value::int32(30)),
            ],
            "iteration must skip tombstoned entries"
        );
    }

    #[test]
    fn iteration_visits_all_live_entries_after_delete_then_reinsert() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        // The sortedness regression: set, set, delete, re-set left a large
        // order in an early vector slot, breaking the binary-search cursor
        // the real iterator protocol uses.
        map_put(
            &mut machine,
            map,
            Value::int32(1),
            Value::int32(10),
            CollectionKind::Map,
        )
        .unwrap();
        map_put(
            &mut machine,
            map,
            Value::int32(2),
            Value::int32(20),
            CollectionKind::Map,
        )
        .unwrap();
        assert!(matches!(
            map_delete_for(&mut machine, map, &[Value::int32(1)], CollectionKind::Map),
            Ok(BuiltinOutcome::Value(Value::TRUE))
        ));
        map_put(
            &mut machine,
            map,
            Value::int32(1),
            Value::int32(99),
            CollectionKind::Map,
        )
        .unwrap();

        // Iterate via the REAL iterator protocol (collection_next), the path
        // forEach/for..of use — NOT collection_entries, which scans by vector
        // position and would miss the sortedness break.
        let mut visited = Vec::new();
        let mut cursor = 0;
        while let Some((next, key, value)) =
            collection_next(&machine, map, CollectionKind::Map, cursor).unwrap()
        {
            cursor = next;
            visited.push((key, value));
        }
        assert_eq!(
            visited,
            vec![
                (Value::int32(2), Value::int32(20)),
                (Value::int32(1), Value::int32(99)),
            ],
            "every live entry must be visited exactly once in insertion order"
        );
    }

    #[test]
    fn repeated_insert_delete_does_not_grow_entries_unboundedly() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let map = construct_builtin(&mut machine, "Map", &[]);
        const N: usize = 50;
        const ROUNDS: usize = 20;
        for _ in 0..ROUNDS {
            for k in 1..=N {
                map_put(
                    &mut machine,
                    map,
                    Value::int32(k as u32),
                    Value::int32((k as u32) * 10),
                    CollectionKind::Map,
                )
                .unwrap();
            }
            for k in 1..=N {
                assert!(matches!(
                    map_delete_for(
                        &mut machine,
                        map,
                        &[Value::int32(k as u32)],
                        CollectionKind::Map
                    ),
                    Ok(BuiltinOutcome::Value(Value::TRUE))
                ));
            }
        }
        // Without compaction, 20 rounds of insert-all/delete-all would
        // accumulate 1000 tombstoned slots. Compaction must keep the vector
        // bounded near the live-set size.
        let len = raw_entries_len(&machine, map);
        assert!(
            len <= 2 * N,
            "entries grew to {len} after {ROUNDS} rounds; compaction should bound it near {N}"
        );
    }

    #[test]
    fn weak_key_rejects_internal_bookkeeping_entries() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let weak_map = construct_builtin(&mut machine, "WeakMap", &[]);

        // An ordinary object is a valid weak key (object-like).
        let obj = ordinary_object(&mut machine);
        assert!(
            call_prototype_method(
                &mut machine,
                "WeakMap",
                "set",
                weak_map,
                &[obj, Value::int32(1)],
            )
            .is_ok(),
            "ordinary object must be a valid weak key"
        );

        // A registered symbol must be rejected (the catch-all previously
        // handled this, but the linear scan was the performance problem).
        let registered = symbol_for(&mut machine, Value::int32(42));
        assert_type_error(call_prototype_method(
            &mut machine,
            "WeakMap",
            "set",
            weak_map,
            &[registered, Value::int32(2)],
        ));

        // A local symbol must be accepted.
        let local = local_symbol(&mut machine);
        assert!(
            call_prototype_method(
                &mut machine,
                "WeakMap",
                "set",
                weak_map,
                &[local, Value::int32(3)],
            )
            .is_ok(),
            "local Symbol must be a valid weak key"
        );
    }

    #[test]
    fn collection_instances_use_their_constructor_prototype() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        for (name, kind) in [
            ("Map", CollectionKind::Map),
            ("Set", CollectionKind::Set),
            ("WeakMap", CollectionKind::WeakMap),
            ("WeakSet", CollectionKind::WeakSet),
        ] {
            let ctor = machine.intrinsics.global(name).expect("global exists");
            let id = machine
                .intrinsics
                .builtins
                .id_named(name)
                .expect("builtin id");
            let expected = machine
                .get_named_property(ctor, "prototype")
                .expect("constructor has prototype");
            let BuiltinOutcome::Value(instance) = machine
                .call_builtin(id, Value::UNDEFINED, &[], true)
                .expect("collection construct succeeds")
            else {
                panic!("{name} construct returns a value");
            };

            let slot = machine
                .runtime_slot(instance)
                .expect("valid instance")
                .expect("slot");
            let HeapEntry::Collection {
                prototype,
                kind: actual_kind,
                ..
            } = &machine.heap[slot]
            else {
                panic!("{name} instance");
            };
            assert_eq!(*prototype, Some(expected));
            assert_eq!(*actual_kind, kind);

            // The prototype's "constructor" is still the original constructor.
            let back = machine
                .get_named_property(expected, "constructor")
                .expect("prototype has constructor");
            assert_eq!(back, ctor);
        }
    }

    use crate::intrinsics::{BuiltinDef, BuiltinHandler, native_function};
    fn native_callback(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            0,
        )
    }

    fn push_log(machine: &mut Machine<'_, TestHost>, event: u32) {
        let log = machine.test_global("log").unwrap();
        machine.array_push(log, Value::int32(event)).unwrap();
    }

    fn get_iter_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let iter = machine.test_global("testIterator").unwrap();
        Ok(BuiltinOutcome::Value(iter))
    }

    fn make_custom_iterator_source(
        machine: &mut Machine<'_, TestHost>,
        next_fn: Value,
        return_fn: Value,
    ) -> Value {
        let iter = ordinary_object(machine);
        machine.set_data_property(iter, "next", next_fn).unwrap();
        machine
            .set_data_property(iter, "return", return_fn)
            .unwrap();
        machine.test_set_global("testIterator", iter);

        let get_iter = native_callback(machine, "custom Symbol.iterator", get_iter_callback);
        let iterable = ordinary_object(machine);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine
            .property_key_from_value(iterator_symbol)
            .expect("Symbol.iterator is a property key");
        machine
            .set_data_property_key(iterable, iterator_key, get_iter)
            .expect("iterator install succeeds");
        iterable
    }

    fn define_getter(
        machine: &mut Machine<'_, TestHost>,
        target: Value,
        key_str: &str,
        getter_fn: Value,
    ) {
        let descriptor = ordinary_object(machine);
        machine
            .set_data_property(descriptor, "get", getter_fn)
            .unwrap();
        machine
            .set_data_property(descriptor, "configurable", Value::TRUE)
            .unwrap();
        machine
            .set_data_property(descriptor, "enumerable", Value::TRUE)
            .unwrap();
        let object_ctor = machine.intrinsics.global("Object").unwrap();
        let define_prop = machine
            .get_named_property(object_ctor, "defineProperty")
            .unwrap();
        let key_val = machine
            .allocate(HeapEntry::String(EcmaString::encode(key_str)))
            .unwrap();
        machine
            .call_value(define_prop, object_ctor, &[target, key_val, descriptor])
            .unwrap();
    }

    // ---- iteration order and abrupt close tests ---------------------------

    fn order_next_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.collect_garbage();
        let count = match machine.test_global("nextCount") {
            Some(v) => match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            },
            None => 0,
        };
        if count == 0 {
            machine.test_set_global("nextCount", Value::int32(1));
            push_log(machine, 10); // NEXT_0
            let entry = machine.test_global("testEntry").unwrap();
            let res = ordinary_object(machine);
            machine.set_data_property(res, "done", Value::FALSE)?;
            machine.set_data_property(res, "value", entry)?;
            Ok(BuiltinOutcome::Value(res))
        } else {
            machine.test_set_global("nextCount", Value::int32(2));
            push_log(machine, 40); // PUT (recorded before NEXT_1)
            push_log(machine, 50); // NEXT_1
            let res = ordinary_object(machine);
            machine.set_data_property(res, "done", Value::TRUE)?;
            machine.set_data_property(res, "value", Value::UNDEFINED)?;
            Ok(BuiltinOutcome::Value(res))
        }
    }

    fn order_get_0_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        push_log(machine, 20); // GET_0
        Ok(BuiltinOutcome::Value(Value::int32(1)))
    }

    fn order_get_1_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        push_log(machine, 30); // GET_1
        Ok(BuiltinOutcome::Value(Value::int32(100)))
    }

    fn order_return_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        push_log(machine, 60); // RETURN
        let res = ordinary_object(machine);
        machine.set_data_property(res, "done", Value::TRUE)?;
        Ok(BuiltinOutcome::Value(res))
    }

    #[test]
    fn map_constructor_iterator_and_entry_evaluation_order() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);
        machine.test_set_global("nextCount", Value::int32(0));

        let entry = ordinary_object(&mut machine);
        let get0 = native_callback(&mut machine, "get 0", order_get_0_callback);
        let get1 = native_callback(&mut machine, "get 1", order_get_1_callback);
        define_getter(&mut machine, entry, "0", get0);
        define_getter(&mut machine, entry, "1", get1);
        machine.test_set_global("testEntry", entry);

        let next = native_callback(&mut machine, "next", order_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let map = construct_builtin(&mut machine, "Map", &[source]);
        let entries = collection_entries(&machine, map);
        assert_eq!(entries, vec![(Value::int32(1), Value::int32(100))]);

        let events = machine.array_elements(log).unwrap().unwrap();
        let event_nums: Vec<u32> = events
            .iter()
            .map(|v| match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            })
            .collect();

        // Pin order: next0 (10), get0 (20), get1 (30), put (40), next1 (50)
        assert_eq!(
            event_nums,
            vec![10, 20, 30, 40, 50],
            "Map constructor must process entries lazily in order: next0, get0, get1, put, next1"
        );
    }

    #[test]
    fn set_constructor_roots_result_across_iterator_callbacks() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);
        machine.test_set_global("nextCount", Value::int32(0));
        let entry = ordinary_object(&mut machine);
        machine.test_set_global("testEntry", entry);

        let next = native_callback(&mut machine, "next", order_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let set = construct_builtin(&mut machine, "Set", &[source]);
        assert_eq!(collection_entries(&machine, set), vec![(entry, entry)]);
    }

    fn failing_entry_next_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = match machine.test_global("nextCount") {
            Some(v) => match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            },
            None => 0,
        };
        machine.test_set_global("nextCount", Value::int32(count + 1));
        push_log(machine, 10); // NEXT_0
        let entry = machine.test_global("testEntry").unwrap();
        let res = ordinary_object(machine);
        machine.set_data_property(res, "done", Value::FALSE)?;
        machine.set_data_property(res, "value", entry)?;
        Ok(BuiltinOutcome::Value(res))
    }

    fn failing_get_1_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        push_log(machine, 70); // GET_1_THROW
        Err(type_error("entry value getter failed"))
    }

    #[test]
    fn map_constructor_closes_iterator_on_entry_property_failure() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);
        machine.test_set_global("nextCount", Value::int32(0));

        let entry = ordinary_object(&mut machine);
        let get0 = native_callback(&mut machine, "get 0", order_get_0_callback);
        let get1 = native_callback(&mut machine, "failing get 1", failing_get_1_callback);
        define_getter(&mut machine, entry, "0", get0);
        define_getter(&mut machine, entry, "1", get1);
        machine.test_set_global("testEntry", entry);

        let next = native_callback(&mut machine, "next", failing_entry_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let id = builtin_id(&machine, "Map");
        let result = machine.call_builtin(id, Value::UNDEFINED, &[source], true);
        assert!(
            result.is_err(),
            "Map constructor must fail when entry get throws"
        );

        let events = machine.array_elements(log).unwrap().unwrap();
        let event_nums: Vec<u32> = events
            .iter()
            .map(|v| match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            })
            .collect();

        // Pin abrupt close: next0 (10), get0 (20), get1_throw (70), return (60)
        assert_eq!(
            event_nums,
            vec![10, 20, 70, 60],
            "Entry property failure must trigger iterator return hook"
        );

        let next_count = match machine.test_global("nextCount").unwrap().decode() {
            Some(Decoded::Int32(n)) => n,
            _ => 0,
        };
        assert_eq!(
            next_count, 1,
            "No second next call must occur after entry failure"
        );
    }

    fn throwing_next_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        push_log(machine, 80); // NEXT_THROW
        Err(type_error("iterator next failed"))
    }

    #[test]
    fn map_constructor_does_not_close_iterator_on_next_failure() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);

        let next = native_callback(&mut machine, "throwing next", throwing_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let id = builtin_id(&machine, "Map");
        let result = machine.call_builtin(id, Value::UNDEFINED, &[source], true);
        assert!(
            result.is_err(),
            "Map constructor must fail when iterator next throws"
        );

        let events = machine.array_elements(log).unwrap().unwrap();
        let event_nums: Vec<u32> = events
            .iter()
            .map(|v| match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            })
            .collect();

        assert_eq!(
            event_nums,
            vec![80],
            "Throwing next() must not call iterator return hook"
        );
    }

    fn weak_set_invalid_next_callback(
        machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let count = match machine.test_global("nextCount") {
            Some(value) => match value.decode() {
                Some(Decoded::Int32(count)) => count,
                _ => 0,
            },
            None => 0,
        };
        machine.test_set_global("nextCount", Value::int32(count + 1));
        push_log(machine, if count == 0 { 10 } else { 40 });

        let result = ordinary_object(machine);
        machine
            .set_data_property(result, "done", Value::FALSE)
            .unwrap();
        machine
            .set_data_property(result, "value", Value::int32(42))
            .unwrap();
        Ok(BuiltinOutcome::Value(result))
    }

    #[test]
    fn weak_set_constructor_closes_before_requesting_next_invalid_value() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);
        machine.test_set_global("nextCount", Value::int32(0));

        let next = native_callback(&mut machine, "next", weak_set_invalid_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let id = builtin_id(&machine, "WeakSet");
        let result = machine.call_builtin(id, Value::UNDEFINED, &[source], true);
        assert_type_error(result);

        let events = machine.array_elements(log).unwrap().unwrap();
        let event_nums: Vec<u32> = events
            .iter()
            .map(|value| match value.decode() {
                Some(Decoded::Int32(number)) => number,
                _ => 0,
            })
            .collect();
        assert_eq!(event_nums, vec![10, 60]);

        let next_count = match machine.test_global("nextCount") {
            Some(value) => match value.decode() {
                Some(Decoded::Int32(count)) => count,
                _ => 0,
            },
            None => 0,
        };
        assert_eq!(next_count, 1);
    }

    #[test]
    fn weak_map_constructor_closes_iterator_on_invalid_key() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let log = allocate_array(&mut machine, Vec::new()).unwrap();
        machine.test_set_global("log", log);
        machine.test_set_global("nextCount", Value::int32(0));

        // Entry with primitive key for WeakMap
        let entry = entry_pair(&mut machine, Value::int32(42), Value::int32(100));
        machine.test_set_global("testEntry", entry);

        let next = native_callback(&mut machine, "next", failing_entry_next_callback);
        let ret = native_callback(&mut machine, "return", order_return_callback);
        let source = make_custom_iterator_source(&mut machine, next, ret);

        let id = builtin_id(&machine, "WeakMap");
        let result = machine.call_builtin(id, Value::UNDEFINED, &[source], true);
        assert!(
            result.is_err(),
            "WeakMap constructor must fail on primitive key"
        );

        let events = machine.array_elements(log).unwrap().unwrap();
        let event_nums: Vec<u32> = events
            .iter()
            .map(|v| match v.decode() {
                Some(Decoded::Int32(n)) => n,
                _ => 0,
            })
            .collect();

        // Pin abrupt close: next0 (10), return (60)
        assert_eq!(
            event_nums,
            vec![10, 60],
            "WeakMap invalid key failure must trigger iterator return hook"
        );

        let next_count = match machine.test_global("nextCount").unwrap().decode() {
            Some(Decoded::Int32(n)) => n,
            _ => 0,
        };
        assert_eq!(
            next_count, 1,
            "No second next call must occur after WeakMap key failure"
        );
    }
}

#[cfg(test)]
mod collection_edge_tests {
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
        crate::intrinsics::native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            name,
            1,
        )
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
