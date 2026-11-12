use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{
    allocate_string, builtin_property, define_data, define_to_string_tag, heap_index,
    install_constructor_function, install_function, type_error,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let prototype = super::super::ordinary_prototype(heap, builtins.object_prototype());
    let iterator = symbol(heap, "Symbol.iterator");
    let async_iterator = symbol(heap, "Symbol.asyncIterator");
    let has_instance = symbol(heap, "Symbol.hasInstance");
    let to_string_tag = symbol(heap, "Symbol.toStringTag");
    let species = symbol(heap, "Symbol.species");
    let dispose = symbol(heap, "Symbol.dispose");
    let async_dispose = symbol(heap, "Symbol.asyncDispose");
    let match_symbol = symbol(heap, "Symbol.match");
    let replace_symbol = symbol(heap, "Symbol.replace");
    let match_all_symbol = symbol(heap, "Symbol.matchAll");
    let search_symbol = symbol(heap, "Symbol.search");
    let split_symbol = symbol(heap, "Symbol.split");
    let is_concat_spreadable = symbol(heap, "Symbol.isConcatSpreadable");
    let to_primitive = symbol(heap, "Symbol.toPrimitive");
    let unscopables = symbol(heap, "Symbol.unscopables");
    builtins.set_symbol_iterator(iterator);
    builtins.set_symbol_async_iterator(async_iterator);
    builtins.set_symbol_match(match_symbol);
    builtins.set_symbol_replace(replace_symbol);
    builtins.set_symbol_match_all(match_all_symbol);
    builtins.set_symbol_search(search_symbol);
    builtins.set_symbol_split(split_symbol);
    builtins.set_symbol_is_concat_spreadable(is_concat_spreadable);
    builtins.set_symbol_has_instance(has_instance);
    builtins.set_symbol_to_primitive(to_primitive);
    builtins.set_symbol_to_string_tag(to_string_tag);
    builtins.set_symbol_species(species);
    builtins.set_symbol_dispose(dispose);
    builtins.set_symbol_async_dispose(async_dispose);
    builtins.set_symbol_unscopables(unscopables);
    builtins.set_symbol_prototype(prototype);

    let constructor = install_constructor_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "Symbol",
            length: 0,
            handler: constructor::<H>,
        },
    );
    builtins.set_constructor_prototype(heap, atoms, shapes, constructor, prototype);
    let symbol_for = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "for",
            length: 1,
            handler: symbol_for::<H>,
        },
    );
    define_native_property(heap, atoms, shapes, constructor, "for", symbol_for);
    let key_for = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "keyFor",
            length: 1,
            handler: key_for::<H>,
        },
    );
    define_native_property(heap, atoms, shapes, constructor, "keyFor", key_for);
    for (name, value) in [
        ("iterator", iterator),
        ("asyncIterator", async_iterator),
        ("hasInstance", has_instance),
        ("match", match_symbol),
        ("replace", replace_symbol),
        ("matchAll", match_all_symbol),
        ("search", search_symbol),
        ("split", split_symbol),
        ("isConcatSpreadable", is_concat_spreadable),
        ("toPrimitive", to_primitive),
        ("toStringTag", to_string_tag),
        ("species", species),
        ("dispose", dispose),
        ("asyncDispose", async_dispose),
        ("unscopables", unscopables),
    ] {
        define_readonly_property(heap, atoms, shapes, constructor, name, value);
    }

    let to_string = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "toString",
            length: 0,
            handler: to_string::<H>,
        },
    );
    let value_of_method = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "valueOf",
            length: 0,
            handler: value_of::<H>,
        },
    );
    let description = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "get description",
            length: 0,
            handler: description::<H>,
        },
    );
    define_data(heap, atoms, shapes, prototype, "toString", to_string);
    define_data(heap, atoms, shapes, prototype, "valueOf", value_of_method);
    let to_primitive_method = install_function(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "[Symbol.toPrimitive]",
            length: 1,
            handler: value_of::<H>,
        },
    );
    define_to_string_tag(heap, shapes, prototype, to_string_tag, "Symbol");
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(prototype)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str("description")),
        Property::Accessor {
            getter: Some(description),
            setter: None,
            enumerable: false,
            configurable: true,
        },
    );
    properties.insert(
        shapes,
        PropertyKey::Symbol(heap_index(to_primitive) as u32),
        Property::Data {
            value: to_primitive_method,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );

    globals.insert(EcmaString::encode("Symbol"), constructor);
}

fn symbol(heap: &mut Vec<HeapEntry>, description: &str) -> Value {
    super::super::push(
        heap,
        HeapEntry::Symbol {
            description: EcmaString::encode(description),
        },
    )
}

fn define_native_property(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        builtin_property(value),
    );
}

fn define_readonly_property(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    object: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(object)] else {
        unreachable!()
    };
    properties.insert(
        shapes,
        PropertyKey::Named(atoms.intern_str(name)),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );
}

fn constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("Symbol is not a constructor"));
    }
    let description = args
        .first()
        .copied()
        .filter(|value| *value != Value::UNDEFINED)
        .map(|value| machine.coerce_string_observable(value))
        .transpose()?
        .unwrap_or_default();
    let symbol = machine
        .allocate(HeapEntry::Symbol { description })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(symbol))
}

fn symbol_for<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let key =
        machine.coerce_string_observable(args.first().copied().unwrap_or(Value::UNDEFINED))?;
    if let Some(existing) = machine.intrinsics.symbol_registry.get(&key).copied() {
        return Ok(BuiltinOutcome::Value(existing));
    }
    let symbol_bytes = key
        .len_units()
        .checked_mul(std::mem::size_of::<u16>())
        .ok_or(EvalFailure::Runtime(
            crate::RuntimeErrorKind::HeapByteLimitExceeded {
                limit: machine.limits.max_heap_bytes,
            },
        ))?;
    let registry_bytes =
        PropertyKey::Named(machine.intern(key.clone())).charge_bytes(&machine.atoms);
    let symbol = machine
        .allocate(HeapEntry::Symbol {
            description: key.clone(),
        })
        .map_err(EvalFailure::Runtime)?;
    if let Err(err) = machine.charge_machine(registry_bytes) {
        let Some(index) = machine.runtime_slot(symbol).map_err(EvalFailure::Runtime)? else {
            unreachable!("allocated symbol has a runtime slot");
        };
        machine.refund_slot(index, symbol_bytes);
        machine.heap[index] = HeapEntry::Vacant;
        machine.vacant_count += 1;
        return Err(EvalFailure::Runtime(err));
    }
    machine.intrinsics.symbol_registry.insert(key, symbol);
    Ok(BuiltinOutcome::Value(symbol))
}

/// `Symbol.keyFor`: a symbol's key is its description only when the global
/// registry holds that very symbol under it.
fn key_for<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let symbol = args.first().copied().unwrap_or(Value::UNDEFINED);
    let index = machine.runtime_slot(symbol).map_err(EvalFailure::Runtime)?;
    let Some(HeapEntry::Symbol { description }) = index.map(|index| &machine.heap[index]) else {
        return Err(type_error("Symbol.keyFor requires a symbol"));
    };
    let description = description.clone();
    if machine.intrinsics.symbol_registry.get(&description) == Some(&symbol) {
        return Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            description,
        )?));
    }
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

/// `ThisSymbolValue`: a symbol, or the symbol a Symbol wrapper object holds.
fn this_symbol_value<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<Value, EvalFailure> {
    let symbol = machine.unbox_primitive_or_self(value)?;
    let index = machine.runtime_slot(symbol).map_err(EvalFailure::Runtime)?;
    match index.map(|index| &machine.heap[index]) {
        Some(HeapEntry::Symbol { .. }) => Ok(symbol),
        _ => Err(type_error("Symbol method called on incompatible receiver")),
    }
}

fn symbol_description<H: Host>(
    machine: &Machine<'_, H>,
    value: Value,
) -> Result<EcmaString, EvalFailure> {
    let symbol = this_symbol_value(machine, value)?;
    let index = machine.runtime_slot(symbol).map_err(EvalFailure::Runtime)?;
    match index.map(|index| &machine.heap[index]) {
        Some(HeapEntry::Symbol { description }) => Ok(description.clone()),
        _ => unreachable!("this_symbol_value returned a symbol"),
    }
}

fn description<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let description = symbol_description(machine, this)?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        description,
    )?))
}

fn to_string<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let description = symbol_description(machine, this)?;
    let mut builder =
        bamts_bytecode::EcmaStringBuilder::with_capacity(description.len_units().saturating_add(8));
    builder.push_utf8("Symbol(");
    for &unit in description.as_units() {
        builder.push_unit(unit);
    }
    builder.push_unit(u16::from(b')'));
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        builder.finish(),
    )?))
}

fn value_of<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    _args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    Ok(BuiltinOutcome::Value(this_symbol_value(machine, this)?))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::Limits;
    use crate::PropertyMap;
    use crate::ThrowOrigin;
    use crate::intrinsics::{BuiltinDef, BuiltinOutcome, BuiltinTable, native_function};
    use bamts_bytecode::{FunctionId, ModuleId, UnaryOp};

    fn well_known_symbol_builtin(builtins: &BuiltinTable<TestHost>, name: &str) -> Option<Value> {
        match name {
            "iterator" => Some(builtins.symbol_iterator()),
            "asyncIterator" => Some(builtins.symbol_async_iterator()),
            "hasInstance" => None,
            "match" => Some(builtins.symbol_match()),
            "replace" => Some(builtins.symbol_replace()),
            "toPrimitive" => Some(builtins.symbol_to_primitive()),
            "toStringTag" => Some(builtins.symbol_to_string_tag()),
            "species" => Some(builtins.symbol_species()),
            "dispose" => Some(builtins.symbol_dispose()),
            "asyncDispose" => Some(builtins.symbol_async_dispose()),
            "unscopables" => Some(builtins.symbol_unscopables()),
            _ => None,
        }
    }

    fn echo_hint(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        args: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(args[0]))
    }

    fn return_this(
        _: &mut Machine<'_, TestHost>,
        this: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    fn with_to_primitive(machine: &mut Machine<'_, TestHost>, method: Value) -> Value {
        let object = ordinary_object(machine);
        let key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_to_primitive())
            .unwrap();
        machine.set_data_property_key(object, key, method).unwrap();
        object
    }

    #[test]
    fn to_primitive_method_receives_the_hint_of_each_coercion() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "echo hint",
            length: 1,
            handler: echo_hint,
        });
        let method = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "echo hint",
            1,
        );
        let object = with_to_primitive(&mut machine, method);

        let string = machine.coerce_primitive_observable(object, true).unwrap();
        let number = machine.coerce_primitive_observable(object, false).unwrap();
        let default = machine.coerce_primitive_default(object).unwrap();
        for (value, hint) in [(string, "string"), (number, "number"), (default, "default")] {
            assert!(
                machine
                    .string_value(value)
                    .is_some_and(|text| text.eq_ascii(hint)),
                "expected hint {hint}"
            );
        }
    }

    fn return_seven(
        _: &mut Machine<'_, TestHost>,
        _: Value,
        _: &[Value],
        _: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(Value::int32(7)))
    }

    #[test]
    fn unary_plus_coerces_an_object_through_to_primitive() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "return seven",
            length: 0,
            handler: return_seven,
        });
        let method = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "return seven",
            0,
        );
        let object = with_to_primitive(&mut machine, method);
        assert_eq!(
            machine.eval_unary(UnaryOp::Plus, object).unwrap(),
            Value::int32(7)
        );
    }

    #[test]
    fn to_primitive_rejects_object_results_and_non_callable_methods() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "return this",
            length: 0,
            handler: return_this,
        });
        let method = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            id,
            "return this",
            0,
        );
        for method in [method, Value::int32(1)] {
            let object = with_to_primitive(&mut machine, method);
            assert!(matches!(
                machine.coerce_primitive_observable(object, false),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ));
        }
    }

    #[test]
    fn a_null_to_primitive_method_falls_back_to_the_ordinary_methods() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let object = with_to_primitive(&mut machine, Value::NULL);
        let primitive = machine.coerce_primitive_observable(object, true).unwrap();
        assert!(
            machine
                .string_value(primitive)
                .is_some_and(|text| text.eq_ascii("[object Object]"))
        );
    }

    #[test]
    fn symbols_are_primitives_not_objects() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let machine = Machine::new(&module, &mut host, Limits::default());
        assert!(!machine.is_object(machine.intrinsics.builtins.symbol_iterator()));
    }

    #[test]
    fn well_known_symbols_are_installed_with_expected_descriptors() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol_constructor = machine
            .intrinsics
            .global("Symbol")
            .expect("Symbol is installed");

        for (name, description) in [
            ("iterator", "Symbol.iterator"),
            ("asyncIterator", "Symbol.asyncIterator"),
            ("hasInstance", "Symbol.hasInstance"),
            ("isConcatSpreadable", "Symbol.isConcatSpreadable"),
            ("matchAll", "Symbol.matchAll"),
            ("search", "Symbol.search"),
            ("split", "Symbol.split"),
            ("toPrimitive", "Symbol.toPrimitive"),
            ("toStringTag", "Symbol.toStringTag"),
            ("species", "Symbol.species"),
            ("dispose", "Symbol.dispose"),
            ("asyncDispose", "Symbol.asyncDispose"),
            ("unscopables", "Symbol.unscopables"),
        ] {
            let first = machine
                .get_named_property(symbol_constructor, name)
                .unwrap_or_else(|_| panic!("Symbol.{name} is installed"));
            let second = machine
                .get_named_property(symbol_constructor, name)
                .unwrap_or_else(|_| panic!("Symbol.{name} is readable on second read"));
            assert_eq!(first, second, "Symbol.{name} identity must be stable");

            if let Some(expected) = well_known_symbol_builtin(&machine.intrinsics.builtins, name) {
                assert_eq!(
                    first, expected,
                    "Symbol.{name} must match the builtins table"
                );
            }

            let actual_description = symbol_description(&machine, first)
                .unwrap_or_else(|_| panic!("Symbol.{name} is a symbol"));
            assert!(
                actual_description.eq_ascii(description),
                "Symbol.{name} description must be '{description}'"
            );

            let key = PropertyKey::Named(machine.intern_str(name));
            let descriptor = machine
                .own_descriptor(symbol_constructor, &key)
                .expect("descriptor lookup succeeds")
                .unwrap_or_else(|| panic!("Symbol.{name} is defined"));
            match descriptor {
                Property::Data {
                    value,
                    writable,
                    enumerable,
                    configurable,
                } => {
                    assert_eq!(
                        value, first,
                        "Symbol.{name} descriptor value must be the symbol"
                    );
                    assert!(!writable, "Symbol.{name} must be non-writable");
                    assert!(!enumerable, "Symbol.{name} must be non-enumerable");
                    assert!(!configurable, "Symbol.{name} must be non-configurable");
                }
                Property::Accessor { .. } => panic!("Symbol.{name} must be a data property"),
            }
        }
    }

    #[test]
    fn symbol_has_construct_but_new_throws_from_the_function_body() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol = machine.intrinsics.global("Symbol").unwrap();
        assert!(
            machine.is_constructor(symbol).unwrap(),
            "an extends clause needs Symbol to have [[Construct]]"
        );
        assert!(matches!(
            machine.construct_value(symbol, &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Symbol is not a constructor"
            }))
        ));
        let result = machine.call_value(symbol, Value::UNDEFINED, &[]).unwrap();
        assert!(
            !machine.is_object(result),
            "a plain call still returns a primitive symbol"
        );
    }

    #[test]
    fn key_for_answers_only_for_the_registered_symbol() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol_constructor = machine.intrinsics.global("Symbol").unwrap();
        let symbol_for = machine
            .get_named_property(symbol_constructor, "for")
            .unwrap();
        let key_for = machine
            .get_named_property(symbol_constructor, "keyFor")
            .unwrap();
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("shared")))
            .unwrap();
        let registered = machine
            .call_value(symbol_for, symbol_constructor, &[key])
            .unwrap();
        let unregistered = machine
            .call_value(symbol_constructor, Value::UNDEFINED, &[key])
            .unwrap();

        let found = machine
            .call_value(key_for, symbol_constructor, &[registered])
            .unwrap();
        assert!(
            machine
                .string_value(found)
                .is_some_and(|text| text.eq_ascii("shared"))
        );
        assert_eq!(
            machine
                .call_value(key_for, symbol_constructor, &[unregistered])
                .unwrap(),
            Value::UNDEFINED,
            "a same-named symbol outside the registry has no key"
        );
        assert!(matches!(
            machine.call_value(key_for, symbol_constructor, &[key]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn symbol_prototype_methods_accept_wrapper_objects() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol = machine.intrinsics.builtins.symbol_iterator();
        let wrapper = machine.value_to_object(symbol).unwrap();

        let key = machine
            .property_key_from_value(machine.intrinsics.builtins.symbol_to_primitive())
            .unwrap();
        let to_primitive = machine.get_property_key(wrapper, &key).unwrap();
        assert_eq!(
            machine.call_value(to_primitive, wrapper, &[]).unwrap(),
            symbol
        );
        assert_eq!(
            machine.coerce_primitive_default(wrapper).unwrap(),
            symbol,
            "ToPrimitive reaches the symbol through the prototype method"
        );
        assert!(matches!(
            machine.call_value(to_primitive, Value::int32(1), &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn failed_symbol_for_charge_releases_symbol_and_leaves_budget_unchanged() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let symbol_constructor = machine
            .intrinsics
            .global("Symbol")
            .expect("Symbol is installed");
        let symbol_for = machine
            .get_named_property(symbol_constructor, "for")
            .expect("Symbol.for is installed");
        let key = machine
            .allocate(HeapEntry::String(EcmaString::encode("key")))
            .expect("registry key allocation succeeds");
        let (
            heap_len_before,
            vacant_before,
            live_before,
            heap_bytes_before,
            machine_bytes_before,
            registry_len_before,
        ) = (
            machine.heap.len(),
            machine.vacant_count,
            machine.live_runtime_slots(),
            machine.heap_bytes,
            machine.machine_bytes,
            machine.intrinsics.symbol_registry.len(),
        );
        // The limit covers the new Symbol (3 code units * 2 bytes) but not the
        // registry entry, so the symbol allocation succeeds and the registry
        // charge fails, exercising the rollback path.
        machine.limits.max_heap_bytes = machine.heap_bytes + 2 * 3;

        assert!(matches!(
            machine.call_value(symbol_for, symbol_constructor, &[key]),
            Err(EvalFailure::Runtime(
                crate::RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert_eq!(
            (
                machine.heap.len(),
                machine.vacant_count,
                machine.live_runtime_slots(),
                machine.heap_bytes,
                machine.machine_bytes,
                machine.intrinsics.symbol_registry.len(),
            ),
            (
                heap_len_before + 1,
                vacant_before + 1,
                live_before,
                heap_bytes_before,
                machine_bytes_before,
                registry_len_before,
            ),
            "a failed Symbol.for charge must release the symbol and leave budget and registry unchanged"
        );
    }
    // --- Symbol.hasInstance / instanceof -------------------------------------

    /// A registered builtin that returns the boolean stored on `this` under
    /// `_hasInstanceResult`, modeling a user-defined `@@hasInstance` handler
    /// whose outcome the test controls.
    fn custom_has_instance<H: Host>(
        machine: &mut Machine<'_, H>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let result = machine.get_named_property(this, "_hasInstanceResult")?;
        Ok(BuiltinOutcome::Value(result))
    }

    fn has_instance_property_key(machine: &mut Machine<'_, TestHost>) -> PropertyKey {
        let symbol_constructor = machine
            .intrinsics
            .global("Symbol")
            .expect("Symbol is installed");
        let has_instance = machine
            .get_named_property(symbol_constructor, "hasInstance")
            .expect("Symbol.hasInstance is installed");
        machine
            .property_key_from_value(has_instance)
            .expect("Symbol.hasInstance is a valid property key")
    }

    /// An ordinary object whose prototype is `prototype`, giving the test
    /// exact control over the value's prototype chain.
    fn object_with_prototype(machine: &mut Machine<'_, TestHost>, prototype: Value) -> Value {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .expect("object allocation succeeds")
    }

    /// A minimal constructor function whose `.prototype` is `prototype`. The
    /// function body is the blank program's halt entry; `instanceof` only
    /// reads `.prototype`, it never calls the constructor.
    fn constructor_with_prototype(machine: &mut Machine<'_, TestHost>, prototype: Value) -> Value {
        let prototype_key = PropertyKey::Named(machine.intern_str("prototype"));
        let mut properties = PropertyMap::default();
        properties.insert(
            &mut machine.shapes,
            prototype_key,
            Property::Data {
                value: prototype,
                writable: true,
                enumerable: false,
                configurable: false,
            },
        );
        machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(0),
                captures: Vec::new(),
                context: None,
                properties,
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .expect("constructor allocation succeeds")
    }

    #[test]
    fn instanceof_consults_callable_symbol_has_instance() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // The value's prototype chain is unrelated to the constructor, so a
        // true result can only come from the @@hasInstance handler.
        let ctor_proto = ordinary_object(&mut machine);
        let constructor = constructor_with_prototype(&mut machine, ctor_proto);
        let unrelated_proto = ordinary_object(&mut machine);
        let value = object_with_prototype(&mut machine, unrelated_proto);

        let handler_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "custom hasInstance",
            length: 1,
            handler: custom_has_instance::<TestHost>,
        });
        let handler = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            handler_id,
            "custom hasInstance",
            1,
        );
        machine
            .set_data_property(constructor, "_hasInstanceResult", Value::TRUE)
            .unwrap();
        let key = has_instance_property_key(&mut machine);
        machine
            .create_data_property_key(constructor, key, handler)
            .unwrap();

        assert!(
            machine.instance_of(value, constructor).unwrap(),
            "a callable @@hasInstance returning true must make instanceof true"
        );

        // Flip the handler to false: the same value must now be false, proving
        // the handler's result is respected rather than the prototype chain.
        machine
            .set_data_property(constructor, "_hasInstanceResult", Value::FALSE)
            .unwrap();
        assert!(
            !machine.instance_of(value, constructor).unwrap(),
            "a callable @@hasInstance returning false must make instanceof false"
        );
    }

    #[test]
    fn instanceof_falls_back_to_prototype_chain_without_symbol_has_instance() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let ctor_proto = ordinary_object(&mut machine);
        let constructor = constructor_with_prototype(&mut machine, ctor_proto);

        // No @@hasInstance installed: the ordinary prototype-chain check runs.
        let on_chain = object_with_prototype(&mut machine, ctor_proto);
        let off_chain_proto = ordinary_object(&mut machine);
        let off_chain = object_with_prototype(&mut machine, off_chain_proto);

        assert!(
            machine.instance_of(on_chain, constructor).unwrap(),
            "a value on the prototype chain must be an instance without @@hasInstance"
        );
        assert!(
            !machine.instance_of(off_chain, constructor).unwrap(),
            "a value off the prototype chain must not be an instance without @@hasInstance"
        );
    }

    #[test]
    fn instanceof_callable_has_instance_overrides_prototype_chain() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        // The value IS on the constructor's prototype chain, so the ordinary
        // check would say true; a @@hasInstance returning false must override.
        let ctor_proto = ordinary_object(&mut machine);
        let constructor = constructor_with_prototype(&mut machine, ctor_proto);
        let on_chain = object_with_prototype(&mut machine, ctor_proto);

        let handler_id = machine.intrinsics.builtins.register(BuiltinDef {
            name: "custom hasInstance override",
            length: 1,
            handler: custom_has_instance::<TestHost>,
        });
        let handler = native_function(
            &mut machine.heap,
            &mut machine.atoms,
            &mut machine.shapes,
            handler_id,
            "custom hasInstance override",
            1,
        );
        machine
            .set_data_property(constructor, "_hasInstanceResult", Value::FALSE)
            .unwrap();
        let key = has_instance_property_key(&mut machine);
        machine
            .create_data_property_key(constructor, key, handler)
            .unwrap();

        assert!(
            !machine.instance_of(on_chain, constructor).unwrap(),
            "a callable @@hasInstance returning false must override a matching prototype chain"
        );
    }

    #[test]
    fn instanceof_non_callable_symbol_has_instance_throws_type_error() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());

        let ctor_proto = ordinary_object(&mut machine);
        let constructor = constructor_with_prototype(&mut machine, ctor_proto);

        // A present but non-callable @@hasInstance is a TypeError per GetMethod.
        let key = has_instance_property_key(&mut machine);
        machine
            .create_data_property_key(constructor, key, Value::int32(42))
            .unwrap();

        let value = ordinary_object(&mut machine);
        assert!(
            matches!(
                machine.instance_of(value, constructor),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
            ),
            "a non-callable @@hasInstance must throw a TypeError"
        );
    }
}
