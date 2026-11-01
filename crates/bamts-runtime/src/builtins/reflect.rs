use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{SlotId, Value};

use super::object::create_list_from_array_like;
use super::property_descriptor::{from_property_descriptor, to_property_descriptor};
use super::{
    allocate_array, allocate_string, define_data, define_to_string_tag, install_function,
    type_error,
};
use crate::intrinsics::{BuiltinHandler, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, PropertyKey, PropertyMap, RUNTIME_HEAP_SEGMENT,
};

pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let reflect = super::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.object_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    for (name, length, handler) in [
        ("apply", 3, apply::<H> as BuiltinHandler<H>),
        ("construct", 2, construct::<H>),
        ("defineProperty", 3, define_property::<H>),
        ("deleteProperty", 2, delete_property::<H>),
        ("get", 2, get::<H>),
        (
            "getOwnPropertyDescriptor",
            2,
            get_own_property_descriptor::<H>,
        ),
        ("getPrototypeOf", 1, get_prototype_of::<H>),
        ("has", 2, has::<H>),
        ("isExtensible", 1, is_extensible::<H>),
        ("ownKeys", 1, own_keys::<H>),
        ("preventExtensions", 1, prevent_extensions::<H>),
        ("set", 3, set::<H>),
        ("setPrototypeOf", 2, set_prototype_of::<H>),
    ] {
        let function = install_function(heap, builtins, name, length, handler);
        define_data(heap, reflect, name, function);
    }
    define_to_string_tag(heap, reflect, builtins.symbol_to_string_tag(), "Reflect");
    globals.insert(EcmaString::encode("Reflect"), reflect);
}

fn argument(args: &[Value], index: usize) -> Value {
    args.get(index).copied().unwrap_or(Value::UNDEFINED)
}

fn require_object<H: Host>(
    machine: &Machine<'_, H>,
    args: &[Value],
    operation: &'static str,
) -> Result<Value, EvalFailure> {
    let target = argument(args, 0);
    if !machine.is_object(target) {
        return Err(type_error(operation));
    }
    Ok(target)
}

fn reject_construction(constructing: bool, operation: &'static str) -> Result<(), EvalFailure> {
    if constructing {
        return Err(type_error(operation));
    }
    Ok(())
}

fn apply<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.apply is not a constructor")?;
    let target = argument(args, 0);
    if !machine.is_callable(target)? {
        return Err(type_error("Reflect.apply target is not callable"));
    }
    let arguments = create_list_from_array_like(machine, argument(args, 2))?;
    Ok(BuiltinOutcome::Call {
        callee: target,
        this_value: argument(args, 1),
        arguments,
    })
}

fn construct<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.construct is not a constructor")?;
    let target = argument(args, 0);
    if !machine.is_constructor(target)? {
        return Err(type_error("Reflect.construct target is not a constructor"));
    }
    let new_target = args.get(2).copied().unwrap_or(target);
    if !machine.is_constructor(new_target)? {
        return Err(type_error(
            "Reflect.construct newTarget is not a constructor",
        ));
    }
    let arguments = create_list_from_array_like(machine, argument(args, 1))?;
    Ok(BuiltinOutcome::Value(
        machine.internal_construct(target, &arguments, new_target)?,
    ))
}

fn define_property<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.defineProperty is not a constructor")?;
    let target = require_object(
        machine,
        args,
        "Reflect.defineProperty target is not an object",
    )?;
    let key = machine.observable_property_key(argument(args, 1))?;
    let descriptor = to_property_descriptor(machine, argument(args, 2))?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_define_own_property(target, key, descriptor)?,
    )))
}

fn delete_property<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.deleteProperty is not a constructor")?;
    let target = require_object(
        machine,
        args,
        "Reflect.deleteProperty target is not an object",
    )?;
    let key = machine.observable_property_key(argument(args, 1))?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_delete(target, &key)?,
    )))
}

fn get<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.get is not a constructor")?;
    let target = require_object(machine, args, "Reflect.get target is not an object")?;
    let key = machine.observable_property_key(argument(args, 1))?;
    let receiver = args.get(2).copied().unwrap_or(target);
    Ok(BuiltinOutcome::Value(
        machine.internal_get(target, &key, receiver)?,
    ))
}

fn get_own_property_descriptor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        "Reflect.getOwnPropertyDescriptor is not a constructor",
    )?;
    let target = require_object(
        machine,
        args,
        "Reflect.getOwnPropertyDescriptor target is not an object",
    )?;
    let key = machine.observable_property_key(argument(args, 1))?;
    let descriptor = machine.internal_get_own_property(target, &key)?;
    Ok(BuiltinOutcome::Value(from_property_descriptor(
        machine, descriptor,
    )?))
}

fn get_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.getPrototypeOf is not a constructor")?;
    let target = require_object(
        machine,
        args,
        "Reflect.getPrototypeOf target is not an object",
    )?;
    Ok(BuiltinOutcome::Value(
        machine
            .internal_get_prototype_of(target)?
            .unwrap_or(Value::NULL),
    ))
}

fn has<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.has is not a constructor")?;
    let target = require_object(machine, args, "Reflect.has target is not an object")?;
    let key = machine.observable_property_key(argument(args, 1))?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_has_property(target, &key)?,
    )))
}

fn is_extensible<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.isExtensible is not a constructor")?;
    let target = require_object(
        machine,
        args,
        "Reflect.isExtensible target is not an object",
    )?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_is_extensible(target)?,
    )))
}

pub(crate) fn property_key_value<H: Host>(
    machine: &mut Machine<'_, H>,
    key: PropertyKey,
) -> Result<Value, EvalFailure> {
    match key {
        PropertyKey::Named(name) => allocate_string(machine, name),
        PropertyKey::Symbol(index) => Ok(Value::heap_ref(
            SlotId::from_parts(RUNTIME_HEAP_SEGMENT, index + 1)
                .expect("symbol property key is a valid runtime slot"),
        )),
        PropertyKey::Private(_) => Err(type_error("Reflect.ownKeys encountered a private name")),
    }
}

fn own_keys<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.ownKeys is not a constructor")?;
    let target = require_object(machine, args, "Reflect.ownKeys target is not an object")?;
    let keys = machine
        .internal_own_property_keys(target)?
        .into_iter()
        .map(|key| property_key_value(machine, key))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(BuiltinOutcome::Value(allocate_array(machine, keys)?))
}

fn prevent_extensions<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(
        constructing,
        "Reflect.preventExtensions is not a constructor",
    )?;
    let target = require_object(
        machine,
        args,
        "Reflect.preventExtensions target is not an object",
    )?;
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_prevent_extensions(target)?,
    )))
}

fn set<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.set is not a constructor")?;
    let target = require_object(machine, args, "Reflect.set target is not an object")?;
    let key = machine.observable_property_key(argument(args, 1))?;
    let receiver = args.get(3).copied().unwrap_or(target);
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_set(target, key, argument(args, 2), receiver)?,
    )))
}

fn set_prototype_of<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    reject_construction(constructing, "Reflect.setPrototypeOf is not a constructor")?;
    let target = require_object(
        machine,
        args,
        "Reflect.setPrototypeOf target is not an object",
    )?;
    let prototype = argument(args, 1);
    let prototype = if prototype == Value::NULL {
        None
    } else if machine.is_object(prototype) {
        Some(prototype)
    } else {
        return Err(type_error(
            "Reflect.setPrototypeOf prototype is not an object or null",
        ));
    };
    Ok(BuiltinOutcome::Value(Value::boolean(
        machine.internal_set_prototype_of(target, prototype)?,
    )))
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{
        TestHost, blank_program, constructable_program, ordinary_object,
    };
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, NativeCallable, Property, ThrowOrigin};
    use bamts_bytecode::{FunctionId, ModuleId};
    use bamts_native::Decoded;

    fn call_reflect(
        machine: &mut Machine<'_, TestHost>,
        name: &str,
        args: &[Value],
    ) -> Result<Value, EvalFailure> {
        let reflect = machine
            .intrinsics
            .global("Reflect")
            .expect("Reflect installed");
        let method = machine.get_named_property(reflect, name)?;
        machine.call_value(method, reflect, args)
    }

    fn empty_array(machine: &mut Machine<'_, TestHost>) -> Value {
        allocate_array(machine, Vec::new()).expect("array allocation succeeds")
    }

    fn callback(
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
        native_function(&mut machine.heap, id, name, length)
    }

    fn return_this(
        _machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Ok(BuiltinOutcome::Value(this))
    }

    fn write_receiver(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "written", argument(args, 0))?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn throw_late(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("late observable operation"))
    }

    fn symbol(machine: &mut Machine<'_, TestHost>, description: &str) -> Value {
        machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode(description),
            })
            .expect("symbol allocation succeeds")
    }

    #[test]
    fn installs_exact_reflect_surface_and_method_descriptors() {
        let module = constructable_program("<reflect-metadata>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let reflect = machine
            .intrinsics
            .global("Reflect")
            .expect("Reflect installed");
        assert!(machine.is_object(reflect));
        assert!(!machine.is_callable(reflect).unwrap());

        for (name, length) in [
            ("apply", 3),
            ("construct", 2),
            ("defineProperty", 3),
            ("deleteProperty", 2),
            ("get", 2),
            ("getOwnPropertyDescriptor", 2),
            ("getPrototypeOf", 1),
            ("has", 2),
            ("isExtensible", 1),
            ("ownKeys", 1),
            ("preventExtensions", 1),
            ("set", 3),
            ("setPrototypeOf", 2),
        ] {
            let key = PropertyKey::Named(EcmaString::encode(name));
            let Some(Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            }) = machine.own_descriptor(reflect, &key).unwrap()
            else {
                panic!("Reflect.{name} must be writable, non-enumerable, configurable data");
            };
            let Some(Decoded::HeapRef(id)) = value.decode() else {
                panic!("Reflect.{name} must be a native function");
            };
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(builtin),
                ..
            } = machine.heap[id.slot() as usize - 1]
            else {
                panic!("Reflect.{name} must be a builtin");
            };
            let definition = machine.intrinsics.builtins.get(builtin);
            assert_eq!(definition.name, name);
            assert_eq!(definition.length, length);
            let function_name = machine.get_named_property(value, "name").unwrap();
            assert!(
                machine
                    .string_value(function_name)
                    .is_some_and(|text| text.eq_ascii(name))
            );
            assert_eq!(
                machine.get_named_property(value, "length").unwrap(),
                Value::int32(length)
            );
        }

        let tag_key = machine
            .observable_property_key(machine.intrinsics.builtins.symbol_to_string_tag())
            .unwrap();
        let Some(Property::Data {
            value: tag,
            writable: false,
            enumerable: false,
            configurable: true,
        }) = machine.own_descriptor(reflect, &tag_key).unwrap()
        else {
            panic!("Reflect @@toStringTag has the required descriptor");
        };
        assert!(
            machine
                .string_value(tag)
                .is_some_and(|text| text.eq_ascii("Reflect"))
        );
    }

    #[test]
    fn rejects_non_object_targets_before_later_coercions() {
        let module = blank_program("<reflect-target-checks>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let throwing = callback(&mut machine, "late getter", 0, throw_late);
        let key = ordinary_object(&mut machine);
        machine
            .define_descriptor(
                key,
                PropertyKey::Named(EcmaString::encode("toString")),
                Property::Accessor {
                    getter: Some(throwing),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();

        for name in [
            "defineProperty",
            "deleteProperty",
            "get",
            "getOwnPropertyDescriptor",
            "has",
            "set",
        ] {
            assert!(matches!(
                call_reflect(&mut machine, name, &[Value::int32(1), key]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                    if operation.contains("target")
            ));
        }
        for name in [
            "getPrototypeOf",
            "isExtensible",
            "ownKeys",
            "preventExtensions",
            "setPrototypeOf",
        ] {
            assert!(matches!(
                call_reflect(&mut machine, name, &[Value::int32(1), key]),
                Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                    if operation.contains("target")
            ));
        }
        assert!(matches!(
            call_reflect(
                &mut machine,
                "apply",
                &[Value::int32(1), Value::UNDEFINED, key]
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation.contains("target")
        ));
        assert!(matches!(
            call_reflect(&mut machine, "construct", &[Value::int32(1), key]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation.contains("target")
        ));
    }

    #[test]
    fn apply_construct_and_receiver_defaults_follow_spec_order() {
        let module = constructable_program("<reflect-call-order>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let return_this_value = callback(&mut machine, "return this", 0, return_this);
        let receiver = ordinary_object(&mut machine);
        let arguments = empty_array(&mut machine);
        assert_eq!(
            call_reflect(
                &mut machine,
                "apply",
                &[return_this_value, receiver, arguments]
            )
            .unwrap(),
            receiver
        );

        let target = ordinary_object(&mut machine);
        let getter = callback(&mut machine, "receiver getter", 0, return_this);
        let setter = callback(&mut machine, "receiver setter", 1, write_receiver);
        machine
            .define_descriptor(
                target,
                PropertyKey::Named(EcmaString::encode("value")),
                Property::Accessor {
                    getter: Some(getter),
                    setter: Some(setter),
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let key = allocate_string(&mut machine, EcmaString::encode("value")).unwrap();
        assert_eq!(
            call_reflect(&mut machine, "get", &[target, key]).unwrap(),
            target
        );
        assert_eq!(
            call_reflect(&mut machine, "get", &[target, key, receiver]).unwrap(),
            receiver
        );
        assert_eq!(
            call_reflect(
                &mut machine,
                "set",
                &[target, key, Value::int32(7), receiver]
            )
            .unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.get_named_property(receiver, "written").unwrap(),
            Value::int32(7)
        );

        let object = machine.intrinsics.global("Object").unwrap();
        let default_instance =
            call_reflect(&mut machine, "construct", &[object, arguments]).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(default_instance).unwrap(),
            Some(machine.intrinsics.object_prototype)
        );

        let prototype = ordinary_object(&mut machine);
        let mut properties = PropertyMap::default();
        properties.insert(
            PropertyKey::Named(EcmaString::encode("prototype")),
            Property::Data {
                value: prototype,
                writable: true,
                enumerable: false,
                configurable: false,
            },
        );
        let new_target = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(0),
                captures: Vec::new(),
                context: None,
                properties,
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap();
        let custom_instance =
            call_reflect(&mut machine, "construct", &[object, arguments, new_target]).unwrap();
        assert_eq!(
            machine.internal_get_prototype_of(custom_instance).unwrap(),
            Some(prototype)
        );

        let throwing_args = ordinary_object(&mut machine);
        let late = callback(&mut machine, "late length", 0, throw_late);
        machine
            .define_descriptor(
                throwing_args,
                PropertyKey::Named(EcmaString::encode("length")),
                Property::Accessor {
                    getter: Some(late),
                    setter: None,
                    enumerable: false,
                    configurable: true,
                },
            )
            .unwrap();
        assert!(matches!(
            call_reflect(
                &mut machine,
                "construct",
                &[object, throwing_args, Value::int32(0)]
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
                if operation.contains("newTarget")
        ));
    }

    #[test]
    fn descriptor_conversion_and_false_results_are_preserved() {
        let module = blank_program("<reflect-descriptors>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let target = ordinary_object(&mut machine);
        let key = allocate_string(&mut machine, EcmaString::encode("fixed")).unwrap();
        let descriptor = ordinary_object(&mut machine);
        machine
            .set_data_property(descriptor, "value", Value::int32(42))
            .unwrap();
        machine
            .set_data_property(descriptor, "writable", Value::FALSE)
            .unwrap();
        machine
            .set_data_property(descriptor, "enumerable", Value::TRUE)
            .unwrap();
        machine
            .set_data_property(descriptor, "configurable", Value::FALSE)
            .unwrap();
        assert_eq!(
            call_reflect(&mut machine, "defineProperty", &[target, key, descriptor]).unwrap(),
            Value::TRUE
        );
        let reified =
            call_reflect(&mut machine, "getOwnPropertyDescriptor", &[target, key]).unwrap();
        assert_eq!(
            machine.get_named_property(reified, "value").unwrap(),
            Value::int32(42)
        );
        assert_eq!(
            machine.get_named_property(reified, "writable").unwrap(),
            Value::FALSE
        );
        assert_eq!(
            machine.get_named_property(reified, "enumerable").unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine.get_named_property(reified, "configurable").unwrap(),
            Value::FALSE
        );
        assert_eq!(
            call_reflect(&mut machine, "get", &[target, key]).unwrap(),
            Value::int32(42)
        );
        assert_eq!(
            call_reflect(&mut machine, "has", &[target, key]).unwrap(),
            Value::TRUE
        );
        assert_eq!(
            call_reflect(&mut machine, "isExtensible", &[target]).unwrap(),
            Value::TRUE
        );
        assert_eq!(
            call_reflect(&mut machine, "getPrototypeOf", &[target]).unwrap(),
            machine.intrinsics.object_prototype
        );
        assert_eq!(
            call_reflect(&mut machine, "deleteProperty", &[target, key]).unwrap(),
            Value::FALSE
        );
        assert_eq!(
            call_reflect(&mut machine, "set", &[target, key, Value::int32(9)]).unwrap(),
            Value::FALSE
        );
        assert_eq!(
            call_reflect(&mut machine, "preventExtensions", &[target]).unwrap(),
            Value::TRUE
        );
        assert_eq!(
            call_reflect(&mut machine, "isExtensible", &[target]).unwrap(),
            Value::FALSE
        );
        let new_key = allocate_string(&mut machine, EcmaString::encode("new")).unwrap();
        let new_descriptor = ordinary_object(&mut machine);
        assert_eq!(
            call_reflect(
                &mut machine,
                "defineProperty",
                &[target, new_key, new_descriptor]
            )
            .unwrap(),
            Value::FALSE
        );
        let different_prototype = ordinary_object(&mut machine);
        assert_eq!(
            call_reflect(
                &mut machine,
                "setPrototypeOf",
                &[target, different_prototype]
            )
            .unwrap(),
            Value::FALSE
        );
    }

    #[test]
    fn own_keys_preserves_canonical_integer_string_symbol_order() {
        let module = blank_program("<reflect-own-keys>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let target = ordinary_object(&mut machine);
        machine.set_data_property(target, "2", Value::TRUE).unwrap();
        machine.set_data_property(target, "x", Value::TRUE).unwrap();
        machine.set_data_property(target, "1", Value::TRUE).unwrap();
        let symbol = symbol(&mut machine, "tail");
        let symbol_key = machine.observable_property_key(symbol).unwrap();
        machine
            .set_data_property_key(target, symbol_key, Value::TRUE)
            .unwrap();

        let keys = call_reflect(&mut machine, "ownKeys", &[target]).unwrap();
        let keys = machine.array_elements(keys).unwrap().unwrap();
        assert_eq!(keys.len(), 4);
        for (value, expected) in keys[..3].iter().zip(["1", "2", "x"]) {
            assert!(
                machine
                    .string_value(*value)
                    .is_some_and(|text| text.eq_ascii(expected))
            );
        }
        assert_eq!(keys[3], symbol);
    }

    #[test]
    fn abrupt_completion_from_keys_descriptors_and_accessors_propagates() {
        let module = blank_program("<reflect-abrupt>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let target = ordinary_object(&mut machine);
        let throwing = callback(&mut machine, "abrupt getter", 0, throw_late);
        machine
            .define_descriptor(
                target,
                PropertyKey::Named(EcmaString::encode("boom")),
                Property::Accessor {
                    getter: Some(throwing),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let boom = allocate_string(&mut machine, EcmaString::encode("boom")).unwrap();
        assert!(matches!(
            call_reflect(&mut machine, "get", &[target, boom]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "late observable operation"
            }))
        ));

        let key = ordinary_object(&mut machine);
        machine
            .define_descriptor(
                key,
                PropertyKey::Named(EcmaString::encode("toString")),
                Property::Accessor {
                    getter: Some(throwing),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        assert!(matches!(
            call_reflect(&mut machine, "has", &[target, key]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "late observable operation"
            }))
        ));

        let descriptor = ordinary_object(&mut machine);
        machine
            .define_descriptor(
                descriptor,
                PropertyKey::Named(EcmaString::encode("enumerable")),
                Property::Accessor {
                    getter: Some(throwing),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        assert!(matches!(
            call_reflect(&mut machine, "defineProperty", &[target, boom, descriptor]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "late observable operation"
            }))
        ));
    }
}
