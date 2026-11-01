use std::collections::BTreeMap;

use bamts_bytecode::{Constant, EcmaString, EcmaStringBuilder};
use bamts_native::Value;

use super::{
    allocate_array, allocate_string, heap_index, install_constructor_function, install_function,
    type_error,
};
use crate::intrinsics::{BuiltinOutcome, BuiltinTable};
use crate::{EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap};

const STACK_GETTER: &str = "\0error.stack.get";
const STACK_SETTER: &str = "\0error.stack.set";
const MAX_CAUSE_DEPTH: usize = 32;

const ERROR_TYPES: [(&str, u32); 9] = [
    ("Error", 1),
    ("EvalError", 1),
    ("RangeError", 1),
    ("ReferenceError", 1),
    ("SyntaxError", 1),
    ("TypeError", 1),
    ("URIError", 1),
    ("AggregateError", 2),
    ("SuppressedError", 3),
];

/// Replaces the baseline error constructors while retaining their realm-owned
/// prototypes. Main must call this after the baseline error installation.
pub(super) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
) {
    let brand = crate::intrinsics::push(
        heap,
        HeapEntry::PrivateName {
            description: EcmaString::encode("[[ErrorData]]"),
        },
    );
    builtins.set_error_brand(brand);
    let error_prototype = prototype_of(heap, globals, "Error");
    let stack_getter = install_function(heap, builtins, "get stack", 0, stack_get::<H>);
    let stack_setter = install_function(heap, builtins, "set stack", 1, stack_set::<H>);
    define_hidden(heap, error_prototype, STACK_GETTER, stack_getter);
    define_hidden(heap, error_prototype, STACK_SETTER, stack_setter);

    for (name, length) in ERROR_TYPES {
        let prototype = prototype_of(heap, globals, name);
        let constructor =
            install_constructor_function(heap, builtins, name, length, error_constructor::<H>);
        builtins.set_constructor_prototype(heap, constructor, prototype);
        builtins.set_error_prototype(heap, constructor, prototype);
        if name == "Error" {
            let capture = install_function(
                heap,
                builtins,
                "captureStackTrace",
                1,
                capture_stack_trace::<H>,
            );
            define_static(heap, constructor, "captureStackTrace", capture);
            let is_error = install_function(heap, builtins, "isError", 1, is_error::<H>);
            define_static(heap, constructor, "isError", is_error);
        }
        globals.insert(EcmaString::encode(name), constructor);
    }
}

fn prototype_of(heap: &[HeapEntry], globals: &BTreeMap<EcmaString, Value>, name: &str) -> Value {
    let constructor = globals
        .get(&EcmaString::encode(name))
        .copied()
        .expect("baseline error constructor is installed first");
    own_data(heap, constructor, "prototype")
}

fn own_data(heap: &[HeapEntry], object: Value, name: &str) -> Value {
    let properties = match &heap[heap_index(object)] {
        HeapEntry::Object { properties, .. } | HeapEntry::NativeFunction { properties, .. } => {
            properties
        }
        _ => panic!("error intrinsic property owner is an object"),
    };
    match properties.get(&PropertyKey::Named(EcmaString::encode(name))) {
        Some(Property::Data { value, .. }) => *value,
        _ => panic!("error intrinsic data property exists"),
    }
}

fn define_static(heap: &mut [HeapEntry], constructor: Value, name: &str, value: Value) {
    let HeapEntry::NativeFunction { properties, .. } = &mut heap[heap_index(constructor)] else {
        panic!("error constructor is a native function")
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        super::builtin_property(value),
    );
}

fn define_hidden(heap: &mut [HeapEntry], object: Value, name: &str, value: Value) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        panic!("Error.prototype is an ordinary object")
    };
    properties.insert(
        PropertyKey::Named(EcmaString::encode(name)),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: false,
        },
    );
}

fn data(value: Value) -> Property {
    Property::Data {
        value,
        writable: true,
        enumerable: false,
        configurable: true,
    }
}

fn define_own<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    value: Value,
) -> Result<(), EvalFailure> {
    machine.define_descriptor(
        object,
        PropertyKey::Named(EcmaString::encode(name)),
        data(value),
    )
}

/// `Error.isError`: true only for objects an Error constructor made. The brand
/// is a private key, so a proxy for an error or an object that merely inherits
/// from `Error.prototype` does not have it.
fn is_error<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let value = args.first().copied().unwrap_or(Value::UNDEFINED);
    let brand = machine.intrinsics.builtins.error_brand_key();
    let branded = machine
        .runtime_slot(value)
        .map_err(EvalFailure::Runtime)?
        .is_some_and(|index| {
            matches!(
                &machine.heap[index],
                HeapEntry::Object { properties, .. } if properties.contains_key(&brand)
            )
        });
    Ok(BuiltinOutcome::Value(Value::boolean(branded)))
}

pub(super) fn error_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let id = machine
        .current_builtin_id()
        .ok_or_else(|| type_error("invalid error constructor"))?;
    let name = machine.intrinsics.builtins.get(id).name;
    let default_prototype = machine.intrinsics.error_prototype(id);
    let new_target = machine.current_new_target();
    let prototype = if new_target == Value::UNDEFINED {
        default_prototype
    } else {
        let candidate = machine.get_named_property(new_target, "prototype")?;
        if machine.is_object(candidate) {
            candidate
        } else {
            default_prototype
        }
    };
    let object = if machine.inherits_from_prototype(this, prototype)? {
        this
    } else {
        machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .map_err(EvalFailure::Runtime)?
    };

    let brand = machine.intrinsics.builtins.error_brand_key();
    machine.define_descriptor(object, brand, crate::error_brand())?;

    let (message_index, options_index) = match name {
        "AggregateError" => (1, 2),
        "SuppressedError" => (2, 3),
        _ => (0, 1),
    };
    let message = args
        .get(message_index)
        .copied()
        .filter(|value| *value != Value::UNDEFINED)
        .map(|value| machine.to_string(value))
        .transpose()?;
    if let Some(text) = &message {
        let value = allocate_string(machine, text.clone())?;
        define_own(machine, object, "message", value)?;
    }

    if let Some(options) = args.get(options_index).copied()
        && machine.is_object(options)
    {
        let key = PropertyKey::Named(EcmaString::encode("cause"));
        if machine.internal_has_property(options, &key)? {
            let cause = machine.get_named_property(options, "cause")?;
            define_own(machine, object, "cause", cause)?;
        }
    }

    match name {
        "AggregateError" => {
            let source = args.first().copied().unwrap_or(Value::UNDEFINED);
            let values = machine.iterable_values(source)?;
            let array = allocate_array(machine, values)?;
            define_own(machine, object, "errors", array)?;
        }
        "SuppressedError" => {
            define_own(
                machine,
                object,
                "error",
                args.first().copied().unwrap_or(Value::UNDEFINED),
            )?;
            define_own(
                machine,
                object,
                "suppressed",
                args.get(1).copied().unwrap_or(Value::UNDEFINED),
            )?;
        }
        _ => {}
    }

    install_stack(machine, object, name, message.as_ref(), None)?;
    Ok(BuiltinOutcome::Value(object))
}

fn install_stack<H: Host>(
    machine: &mut Machine<'_, H>,
    object: Value,
    name: &str,
    message: Option<&EcmaString>,
    skip: Option<Value>,
) -> Result<(), EvalFailure> {
    let name_value = allocate_string(machine, EcmaString::encode(name))?;
    let message_value = allocate_string(
        machine,
        message.cloned().unwrap_or_else(EcmaString::default),
    )?;
    let frames = format_frames(machine, skip);
    let frames_value = allocate_string(machine, frames)?;
    let error = machine
        .intrinsics
        .global("Error")
        .ok_or_else(|| type_error("Error constructor is not installed"))?;
    let error_prototype = machine.get_named_property(error, "prototype")?;
    let getter = machine.get_named_property(error_prototype, STACK_GETTER)?;
    let bind = machine.get_named_property(getter, "bind")?;
    let getter = machine.call_value(
        bind,
        getter,
        &[
            Value::UNDEFINED,
            object,
            name_value,
            message_value,
            frames_value,
        ],
    )?;
    let setter = machine.get_named_property(error_prototype, STACK_SETTER)?;
    machine.define_descriptor(
        object,
        PropertyKey::Named(EcmaString::encode("stack")),
        Property::Accessor {
            getter: Some(getter),
            setter: Some(setter),
            enumerable: false,
            configurable: true,
        },
    )
}

fn format_frames<H: Host>(machine: &Machine<'_, H>, skip: Option<Value>) -> EcmaString {
    let skip_target = skip.and_then(|value| {
        let index = machine.runtime_slot(value).ok().flatten()?;
        match machine.heap[index] {
            HeapEntry::Function {
                module, function, ..
            } => Some((module, function.get() as usize)),
            _ => None,
        }
    });
    let mut skipping = skip_target.is_some();
    let mut stack = EcmaStringBuilder::new();
    let mut emitted = false;
    let boundary = machine.callback_boundaries.last().copied().unwrap_or(0);
    let frames = &machine.frames[boundary.min(machine.frames.len())..];
    for frame in frames.iter().rev() {
        if boundary == 0 && frames.len() == 1 && frame.function == 0 && frame.pc == 0 {
            continue;
        }
        if skipping {
            if skip_target == Some((frame.module, frame.function)) {
                skipping = false;
            }
            continue;
        }
        emitted = true;
        stack.push_utf8("\n    at ");
        let code = machine.module_code(frame.module);
        let function = &code.functions()[frame.function];
        let frame_name =
            function
                .name()
                .and_then(|id| match &code.constants()[id.get() as usize] {
                    Constant::String(value) => Some(value),
                    _ => None,
                });
        if let Some(frame_name) = frame_name {
            for &unit in frame_name.as_units() {
                stack.push_unit(unit);
            }
        } else {
            stack.push_utf8("<anonymous>");
        }
        stack.push_utf8(" (module ");
        stack.push_utf8(&frame.module.get().to_string());
        stack.push_utf8(":");
        stack.push_utf8(&frame.pc.to_string());
        stack.push_utf8(")");
    }
    if !emitted {
        stack.push_utf8("\n    at <bamts>");
    }
    stack.finish()
}

fn stack_get<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let root = args.first().copied().unwrap_or(Value::UNDEFINED);
    let name = machine.to_string(args.get(1).copied().unwrap_or(Value::UNDEFINED))?;
    let message = machine.to_string(args.get(2).copied().unwrap_or(Value::UNDEFINED))?;
    let frames = machine.to_string(args.get(3).copied().unwrap_or(Value::UNDEFINED))?;
    let mut text = EcmaStringBuilder::new();
    append_error_header(&mut text, &name, &message);
    for &unit in frames.as_units() {
        text.push_unit(unit);
    }
    append_cause_chain(machine, &mut text, root)?;
    Ok(BuiltinOutcome::Value(allocate_string(
        machine,
        text.finish(),
    )?))
}

fn append_error_header(text: &mut EcmaStringBuilder, name: &EcmaString, message: &EcmaString) {
    for &unit in name.as_units() {
        text.push_unit(unit);
    }
    if !message.is_empty() {
        text.push_utf8(": ");
        for &unit in message.as_units() {
            text.push_unit(unit);
        }
    }
}

fn append_cause_chain<H: Host>(
    machine: &mut Machine<'_, H>,
    text: &mut EcmaStringBuilder,
    root: Value,
) -> Result<(), EvalFailure> {
    let cause_key = PropertyKey::Named(EcmaString::encode("cause"));
    let mut current = root;
    let mut seen = vec![root];

    for _ in 0..MAX_CAUSE_DEPTH {
        if !machine.is_object(current) || !machine.internal_has_property(current, &cause_key)? {
            return Ok(());
        }
        let cause = machine.get_named_property(current, "cause")?;
        text.push_utf8("\nCaused by: ");
        if machine.is_object(cause) {
            if seen.contains(&cause) {
                text.push_utf8("[Circular]");
                return Ok(());
            }
            seen.push(cause);
            let name_value = machine.get_named_property(cause, "name")?;
            let name = machine.to_string(name_value)?;
            let message_value = machine.get_named_property(cause, "message")?;
            let message = machine.to_string(message_value)?;
            append_error_header(text, &name, &message);
            current = cause;
        } else {
            let cause = machine.to_string(cause)?;
            for &unit in cause.as_units() {
                text.push_unit(unit);
            }
            return Ok(());
        }
    }
    text.push_utf8("\nCaused by: [Truncated]");
    Ok(())
}

fn stack_set<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    define_own(
        machine,
        this,
        "stack",
        args.first().copied().unwrap_or(Value::UNDEFINED),
    )?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

fn capture_stack_trace<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let target = args.first().copied().unwrap_or(Value::UNDEFINED);
    if !machine.is_object(target) {
        return Err(type_error(
            "Error.captureStackTrace target is not an object",
        ));
    }
    let skip = args
        .get(1)
        .copied()
        .filter(|value| *value != Value::UNDEFINED);
    if let Some(skip) = skip
        && !machine.is_callable(skip)?
    {
        return Err(type_error(
            "Error.captureStackTrace constructor is not callable",
        ));
    }
    install_stack(machine, target, "Error", None, skip)?;
    Ok(BuiltinOutcome::Value(Value::UNDEFINED))
}

#[cfg(test)]
mod is_error_tests {
    use super::super::test_support::{TestHost, blank_program, ordinary_object};
    use super::*;
    use crate::{Limits, ThrowOrigin};

    fn is_error_of(machine: &mut Machine<'_, TestHost>, value: Value) -> Value {
        let error = machine.intrinsics.global("Error").unwrap();
        let method = machine.get_named_property(error, "isError").unwrap();
        machine.call_value(method, error, &[value]).unwrap()
    }

    #[test]
    fn the_brand_decides_rather_than_the_prototype_chain() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("RangeError").unwrap();
        let real = machine.construct_value(constructor, &[]).unwrap();
        assert_eq!(is_error_of(&mut machine, real), Value::TRUE);

        let engine = machine
            .materialize_engine_origin(ThrowOrigin::TypeError { operation: "test" })
            .unwrap();
        assert_eq!(
            is_error_of(&mut machine, engine),
            Value::TRUE,
            "errors the engine throws carry the brand too"
        );

        let prototype = machine
            .get_named_property(constructor, "prototype")
            .unwrap();
        assert_eq!(is_error_of(&mut machine, prototype), Value::FALSE);
        let fake = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        assert_eq!(
            is_error_of(&mut machine, fake),
            Value::FALSE,
            "inheriting from an error prototype does not make an error"
        );
        let handler = ordinary_object(&mut machine);
        let proxy = super::super::proxy::create(&mut machine, real, handler).unwrap();
        assert_eq!(is_error_of(&mut machine, proxy), Value::FALSE);
        assert_eq!(is_error_of(&mut machine, Value::int32(1)), Value::FALSE);
    }

    #[test]
    fn the_brand_is_invisible_to_reflection() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let constructor = machine.intrinsics.global("Error").unwrap();
        let error = machine.construct_value(constructor, &[]).unwrap();
        let keys = machine.internal_own_property_keys(error).unwrap();
        assert!(
            !keys
                .iter()
                .any(|key| matches!(key, PropertyKey::Private(_)))
        );
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_support::{TestHost, blank_program, custom_iterable, ordinary_object};
    use super::*;
    use crate::intrinsics::{BuiltinDef, native_function};
    use crate::{Limits, NativeCallable, ThrowOrigin};

    macro_rules! machine {
        ($machine:ident) => {
            let program = blank_program("<error-edge>");
            let mut host = TestHost;
            let mut $machine = Machine::new(&program, &mut host, Limits::default());
        };
    }

    fn call_error(machine: &mut Machine<'_, TestHost>, name: &str, args: &[Value]) -> Value {
        let constructor = machine.intrinsics.global(name).expect("constructor");
        machine
            .call_value(constructor, Value::UNDEFINED, args)
            .unwrap()
    }

    fn descriptor(machine: &mut Machine<'_, TestHost>, object: Value, name: &str) -> Property {
        machine
            .own_descriptor(object, &PropertyKey::Named(EcmaString::encode(name)))
            .unwrap()
            .expect("own descriptor")
    }

    fn iterator_throw(
        _machine: &mut Machine<'_, TestHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        Err(type_error("iterator touched"))
    }

    fn cause_then_iterator(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "_phase", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(Value::UNDEFINED))
    }

    fn iterator_after_cause(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if machine.get_named_property(this, "_phase")? != Value::int32(1) {
            return Err(type_error("iterator before cause"));
        }
        machine.set_data_property(this, "_phase", Value::int32(2))?;
        Err(type_error("iterator after cause"))
    }

    fn cause_abrupt(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "_cause_read", Value::TRUE)?;
        Err(type_error("cause getter"))
    }

    fn chain_name(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.set_data_property(this, "_phase", Value::int32(1))?;
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("Named"),
        )?))
    }

    fn chain_message(
        machine: &mut Machine<'_, TestHost>,
        this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        if machine.get_named_property(this, "_phase")? != Value::int32(1) {
            return Err(type_error("message before name"));
        }
        machine.set_data_property(this, "_phase", Value::int32(2))?;
        Ok(BuiltinOutcome::Value(allocate_string(
            machine,
            EcmaString::encode("detail"),
        )?))
    }

    fn native(
        machine: &mut Machine<'_, TestHost>,
        name: &'static str,
        handler: crate::intrinsics::BuiltinHandler<TestHost>,
    ) -> Value {
        let id = machine.intrinsics.builtins.register(BuiltinDef {
            name,
            length: 0,
            handler,
        });
        native_function(&mut machine.heap, id, name, 0)
    }

    #[test]
    fn error_to_string_defaults_missing_fields_and_requires_an_object() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let error = machine.intrinsics.global("Error").unwrap();
        let prototype = machine.get_named_property(error, "prototype").unwrap();
        let to_string = machine.get_named_property(prototype, "toString").unwrap();
        assert!(matches!(
            machine.call_value(to_string, Value::UNDEFINED, &[]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let plain = ordinary_object(&mut machine);
        let text = machine.call_value(to_string, plain, &[]).unwrap();
        assert!(machine.string_value(text).unwrap().eq_ascii("Error"));
    }

    #[test]
    fn cause_distinguishes_absence_from_present_undefined() {
        machine!(machine);
        let absent = call_error(&mut machine, "Error", &[]);
        assert!(
            machine
                .own_descriptor(absent, &PropertyKey::Named(EcmaString::encode("cause")))
                .unwrap()
                .is_none()
        );

        let null_options = call_error(&mut machine, "Error", &[Value::UNDEFINED, Value::NULL]);
        assert!(
            machine
                .own_descriptor(
                    null_options,
                    &PropertyKey::Named(EcmaString::encode("cause")),
                )
                .unwrap()
                .is_none()
        );
        let options = ordinary_object(&mut machine);
        define_own(&mut machine, options, "cause", Value::UNDEFINED).unwrap();
        let present = call_error(&mut machine, "Error", &[Value::UNDEFINED, options]);
        assert!(matches!(
            descriptor(&mut machine, present, "cause"),
            Property::Data {
                value: Value::UNDEFINED,
                writable: true,
                enumerable: false,
                configurable: true
            }
        ));

        let inherited_cause = ordinary_object(&mut machine);
        define_own(&mut machine, inherited_cause, "cause", Value::int32(7)).unwrap();
        let inherited_options = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(inherited_cause),
                extensible: true,
                boxed_primitive: None,
            })
            .unwrap();
        let inherited = call_error(
            &mut machine,
            "Error",
            &[Value::UNDEFINED, inherited_options],
        );
        assert!(matches!(
            descriptor(&mut machine, inherited, "cause"),
            Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true
            } if value == Value::int32(7)
        ));
    }

    #[test]
    fn aggregate_errors_are_materialized_after_message_and_are_hidden() {
        machine!(machine);
        let iterable = custom_iterable(&mut machine, vec![Value::int32(3), Value::int32(5)]);
        let message = machine
            .allocate(HeapEntry::String(EcmaString::encode("many")))
            .unwrap();
        let error = call_error(&mut machine, "AggregateError", &[iterable, message]);
        let errors = match descriptor(&mut machine, error, "errors") {
            Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            } => value,
            other => panic!("wrong errors descriptor: {other:?}"),
        };
        assert_eq!(
            machine.array_elements(errors).unwrap().unwrap(),
            vec![Value::int32(3), Value::int32(5)]
        );
        let stack = machine.get_named_property(error, "stack").unwrap();
        assert!(
            machine
                .to_string(stack)
                .unwrap()
                .to_utf8_lossy()
                .starts_with("AggregateError: many")
        );
    }

    #[test]
    fn aggregate_converts_message_before_touching_iterator() {
        machine!(machine);
        let message = machine
            .allocate(HeapEntry::Symbol {
                description: EcmaString::encode("message"),
            })
            .unwrap();

        let iterable = ordinary_object(&mut machine);
        let iterator_throw = native(&mut machine, "iterator throw", iterator_throw);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.to_property_key(iterator_symbol).unwrap();
        machine
            .set_data_property_key(iterable, iterator_key, iterator_throw)
            .unwrap();
        let aggregate = machine.intrinsics.global("AggregateError").unwrap();
        assert!(matches!(
            machine.call_value(aggregate, Value::UNDEFINED, &[iterable, message]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "convert symbol to string"
            }))
        ));
    }

    #[test]
    fn aggregate_observes_cause_before_iterator_and_propagates_iterator_failure() {
        machine!(machine);
        let source_and_options = ordinary_object(&mut machine);
        let cause_getter = native(&mut machine, "cause getter", cause_then_iterator);
        machine
            .define_descriptor(
                source_and_options,
                PropertyKey::Named(EcmaString::encode("cause")),
                Property::Accessor {
                    getter: Some(cause_getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let iterator = native(&mut machine, "iterator", iterator_after_cause);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.to_property_key(iterator_symbol).unwrap();
        machine
            .set_data_property_key(source_and_options, iterator_key, iterator)
            .unwrap();

        let aggregate = machine.intrinsics.global("AggregateError").unwrap();
        assert!(matches!(
            machine.call_value(
                aggregate,
                Value::UNDEFINED,
                &[source_and_options, Value::UNDEFINED, source_and_options],
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator after cause"
            }))
        ));
        assert_eq!(
            machine
                .get_named_property(source_and_options, "_phase")
                .unwrap(),
            Value::int32(2)
        );
    }

    #[test]
    fn abrupt_cause_getter_prevents_aggregate_iterator_access() {
        machine!(machine);
        let source_and_options = ordinary_object(&mut machine);
        let cause_getter = native(&mut machine, "cause getter", cause_abrupt);
        machine
            .define_descriptor(
                source_and_options,
                PropertyKey::Named(EcmaString::encode("cause")),
                Property::Accessor {
                    getter: Some(cause_getter),
                    setter: None,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        let iterator = native(&mut machine, "iterator", iterator_after_cause);
        let iterator_symbol = machine.intrinsics.builtins.symbol_iterator();
        let iterator_key = machine.to_property_key(iterator_symbol).unwrap();
        machine
            .set_data_property_key(source_and_options, iterator_key, iterator)
            .unwrap();

        let aggregate = machine.intrinsics.global("AggregateError").unwrap();
        assert!(matches!(
            machine.call_value(
                aggregate,
                Value::UNDEFINED,
                &[source_and_options, Value::UNDEFINED, source_and_options],
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "cause getter"
            }))
        ));
        assert_eq!(
            machine
                .get_named_property(source_and_options, "_cause_read")
                .unwrap(),
            Value::TRUE
        );
        assert_eq!(
            machine
                .get_named_property(source_and_options, "_phase")
                .unwrap(),
            Value::UNDEFINED
        );
    }

    #[test]
    fn hostile_aggregate_iterable_is_typed_abrupt_completion() {
        machine!(machine);
        assert!(matches!(
            machine.call_value(
                machine.intrinsics.global("AggregateError").unwrap(),
                Value::UNDEFINED,
                &[Value::UNDEFINED]
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "value is not iterable"
            }))
        ));
        let hostile = custom_iterable(&mut machine, vec![Value::int32(1)]);
        machine
            .set_data_property(hostile, "_next", Value::int32(0))
            .unwrap();
        let aggregate = machine.intrinsics.global("AggregateError").unwrap();
        assert!(matches!(
            machine.call_value(aggregate, Value::UNDEFINED, &[hostile]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
    }

    #[test]
    fn cause_chain_reads_name_then_message_once() {
        machine!(machine);
        let cause = ordinary_object(&mut machine);
        let name_getter = native(&mut machine, "name getter", chain_name);
        let message_getter = native(&mut machine, "message getter", chain_message);
        for (name, getter) in [("name", name_getter), ("message", message_getter)] {
            machine
                .define_descriptor(
                    cause,
                    PropertyKey::Named(EcmaString::encode(name)),
                    Property::Accessor {
                        getter: Some(getter),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
        }
        let outer = call_error(&mut machine, "Error", &[]);
        define_own(&mut machine, outer, "cause", cause).unwrap();

        let stack = machine.get_named_property(outer, "stack").unwrap();
        let stack = machine.to_string(stack).unwrap().to_utf8_lossy();
        assert!(stack.ends_with("\nCaused by: Named: detail"));
        assert_eq!(
            machine.get_named_property(cause, "_phase").unwrap(),
            Value::int32(2)
        );
    }

    #[test]
    fn stack_formats_deterministic_nested_cause_headers() {
        machine!(machine);
        let inner_message = allocate_string(&mut machine, EcmaString::encode("inner")).unwrap();
        let inner = call_error(&mut machine, "TypeError", &[inner_message]);
        let outer_message = allocate_string(&mut machine, EcmaString::encode("outer")).unwrap();
        let outer = call_error(&mut machine, "Error", &[outer_message]);
        define_own(&mut machine, outer, "cause", inner).unwrap();
        let changed_name = allocate_string(&mut machine, EcmaString::encode("Changed")).unwrap();
        let changed_message = allocate_string(&mut machine, EcmaString::encode("changed")).unwrap();
        define_own(&mut machine, outer, "name", changed_name).unwrap();
        define_own(&mut machine, outer, "message", changed_message).unwrap();

        let stack = machine.get_named_property(outer, "stack").unwrap();
        let stack = machine.to_string(stack).unwrap().to_utf8_lossy();
        assert!(stack.starts_with("Error: outer\n"));
        assert!(stack.ends_with("\nCaused by: TypeError: inner"));
    }

    #[test]
    fn stack_cause_chain_reports_cycles_and_depth_limit() {
        machine!(machine);
        let first = call_error(&mut machine, "Error", &[]);
        let second = call_error(&mut machine, "Error", &[]);
        define_own(&mut machine, first, "cause", second).unwrap();
        define_own(&mut machine, second, "cause", first).unwrap();
        let cyclic = machine.get_named_property(first, "stack").unwrap();
        let cyclic = machine.to_string(cyclic).unwrap().to_utf8_lossy();
        assert!(cyclic.ends_with("\nCaused by: Error\nCaused by: [Circular]"));

        let mut chain = Vec::with_capacity(MAX_CAUSE_DEPTH + 2);
        for _ in 0..MAX_CAUSE_DEPTH + 2 {
            chain.push(call_error(&mut machine, "Error", &[]));
        }
        for pair in chain.windows(2) {
            define_own(&mut machine, pair[0], "cause", pair[1]).unwrap();
        }
        let deep = machine.get_named_property(chain[0], "stack").unwrap();
        let deep = machine.to_string(deep).unwrap().to_utf8_lossy();
        assert!(deep.ends_with("\nCaused by: [Truncated]"));
        assert_eq!(deep.matches("\nCaused by: ").count(), MAX_CAUSE_DEPTH + 1);
    }

    #[test]
    fn subclass_prototype_and_stack_overrides_are_observable() {
        machine!(machine);
        let constructor = machine.intrinsics.global("TypeError").unwrap();
        let prototype = ordinary_object(&mut machine);
        let new_target = ordinary_object(&mut machine);
        define_own(&mut machine, new_target, "prototype", prototype).unwrap();
        let id = match machine.heap[machine.runtime_slot(constructor).unwrap().unwrap()] {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => id,
            _ => panic!("native constructor"),
        };
        machine.current_builtin_id = Some(id);
        machine.current_new_target = new_target;
        let error = error_constructor(&mut machine, Value::UNDEFINED, &[], true).unwrap();
        machine.current_builtin_id = None;
        machine.current_new_target = Value::UNDEFINED;
        let BuiltinOutcome::Value(error) = error else {
            panic!("value")
        };
        assert!(machine.inherits_from_prototype(error, prototype).unwrap());
        assert!(matches!(
            descriptor(&mut machine, error, "stack"),
            Property::Accessor {
                enumerable: false,
                configurable: true,
                ..
            }
        ));
        machine
            .set_data_property(error, "stack", Value::int32(9))
            .unwrap();
        assert_eq!(
            machine.get_named_property(error, "stack").unwrap(),
            Value::int32(9)
        );
    }

    #[test]
    fn subtype_prototype_descriptors_and_stack_header_are_exact() {
        machine!(machine);
        let type_constructor = machine.intrinsics.global("TypeError").unwrap();
        let error_constructor = machine.intrinsics.global("Error").unwrap();
        let error_id = match machine.heap[machine.runtime_slot(error_constructor).unwrap().unwrap()]
        {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => id,
            _ => panic!("Error constructor is native"),
        };
        let error_prototype = machine.intrinsics.error_prototype(error_id);
        let type_prototype = machine
            .get_named_property(type_constructor, "prototype")
            .unwrap();
        assert!(
            machine
                .inherits_from_prototype(type_prototype, error_prototype)
                .unwrap()
        );
        assert!(matches!(
            descriptor(&mut machine, type_constructor, "length"),
            Property::Data {
                writable: false,
                enumerable: false,
                configurable: true,
                ..
            }
        ));
        assert!(matches!(
            descriptor(&mut machine, type_constructor, "prototype"),
            Property::Data {
                writable: false,
                enumerable: false,
                configurable: false,
                ..
            }
        ));
        let error = call_error(&mut machine, "TypeError", &[]);
        let stack = machine.get_named_property(error, "stack").unwrap();
        let stack = machine.to_string(stack).unwrap();
        assert!(stack.to_utf8_lossy().starts_with("TypeError"));
    }
}
