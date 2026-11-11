//! The `Function` constructor global (ECMA-262 19.2).
//!
//! The object installs unconditionally: test262 harness code and ordinary
//! guest code read `Function.prototype` for `call`/`bind` plumbing without
//! ever synthesizing a function, so an absent `Function` global fails every
//! such script at load time with an unbound-global ReferenceError. Dynamic
//! `Function(...)` synthesis additionally requires the host to provide a
//! script compiler; without one the constructor throws a controlled
//! `TypeError` at the call instead of being absent, keeping the failure at
//! the one place that needs dynamic compilation.

use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::Value;

use super::{
    define_data, define_frozen_data, define_to_string_tag, heap_index, install_constructor_function,
};
use crate::intrinsics::{
    BuiltinDef, BuiltinHandler, BuiltinOutcome, BuiltinTable, native_function,
};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, ScriptSource,
    ThrowOrigin,
};

pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    globals: &mut BTreeMap<EcmaString, Value>,
    builtins: &mut BuiltinTable<H>,
    script_compiler: bool,
) {
    let prototype = builtins.function_prototype();
    let constructor = install_constructor_function(
        heap,
        atoms,
        builtins,
        "Function",
        1,
        function_constructor::<H> as BuiltinHandler<H>,
    );
    define_frozen_data(heap, atoms, constructor, "prototype", prototype);
    define_data(heap, atoms, prototype, "constructor", constructor);
    globals.insert(EcmaString::encode("Function"), constructor);
    let generator_prototype = builtins.generator_prototype();
    let async_generator_prototype = builtins.async_generator_prototype();
    let tag = builtins.symbol_to_string_tag();
    define_to_string_tag(heap, generator_prototype, tag, "Generator");
    define_to_string_tag(heap, async_generator_prototype, tag, "AsyncGenerator");
    let generator = install_function_kind(
        heap,
        atoms,
        builtins,
        "GeneratorFunction",
        generator_function_constructor::<H>,
        constructor,
        Some(generator_prototype),
    );
    let asynchronous = install_function_kind(
        heap,
        atoms,
        builtins,
        "AsyncFunction",
        async_function_constructor::<H>,
        constructor,
        None,
    );
    let async_generator = install_function_kind(
        heap,
        atoms,
        builtins,
        "AsyncGeneratorFunction",
        async_generator_function_constructor::<H>,
        constructor,
        Some(async_generator_prototype),
    );
    builtins.set_function_kind_prototypes(generator, asynchronous, async_generator);
    if script_compiler {
        let id = builtins.register(BuiltinDef {
            name: "eval",
            length: 1,
            handler: eval::<H>,
        });
        let function = native_function(heap, atoms, id, "eval", 1);
        globals.insert(EcmaString::encode("eval"), function);
    }
}

/// A read-only link between function-kind intrinsics.
fn define_link(
    heap: &mut [HeapEntry],
    atoms: &mut crate::AtomTable,
    object: Value,
    name: &str,
    value: Value,
) {
    let HeapEntry::Object { properties, .. } = &mut heap[heap_index(object)] else {
        panic!("function kind intrinsics are ordinary objects")
    };
    properties.insert(
        PropertyKey::Named(atoms.intern_str(name)),
        Property::Data {
            value,
            writable: false,
            enumerable: false,
            configurable: true,
        },
    );
}

/// Installs one of the hidden kinds of function constructor and returns the
/// prototype its closures inherit from. Neither is reachable from a global:
/// they are found through `Object.getPrototypeOf(function* () {})`.
fn install_function_kind<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    builtins: &mut BuiltinTable<H>,
    name: &'static str,
    handler: BuiltinHandler<H>,
    function_constructor: Value,
    instance_prototype: Option<Value>,
) -> Value {
    let prototype = crate::intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(builtins.function_prototype()),
            extensible: true,
            boxed_primitive: None,
        },
    );
    let constructor = install_constructor_function(heap, atoms, builtins, name, 1, handler);
    let HeapEntry::NativeFunction {
        prototype: parent, ..
    } = &mut heap[heap_index(constructor)]
    else {
        panic!("function kind constructor is a native function");
    };
    *parent = Some(function_constructor);
    define_frozen_data(heap, atoms, constructor, "prototype", prototype);
    define_link(heap, atoms, prototype, "constructor", constructor);
    define_to_string_tag(heap, prototype, builtins.symbol_to_string_tag(), name);
    if let Some(instance_prototype) = instance_prototype {
        define_link(heap, atoms, prototype, "prototype", instance_prototype);
        define_link(heap, atoms, instance_prototype, "constructor", prototype);
    }
    prototype
}

/// `eval(x)` as an indirect call: the source runs in the global scope, as a
/// classic script, and yields its completion value. Anything but a string comes
/// back unchanged. A host without a script compiler has no `eval` at all, so
/// the name reads as undeclared there rather than failing when called.
fn eval<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error("eval is not a constructor"));
    }
    let source = args.first().copied().unwrap_or(Value::UNDEFINED);
    match machine.string_value(source) {
        Some(text) => run_script(
            machine,
            &text,
            "eval",
            "eval: this host provides no script compiler",
        ),
        None => Ok(BuiltinOutcome::Value(source)),
    }
}

/// Compiles `source` as a classic script, runs it against the global object,
/// and returns its completion value.
fn run_script<H: Host>(
    machine: &mut Machine<'_, H>,
    source: &EcmaString,
    name: &str,
    no_compiler: &'static str,
) -> Result<BuiltinOutcome, EvalFailure> {
    let name = EcmaString::encode(name);
    let compiled = {
        let provider = machine
            .host
            .script_compiler()
            .ok_or_else(|| type_error(no_compiler))?;
        provider.compile_script(ScriptSource {
            source: source.as_units(),
            name: name.as_units(),
        })
    }
    .map_err(|error| crate::vm::compile_error(machine, error))?;
    let module = machine
        .install_script_reserving(compiled, 1, 1)
        .map_err(EvalFailure::Runtime)?;
    let entry = machine
        .allocate(HeapEntry::Function {
            module,
            function: machine.module_code(module).entry(),
            captures: Vec::new(),
            context: None,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    let previous = machine.context_global.take();
    let result = machine.call_value(entry, machine.global_object, &[]);
    machine.context_global = previous;
    result.map(BuiltinOutcome::Value)
}

/// `Function(p1, ..., pn, body)` / `new Function(p1, ..., pn, body)`.
fn function_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    create_dynamic_function(machine, args, "function")
}

fn generator_function_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    create_dynamic_function(machine, args, "function*")
}

fn async_function_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    create_dynamic_function(machine, args, "async function")
}

fn async_generator_function_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    _constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    create_dynamic_function(machine, args, "async function*")
}

/// The arguments synthesize into an `anonymous` function expression compiled
/// as a classic script; classic scripts return their completion value, so the
/// entry's result is the new function itself.
fn create_dynamic_function<H: Host>(
    machine: &mut Machine<'_, H>,
    args: &[Value],
    keyword: &str,
) -> Result<BuiltinOutcome, EvalFailure> {
    let (parameter_source, body_source) = match args.split_last() {
        None => (String::new(), String::new()),
        Some((body, parameters)) => {
            let mut names = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let text = machine.coerce_string_observable(*parameter)?;
                names.push(String::from_utf16_lossy(text.as_units()));
            }
            let body_text = machine.coerce_string_observable(*body)?;
            (
                names.join(","),
                String::from_utf16_lossy(body_text.as_units()),
            )
        }
    };
    // Line offsets inside the body must match the spec's synthesis, so the
    // body starts on its own source line.
    let source = format!("({keyword} anonymous({parameter_source}\n)\n{{\n{body_source}\n}})");
    run_script(
        machine,
        &EcmaString::encode(&source),
        "Function constructor",
        "Function: this host provides no script compiler",
    )
}

fn type_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::TypeError { operation })
}

#[cfg(test)]
mod tests {
    use bamts_bytecode::EcmaString;
    use bamts_native::{Decoded, Value};

    use super::super::test_support::{TestHost, blank_program};
    use crate::{EvalFailure, HeapEntry, Limits, Machine, Property, PropertyKey};

    #[test]
    fn function_global_installs_with_spec_identity() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let function = machine
            .intrinsics
            .global("Function")
            .expect("Function global installs");
        let name = machine
            .get_named_property(function, "name")
            .expect("Function has a name");
        assert!(
            machine
                .to_string(name)
                .expect("name is a string")
                .eq_ascii("Function"),
            "Function.name is \"Function\""
        );
        let length = machine
            .get_named_property(function, "length")
            .expect("Function has a length");
        assert!(
            matches!(length.decode(), Some(Decoded::Int32(1))),
            "Function.length is 1"
        );
        let prototype = machine
            .get_named_property(function, "prototype")
            .expect("Function has a prototype");
        assert_eq!(
            prototype, machine.intrinsics.function_prototype,
            "Function.prototype is %FunctionPrototype%"
        );
        let constructor = machine
            .get_named_property(prototype, "constructor")
            .expect("Function.prototype has a constructor");
        assert_eq!(
            constructor, function,
            "Function.prototype.constructor is Function"
        );
    }

    #[test]
    fn function_prototype_property_is_frozen_and_non_enumerable() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let function = machine
            .intrinsics
            .global("Function")
            .expect("Function global installs");
        let key = PropertyKey::Named(machine.intern_str("prototype"));
        let Some(Property::Data {
            value: _,
            writable,
            enumerable,
            configurable,
        }) = machine
            .own_descriptor(function, &key)
            .expect("Function has an own prototype property")
        else {
            panic!("prototype is a data property");
        };
        assert!(!writable, "Function.prototype is not writable");
        assert!(!enumerable, "Function.prototype is not enumerable");
        assert!(!configurable, "Function.prototype is not configurable");
    }

    #[test]
    fn dynamic_function_without_a_provider_throws_a_controlled_type_error() {
        let module = blank_program("<test>");
        let mut host = TestHost;
        let mut machine = Machine::new(&module, &mut host, Limits::default());
        let function = machine
            .intrinsics
            .global("Function")
            .expect("Function global installs");
        let argument = machine
            .allocate(HeapEntry::String(EcmaString::encode("return 1")))
            .expect("string allocates");
        let failure = machine
            .call_value(function, Value::UNDEFINED, &[argument])
            .expect_err("no-provider synthesis fails");
        match failure {
            EvalFailure::Throw(origin) => {
                assert!(
                    matches!(origin, crate::ThrowOrigin::TypeError { .. }),
                    "the no-provider path reports a TypeError, not a crash"
                );
            }
            other => panic!("expected a throw completion, got {other:?}"),
        }
    }
}
