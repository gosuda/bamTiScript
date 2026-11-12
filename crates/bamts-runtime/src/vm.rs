use std::collections::BTreeMap;

use bamts_bytecode::EcmaString;
use bamts_native::{Decoded, Value};

use crate::external_modules::InstalledModule;
use crate::intrinsics::{self, BuiltinDef, BuiltinOutcome, BuiltinTable};
use crate::{
    EvalFailure, HeapEntry, Host, Machine, Property, PropertyKey, PropertyMap, ScriptCompileError,
    ScriptSource, ThrowOrigin,
};

pub(crate) mod async_iterators;
pub(crate) mod dynamic_import;
pub(crate) mod esm_eval;
pub(crate) mod explicit_resource;
pub(crate) mod generator_async;
pub(crate) mod import_attributes;

pub(crate) fn install<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    object_prototype: Value,
) -> InstalledModule {
    let specifier = EcmaString::encode("node:vm");
    let namespace = intrinsics::push(
        heap,
        HeapEntry::ExternalModuleNamespace {
            specifier: specifier.clone(),
        },
    );
    let script_prototype = intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        },
    );
    let script = register_constructor(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "Script",
            length: 1,
            handler: script_constructor::<H>,
        },
    );
    let run_in_this_context = register_constructor(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "runInThisContext",
            length: 2,
            handler: run_in_this_context::<H>,
        },
    );
    let run_in_new_context = register_constructor(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "runInNewContext",
            length: 3,
            handler: run_in_new_context::<H>,
        },
    );
    let run_prototype = intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        },
    );
    builtins.set_function_prototype(heap, atoms, shapes, run_in_this_context, run_prototype);
    crate::intrinsics::builtins::define_data(
        heap,
        atoms,
        shapes,
        run_prototype,
        "constructor",
        run_in_this_context,
    );
    let run_in_new_context_prototype = intrinsics::push(
        heap,
        HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(object_prototype),
            boxed_primitive: None,
            extensible: true,
        },
    );
    builtins.set_function_prototype(
        heap,
        atoms,
        shapes,
        run_in_new_context,
        run_in_new_context_prototype,
    );
    crate::intrinsics::builtins::define_data(
        heap,
        atoms,
        shapes,
        run_in_new_context_prototype,
        "constructor",
        run_in_new_context,
    );
    let script_run_in_this_context = register(
        heap,
        atoms,
        shapes,
        builtins,
        crate::intrinsics::BuiltinDef {
            name: "runInThisContext",
            length: 1,
            handler: script_run_in_this_context::<H>,
        },
    );

    builtins.set_constructor_prototype(heap, atoms, shapes, script, script_prototype);
    crate::intrinsics::builtins::define_data(
        heap,
        atoms,
        shapes,
        script_prototype,
        "constructor",
        script,
    );
    crate::intrinsics::builtins::define_data(
        heap,
        atoms,
        shapes,
        script_prototype,
        "runInThisContext",
        script_run_in_this_context,
    );

    InstalledModule {
        specifier,
        namespace,
        exports: vec![
            (EcmaString::encode("Script"), script),
            (EcmaString::encode("runInNewContext"), run_in_new_context),
            (EcmaString::encode("runInThisContext"), run_in_this_context),
        ],
        internals: BTreeMap::from([("vm.script.prototype", script_prototype)]),
    }
}

fn register<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    definition: BuiltinDef<H>,
) -> Value {
    let id = builtins.register(definition);
    let installed = builtins.get(id);
    intrinsics::native_function(heap, atoms, shapes, id, installed.name, installed.length)
}

/// Registers a function `new` can reach. Node's `runIn*Context` are plain
/// functions, so unlike `Script` they work with or without it.
fn register_constructor<H: Host>(
    heap: &mut Vec<HeapEntry>,
    atoms: &mut crate::AtomTable,
    shapes: &mut crate::ShapeTable,
    builtins: &mut BuiltinTable<H>,
    definition: BuiltinDef<H>,
) -> Value {
    let id = builtins.register_constructor(definition);
    let installed = builtins.get(id);
    intrinsics::native_function(heap, atoms, shapes, id, installed.name, installed.length)
}

fn type_error(operation: &'static str) -> EvalFailure {
    EvalFailure::Throw(ThrowOrigin::TypeError { operation })
}

#[derive(Clone, Copy)]
enum ScriptAllocation {
    Call,
    ConstructedCall,
    Object,
}

impl ScriptAllocation {
    fn wrappers(self) -> usize {
        match self {
            Self::Call => 1,
            Self::ConstructedCall | Self::Object => 2,
        }
    }
}

fn script_constructor<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if !constructing {
        return Err(type_error(
            "Class constructor Script cannot be invoked without 'new'",
        ));
    }

    let code = args.first().copied().unwrap_or(Value::UNDEFINED);
    let options = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let (code, name) = source_arguments(machine, code, options)?;
    let entry = compile_entry(machine, code, name, ScriptAllocation::Object, None)?;
    let script = machine
        .allocate(HeapEntry::Script {
            entry,
            properties: PropertyMap::default(),
            prototype: Some(script_prototype(machine)),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(BuiltinOutcome::Value(script))
}

fn run_in_this_context<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let prototype = if constructing {
        let function = machine
            .registry
            .external
            .get(&EcmaString::encode("node:vm"))
            .and_then(|module| module.exports.get(&EcmaString::encode("runInThisContext")))
            .expect("node:vm installs runInThisContext")
            .value;
        Some(machine.constructed_prototype(function)?)
    } else {
        None
    };
    let code = args.first().copied().unwrap_or(Value::UNDEFINED);
    let options = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    let (code, name) = source_arguments(machine, code, options)?;
    let allocation = if constructing {
        ScriptAllocation::ConstructedCall
    } else {
        ScriptAllocation::Call
    };
    let entry = compile_entry(machine, code, name, allocation, None)?;
    call_entry(machine, entry, prototype, None)
}

/// `runInNewContext(code, contextObject?, options?)`
///
/// Compiles `code` as a classic script and executes it with a fresh
/// `globalThis`. When `contextObject` is omitted, a fresh object is allocated
/// and becomes `globalThis` for the duration of the call. The new context still
/// shares this machine's intrinsic objects and prototype graph with the outer
/// environment, so `Object`, `Array`, `Object.prototype`, and similar builtins
/// are identical across contexts. Guest code can mutate shared objects such as
/// `Object.prototype`; this is not a separate realm and is not a security
/// boundary.
///
/// An unsupported `timeout` in `options` is rejected rather than silently
/// ignored; see `reject_unsupported_timeout`.
fn run_in_new_context<H: Host>(
    machine: &mut Machine<'_, H>,
    _this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    let prototype = if constructing {
        let function = machine.registry.external[&EcmaString::encode("node:vm")].exports
            [&EcmaString::encode("runInNewContext")]
            .value;
        Some(machine.constructed_prototype(function)?)
    } else {
        None
    };
    let context = match args.get(1).copied().unwrap_or(Value::UNDEFINED) {
        Value::UNDEFINED => machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .map_err(EvalFailure::Runtime)?,
        context if machine.is_object(context) => context,
        _ => {
            return Err(type_error(
                "The \"contextObject\" argument must be an object",
            ));
        }
    };
    let code = args.first().copied().unwrap_or(Value::UNDEFINED);
    let options = args.get(2).copied().unwrap_or(Value::UNDEFINED);
    let (code, name) = source_arguments(machine, code, options)?;
    let allocation = if constructing {
        ScriptAllocation::ConstructedCall
    } else {
        ScriptAllocation::Call
    };
    let entry = compile_entry(machine, code, name, allocation, Some(context))?;
    call_entry(machine, entry, prototype, Some(context))
}

fn script_run_in_this_context<H: Host>(
    machine: &mut Machine<'_, H>,
    this: Value,
    args: &[Value],
    constructing: bool,
) -> Result<BuiltinOutcome, EvalFailure> {
    if constructing {
        return Err(type_error(
            "Script.prototype.runInThisContext is not a constructor",
        ));
    }
    let options = args
        .first()
        .copied()
        .filter(|value| *value != Value::UNDEFINED);
    if let Some(options) = options
        && (!machine.is_object(options) || machine.is_callable(options)?)
    {
        return Err(type_error("The \"options\" argument must be an object"));
    }
    if let Some(options) = options {
        reject_unsupported_timeout(machine, options)?;
    }
    let Some(index) = machine.runtime_slot(this).map_err(EvalFailure::Runtime)? else {
        return Err(type_error(
            "Script.prototype.runInThisContext called on incompatible receiver",
        ));
    };
    let HeapEntry::Script { entry, .. } = machine.heap[index] else {
        return Err(type_error(
            "Script.prototype.runInThisContext called on incompatible receiver",
        ));
    };
    call_entry(machine, entry, None, None)
}

// The runtime has no execution-timeout enforcement point, so a caller-supplied
// `timeout` cannot be honored. Reject it loudly instead of silently dropping a
// safety-relevant option — accepting it would let callers believe guest
// execution is bounded when it is not.
fn reject_unsupported_timeout<H: Host>(
    machine: &mut Machine<'_, H>,
    options: Value,
) -> Result<(), EvalFailure> {
    let timeout = machine.get_named_property(options, "timeout")?;
    if timeout != Value::UNDEFINED {
        return Err(type_error(
            "The \"timeout\" option is not supported by this runtime",
        ));
    }
    Ok(())
}

fn source_arguments<H: Host>(
    machine: &mut Machine<'_, H>,
    code: Value,
    options: Value,
) -> Result<(EcmaString, EcmaString), EvalFailure> {
    let code = machine.to_string(code)?;
    if options == Value::UNDEFINED {
        return Ok((code, EcmaString::encode("evalmachine.<anonymous>")));
    }
    if let Some(name) = machine.string_value(options) {
        return Ok((code, name));
    }
    if !machine.is_object(options) || machine.is_callable(options)? {
        return Err(type_error("The \"options\" argument must be an object"));
    }
    reject_unsupported_timeout(machine, options)?;
    let filename = machine.get_named_property(options, "filename")?;
    if filename == Value::UNDEFINED {
        return Ok((code, EcmaString::encode("evalmachine.<anonymous>")));
    }
    let Some(name) = machine.string_value(filename) else {
        return Err(type_error("The \"filename\" option must be of type string"));
    };
    Ok((code, name))
}

fn compile_entry<H: Host>(
    machine: &mut Machine<'_, H>,
    code: EcmaString,
    name: EcmaString,
    allocation: ScriptAllocation,
    context: Option<Value>,
) -> Result<Value, EvalFailure> {
    let compiled = {
        let provider = machine
            .host
            .script_compiler()
            .ok_or_else(|| type_error("host withdrew its script compiler"))?;
        provider.compile_script(ScriptSource {
            source: code.as_units(),
            name: name.as_units(),
        })
    }
    .map_err(|error| compile_error(machine, error))?;
    let wrappers = allocation.wrappers();
    let module = machine
        .install_script_reserving(compiled, wrappers, wrappers)
        .map_err(EvalFailure::Runtime)?;
    let entry = machine
        .allocate(HeapEntry::Function {
            module,
            function: machine.module_code(module).entry(),
            captures: Vec::new(),
            context,
            properties: PropertyMap::default(),
            prototype: Some(machine.intrinsics.function_prototype),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)?;
    Ok(entry)
}

pub(crate) fn compile_error<H: Host>(
    machine: &mut Machine<'_, H>,
    error: ScriptCompileError,
) -> EvalFailure {
    let (kind, message) = match error {
        ScriptCompileError::IllFormedSource { unit_offset } => (
            "SyntaxError",
            format!("ill-formed UTF-16 source at code unit {unit_offset}"),
        ),
        ScriptCompileError::Syntax { message, .. }
        | ScriptCompileError::Unsupported { message, .. } => ("SyntaxError", message),
        ScriptCompileError::Capacity { message } => ("RangeError", message),
        ScriptCompileError::Internal { message } => ("Error", message),
    };
    let id = machine
        .intrinsics
        .builtins
        .id_named(kind)
        .expect("error constructors install before external modules");
    machine.throw_error(id, message)
}

fn script_prototype<H: Host>(machine: &Machine<'_, H>) -> Value {
    *machine
        .registry
        .external
        .get(&EcmaString::encode("node:vm"))
        .and_then(|module| module.internals.get("vm.script.prototype"))
        .expect("node:vm installs Script.prototype")
}

fn contextify_global<H: Host>(
    machine: &mut Machine<'_, H>,
    context: Value,
) -> Result<(), EvalFailure> {
    let Some(Decoded::HeapRef(marker)) = machine.vm_context_marker.decode() else {
        unreachable!("vm context marker is a private name");
    };
    let marker = PropertyKey::Private(marker.slot() - 1);
    if machine.own_descriptor(context, &marker)?.is_some() {
        return Ok(());
    }

    let global_this = PropertyKey::Named(machine.intern_str("globalThis"));
    let global = PropertyKey::Named(machine.intern_str("global"));
    machine.define_descriptor_batch(
        context,
        [
            (
                global_this,
                Property::Data {
                    value: context,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            ),
            (
                global,
                Property::Data {
                    value: context,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            ),
            (
                marker,
                Property::Data {
                    value: Value::TRUE,
                    writable: false,
                    enumerable: false,
                    configurable: false,
                },
            ),
        ],
    )?;
    // Populate the fresh context with the shared intrinsic globals so
    // runInNewContext can resolve Object, Array, etc. without falling
    // back to the outer global object. The intrinsic objects themselves
    // remain shared (same Value); only the property bindings are copied.
    // Host-only globals such as `process` and `console` are not copied
    // unless they are already present on an explicitly supplied context object.
    let intrinsic_names: Vec<EcmaString> = machine
        .intrinsics
        .globals
        .keys()
        .filter(|name| {
            !name.eq_ascii("globalThis")
                && !name.eq_ascii("global")
                && !name.eq_ascii("process")
                && !name.eq_ascii("console")
        })
        .cloned()
        .collect();
    for name in intrinsic_names {
        let key = PropertyKey::Named(machine.intern(name));
        if machine.own_descriptor(context, &key)?.is_none()
            && let Some(descriptor) = machine.own_descriptor(machine.global_object, &key)?
        {
            machine.define_descriptor(context, key, descriptor)?;
        }
    }
    Ok(())
}

fn call_entry<H: Host>(
    machine: &mut Machine<'_, H>,
    entry: Value,
    prototype: Option<Value>,
    context: Option<Value>,
) -> Result<BuiltinOutcome, EvalFailure> {
    let this_value = context.unwrap_or(machine.global_object);
    if let Some(context) = context {
        contextify_global(machine, context)?;
    }
    let previous = std::mem::replace(&mut machine.context_global, context);
    let result = machine.call_value(entry, this_value, &[]);
    machine.context_global = previous;
    let result = result?;
    if let Some(prototype) = prototype
        && !machine.is_object(result)
    {
        return machine
            .allocate_constructed_receiver_with(prototype)
            .map(BuiltinOutcome::Value)
            .map_err(EvalFailure::Runtime);
    }
    Ok(BuiltinOutcome::Value(result))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use bamts_bytecode::{
        Constant, ConstantId, Function, FunctionFlags, FunctionId, Instruction, Module, ModuleId,
        Program, ProgramModule, Register, Verified,
    };

    use super::*;
    use crate::{CompileProvider, Limits, RuntimeErrorKind};

    struct FakeCompiler {
        program: Arc<Program<Verified>>,
        sources: Vec<(Vec<u16>, Vec<u16>)>,
    }

    impl CompileProvider for FakeCompiler {
        fn compile_script(
            &mut self,
            source: ScriptSource<'_>,
        ) -> Result<Arc<Program<Verified>>, ScriptCompileError> {
            self.sources
                .push((source.source.to_vec(), source.name.to_vec()));
            Ok(self.program.clone())
        }
    }

    #[derive(Default)]
    struct ScriptHost {
        compiler: Option<FakeCompiler>,
    }

    impl Host for ScriptHost {
        fn script_compiler(&mut self) -> Option<&mut (dyn CompileProvider + 'static)> {
            self.compiler
                .as_mut()
                .map(|compiler| compiler as &mut (dyn CompileProvider + 'static))
        }
    }

    fn program_returning(value: i32) -> Program<Verified> {
        let constants = vec![
            Constant::Int32(value),
            Constant::String(EcmaString::encode("test")),
        ];
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                1,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadConst {
                        dst: Register::new(0),
                        constant: ConstantId::new(0),
                    },
                    Instruction::Return {
                        value: Register::new(0),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("test bytecode is verified");
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
        .expect("test program links")
    }

    fn program_checking_intrinsics() -> Program<Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("Array")),
            Constant::String(EcmaString::encode("prototype")),
            Constant::String(EcmaString::encode("shared_marker")),
            Constant::String(EcmaString::encode("<test>")),
            Constant::Int32(1),
        ];
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                11,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadThis {
                        dst: Register::new(0),
                    },
                    Instruction::LoadConst {
                        dst: Register::new(8),
                        constant: ConstantId::new(2),
                    },
                    Instruction::LoadConst {
                        dst: Register::new(9),
                        constant: ConstantId::new(3),
                    },
                    Instruction::LoadConst {
                        dst: Register::new(10),
                        constant: ConstantId::new(5),
                    },
                    Instruction::LoadGlobal {
                        dst: Register::new(1),
                        name: ConstantId::new(0),
                    },
                    Instruction::GetProperty {
                        dst: Register::new(2),
                        object: Register::new(1),
                        key: Register::new(8),
                    },
                    Instruction::DefineDataProperty {
                        object: Register::new(2),
                        key: Register::new(9),
                        value: Register::new(10),
                    },
                    Instruction::CreateObject {
                        dst: Register::new(5),
                    },
                    Instruction::GetProperty {
                        dst: Register::new(6),
                        object: Register::new(5),
                        key: Register::new(9),
                    },
                    Instruction::LoadGlobal {
                        dst: Register::new(3),
                        name: ConstantId::new(1),
                    },
                    Instruction::GetProperty {
                        dst: Register::new(4),
                        object: Register::new(3),
                        key: Register::new(8),
                    },
                    Instruction::CreateArray {
                        dst: Register::new(7),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(7),
                        value: Register::new(0),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(7),
                        value: Register::new(1),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(7),
                        value: Register::new(2),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(7),
                        value: Register::new(4),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(7),
                        value: Register::new(6),
                    },
                    Instruction::Return {
                        value: Register::new(7),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("test bytecode is verified");
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(4),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("test program links")
    }

    fn compiler_host() -> ScriptHost {
        ScriptHost {
            compiler: Some(FakeCompiler {
                program: Arc::new(program_returning(42)),
                sources: Vec::new(),
            }),
        }
    }

    fn vm_exports<H: Host>(machine: &Machine<'_, H>) -> (Value, Value) {
        let vm = machine
            .registry
            .external
            .get(&EcmaString::encode("node:vm"))
            .expect("node:vm is installed");
        (
            vm.exports
                .get(&EcmaString::encode("Script"))
                .expect("Script is exported")
                .value,
            vm.exports
                .get(&EcmaString::encode("runInThisContext"))
                .expect("runInThisContext is exported")
                .value,
        )
    }

    fn builtin_id<H: Host>(machine: &Machine<'_, H>, value: Value) -> crate::intrinsics::BuiltinId {
        let index = machine
            .runtime_slot(value)
            .expect("builtin value is valid")
            .expect("builtin is a runtime object");
        let HeapEntry::NativeFunction {
            callable: crate::NativeCallable::Builtin(id),
            ..
        } = &machine.heap[index]
        else {
            panic!("module export is a native function");
        };
        *id
    }

    #[test]
    fn node_vm_is_absent_without_compile_capability() {
        let program = program_returning(0);
        let mut host = ScriptHost::default();
        let machine = Machine::new(&program, &mut host, Limits::default());
        assert!(
            !machine
                .registry
                .external
                .contains_key(&EcmaString::encode("node:vm"))
        );
    }

    #[test]
    fn node_vm_exports_only_the_bounded_surface() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let (script, run, run_new) = {
            let vm = machine
                .registry
                .external
                .get(&EcmaString::encode("node:vm"))
                .expect("node:vm is installed");
            let names: Vec<_> = vm.exports.keys().cloned().collect();
            assert_eq!(
                names,
                vec![
                    EcmaString::encode("Script"),
                    EcmaString::encode("default"),
                    EcmaString::encode("runInNewContext"),
                    EcmaString::encode("runInThisContext"),
                ]
            );
            let script = vm
                .exports
                .get(&EcmaString::encode("Script"))
                .expect("Script is exported")
                .value;
            let run = vm
                .exports
                .get(&EcmaString::encode("runInThisContext"))
                .expect("runInThisContext is exported")
                .value;
            let run_new = vm
                .exports
                .get(&EcmaString::encode("runInNewContext"))
                .expect("runInNewContext is exported")
                .value;
            (script, run, run_new)
        };
        let prototype = script_prototype(&machine);
        assert_eq!(
            machine
                .get_named_property(prototype, "constructor")
                .unwrap(),
            script
        );
        let prototype_index = machine.runtime_slot(prototype).unwrap().unwrap();
        let HeapEntry::Object { properties, .. } = &machine.heap[prototype_index] else {
            unreachable!();
        };
        assert!(matches!(
            properties.get_ascii(&machine.shapes, &machine.atoms, "constructor"),
            Some(crate::Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            }) if *value == script
        ));
        let script_index = machine.runtime_slot(script).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            properties: script_properties,
            ..
        } = &machine.heap[script_index]
        else {
            unreachable!();
        };
        assert!(matches!(
            script_properties.get_ascii(&machine.shapes, &machine.atoms, "prototype"),
            Some(crate::Property::Data {
                value,
                writable: false,
                enumerable: false,
                configurable: false,
            }) if *value == prototype
        ));
        let run_index = machine.runtime_slot(run).unwrap().unwrap();
        let HeapEntry::NativeFunction {
            properties: run_properties,
            ..
        } = &machine.heap[run_index]
        else {
            unreachable!();
        };
        let Some(crate::Property::Data {
            value: run_prototype,
            writable: true,
            enumerable: false,
            configurable: false,
        }) = run_properties.get_ascii(&machine.shapes, &machine.atoms, "prototype")
        else {
            panic!("runInThisContext has an ordinary function prototype");
        };
        assert_eq!(
            machine
                .get_named_property(*run_prototype, "constructor")
                .unwrap(),
            run
        );
        assert_eq!(
            machine
                .intrinsics
                .builtins
                .get(builtin_id(&machine, script))
                .length,
            1
        );
        assert_eq!(
            machine
                .intrinsics
                .builtins
                .get(builtin_id(&machine, run))
                .length,
            2
        );
        assert_eq!(
            machine
                .intrinsics
                .builtins
                .get(builtin_id(&machine, run_new))
                .length,
            3
        );
    }

    #[test]
    fn run_in_new_context_executes_compiled_source() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let run = machine.registry.external[&EcmaString::encode("node:vm")].exports
            [&EcmaString::encode("runInNewContext")]
            .value;
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("({})")))
            .unwrap();

        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[source])
                .unwrap(),
            Value::int32(42)
        );
        assert!(matches!(
            machine.call_value(run, Value::UNDEFINED, &[source, Value::NULL]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[source, context])
                .unwrap(),
            Value::int32(42)
        );
        assert_eq!(
            machine
                .host
                .compiler
                .as_ref()
                .expect("compiler remains installed")
                .sources
                .len(),
            2
        );
        let BuiltinOutcome::Value(constructed) = machine
            .call_builtin(builtin_id(&machine, run), Value::UNDEFINED, &[source], true)
            .unwrap()
        else {
            panic!("constructed runInNewContext returns a value");
        };
        assert!(machine.is_object(constructed));
        assert_ne!(constructed, Value::int32(42));
        assert_eq!(
            machine
                .host
                .compiler
                .as_ref()
                .expect("compiler remains installed")
                .sources
                .len(),
            3
        );
    }

    #[test]
    fn contextification_runs_once_and_preserves_alias_mutations() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();

        contextify_global(&mut machine, context).unwrap();
        machine
            .set_data_property(context, "globalThis", Value::int32(7))
            .unwrap();
        let global_key = PropertyKey::Named(machine.intern_str("global"));
        assert!(machine.internal_delete(context, &global_key).unwrap());
        contextify_global(&mut machine, context).unwrap();

        assert_eq!(
            machine.get_named_property(context, "globalThis").unwrap(),
            Value::int32(7)
        );
        let global_this_key = PropertyKey::Named(machine.intern_str("globalThis"));
        assert!(matches!(
            machine
                .own_descriptor(
                    context,
                    &global_this_key,
                )
                .unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: false,
                configurable: true,
            }) if value == Value::int32(7)
        ));
        let global_key = PropertyKey::Named(machine.intern_str("global"));
        assert!(
            machine
                .own_descriptor(context, &global_key)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn failed_contextification_restores_every_descriptor() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let global_this = PropertyKey::Named(machine.intern_str("globalThis"));
        let global = PropertyKey::Named(machine.intern_str("global"));
        machine
            .define_descriptor(
                context,
                global_this.clone(),
                Property::Data {
                    value: Value::int32(7),
                    writable: true,
                    enumerable: true,
                    configurable: true,
                },
            )
            .unwrap();
        machine
            .define_descriptor(
                context,
                global.clone(),
                Property::Data {
                    value: Value::int32(8),
                    writable: false,
                    enumerable: true,
                    configurable: false,
                },
            )
            .unwrap();

        assert!(matches!(
            contextify_global(&mut machine, context),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.own_descriptor(context, &global_this).unwrap(),
            Some(Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            }) if value == Value::int32(7)
        ));
        assert!(matches!(
            machine.own_descriptor(context, &global).unwrap(),
            Some(Property::Data {
                value,
                writable: false,
                enumerable: true,
                configurable: false,
            }) if value == Value::int32(8)
        ));
        let Some(Decoded::HeapRef(marker)) = machine.vm_context_marker.decode() else {
            unreachable!();
        };
        assert!(
            machine
                .own_descriptor(context, &PropertyKey::Private(marker.slot() - 1))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn heap_limit_failure_does_not_partially_contextify() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let bytes = machine.heap_bytes;
        machine.limits.max_heap_bytes = bytes;

        assert!(matches!(
            contextify_global(&mut machine, context),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        assert_eq!(machine.heap_bytes, bytes);
        for key in [
            PropertyKey::Named(machine.intern_str("globalThis")),
            PropertyKey::Named(machine.intern_str("global")),
        ] {
            assert!(machine.own_descriptor(context, &key).unwrap().is_none());
        }
        let Some(Decoded::HeapRef(marker)) = machine.vm_context_marker.decode() else {
            unreachable!();
        };
        assert!(
            machine
                .own_descriptor(context, &PropertyKey::Private(marker.slot() - 1))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn run_in_new_context_shares_intrinsics_and_prototypes() {
        let program = program_returning(0);
        let mut host = ScriptHost {
            compiler: Some(FakeCompiler {
                program: Arc::new(program_checking_intrinsics()),
                sources: Vec::new(),
            }),
        };
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let run = machine
            .registry
            .external
            .get(&EcmaString::encode("node:vm"))
            .expect("node:vm is installed")
            .exports
            .get(&EcmaString::encode("runInNewContext"))
            .expect("runInNewContext is exported")
            .value;
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("intrinsics check")))
            .unwrap();

        let first = machine
            .call_value(run, Value::UNDEFINED, &[source])
            .expect("first runInNewContext call succeeds");
        let outer_global_this = machine
            .intrinsics
            .global("globalThis")
            .expect("outer globalThis exists");
        let outer_object = machine.intrinsics.global("Object").expect("Object exists");
        let outer_object_prototype = machine.intrinsics.object_prototype;
        let outer_array_prototype = machine.intrinsics.array_prototype;

        assert_ne!(
            machine.get_named_property(first, "0").unwrap(),
            outer_global_this,
            "runInNewContext provides a fresh globalThis"
        );
        assert_eq!(
            machine.get_named_property(first, "1").unwrap(),
            outer_object,
            "Object is shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(first, "2").unwrap(),
            outer_object_prototype,
            "Object.prototype is shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(first, "3").unwrap(),
            outer_array_prototype,
            "Array.prototype is shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(first, "4").unwrap(),
            Value::int32(1),
            "mutations to the shared Object.prototype are visible to new objects"
        );

        let second = machine
            .call_value(run, Value::UNDEFINED, &[source])
            .expect("second runInNewContext call succeeds");
        assert_ne!(
            machine.get_named_property(second, "0").unwrap(),
            outer_global_this,
            "each new context has a fresh globalThis"
        );
        assert_ne!(
            machine.get_named_property(second, "0").unwrap(),
            machine.get_named_property(first, "0").unwrap(),
            "each new context has a distinct globalThis"
        );
        assert_eq!(
            machine.get_named_property(second, "1").unwrap(),
            outer_object,
            "Object is still shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(second, "2").unwrap(),
            outer_object_prototype,
            "Object.prototype is still shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(second, "3").unwrap(),
            outer_array_prototype,
            "Array.prototype is still shared across contexts"
        );
        assert_eq!(
            machine.get_named_property(second, "4").unwrap(),
            Value::int32(1),
            "mutations to the shared prototype survive into a new context"
        );
    }

    /// Program that checks global isolation: TypeOfGlobal on host-only
    /// names (should be "undefined") and on a standard intrinsic (should be
    /// "function"), returning [typeof hostOnly, typeof process, typeof console, typeof Object].
    fn program_checking_global_isolation() -> Program<Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("hostOnly")),
            Constant::String(EcmaString::encode("process")),
            Constant::String(EcmaString::encode("console")),
            Constant::String(EcmaString::encode("Object")),
            Constant::String(EcmaString::encode("<isolation>")),
        ];
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                5,
                FunctionFlags::default(),
                vec![
                    Instruction::TypeOfGlobal {
                        dst: Register::new(0),
                        name: ConstantId::new(0),
                    },
                    Instruction::TypeOfGlobal {
                        dst: Register::new(1),
                        name: ConstantId::new(1),
                    },
                    Instruction::TypeOfGlobal {
                        dst: Register::new(2),
                        name: ConstantId::new(2),
                    },
                    Instruction::TypeOfGlobal {
                        dst: Register::new(3),
                        name: ConstantId::new(3),
                    },
                    Instruction::CreateArray {
                        dst: Register::new(4),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(4),
                        value: Register::new(0),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(4),
                        value: Register::new(1),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(4),
                        value: Register::new(2),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(4),
                        value: Register::new(3),
                    },
                    Instruction::Return {
                        value: Register::new(4),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("test bytecode is verified");
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(4),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("test program links")
    }

    /// Program that returns the values of explicitly-supplied `process`
    /// and `console` globals: [process, console].
    fn program_returning_supplied_globals() -> Program<Verified> {
        let constants = vec![
            Constant::String(EcmaString::encode("process")),
            Constant::String(EcmaString::encode("console")),
            Constant::String(EcmaString::encode("<explicit>")),
        ];
        let code = Module::new(
            constants,
            vec![Function::new(
                None,
                0,
                0,
                3,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadGlobal {
                        dst: Register::new(0),
                        name: ConstantId::new(0),
                    },
                    Instruction::LoadGlobal {
                        dst: Register::new(1),
                        name: ConstantId::new(1),
                    },
                    Instruction::CreateArray {
                        dst: Register::new(2),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(2),
                        value: Register::new(0),
                    },
                    Instruction::ArrayPush {
                        array: Register::new(2),
                        value: Register::new(1),
                    },
                    Instruction::Return {
                        value: Register::new(2),
                    },
                ],
                Vec::new(),
            )],
            FunctionId::new(0),
        )
        .verify()
        .expect("test bytecode is verified");
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(2),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("test program links")
    }

    #[test]
    fn run_in_new_context_does_not_leak_host_only_globals() {
        let program = program_returning(0);
        let mut host = ScriptHost {
            compiler: Some(FakeCompiler {
                program: Arc::new(program_checking_global_isolation()),
                sources: Vec::new(),
            }),
        };
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();

        // Install a host-only global on the outer global object.
        machine.test_set_global("hostOnly", Value::int32(42));
        assert_eq!(
            machine.test_global("hostOnly"),
            Some(Value::int32(42)),
            "host-only global is visible in the main context"
        );

        let run = machine
            .registry
            .external
            .get(&EcmaString::encode("node:vm"))
            .expect("node:vm is installed")
            .exports
            .get(&EcmaString::encode("runInNewContext"))
            .expect("runInNewContext is exported")
            .value;
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("isolation check")))
            .unwrap();

        let result = machine
            .call_value(run, Value::UNDEFINED, &[source])
            .expect("runInNewContext call succeeds");

        // The host-only globals must NOT leak into the new context.
        let typeof_host_only = machine.get_named_property(result, "0").unwrap();
        assert!(
            machine
                .string_value(typeof_host_only)
                .is_some_and(|text| text.eq_ascii("undefined")),
            "host-only global is absent inside runInNewContext"
        );
        let typeof_process = machine.get_named_property(result, "1").unwrap();
        assert!(
            machine
                .string_value(typeof_process)
                .is_some_and(|text| text.eq_ascii("undefined")),
            "process is absent inside runInNewContext"
        );
        let typeof_console = machine.get_named_property(result, "2").unwrap();
        assert!(
            machine
                .string_value(typeof_console)
                .is_some_and(|text| text.eq_ascii("undefined")),
            "console is absent inside runInNewContext"
        );
        // Standard intrinsics must remain usable in the new context.
        let typeof_object = machine.get_named_property(result, "3").unwrap();
        assert!(
            machine
                .string_value(typeof_object)
                .is_some_and(|text| text.eq_ascii("function")),
            "standard intrinsics work inside runInNewContext"
        );

        // The main-context lookup is unchanged after the call.
        assert_eq!(
            machine.test_global("hostOnly"),
            Some(Value::int32(42)),
            "main-context lookup is unchanged"
        );
    }

    #[test]
    fn run_in_new_context_keeps_explicit_context_properties() {
        let program = program_returning(0);
        let mut host = ScriptHost {
            compiler: Some(FakeCompiler {
                program: Arc::new(program_returning_supplied_globals()),
                sources: Vec::new(),
            }),
        };
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();

        let run = machine
            .registry
            .external
            .get(&EcmaString::encode("node:vm"))
            .expect("node:vm is installed")
            .exports
            .get(&EcmaString::encode("runInNewContext"))
            .expect("runInNewContext is exported")
            .value;
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode(
                "explicit context check",
            )))
            .unwrap();

        // Allocate a context object and explicitly provide `process` and `console`.
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        machine
            .set_data_property(context, "process", Value::int32(123))
            .unwrap();
        machine
            .set_data_property(context, "console", Value::int32(456))
            .unwrap();

        let result = machine
            .call_value(run, Value::UNDEFINED, &[source, context])
            .expect("runInNewContext call succeeds");

        assert_eq!(
            machine.get_named_property(result, "0").unwrap(),
            Value::int32(123),
            "explicit process property is visible inside runInNewContext"
        );
        assert_eq!(
            machine.get_named_property(result, "1").unwrap(),
            Value::int32(456),
            "explicit console property is visible inside runInNewContext"
        );
    }

    #[test]
    fn script_constructs_without_execution_and_runs_via_continuation() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (script_constructor, _) = vm_exports(&machine);
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .expect("source allocation succeeds");
        let script_constructor_id = builtin_id(&machine, script_constructor);
        let script = match machine
            .call_builtin(script_constructor_id, Value::UNDEFINED, &[source], true)
            .expect("construction succeeds")
        {
            BuiltinOutcome::Value(script) => script,
            BuiltinOutcome::Call { .. }
            | BuiltinOutcome::GeneratorResume { .. }
            | BuiltinOutcome::AsyncGeneratorResume { .. } => {
                panic!("Script construction must not execute")
            }
        };
        let run = machine
            .get_named_property(script, "runInThisContext")
            .expect("Script prototype method is readable");
        assert_eq!(
            machine.call_value(run, script, &[]).unwrap(),
            Value::int32(42)
        );
        assert!(matches!(
            machine.call_value(run, script, &[Value::NULL]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.call_value(run, script, &[run]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.call_value(run, script, &[source]),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.call_builtin(
                script_constructor_id,
                Value::UNDEFINED,
                &[source, run],
                true,
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        assert!(matches!(
            machine.call_builtin(builtin_id(&machine, run), script, &[], true),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { .. }))
        ));
        let compiler = machine
            .host
            .compiler
            .as_ref()
            .expect("compiler remains installed");
        assert_eq!(compiler.sources.len(), 1);
        assert_eq!(
            compiler.sources[0].0,
            "ignored".encode_utf16().collect::<Vec<_>>()
        );
        assert_eq!(
            compiler.sources[0].1,
            "evalmachine.<anonymous>".encode_utf16().collect::<Vec<_>>()
        );
    }

    #[test]
    fn code_is_to_string_coerced_but_options_and_filename_are_typed() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (_, run) = vm_exports(&machine);
        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[Value::int32(1)])
                .unwrap(),
            Value::int32(42)
        );
        let compiler = machine
            .host
            .compiler
            .as_ref()
            .expect("compiler remains installed");
        assert_eq!(
            compiler.sources[0].0,
            "1".encode_utf16().collect::<Vec<_>>()
        );
        let filename = machine
            .allocate(HeapEntry::String(EcmaString::encode("custom.js")))
            .unwrap();
        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[Value::int32(1), filename])
                .unwrap(),
            Value::int32(42)
        );
        assert_eq!(
            machine.host.compiler.as_ref().unwrap().sources[1].1,
            "custom.js".encode_utf16().collect::<Vec<_>>()
        );
        let error = machine
            .call_value(run, Value::UNDEFINED, &[Value::int32(1), run])
            .expect_err("callable options are rejected");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));
        let error = machine
            .call_value(run, Value::UNDEFINED, &[Value::int32(1), Value::NULL])
            .expect_err("null options are rejected");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));
        let options = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .expect("options allocation succeeds");
        machine
            .set_data_property(options, "filename", Value::NULL)
            .expect("options property is writable");
        let error = machine
            .call_value(run, Value::UNDEFINED, &[Value::int32(1), options])
            .expect_err("non-string filename is rejected");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));
    }

    #[test]
    fn constructed_run_preflight_does_not_retain_failed_installation() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (_, run) = vm_exports(&machine);
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .unwrap();
        let used_slots = machine.heap.len() - machine.intrinsic_slots;
        machine.limits.max_heap_slots = used_slots + 1;
        let before = (
            machine.dynamic.len(),
            machine.registry.modules.len(),
            machine.heap.len(),
            machine.heap_bytes,
        );

        let error = machine
            .call_builtin(builtin_id(&machine, run), Value::UNDEFINED, &[source], true)
            .expect_err("entry and fallback receiver exceed the slot budget");

        assert!(matches!(
            error,
            EvalFailure::Runtime(RuntimeErrorKind::HeapSlotLimitExceeded { .. })
        ));
        assert_eq!(
            (
                machine.dynamic.len(),
                machine.registry.modules.len(),
                machine.heap.len(),
                machine.heap_bytes,
            ),
            before
        );
    }

    #[test]
    fn script_wrapper_preflight_does_not_retain_failed_installation() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (script_constructor, _) = vm_exports(&machine);
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .unwrap();
        let used_slots = machine.heap.len() - machine.intrinsic_slots;
        machine.limits.max_heap_slots = used_slots + 1;
        let before = (
            machine.dynamic.len(),
            machine.registry.modules.len(),
            machine.heap.len(),
            machine.heap_bytes,
        );

        let error = machine
            .call_builtin(
                builtin_id(&machine, script_constructor),
                Value::UNDEFINED,
                &[source],
                true,
            )
            .expect_err("Script wrappers exceed the remaining slot budget");

        assert!(matches!(
            error,
            EvalFailure::Runtime(RuntimeErrorKind::HeapSlotLimitExceeded { .. })
        ));
        assert_eq!(
            (
                machine.dynamic.len(),
                machine.registry.modules.len(),
                machine.heap.len(),
                machine.heap_bytes,
            ),
            before
        );
    }

    #[test]
    fn script_wrapper_byte_preflight_does_not_retain_failed_installation() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (script_constructor, _) = vm_exports(&machine);
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .unwrap();
        let script_bytes = Machine::<ScriptHost>::script_heap_cost(
            &machine.host.compiler.as_ref().unwrap().program,
        );
        machine.limits.max_heap_bytes = machine.heap_bytes + script_bytes + 1;
        let before = (
            machine.dynamic.len(),
            machine.registry.modules.len(),
            machine.heap.len(),
            machine.heap_bytes,
        );

        let error = machine
            .call_builtin(
                builtin_id(&machine, script_constructor),
                Value::UNDEFINED,
                &[source],
                true,
            )
            .expect_err("Script wrappers exceed the remaining byte budget");

        assert!(matches!(
            error,
            EvalFailure::Runtime(RuntimeErrorKind::HeapByteLimitExceeded { .. })
        ));
        assert_eq!(
            (
                machine.dynamic.len(),
                machine.registry.modules.len(),
                machine.heap.len(),
                machine.heap_bytes,
            ),
            before
        );
    }

    #[test]
    fn script_receiver_cannot_be_forged() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (script_constructor, _) = vm_exports(&machine);
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .expect("source allocation succeeds");
        let script_constructor_id = builtin_id(&machine, script_constructor);
        let script = match machine
            .call_builtin(script_constructor_id, Value::UNDEFINED, &[source], true)
            .unwrap()
        {
            BuiltinOutcome::Value(script) => script,
            BuiltinOutcome::Call { .. }
            | BuiltinOutcome::GeneratorResume { .. }
            | BuiltinOutcome::AsyncGeneratorResume { .. } => unreachable!(),
        };
        let run = machine
            .get_named_property(script, "runInThisContext")
            .unwrap();
        let error = machine
            .call_value(run, Value::UNDEFINED, &[])
            .expect_err("foreign receiver is rejected");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));
        let index = machine.runtime_slot(script).unwrap().unwrap();
        let HeapEntry::Script { properties, .. } = &machine.heap[index] else {
            unreachable!();
        };
        assert_eq!(properties.iter(&machine.shapes).count(), 0);
    }

    fn options_with_timeout<H: Host>(machine: &mut Machine<'_, H>, timeout: Value) -> Value {
        let options = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .expect("options allocation succeeds");
        machine
            .set_data_property(options, "timeout", timeout)
            .expect("timeout property is writable");
        options
    }

    #[test]
    fn timeout_option_is_rejected_not_silently_dropped() {
        let program = program_returning(0);
        let mut host = compiler_host();
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        machine.instantiate_modules().unwrap();
        let (script_constructor, run) = vm_exports(&machine);
        let run_new = machine.registry.external[&EcmaString::encode("node:vm")].exports
            [&EcmaString::encode("runInNewContext")]
            .value;
        let source = machine
            .allocate(HeapEntry::String(EcmaString::encode("ignored")))
            .unwrap();

        // Script.prototype.runInThisContext rejects a timeout it cannot honor.
        let script = match machine
            .call_builtin(
                builtin_id(&machine, script_constructor),
                Value::UNDEFINED,
                &[source],
                true,
            )
            .unwrap()
        {
            BuiltinOutcome::Value(script) => script,
            _ => unreachable!(),
        };
        let script_run = machine
            .get_named_property(script, "runInThisContext")
            .unwrap();
        let timeout_opts = options_with_timeout(&mut machine, Value::int32(50));
        let error = machine
            .call_value(script_run, script, &[timeout_opts])
            .expect_err("timeout must be rejected, not silently dropped");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));

        // runInThisContext(code, { timeout }) rejects.
        let timeout_opts = options_with_timeout(&mut machine, Value::int32(50));
        let error = machine
            .call_value(run, Value::UNDEFINED, &[source, timeout_opts])
            .expect_err("timeout must be rejected, not silently dropped");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));

        // runInNewContext(code, ctx, { timeout }) rejects.
        let context = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        let timeout_opts = options_with_timeout(&mut machine, Value::int32(50));
        let error = machine
            .call_value(run_new, Value::UNDEFINED, &[source, context, timeout_opts])
            .expect_err("timeout must be rejected, not silently dropped");
        assert!(matches!(
            error,
            EvalFailure::Throw(ThrowOrigin::TypeError { .. })
        ));

        // An options object without timeout still runs (happy path intact).
        let plain_options = machine
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[source, plain_options])
                .unwrap(),
            Value::int32(42)
        );

        // `timeout: undefined` is accepted — absence is not a request to bound.
        let absent_timeout_opts = options_with_timeout(&mut machine, Value::UNDEFINED);
        assert_eq!(
            machine
                .call_value(run, Value::UNDEFINED, &[source, absent_timeout_opts])
                .unwrap(),
            Value::int32(42)
        );
    }
}
