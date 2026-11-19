    use std::cell::{Cell, RefCell};
    use std::sync::Arc;

    use bamts_bytecode::{
        AccessorKind, BinaryOp, Binding, BindingId, BindingKind, Constant, ConstantId,
        DescriptorSlot, DisposeHint, Edge, EdgeId, EdgeKind, EdgeTarget, ExceptionHandler, Export,
        ExportSource, Function, FunctionFlags, FunctionId, Instruction, IteratorKind, Module,
        ModuleId, Pc, Program, ProgramModule, Register, Verified,
    };
    use bamts_native::{
        AbiError, Completion, CompletionTag, HELPER_COUNT, HelperCall, HelperResult,
        NativeEntryTable, NativeFrame, NativeHelper, NativeOps, ShadowFrame, Value,
    };

    use crate::intrinsics::{BuiltinDef, BuiltinHandler, BuiltinOutcome, native_function};
    use crate::vm::generator_async::GeneratorCompletion;
    use crate::{
        ArrayElementKind, EvalFailure, GeneratorState, HeapEntry, Host, Limits, Machine, Property,
        PropertyKey, PropertyMap, RuntimeError, RuntimeErrorKind, ThrowOrigin,
    };

    use super::EcmaString;
    use super::{
        Activation, Backend, InvokeOutcome, NativeEngine, NativeError, PendingThrow,
        run_linked_program,
    };

    fn reg(raw: u32) -> Register {
        Register::new(raw)
    }

    fn pc(raw: u32) -> Pc {
        Pc::new(raw)
    }

    fn cid(raw: u32) -> bamts_bytecode::ConstantId {
        bamts_bytecode::ConstantId::new(raw)
    }

    fn test_target() -> crate::RuntimeFunction {
        crate::RuntimeFunction {
            module: ModuleId::new(0),
            function: FunctionId::new(0),
        }
    }

    fn entry_function(register_count: u32, code: Vec<Instruction>) -> Function {
        Function::new(
            None,
            0,
            0,
            register_count,
            FunctionFlags::default(),
            code,
            Vec::new(),
        )
    }

    fn receiver_sum_function() -> Function {
        module_function(
            0,
            5,
            vec![
                Instruction::LoadThis { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(1),
                },
                Instruction::GetProperty {
                    dst: reg(2),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::LoadArguments { dst: reg(3) },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(2),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(3),
                    key: reg(1),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::Add,
                    left: reg(2),
                    right: reg(4),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(3),
                },
                Instruction::GetProperty {
                    dst: reg(4),
                    object: reg(3),
                    key: reg(1),
                },
                Instruction::Binary {
                    dst: reg(2),
                    op: BinaryOp::Add,
                    left: reg(2),
                    right: reg(4),
                },
                Instruction::Return { value: reg(2) },
            ],
        )
    }

    fn verified(constants: Vec<Constant>, functions: Vec<Function>) -> Module<Verified> {
        Module::new(constants, functions, FunctionId::new(0))
            .verify()
            .expect("module verifies")
    }

    fn module_function(captures: u32, registers: u32, code: Vec<Instruction>) -> Function {
        Function::new(
            None,
            captures,
            0,
            registers,
            FunctionFlags::default(),
            code,
            Vec::new(),
        )
    }

    fn module_constructor(
        captures: u32,
        parameters: u32,
        registers: u32,
        code: Vec<Instruction>,
    ) -> Function {
        Function::new(
            None,
            captures,
            parameters,
            registers,
            FunctionFlags {
                is_constructable: true,
                ..FunctionFlags::default()
            },
            code,
            Vec::new(),
        )
    }

    fn program_module(
        name: &str,
        mut constants: Vec<Constant>,
        functions: Vec<Function>,
        edges: Vec<Edge>,
        bindings: Vec<Binding>,
        exports: Vec<Export>,
    ) -> ProgramModule<Verified> {
        constants.insert(0, Constant::String(EcmaString::encode(name)));
        ProgramModule {
            name: cid(0),
            code: Module::new(constants, functions, FunctionId::new(0))
                .verify()
                .expect("module fixture verifies"),
            edges,
            bindings,
            exports,
        }
    }

    fn linked(modules: Vec<ProgramModule<Verified>>, entry: u32) -> Program<Verified> {
        Program::link(modules, ModuleId::new(entry)).expect("module fixture links")
    }

    fn dynamic_cycle_program() -> Program<Verified> {
        let root = program_module(
            "root",
            vec![Constant::String(EcmaString::encode("./target"))],
            vec![entry_function(
                3,
                vec![
                    Instruction::Import {
                        dst: reg(0),
                        specifier: cid(1),
                    },
                    Instruction::Import {
                        dst: reg(1),
                        specifier: cid(1),
                    },
                    Instruction::Binary {
                        dst: reg(2),
                        op: BinaryOp::StrictEqual,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
            )],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Dynamic,
            }],
            Vec::new(),
            Vec::new(),
        );
        let target = program_module(
            "target",
            vec![Constant::String(EcmaString::encode("./root"))],
            vec![entry_function(1, vec![Instruction::Halt])],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            Vec::new(),
            Vec::new(),
        );
        linked(vec![root, target], 0)
    }

    fn assert_program_parity(
        program: &Program<Verified>,
    ) -> Result<crate::Execution, RuntimeError> {
        let limits = Limits::default();
        let mut interpreter_host = SilentHost;
        let mut interpreter = Machine::new(program, &mut interpreter_host, limits.clone());
        let interpreter = run_interpreter_to_quiescence(&mut interpreter)?;
        let mut native_host = SilentHost;
        let entries = NoEntries;
        let native = NativeEngine::new(program, &entries, &mut native_host, limits);
        let native = run_reference_to_quiescence(&native)?;
        assert_eq!(interpreter, native);
        Ok(native)
    }

    fn run_interpreter_to_quiescence<H: Host>(
        machine: &mut Machine<'_, H>,
    ) -> Result<crate::Execution, RuntimeError> {
        let execution = machine.evaluate()?;
        machine.run_to_quiescence()?;
        Ok(execution)
    }

    fn run_reference_to_quiescence<H: Host>(
        engine: &NativeEngine<'_, '_, H>,
    ) -> Result<crate::Execution, RuntimeError> {
        engine.machine.borrow_mut().instantiate_modules()?;
        let entry = engine.program.entry();
        let execution = if engine.machine.borrow().module_graph_suspends(entry) {
            engine
                .machine
                .borrow_mut()
                .evaluate_instantiated_module(entry)?
        } else {
            engine.evaluate_reference_module(entry)?.ok_or_else(|| {
                let function = engine.module(entry).entry().get() as usize;
                engine.error_at(
                    entry,
                    RuntimeErrorKind::InvalidVerifiedProgram {
                        module: entry,
                        instruction: Instruction::Halt,
                    },
                    function,
                    0,
                )
            })?
        };
        engine.machine.borrow_mut().run_to_quiescence()?;
        Ok(execution)
    }

    #[test]
    fn suppress_error_matches_interpreter_and_native_engine() {
        let program = linked(
            vec![program_module(
                "root",
                vec![
                    Constant::Int32(11),
                    Constant::Int32(22),
                    Constant::String(EcmaString::encode("error")),
                    Constant::String(EcmaString::encode("suppressed")),
                ],
                vec![entry_function(
                    7,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(2),
                        },
                        Instruction::SuppressError {
                            dst: reg(2),
                            error: reg(0),
                            suppressed: reg(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(3),
                            constant: cid(3),
                        },
                        Instruction::GetProperty {
                            dst: reg(4),
                            object: reg(2),
                            key: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(4),
                        },
                        Instruction::GetProperty {
                            dst: reg(6),
                            object: reg(2),
                            key: reg(5),
                        },
                        Instruction::Binary {
                            dst: reg(6),
                            op: BinaryOp::Add,
                            left: reg(4),
                            right: reg(6),
                        },
                        Instruction::Return { value: reg(6) },
                    ],
                )],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );

        assert_eq!(
            assert_program_parity(&program)
                .expect("suppression chain construction succeeds")
                .value,
            Value::int32(33),
        );
    }

    #[test]
    fn dispose_capture_matches_interpreter_and_native_engine() {
        let resource = |hint, property| {
            linked(
                vec![program_module(
                    "root",
                    vec![
                        Constant::String(EcmaString::encode("Symbol")),
                        Constant::String(EcmaString::encode(property)),
                        Constant::String(EcmaString::encode("Array")),
                    ],
                    vec![entry_function(
                        7,
                        vec![
                            Instruction::LoadGlobal {
                                dst: reg(0),
                                name: cid(1),
                            },
                            Instruction::LoadConst {
                                dst: reg(1),
                                constant: cid(2),
                            },
                            Instruction::GetProperty {
                                dst: reg(2),
                                object: reg(0),
                                key: reg(1),
                            },
                            Instruction::CreateObject { dst: reg(3) },
                            Instruction::LoadGlobal {
                                dst: reg(4),
                                name: cid(3),
                            },
                            Instruction::SetProperty {
                                object: reg(3),
                                key: reg(2),
                                value: reg(4),
                            },
                            Instruction::DisposeCapture {
                                method: reg(5),
                                kind: reg(6),
                                src: reg(3),
                                hint,
                            },
                            Instruction::Return { value: reg(6) },
                        ],
                    )],
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                )],
                0,
            )
        };
        let nullish = |hint| {
            linked(
                vec![program_module(
                    "root",
                    vec![Constant::Null],
                    vec![entry_function(
                        3,
                        vec![
                            Instruction::LoadConst {
                                dst: reg(0),
                                constant: cid(1),
                            },
                            Instruction::DisposeCapture {
                                method: reg(1),
                                kind: reg(2),
                                src: reg(0),
                                hint,
                            },
                            Instruction::Return { value: reg(2) },
                        ],
                    )],
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                )],
                0,
            )
        };
        let invalid = linked(
            vec![program_module(
                "root",
                vec![],
                vec![entry_function(
                    3,
                    vec![
                        Instruction::CreateObject { dst: reg(0) },
                        Instruction::DisposeCapture {
                            method: reg(1),
                            kind: reg(2),
                            src: reg(0),
                            hint: DisposeHint::Sync,
                        },
                        Instruction::Return { value: reg(2) },
                    ],
                )],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );
        assert_eq!(
            assert_program_parity(&resource(DisposeHint::Sync, "dispose"))
                .expect("sync disposer capture succeeds")
                .value,
            Value::int32(1),
        );
        assert_eq!(
            assert_program_parity(&resource(DisposeHint::Async, "asyncDispose"))
                .expect("async disposer capture succeeds")
                .value,
            Value::int32(1),
        );
        for hint in [DisposeHint::Sync, DisposeHint::Async] {
            assert_eq!(
                assert_program_parity(&nullish(hint))
                    .expect("nullish capture succeeds")
                    .value,
                Value::int32(0),
            );
        }
        assert!(matches!(
            assert_program_parity(&invalid),
            Err(RuntimeError {
                kind: RuntimeErrorKind::UncaughtThrow {
                    origin: ThrowOrigin::TypeError { .. },
                    ..
                },
                ..
            })
        ));
    }

    /// A dummy entry table for the reference backend, which never invokes it.
    struct NoEntries;

    impl NativeEntryTable for NoEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            _frame: &mut ShadowFrame,
            _out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            Err(AbiError::UnknownFunction {
                module_id,
                function_id,
            })
        }
    }

    #[test]
    fn microtask_checkpoint_matches_interpreter_and_native_engine() {
        let program = linked(
            vec![program_module(
                "root",
                vec![
                    Constant::String(EcmaString::encode("queueMicrotask")),
                    Constant::String(EcmaString::encode("observed")),
                    Constant::Int32(7),
                    Constant::Undefined,
                ],
                vec![
                    entry_function(
                        6,
                        vec![
                            Instruction::CreateArray { dst: reg(0) },
                            Instruction::CreateClosure {
                                dst: reg(1),
                                function: FunctionId::new(1),
                                captures: reg(0),
                            },
                            Instruction::LoadGlobal {
                                dst: reg(2),
                                name: cid(1),
                            },
                            Instruction::CreateArray { dst: reg(3) },
                            Instruction::ArrayPush {
                                array: reg(3),
                                value: reg(1),
                            },
                            Instruction::LoadConst {
                                dst: reg(4),
                                constant: cid(4),
                            },
                            Instruction::Call {
                                dst: reg(5),
                                callee: reg(2),
                                this_value: reg(4),
                                arguments: reg(3),
                            },
                            Instruction::Return { value: reg(4) },
                        ],
                    ),
                    module_function(
                        0,
                        1,
                        vec![
                            Instruction::LoadConst {
                                dst: reg(0),
                                constant: cid(3),
                            },
                            Instruction::StoreGlobal {
                                name: cid(2),
                                value: reg(0),
                            },
                            Instruction::Return { value: reg(0) },
                        ],
                    ),
                ],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );

        let mut interpreter_host = SilentHost;
        let mut interpreter = Machine::new(&program, &mut interpreter_host, Limits::default());
        interpreter.evaluate().unwrap();
        assert!(interpreter.test_global("observed").is_none());
        let interpreter_drain = interpreter.drain_microtasks().unwrap();
        let interpreter_value = interpreter.test_global("observed");

        let mut native_host = SilentHost;
        let engine = NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default());
        engine.machine.borrow_mut().instantiate_modules().unwrap();
        engine
            .evaluate_reference_module(program.entry())
            .unwrap()
            .expect("native entry completes");
        assert!(engine.machine.borrow().test_global("observed").is_none());
        let native_drain = engine.machine.borrow_mut().drain_microtasks().unwrap();
        let native_value = engine.machine.borrow().test_global("observed");

        assert_eq!(interpreter_drain, native_drain);
        assert_eq!(interpreter_value, Some(Value::int32(7)));
        assert_eq!(native_value, interpreter_value);
    }

    #[derive(Default)]
    struct RecordingHost {
        stdout: Vec<u8>,
    }

    impl Host for RecordingHost {
        fn write_stdout(&mut self, bytes: &[u8]) {
            self.stdout.extend_from_slice(bytes);
        }
    }

    fn first_window(haystack: &[u8], needle: &[u8]) -> Option<usize> {
        haystack.windows(needle.len()).position(|w| w == needle)
    }

    fn automatic_loop_program(callback: Function) -> Program<Verified> {
        linked(
            vec![program_module(
                "root",
                vec![
                    Constant::String(EcmaString::encode("console")),
                    Constant::String(EcmaString::encode("log")),
                    Constant::String(EcmaString::encode("sync")),
                    Constant::String(EcmaString::encode("async")),
                    Constant::String(EcmaString::encode("queueMicrotask")),
                    Constant::Int32(42),
                    Constant::Undefined,
                ],
                vec![
                    entry_function(
                        7,
                        vec![
                            Instruction::LoadGlobal {
                                dst: reg(0),
                                name: cid(1),
                            },
                            Instruction::LoadConst {
                                dst: reg(2),
                                constant: cid(3),
                            },
                            Instruction::LoadConst {
                                dst: reg(1),
                                constant: cid(2),
                            },
                            Instruction::GetProperty {
                                dst: reg(1),
                                object: reg(0),
                                key: reg(1),
                            },
                            Instruction::CreateArray { dst: reg(3) },
                            Instruction::ArrayPush {
                                array: reg(3),
                                value: reg(2),
                            },
                            Instruction::LoadConst {
                                dst: reg(4),
                                constant: cid(7),
                            },
                            Instruction::Call {
                                dst: reg(5),
                                callee: reg(1),
                                this_value: reg(4),
                                arguments: reg(3),
                            },
                            Instruction::CreateArray { dst: reg(3) },
                            Instruction::CreateClosure {
                                dst: reg(1),
                                function: FunctionId::new(1),
                                captures: reg(3),
                            },
                            Instruction::LoadGlobal {
                                dst: reg(6),
                                name: cid(5),
                            },
                            Instruction::CreateArray { dst: reg(3) },
                            Instruction::ArrayPush {
                                array: reg(3),
                                value: reg(1),
                            },
                            Instruction::LoadConst {
                                dst: reg(4),
                                constant: cid(7),
                            },
                            Instruction::Call {
                                dst: reg(5),
                                callee: reg(6),
                                this_value: reg(4),
                                arguments: reg(3),
                            },
                            Instruction::LoadConst {
                                dst: reg(0),
                                constant: cid(6),
                            },
                            Instruction::Return { value: reg(0) },
                        ],
                    ),
                    callback,
                ],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        )
    }

    fn queue_callback_microtask<H: Host>(
        engine: &mut NativeEngine<'_, '_, H>,
        function: FunctionId,
    ) {
        let mut machine = engine.machine.borrow_mut();
        let prototype = machine.intrinsics.function_prototype;
        let callback = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function,
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(prototype),
                extensible: true,
            })
            .expect("microtask callback allocates");
        let queue = machine
            .intrinsics
            .global("queueMicrotask")
            .expect("queueMicrotask is installed");
        machine
            .call_value(queue, Value::UNDEFINED, &[callback])
            .expect("microtask enqueues");
    }

    #[test]
    fn automatic_loop_drains_microtasks_and_preserves_synchronous_result() {
        let program = automatic_loop_program(module_function(
            0,
            4,
            vec![
                Instruction::LoadGlobal {
                    dst: reg(0),
                    name: cid(1),
                },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(4),
                },
                Instruction::LoadConst {
                    dst: reg(1),
                    constant: cid(2),
                },
                Instruction::GetProperty {
                    dst: reg(1),
                    object: reg(0),
                    key: reg(1),
                },
                Instruction::CreateArray { dst: reg(3) },
                Instruction::ArrayPush {
                    array: reg(3),
                    value: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(7),
                },
                Instruction::Call {
                    dst: reg(2),
                    callee: reg(1),
                    this_value: reg(0),
                    arguments: reg(3),
                },
                Instruction::Return { value: reg(0) },
            ],
        ));

        let mut interpreter_host = RecordingHost::default();
        let interpreter = Machine::new(&program, &mut interpreter_host, Limits::default())
            .run()
            .expect("interpreter drains to quiescence");
        assert_eq!(interpreter.value, Value::int32(42));
        assert!(interpreter.outcome.stdout.is_empty());
        let interp_sync = first_window(&interpreter_host.stdout, b"sync");
        let interp_async = first_window(&interpreter_host.stdout, b"async");
        assert!(
            interp_sync.is_some_and(|s| interp_async.is_some_and(|a| s < a)),
            "host received sync-then-async bytes: {:?}",
            interpreter_host.stdout,
        );

        let mut native_host = RecordingHost::default();
        let native = NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default())
            .run()
            .expect("reference native drains to quiescence");
        assert_eq!(native.value, Value::int32(42));
        assert!(native.outcome.stdout.is_empty());
        assert_eq!(native_host.stdout, interpreter_host.stdout);

        let mut linked_host = RecordingHost::default();
        let linked_outcome = {
            let entries = ForeignEntries {
                program_bytes: program.encode(),
                invoked: Cell::new(false),
            };
            let mut linked = NativeEngine::build(
                &program,
                &entries,
                &mut linked_host,
                Limits::default(),
                Backend::Linked,
                bamts_cancel::CancellationToken::new(),
            );
            queue_callback_microtask(&mut linked, FunctionId::new(1));
            linked
                .run_linked()
                .expect("linked native drains to quiescence")
        };
        assert!(linked_outcome.stdout.is_empty());
        assert!(
            first_window(&linked_host.stdout, b"async").is_some(),
            "linked loop drained the pre-queued microtask: {:?}",
            linked_host.stdout,
        );
    }

    #[test]
    fn automatic_loop_surfaces_uncaught_callback_error_across_entrypoints() {
        let program = automatic_loop_program(module_function(
            0,
            1,
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(6),
                },
                Instruction::Throw { value: reg(0) },
            ],
        ));

        let mut interpreter_host = SilentHost;
        let interpreter_err = Machine::new(&program, &mut interpreter_host, Limits::default())
            .run()
            .expect_err("interpreter surfaces the uncaught callback");
        let thrown = match &interpreter_err.kind {
            RuntimeErrorKind::UncaughtThrow { value, .. } => *value,
            other => panic!("expected UncaughtThrow, got {other:?}"),
        };
        assert_eq!(thrown, Value::int32(42));

        let mut native_host = SilentHost;
        let native_err =
            NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default())
                .run()
                .expect_err("reference native surfaces the uncaught callback");
        assert_eq!(native_err.kind, interpreter_err.kind);

        let mut linked_host = SilentHost;
        let linked_err = {
            let entries = ForeignEntries {
                program_bytes: program.encode(),
                invoked: Cell::new(false),
            };
            let mut linked = NativeEngine::build(
                &program,
                &entries,
                &mut linked_host,
                Limits::default(),
                Backend::Linked,
                bamts_cancel::CancellationToken::new(),
            );
            queue_callback_microtask(&mut linked, FunctionId::new(1));
            linked
                .run_linked()
                .expect_err("linked native surfaces the uncaught callback")
        };
        match linked_err {
            NativeError::Runtime(RuntimeError { ref kind, .. })
                if *kind == interpreter_err.kind => {}
            other => panic!("linked mapped the callback throw: {other:?}"),
        }
    }

    fn async_module_function(registers: u32, code: Vec<Instruction>) -> Function {
        Function::new(
            None,
            0,
            0,
            registers,
            FunctionFlags {
                is_async: true,
                is_generator: false,
                is_constructable: false,
                ..FunctionFlags::default()
            },
            code,
            Vec::new(),
        )
    }

    /// An ordinary async call routed through the native reference engine must
    /// produce the same Promise settlement, globals, and drain counts as the
    /// interpreter, because native async execution reuses the shared Machine
    /// reference state machine.
    #[test]
    fn async_call_matches_interpreter_and_native_engine() {
        let program = linked(
            vec![program_module(
                "root",
                vec![
                    Constant::String(EcmaString::encode("observed")),
                    Constant::Int32(7),
                    Constant::Undefined,
                ],
                vec![
                    entry_function(
                        5,
                        vec![
                            Instruction::CreateArray { dst: reg(0) },
                            Instruction::CreateClosure {
                                dst: reg(1),
                                function: FunctionId::new(1),
                                captures: reg(0),
                            },
                            Instruction::CreateArray { dst: reg(2) },
                            Instruction::LoadConst {
                                dst: reg(3),
                                constant: cid(3),
                            },
                            Instruction::Call {
                                dst: reg(4),
                                callee: reg(1),
                                this_value: reg(3),
                                arguments: reg(2),
                            },
                            Instruction::Return { value: reg(3) },
                        ],
                    ),
                    async_module_function(
                        2,
                        vec![
                            Instruction::LoadConst {
                                dst: reg(0),
                                constant: cid(2),
                            },
                            Instruction::Await {
                                dst: reg(1),
                                src: reg(0),
                                resume: pc(2),
                            },
                            Instruction::StoreGlobal {
                                name: cid(1),
                                value: reg(1),
                            },
                            Instruction::Return { value: reg(1) },
                        ],
                    ),
                ],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );

        let mut interpreter_host = SilentHost;
        let mut interpreter = Machine::new(&program, &mut interpreter_host, Limits::default());
        interpreter.evaluate().unwrap();
        assert!(interpreter.test_global("observed").is_none());
        let interpreter_drain = interpreter.drain_microtasks().unwrap();
        let interpreter_value = interpreter.test_global("observed");

        let mut native_host = SilentHost;
        let engine = NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default());
        engine.machine.borrow_mut().instantiate_modules().unwrap();
        engine
            .evaluate_reference_module(program.entry())
            .unwrap()
            .expect("native entry completes");
        assert!(engine.machine.borrow().test_global("observed").is_none());
        let native_drain = engine.machine.borrow_mut().drain_microtasks().unwrap();
        let native_value = engine.machine.borrow().test_global("observed");

        let mut linked_host = SilentHost;
        let linked = NativeEngine::build(
            &program,
            &NoEntries,
            &mut linked_host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        linked.machine.borrow_mut().instantiate_modules().unwrap();
        assert!(matches!(
            linked.invoke_runtime(
                crate::RuntimeFunction {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                },
                &[],
                None,
                Value::UNDEFINED,
                Value::UNDEFINED,
                &[],
            ),
            InvokeOutcome::Value(_)
        ));
        assert!(linked.machine.borrow().test_global("observed").is_none());
        let linked_drain = linked.machine.borrow_mut().drain_microtasks().unwrap();
        let linked_value = linked.machine.borrow().test_global("observed");

        assert_eq!(interpreter_drain, native_drain);
        assert_eq!(interpreter_value, Some(Value::int32(7)));
        assert_eq!(native_value, interpreter_value);
        assert_eq!(linked_drain, interpreter_drain);
        assert_eq!(linked_value, interpreter_value);
    }

    /// Constructing an async function through the native engine is a TypeError,
    /// matching the interpreter's construct guard, with no bytecode/ABI change.
    #[test]
    fn native_construct_of_async_function_is_a_type_error() {
        let program = linked(
            vec![program_module(
                "root",
                Vec::new(),
                vec![
                    entry_function(
                        4,
                        vec![
                            Instruction::CreateArray { dst: reg(0) },
                            Instruction::CreateClosure {
                                dst: reg(1),
                                function: FunctionId::new(1),
                                captures: reg(0),
                            },
                            Instruction::CreateArray { dst: reg(2) },
                            Instruction::Construct {
                                dst: reg(3),
                                callee: reg(1),
                                arguments: reg(2),
                            },
                            Instruction::Return { value: reg(3) },
                        ],
                    ),
                    async_module_function(1, vec![Instruction::Halt]),
                ],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );
        let mut host = SilentHost;
        let result = NativeEngine::new(&program, &NoEntries, &mut host, Limits::default()).run();
        assert!(matches!(
            result,
            Err(RuntimeError {
                kind: RuntimeErrorKind::UncaughtThrow {
                    origin: ThrowOrigin::TypeError { .. },
                    ..
                },
                ..
            })
        ));
    }

    #[derive(Default)]
    struct RecordingEntries {
        program_bytes: Vec<u8>,
        invoked: RefCell<Vec<(u32, u32)>>,
    }

    impl NativeEntryTable for RecordingEntries {
        fn program_bytes(&self) -> &[u8] {
            &self.program_bytes
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            _frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            self.invoked.borrow_mut().push((module_id, function_id));
            *out = Completion::new(Value::UNDEFINED);
            Ok(CompletionTag::Normal)
        }
    }

    struct ForeignEntries {
        program_bytes: Vec<u8>,
        invoked: Cell<bool>,
    }

    impl NativeEntryTable for ForeignEntries {
        fn program_bytes(&self) -> &[u8] {
            &self.program_bytes
        }

        fn invoke(
            &self,
            _module_id: u32,
            _function_id: u32,
            _frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            self.invoked.set(true);
            *out = Completion::new(Value::UNDEFINED);
            Ok(CompletionTag::Normal)
        }
    }

    struct SmokeEntries {
        program_bytes: Vec<u8>,
        invoked: Cell<Option<u32>>,
    }

    impl NativeEntryTable for SmokeEntries {
        fn program_bytes(&self) -> &[u8] {
            &self.program_bytes
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            _frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            assert_eq!(module_id, 0);
            self.invoked.set(Some(function_id));
            *out = Completion::new(Value::UNDEFINED);
            Ok(CompletionTag::Normal)
        }
    }

    #[derive(Default)]
    struct FailingEntries {
        program_bytes: Vec<u8>,
    }

    impl NativeEntryTable for FailingEntries {
        fn program_bytes(&self) -> &[u8] {
            &self.program_bytes
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            _frame: &mut ShadowFrame,
            _out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            Err(AbiError::UnknownFunction {
                module_id,
                function_id,
            })
        }
    }

    struct ThrowEntries;

    impl NativeEntryTable for ThrowEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            _module_id: u32,
            _function_id: u32,
            _frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            *out = Completion::new(Value::UNDEFINED);
            Ok(CompletionTag::Throw)
        }
    }

    struct FaultSiteEntries {
        entry_tag: Cell<CompletionTag>,
        entry_pc: Cell<u32>,
        child_pc: u32,
    }

    impl FaultSiteEntries {
        fn throwing(entry_pc: u32, child_pc: u32) -> Self {
            Self {
                entry_tag: Cell::new(CompletionTag::Throw),
                entry_pc: Cell::new(entry_pc),
                child_pc,
            }
        }
    }

    impl NativeEntryTable for FaultSiteEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            _module_id: u32,
            function_id: u32,
            frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            *out = Completion::new(Value::UNDEFINED);
            match function_id {
                0 => {
                    frame.bytecode_pc = self.entry_pc.get();
                    Ok(self.entry_tag.get())
                }
                1 => {
                    frame.bytecode_pc = self.child_pc;
                    Ok(CompletionTag::Throw)
                }
                _ => unreachable!("fault-site fixture only exposes entry and child"),
            }
        }
    }

    struct FatalEntries;

    impl NativeEntryTable for FatalEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            _module_id: u32,
            _function_id: u32,
            _frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            *out = Completion::new(Value::UNDEFINED);
            Ok(CompletionTag::FatalTrap)
        }
    }

    #[test]
    fn native_program_keeps_same_name_globals_module_local() {
        let dependency = |name: &str, value: i32| {
            program_module(
                name,
                vec![
                    Constant::String(EcmaString::encode("x")),
                    Constant::Int32(value),
                ],
                vec![module_function(
                    0,
                    1,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(2),
                        },
                        Instruction::StoreGlobal {
                            name: cid(1),
                            value: reg(0),
                        },
                        Instruction::Return { value: reg(0) },
                    ],
                )],
                Vec::new(),
                vec![Binding {
                    name: cid(1),
                    kind: BindingKind::Hoisted,
                }],
                vec![Export {
                    name: cid(1),
                    source: ExportSource::Local(BindingId::new(0)),
                }],
            )
        };
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("left")),
                Constant::String(EcmaString::encode("right")),
                Constant::String(EcmaString::encode("x")),
                Constant::String(EcmaString::encode("one")),
                Constant::String(EcmaString::encode("two")),
            ],
            vec![module_function(
                0,
                3,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(1),
                        name: cid(2),
                    },
                    Instruction::Binary {
                        dst: reg(2),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
            )],
            vec![
                Edge {
                    specifier: cid(3),
                    target: EdgeTarget::Local(ModuleId::new(0)),
                    kind: EdgeKind::Static,
                },
                Edge {
                    specifier: cid(4),
                    target: EdgeTarget::Local(ModuleId::new(1)),
                    kind: EdgeKind::Static,
                },
            ],
            vec![
                Binding {
                    name: cid(1),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(0),
                        name: cid(3),
                    },
                },
                Binding {
                    name: cid(2),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(1),
                        name: cid(3),
                    },
                },
            ],
            Vec::new(),
        );
        let execution = assert_program_parity(&linked(
            vec![dependency("one", 1), dependency("two", 2), root],
            2,
        ))
        .unwrap();
        assert_eq!(execution.value, Value::int32(3));
    }

    #[test]
    fn native_program_preserves_live_mutation_and_nested_closure_module() {
        let dependency = program_module(
            "dependency",
            vec![
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(1),
                Constant::Int32(2),
                Constant::String(EcmaString::encode("set")),
            ],
            vec![
                module_function(
                    0,
                    3,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(2),
                        },
                        Instruction::StoreGlobal {
                            name: cid(1),
                            value: reg(0),
                        },
                        Instruction::CreateArray { dst: reg(1) },
                        Instruction::CreateClosure {
                            dst: reg(2),
                            function: FunctionId::new(1),
                            captures: reg(1),
                        },
                        Instruction::StoreGlobal {
                            name: cid(4),
                            value: reg(2),
                        },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
                module_function(
                    0,
                    1,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(3),
                        },
                        Instruction::StoreGlobal {
                            name: cid(1),
                            value: reg(0),
                        },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
            ],
            Vec::new(),
            vec![
                Binding {
                    name: cid(1),
                    kind: BindingKind::Hoisted,
                },
                Binding {
                    name: cid(4),
                    kind: BindingKind::Hoisted,
                },
            ],
            vec![
                Export {
                    name: cid(1),
                    source: ExportSource::Local(BindingId::new(0)),
                },
                Export {
                    name: cid(4),
                    source: ExportSource::Local(BindingId::new(1)),
                },
            ],
        );
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("set")),
                Constant::String(EcmaString::encode("x")),
                Constant::String(EcmaString::encode("dependency")),
            ],
            vec![module_function(
                0,
                3,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::Call {
                        dst: reg(2),
                        callee: reg(0),
                        this_value: reg(1),
                        arguments: reg(1),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(2),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![Edge {
                specifier: cid(3),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            vec![
                Binding {
                    name: cid(1),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(0),
                        name: cid(1),
                    },
                },
                Binding {
                    name: cid(2),
                    kind: BindingKind::Imported {
                        edge: EdgeId::new(0),
                        name: cid(2),
                    },
                },
            ],
            Vec::new(),
        );
        assert_eq!(
            assert_program_parity(&linked(vec![dependency, root], 1))
                .unwrap()
                .value,
            Value::int32(2)
        );
    }

    #[test]
    fn native_program_cycle_observes_temporal_dead_zone() {
        let first = program_module(
            "first",
            vec![
                Constant::String(EcmaString::encode("a")),
                Constant::Int32(1),
                Constant::String(EcmaString::encode("second")),
            ],
            vec![module_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![Edge {
                specifier: cid(3),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Static,
            }],
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Lexical,
            }],
            vec![Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            }],
        );
        let second = program_module(
            "second",
            vec![
                Constant::String(EcmaString::encode("a")),
                Constant::String(EcmaString::encode("first")),
            ],
            vec![module_function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![Edge {
                specifier: cid(2),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(1),
                },
            }],
            Vec::new(),
        );
        let error = assert_program_parity(&linked(vec![first, second], 0)).unwrap_err();
        assert!(matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                origin: ThrowOrigin::ReferenceError { .. },
                ..
            }
        ));
    }

    #[test]
    fn native_program_namespace_reads_shared_export_cell() {
        let dependency = program_module(
            "dependency",
            vec![
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(7),
            ],
            vec![module_function(
                0,
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            Vec::new(),
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            }],
            vec![Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            }],
        );
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("ns")),
                Constant::String(EcmaString::encode("x")),
                Constant::String(EcmaString::encode("dependency")),
            ],
            vec![module_function(
                0,
                3,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(2),
                        object: reg(0),
                        key: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
            )],
            vec![Edge {
                specifier: cid(3),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Namespace {
                    edge: EdgeId::new(0),
                },
            }],
            Vec::new(),
        );
        assert_eq!(
            assert_program_parity(&linked(vec![dependency, root], 1))
                .unwrap()
                .value,
            Value::int32(7)
        );
    }

    #[test]
    fn native_program_evaluates_duplicate_static_dependency_once() {
        let dependency = program_module(
            "dependency",
            vec![
                Constant::String(EcmaString::encode("count")),
                Constant::Int32(0),
                Constant::Int32(1),
            ],
            vec![module_function(
                0,
                2,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::JumpIfFalse {
                        condition: reg(0),
                        target: pc(4),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::Jump { target: pc(6) },
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::Binary {
                        dst: reg(0),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            Vec::new(),
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Hoisted,
            }],
            vec![Export {
                name: cid(1),
                source: ExportSource::Local(BindingId::new(0)),
            }],
        );
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("count")),
                Constant::String(EcmaString::encode("dependency")),
                Constant::String(EcmaString::encode("dependency-again")),
            ],
            vec![module_function(
                0,
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![
                Edge {
                    specifier: cid(2),
                    target: EdgeTarget::Local(ModuleId::new(0)),
                    kind: EdgeKind::Static,
                },
                Edge {
                    specifier: cid(3),
                    target: EdgeTarget::Local(ModuleId::new(0)),
                    kind: EdgeKind::Static,
                },
            ],
            vec![Binding {
                name: cid(1),
                kind: BindingKind::Imported {
                    edge: EdgeId::new(0),
                    name: cid(1),
                },
            }],
            Vec::new(),
        );
        assert_eq!(
            assert_program_parity(&linked(vec![dependency, root], 1))
                .unwrap()
                .value,
            Value::int32(1)
        );
    }

    #[test]
    fn native_program_memoizes_thrown_object_identity() {
        let module = program_module(
            "throws",
            Vec::new(),
            vec![module_function(
                0,
                1,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::Throw { value: reg(0) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let error = assert_program_parity(&linked(vec![module], 0)).unwrap_err();
        assert!(matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }));
    }

    struct SilentHost;
    impl Host for SilentHost {}

    #[test]
    fn native_matches_interpreter_on_arithmetic() {
        let module = verified(
            vec![Constant::Int32(3), Constant::Int32(4)],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::Binary {
                        dst: reg(0),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        );
        let value = assert_parity(&module, || SilentHost);
        assert_eq!(value.as_int32(), Some(7));
    }

    #[test]
    fn reference_and_interpreter_charge_each_mixed_instruction_once() {
        let module = verified(
            vec![Constant::Int32(1)],
            vec![entry_function(
                3,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Move {
                        dst: reg(1),
                        src: reg(0),
                    },
                    Instruction::Binary {
                        dst: reg(2),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Jump { target: pc(4) },
                    Instruction::Halt,
                ],
            )],
        );
        let program = one_module_program(&module);

        for fuel in [0, 4, 5] {
            let limits = Limits {
                fuel,
                ..Limits::default()
            };
            let mut interpreter_host = SilentHost;
            let interpreter = Machine::new(&program, &mut interpreter_host, limits.clone()).run();
            let mut reference_host = SilentHost;
            let reference =
                NativeEngine::new(&program, &NoEntries, &mut reference_host, limits).run();
            assert_eq!(interpreter, reference, "fuel={fuel}");
            if fuel == 5 {
                assert!(reference.is_ok(), "N instructions must fit fuel N");
            } else {
                assert!(
                    matches!(
                        reference,
                        Err(RuntimeError {
                            kind: RuntimeErrorKind::FuelExhausted { limit },
                            ..
                        }) if limit == fuel
                    ),
                    "fuel={fuel} must exhaust before the next instruction"
                );
            }
        }
    }

    #[test]
    fn native_reservations_share_interpreter_depth_and_register_ceilings() {
        let module = verified(Vec::new(), vec![entry_function(2, vec![Instruction::Halt])]);
        let program = one_module_program(&module);
        let mut host = SilentHost;
        let mut machine = Machine::new(
            &program,
            &mut host,
            Limits {
                max_call_depth: 2,
                max_total_registers: 3,
                ..Limits::default()
            },
        );

        assert_eq!(machine.frames.len(), 1);
        assert_eq!(machine.live_registers, 2);
        machine.reserve_native_activation(1).unwrap();
        assert_eq!((machine.native_depth, machine.live_registers), (1, 3));
        assert!(matches!(
            machine.reserve_native_activation(0),
            Err(RuntimeErrorKind::CallDepthExceeded { limit: 2 })
        ));
        assert_eq!(
            (machine.native_depth, machine.live_registers),
            (1, 3),
            "failed depth reservation is atomic"
        );
        machine.release_native_activation(1);

        machine.limits.max_call_depth = 3;
        machine.limits.max_total_registers = 2;
        assert!(matches!(
            machine.reserve_native_activation(1),
            Err(RuntimeErrorKind::RegisterLimitExceeded { limit: 2 })
        ));
        assert_eq!(
            (machine.native_depth, machine.live_registers),
            (0, 2),
            "failed register reservation is atomic"
        );
    }

    #[test]
    fn native_matches_interpreter_on_loop_and_branches() {
        // acc=0; for i in 1..4 { acc += i } -> 6, exercising Binary compare,
        // JumpIfFalse, and Jump through the native driver's own control flow.
        let module = verified(
            vec![Constant::Int32(0), Constant::Int32(1), Constant::Int32(4)],
            vec![entry_function(
                5,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::Binary {
                        dst: reg(4),
                        op: BinaryOp::LessThan,
                        left: reg(1),
                        right: reg(2),
                    },
                    Instruction::JumpIfFalse {
                        condition: reg(4),
                        target: pc(9),
                    },
                    Instruction::Binary {
                        dst: reg(0),
                        op: BinaryOp::Add,
                        left: reg(0),
                        right: reg(1),
                    },
                    Instruction::Binary {
                        dst: reg(1),
                        op: BinaryOp::Add,
                        left: reg(1),
                        right: reg(3),
                    },
                    Instruction::Jump { target: pc(4) },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        );
        let value = assert_parity(&module, || SilentHost);
        assert_eq!(value.as_int32(), Some(6));
    }

    #[test]
    fn native_matches_interpreter_on_object_property_roundtrip() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(5),
            ],
            vec![entry_function(
                3,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::SetProperty {
                        object: reg(0),
                        key: reg(1),
                        value: reg(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(2),
                        object: reg(0),
                        key: reg(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
            )],
        );
        let value = assert_parity(&module, || SilentHost);
        assert_eq!(value.as_int32(), Some(5));
    }

    #[test]
    fn native_matches_interpreter_on_closure_call() {
        // fn0: build empty captures, close over fn1, call it. fn1: return 42.
        let entry = entry_function(
            3,
            vec![
                Instruction::CreateArray { dst: reg(0) },
                Instruction::CreateClosure {
                    dst: reg(1),
                    function: FunctionId::new(1),
                    captures: reg(0),
                },
                Instruction::CreateArray { dst: reg(0) },
                Instruction::LoadConst {
                    dst: reg(2),
                    constant: cid(0),
                },
                Instruction::Call {
                    dst: reg(0),
                    callee: reg(1),
                    this_value: reg(2),
                    arguments: reg(0),
                },
                Instruction::Return { value: reg(0) },
            ],
        );
        let callee = Function::new(
            None,
            0,
            0,
            1,
            FunctionFlags::default(),
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        );
        let module = verified(
            vec![Constant::Undefined, Constant::Int32(42)],
            vec![entry, callee],
        );
        let value = assert_parity(&module, || SilentHost);
        assert_eq!(value.as_int32(), Some(42));
    }

    #[test]
    fn native_matches_interpreter_on_throw_and_catch() {
        let module = verified(
            vec![Constant::Int32(99)],
            vec![Function::new(
                None,
                0,
                0,
                2,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Throw { value: reg(0) },
                    Instruction::Return { value: reg(1) },
                ],
                vec![ExceptionHandler {
                    start: pc(0),
                    end: pc(2),
                    handler: pc(2),
                    catch_register: reg(1),
                }],
            )],
        );
        let value = assert_parity(&module, || SilentHost);
        assert_eq!(value.as_int32(), Some(99));
    }

    fn one_module_program(module: &Module<Verified>) -> Program<Verified> {
        let mut constants = module.constants().to_vec();
        let name = ConstantId::new(constants.len() as u32);
        constants.push(Constant::String(EcmaString::encode("test-module")));
        let code = Module::new(constants, module.functions().to_vec(), module.entry())
            .verify()
            .expect("test module remains verified");
        Program::link(
            vec![ProgramModule {
                name,
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("one-module reference program links")
    }

    fn assert_parity<H: Host, F: Fn() -> H>(module: &Module<Verified>, make_host: F) -> Value {
        let _suspended = crate::gc::StressSuspended::begin();
        let limits = Limits::default();
        let program = one_module_program(module);

        let mut interp_host = make_host();
        let interpreter = Machine::new(&program, &mut interp_host, limits.clone())
            .run()
            .expect("interpreter runs");

        let mut native_host = make_host();
        let entries = NoEntries;
        let native = NativeEngine::new(&program, &entries, &mut native_host, limits)
            .run()
            .expect("native engine runs");

        assert_eq!(
            interpreter.value, native.value,
            "return value parity: interpreter {:?} vs native {:?}",
            interpreter.value, native.value
        );
        assert_eq!(
            interpreter.outcome, native.outcome,
            "outcome parity: interpreter {:?} vs native {:?}",
            interpreter.outcome, native.outcome
        );
        assert_eq!(
            interpreter.entry_registers, native.entry_registers,
            "entry register parity"
        );
        native.value
    }

    fn trivial_program() -> Program<Verified> {
        let code = verified(
            vec![Constant::String(EcmaString::encode("<test>"))],
            vec![entry_function(1, vec![Instruction::Halt])],
        );
        Program::link(
            vec![ProgramModule {
                name: ConstantId::new(0),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            ModuleId::new(0),
        )
        .expect("valid native test program")
    }

    #[test]
    fn linked_backend_accepts_metadata_empty_single_module_program() {
        let program = trivial_program();
        let entries = SmokeEntries {
            program_bytes: program.encode(),
            invoked: Cell::new(None),
        };
        let mut host = SilentHost;
        let outcome = run_linked_program(&program, &entries, &mut host, &Limits::default())
            .expect("linked program runs");
        assert_eq!(entries.invoked.get(), Some(0), "entry function 0 invoked");
        assert_eq!(outcome.exit_code, 0);
        assert!(outcome.stdout.is_empty());
    }

    #[test]
    fn linked_backend_propagates_abi_error() {
        let program = trivial_program();
        let entries = FailingEntries {
            program_bytes: program.encode(),
        };
        let mut host = SilentHost;
        let error = run_linked_program(&program, &entries, &mut host, &Limits::default())
            .expect_err("entry table failure surfaces");
        assert!(matches!(
            error,
            NativeError::Abi(AbiError::UnknownFunction {
                module_id: 0,
                function_id: 0
            })
        ));
    }

    #[test]
    fn linked_backend_rejects_entries_from_same_shape_different_program_before_invocation() {
        let program = |constant| {
            linked(
                vec![program_module(
                    "entry",
                    vec![Constant::Int32(constant)],
                    vec![entry_function(
                        1,
                        vec![
                            Instruction::LoadConst {
                                dst: reg(0),
                                constant: cid(1),
                            },
                            Instruction::Return { value: reg(0) },
                        ],
                    )],
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                )],
                0,
            )
        };
        let compiled_program = program(1);
        let supplied_program = program(2);
        let entries = ForeignEntries {
            program_bytes: compiled_program.encode(),
            invoked: Cell::new(false),
        };
        let mut host = SilentHost;

        assert_eq!(
            run_linked_program(&supplied_program, &entries, &mut host, &Limits::default()),
            Err(NativeError::ProgramMismatch)
        );
        assert!(
            !entries.invoked.get(),
            "mismatched entries must not be invoked"
        );
    }

    #[test]
    fn linked_backend_invokes_static_dependencies_before_entry_by_tuple() {
        let single = trivial_program();
        let first = single.modules()[0].clone();
        let second = program_module(
            "entry",
            vec![Constant::String(EcmaString::encode("dependency"))],
            vec![entry_function(1, vec![Instruction::Halt])],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            Vec::new(),
            Vec::new(),
        );
        let program = Program::link(vec![first, second], ModuleId::new(1)).unwrap();
        let entries = RecordingEntries {
            program_bytes: program.encode(),
            ..RecordingEntries::default()
        };
        let mut host = SilentHost;
        run_linked_program(&program, &entries, &mut host, &Limits::default()).unwrap();
        assert_eq!(entries.invoked.borrow().as_slice(), &[(0, 0), (1, 0)]);
    }

    #[test]
    fn linked_top_level_await_uses_the_reference_entry() {
        let module = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("after")),
                Constant::Int32(7),
            ],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::Await {
                        dst: reg(1),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let program = linked(vec![module], 0);
        let entries = ForeignEntries {
            program_bytes: program.encode(),
            invoked: Cell::new(false),
        };
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );

        engine.run_linked().expect("top-level await completes");

        assert!(!entries.invoked.get(), "linked entry must not run");
        assert_eq!(
            engine.machine.borrow().test_global("after"),
            Some(Value::int32(7)),
        );
    }

    #[test]
    fn static_dependency_tla_delegates_the_whole_native_graph() {
        let dependency = program_module(
            "dependency",
            vec![
                Constant::String(EcmaString::encode("after")),
                Constant::Undefined,
                Constant::Int32(7),
            ],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(2),
                    },
                    Instruction::Await {
                        dst: reg(0),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(3),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(1),
                    },
                    Instruction::Return { value: reg(1) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("after")),
                Constant::String(EcmaString::encode("dependency")),
            ],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(1),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![Edge {
                specifier: cid(2),
                target: EdgeTarget::Local(ModuleId::new(0)),
                kind: EdgeKind::Static,
            }],
            Vec::new(),
            Vec::new(),
        );
        let program = linked(vec![dependency, root], 1);

        let mut reference_host = SilentHost;
        let execution =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, Limits::default())
                .run()
                .expect("reference backend completes the async dependency");
        assert_eq!(execution.value, Value::int32(7));

        let entries = ForeignEntries {
            program_bytes: program.encode(),
            invoked: Cell::new(false),
        };
        let mut linked_host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut linked_host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine
            .run_linked()
            .expect("linked backend completes the async dependency");
        assert!(
            !entries.invoked.get(),
            "the linked graph must not mix native and interpreter entries"
        );
        assert_eq!(
            engine.machine.borrow().test_global("after"),
            Some(Value::int32(7)),
        );
    }

    fn rejecting_dependency_graph() -> Program<Verified> {
        let rejecting = program_module(
            "rejecting",
            vec![Constant::Undefined, Constant::Int32(9)],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::Await {
                        dst: reg(0),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(2),
                    },
                    Instruction::Throw { value: reg(1) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let pending = program_module(
            "pending",
            vec![Constant::Undefined],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::Await {
                        dst: reg(0),
                        src: reg(0),
                        resume: pc(2),
                    },
                    Instruction::Await {
                        dst: reg(0),
                        src: reg(0),
                        resume: pc(3),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let root = program_module(
            "root",
            vec![
                Constant::String(EcmaString::encode("rejecting")),
                Constant::String(EcmaString::encode("pending")),
                Constant::String(EcmaString::encode("root-ran")),
                Constant::Int32(1),
            ],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(4),
                    },
                    Instruction::StoreGlobal {
                        name: cid(3),
                        value: reg(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
            vec![
                Edge {
                    specifier: cid(1),
                    target: EdgeTarget::Local(ModuleId::new(0)),
                    kind: EdgeKind::Static,
                },
                Edge {
                    specifier: cid(2),
                    target: EdgeTarget::Local(ModuleId::new(1)),
                    kind: EdgeKind::Static,
                },
            ],
            Vec::new(),
            Vec::new(),
        );
        linked(vec![rejecting, pending, root], 2)
    }

    #[test]
    fn a_rejected_first_dependency_survives_a_collection_at_every_safe_point() {
        let program = rejecting_dependency_graph();
        let mut host = SilentHost;
        let limits = Limits {
            collect_every_allocation: true,
            ..Limits::default()
        };
        let mut machine = Machine::new(&program, &mut host, limits);
        let error = machine
            .evaluate()
            .expect_err("the dependency rejection propagates");
        assert!(
            matches!(
                error.kind,
                RuntimeErrorKind::UncaughtThrow { value, .. } if value == Value::int32(9)
            ),
            "unexpected error: {:?}",
            error.kind
        );
        assert!(machine.test_global("root-ran").is_none());
    }

    #[test]
    fn first_static_dependency_tla_rejection_skips_the_native_graph() {
        let program = rejecting_dependency_graph();

        let mut interpreter_host = SilentHost;
        let mut machine = Machine::new(&program, &mut interpreter_host, Limits::default());
        let error = machine
            .evaluate()
            .expect_err("interpreter propagates the first dependency rejection");
        assert!(
            matches!(
                error.kind,
                RuntimeErrorKind::UncaughtThrow {
                    value,
                    ..
                } if value == Value::int32(9)
            ),
            "unexpected error: {:?}",
            error.kind
        );
        assert!(
            machine.test_global("root-ran").is_none(),
            "the root body must not run after a dependency rejects"
        );

        let mut reference_host = SilentHost;
        let error = NativeEngine::new(&program, &NoEntries, &mut reference_host, Limits::default())
            .run()
            .expect_err("reference backend propagates the async dependency rejection");
        assert!(matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                value,
                ..
            } if value == Value::int32(9)
        ));

        let entries = ForeignEntries {
            program_bytes: program.encode(),
            invoked: Cell::new(false),
        };
        let mut linked_host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut linked_host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let error = engine
            .run_linked()
            .expect_err("linked backend propagates the async dependency rejection");
        assert!(matches!(
            error,
            NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::UncaughtThrow {
                    value,
                    ..
                },
                ..
            }) if value == Value::int32(9)
        ));
        assert!(
            !entries.invoked.get(),
            "the rejected async graph must not run a linked entry"
        );
        assert!(
            engine.machine.borrow().test_global("root-ran").is_none(),
            "the linked root body must not run after a dependency rejects"
        );
    }

    #[test]
    fn dynamic_import_cycle_matches_the_reference_backend() {
        let execution = assert_program_parity(&dynamic_cycle_program()).unwrap();
        assert_eq!(execution.value, Value::TRUE);
        assert_eq!(execution.entry_registers[0], execution.entry_registers[1]);
    }

    #[test]
    fn dynamic_import_throw_is_caught_at_the_requester_in_both_backends() {
        let root = program_module(
            "root",
            vec![Constant::String(EcmaString::encode("./target"))],
            vec![Function::new(
                None,
                0,
                0,
                2,
                FunctionFlags::default(),
                vec![
                    Instruction::Import {
                        dst: reg(0),
                        specifier: cid(1),
                    },
                    Instruction::Halt,
                    Instruction::Return { value: reg(1) },
                ],
                vec![ExceptionHandler {
                    start: pc(0),
                    end: pc(1),
                    handler: pc(2),
                    catch_register: reg(1),
                }],
            )],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Dynamic,
            }],
            Vec::new(),
            Vec::new(),
        );
        let target = program_module(
            "target",
            vec![Constant::Int32(9)],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::Throw { value: reg(0) },
                ],
            )],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );

        assert_eq!(
            assert_program_parity(&linked(vec![root, target], 0))
                .unwrap()
                .value,
            Value::int32(9)
        );
    }

    #[test]
    fn linked_dynamic_import_invokes_the_target_once() {
        let program = dynamic_cycle_program();
        let entries = RecordingEntries {
            program_bytes: program.encode(),
            ..RecordingEntries::default()
        };
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.machine.borrow_mut().instantiate_modules().unwrap();
        assert!(matches!(
            engine
                .machine
                .borrow_mut()
                .begin_module_evaluation(ModuleId::new(0))
                .unwrap(),
            crate::ModuleEvaluation::Ready(_)
        ));

        let mut registers = [Value::UNINITIALIZED; 3];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow =
            ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, registers.len() as u16);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let first = engine.dispatch(&mut frame, HelperCall::Import { specifier: 1 });
        let second = engine.dispatch(&mut frame, HelperCall::Import { specifier: 1 });

        assert_eq!(first.tag, CompletionTag::Normal);
        assert_eq!(second.tag, CompletionTag::Normal);
        assert_eq!(first.value, second.value);
        assert_eq!(entries.invoked.borrow().as_slice(), &[(1, 0)]);
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn native_functions_call_and_construct_with_engine_parity() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("Object")),
                Constant::String(EcmaString::encode("prototype")),
                Constant::String(EcmaString::encode("toString")),
                Constant::String(EcmaString::encode("call")),
                Constant::String(EcmaString::encode("[object Object]")),
                Constant::Undefined,
            ],
            vec![entry_function(
                8,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::Construct {
                        dst: reg(2),
                        callee: reg(0),
                        arguments: reg(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::GetProperty {
                        dst: reg(4),
                        object: reg(0),
                        key: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(4),
                        object: reg(4),
                        key: reg(3),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(3),
                    },
                    Instruction::GetProperty {
                        dst: reg(5),
                        object: reg(4),
                        key: reg(3),
                    },
                    Instruction::CreateArray { dst: reg(6) },
                    Instruction::ArrayPush {
                        array: reg(6),
                        value: reg(2),
                    },
                    Instruction::Call {
                        dst: reg(5),
                        callee: reg(5),
                        this_value: reg(4),
                        arguments: reg(6),
                    },
                    Instruction::LoadConst {
                        dst: reg(6),
                        constant: cid(4),
                    },
                    Instruction::Binary {
                        dst: reg(7),
                        op: BinaryOp::StrictEqual,
                        left: reg(5),
                        right: reg(6),
                    },
                    Instruction::Return { value: reg(7) },
                ],
            )],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::TRUE);
    }

    #[test]
    fn builtin_iterators_match_between_engines() {
        let module = verified(
            vec![Constant::Int32(8)],
            vec![entry_function(
                5,
                vec![
                    Instruction::CreateArray { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(1),
                    },
                    Instruction::GetIterator {
                        dst: reg(2),
                        src: reg(0),
                        kind: IteratorKind::Sync,
                    },
                    Instruction::IteratorNext {
                        done: reg(3),
                        value: reg(4),
                        iterator: reg(2),
                    },
                    Instruction::Return { value: reg(4) },
                ],
            )],
        );

        assert_eq!(assert_parity(&module, || SilentHost), Value::int32(8));
    }

    #[test]
    fn bound_calls_match_between_engines() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("bind")),
                Constant::String(EcmaString::encode("marker")),
                Constant::String(EcmaString::encode("0")),
                Constant::String(EcmaString::encode("1")),
                Constant::Int32(7),
                Constant::Int32(1),
                Constant::Int32(2),
            ],
            vec![
                entry_function(
                    8,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(0),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(0),
                            key: reg(1),
                        },
                        Instruction::CreateObject { dst: reg(3) },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(4),
                        },
                        Instruction::SetProperty {
                            object: reg(3),
                            key: reg(4),
                            value: reg(6),
                        },
                        Instruction::CreateArray { dst: reg(5) },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(5),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::Call {
                            dst: reg(7),
                            callee: reg(2),
                            this_value: reg(0),
                            arguments: reg(5),
                        },
                        Instruction::CreateArray { dst: reg(5) },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(6),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::Call {
                            dst: reg(7),
                            callee: reg(7),
                            this_value: reg(3),
                            arguments: reg(5),
                        },
                        Instruction::Return { value: reg(7) },
                    ],
                ),
                receiver_sum_function(),
            ],
        );

        assert_eq!(
            assert_parity(&module, || SilentHost),
            crate::number_value(10.0)
        );
    }

    #[test]
    fn applied_calls_match_between_engines() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("apply")),
                Constant::String(EcmaString::encode("marker")),
                Constant::String(EcmaString::encode("0")),
                Constant::String(EcmaString::encode("1")),
                Constant::Int32(7),
                Constant::Int32(1),
                Constant::Int32(2),
                Constant::String(EcmaString::encode("length")),
                Constant::Undefined,
            ],
            vec![
                entry_function(
                    8,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(0),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(0),
                            key: reg(1),
                        },
                        Instruction::CreateObject { dst: reg(3) },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(4),
                        },
                        Instruction::SetProperty {
                            object: reg(3),
                            key: reg(4),
                            value: reg(6),
                        },
                        Instruction::CreateArray { dst: reg(5) },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(5),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(6),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::CreateArray { dst: reg(6) },
                        Instruction::ArrayPush {
                            array: reg(6),
                            value: reg(3),
                        },
                        Instruction::ArrayPush {
                            array: reg(6),
                            value: reg(5),
                        },
                        Instruction::Call {
                            dst: reg(7),
                            callee: reg(2),
                            this_value: reg(0),
                            arguments: reg(6),
                        },
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(0),
                            function: FunctionId::new(2),
                            captures: reg(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(0),
                            key: reg(1),
                        },
                        Instruction::CreateArray { dst: reg(6) },
                        Instruction::ArrayPush {
                            array: reg(6),
                            value: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(8),
                        },
                        Instruction::ArrayPush {
                            array: reg(6),
                            value: reg(4),
                        },
                        Instruction::Call {
                            dst: reg(4),
                            callee: reg(2),
                            this_value: reg(0),
                            arguments: reg(6),
                        },
                        Instruction::Binary {
                            dst: reg(7),
                            op: BinaryOp::Add,
                            left: reg(7),
                            right: reg(4),
                        },
                        Instruction::Return { value: reg(7) },
                    ],
                ),
                receiver_sum_function(),
                module_function(
                    0,
                    3,
                    vec![
                        Instruction::LoadArguments { dst: reg(0) },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(7),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(0),
                            key: reg(1),
                        },
                        Instruction::Return { value: reg(2) },
                    ],
                ),
            ],
        );

        assert_eq!(
            assert_parity(&module, || SilentHost),
            crate::number_value(10.0)
        );
    }

    #[test]
    fn bound_construction_matches_between_engines() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("bind")),
                Constant::String(EcmaString::encode("prototype")),
                Constant::String(EcmaString::encode("sum")),
                Constant::String(EcmaString::encode("0")),
                Constant::String(EcmaString::encode("1")),
                Constant::Int32(4),
                Constant::Int32(5),
                Constant::Int32(9),
                Constant::Undefined,
            ],
            vec![
                entry_function(
                    10,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(0),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateObject { dst: reg(2) },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(1),
                        },
                        Instruction::SetProperty {
                            object: reg(0),
                            key: reg(1),
                            value: reg(2),
                        },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(3),
                            object: reg(0),
                            key: reg(1),
                        },
                        Instruction::CreateObject { dst: reg(4) },
                        Instruction::CreateArray { dst: reg(5) },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(4),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(5),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::Call {
                            dst: reg(7),
                            callee: reg(3),
                            this_value: reg(0),
                            arguments: reg(5),
                        },
                        Instruction::CreateArray { dst: reg(5) },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(6),
                        },
                        Instruction::ArrayPush {
                            array: reg(5),
                            value: reg(6),
                        },
                        Instruction::Construct {
                            dst: reg(8),
                            callee: reg(7),
                            arguments: reg(5),
                        },
                        Instruction::LoadConst {
                            dst: reg(1),
                            constant: cid(2),
                        },
                        Instruction::GetProperty {
                            dst: reg(9),
                            object: reg(8),
                            key: reg(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(7),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(9),
                            right: reg(6),
                        },
                        Instruction::Binary {
                            dst: reg(6),
                            op: BinaryOp::InstanceOf,
                            left: reg(8),
                            right: reg(7),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::BitAnd,
                            left: reg(9),
                            right: reg(6),
                        },
                        Instruction::Return { value: reg(9) },
                    ],
                ),
                module_constructor(
                    0,
                    0,
                    6,
                    vec![
                        Instruction::LoadThis { dst: reg(0) },
                        Instruction::LoadArguments { dst: reg(1) },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(3),
                        },
                        Instruction::GetProperty {
                            dst: reg(3),
                            object: reg(1),
                            key: reg(2),
                        },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(4),
                        },
                        Instruction::GetProperty {
                            dst: reg(4),
                            object: reg(1),
                            key: reg(2),
                        },
                        Instruction::Binary {
                            dst: reg(3),
                            op: BinaryOp::Add,
                            left: reg(3),
                            right: reg(4),
                        },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(2),
                        },
                        Instruction::SetProperty {
                            object: reg(0),
                            key: reg(2),
                            value: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(8),
                        },
                        Instruction::Return { value: reg(5) },
                    ],
                ),
            ],
        );

        assert_eq!(assert_parity(&module, || SilentHost), Value::int32(1));
    }

    /// Tag 47 lowers to the explicit-newTarget helper with operands read in
    /// the pinned wire order (`callee`, `new_target`, `arguments`).
    #[test]
    fn construct_with_new_target_lowers_with_pinned_operand_order() {
        let module = verified(Vec::new(), vec![entry_function(5, vec![Instruction::Halt])]);
        let program = one_module_program(&module);
        let mut host = SilentHost;
        let entries = NoEntries;
        let engine = NativeEngine::new(&program, &entries, &mut host, Limits::default());
        let mut registers = [
            Value::int32(11),
            Value::int32(22),
            Value::int32(33),
            Value::int32(44),
            Value::UNINITIALIZED,
        ];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow =
            ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, registers.len() as u16);
        let frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let (call, dst) = engine.lower(
            Instruction::ConstructWithNewTarget {
                dst: reg(4),
                callee: reg(1),
                new_target: reg(2),
                arguments: reg(3),
            },
            &frame,
            0,
        );
        assert_eq!(
            call,
            HelperCall::ConstructWithNewTarget {
                callee: Value::int32(22),
                new_target: Value::int32(33),
                arguments: Value::int32(44),
            }
        );
        assert_eq!(dst, Some(4));
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    /// An explicit `new.target` distinct from the callee reaches the
    /// constructed activation in both engines: the constructor returns
    /// `new.target` (an object), so the construct result IS the explicit
    /// target.
    #[test]
    fn construct_with_new_target_delivers_explicit_target_to_both_engines() {
        let module = verified(
            Vec::new(),
            vec![
                entry_function(
                    6,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(1),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateClosure {
                            dst: reg(2),
                            function: FunctionId::new(2),
                            captures: reg(0),
                        },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(3),
                            callee: reg(1),
                            new_target: reg(2),
                            arguments: reg(0),
                        },
                        Instruction::Binary {
                            dst: reg(4),
                            op: BinaryOp::StrictEqual,
                            left: reg(3),
                            right: reg(2),
                        },
                        Instruction::Return { value: reg(4) },
                    ],
                ),
                // The constructed callee: return `new.target` (an object, so
                // it overrides the allocated instance verbatim).
                module_constructor(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::LoadNewTarget { dst: reg(0) },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
                // The explicit `new.target`: any object identity suffices.
                module_constructor(0, 1, 1, vec![Instruction::Return { value: reg(0) }]),
            ],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::TRUE);
    }

    /// Tag 47 over a bound callee keeps an explicit `new.target` distinct
    /// from the wrapper: the constructor still observes the explicit target,
    /// not the bound wrapper and not the flattened target.
    #[test]
    fn construct_with_new_target_preserves_explicit_target_through_bound_callee() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("bind")),
                Constant::Undefined,
            ],
            vec![
                entry_function(
                    8,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(1),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateClosure {
                            dst: reg(2),
                            function: FunctionId::new(2),
                            captures: reg(0),
                        },
                        // Bind the callee with a fixed receiver.
                        Instruction::LoadConst {
                            dst: reg(3),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(3),
                            object: reg(1),
                            key: reg(3),
                        },
                        Instruction::CreateArray { dst: reg(4) },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(1),
                        },
                        Instruction::ArrayPush {
                            array: reg(4),
                            value: reg(5),
                        },
                        Instruction::Call {
                            dst: reg(5),
                            callee: reg(3),
                            this_value: reg(1),
                            arguments: reg(4),
                        },
                        // Construct the bound callee with an explicit
                        // `new.target` distinct from the wrapper.
                        Instruction::CreateArray { dst: reg(4) },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(6),
                            callee: reg(5),
                            new_target: reg(2),
                            arguments: reg(4),
                        },
                        Instruction::Binary {
                            dst: reg(7),
                            op: BinaryOp::StrictEqual,
                            left: reg(6),
                            right: reg(2),
                        },
                        Instruction::Return { value: reg(7) },
                    ],
                ),
                // The bound target: return `new.target` (an object).
                module_constructor(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::LoadNewTarget { dst: reg(0) },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
                // The explicit `new.target`.
                module_constructor(0, 1, 1, vec![Instruction::Return { value: reg(0) }]),
            ],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::TRUE);
    }

    #[test]
    fn construct_with_new_target_forwards_intermediate_bound_wrapper_in_both_engines() {
        // B2 -> B1 -> Base newTarget matrix (interpreter/native parity):
        //   ConstructWithNT(B2, B2|B1|Base) -> Base
        //   ConstructWithNT(B2, Unrelated)  -> Unrelated
        //   Construct(B2)                   -> Base
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("bind")),
                Constant::Undefined,
            ],
            vec![
                entry_function(
                    14,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(1),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(11),
                            function: FunctionId::new(2),
                            captures: reg(0),
                        },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(1),
                            key: reg(2),
                        },
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(1),
                        },
                        Instruction::ArrayPush {
                            array: reg(3),
                            value: reg(4),
                        },
                        Instruction::Call {
                            dst: reg(5),
                            callee: reg(2),
                            this_value: reg(1),
                            arguments: reg(3),
                        },
                        // B2 = B1.bind(undefined)
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(0),
                        },
                        Instruction::GetProperty {
                            dst: reg(2),
                            object: reg(5),
                            key: reg(2),
                        },
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::ArrayPush {
                            array: reg(3),
                            value: reg(4),
                        },
                        Instruction::Call {
                            dst: reg(6),
                            callee: reg(2),
                            this_value: reg(5),
                            arguments: reg(3),
                        },
                        // ConstructWithNT(B2, B2) -> Base
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(6),
                            new_target: reg(6),
                            arguments: reg(3),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(1),
                        },
                        // ConstructWithNT(B2, B1) -> Base
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(6),
                            new_target: reg(5),
                            arguments: reg(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(1),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        // ConstructWithNT(B2, Base) -> Base
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(6),
                            new_target: reg(1),
                            arguments: reg(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(1),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        // ConstructWithNT(B2, Unrelated) -> Unrelated
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(6),
                            new_target: reg(11),
                            arguments: reg(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(11),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        // ordinary Construct(B2) -> Base
                        Instruction::CreateArray { dst: reg(3) },
                        Instruction::Construct {
                            dst: reg(7),
                            callee: reg(6),
                            arguments: reg(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(1),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        Instruction::Return { value: reg(8) },
                    ],
                ),
                module_constructor(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::LoadNewTarget { dst: reg(0) },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
                module_constructor(
                    0,
                    0,
                    1,
                    vec![
                        Instruction::LoadNewTarget { dst: reg(0) },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
            ],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::int32(1));
    }

    #[test]
    fn object_constructor_distinct_new_target_ignores_arguments_in_both_engines() {
        // Reflect-style Construct(Object, [value], customNewTarget) ignores value
        // and allocates under customNewTarget.prototype in both engines.
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("Object")),
                Constant::String(EcmaString::encode("prototype")),
                Constant::String(EcmaString::encode("marker")),
                Constant::Int32(42),
                Constant::Int32(7),
                Constant::String(EcmaString::encode("own")),
            ],
            vec![
                entry_function(
                    12,
                    vec![
                        Instruction::LoadGlobal {
                            dst: reg(0),
                            name: cid(0),
                        },
                        Instruction::CreateArray { dst: reg(1) },
                        Instruction::CreateClosure {
                            dst: reg(2),
                            function: FunctionId::new(1),
                            captures: reg(1),
                        },
                        // customNewTarget.prototype = { marker: 42 }
                        Instruction::CreateObject { dst: reg(3) },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(1),
                        },
                        Instruction::SetProperty {
                            object: reg(2),
                            key: reg(4),
                            value: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(2),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(3),
                        },
                        Instruction::SetProperty {
                            object: reg(3),
                            key: reg(4),
                            value: reg(5),
                        },
                        // existing object argument with own: 7
                        Instruction::CreateObject { dst: reg(6) },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(5),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(4),
                        },
                        Instruction::SetProperty {
                            object: reg(6),
                            key: reg(4),
                            value: reg(5),
                        },
                        Instruction::CreateArray { dst: reg(1) },
                        Instruction::ArrayPush {
                            array: reg(1),
                            value: reg(6),
                        },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(0),
                            new_target: reg(2),
                            arguments: reg(1),
                        },
                        // result !== existing argument
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::StrictNotEqual,
                            left: reg(7),
                            right: reg(6),
                        },
                        // result.marker === 42 via custom prototype
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(2),
                        },
                        Instruction::GetProperty {
                            dst: reg(9),
                            object: reg(7),
                            key: reg(4),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(9),
                            right: reg(5),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        // primitive argument path also ignores boxing
                        Instruction::CreateArray { dst: reg(1) },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(4),
                        },
                        Instruction::ArrayPush {
                            array: reg(1),
                            value: reg(5),
                        },
                        Instruction::ConstructWithNewTarget {
                            dst: reg(7),
                            callee: reg(0),
                            new_target: reg(2),
                            arguments: reg(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(4),
                            constant: cid(2),
                        },
                        Instruction::GetProperty {
                            dst: reg(9),
                            object: reg(7),
                            key: reg(4),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(3),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(9),
                            right: reg(5),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        // legacy tag-12 / ordinary Object still returns the object arg
                        Instruction::CreateArray { dst: reg(1) },
                        Instruction::ArrayPush {
                            array: reg(1),
                            value: reg(6),
                        },
                        Instruction::Construct {
                            dst: reg(7),
                            callee: reg(0),
                            arguments: reg(1),
                        },
                        Instruction::Binary {
                            dst: reg(9),
                            op: BinaryOp::StrictEqual,
                            left: reg(7),
                            right: reg(6),
                        },
                        Instruction::Binary {
                            dst: reg(8),
                            op: BinaryOp::BitAnd,
                            left: reg(8),
                            right: reg(9),
                        },
                        Instruction::Return { value: reg(8) },
                    ],
                ),
                // Placeholder explicit new_target body (never invoked).
                Function::new(
                    None,
                    0,
                    1,
                    1,
                    FunctionFlags::default(),
                    vec![Instruction::Return { value: reg(0) }],
                    Vec::new(),
                ),
            ],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::int32(1));
    }

    #[test]
    fn linked_entry_preserves_pending_throw_origin() {
        let program = trivial_program();
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &ThrowEntries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.pending_throw.set(Some(PendingThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::ReferenceError {
                operation: "fixture",
            },
        }));
        let error = engine.run_linked().unwrap_err();
        assert!(matches!(
            error,
            NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::UncaughtThrow {
                    origin: ThrowOrigin::ReferenceError {
                        operation: "fixture"
                    },
                    ..
                },
                ..
            })
        ));
    }

    #[test]
    fn linked_nested_engine_throw_reports_callee_site_at_entry() {
        let module = verified(
            Vec::new(),
            vec![
                entry_function(1, vec![Instruction::Halt, Instruction::Halt]),
                entry_function(1, vec![Instruction::Halt, Instruction::Halt]),
            ],
        );
        let program = one_module_program(&module);
        let entries = FaultSiteEntries::throwing(0, 1);
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let (callee, arguments) = {
            let mut machine = engine.machine.borrow_mut();
            let function_prototype = machine.intrinsics.function_prototype;
            let callee = machine
                .allocate(HeapEntry::Function {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                    captures: Vec::new(),
                    context: None,
                    properties: PropertyMap::default(),
                    prototype: Some(function_prototype),
                    extensible: true,
                })
                .expect("callee allocates");
            let array_prototype = machine.intrinsics.array_prototype;
            let arguments = machine
                .allocate(HeapEntry::Array {
                    kind: ArrayElementKind::for_elements(&[]),
                    elements: Vec::new(),
                    properties: PropertyMap::default(),
                    prototype: Some(array_prototype),
                    extensible: true,
                    length_writable: true,
                })
                .expect("arguments array allocates");
            (callee, arguments)
        };
        let mut registers = [Value::UNINITIALIZED; 1];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(
            std::ptr::null_mut(),
            0,
            0,
            registers.as_mut_ptr(),
            registers.len() as u16,
        );
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        engine.pending_throw.set(Some(PendingThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::ReferenceError {
                operation: "nested linked fixture",
            },
        }));
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::Call {
                        callee,
                        this_value: Value::UNDEFINED,
                        arguments,
                    },
                )
                .tag,
            CompletionTag::Throw
        );
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();

        let NativeError::Runtime(error) = engine.run_linked().unwrap_err() else {
            panic!("linked entry must propagate the nested engine throw");
        };
        assert_eq!(error.function, FunctionId::new(1));
        assert_eq!(error.pc, pc(1));
        assert!(matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                origin: ThrowOrigin::ReferenceError {
                    operation: "nested linked fixture"
                },
                ..
            }
        ));
    }

    #[test]
    fn linked_normal_entry_clears_fault_before_later_throw() {
        let module = verified(
            Vec::new(),
            vec![
                entry_function(1, vec![Instruction::Halt, Instruction::Halt]),
                entry_function(1, vec![Instruction::Halt, Instruction::Halt]),
            ],
        );
        let program = one_module_program(&module);
        let entries = FaultSiteEntries::throwing(0, 1);
        entries.entry_tag.set(CompletionTag::Normal);
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.pending_fault.set(Some((
            crate::RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            1,
        )));

        engine
            .invoke_linked_entry(ModuleId::new(0))
            .expect("normal entry completes");
        assert!(engine.pending_fault.get().is_none());

        entries.entry_tag.set(CompletionTag::Throw);
        entries.entry_pc.set(1);
        engine.pending_throw.set(Some(PendingThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::ReferenceError {
                operation: "later entry fixture",
            },
        }));
        let NativeError::Runtime(error) = engine.invoke_linked_entry(ModuleId::new(0)).unwrap_err()
        else {
            panic!("later entry must throw");
        };
        assert_eq!(error.function, FunctionId::new(0));
        assert_eq!(error.pc, pc(1));
    }

    #[test]
    fn stale_pending_throw_cannot_replace_a_new_bytecode_throw() {
        let program = trivial_program();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &NoEntries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.pending_throw.set(Some(PendingThrow {
            value: Value::int32(1),
            origin: ThrowOrigin::ReferenceError { operation: "stale" },
        }));

        assert_eq!(
            engine.take_matching_throw(Value::int32(2)),
            (Value::int32(2), ThrowOrigin::Bytecode)
        );
        assert!(engine.pending_throw.get().is_none());
    }

    #[test]
    fn linked_entry_sources_pending_runtime_fatal_kind() {
        let program = trivial_program();
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &FatalEntries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine
            .pending_fatal_kind
            .set(Some(RuntimeErrorKind::InvalidValue { value: Value::NULL }));
        let error = engine.run_linked().unwrap_err();
        assert!(matches!(
            error,
            NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::InvalidValue { value },
                ..
            }) if value == Value::NULL
        ));
    }

    #[test]
    fn nested_linked_unknown_tuple_remains_abi_error() {
        let module = verified(
            Vec::new(),
            vec![
                entry_function(1, vec![Instruction::Halt]),
                entry_function(1, vec![Instruction::Halt]),
            ],
        );
        let program = one_module_program(&module);
        let entries = FailingEntries::default();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let outcome = engine.invoke_runtime(
            crate::RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        );
        assert!(matches!(outcome, InvokeOutcome::Fatal));
        assert!(matches!(
            engine.pending_abi_error.take(),
            Some(AbiError::UnknownFunction {
                module_id: 0,
                function_id: 1
            })
        ));
    }

    #[test]
    fn linked_abi_failure_leaves_module_retryable() {
        let program = trivial_program();
        let entries = FailingEntries::default();
        let mut host = SilentHost;
        let mut engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.machine.borrow_mut().instantiate_modules().unwrap();
        for _ in 0..2 {
            assert!(matches!(
                engine.evaluate_linked_module(ModuleId::new(0)),
                Err(NativeError::Abi(AbiError::UnknownFunction {
                    module_id: 0,
                    function_id: 0
                }))
            ));
        }
    }

    #[test]
    fn linked_backend_routes_dynamic_targets_away_from_entry_table() {
        let root = one_module_program(&verified(
            Vec::new(),
            vec![entry_function(1, vec![Instruction::Halt])],
        ));
        let script = Arc::new(one_module_program(&verified(
            vec![Constant::Int32(42)],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        )));
        let entries = RecordingEntries::default();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &root,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        engine.machine.borrow_mut().instantiate_modules().unwrap();
        let module = engine
            .machine
            .borrow_mut()
            .install_script_reserving(script, 0, 0)
            .unwrap();

        let outcome = engine.invoke_runtime(
            crate::RuntimeFunction {
                module,
                function: FunctionId::new(0),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        );
        assert!(matches!(outcome, InvokeOutcome::Value(value) if value == Value::int32(42)));
        assert!(entries.invoked.borrow().is_empty());
    }
    fn generator_program(code: Vec<Instruction>, constants: Vec<Constant>) -> Program<Verified> {
        let generator = Function::new(
            None,
            0,
            0,
            3,
            FunctionFlags {
                is_async: false,
                is_generator: true,
                is_constructable: false,
                ..FunctionFlags::default()
            },
            code,
            Vec::new(),
        );
        one_module_program(&verified(
            constants,
            vec![entry_function(1, vec![Instruction::Halt]), generator],
        ))
    }

    fn yielding_generator_program() -> Program<Verified> {
        generator_program(
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Suspend {
                    dst: reg(1),
                    src: reg(0),
                    resume: pc(2),
                    mode: reg(2),
                },
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(1),
                },
                Instruction::Suspend {
                    dst: reg(1),
                    src: reg(0),
                    resume: pc(4),
                    mode: reg(2),
                },
                Instruction::Return { value: reg(1) },
            ],
            vec![Constant::Int32(4), Constant::Int32(5)],
        )
    }

    fn invoke_test_generator<H: Host>(engine: &NativeEngine<'_, '_, H>) -> Value {
        match engine.invoke_runtime(
            crate::RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        ) {
            InvokeOutcome::Value(generator) => generator,
            _ => panic!("generator call must return its lazy generator object"),
        }
    }

    fn assert_iterator_result<H: Host>(
        engine: &NativeEngine<'_, '_, H>,
        outcome: InvokeOutcome,
        expected_value: Value,
        expected_done: bool,
    ) {
        let result = match outcome {
            InvokeOutcome::Value(result) => result,
            _ => panic!("generator next must return an iterator result"),
        };
        let mut machine = engine.machine.borrow_mut();
        let value = machine
            .get_named_property(result, "value")
            .expect("iterator result has value");
        let done = machine
            .get_named_property(result, "done")
            .expect("iterator result has done");
        assert_eq!(value, expected_value);
        assert_eq!(done, Value::boolean(expected_done));
    }

    #[test]
    fn reference_generator_is_lazy_yields_resumes_and_completes_stickily() {
        let program = yielding_generator_program();
        let mut host = SilentHost;
        let entries = NoEntries;
        let engine = NativeEngine::new(&program, &entries, &mut host, Limits::default());
        let generator = invoke_test_generator(&engine);

        {
            let machine = engine.machine.borrow();
            let index = machine.runtime_slot(generator).unwrap().unwrap();
            assert!(matches!(
                &machine.heap[index],
                HeapEntry::Generator {
                    state: GeneratorState::SuspendedStart(_),
                    ..
                }
            ));
        }

        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(999))),
            Value::int32(4),
            false,
        );
        {
            let machine = engine.machine.borrow();
            let index = machine.runtime_slot(generator).unwrap().unwrap();
            let HeapEntry::Generator {
                state: GeneratorState::Suspended(activation),
                ..
            } = &machine.heap[index]
            else {
                panic!("generator must retain its suspended activation");
            };
            assert_eq!(activation.resume_token, 2);
            assert_eq!(activation.registers[0], Value::int32(4));
        }

        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(99))),
            Value::int32(5),
            false,
        );
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(7))),
            Value::int32(7),
            true,
        );
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(8))),
            Value::UNDEFINED,
            true,
        );
        let machine = engine.machine.borrow();
        assert_eq!(machine.live_registers, 0);
        assert_eq!(machine.native_depth, 0);
    }

    #[test]
    fn reference_generator_throw_completes_and_preserves_value_and_origin() {
        let program = generator_program(
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                Instruction::Throw { value: reg(0) },
            ],
            vec![Constant::Int32(42)],
        );
        let mut host = SilentHost;
        let entries = NoEntries;
        let engine = NativeEngine::new(&program, &entries, &mut host, Limits::default());
        let generator = invoke_test_generator(&engine);
        assert!(matches!(
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED)),
            InvokeOutcome::Threw(value, ThrowOrigin::Bytecode) if value == Value::int32(42)
        ));
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED)),
            Value::UNDEFINED,
            true,
        );
        let machine = engine.machine.borrow();
        assert_eq!(machine.live_registers, 0);
        assert_eq!(machine.native_depth, 0);
    }

    #[test]
    fn suspended_reference_generator_registers_enforce_the_global_ceiling() {
        let program = yielding_generator_program();
        let mut host = SilentHost;
        let entries = NoEntries;
        let limits = Limits {
            max_total_registers: 3,
            ..Limits::default()
        };
        let engine = NativeEngine::new(&program, &entries, &mut host, limits);
        let first = invoke_test_generator(&engine);
        let second = invoke_test_generator(&engine);
        assert_iterator_result(
            &engine,
            engine.resume_generator(first, GeneratorCompletion::Normal(Value::UNDEFINED)),
            Value::int32(4),
            false,
        );
        assert!(matches!(
            engine.resume_generator(second, GeneratorCompletion::Normal(Value::UNDEFINED)),
            InvokeOutcome::Fatal
        ));
        assert!(matches!(
            engine.pending_fatal_kind.take(),
            Some(RuntimeErrorKind::RegisterLimitExceeded { limit: 3 })
        ));
    }

    #[derive(Clone, Copy)]
    struct GeneratorEntryStep {
        token: u32,
        next_token: u32,
        tag: CompletionTag,
        value: Value,
    }

    struct GeneratorEntries {
        steps: Vec<GeneratorEntryStep>,
        call: Cell<usize>,
        handles: Cell<Option<*mut Value>>,
    }

    impl GeneratorEntries {
        fn yielding() -> Self {
            Self {
                steps: vec![
                    GeneratorEntryStep {
                        token: 0,
                        next_token: 2,
                        tag: CompletionTag::Suspend,
                        value: Value::int32(4),
                    },
                    GeneratorEntryStep {
                        token: 2,
                        next_token: 4,
                        tag: CompletionTag::Suspend,
                        value: Value::int32(5),
                    },
                    GeneratorEntryStep {
                        token: 4,
                        next_token: 4,
                        tag: CompletionTag::Normal,
                        value: Value::int32(7),
                    },
                ],
                call: Cell::new(0),
                handles: Cell::new(None),
            }
        }

        fn terminal(tag: CompletionTag, value: Value) -> Self {
            Self {
                steps: vec![GeneratorEntryStep {
                    token: 0,
                    next_token: 1,
                    tag,
                    value,
                }],
                call: Cell::new(0),
                handles: Cell::new(None),
            }
        }
    }

    impl NativeEntryTable for GeneratorEntries {
        fn program_bytes(&self) -> &[u8] {
            &[]
        }

        fn invoke(
            &self,
            module_id: u32,
            function_id: u32,
            frame: &mut ShadowFrame,
            out: &mut Completion,
        ) -> Result<CompletionTag, AbiError> {
            assert_eq!(module_id, 0);
            assert_eq!(function_id, 1);
            let call = self.call.get();
            let step = self.steps[call];
            self.call.set(call + 1);
            assert_eq!(frame.bytecode_pc, step.token);
            match self.handles.get() {
                Some(handles) => assert_eq!(
                    handles, frame.handles,
                    "linked resumes must reuse the saved register allocation"
                ),
                None => self.handles.set(Some(frame.handles)),
            }
            frame.bytecode_pc = step.next_token;
            *out = Completion::new(step.value);
            Ok(step.tag)
        }
    }

    #[test]
    fn linked_generator_reuses_saved_registers_and_dispatches_resume_tokens() {
        let program = yielding_generator_program();
        let entries = GeneratorEntries::yielding();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let generator = invoke_test_generator(&engine);
        assert_eq!(entries.call.get(), 0, "generator call is lazy");
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(999))),
            Value::int32(4),
            false,
        );
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(99))),
            Value::int32(5),
            false,
        );
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::int32(7))),
            Value::int32(7),
            true,
        );
        assert_iterator_result(
            &engine,
            engine.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED)),
            Value::UNDEFINED,
            true,
        );
        assert_eq!(entries.call.get(), 3);
        let machine = engine.machine.borrow();
        assert_eq!(machine.live_registers, 0);
        assert_eq!(machine.native_depth, 0);
    }

    #[test]
    fn linked_resume_value_dispatch_consumes_the_sent_value_once() {
        let program = yielding_generator_program();
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let resumed_value = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("resume")))
            .unwrap();
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: Some(GeneratorCompletion::Normal(resumed_value)),
            target: test_target(),
        });
        let mut registers = vec![Value::UNINITIALIZED, Value::UNINITIALIZED];
        engine.push_native_roots(&registers);
        engine.machine.borrow_mut().set_gc_watermarks_for_test(0, 0);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 2, 0, registers.as_mut_ptr(), 2);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let resumed = engine.dispatch(&mut frame, HelperCall::ResumeValue);
        assert_eq!(resumed, HelperResult::normal(resumed_value));
        assert!(
            engine
                .machine
                .borrow()
                .runtime_slot(resumed_value)
                .unwrap()
                .is_some()
        );
        let mode = engine.dispatch(&mut frame, HelperCall::ResumeMode);
        assert_eq!(mode, HelperResult::normal(Value::int32(0)));
        assert!(
            engine
                .activations
                .borrow()
                .last()
                .unwrap()
                .pending_resume
                .is_none()
        );
        assert_eq!(
            engine.dispatch(&mut frame, HelperCall::ResumeValue).tag,
            CompletionTag::FatalTrap
        );
        engine
            .activations
            .borrow_mut()
            .last_mut()
            .expect("active generator frame")
            .pending_resume = Some(GeneratorCompletion::Throw {
            value: Value::int32(42),
            origin: ThrowOrigin::Bytecode,
        });
        let thrown = engine.dispatch(&mut frame, HelperCall::ResumeValue);
        assert_eq!(thrown, HelperResult::throw(Value::int32(42)));
        assert_eq!(
            engine.pending_throw.get().map(|p| (p.value, p.origin)),
            Some((Value::int32(42), ThrowOrigin::Bytecode))
        );
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn linked_generator_throw_and_fatal_release_once_and_complete_stickily() {
        for (tag, expected_throw) in [
            (CompletionTag::Throw, true),
            (CompletionTag::FatalTrap, false),
        ] {
            let program = generator_program(vec![Instruction::Halt], Vec::new());
            let entries = GeneratorEntries::terminal(tag, Value::int32(42));
            let mut host = SilentHost;
            let engine = NativeEngine::build(
                &program,
                &entries,
                &mut host,
                Limits::default(),
                Backend::Linked,
                bamts_cancel::CancellationToken::new(),
            );
            let generator = invoke_test_generator(&engine);
            let outcome =
                engine.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED));
            if expected_throw {
                assert!(matches!(
                    outcome,
                    InvokeOutcome::Threw(value, ThrowOrigin::Bytecode)
                        if value == Value::int32(42)
                ));
            } else {
                assert!(matches!(outcome, InvokeOutcome::Fatal));
            }
            assert_iterator_result(
                &engine,
                engine.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED)),
                Value::UNDEFINED,
                true,
            );
            let machine = engine.machine.borrow();
            assert_eq!(machine.live_registers, 0);
            assert_eq!(machine.native_depth, 0);
        }
    }

    #[test]
    fn linked_array_extend_drives_generator_through_linked_entries() {
        let program = yielding_generator_program();
        let entries = GeneratorEntries::yielding();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let generator = invoke_test_generator(&engine);
        let array = {
            let prototype = engine.machine.borrow().intrinsics.array_prototype;
            engine
                .machine
                .borrow_mut()
                .allocate(HeapEntry::Array {
                    kind: ArrayElementKind::for_elements(&[]),
                    elements: Vec::new(),
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                    length_writable: true,
                })
                .unwrap()
        };
        assert!(matches!(
            engine.array_extend_active(array, generator),
            InvokeOutcome::Value(value) if value == Value::UNDEFINED
        ));
        assert_eq!(
            engine.machine.borrow().arguments_from_array(array).unwrap(),
            vec![Value::int32(4), Value::int32(5)]
        );
        assert_eq!(entries.call.get(), 3);
    }
    #[test]
    fn create_cell_helper_seeds_tdz_and_preserves_reference_error_origin() {
        let program = trivial_program();
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Reference,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 1);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let created = engine.dispatch(&mut frame, HelperCall::CreateCell);
        assert_eq!(created.tag, CompletionTag::Normal);
        let read = engine.dispatch(
            &mut frame,
            HelperCall::GetProperty {
                object: created.value,
                key: Value::int32(0),
                site: u32::MAX,
            },
        );
        assert_eq!(read.tag, CompletionTag::Throw);
        assert!(matches!(
            engine.pending_throw.get(),
            Some(PendingThrow {
                origin: ThrowOrigin::ReferenceError { .. },
                ..
            })
        ));
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn native_root_snapshot_retains_activation_values_through_collection() {
        let program = trivial_program();
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let values = {
            let mut machine = engine.machine.borrow_mut();
            [
                "register",
                "this",
                "new.target",
                "argument",
                "arguments",
                "resume",
                "throw",
            ]
            .map(|text| {
                machine
                    .allocate(HeapEntry::String(EcmaString::encode(text)))
                    .unwrap()
            })
        };
        engine.activations.borrow_mut().push(Activation {
            this_value: values[1],
            new_target: values[2],
            args: vec![values[3]],
            arguments_object: Some(values[4]),
            pending_resume: Some(GeneratorCompletion::Normal(values[5])),
            target: test_target(),
        });
        engine.pending_throw.set(Some(PendingThrow {
            value: values[6],
            origin: ThrowOrigin::Bytecode,
        }));
        let mut registers = [values[0]];
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(
            std::ptr::null_mut(),
            0,
            0,
            registers.as_mut_ptr(),
            registers.len() as u16,
        );
        let frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        engine.machine.borrow_mut().set_gc_watermarks_for_test(0, 0);
        engine.prepare_native_helper(&frame);

        for value in values {
            assert!(
                engine
                    .machine
                    .borrow()
                    .runtime_slot(value)
                    .unwrap()
                    .is_some()
            );
        }
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
        assert!(engine.machine.borrow().native_roots.is_empty());
    }

    #[derive(Default)]
    struct ImportMetaHost {
        seen: Vec<EcmaString>,
    }

    impl Host for ImportMetaHost {
        fn import_meta_url(&mut self, module_name: &EcmaString) -> EcmaString {
            self.seen.push(module_name.clone());
            EcmaString::encode("host://modules/entry.mjs")
        }
    }

    #[test]
    fn import_meta_matches_interpreter_with_stable_identity_and_host_url() {
        let program = linked(
            vec![program_module(
                "entry",
                vec![
                    Constant::String(EcmaString::encode("url")),
                    Constant::String(EcmaString::encode("host://modules/entry.mjs")),
                ],
                vec![entry_function(
                    7,
                    vec![
                        Instruction::LoadImportMeta { dst: reg(0) },
                        Instruction::LoadImportMeta { dst: reg(1) },
                        Instruction::Binary {
                            dst: reg(2),
                            op: BinaryOp::StrictEqual,
                            left: reg(0),
                            right: reg(1),
                        },
                        Instruction::LoadConst {
                            dst: reg(3),
                            constant: cid(1),
                        },
                        Instruction::GetProperty {
                            dst: reg(4),
                            object: reg(0),
                            key: reg(3),
                        },
                        Instruction::LoadConst {
                            dst: reg(5),
                            constant: cid(2),
                        },
                        Instruction::Binary {
                            dst: reg(6),
                            op: BinaryOp::StrictEqual,
                            left: reg(4),
                            right: reg(5),
                        },
                        Instruction::Return { value: reg(6) },
                    ],
                )],
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )],
            0,
        );
        assert!(program.modules()[0].edges.is_empty());
        let limits = Limits::default();
        let mut interpreter_host = ImportMetaHost::default();
        let interpreter = Machine::new(&program, &mut interpreter_host, limits.clone())
            .run()
            .unwrap();
        let mut native_host = ImportMetaHost::default();
        let native = NativeEngine::new(&program, &NoEntries, &mut native_host, limits)
            .run()
            .unwrap();
        assert_eq!(native, interpreter);
        assert_eq!(native.entry_registers[0], native.entry_registers[1]);
        assert_eq!(native.entry_registers[2], Value::TRUE);
        assert_eq!(native.value, Value::TRUE);
        assert_eq!(interpreter_host.seen, vec![EcmaString::encode("entry")]);
        assert_eq!(native_host.seen, vec![EcmaString::encode("entry")]);
    }

    #[test]
    fn native_matches_interpreter_on_to_object_and_nullish_throw() {
        let module = verified(
            vec![Constant::Int32(7)],
            vec![entry_function(
                5,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::ToObject {
                        dst: reg(1),
                        src: reg(0),
                    },
                    Instruction::CreateObject { dst: reg(2) },
                    Instruction::ToObject {
                        dst: reg(3),
                        src: reg(2),
                    },
                    Instruction::Binary {
                        dst: reg(4),
                        op: BinaryOp::StrictEqual,
                        left: reg(2),
                        right: reg(3),
                    },
                    Instruction::Return { value: reg(4) },
                ],
            )],
        );
        assert_eq!(assert_parity(&module, || SilentHost), Value::TRUE);

        let nullish = verified(
            vec![Constant::Null],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::ToObject {
                        dst: reg(1),
                        src: reg(0),
                    },
                    Instruction::Halt,
                ],
            )],
        );
        let error = assert_program_parity(&one_module_program(&nullish))
            .expect_err("nullish ToObject throws");
        assert!(matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                origin: ThrowOrigin::TypeError { .. },
                ..
            }
        ));
    }

    #[test]
    fn import_dynamic_instruction_matches_interpreter_and_native_engine() {
        let root = program_module(
            "root",
            vec![Constant::String(EcmaString::encode("./target"))],
            vec![entry_function(
                2,
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(1),
                    },
                    Instruction::ImportDynamic {
                        dst: reg(1),
                        specifier: reg(0),
                    },
                    Instruction::Return { value: reg(1) },
                ],
            )],
            vec![Edge {
                specifier: cid(1),
                target: EdgeTarget::Local(ModuleId::new(1)),
                kind: EdgeKind::Dynamic,
            }],
            Vec::new(),
            Vec::new(),
        );
        let target = program_module(
            "target",
            Vec::new(),
            vec![entry_function(1, vec![Instruction::Halt])],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );

        let execution = assert_program_parity(&linked(vec![root, target], 0))
            .expect("ImportDynamic matches the interpreter and native helper path");
        assert_eq!(execution.value, execution.entry_registers[1]);
        assert_ne!(execution.value, Value::UNDEFINED);
    }

    fn outside_engine_loop_module(instruction: Instruction) -> Module<Verified> {
        let body = Function::new(
            None,
            0,
            0,
            2,
            FunctionFlags::default(),
            vec![
                Instruction::LoadConst {
                    dst: reg(0),
                    constant: cid(0),
                },
                instruction,
                Instruction::Return { value: reg(0) },
            ],
            Vec::new(),
        );
        verified(
            vec![Constant::Undefined],
            vec![
                entry_function(
                    3,
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(1),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::LoadConst {
                            dst: reg(2),
                            constant: cid(0),
                        },
                        Instruction::Call {
                            dst: reg(0),
                            callee: reg(1),
                            this_value: reg(2),
                            arguments: reg(0),
                        },
                        Instruction::Return { value: reg(0) },
                    ],
                ),
                body,
            ],
        )
    }

    #[test]
    fn suspend_and_await_outside_engine_loop_preserve_origin_parity() {
        for (instruction, operation) in [
            (
                Instruction::Suspend {
                    dst: reg(0),
                    src: reg(0),
                    resume: pc(2),
                    mode: reg(1),
                },
                "suspend outside an engine-owned event loop",
            ),
            (
                Instruction::Await {
                    dst: reg(0),
                    src: reg(0),
                    resume: pc(2),
                },
                "await outside an engine-owned event loop",
            ),
        ] {
            let module = outside_engine_loop_module(instruction);
            let program = one_module_program(&module);

            let expected = |error: &RuntimeError, operation: &'static str| {
                assert_eq!(error.function, FunctionId::new(1));
                assert_eq!(error.pc, pc(1));
                assert_eq!(
                    error.kind,
                    RuntimeErrorKind::UncaughtThrow {
                        value: Value::UNDEFINED,
                        origin: ThrowOrigin::TypeError { operation },
                        constructor_name: None,
                        message: None,
                    }
                );
            };

            let mut interpreter_host = SilentHost;
            let interpreter_error =
                Machine::new(&program, &mut interpreter_host, Limits::default())
                    .run()
                    .unwrap_err();
            expected(&interpreter_error, operation);

            let mut reference_host = SilentHost;
            let reference_error =
                NativeEngine::new(&program, &NoEntries, &mut reference_host, Limits::default())
                    .run()
                    .unwrap_err();
            expected(&reference_error, operation);
        }
    }

    // -- Caught engine-origin materialization --------------------------------

    /// Asserts the value is a realm-intrinsic error object: prototype-supplied
    /// `name` and an own `message`, never resolved through user globals.
    fn assert_intrinsic_error<H: Host>(
        machine: &mut Machine<'_, H>,
        error: Value,
        name: &str,
        message: &str,
    ) {
        let name_value = machine.get_named_property(error, "name").unwrap();
        assert!(
            machine
                .string_value(name_value)
                .is_some_and(|text| text.eq_ascii(name))
        );
        let message_value = machine.get_named_property(error, "message").unwrap();
        assert!(
            machine
                .string_value(message_value)
                .is_some_and(|text| text.eq_ascii(message))
        );
    }

    /// Entry shadows the user global `ReferenceError`, loads a missing global
    /// under a covering handler, and returns the caught value. Constants:
    /// 0 = shadow payload, 1 = "ReferenceError", 2 = the missing global's name.
    fn caught_missing_global_module() -> Module<Verified> {
        verified(
            vec![
                Constant::Int32(7),
                Constant::String(EcmaString::encode("ReferenceError")),
                Constant::String(EcmaString::encode("missing_global")),
            ],
            vec![Function::new(
                None,
                0,
                0,
                3,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadConst {
                        dst: reg(0),
                        constant: cid(0),
                    },
                    Instruction::StoreGlobal {
                        name: cid(1),
                        value: reg(0),
                    },
                    Instruction::LoadGlobal {
                        dst: reg(1),
                        name: cid(2),
                    },
                    Instruction::Halt,
                    Instruction::Return { value: reg(2) },
                ],
                vec![ExceptionHandler {
                    start: pc(2),
                    end: pc(3),
                    handler: pc(4),
                    catch_register: reg(2),
                }],
            )],
        )
    }

    #[test]
    fn caught_missing_global_materializes_intrinsic_reference_error() {
        let module = caught_missing_global_module();
        let program = one_module_program(&module);

        // The interpreter is the caught-value oracle.
        let mut interpreter_host = SilentHost;
        let mut interpreter = Machine::new(&program, &mut interpreter_host, Limits::default());
        let interpreter_execution =
            run_interpreter_to_quiescence(&mut interpreter).expect("interpreter catches");
        assert_intrinsic_error(
            &mut interpreter,
            interpreter_execution.value,
            "ReferenceError",
            "global is not defined",
        );

        // The reference native driver catches through `raise` and must agree,
        // even though the user global `ReferenceError` is shadowed.
        let mut reference_host = SilentHost;
        let reference =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, Limits::default());
        let reference_execution =
            run_reference_to_quiescence(&reference).expect("reference native catches");
        assert!(
            reference_execution.value != Value::int32(7),
            "the shadow user global is never consulted"
        );
        assert_intrinsic_error(
            &mut reference.machine.borrow_mut(),
            reference_execution.value,
            "ReferenceError",
            "global is not defined",
        );

        // The linked backend catches through the dispatch postprocessor. The
        // recorded frame pc stands in for the pc generated code writes before
        // each instruction; dispatch is the same seam the helpers call.
        let mut linked_host = SilentHost;
        let linked = NativeEngine::build(
            &program,
            &NoEntries,
            &mut linked_host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED; 3];
        linked.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        linked.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 2, 0, handles, 3);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let result = linked.dispatch(&mut frame, HelperCall::LoadGlobal { name: 2 });
        assert_eq!(result.tag, CompletionTag::Throw);
        assert_ne!(
            result.value,
            Value::UNDEFINED,
            "a covered lazy engine throw is materialized before generated code binds it"
        );
        assert!(
            linked.pending_throw.get().is_none(),
            "a caught throw consumes its pending metadata"
        );
        assert_intrinsic_error(
            &mut linked.machine.borrow_mut(),
            result.value,
            "ReferenceError",
            "global is not defined",
        );
        linked.pop_native_roots();
        linked.activations.borrow_mut().pop();
    }

    #[test]
    fn materialize_catch_value_covers_every_origin_and_preserves_identity() {
        let program = trivial_program();
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &NoEntries,
            &mut host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 1);
        let frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();

        for (origin, name) in [
            (ThrowOrigin::TypeError { operation: "op" }, "TypeError"),
            (ThrowOrigin::RangeError { operation: "op" }, "RangeError"),
            (
                ThrowOrigin::ReferenceError { operation: "op" },
                "ReferenceError",
            ),
            (ThrowOrigin::UriError { operation: "op" }, "URIError"),
        ] {
            let value = engine
                .materialize_catch_value(&frame, test_target(), 0, Value::UNDEFINED, origin)
                .expect("origin materializes");
            assert_ne!(value, Value::UNDEFINED);
            assert_intrinsic_error(&mut engine.machine.borrow_mut(), value, name, "op");
        }

        // Bytecode `undefined` stays exactly undefined.
        assert_eq!(
            engine
                .materialize_catch_value(
                    &frame,
                    test_target(),
                    0,
                    Value::UNDEFINED,
                    ThrowOrigin::Bytecode,
                )
                .unwrap(),
            Value::UNDEFINED
        );

        // A supplied non-undefined engine-origin value keeps exact identity.
        let supplied = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: None,
                boxed_primitive: None,
                extensible: true,
            })
            .unwrap();
        assert_eq!(
            engine
                .materialize_catch_value(
                    &frame,
                    test_target(),
                    0,
                    supplied,
                    ThrowOrigin::TypeError { operation: "op" },
                )
                .unwrap(),
            supplied
        );

        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    /// Entry loads a missing global with no covering handler.
    fn uncaught_missing_global_module() -> Module<Verified> {
        verified(
            vec![Constant::String(EcmaString::encode("missing_global"))],
            vec![entry_function(
                1,
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        )
    }

    #[test]
    fn uncaught_engine_throw_stays_lazy_even_with_zero_heap_slots() {
        let limits = || Limits {
            max_heap_slots: 0,
            ..Limits::default()
        };
        let expected = |error: &RuntimeError| {
            assert_eq!(error.function, FunctionId::new(0));
            assert_eq!(error.pc, pc(0));
            assert_eq!(
                error.kind,
                RuntimeErrorKind::UncaughtThrow {
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::ReferenceError {
                        operation: "global is not defined",
                    },
                    constructor_name: None,
                    message: Some(EcmaString::encode("missing_global is not defined")),
                }
            );
        };

        let program = one_module_program(&uncaught_missing_global_module());

        let mut interpreter_host = SilentHost;
        let interpreter_error = Machine::new(&program, &mut interpreter_host, limits())
            .run()
            .unwrap_err();
        expected(&interpreter_error);

        // The reference native driver never materializes without a handler, so
        // the zero slot budget is irrelevant on the uncaught path.
        let mut reference_host = SilentHost;
        let reference_error =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, limits())
                .run()
                .unwrap_err();
        expected(&reference_error);

        // The linked postprocessor likewise leaves an uncovered throw — value
        // and pending metadata — untouched.
        let mut linked_host = SilentHost;
        let linked = NativeEngine::build(
            &program,
            &NoEntries,
            &mut linked_host,
            limits(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED; 1];
        linked.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        linked.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, 1);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let result = linked.dispatch(&mut frame, HelperCall::LoadGlobal { name: 0 });
        assert_eq!(result.tag, CompletionTag::Throw);
        assert_eq!(result.value, Value::UNDEFINED);
        assert!(matches!(
            linked.pending_throw.get(),
            Some(PendingThrow {
                value: Value::UNDEFINED,
                origin: ThrowOrigin::ReferenceError {
                    operation: "global is not defined",
                },
            })
        ));
        linked.pop_native_roots();
        linked.activations.borrow_mut().pop();
    }

    /// Entry faults on a covered missing-global load; the handler returns a
    /// sentinel, so a returned value would prove the catch block ran.
    fn caught_missing_global_sentinel_module() -> Module<Verified> {
        verified(
            vec![
                Constant::String(EcmaString::encode("missing_global")),
                Constant::Int32(99),
            ],
            vec![Function::new(
                None,
                0,
                0,
                3,
                FunctionFlags::default(),
                vec![
                    Instruction::LoadGlobal {
                        dst: reg(0),
                        name: cid(0),
                    },
                    Instruction::Halt,
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::Return { value: reg(2) },
                ],
                vec![ExceptionHandler {
                    start: pc(0),
                    end: pc(1),
                    handler: pc(2),
                    catch_register: reg(1),
                }],
            )],
        )
    }

    #[test]
    fn failed_materialization_bypasses_the_catch_with_an_exact_sourced_fatal() {
        let limits = || Limits {
            max_heap_slots: 0,
            ..Limits::default()
        };
        let expected = |error: &RuntimeError| {
            assert_eq!(error.function, FunctionId::new(0));
            assert_eq!(error.pc, pc(0));
            assert_eq!(
                error.kind,
                RuntimeErrorKind::HeapSlotLimitExceeded { limit: 0 }
            );
        };

        let program = one_module_program(&caught_missing_global_sentinel_module());

        // Interpreter oracle: the catch never runs; the allocation failure is
        // fatal and sourced at the faulting instruction.
        let mut interpreter_host = SilentHost;
        let interpreter_error = Machine::new(&program, &mut interpreter_host, limits())
            .run()
            .unwrap_err();
        expected(&interpreter_error);

        // Reference native: `raise` propagates the exact RuntimeError instead
        // of binding undefined into the catch register.
        let mut reference_host = SilentHost;
        let reference_error =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, limits())
                .run()
                .unwrap_err();
        expected(&reference_error);

        // Linked native: the postprocessor stores the fully sourced error in
        // `pending_error`, answers `FatalTrap`, and clears the pending throw,
        // so generated code never enters the handler.
        let mut linked_host = SilentHost;
        let linked = NativeEngine::build(
            &program,
            &NoEntries,
            &mut linked_host,
            limits(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED; 3];
        linked.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        linked.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, 3);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let result = linked.dispatch(&mut frame, HelperCall::LoadGlobal { name: 0 });
        assert_eq!(result.tag, CompletionTag::FatalTrap);
        assert_eq!(result.value, Value::UNDEFINED);
        assert!(
            linked.pending_throw.get().is_none(),
            "the pending throw is cleared before materialization"
        );
        assert!(
            linked.pending_fatal_kind.take().is_none(),
            "materialization failures never use the shallow fatal kind"
        );
        let error = linked
            .pending_error
            .replace(None)
            .expect("the exact sourced error is pending");
        expected(&error);
        linked.pop_native_roots();
        linked.activations.borrow_mut().pop();
    }

    /// Entry calls a callee whose covered missing-global load faults, so the
    /// materialization failure originates in the nested activation.
    fn nested_caught_missing_global_module() -> Module<Verified> {
        verified(
            vec![Constant::String(EcmaString::encode("missing_global"))],
            vec![
                Function::new(
                    None,
                    0,
                    0,
                    4,
                    FunctionFlags::default(),
                    vec![
                        Instruction::CreateArray { dst: reg(0) },
                        Instruction::CreateClosure {
                            dst: reg(1),
                            function: FunctionId::new(1),
                            captures: reg(0),
                        },
                        Instruction::CreateArray { dst: reg(2) },
                        Instruction::Call {
                            dst: reg(3),
                            callee: reg(1),
                            this_value: reg(0),
                            arguments: reg(2),
                        },
                        Instruction::Return { value: reg(3) },
                    ],
                    Vec::new(),
                ),
                Function::new(
                    None,
                    0,
                    0,
                    2,
                    FunctionFlags::default(),
                    vec![
                        Instruction::LoadGlobal {
                            dst: reg(0),
                            name: cid(0),
                        },
                        Instruction::Halt,
                        Instruction::Return { value: reg(1) },
                    ],
                    vec![ExceptionHandler {
                        start: pc(0),
                        end: pc(1),
                        handler: pc(2),
                        catch_register: reg(1),
                    }],
                ),
            ],
        )
    }

    #[test]
    fn nested_materialization_failure_keeps_the_inner_fault_site() {
        let program = one_module_program(&nested_caught_missing_global_module());
        let limits = || Limits {
            // Three slots cover the entry's array/closure/array setup; the
            // callee's materialization then has no headroom.
            max_heap_slots: 3,
            ..Limits::default()
        };
        let expected = |error: &RuntimeError| {
            assert_eq!(error.function, FunctionId::new(1));
            assert_eq!(error.pc, pc(0));
            assert!(matches!(
                error.kind,
                RuntimeErrorKind::HeapSlotLimitExceeded { .. }
            ));
            assert!(matches!(
                error.source.instruction,
                Instruction::LoadGlobal { .. }
            ));
        };

        // Interpreter oracle for the nested fault site.
        let mut interpreter_host = SilentHost;
        let interpreter_error = Machine::new(&program, &mut interpreter_host, limits())
            .run()
            .unwrap_err();
        expected(&interpreter_error);

        // Reference native: the nested `execute` propagates the inner error
        // through `pending_error`, retaining the inner module/function/pc.
        let mut reference_host = SilentHost;
        let reference_error =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, limits())
                .run()
                .unwrap_err();
        expected(&reference_error);
    }

    #[test]
    fn prematerialized_error_keeps_identity_through_catch() {
        // CreateCell TDZ throws ThrowValueOrigin with a pre-built
        // ReferenceError; both backends must bind that exact value.
        let module = verified(
            vec![Constant::Int32(0)],
            vec![Function::new(
                None,
                0,
                0,
                5,
                FunctionFlags::default(),
                vec![
                    Instruction::CreateCell { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::GetProperty {
                        dst: reg(2),
                        object: reg(0),
                        key: reg(1),
                    },
                    Instruction::Halt,
                    Instruction::Throw { value: reg(3) },
                    Instruction::Binary {
                        dst: reg(4),
                        op: BinaryOp::StrictEqual,
                        left: reg(3),
                        right: reg(0),
                    },
                    Instruction::Return { value: reg(4) },
                ],
                vec![
                    ExceptionHandler {
                        start: pc(2),
                        end: pc(3),
                        handler: pc(4),
                        catch_register: reg(3),
                    },
                    ExceptionHandler {
                        start: pc(4),
                        end: pc(5),
                        handler: pc(5),
                        catch_register: reg(0),
                    },
                ],
            )],
        );
        let program = one_module_program(&module);

        // Reference native: two catches preserve the exact supplied value.
        let mut reference_host = SilentHost;
        let reference =
            NativeEngine::new(&program, &NoEntries, &mut reference_host, Limits::default());
        let execution =
            run_reference_to_quiescence(&reference).expect("reference native catches twice");
        assert_eq!(execution.value, Value::TRUE);
        let caught = execution.entry_registers[3];
        assert_eq!(caught, execution.entry_registers[0]);
        assert_intrinsic_error(
            &mut reference.machine.borrow_mut(),
            caught,
            "ReferenceError",
            "Cannot access lexical binding before initialization",
        );

        // Linked native: the covered GetProperty dispatch yields the supplied
        // value unchanged — identity, not a rematerialized copy.
        let mut linked_host = SilentHost;
        let linked = NativeEngine::build(
            &program,
            &NoEntries,
            &mut linked_host,
            Limits::default(),
            Backend::Linked,
            bamts_cancel::CancellationToken::new(),
        );
        let mut registers = vec![Value::UNINITIALIZED; 5];
        linked.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        linked.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 2, 0, handles, 5);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let created = linked.dispatch(&mut frame, HelperCall::CreateCell);
        assert_eq!(created.tag, CompletionTag::Normal);
        let read = linked.dispatch(
            &mut frame,
            HelperCall::GetProperty {
                object: created.value,
                key: Value::int32(0),
                site: u32::MAX,
            },
        );
        assert_eq!(read.tag, CompletionTag::Throw);
        assert_ne!(read.value, Value::UNDEFINED);
        // The message is the pre-built TDZ text, not the origin's operation
        // string: rematerializing would allocate a different object whose
        // message is "lexical binding is uninitialized".
        assert_intrinsic_error(
            &mut linked.machine.borrow_mut(),
            read.value,
            "ReferenceError",
            "Cannot access lexical binding before initialization",
        );
        assert!(
            linked.pending_throw.get().is_none(),
            "a caught throw consumes its pending metadata"
        );
        linked.pop_native_roots();
        linked.activations.borrow_mut().pop();
    }

    #[test]
    fn define_data_property_helper_installs_own_data() {
        let program = trivial_program();
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Reference,
            bamts_cancel::CancellationToken::new(),
        );
        let key = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let mut registers = vec![Value::UNINITIALIZED];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 1);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let object = engine.dispatch(&mut frame, HelperCall::CreateObject);
        assert_eq!(object.tag, CompletionTag::Normal);
        let defined = engine.dispatch(
            &mut frame,
            HelperCall::DefineDataProperty {
                object: object.value,
                key,
                value: Value::int32(7),
            },
        );
        assert_eq!(defined.tag, CompletionTag::Normal);
        assert_eq!(defined.value, Value::UNDEFINED);
        let read = engine.dispatch(
            &mut frame,
            HelperCall::GetProperty {
                object: object.value,
                key,
                site: u32::MAX,
            },
        );
        assert_eq!(read.tag, CompletionTag::Normal);
        assert_eq!(read.value, Value::int32(7));
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn extension_helpers_lower_with_exact_operands_and_destinations() {
        let module = verified(
            Vec::new(),
            vec![entry_function(10, vec![Instruction::Halt])],
        );
        let program = one_module_program(&module);
        let mut host = SilentHost;
        let entries = NoEntries;
        let engine = NativeEngine::new(&program, &entries, &mut host, Limits::default());
        let mut registers = [
            Value::int32(10),
            Value::int32(11),
            Value::int32(12),
            Value::int32(13),
            Value::int32(14),
            Value::int32(15),
            Value::int32(16),
            Value::int32(17),
            Value::int32(18),
            Value::UNINITIALIZED,
        ];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let mut shadow =
            ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, registers.len() as u16);
        let frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();
        let cases = [
            (
                Instruction::GetSuper {
                    dst: reg(9),
                    home: reg(0),
                    receiver: reg(1),
                    key: reg(2),
                },
                HelperCall::GetSuper {
                    home: Value::int32(10),
                    receiver: Value::int32(11),
                    key: Value::int32(12),
                },
                Some(9),
            ),
            (
                Instruction::SetSuper {
                    home: reg(1),
                    receiver: reg(2),
                    key: reg(3),
                    value: reg(4),
                },
                HelperCall::SetSuper {
                    home: Value::int32(11),
                    receiver: Value::int32(12),
                    key: Value::int32(13),
                    value: Value::int32(14),
                },
                None,
            ),
            (
                Instruction::ImportAttributes {
                    dst: reg(9),
                    specifier: cid(7),
                    attributes: reg(5),
                },
                HelperCall::ImportAttributes {
                    specifier: 7,
                    attributes: Value::int32(15),
                },
                Some(9),
            ),
            (
                Instruction::ImportDynamicAttributes {
                    dst: reg(9),
                    specifier: reg(6),
                    attributes: reg(7),
                },
                HelperCall::ImportDynamicAttributes {
                    specifier: Value::int32(16),
                    attributes: Value::int32(17),
                },
                Some(9),
            ),
            (
                Instruction::CopyDataProperties {
                    target: reg(0),
                    source: reg(1),
                    excluded: reg(2),
                },
                HelperCall::CopyDataProperties {
                    target: Value::int32(10),
                    source: Value::int32(11),
                    excluded: Value::int32(12),
                },
                None,
            ),
            (
                Instruction::GetTemplateObject {
                    dst: reg(9),
                    cooked: reg(3),
                    raw: reg(4),
                },
                HelperCall::GetTemplateObject {
                    cooked: Value::int32(13),
                    raw: Value::int32(14),
                },
                Some(9),
            ),
        ];
        for (instruction, expected_call, expected_dst) in cases {
            assert!(!super::is_inline_instruction(instruction));
            let (call, dst) = engine.lower(instruction, &frame, 0);
            assert_eq!(call, expected_call);
            assert_eq!(dst, expected_dst);
        }
        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn super_and_copy_data_properties_match_interpreter_dispatch() {
        let super_module = verified(
            vec![
                Constant::String(EcmaString::encode("<test>")),
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(7),
                Constant::Int32(9),
                Constant::String(EcmaString::encode("y")),
                Constant::Int32(13),
            ],
            vec![entry_function(
                9,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(2),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(0),
                        key: reg(1),
                        value: reg(2),
                    },
                    Instruction::CreateObject { dst: reg(3) },
                    Instruction::SetPrototype {
                        object: reg(3),
                        prototype: reg(0),
                    },
                    Instruction::CreateObject { dst: reg(4) },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(3),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(4),
                        key: reg(1),
                        value: reg(5),
                    },
                    Instruction::GetSuper {
                        dst: reg(6),
                        home: reg(3),
                        receiver: reg(4),
                        key: reg(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(4),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(5),
                    },
                    Instruction::SetSuper {
                        home: reg(3),
                        receiver: reg(4),
                        key: reg(1),
                        value: reg(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(7),
                        object: reg(4),
                        key: reg(1),
                    },
                    Instruction::Binary {
                        dst: reg(8),
                        op: BinaryOp::Add,
                        left: reg(6),
                        right: reg(7),
                    },
                    Instruction::Return { value: reg(8) },
                ],
            )],
        );
        assert_eq!(
            assert_parity(&super_module, || SilentHost),
            Value::int32(20)
        );

        let copy_module = verified(
            vec![
                Constant::String(EcmaString::encode("<test>")),
                Constant::String(EcmaString::encode("x")),
                Constant::String(EcmaString::encode("y")),
                Constant::Int32(5),
                Constant::Int32(7),
                Constant::Int32(99),
            ],
            vec![entry_function(
                8,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::CreateObject { dst: reg(1) },
                    Instruction::CreateArray { dst: reg(2) },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(1),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(5),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(0),
                        key: reg(3),
                        value: reg(5),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(3),
                    },
                    Instruction::SetProperty {
                        object: reg(1),
                        key: reg(3),
                        value: reg(5),
                    },
                    Instruction::LoadConst {
                        dst: reg(4),
                        constant: cid(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(6),
                        constant: cid(4),
                    },
                    Instruction::SetProperty {
                        object: reg(1),
                        key: reg(4),
                        value: reg(6),
                    },
                    Instruction::ArrayPush {
                        array: reg(2),
                        value: reg(3),
                    },
                    Instruction::CopyDataProperties {
                        target: reg(0),
                        source: reg(1),
                        excluded: reg(2),
                    },
                    Instruction::GetProperty {
                        dst: reg(5),
                        object: reg(0),
                        key: reg(3),
                    },
                    Instruction::GetProperty {
                        dst: reg(7),
                        object: reg(0),
                        key: reg(4),
                    },
                    Instruction::Binary {
                        dst: reg(7),
                        op: BinaryOp::Add,
                        left: reg(5),
                        right: reg(7),
                    },
                    Instruction::Return { value: reg(7) },
                ],
            )],
        );
        assert_eq!(
            assert_parity(&copy_module, || SilentHost),
            Value::int32(106)
        );
    }

    #[test]
    fn template_object_dispatch_matches_interpreter_site_identity() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("<test>")),
                Constant::String(EcmaString::encode("cooked")),
                Constant::String(EcmaString::encode("raw")),
            ],
            vec![entry_function(
                4,
                vec![
                    Instruction::CreateArray { dst: reg(0) },
                    Instruction::CreateArray { dst: reg(1) },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::ArrayPush {
                        array: reg(0),
                        value: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(2),
                    },
                    Instruction::ArrayPush {
                        array: reg(1),
                        value: reg(2),
                    },
                    Instruction::GetTemplateObject {
                        dst: reg(3),
                        cooked: reg(0),
                        raw: reg(1),
                    },
                    Instruction::Return { value: reg(3) },
                ],
            )],
        );
        assert_ne!(assert_parity(&module, || SilentHost), Value::UNDEFINED);
    }

    #[test]
    fn with_has_binding_is_helper_backed_and_not_inline() {
        assert!(!super::is_inline_instruction(Instruction::WithHasBinding {
            dst: reg(0),
            object: reg(1),
            key: reg(2),
        }));
        assert_eq!(
            HelperCall::WithHasBinding {
                object: Value::NULL,
                key: Value::NULL,
            }
            .helper(),
            NativeHelper::WithHasBinding
        );
        assert_eq!(NativeHelper::WithHasBinding.as_u32(), 45);
        assert_eq!(
            NativeHelper::WithHasBinding.symbol(),
            "bamts_with_has_binding"
        );
        assert_eq!(NativeHelper::ResumeMode.as_u32(), 46);
        assert_eq!(HELPER_COUNT, 56);
    }

    #[test]
    fn with_has_binding_helper_parity_covers_absent_allowed_blocked_and_primitive_unscopables() {
        let program = trivial_program();
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Reference,
            bamts_cancel::CancellationToken::new(),
        );
        let key_x = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let key_missing = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("missing")))
            .unwrap();
        let mut registers = vec![Value::UNINITIALIZED; 2];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 2);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();

        let object = engine.dispatch(&mut frame, HelperCall::CreateObject);
        assert_eq!(object.tag, CompletionTag::Normal);
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::DefineDataProperty {
                        object: object.value,
                        key: key_x,
                        value: Value::int32(1),
                    },
                )
                .tag,
            CompletionTag::Normal
        );

        let absent = engine.dispatch(
            &mut frame,
            HelperCall::WithHasBinding {
                object: object.value,
                key: key_missing,
            },
        );
        assert_eq!(absent.tag, CompletionTag::Normal);
        assert_eq!(absent.value, Value::FALSE);

        let allowed = engine.dispatch(
            &mut frame,
            HelperCall::WithHasBinding {
                object: object.value,
                key: key_x,
            },
        );
        assert_eq!(allowed.tag, CompletionTag::Normal);
        assert_eq!(allowed.value, Value::TRUE);

        let blocklist = engine.dispatch(&mut frame, HelperCall::CreateObject);
        assert_eq!(blocklist.tag, CompletionTag::Normal);
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::DefineDataProperty {
                        object: blocklist.value,
                        key: key_x,
                        value: Value::TRUE,
                    },
                )
                .tag,
            CompletionTag::Normal
        );
        let unscopables = engine
            .machine
            .borrow()
            .intrinsics
            .builtins
            .symbol_unscopables();
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::SetProperty {
                        object: object.value,
                        key: unscopables,
                        value: blocklist.value,
                        site: u32::MAX,
                    },
                )
                .tag,
            CompletionTag::Normal
        );
        let blocked = engine.dispatch(
            &mut frame,
            HelperCall::WithHasBinding {
                object: object.value,
                key: key_x,
            },
        );
        assert_eq!(blocked.tag, CompletionTag::Normal);
        assert_eq!(blocked.value, Value::FALSE);

        // Primitive @@unscopables must be ignored (binding remains visible).
        let primitive = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("not-object")))
            .unwrap();
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::SetProperty {
                        object: object.value,
                        key: unscopables,
                        value: primitive,
                        site: u32::MAX,
                    },
                )
                .tag,
            CompletionTag::Normal
        );
        let still_allowed = engine.dispatch(
            &mut frame,
            HelperCall::WithHasBinding {
                object: object.value,
                key: key_x,
            },
        );
        assert_eq!(still_allowed.tag, CompletionTag::Normal);
        assert_eq!(still_allowed.value, Value::TRUE);

        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn with_has_binding_propagates_unscopables_getter_throw() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("<test>")),
                Constant::String(EcmaString::encode("x")),
                Constant::Int32(1),
            ],
            vec![
                entry_function(1, vec![Instruction::Halt]),
                entry_function(
                    2,
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(2),
                        },
                        Instruction::Throw { value: reg(0) },
                    ],
                ),
            ],
        );
        let program = one_module_program(&module);
        let entries = NoEntries;
        let mut host = SilentHost;
        let engine = NativeEngine::build(
            &program,
            &entries,
            &mut host,
            Limits::default(),
            Backend::Reference,
            bamts_cancel::CancellationToken::new(),
        );
        let key_x = engine
            .machine
            .borrow_mut()
            .allocate(HeapEntry::String(EcmaString::encode("x")))
            .unwrap();
        let mut registers = vec![Value::UNINITIALIZED; 2];
        engine.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: test_target(),
        });
        engine.push_native_roots(&registers);
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, registers.as_mut_ptr(), 2);
        let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();

        let object = engine.dispatch(&mut frame, HelperCall::CreateObject);
        assert_eq!(object.tag, CompletionTag::Normal);
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::DefineDataProperty {
                        object: object.value,
                        key: key_x,
                        value: Value::int32(1),
                    },
                )
                .tag,
            CompletionTag::Normal
        );
        let thrower = {
            let prototype = engine.machine.borrow().intrinsics.function_prototype;
            engine
                .machine
                .borrow_mut()
                .allocate(HeapEntry::Function {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                    captures: Vec::new(),
                    context: None,
                    properties: PropertyMap::default(),
                    prototype: Some(prototype),
                    extensible: true,
                })
                .unwrap()
        };
        let unscopables = engine
            .machine
            .borrow()
            .intrinsics
            .builtins
            .symbol_unscopables();
        assert_eq!(
            engine
                .dispatch(
                    &mut frame,
                    HelperCall::DefineAccessor {
                        object: object.value,
                        key: unscopables,
                        accessor: thrower,
                        kind: super::accessor_to_selector(AccessorKind::Getter),
                    },
                )
                .tag,
            CompletionTag::Normal
        );
        let threw = engine.dispatch(
            &mut frame,
            HelperCall::WithHasBinding {
                object: object.value,
                key: key_x,
            },
        );
        assert_eq!(threw.tag, CompletionTag::Throw);
        assert_eq!(threw.value, Value::int32(1));

        engine.pop_native_roots();
        engine.activations.borrow_mut().pop();
    }

    #[test]
    fn descriptor_slot_selectors_are_exhaustive_round_trips() {
        for (slot, selector) in [
            (DescriptorSlot::Value, 0),
            (DescriptorSlot::Getter, 1),
            (DescriptorSlot::Setter, 2),
        ] {
            assert_eq!(super::descriptor_slot_to_selector(slot), selector);
            assert_eq!(super::descriptor_slot_from_selector(selector), Some(slot));
        }
        assert_eq!(super::descriptor_slot_from_selector(3), None);
        assert_eq!(super::descriptor_slot_from_selector(u32::MAX), None);
        assert!(!super::is_inline_instruction(
            Instruction::LoadOwnDescriptorSlot {
                dst: reg(0),
                object: reg(1),
                key: reg(2),
                slot: DescriptorSlot::Value,
            }
        ));
        assert!(!super::is_inline_instruction(
            Instruction::DefineOwnDescriptorSlot {
                object: reg(0),
                key: reg(1),
                src: reg(2),
                slot: DescriptorSlot::Setter,
            }
        ));
    }

    #[test]
    fn load_own_descriptor_slot_parity_covers_absent_data_accessor_and_mismatch() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("data")),
                Constant::Int32(7),
                Constant::String(EcmaString::encode("accessor")),
                Constant::String(EcmaString::encode("missing")),
            ],
            vec![entry_function(
                10,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(0),
                        key: reg(1),
                        value: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(2),
                    },
                    Instruction::CreateObject { dst: reg(4) },
                    Instruction::DefineAccessor {
                        object: reg(0),
                        key: reg(3),
                        accessor: reg(4),
                        kind: AccessorKind::Getter,
                    },
                    Instruction::LoadOwnDescriptorSlot {
                        dst: reg(5),
                        object: reg(0),
                        key: reg(1),
                        slot: DescriptorSlot::Value,
                    },
                    Instruction::LoadOwnDescriptorSlot {
                        dst: reg(6),
                        object: reg(0),
                        key: reg(1),
                        slot: DescriptorSlot::Getter,
                    },
                    Instruction::LoadOwnDescriptorSlot {
                        dst: reg(7),
                        object: reg(0),
                        key: reg(3),
                        slot: DescriptorSlot::Getter,
                    },
                    Instruction::LoadOwnDescriptorSlot {
                        dst: reg(8),
                        object: reg(0),
                        key: reg(3),
                        slot: DescriptorSlot::Value,
                    },
                    Instruction::LoadConst {
                        dst: reg(9),
                        constant: cid(3),
                    },
                    Instruction::LoadOwnDescriptorSlot {
                        dst: reg(9),
                        object: reg(0),
                        key: reg(9),
                        slot: DescriptorSlot::Value,
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        );
        let value = assert_parity(&module, || SilentHost);
        let program = one_module_program(&module);
        let mut host = SilentHost;
        let native = NativeEngine::new(&program, &NoEntries, &mut host, Limits::default())
            .run()
            .expect("reference native runs load slots");
        assert_eq!(value, native.value);
        assert_eq!(native.entry_registers[5], Value::int32(7));
        assert_eq!(
            native.entry_registers[6],
            Value::UNDEFINED,
            "data/getter mismatch yields undefined"
        );
        assert_eq!(
            native.entry_registers[7], native.entry_registers[4],
            "accessor getter slot returns the installed getter"
        );
        assert_eq!(
            native.entry_registers[8],
            Value::UNDEFINED,
            "accessor/value mismatch yields undefined"
        );
        assert_eq!(
            native.entry_registers[9],
            Value::UNDEFINED,
            "absent property yields undefined"
        );
    }

    #[test]
    fn define_own_descriptor_slot_parity_creates_absent_preserves_and_rejects_mismatch() {
        let module = verified(
            vec![
                Constant::String(EcmaString::encode("created")),
                Constant::Int32(9),
                Constant::String(EcmaString::encode("data")),
                Constant::Int32(1),
                Constant::Int32(8),
                Constant::String(EcmaString::encode("accessor")),
            ],
            vec![entry_function(
                8,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::DefineOwnDescriptorSlot {
                        object: reg(0),
                        key: reg(1),
                        src: reg(2),
                        slot: DescriptorSlot::Value,
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(4),
                        constant: cid(3),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(0),
                        key: reg(3),
                        value: reg(4),
                    },
                    Instruction::LoadConst {
                        dst: reg(5),
                        constant: cid(4),
                    },
                    Instruction::DefineOwnDescriptorSlot {
                        object: reg(0),
                        key: reg(3),
                        src: reg(5),
                        slot: DescriptorSlot::Value,
                    },
                    Instruction::LoadConst {
                        dst: reg(6),
                        constant: cid(5),
                    },
                    Instruction::CreateObject { dst: reg(7) },
                    Instruction::DefineAccessor {
                        object: reg(0),
                        key: reg(6),
                        accessor: reg(7),
                        kind: AccessorKind::Getter,
                    },
                    Instruction::CreateObject { dst: reg(1) },
                    Instruction::DefineOwnDescriptorSlot {
                        object: reg(0),
                        key: reg(6),
                        src: reg(1),
                        slot: DescriptorSlot::Setter,
                    },
                    Instruction::Return { value: reg(0) },
                ],
            )],
        );
        let program = one_module_program(&module);

        let mut interpreter_host = SilentHost;
        let mut interpreter = Machine::new(&program, &mut interpreter_host, Limits::default());
        let interpreter_execution =
            run_interpreter_to_quiescence(&mut interpreter).expect("interpreter defines slots");
        let interpreter_object = interpreter_execution.value;

        let mut native_host = SilentHost;
        let native = NativeEngine::new(&program, &NoEntries, &mut native_host, Limits::default());
        let native_execution =
            run_reference_to_quiescence(&native).expect("reference native defines slots");
        let native_object = native_execution.value;

        assert_eq!(
            interpreter_execution.entry_registers,
            native_execution.entry_registers
        );
        let assert_slots =
            |machine: &mut Machine<'_, SilentHost>, object: Value, registers: &[Value]| {
                let created = PropertyKey::Named(machine.intern_str("created"));
                let data = PropertyKey::Named(machine.intern_str("data"));
                let accessor = PropertyKey::Named(machine.intern_str("accessor"));
                assert!(matches!(
                    machine.own_descriptor(object, &created).unwrap(),
                    Some(Property::Data {
                        value,
                        writable: true,
                        enumerable: false,
                        configurable: true,
                    }) if value == Value::int32(9)
                ));
                assert!(matches!(
                    machine.own_descriptor(object, &data).unwrap(),
                    Some(Property::Data {
                        value,
                        writable: true,
                        enumerable: false,
                        configurable: true,
                    }) if value == Value::int32(8)
                ));
                match machine
                    .own_descriptor(object, &accessor)
                    .unwrap()
                    .expect("accessor remains installed")
                {
                    Property::Accessor {
                        getter: Some(getter),
                        setter: Some(setter),
                        enumerable: true,
                        configurable: true,
                    } => {
                        assert_eq!(getter, registers[7]);
                        assert_eq!(setter, registers[1]);
                    }
                    other => panic!("expected accessor with both halves, got {other:?}"),
                }
            };
        assert_slots(
            &mut interpreter,
            interpreter_object,
            &interpreter_execution.entry_registers,
        );
        assert_slots(
            &mut native.machine.borrow_mut(),
            native_object,
            &native_execution.entry_registers,
        );

        let mismatch = verified(
            vec![
                Constant::String(EcmaString::encode("data")),
                Constant::Int32(1),
                Constant::Int32(2),
            ],
            vec![entry_function(
                4,
                vec![
                    Instruction::CreateObject { dst: reg(0) },
                    Instruction::LoadConst {
                        dst: reg(1),
                        constant: cid(0),
                    },
                    Instruction::LoadConst {
                        dst: reg(2),
                        constant: cid(1),
                    },
                    Instruction::DefineDataProperty {
                        object: reg(0),
                        key: reg(1),
                        value: reg(2),
                    },
                    Instruction::LoadConst {
                        dst: reg(3),
                        constant: cid(2),
                    },
                    Instruction::DefineOwnDescriptorSlot {
                        object: reg(0),
                        key: reg(1),
                        src: reg(3),
                        slot: DescriptorSlot::Getter,
                    },
                    Instruction::Halt,
                ],
            )],
        );
        let mismatch_program = one_module_program(&mismatch);
        let mut interpreter_host = SilentHost;
        let interpreter_error =
            Machine::new(&mismatch_program, &mut interpreter_host, Limits::default())
                .run()
                .expect_err("interpreter rejects data/getter shape mismatch");
        let mut native_host = SilentHost;
        let native_error = NativeEngine::new(
            &mismatch_program,
            &NoEntries,
            &mut native_host,
            Limits::default(),
        )
        .run()
        .expect_err("reference native rejects data/getter shape mismatch");
        for error in [&interpreter_error, &native_error] {
            assert!(matches!(
                error.kind,
                RuntimeErrorKind::UncaughtThrow {
                    origin: ThrowOrigin::TypeError {
                        operation: "decorator replacement changes descriptor shape"
                    },
                    ..
                }
            ));
        }
    }

    #[test]
    fn own_descriptor_slot_helpers_pass_raw_keys_and_reject_invalid_slots() {
        for backend in [Backend::Reference, Backend::Linked] {
            let program = trivial_program();
            let entries = NoEntries;
            let mut host = SilentHost;
            let engine = NativeEngine::build(
                &program,
                &entries,
                &mut host,
                Limits::default(),
                backend,
                bamts_cancel::CancellationToken::new(),
            );
            let mut registers = vec![Value::UNINITIALIZED; 2];
            engine.activations.borrow_mut().push(Activation {
                this_value: Value::UNDEFINED,
                new_target: Value::UNDEFINED,
                args: Vec::new(),
                arguments_object: None,
                pending_resume: None,
                target: test_target(),
            });
            engine.push_native_roots(&registers);
            let handles = registers.as_mut_ptr();
            let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, 0, handles, 2);
            let mut frame = NativeFrame::new(&mut shadow, &mut registers).unwrap();

            let object = engine.dispatch(&mut frame, HelperCall::CreateObject);
            assert_eq!(object.tag, CompletionTag::Normal);

            // Raw non-string keys must reach Machine unchanged; Machine coerces.
            let defined = engine.dispatch(
                &mut frame,
                HelperCall::DefineOwnDescriptorSlot {
                    object: object.value,
                    key: Value::int32(7),
                    src: Value::int32(42),
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Value),
                },
            );
            assert_eq!(defined.tag, CompletionTag::Normal);
            assert_eq!(defined.value, Value::UNDEFINED);

            let loaded = engine.dispatch(
                &mut frame,
                HelperCall::LoadOwnDescriptorSlot {
                    object: object.value,
                    key: Value::int32(7),
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Value),
                },
            );
            assert_eq!(loaded.tag, CompletionTag::Normal);
            assert_eq!(loaded.value, Value::int32(42));

            let getter = engine.dispatch(&mut frame, HelperCall::CreateObject);
            assert_eq!(getter.tag, CompletionTag::Normal);
            let accessor_key = engine
                .machine
                .borrow_mut()
                .allocate(HeapEntry::String(EcmaString::encode("acc")))
                .unwrap();
            let installed = engine.dispatch(
                &mut frame,
                HelperCall::DefineOwnDescriptorSlot {
                    object: object.value,
                    key: accessor_key,
                    src: getter.value,
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Getter),
                },
            );
            assert_eq!(installed.tag, CompletionTag::Normal);
            let setter = engine.dispatch(&mut frame, HelperCall::CreateObject);
            assert_eq!(setter.tag, CompletionTag::Normal);
            let set_half = engine.dispatch(
                &mut frame,
                HelperCall::DefineOwnDescriptorSlot {
                    object: object.value,
                    key: accessor_key,
                    src: setter.value,
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Setter),
                },
            );
            assert_eq!(set_half.tag, CompletionTag::Normal);
            let got_getter = engine.dispatch(
                &mut frame,
                HelperCall::LoadOwnDescriptorSlot {
                    object: object.value,
                    key: accessor_key,
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Getter),
                },
            );
            let got_setter = engine.dispatch(
                &mut frame,
                HelperCall::LoadOwnDescriptorSlot {
                    object: object.value,
                    key: accessor_key,
                    slot: super::descriptor_slot_to_selector(DescriptorSlot::Setter),
                },
            );
            assert_eq!(got_getter.tag, CompletionTag::Normal);
            assert_eq!(got_getter.value, getter.value);
            assert_eq!(got_setter.tag, CompletionTag::Normal);
            assert_eq!(got_setter.value, setter.value);

            for invalid_slot in [3_u32, 99, u32::MAX] {
                let invalid_load = engine.dispatch(
                    &mut frame,
                    HelperCall::LoadOwnDescriptorSlot {
                        object: object.value,
                        key: Value::int32(7),
                        slot: invalid_slot,
                    },
                );
                assert_eq!(invalid_load.tag, CompletionTag::FatalTrap);
                assert_eq!(invalid_load.value, Value::UNDEFINED);
                assert_eq!(
                    engine.pending_fatal_kind.take(),
                    Some(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED
                    })
                );

                let invalid_define = engine.dispatch(
                    &mut frame,
                    HelperCall::DefineOwnDescriptorSlot {
                        object: object.value,
                        key: Value::int32(7),
                        src: Value::int32(1),
                        slot: invalid_slot,
                    },
                );
                assert_eq!(invalid_define.tag, CompletionTag::FatalTrap);
                assert_eq!(invalid_define.value, Value::UNDEFINED);
                assert_eq!(
                    engine.pending_fatal_kind.take(),
                    Some(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED
                    })
                );
            }

            engine.pop_native_roots();
            engine.activations.borrow_mut().pop();
        }
    }

    #[test]
    fn pre_cancelled_token_aborts_before_entry_invocation() {
        let program = trivial_program();
        let entries = RecordingEntries {
            program_bytes: program.encode(),
            ..RecordingEntries::default()
        };
        let token = bamts_cancel::CancellationToken::new();
        token.cancel();
        let mut host = SilentHost;
        let error = super::run_linked_program_with_cancel(
            &program,
            &entries,
            &mut host,
            &Limits::default(),
            token,
        )
        .expect_err("pre-cancelled token aborts");
        assert_eq!(error, NativeError::Cancelled);
        assert!(
            entries.invoked.borrow().is_empty(),
            "entry must not be invoked when pre-cancelled"
        );
    }

    #[test]
    fn fresh_token_preserves_existing_run_linked_program_behavior() {
        let program = trivial_program();
        let entries = RecordingEntries {
            program_bytes: program.encode(),
            ..RecordingEntries::default()
        };
        let mut host = SilentHost;
        let outcome = run_linked_program(&program, &entries, &mut host, &Limits::default())
            .expect("fresh token runs to completion");
        assert_eq!(outcome.exit_code, 0);
        assert_eq!(entries.invoked.borrow().as_slice(), &[(0, 0)]);
    }

    #[test]
    fn fuel_checkpoint_cancellation_aborts_long_execution() {
        // A program that loops forever via a backward jump. The fuel
        // checkpoint in `consume_fuel` checks the cancellation token before
        // decrementing, so a token cancelled mid-flight aborts with
        // `RuntimeErrorKind::Cancelled` surfaced through `NativeError`.
        let code = verified(
            vec![Constant::String(EcmaString::encode("<loop>"))],
            vec![entry_function(1, vec![Instruction::Jump { target: pc(0) }])],
        );
        let program = linked(
            vec![ProgramModule {
                name: ConstantId::new(0),
                code,
                edges: Vec::new(),
                bindings: Vec::new(),
                exports: Vec::new(),
            }],
            0,
        );
        let entries = RecordingEntries {
            program_bytes: program.encode(),
            ..RecordingEntries::default()
        };
        let token = bamts_cancel::CancellationToken::new();
        // Cancel after construction but before running — the pre-cancel
        // check in `run_linked` catches it.
        token.cancel();
        let mut host = SilentHost;
        let error = super::run_linked_program_with_cancel(
            &program,
            &entries,
            &mut host,
            &Limits::default(),
            token,
        )
        .expect_err("cancelled token aborts loop");
        assert_eq!(error, NativeError::Cancelled);
    }

    /// A getter whose value only the list being read holds.
    fn fresh_object(
        machine: &mut Machine<'_, SilentHost>,
        _this: Value,
        _args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        let prototype = machine.intrinsics.object_prototype;
        let object = crate::builtins::ordinary_runtime(machine, Some(prototype))?;
        machine.set_data_property(object, "marker", Value::int32(7))?;
        Ok(BuiltinOutcome::Value(object))
    }

    /// A callee that reaches a collection before it reads what it was given.
    fn collect_then_read(
        machine: &mut Machine<'_, SilentHost>,
        _this: Value,
        args: &[Value],
        _constructing: bool,
    ) -> Result<BuiltinOutcome, EvalFailure> {
        machine.collect_garbage();
        machine
            .get_named_property(args[0], "marker")
            .map(BuiltinOutcome::Value)
    }

    fn builtin(
        machine: &mut Machine<'_, SilentHost>,
        name: &'static str,
        handler: BuiltinHandler<SilentHost>,
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

    #[test]
    fn a_collection_in_the_next_builtin_keeps_the_arguments_of_apply() {
        let program = trivial_program();
        let mut host = SilentHost;
        let engine = NativeEngine::new(&program, &NoEntries, &mut host, Limits::default());
        let (apply, reflect, target, list) = {
            let mut machine = engine.machine.borrow_mut();
            let target = builtin(&mut machine, "collect then read", collect_then_read);
            let getter = builtin(&mut machine, "fresh object", fresh_object);
            let prototype = machine.intrinsics.object_prototype;
            let list = crate::builtins::ordinary_runtime(&mut machine, Some(prototype)).unwrap();
            machine
                .set_data_property(list, "length", Value::int32(1))
                .unwrap();
            let index_key = PropertyKey::Named(machine.intern_str("0"));
            machine
                .define_descriptor(
                    list,
                    index_key,
                    Property::Accessor {
                        getter: Some(getter),
                        setter: None,
                        enumerable: true,
                        configurable: true,
                    },
                )
                .unwrap();
            machine.hold_temporaries(&[target, list]);
            let reflect = machine.intrinsics.global("Reflect").unwrap();
            let apply = machine.get_named_property(reflect, "apply").unwrap();
            (apply, reflect, target, list)
        };
        let held = engine.machine.borrow().builtin_temporaries.len();

        let outcome = engine.invoke_callee(
            apply,
            reflect,
            &[target, Value::UNDEFINED, list],
            Value::UNDEFINED,
        );

        assert!(matches!(outcome, InvokeOutcome::Value(value) if value == Value::int32(7)));
        assert_eq!(engine.machine.borrow().builtin_temporaries.len(), held);
    }
