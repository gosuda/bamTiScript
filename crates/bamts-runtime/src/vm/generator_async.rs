//! Generator and async-function resumption policy.
//!
//! This module owns the total transition table and the typed completion carried
//! across a suspension. The activation itself remains the runtime's existing
//! `GeneratorState` / `SuspendedActivation`; no second VM or frame model is
//! introduced.

use bamts_bytecode::{RESUME_NEXT, RESUME_RETURN, RESUME_THROW};
use bamts_native::Value;

use crate::{
    EvalFailure, GeneratorStart, GeneratorState, HeapEntry, Host, Machine, RuntimeErrorKind,
    RuntimeFunction, SuspendedActivation, ThrowOrigin,
};

/// The externally requested generator operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GeneratorOperation {
    Next,
    Return,
    Throw,
}

impl GeneratorOperation {
    /// TypeError message for a synchronous `.next`/`.return`/`.throw` receiver
    /// that is not a generator.
    pub(crate) const fn sync_receiver_error(self) -> &'static str {
        match self {
            Self::Next => "Generator.prototype.next called on incompatible receiver",
            Self::Throw => "Generator.prototype.throw called on incompatible receiver",
            Self::Return => "Generator.prototype.return called on incompatible receiver",
        }
    }

    /// TypeError message for an async-generator `.next`/`.return`/`.throw`
    /// receiver that is not an async generator.
    pub(crate) const fn async_receiver_error(self) -> &'static str {
        match self {
            Self::Next => "AsyncGenerator.prototype.next called on incompatible receiver",
            Self::Throw => "AsyncGenerator.prototype.throw called on incompatible receiver",
            Self::Return => "AsyncGenerator.prototype.return called on incompatible receiver",
        }
    }
}

/// Initial `%GeneratorPrototype%` method metadata. Installation registers these
/// as writable, non-enumerable, configurable data properties.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GeneratorMethod {
    pub(crate) name: &'static str,
    pub(crate) length: u32,
}

pub(crate) const GENERATOR_METHODS: [GeneratorMethod; 3] = [
    GeneratorMethod {
        name: "next",
        length: 1,
    },
    GeneratorMethod {
        name: "return",
        length: 1,
    },
    GeneratorMethod {
        name: "throw",
        length: 1,
    },
];

/// A completion delivered to a generator's suspended evaluation context.
///
/// `Return` and `Throw` are deliberately distinct from an ordinary sent value:
/// both must traverse the suspended body's active `finally` regions before the
/// generator is settled.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GeneratorCompletion {
    Normal(Value),
    Return(Value),
    Throw { value: Value, origin: ThrowOrigin },
}

impl GeneratorCompletion {
    /// Visits every heap value retained by an in-flight completion.
    pub(crate) fn visit_roots(self, mut visit: impl FnMut(Value)) {
        match self {
            Self::Normal(value) | Self::Return(value) | Self::Throw { value, .. } => visit(value),
        }
    }

    /// The carried value, regardless of how it is delivered to the body.
    pub(crate) const fn value(self) -> Value {
        match self {
            Self::Normal(value) | Self::Return(value) | Self::Throw { value, .. } => value,
        }
    }

    /// Resume-mode operand written into the suspension's mode register
    /// (`RESUME_NEXT` / `RESUME_THROW` / `RESUME_RETURN` bytecode ABI).
    pub(crate) const fn mode(self) -> u32 {
        match self {
            Self::Normal(_) => RESUME_NEXT as u32,
            Self::Throw { .. } => RESUME_THROW as u32,
            Self::Return(_) => RESUME_RETURN as u32,
        }
    }

    /// The externally visible operation this completion encodes.
    pub(crate) const fn operation(self) -> GeneratorOperation {
        match self {
            Self::Normal(_) => GeneratorOperation::Next,
            Self::Return(_) => GeneratorOperation::Return,
            Self::Throw { .. } => GeneratorOperation::Throw,
        }
    }
}

/// A non-owning view of the existing `GeneratorState` used to make the
/// transition table exhaustively testable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GeneratorPhase {
    SuspendedStart,
    SuspendedYield,
    Executing,
    Completed,
}

impl From<&GeneratorState> for GeneratorPhase {
    fn from(state: &GeneratorState) -> Self {
        match state {
            GeneratorState::SuspendedStart(_) => Self::SuspendedStart,
            GeneratorState::Suspended(_) => Self::SuspendedYield,
            GeneratorState::Executing => Self::Executing,
            GeneratorState::Completed => Self::Completed,
        }
    }
}

/// Work selected by the generator transition table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GeneratorPlan {
    /// Resume the existing activation with this typed completion.
    Resume(GeneratorCompletion),
    /// Complete without entering the body and return `{ value, done: true }`.
    Complete(Value),
    /// Complete without entering the body and propagate this throw.
    Raise { value: Value, origin: ThrowOrigin },
}

/// Re-entering a generator while its activation is executing is always a
/// synchronous TypeError, regardless of the requested operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GeneratorReentrancy {
    // Retained for test diagnostics; underscore avoids lib dead_code.
    _operation: GeneratorOperation,
}

impl GeneratorReentrancy {
    /// The operation that attempted the re-entry, kept for diagnostics.
    #[cfg(test)]
    pub(crate) const fn operation(self) -> GeneratorOperation {
        self._operation
    }

    pub(crate) const fn into_failure(self) -> EvalFailure {
        EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "generator is already running",
        })
    }
}

/// Computes the ECMA-262 GeneratorResume / GeneratorResumeAbrupt transition.
///
/// The first `.next(value)` ignores `value` and starts with `undefined`.
/// `return` and `throw` from suspended-start never execute the body. Abrupt
/// completion from suspended-yield is resumed into the body so `finally` can
/// observe or replace it.
pub(crate) const fn generator_plan(
    phase: GeneratorPhase,
    completion: GeneratorCompletion,
) -> Result<GeneratorPlan, GeneratorReentrancy> {
    use GeneratorCompletion::{Normal, Return, Throw};
    use GeneratorPhase::{Completed, Executing, SuspendedStart, SuspendedYield};

    match (phase, completion) {
        (Executing, completion) => Err(GeneratorReentrancy {
            _operation: completion.operation(),
        }),

        (SuspendedStart, Normal(_)) => Ok(GeneratorPlan::Resume(GeneratorCompletion::Normal(
            Value::UNDEFINED,
        ))),
        (SuspendedStart, Return(value)) => Ok(GeneratorPlan::Complete(value)),
        (SuspendedStart, Throw { value, origin }) => Ok(GeneratorPlan::Raise { value, origin }),

        (SuspendedYield, completion) => Ok(GeneratorPlan::Resume(completion)),

        (Completed, Normal(_)) => Ok(GeneratorPlan::Complete(Value::UNDEFINED)),
        (Completed, Return(value)) => Ok(GeneratorPlan::Complete(value)),
        (Completed, Throw { value, origin }) => Ok(GeneratorPlan::Raise { value, origin }),
    }
}
/// A prepared operation owns the runtime's existing activation while the heap
/// generator is marked `Executing`.
#[derive(Clone, Debug)]
pub(crate) enum PreparedGeneratorOperation {
    Start {
        start: GeneratorStart,
    },
    Resume {
        activation: SuspendedActivation,
        completion: GeneratorCompletion,
    },
    Complete(Value),
    Raise {
        value: Value,
        origin: ThrowOrigin,
    },
}

/// Atomically validates, transitions, and detaches one generator activation.
///
/// Resumable states become `Executing` before control can re-enter user code.
/// Terminal operations become `Completed` in the same borrow, so failure paths
/// cannot leave the object resumable. An already executing generator is left
/// untouched and reports the operation-specific reentrancy TypeError.
pub(crate) fn prepare_generator_operation<H: Host>(
    machine: &mut Machine<'_, H>,
    generator: Value,
    completion: GeneratorCompletion,
) -> Result<PreparedGeneratorOperation, EvalFailure> {
    let operation = completion.operation();
    let Some(index) = machine
        .runtime_slot(generator)
        .map_err(EvalFailure::Runtime)?
    else {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: operation.sync_receiver_error(),
        }));
    };
    let HeapEntry::Generator { state, .. } = &mut machine.heap[index] else {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: operation.sync_receiver_error(),
        }));
    };
    let plan = generator_plan(GeneratorPhase::from(&*state), completion)
        .map_err(GeneratorReentrancy::into_failure)?;
    match plan {
        GeneratorPlan::Resume(completion) => {
            let previous = std::mem::replace(state, GeneratorState::Executing);
            match previous {
                GeneratorState::SuspendedStart(start) => {
                    Ok(PreparedGeneratorOperation::Start { start })
                }
                GeneratorState::Suspended(activation) => Ok(PreparedGeneratorOperation::Resume {
                    activation,
                    completion,
                }),
                GeneratorState::Executing | GeneratorState::Completed => {
                    unreachable!("generator plan selected a non-resumable state")
                }
            }
        }
        GeneratorPlan::Complete(value) => {
            *state = GeneratorState::Completed;
            Ok(PreparedGeneratorOperation::Complete(value))
        }
        GeneratorPlan::Raise { value, origin } => {
            *state = GeneratorState::Completed;
            Ok(PreparedGeneratorOperation::Raise { value, origin })
        }
    }
}

/// Fulfillment or rejection delivered by the promise reaction for one await.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AwaitSettlement {
    Fulfilled(Value),
    Rejected { reason: Value, origin: ThrowOrigin },
}

/// Starts an async function on the Machine's existing detached-activation and
/// implicit-promise path.
pub(crate) fn start_async_function<H: Host>(
    machine: &mut Machine<'_, H>,
    target: RuntimeFunction,
    captures: &[Value],
    context: Option<Value>,
    this_value: Value,
    new_target: Value,
    arguments: &[Value],
) -> Result<Value, EvalFailure> {
    machine.start_async_call(target, captures, context, this_value, new_target, arguments)
}

/// Resumes one existing async activation from its Promise reaction job.
///
/// This is intentionally a thin entry point into `Machine::resume_async`:
/// fulfillment writes the await destination, while rejection injects a throw
/// at the suspension PC so an enclosing catch/finally runs.
pub(crate) fn resume_async_function<H: Host>(
    machine: &mut Machine<'_, H>,
    activation: Value,
    settlement: AwaitSettlement,
) -> Result<(), RuntimeErrorKind> {
    match settlement {
        AwaitSettlement::Fulfilled(value) => machine.resume_async(activation, value, None),
        AwaitSettlement::Rejected { reason, origin } => {
            machine.resume_async(activation, reason, Some(origin))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Limits, PromiseState, PropertyMap};
    use bamts_bytecode::{
        Constant, ConstantId, Function, FunctionFlags, FunctionId, Instruction, Module, ModuleId,
        Pc, Program, ProgramModule, Register, Verified,
    };

    #[derive(Default)]
    struct TestHost;

    impl Host for TestHost {}

    fn reg(raw: u32) -> Register {
        Register::new(raw)
    }

    fn pc(raw: u32) -> Pc {
        Pc::new(raw)
    }
    fn cid(raw: u32) -> ConstantId {
        ConstantId::new(raw)
    }

    fn number(value: u32) -> Value {
        Value::int32(value)
    }

    fn function(
        captures: u32,
        registers: u32,
        flags: FunctionFlags,
        code: Vec<Instruction>,
    ) -> Function {
        Function::new(None, captures, 0, registers, flags, code, Vec::new())
    }

    fn verified(mut constants: Vec<Constant>, functions: Vec<Function>) -> Program<Verified> {
        let name = ConstantId::new(constants.len() as u32);
        constants.push(Constant::String(bamts_bytecode::EcmaString::encode(
            "<generator-async-test>",
        )));
        let code = Module::new(constants, functions, FunctionId::new(0))
            .verify()
            .expect("valid generator/async test bytecode");
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
        .expect("valid generator/async test program")
    }

    #[test]
    fn transition_table_covers_next_return_throw_in_every_state() {
        let sent = number(17);
        let origin = ThrowOrigin::Bytecode;

        let rows = [
            (
                GeneratorPhase::SuspendedStart,
                GeneratorOperation::Next,
                Ok(GeneratorPlan::Resume(GeneratorCompletion::Normal(
                    Value::UNDEFINED,
                ))),
            ),
            (
                GeneratorPhase::SuspendedStart,
                GeneratorOperation::Return,
                Ok(GeneratorPlan::Complete(sent)),
            ),
            (
                GeneratorPhase::SuspendedStart,
                GeneratorOperation::Throw,
                Ok(GeneratorPlan::Raise {
                    value: sent,
                    origin,
                }),
            ),
            (
                GeneratorPhase::SuspendedYield,
                GeneratorOperation::Next,
                Ok(GeneratorPlan::Resume(GeneratorCompletion::Normal(sent))),
            ),
            (
                GeneratorPhase::SuspendedYield,
                GeneratorOperation::Return,
                Ok(GeneratorPlan::Resume(GeneratorCompletion::Return(sent))),
            ),
            (
                GeneratorPhase::SuspendedYield,
                GeneratorOperation::Throw,
                Ok(GeneratorPlan::Resume(GeneratorCompletion::Throw {
                    value: sent,
                    origin,
                })),
            ),
            (
                GeneratorPhase::Completed,
                GeneratorOperation::Next,
                Ok(GeneratorPlan::Complete(Value::UNDEFINED)),
            ),
            (
                GeneratorPhase::Completed,
                GeneratorOperation::Return,
                Ok(GeneratorPlan::Complete(sent)),
            ),
            (
                GeneratorPhase::Completed,
                GeneratorOperation::Throw,
                Ok(GeneratorPlan::Raise {
                    value: sent,
                    origin,
                }),
            ),
        ];

        for (phase, operation, expected) in rows {
            let completion = match operation {
                GeneratorOperation::Next => GeneratorCompletion::Normal(sent),
                GeneratorOperation::Return => GeneratorCompletion::Return(sent),
                GeneratorOperation::Throw => GeneratorCompletion::Throw {
                    value: sent,
                    origin,
                },
            };
            assert_eq!(generator_plan(phase, completion), expected);
        }
    }

    #[test]
    fn generator_method_contract_has_spec_names_and_lengths() {
        assert_eq!(
            GENERATOR_METHODS,
            [
                GeneratorMethod {
                    name: "next",
                    length: 1,
                },
                GeneratorMethod {
                    name: "return",
                    length: 1,
                },
                GeneratorMethod {
                    name: "throw",
                    length: 1,
                },
            ]
        );
    }

    #[test]
    fn prepare_operation_atomically_marks_execution_and_rejects_reentrancy() {
        let program = verified(
            Vec::new(),
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    0,
                    3,
                    FunctionFlags {
                        is_async: false,
                        is_generator: true,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
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
                        Instruction::Return { value: reg(1) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let generator = machine
            .create_generator(GeneratorStart {
                target: RuntimeFunction {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                },
                captures: Vec::new(),
                context: None,
                this_value: Value::UNDEFINED,
                new_target: Value::UNDEFINED,
                args: Vec::new(),
            })
            .expect("generator allocates");
        let prepared = prepare_generator_operation(
            &mut machine,
            generator,
            GeneratorCompletion::Normal(number(5)),
        )
        .expect("suspended-start generator prepares");
        assert!(matches!(prepared, PreparedGeneratorOperation::Start { .. }));
        let index = machine.runtime_slot(generator).unwrap().unwrap();
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::Generator {
                state: GeneratorState::Executing,
                ..
            }
        ));
        assert!(matches!(
            prepare_generator_operation(
                &mut machine,
                generator,
                GeneratorCompletion::Return(number(7)),
            ),
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "generator is already running"
            }))
        ));
    }

    #[test]
    fn return_and_throw_from_suspended_yield_enter_the_body() {
        let value = number(23);
        assert_eq!(
            generator_plan(
                GeneratorPhase::SuspendedYield,
                GeneratorCompletion::Return(value),
            ),
            Ok(GeneratorPlan::Resume(GeneratorCompletion::Return(value)))
        );
        assert_eq!(
            generator_plan(
                GeneratorPhase::SuspendedYield,
                GeneratorCompletion::Throw {
                    value,
                    origin: ThrowOrigin::Bytecode,
                },
            ),
            Ok(GeneratorPlan::Resume(GeneratorCompletion::Throw {
                value,
                origin: ThrowOrigin::Bytecode,
            }))
        );
    }

    #[test]
    fn reentrancy_error_preserves_operation_and_uses_shared_message() {
        for operation in [
            GeneratorOperation::Next,
            GeneratorOperation::Return,
            GeneratorOperation::Throw,
        ] {
            let completion = match operation {
                GeneratorOperation::Next => GeneratorCompletion::Normal(Value::UNDEFINED),
                GeneratorOperation::Return => GeneratorCompletion::Return(Value::UNDEFINED),
                GeneratorOperation::Throw => GeneratorCompletion::Throw {
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::Bytecode,
                },
            };
            let error = generator_plan(GeneratorPhase::Executing, completion)
                .expect_err("reentrant operation must fail");
            assert_eq!(error.operation(), operation);
            assert!(matches!(
                error.into_failure(),
                EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "generator is already running"
                })
            ));
        }
    }

    #[test]
    fn pending_completions_expose_their_gc_root() {
        let rooted = number(41);
        for completion in [
            GeneratorCompletion::Normal(rooted),
            GeneratorCompletion::Return(rooted),
            GeneratorCompletion::Throw {
                value: rooted,
                origin: ThrowOrigin::Bytecode,
            },
        ] {
            let mut roots = Vec::new();
            completion.visit_roots(|value| roots.push(value));
            assert_eq!(roots, vec![rooted]);
        }
    }

    #[test]
    fn async_throw_rejects_the_implicit_promise() {
        let program = verified(
            vec![Constant::Int32(73)],
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    0,
                    1,
                    FunctionFlags {
                        is_async: true,
                        is_generator: false,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(0),
                        },
                        Instruction::Throw { value: reg(0) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let promise = start_async_function(
            &mut machine,
            RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        )
        .expect("async call returns its implicit promise");
        let index = machine
            .runtime_slot(promise)
            .unwrap()
            .expect("promise is a runtime object");
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::Promise {
                state: PromiseState::Rejected { .. },
                ..
            }
        ));
    }

    #[test]
    fn await_resumes_from_one_fifo_microtask_before_settling() {
        let program = verified(
            vec![Constant::Int32(83)],
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    0,
                    2,
                    FunctionFlags {
                        is_async: true,
                        is_generator: false,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(0),
                        },
                        Instruction::Await {
                            dst: reg(1),
                            src: reg(0),
                            resume: pc(2),
                        },
                        Instruction::Return { value: reg(1) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let promise = start_async_function(
            &mut machine,
            RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        )
        .expect("async call suspends on await");
        let index = machine
            .runtime_slot(promise)
            .unwrap()
            .expect("promise is a runtime object");
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            }
        ));

        let report = machine
            .drain_microtasks()
            .expect("await reaction drains successfully");
        assert_eq!(
            report.executed, 1,
            "await resumes from exactly one FIFO job"
        );
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } if *value == number(83)
        ));
    }

    #[test]
    fn rejected_await_injects_throw_and_rejects_async_result() {
        let program = verified(
            Vec::new(),
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    1,
                    2,
                    FunctionFlags {
                        is_async: true,
                        is_generator: false,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
                    vec![
                        Instruction::Await {
                            dst: reg(1),
                            src: reg(0),
                            resume: pc(1),
                        },
                        Instruction::Return { value: reg(1) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let awaited = machine.create_promise().expect("awaited promise allocates");
        machine
            .reject_promise(awaited, number(89), ThrowOrigin::Bytecode)
            .expect("awaited promise rejects");
        let result = start_async_function(
            &mut machine,
            RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[awaited],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        )
        .expect("async function suspends on rejected promise");

        machine
            .drain_microtasks()
            .expect("rejection reaction resumes async function");
        let index = machine
            .runtime_slot(result)
            .unwrap()
            .expect("async result is a runtime promise");
        assert!(matches!(
            &machine.heap[index],
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, .. },
                ..
            } if *reason == number(89)
        ));
    }

    #[test]
    fn suspended_generator_activation_keeps_captured_gc_roots_alive() {
        let program = verified(
            Vec::new(),
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    1,
                    3,
                    FunctionFlags {
                        is_async: false,
                        is_generator: true,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
                    vec![
                        Instruction::Suspend {
                            dst: reg(1),
                            src: reg(0),
                            resume: pc(1),
                            mode: reg(2),
                        },
                        Instruction::Suspend {
                            dst: reg(1),
                            src: reg(0),
                            resume: pc(2),
                            mode: reg(2),
                        },
                        Instruction::Return { value: reg(1) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let captured = machine
            .allocate(HeapEntry::String(bamts_bytecode::EcmaString::encode(
                "captured",
            )))
            .expect("captured heap value allocates");
        let generator = machine
            .create_generator(GeneratorStart {
                target: RuntimeFunction {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                },
                captures: vec![captured],
                context: None,
                this_value: Value::UNDEFINED,
                new_target: Value::UNDEFINED,
                args: Vec::new(),
            })
            .expect("generator allocates");
        machine.test_set_global("rootedGenerator", generator);
        machine
            .resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED))
            .expect("first next suspends");

        machine.collect_garbage();

        let result = machine
            .resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED))
            .expect("second next observes retained capture");
        assert_eq!(
            machine
                .get_named_property(result, "value")
                .expect("iterator result value is readable"),
            captured
        );
    }

    #[test]
    fn for_await_over_sync_array_completes_through_async_from_sync() {
        use crate::IteratorKind;
        let program = verified(
            vec![Constant::Int32(42), Constant::Undefined],
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    0,
                    8,
                    FunctionFlags {
                        is_async: true,
                        is_generator: false,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
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
                            dst: reg(1),
                            src: reg(0),
                            kind: IteratorKind::Async,
                        },
                        Instruction::LoadConst {
                            dst: reg(6),
                            constant: cid(1),
                        },
                        // loop head @5
                        Instruction::IteratorStep {
                            dst: reg(2),
                            iterator: reg(1),
                        },
                        Instruction::Await {
                            dst: reg(3),
                            src: reg(2),
                            resume: pc(7),
                        },
                        Instruction::IteratorResult {
                            done: reg(4),
                            value: reg(5),
                            result: reg(3),
                        },
                        Instruction::JumpIfTrue {
                            condition: reg(4),
                            target: pc(11),
                        },
                        // body @9
                        Instruction::Move {
                            dst: reg(6),
                            src: reg(5),
                        },
                        // loop back @10
                        Instruction::Jump { target: pc(5) },
                        // exit @11
                        Instruction::Return { value: reg(6) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let promise = start_async_function(
            &mut machine,
            RuntimeFunction {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
            },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        )
        .expect("async function starts");
        machine
            .drain_microtasks()
            .expect("microtask drain completes the async function");
        let index = machine
            .runtime_slot(promise)
            .unwrap()
            .expect("promise is a runtime object");
        assert!(
            matches!(
                &machine.heap[index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled { value },
                    ..
                } if *value == number(42)
            ),
            "for-await-of over [42] should fulfill with 42"
        );
    }

    #[test]
    fn async_generator_throw_on_suspended_start_then_next_completes() {
        let program = verified(
            vec![Constant::Int32(99)],
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    0,
                    2,
                    FunctionFlags {
                        is_async: true,
                        is_generator: true,
                        is_constructable: false,
                        ..FunctionFlags::default()
                    },
                    vec![
                        Instruction::LoadConst {
                            dst: reg(0),
                            constant: cid(0),
                        },
                        Instruction::Throw { value: reg(0) },
                    ],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let generator = machine
            .create_async_generator(GeneratorStart {
                target: RuntimeFunction {
                    module: ModuleId::new(0),
                    function: FunctionId::new(1),
                },
                captures: Vec::new(),
                context: None,
                this_value: Value::UNDEFINED,
                new_target: Value::UNDEFINED,
                args: Vec::new(),
            })
            .expect("async generator allocates");
        // throw on SuspendedStart: completes the generator and rejects the
        // front request promise.
        let throw_method = machine.get_named_property(generator, "throw").unwrap();
        let throw_promise = machine
            .call_value(throw_method, generator, &[number(99)])
            .expect("throw returns a promise");
        let throw_index = machine
            .runtime_slot(throw_promise)
            .unwrap()
            .expect("throw promise is a runtime object");
        assert!(
            matches!(
                &machine.heap[throw_index],
                HeapEntry::Promise {
                    state: PromiseState::Rejected { .. },
                    ..
                }
            ),
            "throw on SuspendedStart rejects immediately"
        );
        let next_method = machine.get_named_property(generator, "next").unwrap();
        let next_promise = machine
            .call_value(next_method, generator, &[Value::UNDEFINED])
            .expect("next returns a promise");
        let next_index = machine
            .runtime_slot(next_promise)
            .unwrap()
            .expect("next promise is a runtime object");
        assert!(
            matches!(
                &machine.heap[next_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled { .. },
                    ..
                }
            ),
            "next on Completed resolves with done:true"
        );
    }
    #[test]
    fn promise_rejection_propagates_through_then_chain() {
        let program = verified(
            Vec::new(),
            vec![
                function(0, 0, FunctionFlags::default(), vec![Instruction::Halt]),
                function(
                    1,
                    1,
                    FunctionFlags::default(),
                    vec![Instruction::Return { value: reg(0) }],
                ),
            ],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());

        let promise = machine.create_promise().unwrap();
        let handler = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap();

        let then_method = machine.get_named_property(promise, "then").unwrap();
        let derived = machine
            .call_value(then_method, promise, &[handler, handler])
            .unwrap();

        let done_handler = machine
            .allocate(HeapEntry::Function {
                module: ModuleId::new(0),
                function: FunctionId::new(1),
                captures: Vec::new(),
                context: None,
                properties: PropertyMap::default(),
                prototype: Some(machine.intrinsics.function_prototype),
                extensible: true,
            })
            .unwrap();
        let then_method2 = machine.get_named_property(derived, "then").unwrap();
        let final_promise = machine
            .call_value(then_method2, derived, &[done_handler, done_handler])
            .unwrap();

        machine
            .reject_promise(promise, number(42), ThrowOrigin::Bytecode)
            .unwrap();

        machine
            .drain_microtasks()
            .expect("microtask drain completes the chain");

        let final_index = machine
            .runtime_slot(final_promise)
            .unwrap()
            .expect("final promise is a runtime object");
        assert!(
            matches!(
                &machine.heap[final_index],
                HeapEntry::Promise {
                    state: PromiseState::Fulfilled { .. },
                    ..
                }
            ),
            "rejection chain should fulfill the final derived promise"
        );
    }
}
