#![cfg(feature = "host-jit")]

use std::collections::BTreeSet;

use bamts_bytecode::{
    AccessorKind, BinaryOp, Constant, ConstantId, EcmaString, Function, FunctionFlags, FunctionId,
    Instruction, Module, ModuleId, Pc, Program, ProgramModule, Register, Verified,
};
use bamts_codegen::compile_jit;
use bamts_codegen::helpers::{
    HelperDemand, ISA_REPRESENTATIVES, STRUCTURAL_HELPERS, helper_demand, verify_helper_coverage,
};
use bamts_native::tiering::{
    DeoptReason, OsrEntry, Tier, TierTransition, TieringState, WarmupPolicy,
    verify_tiering_contract,
};
use bamts_native::{Completion, CompletionTag, NativeEntryTable, ShadowFrame, Value};
use bamts_runtime::{
    CancellationToken, Host, Limits, NativeError, RuntimeError, RuntimeErrorKind, TieredRunReport,
    UnitTieringSummary, run as run_interpreter, run_linked_program, run_linked_program_tiered,
};

#[derive(Default)]
struct RecordingHost {
    stdout: Vec<u8>,
}

impl Host for RecordingHost {
    fn write_stdout(&mut self, bytes: &[u8]) {
        self.stdout.extend_from_slice(bytes);
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Observable {
    Normal { stdout: Vec<u8>, exit_code: i32 },
    Abrupt(RuntimeError),
}

fn function(register_count: u32, code: Vec<Instruction>) -> Function {
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

fn program(
    constants: Vec<Constant>,
    register_count: u32,
    code: Vec<Instruction>,
) -> Program<Verified> {
    let module = ProgramModule {
        name: ConstantId::new(0),
        code: Module::new(
            constants,
            vec![function(register_count, code)],
            FunctionId::new(0),
        )
        .verify()
        .expect("stress fixture must verify"),
        edges: Vec::new(),
        bindings: Vec::new(),
        exports: Vec::new(),
    };
    Program::link(vec![module], ModuleId::new(0)).expect("stress fixture must link")
}

fn interpreter(program: &Program<Verified>, limits: &Limits) -> Observable {
    let mut host = RecordingHost::default();
    match run_interpreter(program, &mut host, limits) {
        Ok(outcome) => Observable::Normal {
            stdout: host.stdout,
            exit_code: outcome.exit_code,
        },
        Err(error) => Observable::Abrupt(error),
    }
}

fn jit(program: &Program<Verified>, limits: &Limits) -> Observable {
    let compiled = compile_jit(program).expect("stress fixture must compile to native code");
    assert_eq!(
        compiled.program_bytes(),
        program.encode(),
        "a published JIT artifact must remain bound to the exact verified program",
    );
    let mut host = RecordingHost::default();
    match run_linked_program(program, &compiled, &mut host, limits) {
        Ok(outcome) => Observable::Normal {
            stdout: host.stdout,
            exit_code: outcome.exit_code,
        },
        Err(NativeError::Runtime(error)) => Observable::Abrupt(error),
        Err(error) => panic!("native-only failure without interpreter analogue: {error:?}"),
    }
}

fn assert_differential(name: &str, program: &Program<Verified>, limits: &Limits) {
    let expected = interpreter(program, limits);
    let actual = jit(program, limits);
    assert_eq!(actual, expected, "interpreter/JIT mismatch in {name}");
}

fn reg(index: u32) -> Register {
    Register::new(index)
}

fn cid(index: u32) -> ConstantId {
    ConstantId::new(index)
}

/// Emits one observable value through the real `print` host builtin. The
/// computation before this suffix is therefore visible on both execution paths.
fn print_suffix(value: Register, scratch: u32) -> Vec<Instruction> {
    vec![
        Instruction::LoadGlobal {
            dst: reg(scratch),
            name: cid(1),
        },
        Instruction::CreateArray {
            dst: reg(scratch + 1),
        },
        Instruction::ArrayPush {
            array: reg(scratch + 1),
            value,
        },
        Instruction::LoadConst {
            dst: reg(scratch + 2),
            constant: cid(2),
        },
        Instruction::Call {
            dst: reg(scratch + 3),
            callee: reg(scratch),
            this_value: reg(scratch + 2),
            arguments: reg(scratch + 1),
        },
        Instruction::Halt,
    ]
}

fn arithmetic_program(left: i32, right: i32, op: BinaryOp) -> Program<Verified> {
    let mut code = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(3),
        },
        Instruction::LoadConst {
            dst: reg(1),
            constant: cid(4),
        },
        Instruction::Binary {
            dst: reg(2),
            op,
            left: reg(0),
            right: reg(1),
        },
    ];
    code.extend(print_suffix(reg(2), 3));
    program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::String(EcmaString::encode("print")),
            Constant::Undefined,
            Constant::Int32(left),
            Constant::Int32(right),
        ],
        7,
        code,
    )
}

#[derive(Clone, Copy)]
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 32) as u32
    }

    fn operand(&mut self) -> i32 {
        (self.next() % 2_001) as i32 - 1_000
    }
}

#[test]
fn every_classified_opcode_and_helper_is_accounted_for() {
    verify_helper_coverage().expect("the landed helper classifier must cover the complete ISA");

    let mut helpers = BTreeSet::new();
    for helper in STRUCTURAL_HELPERS {
        helpers.insert(helper.external_index());
    }
    for instruction in ISA_REPRESENTATIVES {
        match helper_demand(instruction) {
            HelperDemand::Inline => {}
            HelperDemand::Call(helper) => {
                helpers.insert(helper.external_index());
            }
            HelperDemand::Missing { name, contract } => {
                panic!("classified opcode still lacks real helper {name}: {contract}")
            }
        }
    }

    let expected: BTreeSet<_> = (0..bamts_native::HELPER_COUNT).collect();
    assert_eq!(helpers, expected, "every runtime helper must be reachable");
    assert_eq!(ISA_REPRESENTATIVES.len(), 59, "append-only ISA changed");
    assert_eq!(helpers.len(), 54, "runtime helper namespace changed");
}

#[test]
fn deterministic_seeded_arithmetic_matches_interpreter() {
    const SEEDS: [u64; 8] = [
        0,
        1,
        0x5eed,
        0xdead_beef,
        0x0123_4567_89ab_cdef,
        0x8000_0000_0000_0000,
        u64::MAX - 1,
        u64::MAX,
    ];
    const OPS: [BinaryOp; 20] = [
        BinaryOp::Add,
        BinaryOp::Subtract,
        BinaryOp::Multiply,
        BinaryOp::Divide,
        BinaryOp::Remainder,
        BinaryOp::Exponent,
        BinaryOp::BitAnd,
        BinaryOp::BitOr,
        BinaryOp::BitXor,
        BinaryOp::ShiftLeft,
        BinaryOp::ShiftRight,
        BinaryOp::UnsignedShiftRight,
        BinaryOp::Equal,
        BinaryOp::NotEqual,
        BinaryOp::StrictEqual,
        BinaryOp::StrictNotEqual,
        BinaryOp::LessThan,
        BinaryOp::LessThanOrEqual,
        BinaryOp::GreaterThan,
        BinaryOp::GreaterThanOrEqual,
    ];

    for seed in SEEDS {
        let mut random = Lcg(seed);
        for (index, op) in OPS.into_iter().enumerate() {
            let left = random.operand();
            let mut right = random.operand();
            if matches!(op, BinaryOp::Divide | BinaryOp::Remainder) && right == 0 {
                right = 1;
            }
            let case = arithmetic_program(left, right, op);
            assert_differential(
                &format!("seed={seed:#018x}, operator={index}, operands=({left},{right})"),
                &case,
                &Limits::default(),
            );
            // A second compilation proves the corpus is deterministic and that
            // publication does not retain or patch the first executable image.
            assert_differential(
                &format!("repeat seed={seed:#018x}, operator={index}"),
                &case,
                &Limits::default(),
            );
        }
    }
}

#[test]
fn branches_moves_and_normal_completion_match_interpreter() {
    let mut code = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(3),
        },
        Instruction::Move {
            dst: reg(1),
            src: reg(0),
        },
        Instruction::JumpIfFalse {
            condition: reg(1),
            target: Pc::new(5),
        },
        Instruction::LoadConst {
            dst: reg(2),
            constant: cid(4),
        },
        Instruction::Jump { target: Pc::new(6) },
        Instruction::LoadConst {
            dst: reg(2),
            constant: cid(5),
        },
    ];
    code.extend(print_suffix(reg(2), 3));
    let case = program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::String(EcmaString::encode("print")),
            Constant::Undefined,
            Constant::Boolean(true),
            Constant::Int32(11),
            Constant::Int32(99),
        ],
        7,
        code,
    );
    assert_differential("branch/move/normal", &case, &Limits::default());
}

#[test]
fn abrupt_throw_and_fuel_deopt_match_interpreter() {
    let thrown = program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::Int32(0x2a),
        ],
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(1),
            },
            Instruction::Throw { value: reg(0) },
        ],
    );
    assert_differential("uncaught throw", &thrown, &Limits::default());

    let spin = program(
        vec![Constant::String(EcmaString::encode("entry"))],
        0,
        vec![Instruction::Jump { target: Pc::new(0) }],
    );
    assert_differential(
        "fuel deopt",
        &spin,
        &Limits {
            fuel: 31,
            ..Limits::default()
        },
    );
}

#[test]
fn osr_deopt_and_cancellation_are_exact_and_terminal() {
    verify_tiering_contract().expect("landed tiering contract must pass");
    let policy = WarmupPolicy {
        baseline_invocations: 3,
        optimized_invocations: 5,
        osr_back_edges: 4,
        deopt_budget: 2,
    };

    let mut warm = TieringState::new(policy).expect("valid stress policy");
    assert_eq!(warm.observe_invocation(), None);
    assert_eq!(warm.observe_invocation(), None);
    assert_eq!(
        warm.observe_invocation(),
        Some(TierTransition {
            from: Tier::Interpreter,
            to: Tier::Baseline,
        })
    );
    assert_eq!(warm.observe_invocation(), None);
    assert_eq!(
        warm.observe_invocation(),
        Some(TierTransition {
            from: Tier::Baseline,
            to: Tier::Optimized,
        })
    );

    let mut osr = TieringState::new(policy).expect("valid stress policy");
    for _ in 0..policy.osr_back_edges - 1 {
        assert_eq!(osr.observe_back_edge(Pc::new(2), Pc::new(9)), None);
    }
    assert_eq!(
        osr.observe_back_edge(Pc::new(2), Pc::new(9)),
        Some(OsrEntry { pc: Pc::new(2) })
    );
    assert_eq!(
        osr.observe_back_edge(Pc::new(9), Pc::new(2)),
        None,
        "forward edges must never become OSR entries"
    );

    assert_eq!(warm.record_deopt(DeoptReason::Panic), Tier::Interpreter);
    assert!(!warm.is_pinned());
    assert_eq!(
        warm.record_deopt(DeoptReason::InvalidRegister),
        Tier::Interpreter
    );
    assert!(warm.is_pinned());
    for _ in 0..policy.optimized_invocations {
        assert_eq!(warm.observe_invocation(), None);
    }

    let mut cancelled = TieringState::new(policy).expect("valid stress policy");
    cancelled.cancel();
    cancelled.cancel();
    assert!(cancelled.is_cancelled());
    assert_eq!(cancelled.observe_invocation(), None);
    assert_eq!(cancelled.observe_back_edge(Pc::new(0), Pc::new(1)), None);
    assert_eq!(
        cancelled.record_deopt(DeoptReason::Panic),
        Tier::Interpreter
    );
    assert!(!cancelled.is_pinned());
}

#[test]
fn executable_publication_is_repeatable_and_program_bound() {
    // `compile_jit` cannot construct `JitProgram` until the private W^X handle
    // has sealed every mapping and minted its FinalizedMemory receipt. Repeated
    // compile/run/drop cycles exercise the public consequence without exposing
    // writable pages or raw entry pointers to this integration test.
    for seed in 0..32 {
        let case = arithmetic_program(seed, seed.wrapping_mul(17), BinaryOp::BitXor);
        let expected = interpreter(&case, &Limits::default());
        for generation in 0..3 {
            let actual = jit(&case, &Limits::default());
            assert_eq!(
                actual, expected,
                "W^X publication changed result at seed {seed}, generation {generation}"
            );
        }
    }
}
fn tiered(
    program: &Program<Verified>,
    limits: &Limits,
    policy: WarmupPolicy,
) -> (Observable, TieredRunReport) {
    let compiled = compile_jit(program).expect("stress fixture must compile to native code");
    assert_eq!(
        compiled.program_bytes(),
        program.encode(),
        "a published JIT artifact must remain bound to the exact verified program",
    );
    let mut host = RecordingHost::default();
    let (outcome, report) = run_linked_program_tiered(
        program,
        &compiled,
        &mut host,
        limits,
        policy,
        CancellationToken::new(),
    )
    .expect("tiered run links");
    let observable = match outcome {
        Ok(outcome) => Observable::Normal {
            stdout: host.stdout,
            exit_code: outcome.exit_code,
        },
        Err(NativeError::Runtime(error)) => Observable::Abrupt(error),
        Err(error) => panic!("native-only failure without interpreter analogue: {error:?}"),
    };
    (observable, report)
}

fn osr_only_policy() -> WarmupPolicy {
    WarmupPolicy {
        baseline_invocations: u32::MAX,
        optimized_invocations: u32::MAX,
        osr_back_edges: 2,
        deopt_budget: 8,
    }
}

fn entry_summary(report: &TieredRunReport) -> &UnitTieringSummary {
    report
        .units
        .iter()
        .find(|unit| unit.module == ModuleId::new(0) && unit.function == FunctionId::new(0))
        .expect("entry unit is reported")
}

fn loop_print_program(iterations: i32) -> Program<Verified> {
    let code = vec![
        Instruction::LoadGlobal {
            dst: reg(7),
            name: cid(1),
        },
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(3),
        },
        Instruction::LoadConst {
            dst: reg(1),
            constant: cid(4),
        },
        Instruction::LoadConst {
            dst: reg(2),
            constant: cid(5),
        },
        Instruction::Binary {
            dst: reg(3),
            op: BinaryOp::LessThan,
            left: reg(0),
            right: reg(1),
        },
        Instruction::JumpIfFalse {
            condition: reg(3),
            target: Pc::new(12),
        },
        Instruction::CreateArray { dst: reg(6) },
        Instruction::ArrayPush {
            array: reg(6),
            value: reg(0),
        },
        Instruction::LoadConst {
            dst: reg(9),
            constant: cid(2),
        },
        Instruction::Call {
            dst: reg(8),
            callee: reg(7),
            this_value: reg(9),
            arguments: reg(6),
        },
        Instruction::Binary {
            dst: reg(0),
            op: BinaryOp::Add,
            left: reg(0),
            right: reg(2),
        },
        Instruction::Jump { target: Pc::new(4) },
        Instruction::Halt,
    ];
    program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::String(EcmaString::encode("print")),
            Constant::Undefined,
            Constant::Int32(0),
            Constant::Int32(iterations),
            Constant::Int32(1),
        ],
        10,
        code,
    )
}

fn loop_throw_program() -> Program<Verified> {
    let constants = vec![
        Constant::String(EcmaString::encode("entry")),
        Constant::String(EcmaString::encode("print")),
        Constant::Undefined,
        Constant::Int32(0),
        Constant::Int32(5),
        Constant::Int32(3),
        Constant::Int32(1),
        Constant::Int32(99),
    ];
    let entry = Function::new(
        None,
        0,
        0,
        10,
        FunctionFlags::default(),
        vec![
            Instruction::LoadGlobal {
                dst: reg(6),
                name: cid(1),
            },
            Instruction::CreateArray { dst: reg(0) },
            Instruction::CreateClosure {
                dst: reg(1),
                function: FunctionId::new(1),
                captures: reg(0),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(2),
            },
            Instruction::CreateArray { dst: reg(3) },
            Instruction::Call {
                dst: reg(4),
                callee: reg(1),
                this_value: reg(2),
                arguments: reg(3),
            },
            Instruction::Halt,
            Instruction::CreateArray { dst: reg(7) },
            Instruction::ArrayPush {
                array: reg(7),
                value: reg(5),
            },
            Instruction::LoadConst {
                dst: reg(8),
                constant: cid(2),
            },
            Instruction::Call {
                dst: reg(9),
                callee: reg(6),
                this_value: reg(8),
                arguments: reg(7),
            },
            Instruction::Halt,
        ],
        vec![bamts_bytecode::ExceptionHandler {
            start: Pc::new(5),
            end: Pc::new(6),
            handler: Pc::new(7),
            catch_register: reg(5),
        }],
    );
    let callee = Function::new(
        None,
        0,
        0,
        11,
        FunctionFlags::default(),
        vec![
            Instruction::LoadGlobal {
                dst: reg(7),
                name: cid(1),
            },
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(3),
            },
            Instruction::LoadConst {
                dst: reg(1),
                constant: cid(4),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(6),
            },
            Instruction::LoadConst {
                dst: reg(4),
                constant: cid(5),
            },
            Instruction::LoadConst {
                dst: reg(9),
                constant: cid(7),
            },
            Instruction::Binary {
                dst: reg(3),
                op: BinaryOp::LessThan,
                left: reg(0),
                right: reg(1),
            },
            Instruction::JumpIfFalse {
                condition: reg(3),
                target: Pc::new(17),
            },
            Instruction::Binary {
                dst: reg(5),
                op: BinaryOp::Equal,
                left: reg(0),
                right: reg(4),
            },
            Instruction::JumpIfTrue {
                condition: reg(5),
                target: Pc::new(16),
            },
            Instruction::CreateArray { dst: reg(6) },
            Instruction::ArrayPush {
                array: reg(6),
                value: reg(0),
            },
            Instruction::LoadConst {
                dst: reg(8),
                constant: cid(2),
            },
            Instruction::Call {
                dst: reg(10),
                callee: reg(7),
                this_value: reg(8),
                arguments: reg(6),
            },
            Instruction::Binary {
                dst: reg(0),
                op: BinaryOp::Add,
                left: reg(0),
                right: reg(2),
            },
            Instruction::Jump { target: Pc::new(6) },
            Instruction::Throw { value: reg(9) },
            Instruction::Halt,
        ],
        Vec::new(),
    );
    let module = Module::new(constants, vec![entry, callee], FunctionId::new(0))
        .verify()
        .expect("stress fixture must verify");
    let module = ProgramModule {
        name: ConstantId::new(0),
        code: module,
        edges: Vec::new(),
        bindings: Vec::new(),
        exports: Vec::new(),
    };
    Program::link(vec![module], ModuleId::new(0)).expect("stress fixture must link")
}

fn generator_loop_program() -> Program<Verified> {
    let code = vec![
        Instruction::LoadConst {
            dst: reg(3),
            constant: cid(2),
        },
        Instruction::LoadConst {
            dst: reg(4),
            constant: cid(3),
        },
        Instruction::LoadConst {
            dst: reg(5),
            constant: cid(4),
        },
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(1),
        },
        Instruction::Suspend {
            dst: reg(1),
            src: reg(0),
            resume: Pc::new(5),
            mode: reg(2),
        },
        Instruction::Binary {
            dst: reg(0),
            op: BinaryOp::LessThan,
            left: reg(3),
            right: reg(4),
        },
        Instruction::JumpIfFalse {
            condition: reg(0),
            target: Pc::new(9),
        },
        Instruction::Binary {
            dst: reg(3),
            op: BinaryOp::Add,
            left: reg(3),
            right: reg(5),
        },
        Instruction::Jump { target: Pc::new(5) },
        Instruction::Return { value: reg(3) },
    ];
    let module = Module::new(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::Int32(1),
            Constant::Int32(0),
            Constant::Int32(3),
            Constant::Int32(1),
        ],
        vec![Function::new(
            None,
            0,
            0,
            6,
            FunctionFlags {
                is_async: false,
                is_generator: true,
                is_constructable: false,
                ..FunctionFlags::default()
            },
            code,
            Vec::new(),
        )],
        FunctionId::new(0),
    )
    .verify()
    .expect("stress fixture must verify");
    let module = ProgramModule {
        name: ConstantId::new(0),
        code: module,
        edges: Vec::new(),
        bindings: Vec::new(),
        exports: Vec::new(),
    };
    Program::link(vec![module], ModuleId::new(0)).expect("stress fixture must link")
}

#[test]
fn tiered_first_call_promotes_to_baseline_and_matches_interpreter() {
    let case = arithmetic_program(19, 23, BinaryOp::Add);
    let expected = interpreter(&case, &Limits::default());
    let (actual, report) = tiered(&case, &Limits::default(), WarmupPolicy::DEFAULT);
    assert_eq!(
        actual, expected,
        "tiered baseline must match the interpreter"
    );
    let entry = entry_summary(&report);
    assert_eq!(
        entry.tier,
        Tier::Baseline,
        "one call promotes under the shipped policy"
    );
    assert_eq!(entry.deopts, 0);
}

#[test]
fn tiered_loop_enters_at_header_with_identical_side_effects() {
    let case = loop_print_program(5);
    let expected = interpreter(&case, &Limits::default());
    let (actual, report) = tiered(&case, &Limits::default(), osr_only_policy());
    assert_eq!(
        actual, expected,
        "restarting at pc 0 would duplicate the prefix"
    );
    let entry = entry_summary(&report);
    assert!(
        entry.osr_entries > 0,
        "the loop must transfer into compiled code"
    );
    assert_eq!(
        entry.deopts, 0,
        "a refused entry deoptimizes and must not pass"
    );
    assert_eq!(entry.tier, Tier::Interpreter);
}

#[test]
fn tiered_loop_throw_reaches_handler_with_identical_output() {
    let case = loop_throw_program();
    let expected = interpreter(&case, &Limits::default());
    let (actual, report) = tiered(&case, &Limits::default(), osr_only_policy());
    assert_eq!(
        actual, expected,
        "compiled throw must reach the same handler"
    );
    let callee = report
        .units
        .iter()
        .find(|unit| unit.module == ModuleId::new(0) && unit.function == FunctionId::new(1))
        .expect("callee unit is reported");
    assert!(
        callee.osr_entries > 0,
        "the loop must transfer before it throws"
    );
    assert_eq!(
        callee.deopts, 0,
        "the throw is ordinary completion, not a deopt"
    );
}

#[test]
fn tiered_corpus_matches_interpreter() {
    let policy = osr_only_policy();
    for seed in [0u64, 1, 0x5eed] {
        let low = i32::try_from(seed).expect("seed fits in i32");
        let high = i32::try_from(seed >> 32).expect("seed fits in i32");
        let case = arithmetic_program(low, high, BinaryOp::Add);
        let expected = interpreter(&case, &Limits::default());
        let (actual, _) = tiered(&case, &Limits::default(), policy);
        assert_eq!(actual, expected, "tiered corpus mismatch at seed {seed}");
    }
    let branch = program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::String(EcmaString::encode("print")),
            Constant::Undefined,
            Constant::Boolean(true),
            Constant::Int32(11),
            Constant::Int32(99),
        ],
        7,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(3),
            },
            Instruction::Move {
                dst: reg(1),
                src: reg(0),
            },
            Instruction::JumpIfFalse {
                condition: reg(1),
                target: Pc::new(5),
            },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(4),
            },
            Instruction::Jump { target: Pc::new(6) },
            Instruction::LoadConst {
                dst: reg(2),
                constant: cid(5),
            },
            Instruction::LoadGlobal {
                dst: reg(3),
                name: cid(1),
            },
            Instruction::CreateArray { dst: reg(4) },
            Instruction::ArrayPush {
                array: reg(4),
                value: reg(2),
            },
            Instruction::LoadConst {
                dst: reg(5),
                constant: cid(2),
            },
            Instruction::Call {
                dst: reg(6),
                callee: reg(3),
                this_value: reg(5),
                arguments: reg(4),
            },
            Instruction::Halt,
        ],
    );
    let expected = interpreter(&branch, &Limits::default());
    let (actual, _) = tiered(&branch, &Limits::default(), policy);
    assert_eq!(actual, expected, "tiered branch mismatch");
    let thrown = program(
        vec![
            Constant::String(EcmaString::encode("entry")),
            Constant::Int32(0x2a),
        ],
        1,
        vec![
            Instruction::LoadConst {
                dst: reg(0),
                constant: cid(1),
            },
            Instruction::Throw { value: reg(0) },
        ],
    );
    let expected = interpreter(&thrown, &Limits::default());
    let (actual, _) = tiered(&thrown, &Limits::default(), policy);
    assert_eq!(actual, expected, "tiered throw mismatch");
}

#[test]
fn generator_loop_dispatch_accepts_resume_and_osr_tokens() {
    let program = generator_loop_program();
    let compiled = compile_jit(&program).expect("generator loop must compile");
    let mut registers = vec![Value::UNDEFINED; 6];
    let mut run = |token: u32| {
        let mut shadow =
            ShadowFrame::new(std::ptr::null_mut(), token, 0, registers.as_mut_ptr(), 6);
        let mut out = Completion::new(Value::UNDEFINED);
        let tag = compiled.invoke(0, 0, &mut shadow, &mut out);
        (tag, out.value.as_int32(), out.value.to_bits())
    };
    let (tag, id, _) = run(5);
    assert_eq!(tag, Ok(CompletionTag::FatalTrap));
    assert_eq!(id, Some(bamts_native::TRAP_MISSING_NATIVE_OPS));
    let (tag, id, _) = run(0x8000_0000u32 | 5);
    assert_eq!(tag, Ok(CompletionTag::FatalTrap));
    assert_eq!(id, Some(bamts_native::TRAP_MISSING_NATIVE_OPS));
    let (tag, _, bits) = run(0x1234);
    assert_eq!(tag, Ok(CompletionTag::FatalTrap));
    assert_eq!(bits, 1);
}

fn module_program(constants: Vec<Constant>, functions: Vec<Function>) -> Program<Verified> {
    let module = ProgramModule {
        name: ConstantId::new(0),
        code: Module::new(constants, functions, FunctionId::new(0))
            .verify()
            .expect("global binding fixture must verify"),
        edges: Vec::new(),
        bindings: Vec::new(),
        exports: Vec::new(),
    };
    Program::link(vec![module], ModuleId::new(0)).expect("global binding fixture must link")
}

fn global_binding_constants() -> Vec<Constant> {
    vec![
        Constant::String(EcmaString::encode("entry")),
        Constant::String(EcmaString::encode("print")),
        Constant::Undefined,
        Constant::String(EcmaString::encode("globalThis")),
        Constant::String(EcmaString::encode("gets")),
        Constant::String(EcmaString::encode("sets")),
        Constant::String(EcmaString::encode("x")),
        Constant::Int32(0),
        Constant::Int32(1),
        Constant::Int32(100),
        Constant::Int32(41),
        Constant::String(EcmaString::encode("undeclared")),
    ]
}

fn counter_bump(counter: u32, base: u32) -> [Instruction; 3] {
    [
        Instruction::LoadGlobal {
            dst: reg(base),
            name: cid(counter),
        },
        Instruction::Binary {
            dst: reg(base),
            op: BinaryOp::Add,
            left: reg(base),
            right: reg(base + 1),
        },
        Instruction::StoreGlobal {
            name: cid(counter),
            value: reg(base),
        },
    ]
}

/// A strict script that installs a counting accessor pair on global `x`,
/// ends its getter with `getter_tail`, runs `assignment`, and prints `gets * 100 + sets`.
fn global_accessor_program(getter_tail: Instruction, assignment: &[Instruction]) -> Program<Verified> {
    let mut entry = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(7),
        },
        Instruction::StoreGlobal {
            name: cid(4),
            value: reg(0),
        },
        Instruction::StoreGlobal {
            name: cid(5),
            value: reg(0),
        },
        Instruction::LoadGlobal {
            dst: reg(1),
            name: cid(3),
        },
        Instruction::CreateArray { dst: reg(2) },
        Instruction::CreateClosure {
            dst: reg(3),
            function: FunctionId::new(1),
            captures: reg(2),
        },
        Instruction::CreateClosure {
            dst: reg(4),
            function: FunctionId::new(2),
            captures: reg(2),
        },
        Instruction::LoadConst {
            dst: reg(5),
            constant: cid(6),
        },
        Instruction::DefineAccessor {
            object: reg(1),
            key: reg(5),
            accessor: reg(3),
            kind: AccessorKind::Getter,
        },
        Instruction::DefineAccessor {
            object: reg(1),
            key: reg(5),
            accessor: reg(4),
            kind: AccessorKind::Setter,
        },
        Instruction::LoadConst {
            dst: reg(8),
            constant: cid(8),
        },
    ];
    entry.extend_from_slice(assignment);
    entry.extend([
        Instruction::LoadGlobal {
            dst: reg(9),
            name: cid(4),
        },
        Instruction::LoadConst {
            dst: reg(10),
            constant: cid(9),
        },
        Instruction::Binary {
            dst: reg(9),
            op: BinaryOp::Multiply,
            left: reg(9),
            right: reg(10),
        },
        Instruction::LoadGlobal {
            dst: reg(10),
            name: cid(5),
        },
        Instruction::Binary {
            dst: reg(9),
            op: BinaryOp::Add,
            left: reg(9),
            right: reg(10),
        },
    ]);
    entry.extend(print_suffix(reg(9), 11));
    let mut getter = vec![Instruction::LoadConst {
        dst: reg(1),
        constant: cid(8),
    }];
    getter.extend(counter_bump(4, 0));
    getter.push(getter_tail);
    getter.push(Instruction::Return { value: reg(0) });
    let mut setter = vec![Instruction::LoadConst {
        dst: reg(2),
        constant: cid(8),
    }];
    setter.extend(counter_bump(5, 1));
    setter.push(Instruction::Return { value: reg(1) });
    module_program(
        global_binding_constants(),
        vec![
            function(15, entry),
            function(2, getter),
            Function::new(None, 0, 1, 3, FunctionFlags::default(), setter, Vec::new()),
        ],
    )
}

fn assert_prints(name: &str, program: &Program<Verified>, expected: &str) {
    assert_differential(name, program, &Limits::default());
    assert_eq!(
        interpreter(program, &Limits::default()),
        Observable::Normal {
            stdout: expected.as_bytes().to_vec(),
            exit_code: 0,
        },
        "{name}"
    );
}

fn assert_uncaught(name: &str, program: &Program<Verified>, constructor: &str, message: &str) {
    assert_differential(name, program, &Limits::default());
    let Observable::Abrupt(error) = interpreter(program, &Limits::default()) else {
        panic!("{name} must throw");
    };
    let RuntimeErrorKind::UncaughtThrow {
        constructor_name,
        message: thrown,
        ..
    } = error.kind
    else {
        panic!("{name} must end in an uncaught throw: {error:?}");
    };
    assert_eq!(constructor_name, Some(EcmaString::encode(constructor)), "{name}");
    assert_eq!(thrown, Some(EcmaString::encode(message)), "{name}");
}

#[test]
fn strict_simple_assignment_runs_only_the_global_setter() {
    let program = global_accessor_program(
        Instruction::Throw { value: reg(0) },
        &[
            Instruction::RequireGlobalBinding { name: cid(6) },
            Instruction::StoreGlobal {
                name: cid(6),
                value: reg(8),
            },
        ],
    );
    assert_prints("x = 1 under a throwing getter", &program, "1\n");
}

#[test]
fn strict_compound_assignment_runs_the_global_getter_once() {
    let program = global_accessor_program(
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(10),
        },
        &[
            Instruction::LoadGlobal {
                dst: reg(6),
                name: cid(6),
            },
            Instruction::Binary {
                dst: reg(6),
                op: BinaryOp::Add,
                left: reg(6),
                right: reg(8),
            },
            Instruction::RequireGlobalBinding { name: cid(6) },
            Instruction::StoreGlobal {
                name: cid(6),
                value: reg(6),
            },
        ],
    );
    assert_prints("y += 1 under a counting getter", &program, "101\n");
}

#[test]
fn strict_assignment_to_an_undeclared_global_throws_and_creates_nothing() {
    let mut code = vec![
        Instruction::LoadConst {
            dst: reg(0),
            constant: cid(8),
        },
        Instruction::RequireGlobalBinding { name: cid(11) },
        Instruction::StoreGlobal {
            name: cid(11),
            value: reg(0),
        },
    ];
    code.extend(print_suffix(reg(0), 1));
    let program = module_program(global_binding_constants(), vec![function(5, code)]);
    assert_uncaught(
        "undeclared = 1",
        &program,
        "ReferenceError",
        "undeclared is not defined",
    );
}
