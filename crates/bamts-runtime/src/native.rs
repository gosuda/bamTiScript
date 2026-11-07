//! The native semantic engine.
//!
//! [`NativeEngine`] is the runtime side of the native-execution ABI. It
//! implements [`bamts_native::NativeOps`] — the panic- and nesting-safe seam the
//! generated `bamts_*` helpers dispatch into — by reusing the *exact* heap,
//! global, host, and value-semantic methods of the interpreter [`Machine`]. It
//! adds no second copy of any JavaScript semantic: `dispatch` funnels every one
//! of the 53 helpers (which cover all 58 opcodes) into the shared [`Machine`]
//! methods, so the interpreter and the native engine agree by construction.
//!
//! What the engine owns beyond the shared semantics is exactly the layer the
//! interpreter's dispatch loop cannot be reused for: its own **activation
//! records** (`this`/`arguments`/`new.target`, resume state), **register
//! lifetime** (each frame's register file is a driver-stack local, never
//! engine state, so a validated [`NativeFrame`] view borrows it disjointly),
//! **completions/handlers**, **suspend/resume**, and **stdout/exit**.
//!
//! # `&self` dispatch and interior mutability
//!
//! [`NativeOps::dispatch`] takes `&self`: a re-entrant helper (a nested `Call`
//! or accessor invocation) dispatches back into the *same* engine on the same
//! thread while an outer `dispatch` is still on the stack. A `&mut self`
//! receiver would make those nested reborrows aliasing UB, so all mutable
//! engine state lives behind [`RefCell`]/[`Cell`]. The invariant that keeps this
//! sound and panic-free: **no borrow guard is ever held across a nested call**
//! ([`NativeEntryTable::invoke`], [`NativeEngine::execute`], or
//! [`NativeEngine::invoke_callee`]). Every `machine`/`activations` borrow is
//! taken, used, and dropped before the nested call begins.
//!
//! # Two backends, one semantic core
//!
//! * **Reference** ([`NativeEngine::run`]) — the compiler-free driver. It walks
//!   verified bytecode, and for every value/heap/host operation constructs the
//!   [`HelperCall`] the code generator would emit and routes it through
//!   [`NativeOps::dispatch`]. Control flow (branches, calls, handler search,
//!   suspend/resume) is the driver's, standing in for the CLIF the AOT/JIT
//!   backend generates. It never invokes [`Machine::run`] or its loop.
//! * **Linked** ([`run_linked_program`]) — the real AOT/JIT path. It installs
//!   the engine as the thread's [`NativeOps`] with
//!   [`bamts_native::with_native_ops`] and invokes compiled entries through a
//!   borrowed [`bamts_native::NativeEntryTable`]; the compiled code calls the
//!   `bamts_*` helpers, which dispatch back into the same engine.
//!
//! Both backends share the identical `dispatch`/`truthy` implementation.
//!
//! No `unsafe` lives here: [`bamts_native::ShadowFrame::new`] and
//! [`bamts_native::NativeFrame::new`] are safe constructors, and all raw-pointer
//! dereferencing stays inside `bamts-native`.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::error::Error;
use std::fmt;
use std::sync::Arc;

use bamts_bytecode::{
    ConstantId, DisposeHint, EcmaString, FunctionId, Instruction, Module, ModuleId, Pc, Program,
    Verified,
};
pub use bamts_native::AbiError;
use bamts_native::tiering::{DeoptReason, Tier, TieringState, WarmupPolicy, deopt_reason};
use bamts_native::{
    Completion, CompletionTag, Decoded, HelperCall, HelperResult, NativeEntryTable, NativeFrame,
    NativeOps, ShadowFrame, Value, with_native_ops, with_native_ops_ref,
};

use crate::intrinsics::BuiltinOutcome;
use crate::vm::generator_async::GeneratorCompletion;
use crate::{
    CalleeKind, EvalFailure, Execution, ExecutionOutcome, GeneratorResume, GeneratorStart,
    GetOutcome, HeapEntry, Host, IteratorNextPrepared, Limits, Machine, Property, PropertyMap,
    RuntimeError, RuntimeErrorKind, SetOutcome, SuspendedActivation, ThrowOrigin,
    accessor_from_selector, binary_from_selector, iterator_kind_from_selector, unary_from_selector,
};

// -- ABI selector encoders (inverse of the shared `*_from_selector` decoders) --
//
// The reference driver holds a `bamts_bytecode` operator enum and must produce
// the raw `u32` selector the code generator would pass, so the value round-trips
// through the same `HelperCall`/`dispatch` seam generated code uses. The mapping
// is byte-identical to `bamts_codegen`'s `*_op_selector` functions.

fn unary_to_selector(op: bamts_bytecode::UnaryOp) -> u32 {
    use bamts_bytecode::UnaryOp;
    match op {
        UnaryOp::Void => 0,
        UnaryOp::TypeOf => 1,
        UnaryOp::Plus => 2,
        UnaryOp::Negate => 3,
        UnaryOp::BitwiseNot => 4,
        UnaryOp::LogicalNot => 5,
        UnaryOp::ToString => 6,
        UnaryOp::ToPropertyKey => 7,
    }
}

fn binary_to_selector(op: bamts_bytecode::BinaryOp) -> u32 {
    use bamts_bytecode::BinaryOp;
    match op {
        BinaryOp::Add => 0,
        BinaryOp::Subtract => 1,
        BinaryOp::Multiply => 2,
        BinaryOp::Divide => 3,
        BinaryOp::Remainder => 4,
        BinaryOp::Exponent => 5,
        BinaryOp::BitAnd => 6,
        BinaryOp::BitOr => 7,
        BinaryOp::BitXor => 8,
        BinaryOp::ShiftLeft => 9,
        BinaryOp::ShiftRight => 10,
        BinaryOp::UnsignedShiftRight => 11,
        BinaryOp::Equal => 12,
        BinaryOp::NotEqual => 13,
        BinaryOp::StrictEqual => 14,
        BinaryOp::StrictNotEqual => 15,
        BinaryOp::LessThan => 16,
        BinaryOp::LessThanOrEqual => 17,
        BinaryOp::GreaterThan => 18,
        BinaryOp::GreaterThanOrEqual => 19,
        BinaryOp::InstanceOf => 20,
        BinaryOp::In => 21,
    }
}

fn iterator_kind_to_selector(kind: bamts_bytecode::IteratorKind) -> u32 {
    use bamts_bytecode::IteratorKind;
    match kind {
        IteratorKind::Sync => 0,
        IteratorKind::Async => 1,
        IteratorKind::Keys => 2,
    }
}

fn iterator_close_mode_to_selector(mode: bamts_bytecode::IteratorCloseMode) -> u32 {
    use bamts_bytecode::IteratorCloseMode;
    match mode {
        IteratorCloseMode::Propagate => 0,
        IteratorCloseMode::PreserveAbrupt => 1,
    }
}

fn dispose_hint_to_selector(hint: DisposeHint) -> u32 {
    match hint {
        DisposeHint::Sync => 0,
        DisposeHint::Async => 1,
    }
}

fn accessor_to_selector(kind: bamts_bytecode::AccessorKind) -> u32 {
    use bamts_bytecode::AccessorKind;
    match kind {
        AccessorKind::Getter => 0,
        AccessorKind::Setter => 1,
        AccessorKind::ClassGetter => 2,
        AccessorKind::ClassSetter => 3,
    }
}

fn descriptor_slot_to_selector(slot: bamts_bytecode::DescriptorSlot) -> u32 {
    use bamts_bytecode::DescriptorSlot;
    match slot {
        DescriptorSlot::Value => 0,
        DescriptorSlot::Getter => 1,
        DescriptorSlot::Setter => 2,
        DescriptorSlot::Entire => 4,
    }
}

fn descriptor_slot_from_selector(selector: u32) -> Option<bamts_bytecode::DescriptorSlot> {
    use bamts_bytecode::DescriptorSlot;
    match selector {
        0 => Some(DescriptorSlot::Value),
        1 => Some(DescriptorSlot::Getter),
        2 => Some(DescriptorSlot::Setter),
        4 => Some(DescriptorSlot::Entire),
        _ => None,
    }
}

// -- Errors ------------------------------------------------------------------

/// A native-execution failure: a runtime error, an AOT/entry linkage error, or
/// an unrecoverable native trap whose completion value carries a trap id.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeError {
    /// A deterministic runtime error (throw, limit, or malformed value).
    Runtime(RuntimeError),
    /// An AOT image or entry-table linkage failure.
    Abi(AbiError),
    /// The entry table was not compiled from the supplied program's canonical bytes.
    ProgramMismatch,
    /// A native entry returned `FatalTrap`; `value` is the raw trap id word.
    FatalTrap { value: Value },
    /// A caller-supplied [`bamts_cancel::CancellationToken`] was triggered.
    Cancelled,
}

impl fmt::Display for NativeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeError::Runtime(error) => write!(formatter, "{error}"),
            NativeError::Abi(error) => write!(formatter, "{error}"),
            NativeError::ProgramMismatch => {
                write!(
                    formatter,
                    "native entries were compiled from different program bytes"
                )
            }
            NativeError::FatalTrap { value } => {
                write!(
                    formatter,
                    "native fatal trap (value {:#018x})",
                    value.to_bits()
                )
            }
            NativeError::Cancelled => formatter.write_str("operation cancelled"),
        }
    }
}

impl Error for NativeError {}

impl From<RuntimeError> for NativeError {
    fn from(error: RuntimeError) -> Self {
        NativeError::Runtime(error)
    }
}

impl From<AbiError> for NativeError {
    fn from(error: AbiError) -> Self {
        NativeError::Abi(error)
    }
}

// -- Engine state ------------------------------------------------------------

/// Which entry-invocation seam a nested runtime call re-enters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Backend {
    /// The compiler-free driver; nested calls recurse into [`NativeEngine::execute`].
    Reference,
    /// Compiled entries; nested calls go through the [`NativeEntryTable`].
    Linked,
}

/// A resolved bytecode owner that outlives a temporary machine borrow.
enum CodeRef<'m> {
    Root(&'m Program<Verified>),
    Dynamic(Arc<Program<Verified>>),
}

impl CodeRef<'_> {
    fn code(&self, module: ModuleId) -> &Module<Verified> {
        match self {
            Self::Root(program) => {
                &program
                    .module(module)
                    .expect("verified native module id remains in bounds")
                    .code
            }
            Self::Dynamic(program) => &program.modules()[0].code,
        }
    }
}

/// A native activation record. It holds only per-call *metadata*; the register
/// file lives as a driver-stack-local `Vec<Value>` so a [`NativeFrame`] can
struct Activation {
    this_value: Value,
    new_target: Value,
    args: Vec<Value>,
    arguments_object: Option<Value>,
    /// The pending GeneratorCompletion delivered to HelperCall::ResumeValue /
    /// [`HelperCall::ResumeMode`] (linked backend).
    pending_resume: Option<GeneratorCompletion>,
    /// The executing function; [`ShadowFrame`] carries only module and pc, so
    /// the activation supplies the function id for sourced errors and handler
    /// lookup at the helper boundary.
    target: crate::RuntimeFunction,
}

/// A thrown value together with its origin, threaded out of `dispatch` through
/// the engine (the native completion ABI carries only a value).
#[derive(Clone, Copy)]
struct PendingThrow {
    value: Value,
    origin: ThrowOrigin,
}

/// How a single driven instruction resolves.
enum Flow {
    /// Advance to the next instruction.
    Next,
    /// Jump to a program counter.
    Goto(usize),
    /// No covering handler; unwind this frame with the thrown value.
    Unwind(Value, ThrowOrigin),
}

/// The observable result of driving one activation to termination.
enum FrameCompletion {
    Normal(Value),
    Unwind(Value, ThrowOrigin, usize),
    Suspend(Value, u32),
}

/// Outcome of an OSR attempt from a taken back edge inside [`NativeEngine::run_frame`].
enum OsrFlow {
    /// Compiled activation finished; unwind the interpreted frame.
    Done(FrameCompletion),
    /// Deopt reconstruction: continue this interpreted frame at `pc`.
    ContinueAt(usize),
}
#[derive(Clone, Copy)]
enum FrameDrive {
    Ordinary,
    GeneratorStart,
    GeneratorResume {
        token: u32,
        completion: GeneratorCompletion,
    },
    /// Re-enter the instruction loop at `pc` (deopt reconstruction).
    Resume {
        pc: usize,
    },
}

/// The result of invoking a callee (runtime function, host entity, or foreign
/// value).
enum InvokeOutcome {
    Value(Value),
    Threw(Value, ThrowOrigin),
    /// An unrecoverable error; the engine's pending trap state is set.
    Fatal,
}

enum ImportFailure {
    Threw(RuntimeError),
    Fatal,
}

/// Per-unit counters returned by a tiered linked run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnitTieringSummary {
    pub module: ModuleId,
    pub function: FunctionId,
    pub invocations: u32,
    pub back_edges: u32,
    pub osr_entries: u32,
    pub deopts: u32,
    pub tier: Tier,
    pub pinned: bool,
    pub cancelled: bool,
}

/// Aggregate tiering report for one [`run_linked_program_tiered`] execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TieredRunReport {
    pub units: Vec<UnitTieringSummary>,
}

/// Live per-unit tiering state for a linked program under a [`WarmupPolicy`].
///
/// Dynamic modules are excluded: they have no compiled entries and stay on the
/// reference path for their lifetime.
struct TieringTable {
    units: std::collections::BTreeMap<(ModuleId, FunctionId), UnitTier>,
}

#[derive(Clone, Copy, Debug)]
struct UnitTier {
    state: TieringState,
    osr_entries: u32,
}

impl TieringTable {
    fn from_program(
        program: &Program<Verified>,
        policy: WarmupPolicy,
    ) -> Result<Self, bamts_native::tiering::TieringError> {
        let mut units = std::collections::BTreeMap::new();
        for (module_index, module) in program.modules().iter().enumerate() {
            let module_id = ModuleId::new(module_index as u32);
            for (function_index, _) in module.code().functions().iter().enumerate() {
                let function_id = FunctionId::new(function_index as u32);
                units.insert(
                    (module_id, function_id),
                    UnitTier {
                        state: TieringState::new(policy)?,
                        osr_entries: 0,
                    },
                );
            }
        }
        Ok(Self { units })
    }

    fn get_mut(&mut self, module: ModuleId, function: FunctionId) -> Option<&mut UnitTier> {
        self.units.get_mut(&(module, function))
    }

    fn cancel_all(&mut self) {
        for unit in self.units.values_mut() {
            unit.state.cancel();
        }
    }

    fn report(&self) -> TieredRunReport {
        let units = self
            .units
            .iter()
            .map(|(&(module, function), unit)| UnitTieringSummary {
                module,
                function,
                invocations: unit.state.invocations(),
                back_edges: unit.state.back_edges(),
                osr_entries: unit.osr_entries,
                deopts: unit.state.deopts(),
                tier: unit.state.tier(),
                pinned: unit.state.is_pinned(),
                cancelled: unit.state.is_cancelled(),
            })
            .collect();
        TieredRunReport { units }
    }
}

/// The native semantic engine over a verified program.
///
/// `'m` bounds the module and entry table; `'h` bounds the host borrow. The
/// embedded [`Machine`] owns the shared heap/globals/host/limits and every
/// value-semantic method; the engine never calls [`Machine::run`]. All mutable
/// state is behind [`RefCell`]/[`Cell`] because [`NativeOps`] dispatches on
/// `&self` (see the module docs on re-entrancy).
pub struct NativeEngine<'m, 'h, H: Host> {
    /// The shared semantic core: heap, globals, host, limits, and the one live
    /// module registry used by interpreter and native execution alike.
    machine: RefCell<Machine<'h, H>>,
    /// The verified program whose module-local bytecode drives reference calls.
    program: &'m Program<Verified>,
    /// The compiled entry table, used by the linked backend and nested calls.
    entries: &'m dyn NativeEntryTable,
    backend: Backend,
    /// Metadata for each live activation; register files are driver-stack locals.
    activations: RefCell<Vec<Activation>>,
    /// Buffered process stdout.
    stdout: RefCell<Vec<u8>>,
    /// The process exit code (`0` for normal termination).
    exit_code: Cell<i32>,
    /// A throw's value+origin, set by `dispatch`, consumed by the driver.
    pending_throw: Cell<Option<PendingThrow>>,
    /// The innermost uncaught throw site preserved across a nested call unwind.
    pending_fault: Cell<Option<(crate::RuntimeFunction, usize)>>,
    /// A shallow fatal kind, set by `dispatch`; the driver attaches source.
    pending_fatal_kind: Cell<Option<RuntimeErrorKind>>,
    /// A fully-sourced error from a nested activation, propagated verbatim.
    pending_error: Cell<Option<RuntimeError>>,
    /// A nested entry-table linkage failure, propagated through `FatalTrap`.
    pending_abi_error: Cell<Option<AbiError>>,
    /// Cooperative cancellation signal shared with the embedded [`Machine`].
    cancel: bamts_cancel::CancellationToken,
    /// Live tiering table for [`run_linked_program_tiered`]. `None` on every
    /// existing constructor/build path so linked and reference behavior is
    /// unchanged unless the tiered entry is used.
    tiering: Option<RefCell<TieringTable>>,
}

impl<'m, 'h, H: Host> NativeEngine<'m, 'h, H> {
    fn build(
        program: &'m Program<Verified>,
        entries: &'m dyn NativeEntryTable,
        host: &'h mut H,
        limits: Limits,
        backend: Backend,
        cancel: bamts_cancel::CancellationToken,
    ) -> Self
    where
        'm: 'h,
    {
        Self::build_with_tiering(program, entries, host, limits, backend, cancel, None)
    }

    fn build_with_tiering(
        program: &'m Program<Verified>,
        entries: &'m dyn NativeEntryTable,
        host: &'h mut H,
        limits: Limits,
        backend: Backend,
        cancel: bamts_cancel::CancellationToken,
        tiering: Option<TieringTable>,
    ) -> Self
    where
        'm: 'h,
    {
        let mut machine = Machine::new_with_cancel(program, host, limits, cancel.clone());
        machine.frames.clear();
        machine.live_registers = 0;
        NativeEngine {
            machine: RefCell::new(machine),
            program,
            entries,
            backend,
            activations: RefCell::new(Vec::new()),
            stdout: RefCell::new(Vec::new()),
            exit_code: Cell::new(0),
            pending_throw: Cell::new(None),
            pending_fault: Cell::new(None),
            pending_fatal_kind: Cell::new(None),
            pending_error: Cell::new(None),
            pending_abi_error: Cell::new(None),
            cancel,
            tiering: tiering.map(RefCell::new),
        }
    }

    /// A native engine that drives control flow itself (the compiler-free
    /// reference backend). `entries` is used only for nested calls under the
    /// linked backend; the reference backend recurses internally.
    #[must_use]
    pub fn new(
        program: &'m Program<Verified>,
        entries: &'m dyn NativeEntryTable,
        host: &'h mut H,
        limits: Limits,
    ) -> Self
    where
        'm: 'h,
    {
        Self::build(
            program,
            entries,
            host,
            limits,
            Backend::Reference,
            bamts_cancel::CancellationToken::new(),
        )
    }

    /// Buffered process stdout produced during execution.
    #[must_use]
    pub fn stdout(&self) -> Vec<u8> {
        self.stdout.borrow().clone()
    }

    /// The process exit code.
    #[must_use]
    pub fn exit_code(&self) -> i32 {
        self.exit_code.get()
    }

    fn max_call_depth(&self) -> usize {
        self.machine.borrow().limits.max_call_depth
    }

    fn max_total_registers(&self) -> usize {
        self.machine.borrow().limits.max_total_registers
    }

    fn uncaught_throw_at(
        &self,
        module: ModuleId,
        function: usize,
        pc: usize,
        value: Value,
        origin: ThrowOrigin,
    ) -> RuntimeError {
        if let Some((site, fault_pc)) = self.pending_fault.take() {
            return self.error_at(
                site.module,
                RuntimeErrorKind::UncaughtThrow {
                    value,
                    origin,
                    constructor_name: None,
                    message: None,
                },
                site.function.get() as usize,
                fault_pc,
            );
        }
        self.error_at(
            module,
            RuntimeErrorKind::UncaughtThrow {
                value,
                origin,
                constructor_name: None,
                message: None,
            },
            function,
            pc,
        )
    }

    fn error_at(
        &self,
        module: ModuleId,
        kind: RuntimeErrorKind,
        function: usize,
        pc: usize,
    ) -> RuntimeError {
        self.machine
            .borrow()
            .error_at_in_module(kind, module, function, pc)
    }

    fn module(&self, module: ModuleId) -> &Module<Verified> {
        debug_assert!((module.get() as usize) < self.machine.borrow().dynamic_base);
        &self
            .program
            .module(module)
            .expect("verified native module id remains in bounds")
            .code
    }

    fn code_ref(&self, module: ModuleId) -> CodeRef<'m> {
        let dynamic = {
            let machine = self.machine.borrow();
            let index = module.get() as usize;
            (index >= machine.dynamic_base).then(|| {
                machine.dynamic[index - machine.dynamic_base]
                    .program
                    .clone()
            })
        };
        dynamic.map_or(CodeRef::Root(self.program), CodeRef::Dynamic)
    }

    fn is_dynamic_module(&self, module: ModuleId) -> bool {
        module.get() as usize >= self.machine.borrow().dynamic_base
    }

    /// Builds the root set for the current native activation. The registers are
    /// driver-stack locals, so they must be copied into the Machine before GC.
    fn native_root_snapshot(&self, registers: &[Value]) -> Vec<Value> {
        let activations = self.activations.borrow();
        let activation = activations
            .last()
            .expect("a native root snapshot requires an active activation");
        let mut roots = Vec::with_capacity(
            registers.len()
                + activation.args.len()
                + 2
                + usize::from(activation.arguments_object.is_some())
                + usize::from(activation.pending_resume.is_some())
                + usize::from(self.pending_throw.get().is_some()),
        );
        roots.extend_from_slice(registers);
        roots.push(activation.this_value);
        roots.push(activation.new_target);
        roots.extend_from_slice(&activation.args);
        roots.extend(activation.arguments_object);
        roots.extend(
            activation
                .pending_resume
                .map(|completion| completion.value()),
        );
        roots.extend(self.pending_throw.get().map(|pending| pending.value));
        roots
    }

    fn push_native_roots(&self, registers: &[Value]) {
        let depth = self.activations.borrow().len() - 1;
        let roots = self.native_root_snapshot(registers);
        self.machine.borrow_mut().push_native_roots(depth, &roots);
    }

    fn refresh_native_roots(&self, frame: &NativeFrame<'_>) {
        let depth = self.activations.borrow().len() - 1;
        let roots = self.native_root_snapshot(frame.registers());
        self.machine
            .borrow_mut()
            .refresh_native_roots(depth, &roots);
    }

    fn pop_native_roots(&self) {
        let depth = self.activations.borrow().len() - 1;
        self.machine.borrow_mut().pop_native_roots(depth);
    }

    /// The only re-entrant native-helper boundary. Refresh first because the
    /// helper may collect before it decodes operands or enters another engine.
    fn prepare_native_helper(&self, frame: &NativeFrame<'_>) {
        self.refresh_native_roots(frame);
        let mut machine = self.machine.borrow_mut();
        if machine.gc_pending() {
            machine.collect_if_pending();
        }
    }

    // -- Reference backend: control-flow driver ------------------------------

    /// Executes the program entry with the reference driver, then drives the
    /// shared automatic event loop to quiescence. Never invokes [`Machine::run`];
    /// it reuses the machine's own loop driver directly.
    pub fn run(self) -> Result<Execution, RuntimeError> {
        let result = (|| {
            self.machine.borrow_mut().instantiate_modules()?;
            let entry = self.program.entry();
            let execution = if self.machine.borrow().module_graph_suspends(entry) {
                self.machine
                    .borrow_mut()
                    .evaluate_instantiated_module(entry)?
            } else {
                self.evaluate_reference_module(entry)?.ok_or_else(|| {
                    let function = self.module(entry).entry().get() as usize;
                    self.error_at(
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
            self.machine.borrow_mut().run_to_quiescence()?;
            Ok(execution)
        })();
        self.machine.borrow_mut().clear_kept_alive_for_job();
        match result {
            Ok(execution) => Ok(execution),
            Err(mut error) => {
                self.machine.borrow_mut().enrich_uncaught_throw(&mut error);
                Err(error)
            }
        }
    }

    fn evaluate_reference_module(
        &self,
        module: ModuleId,
    ) -> Result<Option<Execution>, RuntimeError> {
        let dependencies = match self.machine.borrow_mut().begin_module_evaluation(module)? {
            crate::ModuleEvaluation::Cycle => return Ok(None),
            crate::ModuleEvaluation::Evaluated(result) => return result.map(|()| None),
            crate::ModuleEvaluation::Ready(dependencies) => dependencies,
        };
        for dependency in dependencies {
            if let Err(error) = self.evaluate_reference_module(dependency) {
                return self
                    .machine
                    .borrow_mut()
                    .finish_module_evaluation(module, Err(error))
                    .map(Some);
            }
        }

        let code = self.module(module);
        let function = code.entry().get() as usize;
        let register_count = code.functions()[function].register_count() as usize;
        let result = if self.max_call_depth() < 1 {
            Err(self.error_at(
                module,
                RuntimeErrorKind::CallDepthExceeded {
                    limit: self.max_call_depth(),
                },
                function,
                0,
            ))
        } else if register_count > self.max_total_registers() {
            Err(self.error_at(
                module,
                RuntimeErrorKind::RegisterLimitExceeded {
                    limit: self.max_total_registers(),
                },
                function,
                0,
            ))
        } else {
            self.execute(
                module,
                function,
                Value::UNDEFINED,
                Value::UNDEFINED,
                Vec::new(),
                &[],
            )
            .and_then(|(completion, registers)| match completion {
                FrameCompletion::Normal(value) => Ok(Execution {
                    outcome: ExecutionOutcome {
                        stdout: self.stdout.borrow().clone(),
                        exit_code: self.exit_code.get(),
                    },
                    value,
                    link: value,
                    entry_registers: registers,
                }),
                FrameCompletion::Unwind(value, origin, pc) => {
                    Err(self.uncaught_throw_at(module, function, pc, value, origin))
                }
                FrameCompletion::Suspend(value, _) => Err(self.error_at(
                    module,
                    RuntimeErrorKind::InvalidValue { value },
                    function,
                    0,
                )),
            })
        };
        self.machine
            .borrow_mut()
            .finish_module_evaluation(module, result)
            .map(Some)
    }

    /// Seeds a fresh register file: leading captures, then parameters, the rest
    /// uninitialized — identical to the interpreter's frame prologue.
    fn seed_registers(
        &self,
        code: &Module<Verified>,
        function: usize,
        captures: &[Value],
        args: &[Value],
    ) -> Vec<Value> {
        let metadata = &code.functions()[function];
        let register_count = metadata.register_count() as usize;
        let capture_count = metadata.capture_count() as usize;
        let parameter_count = metadata.parameter_count() as usize;
        let mut registers = vec![Value::UNINITIALIZED; register_count];
        for index in 0..capture_count {
            if let Some(slot) = registers.get_mut(index) {
                *slot = captures.get(index).copied().unwrap_or(Value::UNDEFINED);
            }
        }
        for index in 0..parameter_count {
            if let Some(slot) = registers.get_mut(capture_count + index) {
                *slot = args.get(index).copied().unwrap_or(Value::UNDEFINED);
            }
        }
        registers
    }

    /// Drives one activation to termination. Pushes the activation metadata,
    /// runs the instruction loop over a driver-local register file, and returns
    /// both the completion and the final register file (the caller ignores the
    /// registers except for the entry frame).
    fn execute(
        &self,
        module: ModuleId,
        function: usize,
        this_value: Value,
        new_target: Value,
        args: Vec<Value>,
        captures: &[Value],
    ) -> Result<(FrameCompletion, Vec<Value>), RuntimeError> {
        let handle = self.code_ref(module);
        let code = handle.code(module);
        let register_count = code.functions()[function].register_count() as usize;
        let mut registers = self.seed_registers(code, function, captures, &args);
        let reserved = self
            .machine
            .borrow_mut()
            .reserve_native_activation(register_count);
        reserved.map_err(|kind| self.error_at(module, kind, function, 0))?;
        self.activations.borrow_mut().push(Activation {
            this_value,
            new_target,
            args,
            arguments_object: None,
            pending_resume: None,
            target: crate::RuntimeFunction {
                module,
                function: FunctionId::new(function as u32),
            },
        });
        self.push_native_roots(&registers);
        let completion =
            self.run_frame(module, function, code, &mut registers, FrameDrive::Ordinary);
        self.pop_native_roots();
        self.activations.borrow_mut().pop();
        self.machine
            .borrow_mut()
            .release_native_activation(register_count);
        completion.map(|completion| (completion, registers))
    }

    /// The instruction loop for one activation. `registers` is the caller-owned
    /// register file; a [`NativeFrame`] borrows it disjointly from `self`.
    fn run_frame(
        &self,
        module: ModuleId,
        function: usize,
        code: &Module<Verified>,
        registers: &mut Vec<Value>,
        drive: FrameDrive,
    ) -> Result<FrameCompletion, RuntimeError> {
        let length = u16::try_from(registers.len()).map_err(|_| {
            let limit = self.max_total_registers();
            self.error_at(
                module,
                RuntimeErrorKind::RegisterLimitExceeded { limit },
                function,
                0,
            )
        })?;
        let handles = registers.as_mut_ptr();
        let mut shadow = ShadowFrame::new(std::ptr::null_mut(), 0, module.get(), handles, length);
        let mut frame =
            NativeFrame::new(&mut shadow, registers.as_mut_slice()).ok_or_else(|| {
                self.error_at(
                    module,
                    RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    },
                    function,
                    0,
                )
            })?;

        let target = crate::RuntimeFunction {
            module,
            function: FunctionId::new(function as u32),
        };
        let mut pc = match drive {
            FrameDrive::Ordinary | FrameDrive::GeneratorStart => 0,
            FrameDrive::Resume { pc: resume_pc } => {
                let length = code.functions()[function].code().len();
                if resume_pc >= length {
                    return Err(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        },
                        function,
                        resume_pc,
                    ));
                }
                resume_pc
            }
            FrameDrive::GeneratorResume { token, completion } => {
                let suspend_pc = token.checked_sub(1).map(|pc| pc as usize).ok_or_else(|| {
                    self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        },
                        function,
                        0,
                    )
                })?;
                let Instruction::Suspend {
                    dst, resume, mode, ..
                } = code.functions()[function].code()[suspend_pc]
                else {
                    return Err(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        },
                        function,
                        suspend_pc,
                    ));
                };
                frame.set_register(dst.get(), completion.value());
                frame.set_register(mode.get(), Value::int32(completion.mode()));
                resume.get() as usize
            }
        };
        loop {
            let instruction = code.functions()[function].code()[pc];
            if is_inline_instruction(instruction) {
                let consumed = self.machine.borrow_mut().consume_fuel(1);
                if let Err(kind) = consumed {
                    return Err(self.error_at(module, kind, function, pc));
                }
            }

            // Control-flow opcodes are the driver's own responsibility (the CLIF
            // the AOT/JIT backend generates); every value/heap/host opcode is
            // routed through `dispatch` into the shared semantics.
            match instruction {
                Instruction::Move { dst, src } => {
                    let value = frame.register(src.get());
                    frame.set_register(dst.get(), value);
                    pc += 1;
                }
                Instruction::Jump { target } => {
                    let next = target.get() as usize;
                    let function_id = FunctionId::new(function as u32);
                    if let Some(entry) = self.poll_osr_entry(module, function_id, next, pc) {
                        let osr_pc = entry.pc.get();
                        // End the NativeFrame borrow of `shadow` before transfer_osr.
                        {
                            let _frame = frame;
                        }
                        match self.transfer_osr(module, function, &mut shadow, osr_pc)? {
                            OsrFlow::Done(completion) => return Ok(completion),
                            OsrFlow::ContinueAt(resume_pc) => {
                                frame = NativeFrame::new(&mut shadow, registers.as_mut_slice())
                                    .ok_or_else(|| {
                                        self.error_at(
                                            module,
                                            RuntimeErrorKind::InvalidValue {
                                                value: Value::UNDEFINED,
                                            },
                                            function,
                                            resume_pc,
                                        )
                                    })?;
                                pc = resume_pc;
                            }
                        }
                    } else {
                        pc = next;
                    }
                }
                Instruction::JumpIfTrue { condition, target } => {
                    let value = frame.register(condition.get());
                    if self.truthy(&mut frame, value) {
                        let next = target.get() as usize;
                        let function_id = FunctionId::new(function as u32);
                        if let Some(entry) = self.poll_osr_entry(module, function_id, next, pc) {
                            let osr_pc = entry.pc.get();
                            // End the NativeFrame borrow of `shadow` before transfer_osr.
                            {
                                let _frame = frame;
                            }
                            match self.transfer_osr(module, function, &mut shadow, osr_pc)? {
                                OsrFlow::Done(completion) => return Ok(completion),
                                OsrFlow::ContinueAt(resume_pc) => {
                                    frame = NativeFrame::new(&mut shadow, registers.as_mut_slice())
                                        .ok_or_else(|| {
                                            self.error_at(
                                                module,
                                                RuntimeErrorKind::InvalidValue {
                                                    value: Value::UNDEFINED,
                                                },
                                                function,
                                                resume_pc,
                                            )
                                        })?;
                                    pc = resume_pc;
                                }
                            }
                        } else {
                            pc = next;
                        }
                    } else {
                        pc += 1;
                    }
                }
                Instruction::JumpIfFalse { condition, target } => {
                    let value = frame.register(condition.get());
                    if self.truthy(&mut frame, value) {
                        pc += 1;
                    } else {
                        let next = target.get() as usize;
                        let function_id = FunctionId::new(function as u32);
                        if let Some(entry) = self.poll_osr_entry(module, function_id, next, pc) {
                            let osr_pc = entry.pc.get();
                            // End the NativeFrame borrow of `shadow` before transfer_osr.
                            {
                                let _frame = frame;
                            }
                            match self.transfer_osr(module, function, &mut shadow, osr_pc)? {
                                OsrFlow::Done(completion) => return Ok(completion),
                                OsrFlow::ContinueAt(resume_pc) => {
                                    frame = NativeFrame::new(&mut shadow, registers.as_mut_slice())
                                        .ok_or_else(|| {
                                            self.error_at(
                                                module,
                                                RuntimeErrorKind::InvalidValue {
                                                    value: Value::UNDEFINED,
                                                },
                                                function,
                                                resume_pc,
                                            )
                                        })?;
                                    pc = resume_pc;
                                }
                            }
                        } else {
                            pc = next;
                        }
                    }
                }
                Instruction::Return { value } => {
                    return Ok(FrameCompletion::Normal(frame.register(value.get())));
                }
                Instruction::Halt => return Ok(FrameCompletion::Normal(Value::UNDEFINED)),
                Instruction::Throw { value } => {
                    let thrown = frame.register(value.get());
                    match self.raise(
                        &mut frame,
                        code,
                        function,
                        pc,
                        thrown,
                        ThrowOrigin::Bytecode,
                    )? {
                        Flow::Next => pc += 1,
                        Flow::Goto(target) => pc = target,
                        Flow::Unwind(value, origin) => {
                            return Ok(FrameCompletion::Unwind(value, origin, pc));
                        }
                    }
                }
                Instruction::Suspend { src, .. }
                    if matches!(
                        drive,
                        FrameDrive::GeneratorStart | FrameDrive::GeneratorResume { .. }
                    ) =>
                {
                    let token = u32::try_from(pc + 1).map_err(|_| {
                        self.error_at(
                            module,
                            RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            },
                            function,
                            pc,
                        )
                    })?;
                    return Ok(FrameCompletion::Suspend(frame.register(src.get()), token));
                }
                instruction @ (Instruction::Suspend { .. } | Instruction::Await { .. }) => {
                    let operation = match instruction {
                        Instruction::Suspend { .. } => "suspend outside an engine-owned event loop",
                        Instruction::Await { .. } => "await outside an engine-owned event loop",
                        _ => unreachable!(),
                    };
                    match self.raise(
                        &mut frame,
                        code,
                        function,
                        pc,
                        Value::UNDEFINED,
                        ThrowOrigin::TypeError { operation },
                    )? {
                        Flow::Next => pc += 1,
                        Flow::Goto(target) => pc = target,
                        Flow::Unwind(value, origin) => {
                            return Ok(FrameCompletion::Unwind(value, origin, pc));
                        }
                    }
                }
                other => {
                    frame.set_resume(pc as u32);
                    let (call, dst) = self.lower(other, &frame);
                    let result = self.dispatch(&mut frame, call);
                    match self.apply(&mut frame, target, code, pc, dst, result)? {
                        Flow::Next => pc += 1,
                        Flow::Goto(target) => pc = target,
                        Flow::Unwind(value, origin) => {
                            return Ok(FrameCompletion::Unwind(value, origin, pc));
                        }
                    }
                }
            }
        }
    }

    /// Lowers a value/heap/host opcode into the [`HelperCall`] the code
    /// generator would emit plus the destination register (if any). Reading
    /// operand registers here mirrors codegen's register loads.
    fn lower(
        &self,
        instruction: Instruction,
        frame: &NativeFrame<'_>,
    ) -> (HelperCall, Option<u32>) {
        let register = |r: bamts_bytecode::Register| frame.register(r.get());
        match instruction {
            Instruction::LoadConst { dst, constant } => (
                HelperCall::LoadConstant {
                    const_id: constant.get(),
                },
                Some(dst.get()),
            ),
            Instruction::Unary { dst, op, operand } => (
                HelperCall::Unary {
                    op: unary_to_selector(op),
                    operand: register(operand),
                },
                Some(dst.get()),
            ),
            Instruction::Binary {
                dst,
                op,
                left,
                right,
            } => (
                HelperCall::Binary {
                    op: binary_to_selector(op),
                    left: register(left),
                    right: register(right),
                },
                Some(dst.get()),
            ),
            Instruction::CreateObject { dst } => (HelperCall::CreateObject, Some(dst.get())),
            Instruction::ToObject { dst, src } => (
                HelperCall::ToObject {
                    value: register(src),
                },
                Some(dst.get()),
            ),
            Instruction::CreateArray { dst } => (HelperCall::CreateArray, Some(dst.get())),
            Instruction::CreateCell { dst } => (HelperCall::CreateCell, Some(dst.get())),
            Instruction::CreateClosure {
                dst,
                function,
                captures,
            } => (
                HelperCall::CreateClosure {
                    function_id: function.get(),
                    captures: register(captures),
                },
                Some(dst.get()),
            ),
            Instruction::GetProperty { dst, object, key } => (
                HelperCall::GetProperty {
                    object: register(object),
                    key: register(key),
                },
                Some(dst.get()),
            ),
            Instruction::SetProperty { object, key, value } => (
                HelperCall::SetProperty {
                    object: register(object),
                    key: register(key),
                    value: register(value),
                },
                None,
            ),
            Instruction::DeleteProperty { dst, object, key } => (
                HelperCall::DeleteProperty {
                    object: register(object),
                    key: register(key),
                },
                Some(dst.get()),
            ),
            Instruction::DefineAccessor {
                object,
                key,
                accessor,
                kind,
            } => (
                HelperCall::DefineAccessor {
                    object: register(object),
                    key: register(key),
                    accessor: register(accessor),
                    kind: accessor_to_selector(kind),
                },
                None,
            ),
            Instruction::DefineDataProperty { object, key, value } => (
                HelperCall::DefineDataProperty {
                    object: register(object),
                    key: register(key),
                    value: register(value),
                },
                None,
            ),
            Instruction::LoadOwnDescriptorSlot {
                dst,
                object,
                key,
                slot,
            } => (
                HelperCall::LoadOwnDescriptorSlot {
                    object: register(object),
                    key: register(key),
                    slot: descriptor_slot_to_selector(slot),
                },
                Some(dst.get()),
            ),
            Instruction::DefineOwnDescriptorSlot {
                object,
                key,
                src,
                slot,
            } => (
                HelperCall::DefineOwnDescriptorSlot {
                    object: register(object),
                    key: register(key),
                    src: register(src),
                    slot: descriptor_slot_to_selector(slot),
                },
                None,
            ),
            Instruction::WithHasBinding { dst, object, key } => (
                HelperCall::WithHasBinding {
                    object: register(object),
                    key: register(key),
                },
                Some(dst.get()),
            ),
            Instruction::GetSuper {
                dst,
                home,
                receiver,
                key,
            } => (
                HelperCall::GetSuper {
                    home: register(home),
                    receiver: register(receiver),
                    key: register(key),
                },
                Some(dst.get()),
            ),
            Instruction::SetSuper {
                home,
                receiver,
                key,
                value,
            } => (
                HelperCall::SetSuper {
                    home: register(home),
                    receiver: register(receiver),
                    key: register(key),
                    value: register(value),
                },
                None,
            ),
            Instruction::ImportAttributes {
                dst,
                specifier,
                attributes,
            } => (
                HelperCall::ImportAttributes {
                    specifier: specifier.get(),
                    attributes: register(attributes),
                },
                Some(dst.get()),
            ),
            Instruction::ImportDynamicAttributes {
                dst,
                specifier,
                attributes,
            } => (
                HelperCall::ImportDynamicAttributes {
                    specifier: register(specifier),
                    attributes: register(attributes),
                },
                Some(dst.get()),
            ),
            Instruction::CopyDataProperties {
                target,
                source,
                excluded,
            } => (
                HelperCall::CopyDataProperties {
                    target: register(target),
                    source: register(source),
                    excluded: register(excluded),
                },
                None,
            ),
            Instruction::GetTemplateObject { dst, cooked, raw } => (
                HelperCall::GetTemplateObject {
                    cooked: register(cooked),
                    raw: register(raw),
                },
                Some(dst.get()),
            ),
            Instruction::Call {
                dst,
                callee,
                this_value,
                arguments,
            } => (
                HelperCall::Call {
                    callee: register(callee),
                    this_value: register(this_value),
                    arguments: register(arguments),
                },
                Some(dst.get()),
            ),
            Instruction::Construct {
                dst,
                callee,
                arguments,
            } => (
                HelperCall::Construct {
                    callee: register(callee),
                    arguments: register(arguments),
                },
                Some(dst.get()),
            ),
            Instruction::ConstructWithNewTarget {
                dst,
                callee,
                new_target,
                arguments,
            } => (
                HelperCall::ConstructWithNewTarget {
                    callee: register(callee),
                    new_target: register(new_target),
                    arguments: register(arguments),
                },
                Some(dst.get()),
            ),
            Instruction::LoadGlobal { dst, name } => {
                (HelperCall::LoadGlobal { name: name.get() }, Some(dst.get()))
            }
            Instruction::StoreGlobal { name, value } => (
                HelperCall::StoreGlobal {
                    name: name.get(),
                    value: register(value),
                },
                None,
            ),
            Instruction::TypeOfGlobal { dst, name } => (
                HelperCall::TypeOfGlobal { name: name.get() },
                Some(dst.get()),
            ),
            Instruction::LoadThis { dst } => (HelperCall::LoadThis, Some(dst.get())),
            Instruction::LoadArguments { dst } => (HelperCall::LoadArguments, Some(dst.get())),
            Instruction::LoadNewTarget { dst } => (HelperCall::LoadNewTarget, Some(dst.get())),
            Instruction::ArrayPush { array, value } => (
                HelperCall::ArrayPush {
                    array: register(array),
                    value: register(value),
                },
                None,
            ),
            Instruction::ArrayExtend { array, iterable } => (
                HelperCall::ArrayExtend {
                    array: register(array),
                    iterable: register(iterable),
                },
                None,
            ),
            Instruction::ObjectSpread { target, source } => (
                HelperCall::ObjectSpread {
                    target: register(target),
                    source: register(source),
                },
                None,
            ),
            Instruction::SetPrototype { object, prototype } => (
                HelperCall::SetPrototype {
                    object: register(object),
                    prototype: register(prototype),
                },
                None,
            ),
            Instruction::CreatePrivateName { dst, description } => (
                HelperCall::CreatePrivateName {
                    description: description.get(),
                },
                Some(dst.get()),
            ),
            Instruction::CreateRegExp {
                dst,
                pattern,
                flags,
            } => (
                HelperCall::CreateRegExp {
                    pattern: pattern.get(),
                    flags: flags.get(),
                },
                Some(dst.get()),
            ),
            Instruction::GetIterator { dst, src, kind } => (
                HelperCall::GetIterator {
                    src: register(src),
                    kind: iterator_kind_to_selector(kind),
                },
                Some(dst.get()),
            ),
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            } => (
                HelperCall::IteratorNext {
                    iterator: register(iterator),
                    done_reg: done.get(),
                    value_reg: value.get(),
                },
                None,
            ),
            Instruction::IteratorStep { dst, iterator } => (
                HelperCall::IteratorStep {
                    iterator: register(iterator),
                },
                Some(dst.get()),
            ),
            Instruction::IteratorResult {
                done,
                value,
                result,
            } => (
                HelperCall::IteratorResult {
                    result: register(result),
                    done_reg: done.get(),
                    value_reg: value.get(),
                },
                None,
            ),
            Instruction::IteratorClose {
                result,
                called,
                iterator,
                mode,
            } => (
                HelperCall::IteratorClose {
                    iterator: register(iterator),
                    mode: iterator_close_mode_to_selector(mode),
                    called_reg: called.get(),
                },
                Some(result.get()),
            ),
            Instruction::RequireCloseResult { result, called } => (
                HelperCall::RequireCloseResult {
                    result: register(result),
                    called: register(called),
                },
                None,
            ),
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint,
            } => (
                HelperCall::DisposeCapture {
                    src: register(src),
                    hint: dispose_hint_to_selector(hint),
                    kind_reg: kind.get(),
                },
                Some(method.get()),
            ),
            Instruction::SuppressError {
                dst,
                error,
                suppressed,
            } => (
                HelperCall::SuppressError {
                    error: register(error),
                    suppressed: register(suppressed),
                },
                Some(dst.get()),
            ),
            Instruction::LoadImportMeta { dst } => (HelperCall::LoadImportMeta, Some(dst.get())),
            Instruction::Import { dst, specifier } => (
                HelperCall::Import {
                    specifier: specifier.get(),
                },
                Some(dst.get()),
            ),
            Instruction::ImportDynamic { dst, specifier } => (
                HelperCall::ImportDynamic {
                    specifier: register(specifier),
                },
                Some(dst.get()),
            ),
            Instruction::Export { name, src } => (
                HelperCall::Export {
                    name: name.get(),
                    src: register(src),
                },
                None,
            ),
            // Control-flow opcodes are handled by the driver and never lowered.
            Instruction::Move { .. }
            | Instruction::Jump { .. }
            | Instruction::JumpIfTrue { .. }
            | Instruction::JumpIfFalse { .. }
            | Instruction::Return { .. }
            | Instruction::Throw { .. }
            | Instruction::Suspend { .. }
            | Instruction::Await { .. }
            | Instruction::Halt => {
                unreachable!("control-flow opcode is not lowered to a helper call")
            }
        }
    }

    /// Interprets a [`HelperResult`] against the frame: stores a normal result
    /// into `dst`, searches handlers for a throw, or turns a trap into an error.
    fn take_matching_throw(&self, value: Value) -> (Value, ThrowOrigin) {
        match self.pending_throw.take() {
            Some(pending) if pending.value == value => (pending.value, pending.origin),
            Some(_) | None => (value, ThrowOrigin::Bytecode),
        }
    }

    fn apply(
        &self,
        frame: &mut NativeFrame<'_>,
        target: crate::RuntimeFunction,
        code: &Module<Verified>,
        pc: usize,
        dst: Option<u32>,
        result: HelperResult,
    ) -> Result<Flow, RuntimeError> {
        let function = target.function.get() as usize;
        match result.tag {
            CompletionTag::Normal => {
                self.pending_throw.take();
                self.pending_fault.take();
                if let Some(register) = dst {
                    frame.set_register(register, result.value);
                }
                Ok(Flow::Next)
            }
            CompletionTag::Throw => {
                let (value, origin) = self.take_matching_throw(result.value);
                self.raise(frame, code, function, pc, value, origin)
            }
            CompletionTag::Suspend => {
                // The reference driver drives `Suspend` inline; a helper never
                // returns it. Treat as a malformed completion.
                Err(self.error_at(
                    target.module,
                    RuntimeErrorKind::InvalidValue {
                        value: result.value,
                    },
                    function,
                    pc,
                ))
            }
            CompletionTag::FatalTrap => {
                if let Some(error) = self.pending_error.take() {
                    return Err(error);
                }
                let kind = self.pending_fatal_kind.take().unwrap_or({
                    RuntimeErrorKind::InvalidValue {
                        value: result.value,
                    }
                });
                Err(self.error_at(target.module, kind, function, pc))
            }
        }
    }

    /// Searches the current function's handlers covering `pc`. Binds the thrown
    /// value into the handler's catch register and jumps, or signals an unwind.
    ///
    /// A caught, still-lazy engine throw (`value == UNDEFINED`, non-`Bytecode`
    /// origin) is materialized into the realm-intrinsic error object here, so
    /// the reference backend observes the same caught value as the linked one.
    fn raise(
        &self,
        frame: &mut NativeFrame<'_>,
        code: &Module<Verified>,
        function: usize,
        pc: usize,
        value: Value,
        origin: ThrowOrigin,
    ) -> Result<Flow, RuntimeError> {
        match crate::innermost_handler(&code.functions()[function], pc) {
            Some(handler) => {
                self.pending_fault.take();
                let target = crate::RuntimeFunction {
                    module: ModuleId::new(frame.module_id()),
                    function: FunctionId::new(function as u32),
                };
                let catch_value = self.materialize_catch_value(frame, target, pc, value, origin)?;
                frame.set_register(handler.catch_register.get(), catch_value);
                Ok(Flow::Goto(handler.handler.get() as usize))
            }
            None => Ok(Flow::Unwind(value, origin)),
        }
    }

    /// The shared catch-value decision: bytecode throws and supplied
    /// (non-`UNDEFINED`) values keep their identity; a still-lazy engine origin
    /// allocates the realm-intrinsic error object. The machine borrow is scoped
    /// so `error_at` never reborrows the `RefCell` while the mutable guard is
    /// live. `pc` is the faulting instruction: the reference driver passes its
    /// live pc; the linked postprocessor passes the frame-recorded pc.
    fn materialize_catch_value(
        &self,
        frame: &NativeFrame<'_>,
        target: crate::RuntimeFunction,
        pc: usize,
        value: Value,
        origin: ThrowOrigin,
    ) -> Result<Value, RuntimeError> {
        if !crate::catch_value_needs_materialization(value, origin) {
            return Ok(value);
        }
        self.refresh_native_roots(frame);
        let materialized = {
            let mut machine = self.machine.borrow_mut();
            machine.materialize_engine_origin(origin)
        };
        materialized
            .map_err(|kind| self.error_at(target.module, kind, target.function.get() as usize, pc))
    }

    /// Handler-aware postprocessor for linked helper completions. Generated
    /// code routes an abnormal completion into a covering handler by copying
    /// the raw completion value into the catch register, so a caught, still-
    /// lazy engine throw must be materialized here, before the generated code
    /// sees it. A throw with no covering handler at the frame-recorded target
    /// and pc is returned untouched — pending metadata and all — so the
    /// uncaught path stays lazy.
    ///
    /// The pending throw is consumed before materialization, so a failed
    /// allocation cannot later be misread as a throw; the exact sourced error
    /// is stored in `pending_error` and surfaced as `FatalTrap`, bypassing
    /// JavaScript handlers. `pending_fatal_kind` is never used for this case.
    fn finish_helper_result(&self, frame: &NativeFrame<'_>, result: HelperResult) -> HelperResult {
        if self.backend != Backend::Linked || result.tag != CompletionTag::Throw {
            return result;
        }
        let (target, pc) = {
            let activations = self.activations.borrow();
            match activations.last() {
                Some(activation) => (activation.target, frame.pc() as usize),
                None => return result,
            }
        };
        let handle = self.code_ref(target.module);
        let code = handle.code(target.module);
        let function = &code.functions()[target.function.get() as usize];
        if crate::innermost_handler(function, pc).is_none() {
            return result;
        }
        self.pending_fault.take();
        let (value, origin) = self.take_matching_throw(result.value);
        match self.materialize_catch_value(frame, target, pc, value, origin) {
            Ok(catch_value) => HelperResult::throw(catch_value),
            Err(error) => {
                self.pending_error.set(Some(error));
                HelperResult {
                    tag: CompletionTag::FatalTrap,
                    value: Value::UNDEFINED,
                }
            }
        }
    }

    // -- Callee invocation ---------------------------------------------------

    /// Invokes a callee value: a runtime closure re-enters native execution; a
    /// host function/foreign value routes to the host. Shared with the
    /// interpreter's classification via [`Machine::callee_kind`].
    fn invoke_callee(
        &self,
        callee: Value,
        this: Value,
        args: &[Value],
        new_target: Value,
    ) -> InvokeOutcome {
        let mark = self.machine.borrow_mut().hold_temporaries(&[]);
        let outcome = self.invoke_callee_forwarding(callee, this, args, new_target);
        self.machine.borrow_mut().release_temporaries(mark);
        outcome
    }

    /// [`Self::invoke_callee`], which releases what this holds for a forward.
    fn invoke_callee_forwarding(
        &self,
        callee: Value,
        this: Value,
        args: &[Value],
        new_target: Value,
    ) -> InvokeOutcome {
        let mut callee = callee;
        let mut this = this;
        let mut args = Cow::Borrowed(args);
        let mut new_target = new_target;
        loop {
            let kind = self.machine.borrow().callee_kind(callee);
            match kind {
                Ok(CalleeKind::Runtime {
                    target,
                    captures,
                    context,
                }) => {
                    return self.invoke_runtime(
                        target,
                        &captures,
                        context,
                        this,
                        new_target,
                        args.as_ref(),
                    );
                }
                Ok(CalleeKind::Proxy) => {
                    let outcome = crate::builtins::proxy::call(
                        &mut self.machine.borrow_mut(),
                        callee,
                        this,
                        args.as_ref(),
                    );
                    return self.eval_outcome(outcome);
                }
                Ok(CalleeKind::ProxyRevoker) => {
                    let outcome = crate::builtins::proxy::call_revoker(
                        &mut self.machine.borrow_mut(),
                        callee,
                    );
                    return self.eval_outcome(outcome);
                }
                Ok(CalleeKind::Builtin { id }) => {
                    let result = {
                        self.machine
                            .borrow_mut()
                            .call_builtin(id, this, args.as_ref(), false)
                    };
                    match result {
                        Ok(BuiltinOutcome::Value(value)) => {
                            return InvokeOutcome::Value(value);
                        }
                        Ok(BuiltinOutcome::Call {
                            callee: next,
                            this_value: next_this,
                            arguments: next_arguments,
                        }) => {
                            self.machine.borrow_mut().hold_forwarded_call(
                                next,
                                next_this,
                                &next_arguments,
                            );
                            callee = next;
                            this = next_this;
                            args = Cow::Owned(next_arguments);
                            new_target = Value::UNDEFINED;
                        }
                        Ok(BuiltinOutcome::GeneratorResume {
                            generator,
                            completion,
                        }) => {
                            return self.resume_generator(generator, completion);
                        }
                        Ok(BuiltinOutcome::AsyncGeneratorResume {
                            generator,
                            completion,
                        }) => {
                            let outcome = self
                                .machine
                                .borrow_mut()
                                .enqueue_async_generator_request(generator, completion);
                            return match outcome {
                                Ok(promise) => InvokeOutcome::Value(promise),
                                Err(failure) => self.failure_outcome(failure),
                            };
                        }
                        Err(EvalFailure::Throw(origin)) => {
                            return InvokeOutcome::Threw(Value::UNDEFINED, origin);
                        }
                        Err(EvalFailure::ThrowValue(value)) => {
                            return InvokeOutcome::Threw(value, ThrowOrigin::Bytecode);
                        }
                        Err(EvalFailure::ThrowValueOrigin { value, origin }) => {
                            return InvokeOutcome::Threw(value, origin);
                        }
                        Err(EvalFailure::Runtime(kind)) => {
                            self.pending_fatal_kind.set(Some(kind));
                            return InvokeOutcome::Fatal;
                        }
                    }
                }
                Ok(CalleeKind::Bound) => {
                    let bound = self.machine.borrow().flatten_bound(
                        callee,
                        this,
                        args.as_ref(),
                        Value::UNDEFINED,
                    );
                    match bound {
                        Ok(bound) => {
                            callee = bound.target;
                            if new_target == Value::UNDEFINED {
                                this = bound.this_value;
                            }
                            args = Cow::Owned(bound.arguments);
                        }
                        Err(kind) => {
                            self.pending_fatal_kind.set(Some(kind));
                            return InvokeOutcome::Fatal;
                        }
                    }
                }
                Ok(CalleeKind::NotCallable) => {
                    return InvokeOutcome::Threw(
                        Value::UNDEFINED,
                        ThrowOrigin::TypeError { operation: "call" },
                    );
                }
                Err(kind) => {
                    self.pending_fatal_kind.set(Some(kind));
                    return InvokeOutcome::Fatal;
                }
            }
        }
    }

    /// Re-enters a runtime function with the active recursion and register
    /// ceilings, dispatching to the reference driver or the linked entry table.
    fn invoke_runtime(
        &self,
        target: crate::RuntimeFunction,
        captures: &[Value],
        context: Option<Value>,
        this: Value,
        new_target: Value,
        args: &[Value],
    ) -> InvokeOutcome {
        let index = target.function.get() as usize;
        let handle = self.code_ref(target.module);
        let flags = handle.code(target.module).functions()[index].flags();
        if flags.is_async && flags.is_generator {
            // An async generator's prologue runs on the shared Machine, like
            // the rest of its body.
            let start = GeneratorStart {
                target,
                captures: captures.to_vec(),
                context,
                this_value: this,
                new_target,
                args: args.to_vec(),
            };
            let started = self.machine.borrow_mut().start_generator(start, flags);
            return match started {
                Ok(generator) => InvokeOutcome::Value(generator),
                Err(failure) => self.failure_outcome(failure),
            };
        }
        if flags.is_generator {
            let created = self.machine.borrow_mut().create_generator(GeneratorStart {
                target,
                captures: captures.to_vec(),
                context,
                this_value: this,
                new_target,
                args: args.to_vec(),
            });
            let generator = match created {
                Ok(generator) => generator,
                Err(kind) => {
                    self.pending_fatal_kind.set(Some(kind));
                    return InvokeOutcome::Fatal;
                }
            };
            if flags.binds_at_call {
                let completion = GeneratorCompletion::Normal(Value::UNDEFINED);
                match self.resume_generator(generator, completion) {
                    InvokeOutcome::Value(_) => {}
                    other => return other,
                }
            }
            return InvokeOutcome::Value(generator);
        }
        if flags.is_async && !flags.is_generator {
            // Async calls route through the shared reference Machine state
            // machine, which drives the body on the interpreter to its first
            // await or completion and returns the implicit Promise. No
            // bytecode, codegen, or ABI change is involved.
            let outcome = crate::vm::generator_async::start_async_function(
                &mut self.machine.borrow_mut(),
                target,
                captures,
                context,
                this,
                new_target,
                args,
            );
            return match outcome {
                Ok(promise) => InvokeOutcome::Value(promise),
                Err(failure) => self.failure_outcome(failure),
            };
        }
        let previous = {
            let mut machine = self.machine.borrow_mut();
            std::mem::replace(&mut machine.context_global, context)
        };
        let outcome = if self.backend == Backend::Reference || self.is_dynamic_module(target.module)
        {
            match self.execute(
                target.module,
                index,
                this,
                new_target,
                args.to_vec(),
                captures,
            ) {
                Ok((FrameCompletion::Normal(value), _)) => InvokeOutcome::Value(value),
                Ok((FrameCompletion::Unwind(value, origin, fault_pc), _)) => {
                    self.pending_fault.set(Some((target, fault_pc)));
                    InvokeOutcome::Threw(value, origin)
                }
                Ok((FrameCompletion::Suspend(value, _), _)) => {
                    self.pending_fatal_kind
                        .set(Some(RuntimeErrorKind::InvalidValue { value }));
                    InvokeOutcome::Fatal
                }
                Err(error) => {
                    self.pending_error.set(Some(error));
                    InvokeOutcome::Fatal
                }
            }
        } else {
            self.invoke_linked(target, captures, this, new_target, args)
        };
        self.machine.borrow_mut().context_global = previous;
        outcome
    }

    fn resume_generator(&self, generator: Value, completion: GeneratorCompletion) -> InvokeOutcome {
        let operation = crate::vm::generator_async::prepare_generator_operation(
            &mut self.machine.borrow_mut(),
            generator,
            completion,
        );
        let resumed = match operation {
            Ok(crate::vm::generator_async::PreparedGeneratorOperation::Start { start, .. }) => {
                if self.backend == Backend::Reference || self.is_dynamic_module(start.target.module)
                {
                    self.start_reference_generator(start)
                } else {
                    self.start_linked_generator(start)
                }
            }
            Ok(crate::vm::generator_async::PreparedGeneratorOperation::Resume {
                activation,
                completion,
            }) => {
                if self.backend == Backend::Reference
                    || self.is_dynamic_module(activation.target.module)
                {
                    self.resume_reference_generator(activation, completion)
                } else {
                    self.resume_linked_generator(activation, completion)
                }
            }
            Ok(crate::vm::generator_async::PreparedGeneratorOperation::Complete(value)) => {
                return self.generator_result(value, true);
            }
            Ok(crate::vm::generator_async::PreparedGeneratorOperation::Raise { value, origin }) => {
                return InvokeOutcome::Threw(value, origin);
            }
            Err(failure) => return self.failure_outcome(failure),
        };

        match resumed {
            Some(GeneratorResume::Yield { value, activation }) => {
                let result = self
                    .machine
                    .borrow_mut()
                    .settle_generator_yield(generator, value, activation);
                self.eval_outcome(result)
            }
            Some(GeneratorResume::Return(value)) => {
                let settled = self
                    .machine
                    .borrow_mut()
                    .settle_generator_completed(generator);
                if let Err(failure) = settled {
                    return self.failure_outcome(failure);
                }
                self.generator_result(value, true)
            }
            Some(GeneratorResume::Throw { value, origin }) => {
                let settled = self
                    .machine
                    .borrow_mut()
                    .settle_generator_completed(generator);
                if let Err(failure) = settled {
                    return self.failure_outcome(failure);
                }
                InvokeOutcome::Threw(value, origin)
            }
            None => {
                if let Err(failure) = self
                    .machine
                    .borrow_mut()
                    .settle_generator_completed(generator)
                {
                    return self.failure_outcome(failure);
                }
                InvokeOutcome::Fatal
            }
        }
    }

    fn generator_result(&self, value: Value, done: bool) -> InvokeOutcome {
        let result = self.machine.borrow_mut().iterator_result(value, done);
        self.eval_outcome(result)
    }

    fn eval_outcome(&self, result: Result<Value, EvalFailure>) -> InvokeOutcome {
        match result {
            Ok(value) => InvokeOutcome::Value(value),
            Err(failure) => self.failure_outcome(failure),
        }
    }

    fn failure_outcome(&self, failure: EvalFailure) -> InvokeOutcome {
        match failure {
            EvalFailure::Throw(origin) => InvokeOutcome::Threw(Value::UNDEFINED, origin),
            EvalFailure::ThrowValue(value) => InvokeOutcome::Threw(value, ThrowOrigin::Bytecode),
            EvalFailure::ThrowValueOrigin { value, origin } => InvokeOutcome::Threw(value, origin),
            EvalFailure::Runtime(kind) => {
                self.pending_fatal_kind.set(Some(kind));
                InvokeOutcome::Fatal
            }
        }
    }

    fn get_outcome(
        &self,
        outcome: Result<GetOutcome, EvalFailure>,
        receiver: Value,
    ) -> InvokeOutcome {
        match outcome {
            Ok(GetOutcome::Value(value)) => InvokeOutcome::Value(value),
            Ok(GetOutcome::Text(text)) => {
                match self.machine.borrow_mut().allocate(HeapEntry::String(text)) {
                    Ok(value) => InvokeOutcome::Value(value),
                    Err(kind) => {
                        self.pending_fatal_kind.set(Some(kind));
                        InvokeOutcome::Fatal
                    }
                }
            }
            Ok(GetOutcome::Getter(getter)) => {
                self.invoke_callee(getter, receiver, &[], Value::UNDEFINED)
            }
            Err(failure) => self.failure_outcome(failure),
        }
    }

    fn get_ascii(&self, object: Value, name: &str) -> InvokeOutcome {
        let key = crate::PropertyKey::Named(bamts_bytecode::EcmaString::encode(name));
        let outcome = self
            .machine
            .borrow_mut()
            .internal_get(object, &key, object)
            .map(crate::GetOutcome::Value);
        self.get_outcome(outcome, object)
    }

    fn dispose_capture_active(
        &self,
        source: Value,
        hint: u32,
    ) -> Result<(Value, u32), InvokeOutcome> {
        if matches!(source.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return Ok((Value::UNDEFINED, 0));
        }
        if !self.machine.borrow().is_object(source) {
            return Err(InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "disposable resource is not an object",
                },
            ));
        }

        let async_hint = match hint {
            0 => false,
            1 => true,
            _ => {
                return Err(self.failure_outcome(EvalFailure::Runtime(
                    RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    },
                )));
            }
        };
        let symbol = if async_hint {
            self.machine
                .borrow()
                .intrinsics
                .builtins
                .symbol_async_dispose()
        } else {
            self.machine.borrow().intrinsics.builtins.symbol_dispose()
        };
        let key = match self.machine.borrow_mut().to_property_key(symbol) {
            Ok(key) => key,
            Err(failure) => return Err(self.failure_outcome(failure)),
        };
        let method = match self.get_outcome(
            self.machine
                .borrow_mut()
                .internal_get(source, &key, source)
                .map(crate::GetOutcome::Value),
            source,
        ) {
            InvokeOutcome::Value(method) => method,
            outcome => return Err(outcome),
        };
        if !matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            let callable = match self.machine.borrow().is_callable(method) {
                Ok(callable) => callable,
                Err(failure) => return Err(self.failure_outcome(failure)),
            };
            return callable.then_some((method, 1)).ok_or(InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "disposal method is not callable",
                },
            ));
        }
        if !async_hint {
            return Err(InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "disposal method is not callable",
                },
            ));
        }

        let symbol = self.machine.borrow().intrinsics.builtins.symbol_dispose();
        let key = match self.machine.borrow_mut().to_property_key(symbol) {
            Ok(key) => key,
            Err(failure) => return Err(self.failure_outcome(failure)),
        };
        let method = match self.get_outcome(
            self.machine
                .borrow_mut()
                .internal_get(source, &key, source)
                .map(crate::GetOutcome::Value),
            source,
        ) {
            InvokeOutcome::Value(method) => method,
            outcome => return Err(outcome),
        };
        let callable = match self.machine.borrow().is_callable(method) {
            Ok(callable) => callable,
            Err(failure) => return Err(self.failure_outcome(failure)),
        };
        callable.then_some((method, 2)).ok_or(InvokeOutcome::Threw(
            Value::UNDEFINED,
            ThrowOrigin::TypeError {
                operation: "disposal method is not callable",
            },
        ))
    }

    fn get_iterator_active(
        &self,
        source: Value,
        kind: bamts_bytecode::IteratorKind,
    ) -> InvokeOutcome {
        if kind == bamts_bytecode::IteratorKind::Keys {
            let created = self.machine.borrow_mut().create_iterator(source, kind);
            return self.eval_outcome(created);
        }
        let symbol = match kind {
            bamts_bytecode::IteratorKind::Async => self
                .machine
                .borrow()
                .intrinsics
                .builtins
                .symbol_async_iterator(),
            bamts_bytecode::IteratorKind::Sync => {
                self.machine.borrow().intrinsics.builtins.symbol_iterator()
            }
            bamts_bytecode::IteratorKind::Keys => unreachable!("keys handled above"),
        };
        let key = match self.machine.borrow_mut().to_property_key(symbol) {
            Ok(key) => key,
            Err(failure) => return self.failure_outcome(failure),
        };
        let method = self
            .machine
            .borrow_mut()
            .internal_get(source, &key, source)
            .map(crate::GetOutcome::Value);
        let mut method = match self.get_outcome(method, source) {
            InvokeOutcome::Value(method) => method,
            other => return other,
        };
        let mut from_sync = false;
        if kind == bamts_bytecode::IteratorKind::Async
            && matches!(method, Value::UNDEFINED | Value::NULL)
        {
            from_sync = true;
            let symbol = self.machine.borrow().intrinsics.builtins.symbol_iterator();
            let key = match self.machine.borrow_mut().to_property_key(symbol) {
                Ok(key) => key,
                Err(failure) => return self.failure_outcome(failure),
            };
            let fallback = self
                .machine
                .borrow_mut()
                .internal_get(source, &key, source)
                .map(crate::GetOutcome::Value);
            method = match self.get_outcome(fallback, source) {
                InvokeOutcome::Value(method) => method,
                other => return other,
            };
        }
        match self.machine.borrow().is_callable(method) {
            Ok(true) => {}
            Ok(false) => {
                return InvokeOutcome::Threw(
                    Value::UNDEFINED,
                    ThrowOrigin::TypeError {
                        operation: "value is not iterable",
                    },
                );
            }
            Err(failure) => return self.failure_outcome(failure),
        }
        let iterator = match self.invoke_callee(method, source, &[], Value::UNDEFINED) {
            InvokeOutcome::Value(iterator) => iterator,
            other => return other,
        };
        if !self.machine.borrow().is_object(iterator) {
            return InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "iterator method returned a non-object",
                },
            );
        }
        let next = match self.get_ascii(iterator, "next") {
            InvokeOutcome::Value(next) => next,
            other => return other,
        };
        let created = if from_sync {
            self.machine
                .borrow_mut()
                .create_async_from_sync_iterator(iterator, next)
        } else {
            self.machine
                .borrow_mut()
                .create_protocol_iterator(iterator, next)
        };
        self.eval_outcome(created)
    }

    fn iterator_step_active(&self, iterator: Value) -> Result<Value, InvokeOutcome> {
        let prepared = self.machine.borrow_mut().prepare_iterator_next(iterator);
        match prepared {
            Ok(IteratorNextPrepared::Ready { done, value }) => {
                let result = self.machine.borrow_mut().iterator_result(value, done);
                result.map_err(|failure| self.failure_outcome(failure))
            }
            Ok(IteratorNextPrepared::Call { callee, this_value }) => {
                match self.invoke_callee(callee, this_value, &[], Value::UNDEFINED) {
                    InvokeOutcome::Value(result) => Ok(result),
                    other => Err(other),
                }
            }
            Ok(IteratorNextPrepared::AsyncFromSyncCall { callee, this_value }) => {
                let call = match self.invoke_callee(callee, this_value, &[], Value::UNDEFINED) {
                    InvokeOutcome::Value(result) => Ok(result),
                    InvokeOutcome::Threw(value, origin) => {
                        Err(EvalFailure::ThrowValueOrigin { value, origin })
                    }
                    InvokeOutcome::Fatal => return Err(InvokeOutcome::Fatal),
                };
                self.machine
                    .borrow_mut()
                    .async_from_sync_continuation(this_value, call)
                    .map_err(|failure| self.failure_outcome(failure))
            }
            Err(failure) => Err(self.failure_outcome(failure)),
        }
    }

    fn close_iterator_active(
        &self,
        frame: &mut NativeFrame<'_>,
        iterator: Value,
        mode: u32,
        called_reg: u32,
    ) -> Result<Value, InvokeOutcome> {
        frame.set_register(called_reg, Value::FALSE);
        let preserve_abrupt = mode == 1;
        let map_outcome = |outcome| match outcome {
            InvokeOutcome::Value(value) => Ok(value),
            InvokeOutcome::Fatal => Err(InvokeOutcome::Fatal),
            InvokeOutcome::Threw(_, _) if preserve_abrupt => Ok(Value::UNDEFINED),
            InvokeOutcome::Threw(value, origin) => Err(InvokeOutcome::Threw(value, origin)),
        };
        let target = match self.machine.borrow_mut().iterator_close_target(iterator) {
            Ok(Some(target)) => target,
            Ok(None) => return Ok(Value::UNDEFINED),
            Err(failure) => return map_outcome(self.failure_outcome(failure)),
        };
        let close = match self.get_ascii(target, "return") {
            InvokeOutcome::Value(close) => close,
            outcome => return map_outcome(outcome),
        };
        if matches!(close.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return Ok(Value::UNDEFINED);
        }
        let callable = match self.machine.borrow().is_callable(close) {
            Ok(callable) => callable,
            Err(failure) => return map_outcome(self.failure_outcome(failure)),
        };
        if !callable {
            return map_outcome(InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "iterator return method is not callable",
                },
            ));
        }
        frame.set_register(called_reg, Value::TRUE);
        map_outcome(self.invoke_callee(close, target, &[], Value::UNDEFINED))
    }

    fn iterator_result_active(&self, result: Value) -> Result<(bool, Value), InvokeOutcome> {
        if !self.machine.borrow().is_object(result) {
            return Err(InvokeOutcome::Threw(
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "iterator result is not an object",
                },
            ));
        }
        let done = match self.get_ascii(result, "done") {
            InvokeOutcome::Value(done) => done,
            other => return Err(other),
        };
        if self.machine.borrow().truthy(done) {
            return Ok((true, Value::UNDEFINED));
        }
        let value = match self.get_ascii(result, "value") {
            InvokeOutcome::Value(value) => value,
            other => return Err(other),
        };
        Ok((false, value))
    }

    fn iterator_next_active(&self, iterator: Value) -> Result<(bool, Value), InvokeOutcome> {
        // Fused sync consumption reads the raw result directly; the
        // async-from-sync adapter wraps only the `for await` step path.
        let prepared = self.machine.borrow_mut().prepare_iterator_next(iterator);
        let result = match prepared {
            Ok(IteratorNextPrepared::Ready { done, value }) => self
                .machine
                .borrow_mut()
                .iterator_result(value, done)
                .map_err(|failure| self.failure_outcome(failure))?,
            Ok(IteratorNextPrepared::Call { callee, this_value })
            | Ok(IteratorNextPrepared::AsyncFromSyncCall { callee, this_value }) => {
                match self.invoke_callee(callee, this_value, &[], Value::UNDEFINED) {
                    InvokeOutcome::Value(result) => result,
                    other => return Err(other),
                }
            }
            Err(failure) => return Err(self.failure_outcome(failure)),
        };
        self.iterator_result_active(result)
    }

    fn array_extend_active(&self, array: Value, iterable: Value) -> InvokeOutcome {
        // The iteration runs user code, and only these locals hold its operands.
        let mark = self
            .machine
            .borrow_mut()
            .hold_temporaries(&[array, iterable]);
        let outcome = self.drain_iterable_into(array, iterable);
        self.machine.borrow_mut().release_temporaries(mark);
        outcome
    }

    fn drain_iterable_into(&self, array: Value, iterable: Value) -> InvokeOutcome {
        let iterator = match self.get_iterator_active(iterable, bamts_bytecode::IteratorKind::Sync)
        {
            InvokeOutcome::Value(iterator) => iterator,
            other => return other,
        };
        self.machine.borrow_mut().hold_temporaries(&[iterator]);
        loop {
            let (done, value) = match self.iterator_next_active(iterator) {
                Ok(step) => step,
                Err(outcome) => return outcome,
            };
            if done {
                return InvokeOutcome::Value(Value::UNDEFINED);
            }
            if let Err(failure) = self.machine.borrow_mut().array_push(array, value) {
                return self.failure_outcome(failure);
            }
        }
    }

    fn start_reference_generator(&self, start: GeneratorStart) -> Option<GeneratorResume> {
        let target = start.target;
        let context = start.context;
        let index = target.function.get() as usize;
        let handle = self.code_ref(target.module);
        let code = handle.code(target.module);
        let register_count = code.functions()[index].register_count() as usize;
        let mut registers = self.seed_registers(code, index, &start.captures, &start.args);
        if let Err(kind) = self
            .machine
            .borrow_mut()
            .reserve_suspended_activation_registers(register_count)
        {
            self.pending_fatal_kind.set(Some(kind));
            return None;
        }
        if let Err(kind) = self.machine.borrow_mut().enter_native_generator() {
            self.machine
                .borrow_mut()
                .release_suspended_activation_registers(register_count);
            self.pending_fatal_kind.set(Some(kind));
            return None;
        }
        self.activations.borrow_mut().push(Activation {
            this_value: start.this_value,
            new_target: start.new_target,
            args: start.args.clone(),
            arguments_object: None,
            pending_resume: None,
            target,
        });
        self.push_native_roots(&registers);
        let previous = {
            let mut machine = self.machine.borrow_mut();
            std::mem::replace(&mut machine.context_global, context)
        };
        let completion = self.run_frame(
            target.module,
            index,
            code,
            &mut registers,
            FrameDrive::GeneratorStart,
        );
        self.machine.borrow_mut().context_global = previous;
        self.pop_native_roots();
        let activation = self
            .activations
            .borrow_mut()
            .pop()
            .expect("generator activation exists");
        self.machine.borrow_mut().leave_native_generator();
        self.finish_reference_generator(target, registers, activation, context, completion)
    }

    fn resume_reference_generator(
        &self,
        mut suspended: SuspendedActivation,
        completion: GeneratorCompletion,
    ) -> Option<GeneratorResume> {
        let target = suspended.target;
        let context = suspended.context;
        let index = target.function.get() as usize;
        let handle = self.code_ref(target.module);
        let code = handle.code(target.module);
        let register_count = suspended.registers.len();
        if let Err(kind) = self.machine.borrow_mut().enter_native_generator() {
            self.machine
                .borrow_mut()
                .release_suspended_activation_registers(register_count);
            self.pending_fatal_kind.set(Some(kind));
            return None;
        }
        self.activations.borrow_mut().push(Activation {
            this_value: suspended.this_value,
            new_target: suspended.new_target,
            args: suspended.args.clone(),
            arguments_object: suspended.arguments_object,
            pending_resume: None,
            target,
        });
        self.push_native_roots(&suspended.registers);
        let previous = {
            let mut machine = self.machine.borrow_mut();
            std::mem::replace(&mut machine.context_global, context)
        };
        let completion = self.run_frame(
            target.module,
            index,
            code,
            &mut suspended.registers,
            FrameDrive::GeneratorResume {
                token: suspended.resume_token,
                completion,
            },
        );
        self.machine.borrow_mut().context_global = previous;
        self.pop_native_roots();
        let activation = self
            .activations
            .borrow_mut()
            .pop()
            .expect("generator activation exists");
        self.machine.borrow_mut().leave_native_generator();
        self.finish_reference_generator(
            target,
            suspended.registers,
            activation,
            context,
            completion,
        )
    }

    fn finish_reference_generator(
        &self,
        target: crate::RuntimeFunction,
        registers: Vec<Value>,
        activation: Activation,
        context: Option<Value>,
        completion: Result<FrameCompletion, RuntimeError>,
    ) -> Option<GeneratorResume> {
        let register_count = registers.len();
        match completion {
            Ok(FrameCompletion::Suspend(value, resume_token)) => Some(GeneratorResume::Yield {
                value,
                activation: SuspendedActivation {
                    target,
                    registers,
                    this_value: activation.this_value,
                    new_target: activation.new_target,
                    args: activation.args,
                    arguments_object: activation.arguments_object,
                    context,
                    resume_token,
                },
            }),
            Ok(FrameCompletion::Normal(value)) => {
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                Some(GeneratorResume::Return(value))
            }
            Ok(FrameCompletion::Unwind(value, origin, _)) => {
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                Some(GeneratorResume::Throw { value, origin })
            }
            Err(error) => {
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                self.pending_error.set(Some(error));
                None
            }
        }
    }

    fn start_linked_generator(&self, start: GeneratorStart) -> Option<GeneratorResume> {
        let index = start.target.function.get() as usize;
        let handle = self.code_ref(start.target.module);
        let code = handle.code(start.target.module);
        let registers = self.seed_registers(code, index, &start.captures, &start.args);
        if let Err(kind) = self
            .machine
            .borrow_mut()
            .reserve_suspended_activation_registers(registers.len())
        {
            self.pending_fatal_kind.set(Some(kind));
            return None;
        }
        self.drive_linked_generator(
            SuspendedActivation {
                target: start.target,
                registers,
                this_value: start.this_value,
                new_target: start.new_target,
                args: start.args,
                arguments_object: None,
                context: start.context,
                resume_token: 0,
            },
            None,
        )
    }

    fn resume_linked_generator(
        &self,
        activation: SuspendedActivation,
        completion: GeneratorCompletion,
    ) -> Option<GeneratorResume> {
        self.drive_linked_generator(activation, Some(completion))
    }

    fn drive_linked_generator(
        &self,
        mut suspended: SuspendedActivation,
        pending_resume: Option<GeneratorCompletion>,
    ) -> Option<GeneratorResume> {
        let register_count = suspended.registers.len();
        if let Err(kind) = self.machine.borrow_mut().enter_native_generator() {
            self.machine
                .borrow_mut()
                .release_suspended_activation_registers(register_count);
            self.pending_fatal_kind.set(Some(kind));
            return None;
        }
        let length = match u16::try_from(register_count) {
            Ok(length) => length,
            Err(_) => {
                self.machine.borrow_mut().leave_native_generator();
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                self.pending_fatal_kind
                    .set(Some(RuntimeErrorKind::RegisterLimitExceeded {
                        limit: self.max_total_registers(),
                    }));
                return None;
            }
        };
        self.activations.borrow_mut().push(Activation {
            this_value: suspended.this_value,
            new_target: suspended.new_target,
            args: suspended.args.clone(),
            arguments_object: suspended.arguments_object,
            pending_resume,
            target: suspended.target,
        });
        self.push_native_roots(&suspended.registers);
        let handles = suspended.registers.as_mut_ptr();
        let previous = {
            let mut machine = self.machine.borrow_mut();
            std::mem::replace(&mut machine.context_global, suspended.context)
        };
        let (invoked, next_token, out) = {
            let mut shadow = ShadowFrame::new(
                std::ptr::null_mut(),
                suspended.resume_token,
                suspended.target.module.get(),
                handles,
                length,
            );
            let mut out = Completion::new(Value::UNDEFINED);
            let invoked = self.entries.invoke(
                suspended.target.module.get(),
                suspended.target.function.get(),
                &mut shadow,
                &mut out,
            );
            (invoked, shadow.bytecode_pc, out)
        };
        self.machine.borrow_mut().context_global = previous;
        self.pop_native_roots();
        let activation = self
            .activations
            .borrow_mut()
            .pop()
            .expect("generator activation exists");
        self.machine.borrow_mut().leave_native_generator();
        suspended.arguments_object = activation.arguments_object;

        match invoked {
            Ok(CompletionTag::Suspend) if next_token != 0 => {
                suspended.resume_token = next_token;
                Some(GeneratorResume::Yield {
                    value: out.value,
                    activation: suspended,
                })
            }
            Ok(CompletionTag::Normal) => {
                self.pending_throw.take();
                self.pending_fault.take();
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                Some(GeneratorResume::Return(out.value))
            }
            Ok(CompletionTag::Throw) => {
                if self.pending_fault.get().is_none() {
                    self.pending_fault
                        .set(Some((suspended.target, next_token as usize)));
                }
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                let (value, origin) = self.take_matching_throw(out.value);
                Some(GeneratorResume::Throw { value, origin })
            }
            Ok(CompletionTag::Suspend | CompletionTag::FatalTrap) => {
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                None
            }
            Err(error) => {
                self.machine
                    .borrow_mut()
                    .release_suspended_activation_registers(register_count);
                self.pending_abi_error.set(Some(error));
                None
            }
        }
    }

    /// True when this engine was built by [`run_linked_program_tiered`].
    fn tiering_enabled(&self) -> bool {
        self.tiering.is_some()
    }

    /// Cancels every unit in the live tiering table, if any.
    fn cancel_tiering(&self) {
        if let Some(table) = &self.tiering {
            table.borrow_mut().cancel_all();
        }
    }

    /// Surfaces cooperative cancellation as [`NativeError::Cancelled`] and
    /// freezes the tiering table so later observations stay inert.
    fn native_cancel(&self) -> NativeError {
        self.cancel_tiering();
        NativeError::Cancelled
    }

    /// Maps a runtime error that may be a cancel checkpoint into the public
    /// cancel error when appropriate.
    fn map_runtime_cancel(&self, error: RuntimeError) -> NativeError {
        if matches!(error.kind, RuntimeErrorKind::Cancelled) {
            self.native_cancel()
        } else {
            NativeError::Runtime(error)
        }
    }

    /// Records one invocation under the live policy and returns whether this
    /// activation must stay on the reference `execute()` path (still
    /// interpreted, or pinned).
    fn should_interpret_unit(&self, module: ModuleId, function: FunctionId) -> bool {
        let Some(table) = &self.tiering else {
            return false;
        };
        let mut table = table.borrow_mut();
        let Some(unit) = table.get_mut(module, function) else {
            return true;
        };
        let _ = unit.state.observe_invocation();
        unit.state.is_pinned() || matches!(unit.state.tier(), Tier::Interpreter)
    }

    /// Polls the tiering table for an OSR decision on a taken back edge.
    fn poll_osr_entry(
        &self,
        module: ModuleId,
        function: FunctionId,
        target: usize,
        current: usize,
    ) -> Option<bamts_native::tiering::OsrEntry> {
        if !self.tiering_enabled() || target > current {
            return None;
        }
        let table = self.tiering.as_ref()?;
        let mut table = table.borrow_mut();
        let unit = table.get_mut(module, function)?;
        unit.state
            .observe_back_edge(Pc::new(target as u32), Pc::new(current as u32))
    }

    /// Performs the compiled OSR transfer after the caller has ended its
    /// [`NativeFrame`] borrow. Reuses the same [`ShadowFrame`]/registers.
    fn transfer_osr(
        &self,
        module: ModuleId,
        function: usize,
        shadow: &mut ShadowFrame,
        osr_pc: u32,
    ) -> Result<OsrFlow, RuntimeError> {
        let function_id = FunctionId::new(function as u32);
        shadow.bytecode_pc = 0x8000_0000u32 | osr_pc;
        if let Some(table) = &self.tiering
            && let Some(unit) = table.borrow_mut().get_mut(module, function_id)
        {
            unit.osr_entries = unit.osr_entries.saturating_add(1);
        }
        let mut out = Completion::new(Value::UNDEFINED);
        let entries = self.entries;
        let tag = with_native_ops_ref(self, || {
            entries.invoke(module.get(), function_id.get(), shadow, &mut out)
        });
        let fault_pc = shadow.bytecode_pc as usize;
        match tag {
            Ok(CompletionTag::Normal) => {
                self.pending_throw.take();
                self.pending_fault.take();
                Ok(OsrFlow::Done(FrameCompletion::Normal(out.value)))
            }
            Ok(CompletionTag::Throw) => {
                let target = crate::RuntimeFunction {
                    module,
                    function: function_id,
                };
                if self.pending_fault.get().is_none() {
                    self.pending_fault.set(Some((target, fault_pc)));
                }
                let (value, origin) = self.take_matching_throw(out.value);
                Ok(OsrFlow::Done(FrameCompletion::Unwind(
                    value, origin, fault_pc,
                )))
            }
            Ok(CompletionTag::Suspend) => Err(self.error_at(
                module,
                RuntimeErrorKind::InvalidValue { value: out.value },
                function,
                fault_pc,
            )),
            Ok(CompletionTag::FatalTrap) => {
                let pending_error = self.pending_error.take();
                let pending_fatal_kind = self.pending_fatal_kind.take();
                let pending_abi_error = self.pending_abi_error.take();
                let can_classify = pending_error.is_none()
                    && pending_fatal_kind.is_none()
                    && pending_abi_error.is_none();
                if !can_classify {
                    if let Some(error) = pending_error {
                        self.pending_error.set(Some(error));
                    }
                    if let Some(kind) = pending_fatal_kind {
                        self.pending_fatal_kind.set(Some(kind));
                    }
                    if let Some(error) = pending_abi_error {
                        self.pending_abi_error.set(Some(error));
                    }
                }
                let reason = match (can_classify, out.value.as_int32()) {
                    (true, Some(trap_id)) => deopt_reason(CompletionTag::FatalTrap, trap_id),
                    _ => None,
                };
                let Some(reason) = reason else {
                    if let Some(error) = self.pending_error.take() {
                        return Err(error);
                    }
                    if let Some(kind) = self.pending_fatal_kind.take() {
                        return Err(self.error_at(module, kind, function, fault_pc));
                    }
                    return Err(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue { value: out.value },
                        function,
                        fault_pc,
                    ));
                };
                if let Some(table) = &self.tiering
                    && let Some(unit) = table.borrow_mut().get_mut(module, function_id)
                {
                    let _ = unit.state.record_deopt(reason);
                }
                if matches!(reason, DeoptReason::Panic) {
                    return Err(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue { value: out.value },
                        function,
                        fault_pc,
                    ));
                }
                Ok(OsrFlow::ContinueAt(fault_pc))
            }
            Err(error) => {
                self.pending_abi_error.set(Some(error));
                Err(self.error_at(
                    module,
                    RuntimeErrorKind::InvalidValue { value: out.value },
                    function,
                    fault_pc,
                ))
            }
        }
    }

    fn map_execute_outcome(
        &self,
        target: crate::RuntimeFunction,
        result: Result<(FrameCompletion, Vec<Value>), RuntimeError>,
    ) -> InvokeOutcome {
        match result {
            Ok((FrameCompletion::Normal(value), _)) => InvokeOutcome::Value(value),
            Ok((FrameCompletion::Unwind(value, origin, fault_pc), _)) => {
                self.pending_fault.set(Some((target, fault_pc)));
                InvokeOutcome::Threw(value, origin)
            }
            Ok((FrameCompletion::Suspend(value, _), _)) => {
                self.pending_fatal_kind
                    .set(Some(RuntimeErrorKind::InvalidValue { value }));
                InvokeOutcome::Fatal
            }
            Err(error) => {
                if matches!(error.kind, RuntimeErrorKind::Cancelled) {
                    self.cancel_tiering();
                }
                self.pending_error.set(Some(error));
                InvokeOutcome::Fatal
            }
        }
    }

    /// Invokes a compiled entry through the borrowed [`NativeEntryTable`],
    /// building a fresh child [`ShadowFrame`] over a driver-local register file.
    fn invoke_linked(
        &self,
        target: crate::RuntimeFunction,
        captures: &[Value],
        this: Value,
        new_target: Value,
        args: &[Value],
    ) -> InvokeOutcome {
        debug_assert!(!self.is_dynamic_module(target.module));
        let index = target.function.get() as usize;
        if self.should_interpret_unit(target.module, target.function) {
            return self.map_execute_outcome(
                target,
                self.execute(
                    target.module,
                    index,
                    this,
                    new_target,
                    args.to_vec(),
                    captures,
                ),
            );
        }
        let handle = self.code_ref(target.module);
        let code = handle.code(target.module);
        let register_count = code.functions()[index].register_count() as usize;
        let mut registers = self.seed_registers(code, index, captures, args);
        let length = match u16::try_from(registers.len()) {
            Ok(length) => length,
            Err(_) => {
                let limit = self.max_total_registers();
                self.pending_fatal_kind
                    .set(Some(RuntimeErrorKind::RegisterLimitExceeded { limit }));
                return InvokeOutcome::Fatal;
            }
        };
        if let Err(kind) = self
            .machine
            .borrow_mut()
            .reserve_native_activation(register_count)
        {
            self.pending_fatal_kind.set(Some(kind));
            return InvokeOutcome::Fatal;
        }
        self.activations.borrow_mut().push(Activation {
            this_value: this,
            new_target,
            args: args.to_vec(),
            arguments_object: None,
            pending_resume: None,
            target,
        });
        self.push_native_roots(&registers);
        let handles = registers.as_mut_ptr();
        let (tag, mut out, fault_pc) = {
            let mut shadow = ShadowFrame::new(
                std::ptr::null_mut(),
                0,
                target.module.get(),
                handles,
                length,
            );
            let mut out = Completion::new(Value::UNDEFINED);
            let entries = self.entries;
            let tag = if self.tiering_enabled() {
                with_native_ops_ref(self, || {
                    entries.invoke(
                        target.module.get(),
                        target.function.get(),
                        &mut shadow,
                        &mut out,
                    )
                })
            } else {
                entries.invoke(
                    target.module.get(),
                    target.function.get(),
                    &mut shadow,
                    &mut out,
                )
            };
            (tag, out, shadow.bytecode_pc as usize)
        };
        let outcome = match tag {
            Ok(CompletionTag::Normal) => {
                self.pending_throw.take();
                self.pending_fault.take();
                InvokeOutcome::Value(out.value)
            }
            Ok(CompletionTag::Throw) => {
                if self.pending_fault.get().is_none() {
                    self.pending_fault.set(Some((target, fault_pc)));
                }
                let (value, origin) = self.take_matching_throw(out.value);
                InvokeOutcome::Threw(value, origin)
            }
            Ok(CompletionTag::Suspend) => InvokeOutcome::Fatal,
            Ok(CompletionTag::FatalTrap) => {
                let pending_error = self.pending_error.take();
                let pending_fatal_kind = self.pending_fatal_kind.take();
                let pending_abi_error = self.pending_abi_error.take();
                let can_classify = pending_error.is_none()
                    && pending_fatal_kind.is_none()
                    && pending_abi_error.is_none();
                if !can_classify {
                    if let Some(error) = pending_error {
                        self.pending_error.set(Some(error));
                    }
                    if let Some(kind) = pending_fatal_kind {
                        self.pending_fatal_kind.set(Some(kind));
                    }
                    if let Some(error) = pending_abi_error {
                        self.pending_abi_error.set(Some(error));
                    }
                }
                let reason = match (can_classify, out.value.as_int32()) {
                    (true, Some(trap_id)) => deopt_reason(CompletionTag::FatalTrap, trap_id),
                    _ => None,
                };
                match reason {
                    Some(reason) => {
                        if let Some(table) = &self.tiering
                            && let Some(unit) =
                                table.borrow_mut().get_mut(target.module, target.function)
                        {
                            let _ = unit.state.record_deopt(reason);
                        }
                        // Panic: record deopt/pin, but do not resume this activation.
                        if matches!(reason, DeoptReason::Panic) {
                            InvokeOutcome::Fatal
                        } else {
                            // Keep Activation pushed; reconstruct at fault_pc.
                            let handle = self.code_ref(target.module);
                            let code = handle.code(target.module);
                            match self.run_frame(
                                target.module,
                                index,
                                code,
                                &mut registers,
                                FrameDrive::Resume { pc: fault_pc },
                            ) {
                                Ok(FrameCompletion::Normal(value)) => InvokeOutcome::Value(value),
                                Ok(FrameCompletion::Unwind(value, origin, unwind_pc)) => {
                                    if self.pending_fault.get().is_none() {
                                        self.pending_fault.set(Some((target, unwind_pc)));
                                    }
                                    InvokeOutcome::Threw(value, origin)
                                }
                                Ok(FrameCompletion::Suspend(value, _)) => {
                                    self.pending_fatal_kind
                                        .set(Some(RuntimeErrorKind::InvalidValue { value }));
                                    InvokeOutcome::Fatal
                                }
                                Err(error) => {
                                    if matches!(error.kind, RuntimeErrorKind::Cancelled) {
                                        self.cancel_tiering();
                                    }
                                    self.pending_error.set(Some(error));
                                    InvokeOutcome::Fatal
                                }
                            }
                        }
                    }
                    None => InvokeOutcome::Fatal,
                }
            }
            Err(error) => {
                self.pending_abi_error.set(Some(error));
                InvokeOutcome::Fatal
            }
        };
        drop(registers);
        self.pop_native_roots();
        self.activations.borrow_mut().pop();
        self.machine
            .borrow_mut()
            .release_native_activation(register_count);
        let _ = &mut out;
        outcome
    }

    fn evaluate_import(&self, module: ModuleId) -> Result<(), ImportFailure> {
        let begun = self.machine.borrow_mut().begin_module_evaluation(module);
        let dependencies = match begun {
            Err(error) => {
                self.pending_error.set(Some(error));
                return Err(ImportFailure::Fatal);
            }
            Ok(crate::ModuleEvaluation::Cycle) => return Ok(()),
            Ok(crate::ModuleEvaluation::Evaluated(Ok(()))) => return Ok(()),
            Ok(crate::ModuleEvaluation::Evaluated(Err(error))) => {
                if matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }) {
                    return Err(ImportFailure::Threw(error));
                }
                self.pending_error.set(Some(error));
                return Err(ImportFailure::Fatal);
            }
            Ok(crate::ModuleEvaluation::Ready(dependencies)) => dependencies,
        };
        for dependency in dependencies {
            if let Err(failure) = self.evaluate_import(dependency) {
                let mut machine = self.machine.borrow_mut();
                match &failure {
                    ImportFailure::Threw(error) => {
                        machine.settle_module_evaluation(module, Err(error.clone()));
                    }
                    ImportFailure::Fatal => machine.abort_module_evaluation(module),
                }
                return Err(failure);
            }
        }

        let function = self.module(module).entry();
        let outcome = self.invoke_runtime(
            crate::RuntimeFunction { module, function },
            &[],
            None,
            Value::UNDEFINED,
            Value::UNDEFINED,
            &[],
        );
        match outcome {
            InvokeOutcome::Value(_) => {
                self.machine
                    .borrow_mut()
                    .settle_module_evaluation(module, Ok(()));
                Ok(())
            }
            InvokeOutcome::Threw(value, origin) => {
                let error = self.error_at(
                    module,
                    RuntimeErrorKind::UncaughtThrow {
                        value,
                        origin,
                        constructor_name: None,
                        message: None,
                    },
                    function.get() as usize,
                    0,
                );
                self.machine
                    .borrow_mut()
                    .settle_module_evaluation(module, Err(error.clone()));
                Err(ImportFailure::Threw(error))
            }
            InvokeOutcome::Fatal => {
                self.machine.borrow_mut().abort_module_evaluation(module);
                Err(ImportFailure::Fatal)
            }
        }
    }

    fn import_namespace(&self, requester: ModuleId, specifier: u32) -> HelperResult {
        let target = self
            .machine
            .borrow()
            .resolve_import(requester, ConstantId::new(specifier));
        let target = match target {
            Ok(target) => target,
            Err(kind) => return self.fatal(kind),
        };
        if let crate::ImportTarget::Local(module) = target
            && let Err(failure) = self.evaluate_import(module)
        {
            return match failure {
                ImportFailure::Threw(error) => self.fail(crate::import_failure(&error)),
                ImportFailure::Fatal => HelperResult {
                    tag: CompletionTag::FatalTrap,
                    value: Value::UNDEFINED,
                },
            };
        }
        let namespace = self
            .machine
            .borrow_mut()
            .imported_namespace(requester, target);
        match namespace {
            Ok(value) => HelperResult::normal(value),
            Err(kind) => self.fatal(kind),
        }
    }

    // -- HelperResult constructors -------------------------------------------

    fn fatal(&self, kind: RuntimeErrorKind) -> HelperResult {
        self.pending_fatal_kind.set(Some(kind));
        HelperResult {
            tag: CompletionTag::FatalTrap,
            value: Value::UNDEFINED,
        }
    }

    /// The function the innermost activation runs.
    fn running_function(&self) -> crate::RuntimeFunction {
        self.activations
            .borrow()
            .last()
            .expect("a helper runs inside an activation")
            .target
    }

    fn running_is_sloppy(&self) -> bool {
        let target = self.running_function();
        self.machine
            .borrow()
            .is_sloppy(target.module, target.function.get() as usize)
    }

    fn load_this(&self) -> HelperResult {
        let target = self.running_function();
        let this_value = self
            .activations
            .borrow()
            .last()
            .map_or(Value::UNDEFINED, |activation| activation.this_value);
        let bound = self.machine.borrow_mut().bind_this(
            target.module,
            target.function.get() as usize,
            this_value,
        );
        match bound {
            Ok(value) => {
                if let Some(activation) = self.activations.borrow_mut().last_mut() {
                    activation.this_value = value;
                }
                HelperResult::normal(value)
            }
            Err(failure) => self.fail(failure),
        }
    }

    fn fail(&self, failure: EvalFailure) -> HelperResult {
        match failure {
            EvalFailure::Throw(origin) => {
                self.pending_throw.set(Some(PendingThrow {
                    value: Value::UNDEFINED,
                    origin,
                }));
                HelperResult::throw(Value::UNDEFINED)
            }
            EvalFailure::ThrowValue(value) => {
                self.pending_throw.set(Some(PendingThrow {
                    value,
                    origin: ThrowOrigin::Bytecode,
                }));
                HelperResult::throw(value)
            }
            EvalFailure::ThrowValueOrigin { value, origin } => {
                self.pending_throw.set(Some(PendingThrow { value, origin }));
                HelperResult::throw(value)
            }
            EvalFailure::Runtime(kind) => self.fatal(kind),
        }
    }

    fn eval_result(&self, result: Result<Value, EvalFailure>) -> HelperResult {
        match result {
            Ok(value) => HelperResult::normal(value),
            Err(failure) => self.fail(failure),
        }
    }

    fn outcome_result(&self, outcome: InvokeOutcome) -> HelperResult {
        match outcome {
            InvokeOutcome::Value(value) => HelperResult::normal(value),
            InvokeOutcome::Threw(value, origin) => {
                self.pending_throw.set(Some(PendingThrow { value, origin }));
                HelperResult::throw(value)
            }
            InvokeOutcome::Fatal => HelperResult {
                tag: CompletionTag::FatalTrap,
                value: Value::UNDEFINED,
            },
        }
    }

    fn validated(&self, value: Value) -> HelperResult {
        HelperResult::normal(value)
    }

    fn allocated(&self, entry: HeapEntry) -> HelperResult {
        let result = self.machine.borrow_mut().allocate(entry);
        match result {
            Ok(value) => HelperResult::normal(value),
            Err(kind) => self.fatal(kind),
        }
    }

    fn constant_text(&self, module: ModuleId, id: u32) -> EcmaString {
        self.machine
            .borrow()
            .constant_text(module, ConstantId::new(id))
            .clone()
    }

    /// Materializes the `arguments` object for the current activation, caching it.
    fn load_arguments(&self) -> HelperResult {
        let args = match self.activations.borrow().last() {
            Some(activation) => activation.args.clone(),
            None => return HelperResult::normal(Value::UNDEFINED),
        };
        if let Some(existing) = self
            .activations
            .borrow()
            .last()
            .and_then(|activation| activation.arguments_object)
        {
            return HelperResult::normal(existing);
        }
        let prototype = self.machine.borrow().intrinsics.array_prototype;
        let properties = self
            .machine
            .borrow()
            .arguments_properties(self.running_is_sloppy());
        let allocated = self.machine.borrow_mut().allocate(HeapEntry::Array {
            elements: args,
            properties,
            prototype: Some(prototype),
            extensible: true,
            length_writable: true,
        });
        let value = match allocated {
            Ok(value) => value,
            Err(kind) => return self.fatal(kind),
        };
        if let Some(activation) = self.activations.borrow_mut().last_mut() {
            activation.arguments_object = Some(value);
        }
        HelperResult::normal(value)
    }

    /// `Construct`/`ConstructWithNewTarget`: allocate the instance with
    /// `new_target`'s `prototype`, invoke with `new.target`, and override a
    /// non-object return with the instance — the shared construct semantics,
    /// over native activations. The legacy tag-12 path passes `callee` as
    /// `new_target`.
    fn construct(&self, callee: Value, new_target: Value, arguments: &[Value]) -> HelperResult {
        let mut callee = callee;
        let mut new_target = new_target;
        let mut arguments = Cow::Borrowed(arguments);
        if matches!(
            self.machine.borrow().callee_kind(callee),
            Ok(CalleeKind::Bound)
        ) {
            let bound = self.machine.borrow().flatten_bound(
                callee,
                Value::UNDEFINED,
                arguments.as_ref(),
                new_target,
            );
            match bound {
                Ok(bound) => {
                    // BoundFunction [[Construct]] forwards through each wrapper;
                    // flatten_bound already applied the recursive newTarget rule.
                    new_target = bound.new_target;
                    callee = bound.target;
                    arguments = Cow::Owned(bound.arguments);
                }
                Err(kind) => return self.fatal(kind),
            }
        }
        let kind = self.machine.borrow().callee_kind(callee);
        match kind {
            Ok(CalleeKind::Builtin { id })
                if !self
                    .machine
                    .borrow()
                    .intrinsics
                    .builtins
                    .is_constructable(id) =>
            {
                self.pending_throw.set(Some(PendingThrow {
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::TypeError {
                        operation: "construct",
                    },
                }));
                HelperResult::throw(Value::UNDEFINED)
            }
            Ok(CalleeKind::Builtin { id }) => {
                let result = self.machine.borrow_mut().call_builtin_with_new_target(
                    id,
                    Value::UNDEFINED,
                    arguments.as_ref(),
                    true,
                    new_target,
                );
                match result {
                    Ok(BuiltinOutcome::Value(value)) => HelperResult::normal(value),
                    Ok(
                        BuiltinOutcome::Call { .. }
                        | BuiltinOutcome::GeneratorResume { .. }
                        | BuiltinOutcome::AsyncGeneratorResume { .. },
                    ) => {
                        self.pending_throw.set(Some(PendingThrow {
                            value: Value::UNDEFINED,
                            origin: ThrowOrigin::TypeError {
                                operation: "construct",
                            },
                        }));
                        HelperResult::throw(Value::UNDEFINED)
                    }
                    Err(failure) => self.fail(failure),
                }
            }
            Ok(CalleeKind::Proxy) => {
                let outcome = crate::builtins::proxy::construct(
                    &mut self.machine.borrow_mut(),
                    callee,
                    arguments.as_ref(),
                    new_target,
                );
                self.outcome_result(self.eval_outcome(outcome))
            }
            Ok(CalleeKind::ProxyRevoker) => {
                self.pending_throw.set(Some(PendingThrow {
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::TypeError {
                        operation: "construct",
                    },
                }));
                HelperResult::throw(Value::UNDEFINED)
            }
            Ok(CalleeKind::Runtime {
                target,
                captures,
                context,
            }) => {
                let flags = {
                    let handle = self.code_ref(target.module);
                    handle.code(target.module).functions()[target.function.get() as usize].flags()
                };
                if !flags.is_constructable {
                    self.pending_throw.set(Some(PendingThrow {
                        value: Value::UNDEFINED,
                        origin: ThrowOrigin::TypeError {
                            operation: "construct",
                        },
                    }));
                    return HelperResult::throw(Value::UNDEFINED);
                }
                let instance = {
                    let allocated = self
                        .machine
                        .borrow_mut()
                        .allocate_constructed_receiver(new_target);
                    match allocated {
                        Ok(value) => value,
                        Err(failure) => return self.fail(failure),
                    }
                };
                let outcome = self.invoke_runtime(
                    target,
                    &captures,
                    context,
                    instance,
                    new_target,
                    arguments.as_ref(),
                );
                match outcome {
                    InvokeOutcome::Value(returned) => {
                        let is_object = self.machine.borrow().is_object(returned);
                        HelperResult::normal(if is_object { returned } else { instance })
                    }
                    other => self.outcome_result(other),
                }
            }
            Ok(CalleeKind::Bound) => self.fatal(RuntimeErrorKind::InvalidValue { value: callee }),
            Ok(CalleeKind::NotCallable) => {
                self.pending_throw.set(Some(PendingThrow {
                    value: Value::UNDEFINED,
                    origin: ThrowOrigin::TypeError {
                        operation: "construct",
                    },
                }));
                HelperResult::throw(Value::UNDEFINED)
            }
            Err(kind) => self.fatal(kind),
        }
    }

    fn run_linked(&mut self) -> Result<ExecutionOutcome, NativeError> {
        let result = (|| {
            if self.cancel.is_cancelled() {
                return Err(self.native_cancel());
            }
            self.machine.borrow_mut().instantiate_modules()?;
            let module = self.program.entry();
            let execution = if self.machine.borrow().module_graph_suspends(module) {
                self.machine
                    .borrow_mut()
                    .evaluate_instantiated_module(module)
                    .map_err(NativeError::Runtime)?
            } else {
                self.evaluate_linked_module(module)?.ok_or_else(|| {
                    let function = self.module(module).entry().get() as usize;
                    NativeError::Runtime(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidVerifiedProgram {
                            module,
                            instruction: Instruction::Halt,
                        },
                        function,
                        0,
                    ))
                })?
            };
            self.machine
                .borrow_mut()
                .run_to_quiescence()
                .map_err(NativeError::Runtime)?;
            Ok(execution.outcome)
        })();
        self.machine.borrow_mut().clear_kept_alive_for_job();
        if let Err(NativeError::Runtime(error)) = &result {
            let mut error = error.clone();
            self.machine.borrow_mut().enrich_uncaught_throw(&mut error);
            return Err(NativeError::Runtime(error));
        }
        result
    }

    fn evaluate_linked_module(
        &mut self,
        module: ModuleId,
    ) -> Result<Option<Execution>, NativeError> {
        let dependencies = match self.machine.borrow_mut().begin_module_evaluation(module)? {
            crate::ModuleEvaluation::Cycle => return Ok(None),
            crate::ModuleEvaluation::Evaluated(result) => {
                return result.map(|()| None).map_err(Into::into);
            }
            crate::ModuleEvaluation::Ready(dependencies) => dependencies,
        };
        for dependency in dependencies {
            match self.evaluate_linked_module(dependency) {
                Ok(_) => {}
                Err(NativeError::Runtime(error)) => {
                    let error = self
                        .machine
                        .borrow_mut()
                        .finish_module_evaluation(module, Err(error))
                        .expect_err("dependency failure remains an error");
                    return Err(NativeError::Runtime(error));
                }
                Err(error) => {
                    self.machine.borrow_mut().abort_module_evaluation(module);
                    return Err(error);
                }
            }
        }

        let result = if self.machine.borrow().module_entry_suspends(module) {
            self.machine
                .borrow_mut()
                .run_module_entry(module)
                .map_err(NativeError::Runtime)
        } else {
            self.invoke_linked_entry(module)
        };

        match result {
            Ok(execution) => self
                .machine
                .borrow_mut()
                .finish_module_evaluation(module, Ok(execution))
                .map(Some)
                .map_err(Into::into),
            Err(NativeError::Runtime(error)) => {
                let error = self
                    .machine
                    .borrow_mut()
                    .finish_module_evaluation(module, Err(error))
                    .expect_err("module failure remains an error");
                Err(NativeError::Runtime(error))
            }
            Err(error) => {
                self.machine.borrow_mut().abort_module_evaluation(module);
                Err(error)
            }
        }
    }

    fn invoke_linked_entry(&mut self, module: ModuleId) -> Result<Execution, NativeError> {
        let code = self.module(module);
        let function_id = code.entry();
        let function = function_id.get() as usize;
        let register_count = code.functions()[function].register_count() as usize;
        if self.max_call_depth() < 1 {
            return Err(NativeError::Runtime(self.error_at(
                module,
                RuntimeErrorKind::CallDepthExceeded {
                    limit: self.max_call_depth(),
                },
                function,
                0,
            )));
        }
        if register_count > self.max_total_registers() {
            return Err(NativeError::Runtime(self.error_at(
                module,
                RuntimeErrorKind::RegisterLimitExceeded {
                    limit: self.max_total_registers(),
                },
                function,
                0,
            )));
        }
        if self.cancel.is_cancelled() {
            return Err(self.native_cancel());
        }
        // Tiered entry starts interpreted until promotion; observe first.
        if self.should_interpret_unit(module, function_id) {
            return match self.execute(
                module,
                function,
                Value::UNDEFINED,
                Value::UNDEFINED,
                Vec::new(),
                &[],
            ) {
                Ok((FrameCompletion::Normal(value), registers)) => Ok(Execution {
                    outcome: ExecutionOutcome {
                        stdout: self.stdout.borrow().clone(),
                        exit_code: self.exit_code.get(),
                    },
                    value,
                    link: value,
                    entry_registers: registers,
                }),
                Ok((FrameCompletion::Unwind(value, origin, fault_pc), _)) => {
                    Err(NativeError::Runtime(self.uncaught_throw_at(
                        module, function, fault_pc, value, origin,
                    )))
                }
                Ok((FrameCompletion::Suspend(value, _), _)) => {
                    Err(NativeError::Runtime(self.error_at(
                        module,
                        RuntimeErrorKind::InvalidValue { value },
                        function,
                        0,
                    )))
                }
                Err(error) => Err(self.map_runtime_cancel(error)),
            };
        }
        let mut registers = self.seed_registers(code, function, &[], &[]);
        let length = u16::try_from(register_count).map_err(|_| {
            NativeError::Runtime(self.error_at(
                module,
                RuntimeErrorKind::RegisterLimitExceeded {
                    limit: self.max_total_registers(),
                },
                function,
                0,
            ))
        })?;
        let reserved = self
            .machine
            .borrow_mut()
            .reserve_native_activation(register_count);
        reserved.map_err(|kind| NativeError::Runtime(self.error_at(module, kind, function, 0)))?;
        self.activations.borrow_mut().push(Activation {
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            args: Vec::new(),
            arguments_object: None,
            pending_resume: None,
            target: crate::RuntimeFunction {
                module,
                function: function_id,
            },
        });
        self.push_native_roots(&registers);
        if self.cancel.is_cancelled() {
            self.pop_native_roots();
            self.activations.borrow_mut().pop();
            self.machine
                .borrow_mut()
                .release_native_activation(register_count);
            return Err(self.native_cancel());
        }
        let handles = registers.as_mut_ptr();
        let entries = self.entries;
        let (tag, out, fault_pc) = {
            let mut shadow =
                ShadowFrame::new(std::ptr::null_mut(), 0, module.get(), handles, length);
            let mut out = Completion::new(Value::UNDEFINED);
            let tag = with_native_ops(self, || {
                entries.invoke(module.get(), function_id.get(), &mut shadow, &mut out)
            });
            (tag, out, shadow.bytecode_pc as usize)
        };
        let finish = |engine: &Self, register_count: usize| {
            engine.pop_native_roots();
            engine.activations.borrow_mut().pop();
            engine
                .machine
                .borrow_mut()
                .release_native_activation(register_count);
        };
        let result = match tag {
            Ok(CompletionTag::Normal) => {
                self.pending_throw.take();
                self.pending_fault.take();
                let execution = Execution {
                    outcome: ExecutionOutcome {
                        stdout: self.stdout.borrow().clone(),
                        exit_code: self.exit_code.get(),
                    },
                    value: out.value,
                    link: out.value,
                    entry_registers: registers,
                };
                finish(self, register_count);
                Ok(execution)
            }
            Ok(CompletionTag::Throw) => {
                let (value, origin) = self.take_matching_throw(out.value);
                let error = NativeError::Runtime(
                    self.uncaught_throw_at(module, function, fault_pc, value, origin),
                );
                drop(registers);
                finish(self, register_count);
                Err(error)
            }
            Ok(CompletionTag::Suspend) => {
                let error = if let Some(error) = self.pending_abi_error.take() {
                    NativeError::Abi(error)
                } else if let Some(error) = self.pending_error.take() {
                    self.map_runtime_cancel(error)
                } else if let Some(kind) = self.pending_fatal_kind.take() {
                    if matches!(kind, RuntimeErrorKind::Cancelled) {
                        self.native_cancel()
                    } else {
                        NativeError::Runtime(self.error_at(module, kind, function, fault_pc))
                    }
                } else {
                    NativeError::FatalTrap { value: out.value }
                };
                drop(registers);
                finish(self, register_count);
                Err(error)
            }
            Ok(CompletionTag::FatalTrap) => {
                let pending_error = self.pending_error.take();
                let pending_fatal_kind = self.pending_fatal_kind.take();
                let pending_abi_error = self.pending_abi_error.take();
                let can_classify = pending_error.is_none()
                    && pending_fatal_kind.is_none()
                    && pending_abi_error.is_none();
                if !can_classify {
                    if let Some(error) = pending_error {
                        self.pending_error.set(Some(error));
                    }
                    if let Some(kind) = pending_fatal_kind {
                        self.pending_fatal_kind.set(Some(kind));
                    }
                    if let Some(error) = pending_abi_error {
                        self.pending_abi_error.set(Some(error));
                    }
                }
                let reason = match (can_classify, out.value.as_int32()) {
                    (true, Some(trap_id)) => deopt_reason(CompletionTag::FatalTrap, trap_id),
                    _ => None,
                };
                if let Some(reason) = reason {
                    if let Some(table) = &self.tiering
                        && let Some(unit) = table.borrow_mut().get_mut(module, function_id)
                    {
                        let _ = unit.state.record_deopt(reason);
                    }
                    if matches!(reason, DeoptReason::Panic) {
                        let error = NativeError::FatalTrap { value: out.value };
                        drop(registers);
                        finish(self, register_count);
                        Err(error)
                    } else {
                        let handle = self.code_ref(module);
                        let code = handle.code(module);
                        let reconstructed = self.run_frame(
                            module,
                            function,
                            code,
                            &mut registers,
                            FrameDrive::Resume { pc: fault_pc },
                        );
                        match reconstructed {
                            Ok(FrameCompletion::Normal(value)) => {
                                let execution = Execution {
                                    outcome: ExecutionOutcome {
                                        stdout: self.stdout.borrow().clone(),
                                        exit_code: self.exit_code.get(),
                                    },
                                    value,
                                    link: value,
                                    entry_registers: registers,
                                };
                                finish(self, register_count);
                                Ok(execution)
                            }
                            Ok(FrameCompletion::Unwind(value, origin, unwind_pc)) => {
                                let error =
                                    NativeError::Runtime(self.uncaught_throw_at(
                                        module, function, unwind_pc, value, origin,
                                    ));
                                drop(registers);
                                finish(self, register_count);
                                Err(error)
                            }
                            Ok(FrameCompletion::Suspend(value, _)) => {
                                let error = NativeError::Runtime(self.error_at(
                                    module,
                                    RuntimeErrorKind::InvalidValue { value },
                                    function,
                                    fault_pc,
                                ));
                                drop(registers);
                                finish(self, register_count);
                                Err(error)
                            }
                            Err(error) => {
                                let error = self.map_runtime_cancel(error);
                                drop(registers);
                                finish(self, register_count);
                                Err(error)
                            }
                        }
                    }
                } else {
                    let error = if let Some(error) = self.pending_abi_error.take() {
                        NativeError::Abi(error)
                    } else if let Some(error) = self.pending_error.take() {
                        self.map_runtime_cancel(error)
                    } else if let Some(kind) = self.pending_fatal_kind.take() {
                        if matches!(kind, RuntimeErrorKind::Cancelled) {
                            self.native_cancel()
                        } else {
                            NativeError::Runtime(self.error_at(module, kind, function, fault_pc))
                        }
                    } else {
                        NativeError::FatalTrap { value: out.value }
                    };
                    drop(registers);
                    finish(self, register_count);
                    Err(error)
                }
            }
            Err(error) => {
                drop(registers);
                finish(self, register_count);
                Err(NativeError::Abi(error))
            }
        };
        if self.cancel.is_cancelled() {
            return Err(self.native_cancel());
        }
        result
    }
}

// -- The NativeOps seam ------------------------------------------------------

impl<'m, 'h, H: Host> NativeOps for NativeEngine<'m, 'h, H> {
    fn truthy(&self, _frame: &mut NativeFrame<'_>, value: Value) -> bool {
        self.machine.borrow().truthy(value)
    }

    fn dispatch(&self, frame: &mut NativeFrame<'_>, call: HelperCall) -> HelperResult {
        self.prepare_native_helper(frame);
        let module = ModuleId::new(frame.module_id());
        let amount = match call {
            HelperCall::ResumeValue | HelperCall::ResumeMode => None,
            HelperCall::ConsumeFuel { amount } => Some(u64::from(amount)),
            _ => Some(1),
        };
        if let Some(amount) = amount
            && let Err(kind) = self.machine.borrow_mut().consume_fuel(amount)
        {
            return self.fatal(kind);
        }
        let result = 'result: {
            match call {
                HelperCall::LoadConstant { const_id } => {
                    let result = self
                        .machine
                        .borrow_mut()
                        .load_constant_value(module, ConstantId::new(const_id));
                    match result {
                        Ok(value) => HelperResult::normal(value),
                        Err(kind) => self.fatal(kind),
                    }
                }
                HelperCall::Unary { op, operand } => match unary_from_selector(op) {
                    Some(op) => {
                        let result = self.machine.borrow_mut().eval_unary(op, operand);
                        self.eval_result(result)
                    }
                    None => self.fatal(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    }),
                },
                HelperCall::Binary { op, left, right } => match binary_from_selector(op) {
                    Some(op) => {
                        let result = self.machine.borrow_mut().eval_binary(op, left, right);
                        self.eval_result(result)
                    }
                    None => self.fatal(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    }),
                },
                HelperCall::CreateObject => {
                    let prototype = self.machine.borrow().intrinsics.object_prototype;
                    self.allocated(HeapEntry::Object {
                        properties: PropertyMap::default(),
                        prototype: Some(prototype),
                        boxed_primitive: None,
                        extensible: true,
                    })
                }
                HelperCall::ToObject { value } => {
                    let result = self.machine.borrow_mut().value_to_object(value);
                    self.eval_result(result)
                }
                HelperCall::CreateArray => {
                    let prototype = self.machine.borrow().intrinsics.array_prototype;
                    self.allocated(HeapEntry::Array {
                        elements: Vec::new(),
                        properties: PropertyMap::default(),
                        prototype: Some(prototype),
                        extensible: true,
                        length_writable: true,
                    })
                }
                HelperCall::CreateCell => {
                    let prototype = self.machine.borrow().intrinsics.array_prototype;
                    self.allocated(HeapEntry::Array {
                        elements: vec![Value::UNINITIALIZED],
                        properties: PropertyMap::default(),
                        prototype: Some(prototype),
                        extensible: true,
                        length_writable: true,
                    })
                }
                HelperCall::CreateClosure {
                    function_id,
                    captures,
                } => {
                    let function = FunctionId::new(function_id);
                    let materialized = self
                        .machine
                        .borrow()
                        .captures_from_array(module, captures, function);
                    let context = self.machine.borrow().context_global;
                    match materialized {
                        Ok(captures) => {
                            let prototype =
                                self.machine.borrow().closure_prototype(module, function);
                            let properties = self
                                .machine
                                .borrow_mut()
                                .closure_properties(module, function);
                            let properties = match properties {
                                Ok(properties) => properties,
                                Err(kind) => break 'result self.fatal(kind),
                            };
                            self.allocated(HeapEntry::Function {
                                module,
                                function,
                                captures,
                                context,
                                properties,
                                prototype: Some(prototype),
                                extensible: true,
                            })
                        }
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::GetProperty { object, key } => {
                    let key = {
                        let coerced = self.machine.borrow_mut().computed_property_key(object, key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let outcome = self.machine.borrow_mut().internal_get(object, &key, object);
                    match outcome {
                        Ok(value) => self.validated(value),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::SetProperty { object, key, value } => {
                    let key = {
                        let coerced = self.machine.borrow_mut().computed_property_key(object, key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let outcome = self
                        .machine
                        .borrow_mut()
                        .internal_set(object, key, value, object);
                    match outcome {
                        Ok(true) => HelperResult::normal(Value::UNDEFINED),
                        Ok(false) if self.running_is_sloppy() => {
                            HelperResult::normal(Value::UNDEFINED)
                        }
                        Ok(false) => {
                            self.pending_throw.set(Some(PendingThrow {
                                value: Value::UNDEFINED,
                                origin: ThrowOrigin::TypeError {
                                    operation: "assign to read only property",
                                },
                            }));
                            HelperResult::throw(Value::UNDEFINED)
                        }
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::DeleteProperty { object, key } => {
                    let key = {
                        let coerced = self.machine.borrow_mut().computed_property_key(object, key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let deleted = self.machine.borrow_mut().internal_delete(object, &key);
                    let target = self.running_function();
                    let deleted = deleted.and_then(|deleted| {
                        self.machine.borrow().deletion_result(
                            target.module,
                            target.function.get() as usize,
                            deleted,
                        )
                    });
                    match deleted {
                        Ok(deleted) => HelperResult::normal(Value::boolean(deleted)),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::DefineAccessor {
                    object,
                    key,
                    accessor,
                    kind,
                } => {
                    let kind = match accessor_from_selector(kind) {
                        Some(kind) => kind,
                        None => {
                            break 'result self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            });
                        }
                    };
                    let key = {
                        let coerced = self.machine.borrow_mut().observable_property_key(key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let defined = self
                        .machine
                        .borrow_mut()
                        .define_accessor(object, key, accessor, kind);
                    match defined {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::DefineDataProperty { object, key, value } => {
                    let key = {
                        let coerced = self.machine.borrow_mut().observable_property_key(key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let defined = self.machine.borrow_mut().define_descriptor(
                        object,
                        key,
                        Property::Data {
                            value,
                            writable: true,
                            enumerable: false,
                            configurable: true,
                        },
                    );
                    match defined {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::LoadOwnDescriptorSlot { object, key, slot } => {
                    let slot = match descriptor_slot_from_selector(slot) {
                        Some(slot) => slot,
                        None => {
                            break 'result self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            });
                        }
                    };
                    let read = self
                        .machine
                        .borrow_mut()
                        .load_own_descriptor_slot(object, key, slot);
                    match read {
                        Ok(value) => HelperResult::normal(value),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::DefineOwnDescriptorSlot {
                    object,
                    key,
                    src,
                    slot,
                } => {
                    let slot = match descriptor_slot_from_selector(slot) {
                        Some(slot) => slot,
                        None => {
                            break 'result self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            });
                        }
                    };
                    let defined = self
                        .machine
                        .borrow_mut()
                        .define_own_descriptor_slot(object, key, src, slot);
                    match defined {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::WithHasBinding { object, key } => {
                    // Shared Object Environment Record HasBinding. Machine owns the
                    // getter path via call_value; scope the RefCell borrow to this
                    // single call so no outer borrow spans getter re-entry.
                    let found = self.machine.borrow_mut().with_has_binding(object, key);
                    match found {
                        Ok(found) => HelperResult::normal(Value::boolean(found)),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::GetSuper {
                    home,
                    receiver,
                    key,
                } => {
                    let key = match self.machine.borrow_mut().observable_property_key(key) {
                        Ok(key) => key,
                        Err(failure) => break 'result self.fail(failure),
                    };
                    let result = self.machine.borrow_mut().get_super(home, receiver, &key);
                    self.eval_result(result)
                }
                HelperCall::SetSuper {
                    home,
                    receiver,
                    key,
                    value,
                } => {
                    let key = match self.machine.borrow_mut().observable_property_key(key) {
                        Ok(key) => key,
                        Err(failure) => break 'result self.fail(failure),
                    };
                    let outcome = self
                        .machine
                        .borrow_mut()
                        .set_super(home, receiver, key, value);
                    match outcome {
                        Ok(SetOutcome::Done) => HelperResult::normal(Value::UNDEFINED),
                        Ok(SetOutcome::Setter(setter)) => {
                            match self.invoke_callee(setter, receiver, &[value], Value::UNDEFINED) {
                                InvokeOutcome::Value(_) => HelperResult::normal(Value::UNDEFINED),
                                other => self.outcome_result(other),
                            }
                        }
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::ImportAttributes {
                    specifier,
                    attributes,
                } => {
                    let result = self.machine.borrow_mut().import_namespace_with_attributes(
                        module,
                        ConstantId::new(specifier),
                        attributes,
                    );
                    self.eval_result(result)
                }
                HelperCall::ImportDynamicAttributes {
                    specifier,
                    attributes,
                } => {
                    let result = self
                        .machine
                        .borrow_mut()
                        .import_dynamic_expression_with_attributes(module, specifier, attributes);
                    self.eval_result(result)
                }
                HelperCall::CopyDataProperties {
                    target,
                    source,
                    excluded,
                } => {
                    let result = self
                        .machine
                        .borrow_mut()
                        .copy_data_properties(target, source, excluded);
                    match result {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::GetTemplateObject { cooked, raw } => {
                    let site = {
                        let activations = self.activations.borrow();
                        let Some(activation) = activations.last() else {
                            break 'result self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            });
                        };
                        (
                            activation.target.module.get(),
                            activation.target.function.get(),
                            frame.pc(),
                        )
                    };
                    let result = self
                        .machine
                        .borrow_mut()
                        .template_object_at(site, cooked, raw);
                    self.eval_result(result)
                }
                HelperCall::Call {
                    callee,
                    this_value,
                    arguments,
                } => {
                    let arguments = {
                        let read = self.machine.borrow().arguments_from_array(arguments);
                        match read {
                            Ok(arguments) => arguments,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let outcome =
                        self.invoke_callee(callee, this_value, &arguments, Value::UNDEFINED);
                    self.outcome_result(outcome)
                }
                HelperCall::Construct { callee, arguments } => {
                    let arguments = {
                        let read = self.machine.borrow().arguments_from_array(arguments);
                        match read {
                            Ok(arguments) => arguments,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    // Tag 12 has no explicit `new.target`: the callee is it.
                    self.construct(callee, callee, &arguments)
                }
                HelperCall::ConstructWithNewTarget {
                    callee,
                    new_target,
                    arguments,
                } => {
                    let arguments = {
                        let read = self.machine.borrow().arguments_from_array(arguments);
                        match read {
                            Ok(arguments) => arguments,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    self.construct(callee, new_target, &arguments)
                }
                HelperCall::Import { specifier } => self.import_namespace(module, specifier),
                HelperCall::LoadImportMeta => {
                    let result = self.machine.borrow_mut().load_import_meta(module);
                    match result {
                        Ok(value) => HelperResult::normal(value),
                        Err(kind) => self.fatal(kind),
                    }
                }
                HelperCall::ImportDynamic { specifier } => {
                    let result = self
                        .machine
                        .borrow_mut()
                        .import_dynamic_expression(module, specifier);
                    self.eval_result(result)
                }
                HelperCall::Truthy { value } => {
                    HelperResult::normal(Value::boolean(self.machine.borrow().truthy(value)))
                }
                HelperCall::ResumeValue => {
                    match self
                        .activations
                        .borrow()
                        .last()
                        .and_then(|a| a.pending_resume)
                    {
                        Some(GeneratorCompletion::Throw { value, origin }) => {
                            self.pending_throw.set(Some(PendingThrow { value, origin }));
                            HelperResult::throw(value)
                        }
                        Some(completion) => self.validated(completion.value()),
                        None => self.fatal(RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        }),
                    }
                }
                HelperCall::ResumeMode => {
                    match self
                        .activations
                        .borrow_mut()
                        .last_mut()
                        .and_then(|a| a.pending_resume.take())
                    {
                        Some(completion) => self.validated(Value::int32(completion.mode())),
                        None => self.fatal(RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        }),
                    }
                }
                HelperCall::LoadGlobal { name } => {
                    let resolved = self
                        .machine
                        .borrow_mut()
                        .load_global(module, ConstantId::new(name));
                    match resolved {
                        Ok(Some(value)) => self.validated(value),
                        Ok(None) => {
                            self.pending_throw.set(Some(PendingThrow {
                                value: Value::UNDEFINED,
                                origin: ThrowOrigin::ReferenceError {
                                    operation: "global is not defined",
                                },
                            }));
                            HelperResult::throw(Value::UNDEFINED)
                        }
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::StoreGlobal { name, value } => {
                    let sloppy = self.running_is_sloppy();
                    let stored = self.machine.borrow_mut().store_global(
                        module,
                        ConstantId::new(name),
                        value,
                        sloppy,
                    );
                    match stored {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::TypeOfGlobal { name } => {
                    let resolved = self
                        .machine
                        .borrow_mut()
                        .load_global(module, ConstantId::new(name));
                    let text = match resolved {
                        Ok(Some(value)) => EcmaString::encode(self.machine.borrow().type_of(value)),
                        Ok(None) => EcmaString::encode("undefined"),
                        Err(failure) => break 'result self.fail(failure),
                    };
                    self.allocated(HeapEntry::String(text))
                }
                HelperCall::LoadThis => self.load_this(),
                HelperCall::LoadArguments => self.load_arguments(),
                HelperCall::LoadNewTarget => HelperResult::normal(
                    self.activations
                        .borrow()
                        .last()
                        .map_or(Value::UNDEFINED, |activation| activation.new_target),
                ),
                HelperCall::ArrayPush { array, value } => {
                    let result = self.machine.borrow_mut().array_push(array, value);
                    match result {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::ArrayExtend { array, iterable } => {
                    let outcome = self.array_extend_active(array, iterable);
                    self.outcome_result(outcome)
                }
                HelperCall::ObjectSpread { target, source } => {
                    let result = self.machine.borrow_mut().object_spread(target, source);
                    match result {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::SetPrototype { object, prototype } => {
                    let result = self.machine.borrow_mut().set_prototype(object, prototype);
                    match result {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::CreatePrivateName { description } => {
                    let description = self.constant_text(module, description);
                    self.allocated(HeapEntry::PrivateName { description })
                }
                HelperCall::CreateRegExp { pattern, flags } => {
                    let pattern = self.constant_text(module, pattern);
                    let flags = self.constant_text(module, flags);
                    let prototype = self.machine.borrow().intrinsics.regexp_prototype();
                    let properties = crate::intrinsics::builtins::initial_regexp_properties();
                    self.allocated(HeapEntry::RegExp {
                        pattern,
                        flags,
                        properties,
                        prototype: Some(prototype),
                        extensible: true,
                    })
                }
                HelperCall::GetIterator { src, kind } => match iterator_kind_from_selector(kind) {
                    Some(kind) => self.outcome_result(self.get_iterator_active(src, kind)),
                    None => self.fatal(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    }),
                },
                HelperCall::IteratorNext {
                    iterator,
                    done_reg,
                    value_reg,
                } => match self.iterator_next_active(iterator) {
                    Ok((done, value)) => {
                        let wrote_done = frame.try_set_register(done_reg, Value::boolean(done));
                        let wrote_value = frame.try_set_register(value_reg, value);
                        if wrote_done && wrote_value {
                            HelperResult::normal(Value::UNDEFINED)
                        } else {
                            self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            })
                        }
                    }
                    Err(outcome) => self.outcome_result(outcome),
                },
                HelperCall::IteratorStep { iterator } => {
                    match self.iterator_step_active(iterator) {
                        Ok(result) => HelperResult::normal(result),
                        Err(outcome) => self.outcome_result(outcome),
                    }
                }
                HelperCall::IteratorResult {
                    result,
                    done_reg,
                    value_reg,
                } => match self.iterator_result_active(result) {
                    Ok((done, value)) => {
                        let wrote_done = frame.try_set_register(done_reg, Value::boolean(done));
                        let wrote_value = frame.try_set_register(value_reg, value);
                        if wrote_done && wrote_value {
                            HelperResult::normal(Value::UNDEFINED)
                        } else {
                            self.fatal(RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            })
                        }
                    }
                    Err(outcome) => self.outcome_result(outcome),
                },
                HelperCall::IteratorClose {
                    iterator,
                    mode,
                    called_reg,
                } => match self.close_iterator_active(frame, iterator, mode, called_reg) {
                    Ok(result) => HelperResult::normal(result),
                    Err(outcome) => self.outcome_result(outcome),
                },
                HelperCall::RequireCloseResult { result, called } => {
                    if called == Value::TRUE && !self.machine.borrow().is_object(result) {
                        self.fail(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "iterator.return() returned a non-object",
                        }))
                    } else {
                        HelperResult::normal(Value::UNDEFINED)
                    }
                }
                HelperCall::DisposeCapture {
                    src,
                    hint,
                    kind_reg,
                } => match self.dispose_capture_active(src, hint) {
                    Ok((method, kind)) if frame.try_set_register(kind_reg, Value::int32(kind)) => {
                        HelperResult::normal(method)
                    }
                    Ok(_) => self.fatal(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    }),
                    Err(outcome) => self.outcome_result(outcome),
                },
                HelperCall::SuppressError { error, suppressed } => {
                    let result = self
                        .machine
                        .borrow_mut()
                        .make_suppressed_error(error, suppressed);
                    match result {
                        Ok(value) => self.validated(value),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::Export { .. } => {
                    self.fail(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "export outside an engine-owned module registry",
                    }))
                }
                HelperCall::ConsumeFuel { .. } => HelperResult::normal(Value::UNDEFINED),
            }
        };
        self.finish_helper_result(frame, result)
    }
}

fn is_inline_instruction(instruction: Instruction) -> bool {
    match instruction {
        Instruction::Move { .. }
        | Instruction::Jump { .. }
        | Instruction::JumpIfTrue { .. }
        | Instruction::JumpIfFalse { .. }
        | Instruction::Return { .. }
        | Instruction::Halt
        | Instruction::Throw { .. }
        | Instruction::Suspend { .. }
        | Instruction::Await { .. } => true,
        Instruction::LoadConst { .. }
        | Instruction::Unary { .. }
        | Instruction::Binary { .. }
        | Instruction::CreateObject { .. }
        | Instruction::CreateArray { .. }
        | Instruction::CreateCell { .. }
        | Instruction::CreateClosure { .. }
        | Instruction::GetProperty { .. }
        | Instruction::SetProperty { .. }
        | Instruction::DeleteProperty { .. }
        | Instruction::DefineAccessor { .. }
        | Instruction::DefineDataProperty { .. }
        | Instruction::LoadOwnDescriptorSlot { .. }
        | Instruction::DefineOwnDescriptorSlot { .. }
        | Instruction::WithHasBinding { .. }
        | Instruction::Call { .. }
        | Instruction::Construct { .. }
        | Instruction::ConstructWithNewTarget { .. }
        | Instruction::LoadGlobal { .. }
        | Instruction::StoreGlobal { .. }
        | Instruction::TypeOfGlobal { .. }
        | Instruction::LoadThis { .. }
        | Instruction::LoadArguments { .. }
        | Instruction::LoadNewTarget { .. }
        | Instruction::LoadImportMeta { .. }
        | Instruction::ArrayPush { .. }
        | Instruction::ArrayExtend { .. }
        | Instruction::ObjectSpread { .. }
        | Instruction::SetPrototype { .. }
        | Instruction::CreatePrivateName { .. }
        | Instruction::CreateRegExp { .. }
        | Instruction::GetIterator { .. }
        | Instruction::IteratorNext { .. }
        | Instruction::IteratorStep { .. }
        | Instruction::IteratorResult { .. }
        | Instruction::IteratorClose { .. }
        | Instruction::RequireCloseResult { .. }
        | Instruction::DisposeCapture { .. }
        | Instruction::SuppressError { .. }
        | Instruction::Import { .. }
        | Instruction::ToObject { .. }
        | Instruction::ImportDynamic { .. }
        | Instruction::GetSuper { .. }
        | Instruction::SetSuper { .. }
        | Instruction::ImportAttributes { .. }
        | Instruction::ImportDynamicAttributes { .. }
        | Instruction::CopyDataProperties { .. }
        | Instruction::GetTemplateObject { .. }
        | Instruction::Export { .. } => false,
    }
}

/// Runs a linked program's entry through the native engine and returns its
/// observable outcome. This is the runtime side of the AOT `main`: `entries` is
/// a compiled [`NativeEntryTable`] (an AOT `LinkedProgram` or a JIT program),
/// and the returned [`ExecutionOutcome`] carries buffered stdout and the exit
/// code. It is always available and never feature-gated, so a downstream host
/// crate can link against it without enabling the runtime's `aot-main` feature.
///
/// Returns [`NativeError::ProgramMismatch`] before constructing the engine when
/// `entries` was not compiled from this program's exact canonical encoding.
pub fn run_linked_program<H: Host>(
    program: &Program<Verified>,
    entries: &dyn NativeEntryTable,
    host: &mut H,
    limits: &Limits,
) -> Result<ExecutionOutcome, NativeError> {
    run_linked_program_with_cancel(
        program,
        entries,
        host,
        limits,
        bamts_cancel::CancellationToken::new(),
    )
}

/// Runs a linked program's entry through the native engine with a
/// caller-supplied [`bamts_cancel::CancellationToken`].
///
/// The token is checked before engine construction, immediately before and
/// after the linked entry invocation, and at every fuel, microtask, timer, and
/// quiescence checkpoint inside the shared [`Machine`]. Triggering it aborts
/// execution with [`NativeError::Cancelled`].
///
/// Returns [`NativeError::ProgramMismatch`] before constructing the engine when
/// `entries` was not compiled from this program's exact canonical encoding.
pub fn run_linked_program_with_cancel<H: Host>(
    program: &Program<Verified>,
    entries: &dyn NativeEntryTable,
    host: &mut H,
    limits: &Limits,
    cancel: bamts_cancel::CancellationToken,
) -> Result<ExecutionOutcome, NativeError> {
    if cancel.is_cancelled() {
        return Err(NativeError::Cancelled);
    }
    let program_bytes = program.encode();
    if program_bytes != entries.program_bytes() {
        return Err(NativeError::ProgramMismatch);
    }
    let mut engine = NativeEngine::build(
        program,
        entries,
        host,
        limits.clone(),
        Backend::Linked,
        cancel,
    );
    engine.run_linked()
}

/// Runs a linked program under a live [`WarmupPolicy`], returning both the
/// ordinary execution outcome and a per-unit [`TieredRunReport`].
///
/// Same `ProgramMismatch` / cancel checks as
/// [`run_linked_program_with_cancel`]. Existing linked callers are unchanged:
/// only this entry constructs the engine with a tiering table.
pub fn run_linked_program_tiered<H: Host>(
    program: &Program<Verified>,
    entries: &dyn NativeEntryTable,
    host: &mut H,
    limits: &Limits,
    policy: WarmupPolicy,
    cancel: bamts_cancel::CancellationToken,
) -> Result<(Result<ExecutionOutcome, NativeError>, TieredRunReport), NativeError> {
    if cancel.is_cancelled() {
        return Err(NativeError::Cancelled);
    }
    let program_bytes = program.encode();
    if program_bytes != entries.program_bytes() {
        return Err(NativeError::ProgramMismatch);
    }
    let table = match TieringTable::from_program(program, policy) {
        Ok(table) => table,
        Err(_) => {
            // Policy errors are caller bugs; NativeError's variant set is
            // closed (corpus matching), so surface them as an invalid value.
            return Err(NativeError::Runtime(RuntimeError {
                kind: RuntimeErrorKind::InvalidValue {
                    value: Value::UNDEFINED,
                },
                function: FunctionId::new(0),
                pc: Pc::new(0),
                source: crate::RuntimeSource {
                    function_name: None,
                    instruction: Instruction::Halt,
                },
            }));
        }
    };
    let mut engine = NativeEngine::build_with_tiering(
        program,
        entries,
        host,
        limits.clone(),
        Backend::Linked,
        cancel,
        Some(table),
    );
    let outcome = engine.run_linked();
    if matches!(outcome, Err(NativeError::Cancelled)) {
        engine.cancel_tiering();
    }
    let report = engine
        .tiering
        .as_ref()
        .expect("tiered entry installs a table")
        .borrow()
        .report();
    Ok((outcome, report))
}

#[cfg(test)]
mod tests {
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
        EvalFailure, GeneratorState, HeapEntry, Host, Limits, Machine, Property, PropertyKey,
        PropertyMap, RuntimeError, RuntimeErrorKind, ThrowOrigin,
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

    #[test]
    fn first_static_dependency_tla_rejection_skips_the_native_graph() {
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
        let program = linked(vec![rejecting, pending, root], 2);

        let mut interpreter_host = SilentHost;
        let mut machine = Machine::new(&program, &mut interpreter_host, Limits::default());
        let error = machine
            .evaluate()
            .expect_err("interpreter propagates the first dependency rejection");
        assert!(matches!(
            error.kind,
            RuntimeErrorKind::UncaughtThrow {
                value,
                ..
            } if value == Value::int32(9)
        ));
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
            let (call, dst) = engine.lower(instruction, &frame);
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
        assert_eq!(HELPER_COUNT, 53);
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
        let created = PropertyKey::Named(EcmaString::encode("created"));
        let data = PropertyKey::Named(EcmaString::encode("data"));
        let accessor = PropertyKey::Named(EcmaString::encode("accessor"));

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
        native_function(&mut machine.heap, id, name, 0)
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
            machine
                .define_descriptor(
                    list,
                    PropertyKey::Named(EcmaString::encode("0")),
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
}
