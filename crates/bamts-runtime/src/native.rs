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
    ConstantId, DisposeHint, EcmaString, FunctionId, Instruction, IntrinsicErrorKind, Module,
    ModuleId, Pc, Program, Verified,
};
pub use bamts_native::AbiError;
pub use bamts_native::tiering::WarmupPolicy;
use bamts_native::tiering::{DeoptReason, SiteProfile, Tier, TieringState, deopt_reason};
use bamts_native::{
    Completion, CompletionTag, Decoded, HelperCall, HelperResult, NativeEntryTable, NativeFrame,
    NativeOps, ShadowFrame, Value, with_native_ops_ref,
};

use crate::intrinsics::BuiltinOutcome;
use crate::vm::generator_async::GeneratorCompletion;
use crate::{
    ArrayElementKind, CalleeKind, EvalFailure, Execution, ExecutionOutcome, GeneratorResume,
    GeneratorStart, GetOutcome, HeapEntry, Host, IteratorNextPrepared, Limits, Machine, Property,
    PropertyMap, RuntimeError, RuntimeErrorKind, SetOutcome, SuspendedActivation, ThrowOrigin,
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

#[derive(Clone, Debug)]
struct UnitTier {
    state: TieringState,
    osr_entries: u32,
    profile: Vec<SiteProfile>,
}

impl TieringTable {
    fn from_program(
        program: &Program<Verified>,
        policy: WarmupPolicy,
    ) -> Result<Self, bamts_native::tiering::TieringError> {
        let mut units = std::collections::BTreeMap::new();
        for (module_index, module) in program.modules().iter().enumerate() {
            let module_id = ModuleId::new(module_index as u32);
            for (function_index, function) in module.code().functions().iter().enumerate() {
                let function_id = FunctionId::new(function_index as u32);
                units.insert(
                    (module_id, function_id),
                    UnitTier {
                        state: TieringState::new(policy)?,
                        osr_entries: 0,
                        profile: vec![SiteProfile::default(); function.code().len()],
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

    /// Appends the root set of the current native activation to `roots`. The
    /// registers are driver-stack locals, so they must be copied into the Machine
    /// before GC.
    fn extend_with_native_roots(&self, registers: &[Value], roots: &mut Vec<Value>) {
        let activations = self.activations.borrow();
        let activation = activations
            .last()
            .expect("a native root snapshot requires an active activation");
        roots.reserve(
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
    }

    fn push_native_roots(&self, registers: &[Value]) {
        let depth = self.activations.borrow().len() - 1;
        let mut roots = Vec::new();
        self.extend_with_native_roots(registers, &mut roots);
        self.machine.borrow_mut().push_native_roots(depth, &roots);
    }

    /// Rebuilds the activation's roots inside the vector the Machine already
    /// holds, so a helper call allocates nothing for them.
    fn refresh_native_roots(&self, frame: &NativeFrame<'_>) {
        let depth = self.activations.borrow().len() - 1;
        self.machine
            .borrow_mut()
            .refresh_native_roots_with(depth, |roots| {
                self.extend_with_native_roots(frame.registers(), roots);
            });
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
                    let (call, dst) = self.lower(other, &frame, pc);
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
        pc: usize,
    ) -> (HelperCall, Option<u32>) {
        let register = |r: bamts_bytecode::Register| frame.register(r.get());
        let site = || u32::try_from(pc).expect("instruction index fits u32");
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
                    site: site(),
                },
                Some(dst.get()),
            ),
            Instruction::SetProperty { object, key, value } => (
                HelperCall::SetProperty {
                    object: register(object),
                    key: register(key),
                    value: register(value),
                    site: site(),
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
            Instruction::RequireGlobalBinding { name } => {
                (HelperCall::RequireGlobalBinding { name: name.get() }, None)
            }
            Instruction::ThrowIntrinsicError { kind, message } => (
                HelperCall::ThrowIntrinsicError {
                    kind: kind.selector(),
                    message: message.get(),
                },
                None,
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
    /// A call past the guest stack throws in place of the activation.
    fn invoke_runtime(
        &self,
        target: crate::RuntimeFunction,
        captures: &[Value],
        context: Option<Value>,
        this: Value,
        new_target: Value,
        args: &[Value],
    ) -> InvokeOutcome {
        if self.machine.borrow().stack_overflows() {
            return InvokeOutcome::Threw(Value::UNDEFINED, crate::STACK_OVERFLOW);
        }
        let index = target.function.get() as usize;
        let handle = self.code_ref(target.module);
        let flags = handle.code(target.module).functions()[index].flags();
        if flags.is_async || flags.is_generator {
            return self.start_suspendable(target, captures, context, this, new_target, args);
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

    /// The start of a generator or an async function. It stays out of the frame of
    /// [`Self::invoke_runtime`], which a recursion has on the stack once for each
    /// level.
    #[inline(never)]
    fn start_suspendable(
        &self,
        target: crate::RuntimeFunction,
        captures: &[Value],
        context: Option<Value>,
        this: Value,
        new_target: Value,
        args: &[Value],
    ) -> InvokeOutcome {
        let handle = self.code_ref(target.module);
        let flags = handle.code(target.module).functions()[target.function.get() as usize].flags();
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
        match outcome {
            Ok(promise) => InvokeOutcome::Value(promise),
            Err(failure) => self.failure_outcome(failure),
        }
    }

    fn resume_generator(&self, generator: Value, completion: GeneratorCompletion) -> InvokeOutcome {
        if self.machine.borrow().stack_overflows() {
            return InvokeOutcome::Threw(Value::UNDEFINED, crate::STACK_OVERFLOW);
        }
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
        let key = crate::PropertyKey::Named(self.machine.borrow_mut().intern_str(name));
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
        let key = match self.machine.borrow_mut().property_key_from_value(symbol) {
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
        let key = match self.machine.borrow_mut().property_key_from_value(symbol) {
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
        let key = match self.machine.borrow_mut().property_key_from_value(symbol) {
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
            let key = match self.machine.borrow_mut().property_key_from_value(symbol) {
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
        if let Some(transition) = unit.state.observe_invocation()
            && transition.to == Tier::Optimized
            && !self
                .entries
                .promote(self.program, module.get(), function.get(), &unit.profile)
        {
            unit.state.decline_optimization();
        }
        unit.state.is_pinned() || matches!(unit.state.tier(), Tier::Interpreter)
    }

    /// Ors the kinds of `operands` into the profile of instruction `pc` of the
    /// running unit.
    fn observe_operands(&self, pc: u32, operands: &[Value]) {
        let Some(table) = &self.tiering else {
            return;
        };
        let target = self.running_function();
        let mut table = table.borrow_mut();
        let Some(unit) = table.get_mut(target.module, target.function) else {
            return;
        };
        if let Some(site) = unit.profile.get_mut(pc as usize) {
            *site = operands.iter().fold(*site, |profile, value| {
                profile.observe(SiteProfile::of(*value))
            });
        }
    }

    /// After a speculation trap, records what the failed site saw so the next
    /// optimized compile of the unit does not repeat the guess.
    fn record_speculation_failure(
        &self,
        target: crate::RuntimeFunction,
        instruction: Instruction,
        pc: usize,
        registers: &[Value],
    ) {
        let word = |register: bamts_bytecode::Register| {
            registers
                .get(register.get() as usize)
                .copied()
                .unwrap_or(Value::UNDEFINED)
        };
        let observed = match instruction {
            Instruction::Binary { left, right, .. } => {
                SiteProfile::of(word(left)) | SiteProfile::of(word(right))
            }
            Instruction::Unary { operand, .. } => SiteProfile::of(word(operand)),
            Instruction::GetProperty { .. } => SiteProfile::OTHER,
            _ => return,
        };
        let Some(table) = &self.tiering else {
            return;
        };
        let mut table = table.borrow_mut();
        if let Some(site) = table
            .get_mut(target.module, target.function)
            .and_then(|unit| unit.profile.get_mut(pc))
        {
            *site = site.observe(observed);
        }
    }

    /// Enters the compiled entry of a unit: the newest optimized artifact when
    /// the unit holds that tier, the baseline artifact otherwise.
    fn invoke_entry(
        &self,
        module: ModuleId,
        function: FunctionId,
        shadow: &mut ShadowFrame,
        out: &mut Completion,
    ) -> Result<CompletionTag, AbiError> {
        let optimized = self.tiering.as_ref().is_some_and(|table| {
            table
                .borrow_mut()
                .get_mut(module, function)
                .is_some_and(|unit| matches!(unit.state.tier(), Tier::Optimized))
        });
        if optimized {
            self.entries
                .invoke_optimized(module.get(), function.get(), shadow, out)
        } else {
            self.entries
                .invoke(module.get(), function.get(), shadow, out)
        }
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
        let fault_pc = if shadow.bytecode_pc & 0x8000_0000 != 0 {
            osr_pc as usize
        } else {
            shadow.bytecode_pc as usize
        };
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
            let tag = if self.tiering_enabled() {
                with_native_ops_ref(self, || {
                    self.invoke_entry(target.module, target.function, &mut shadow, &mut out)
                })
            } else {
                self.invoke_entry(target.module, target.function, &mut shadow, &mut out)
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
                        if matches!(reason, DeoptReason::Speculation) {
                            let handle = self.code_ref(target.module);
                            let code = handle.code(target.module);
                            if let Some(instruction) = code.functions()[index].code().get(fault_pc)
                            {
                                self.record_speculation_failure(
                                    target,
                                    *instruction,
                                    fault_pc,
                                    &registers,
                                );
                            }
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
        let sloppy = self.running_is_sloppy();
        let properties = self.machine.borrow_mut().arguments_properties(sloppy);
        let allocated = self.machine.borrow_mut().allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&args),
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
        let (tag, out, fault_pc) = {
            let mut shadow =
                ShadowFrame::new(std::ptr::null_mut(), 0, module.get(), handles, length);
            let mut out = Completion::new(Value::UNDEFINED);
            let tag = with_native_ops_ref(&*self, || {
                self.invoke_entry(module, function_id, &mut shadow, &mut out)
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
        let result = match call {
            HelperCall::Call {
                callee,
                this_value,
                arguments,
            } => self.call_helper(callee, this_value, arguments),
            // Tag 12 has no explicit `new.target`: the callee is it.
            HelperCall::Construct { callee, arguments } => {
                self.construct_helper(callee, callee, arguments)
            }
            HelperCall::ConstructWithNewTarget {
                callee,
                new_target,
                arguments,
            } => self.construct_helper(callee, new_target, arguments),
            call => self.helper(frame, call),
        };
        self.finish_helper_result(frame, result)
    }
}

impl<'m, 'h, H: Host> NativeEngine<'m, 'h, H> {
    /// A call from native code. A recursion has this frame on the stack once for
    /// each level, so the call stays out of [`Self::helper`], whose frame holds the
    /// locals of every other helper.
    fn call_helper(&self, callee: Value, this_value: Value, arguments: Value) -> HelperResult {
        let read = self.machine.borrow().arguments_from_array(arguments);
        let arguments = match read {
            Ok(arguments) => arguments,
            Err(failure) => return self.fail(failure),
        };
        let outcome = self.invoke_callee(callee, this_value, &arguments, Value::UNDEFINED);
        self.outcome_result(outcome)
    }

    /// A construction from native code, kept out of [`Self::helper`] as a call is.
    fn construct_helper(&self, callee: Value, new_target: Value, arguments: Value) -> HelperResult {
        let read = self.machine.borrow().arguments_from_array(arguments);
        let arguments = match read {
            Ok(arguments) => arguments,
            Err(failure) => return self.fail(failure),
        };
        self.construct(callee, new_target, &arguments)
    }

    /// Every helper except a call and a construction.
    #[inline(never)]
    fn helper(&self, frame: &mut NativeFrame<'_>, call: HelperCall) -> HelperResult {
        let module = ModuleId::new(frame.module_id());
        'result: {
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
                        self.observe_operands(frame.pc(), &[operand]);
                        let result = self.machine.borrow_mut().eval_unary(op, operand);
                        self.eval_result(result)
                    }
                    None => self.fatal(RuntimeErrorKind::InvalidValue {
                        value: Value::UNDEFINED,
                    }),
                },
                HelperCall::Binary { op, left, right } => match binary_from_selector(op) {
                    Some(op) => {
                        self.observe_operands(frame.pc(), &[left, right]);
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
                        kind: ArrayElementKind::for_elements(&[]),
                        elements: Vec::new(),
                        properties: PropertyMap::default(),
                        prototype: Some(prototype),
                        extensible: true,
                        length_writable: true,
                    })
                }
                HelperCall::CreateCell => {
                    let prototype = self.machine.borrow().intrinsics.array_prototype;
                    let elements = vec![Value::UNINITIALIZED];
                    self.allocated(HeapEntry::Array {
                        kind: ArrayElementKind::for_elements(&elements),
                        elements,
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
                HelperCall::GetProperty { object, key, site } => {
                    let key_value = key;
                    let key = {
                        let coerced = self.machine.borrow_mut().computed_property_key(object, key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let target = self.running_function();
                    let cached = self.machine.borrow_mut().property_site_hit_get(
                        target.module,
                        target.function,
                        site as usize,
                        object,
                        &key,
                    );
                    if let Some(value) = cached {
                        self.observe_operands(site, &[key_value, value]);
                        break 'result self.validated(value);
                    }
                    let outcome = self.machine.borrow_mut().internal_get(object, &key, object);
                    if outcome.is_ok() {
                        self.machine.borrow_mut().property_site_record_get(
                            target.module,
                            target.function,
                            site as usize,
                            object,
                            &key,
                        );
                    }
                    match outcome {
                        Ok(value) => {
                            self.observe_operands(site, &[key_value, value]);
                            self.validated(value)
                        }
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::SetProperty {
                    object,
                    key,
                    value,
                    site,
                } => {
                    let key = {
                        let coerced = self.machine.borrow_mut().computed_property_key(object, key);
                        match coerced {
                            Ok(key) => key,
                            Err(failure) => break 'result self.fail(failure),
                        }
                    };
                    let target = self.running_function();
                    let cached = self.machine.borrow_mut().property_site_hit_set(
                        target.module,
                        target.function,
                        site as usize,
                        object,
                        &key,
                        value,
                    );
                    if cached.is_some() {
                        break 'result HelperResult::normal(Value::UNDEFINED);
                    }
                    let outcome =
                        self.machine
                            .borrow_mut()
                            .internal_set(object, key.clone(), value, object);
                    if matches!(outcome, Ok(true)) {
                        self.machine.borrow_mut().property_site_record_set(
                            target.module,
                            target.function,
                            site as usize,
                            object,
                            &key,
                        );
                    }
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
                HelperCall::RequireGlobalBinding { name } => {
                    let required = self
                        .machine
                        .borrow_mut()
                        .require_global_binding(module, ConstantId::new(name));
                    match required {
                        Ok(()) => HelperResult::normal(Value::UNDEFINED),
                        Err(failure) => self.fail(failure),
                    }
                }
                HelperCall::ThrowIntrinsicError { kind, message } => {
                    let Some(kind) = IntrinsicErrorKind::from_selector(kind) else {
                        break 'result self.fatal(RuntimeErrorKind::InvalidValue {
                            value: Value::UNDEFINED,
                        });
                    };
                    let failure = self.machine.borrow_mut().throw_intrinsic_error(
                        module,
                        kind,
                        ConstantId::new(message),
                    );
                    self.fail(failure)
                }
                HelperCall::Call { .. }
                | HelperCall::Construct { .. }
                | HelperCall::ConstructWithNewTarget { .. } => {
                    unreachable!("`dispatch` runs a call outside this frame")
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
                    let properties = {
                        let mut borrowed = self.machine.borrow_mut();
                        let machine: &mut Machine<'_, H> = &mut borrowed;
                        crate::intrinsics::builtins::initial_regexp_properties(
                            &mut machine.atoms,
                            &mut machine.shapes,
                        )
                    };
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
                HelperCall::ArrayGetNumber { array, index } => {
                    let element = self.machine.borrow().array_element_number(array, index);
                    match element {
                        Some(value) => HelperResult::normal(value),
                        None => HelperResult {
                            tag: CompletionTag::FatalTrap,
                            value: Value::int32(bamts_native::TRAP_SPECULATION),
                        },
                    }
                }
                HelperCall::ConsumeFuel { .. } => HelperResult::normal(Value::UNDEFINED),
            }
        }
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
        | Instruction::RequireGlobalBinding { .. }
        | Instruction::ThrowIntrinsicError { .. }
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
mod tests;
