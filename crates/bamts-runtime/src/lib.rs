//! Deterministic register interpreter for verified production BamTS bytecode.
//!
//! Persisted constants never carry runtime identity. This interpreter therefore
//! owns a slot heap for strings, bigints, objects, arrays, closures, private
//! names, regular expressions, and iterators, and exposes only
//! `bamts_native::Value` words at host boundaries. Bytecode heap slots use
//! segment 1; other segments remain host-owned.
//!
//! The 36-op dynamic-computation ISA is executed locally: register-keyed
//! property access (with data properties, accessor descriptors, and private-name
//! identity), prototype chains, closures with explicit capture environments,
//! arguments arrays, `this`/`arguments`/`new.target`, globals, arrays with
//! spread, object spread, iterators (sync/async/keys) with the two-write
//! `IteratorNext`, and generator/async `Suspend`-resume. The [`Host`] trait owns
//! only *external* module and builtin operations (foreign calls/constructs,
//! foreign property access, `import`, `export`, and the suspension driver);
//! internal objects, arrays, functions, closures, prototypes, and private names
//! never leave the interpreter.

#![forbid(unsafe_code)]

use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::error::Error;
use std::fmt;
use std::num::NonZeroU32;
use std::sync::Arc;

use crate::vm::explicit_resource::DisposalStackState;
use crate::vm::generator_async::GeneratorCompletion;
use bamts_bytecode::{
    AccessorKind, BinaryOp, BindingId, BindingKind, Constant, ConstantId, DisposeHint, EcmaString,
    EcmaStringBuilder, EdgeId, EdgeTarget, Function, FunctionId, Instruction, IntrinsicErrorKind,
    IteratorCloseMode, IteratorKind, Module, ModuleId, Pc, Program, ProgramModule, Register,
    ResolvedExport, UnaryOp, Verified, format_number,
};
pub use bamts_cancel::CancellationToken;
use bamts_native::{Decoded, SlotId, Value};
use heap::Heap;
use intrinsics::builtins::typedarray::{self, ElementKind, LengthSlot};

mod external_modules;
mod gc;
mod heap;
mod host_objects;
pub mod intl;
mod intrinsics;
mod native;
#[cfg(test)]
mod proxy_reflect_integration;
mod shape;
mod temporal;
mod vm;
pub(crate) use intrinsics::builtins;
pub(crate) use shape::{FunctionSites, SHAPED_CAPACITY, ShapeId, ShapeTable, Which};

pub use native::{
    NativeEngine, NativeError, TieredRunReport, UnitTieringSummary, WarmupPolicy,
    run_linked_program, run_linked_program_tiered, run_linked_program_with_cancel,
};

/// Callback results a builtin keeps rooted, for the locals it still holds.
const RECENT_CALLBACK_RESULTS: usize = 32;
const RUNTIME_HEAP_SEGMENT: u16 = 1;

/// The observable result of a terminated execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionOutcome {
    /// Reserved for output produced by host builtins.
    pub stdout: Vec<u8>,
    /// `0` for normal bytecode termination.
    pub exit_code: i32,
}

/// A terminated execution and the entry activation's observable state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Execution {
    pub outcome: ExecutionOutcome,
    /// The explicit entry return value, or `undefined` for `Halt`.
    pub value: Value,
    /// Backward-compatible name for the final returned value.
    pub link: Value,
    pub entry_registers: Vec<Value>,
}

/// Deterministic execution and allocation ceilings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Limits {
    pub fuel: u64,
    /// The ceiling of the host on activations. Past it the run ends.
    pub max_call_depth: usize,
    /// The activations of the guest stack. A call past it throws `RangeError`, which
    /// the program can catch, as V8 does when its stack is full.
    pub max_stack_depth: usize,
    /// The native stack that the guest stack can use, from the position where the
    /// machine was built. A call past it throws the same `RangeError`. Build and run
    /// the machine on one thread when this is less than `usize::MAX`.
    pub max_stack_bytes: usize,
    pub max_total_registers: usize,
    /// Ceiling on the length of a single call's arguments array.
    pub max_argument_count: u32,
    pub max_heap_slots: usize,
    pub max_heap_bytes: usize,
    /// Ceiling on engine-owned module binding cells.
    pub max_module_cells: usize,
    /// Ceiling on host-compiled scripts retained by one machine.
    pub max_dynamic_modules: usize,
    /// Ceiling on queued microtasks.
    pub max_microtasks: usize,
    /// Ceiling on live timers armed at once.
    pub max_timers: usize,
    /// This agent's `[[CanBlock]]`: whether `Atomics.wait` may suspend it.
    pub agent_can_suspend: bool,
    /// Test hook: every allocation requests a collection, which runs at the next
    /// safe point. Defaults to false.
    pub collect_every_allocation: bool,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            fuel: 1_000_000,
            max_call_depth: 64,
            max_stack_depth: usize::MAX,
            max_stack_bytes: usize::MAX,
            max_total_registers: 1 << 20,
            max_argument_count: 1 << 16,
            max_heap_slots: 1 << 20,
            max_heap_bytes: 64 << 20,
            max_module_cells: 1 << 20,
            max_dynamic_modules: 1 << 10,
            max_microtasks: 1 << 20,
            max_timers: 1 << 20,
            agent_can_suspend: true,
            collect_every_allocation: false,
        }
    }
}

impl Limits {
    /// The native stack of the thread that runs a compiled program. The system
    /// reserves it as address space and commits only the pages that the program uses.
    pub const PROGRAM_STACK: usize = 256 << 20;

    /// The ceilings of a compiled program. The defaults hold a test, an embedded script
    /// or an API request to a small budget. A compiled program runs until it ends, and
    /// its heap stops near the default of Node.
    /// 10,000 calls use less than half of it, and a call through a builtin callback,
    /// which takes more, stops at [`Self::max_stack_bytes`]. The host ceiling stays
    /// far past the guest stack, and the registers hold 10,000 large frames.
    #[must_use]
    pub fn program() -> Self {
        Self {
            fuel: u64::MAX,
            max_call_depth: 1 << 20,
            max_stack_depth: 10_000,
            max_stack_bytes: Self::PROGRAM_STACK - (16 << 20),
            max_total_registers: 1 << 24,
            max_heap_slots: 1 << 30,
            max_heap_bytes: 1 << 32,
            ..Self::default()
        }
    }
}

/// What a call throws when it passes the guest stack, in the words of V8.
pub(crate) const STACK_OVERFLOW: ThrowOrigin = ThrowOrigin::RangeError {
    operation: "Maximum call stack size exceeded",
};

/// How far past [`Limits::max_stack_bytes`] the native stack goes before the run
/// ends. It covers the frames between the check of a call and the next check of
/// the host ceiling.
const STACK_SLACK: usize = 1 << 20;

/// The address of a local in the frame of the caller. The stack grows down on
/// every supported target, so a deeper call has a smaller position.
fn stack_position() -> usize {
    let marker = 0_u8;
    std::ptr::from_ref(&marker).addr()
}

/// The exact source of one classic script. Source and resource name preserve
/// UTF-16 code units verbatim, including unpaired surrogates.
pub struct ScriptSource<'a> {
    pub source: &'a [u16],
    pub name: &'a [u16],
}

/// Why a host compiler refused a classic script.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptCompileError {
    IllFormedSource {
        unit_offset: usize,
    },
    Syntax {
        message: String,
        line: u32,
        column: u32,
    },
    Unsupported {
        message: String,
        line: u32,
        column: u32,
    },
    Capacity {
        message: String,
    },
    Internal {
        message: String,
    },
}

/// A host capability for compiling a classic script without observing machine state.
pub trait CompileProvider {
    fn compile_script(
        &mut self,
        source: ScriptSource<'_>,
    ) -> Result<Arc<Program<Verified>>, ScriptCompileError>;
}

/// External capabilities available to the JavaScript runtime.
///
/// Runtime values never cross this boundary. The engine owns all JavaScript
/// objects and value semantics; hosts provide byte sinks and process services.
pub trait Host {
    fn write_stdout(&mut self, _bytes: &[u8]) {}

    fn write_stderr(&mut self, _bytes: &[u8]) {}

    fn exit_code(&self) -> Option<i32> {
        None
    }

    fn set_exit_code(&mut self, _exit_code: i32) {}

    fn argv(&self) -> &[String] {
        &[]
    }

    fn env(&self, _name: &str) -> Option<&str> {
        None
    }

    fn set_env(&mut self, _name: &str, _value: &str) {}

    fn delete_env(&mut self, _name: &str) -> bool {
        false
    }

    /// Supplies the URL exposed by this module's stable `import.meta` object.
    /// The runtime calls this at most once per instantiated module.
    fn import_meta_url(&mut self, module_name: &EcmaString) -> EcmaString {
        module_name.clone()
    }

    fn now_ms(&mut self) -> u64 {
        0
    }

    fn monotonic_ns(&mut self) -> u64 {
        0
    }

    fn random(&mut self) -> f64 {
        0.0
    }

    fn hash(&mut self, _algorithm: &str, _data: &[u8]) -> Option<Vec<u8>> {
        None
    }

    /// This host's script compiler, or `None` when it provides none.
    ///
    /// Presence MUST remain stable for the lifetime of one machine because it
    /// determines whether `node:vm` is installed during construction. When
    /// present, `runInNewContext` provides a fresh `globalThis` per call but
    /// still shares this machine's intrinsic objects and prototype graph; guest
    /// code can mutate shared objects such as `Object.prototype`.
    fn script_compiler(&mut self) -> Option<&mut (dyn CompileProvider + 'static)> {
        None
    }

    /// This host's timer scheduler, or `None` when it provides none.
    ///
    /// Presence MUST remain stable for the lifetime of one machine because it
    /// determines whether `setTimeout`/`clearTimeout` and
    /// `setInterval`/`clearInterval` are installed during construction.
    fn timers(&mut self) -> Option<&mut (dyn TimerProvider + 'static)> {
        None
    }
}

/// A single expired timer reported by a [`TimerProvider`].
///
/// `id` echoes the machine-owned JavaScript identifier passed to
/// [`TimerProvider::schedule`]; `deadline_ms` is the provider's monotonic
/// absolute-millisecond deadline used as the promotion watermark.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TimerWakeup {
    pub id: u64,
    pub deadline_ms: u64,
}

/// An owned failure message produced by a [`TimerProvider`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TimerError {
    message: String,
}

impl TimerError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for TimerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for TimerError {}

/// A host capability that schedules real time without observing machine state.
///
/// The provider owns only opaque `u64` identifiers and monotonic millisecond
/// deadlines; it never stores a JavaScript `Value`. The machine owns visible
/// ordering and every callback identity.
pub trait TimerProvider {
    /// Arms a timer for `id` after at least `delay_ms` milliseconds, returning
    /// the provider-monotonic absolute-millisecond deadline.
    fn schedule(&mut self, id: u64, delay_ms: u32) -> Result<u64, TimerError>;

    /// Cancels the armed timer for `id`, returning whether one was removed.
    fn cancel(&mut self, id: u64) -> Result<bool, TimerError>;

    /// Drains every currently expired timer into `output` without blocking.
    fn poll_expired(&mut self, output: &mut Vec<TimerWakeup>) -> Result<(), TimerError>;

    /// Blocks until the next timer expires, returns `None` when none pend, or
    /// returns `None` early if `cancel` is triggered.
    fn wait_expired(
        &mut self,
        cancel: &CancellationToken,
    ) -> Result<Option<TimerWakeup>, TimerError>;

    /// Reports whether the provider has any armed timer.
    fn has_pending(&self) -> bool;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ThrowOrigin {
    Bytecode,
    TypeError { operation: &'static str },
    RangeError { operation: &'static str },
    ReferenceError { operation: &'static str },
    UriError { operation: &'static str },
}

/// Source metadata attached to every machine failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeSource {
    pub function_name: Option<EcmaString>,
    pub instruction: Instruction,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeError {
    pub kind: RuntimeErrorKind,
    pub function: FunctionId,
    pub pc: Pc,
    pub source: RuntimeSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuntimeErrorKind {
    UncaughtThrow {
        value: Value,
        origin: ThrowOrigin,
        /// Resolved constructor name for guest-thrown values
        /// ([`ThrowOrigin::Bytecode`]). Populated by
        /// [`Machine::enrich_uncaught_throw`] before the error crosses the
        /// public runtime boundary, so downstream oracles can classify the
        /// thrown error without access to the machine heap. `None` for
        /// engine-originated throws whose [`ThrowOrigin`] variant already
        /// names the constructor, or when the value is not an object with a
        /// resolvable constructor.
        constructor_name: Option<EcmaString>,
        /// The thrown object's own `message` data property, read at the same
        /// boundary, so a failure can say more than which constructor threw.
        message: Option<EcmaString>,
    },
    FuelExhausted {
        limit: u64,
    },
    CallDepthExceeded {
        limit: usize,
    },
    RegisterLimitExceeded {
        limit: usize,
    },
    ArgumentLimitExceeded {
        limit: u32,
        requested: u32,
    },
    HeapSlotLimitExceeded {
        limit: usize,
    },
    HeapByteLimitExceeded {
        limit: usize,
    },
    ModuleCellLimitExceeded {
        limit: usize,
    },
    DynamicModuleLimitExceeded {
        limit: usize,
    },
    MicrotaskQueueLimitExceeded {
        limit: usize,
    },
    MicrotaskDrainReentry,
    TimerProviderFailure {
        message: String,
    },
    TimerCapacityExceeded {
        limit: usize,
    },
    TimerCheckpointReentry,
    InvalidDynamicScript {
        reason: &'static str,
    },
    TemporalDeadZone {
        module: ModuleId,
        binding: BindingId,
    },
    ExternalModuleUnavailable {
        module: ModuleId,
        edge: EdgeId,
    },
    DynamicImportEdgeMissing {
        module: ModuleId,
        specifier: ConstantId,
    },
    InvalidVerifiedProgram {
        module: ModuleId,
        instruction: Instruction,
    },
    InvalidValue {
        value: Value,
    },
    InvalidRuntimeHeapReference {
        slot: u32,
    },
    ModuleEvaluationStalled {
        module: ModuleId,
    },
    /// The regexp backtracking step budget was exhausted by a pathologically
    /// complex pattern. Surfaced as a runtime error (not a silent non-match)
    /// so callers can distinguish an aborted match from a genuine non-match.
    RegexpStepBudgetExceeded {
        limit: usize,
    },
    /// A caller-supplied cancellation token was triggered at a checkpoint.
    Cancelled,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "runtime error in function {} at pc {}",
            self.function.get(),
            self.pc.get()
        )?;
        if let Some(name) = &self.source.function_name {
            write!(formatter, " ({})", name.to_utf8_lossy())?;
        }
        write!(formatter, ": ")?;
        match &self.kind {
            RuntimeErrorKind::UncaughtThrow {
                value,
                origin,
                constructor_name,
                ..
            } => match constructor_name {
                Some(name) => write!(
                    formatter,
                    "uncaught {origin:?} throw (value {:#018x}, constructor {})",
                    value.to_bits(),
                    name.to_utf8_lossy()
                ),
                None => write!(
                    formatter,
                    "uncaught {origin:?} throw (value {:#018x})",
                    value.to_bits()
                ),
            },
            RuntimeErrorKind::FuelExhausted { limit } => {
                write!(formatter, "fuel exhausted after {limit} instructions")
            }
            RuntimeErrorKind::CallDepthExceeded { limit } => {
                write!(formatter, "call depth limit {limit} exceeded")
            }
            RuntimeErrorKind::RegisterLimitExceeded { limit } => {
                write!(formatter, "live register limit {limit} exceeded")
            }
            RuntimeErrorKind::ArgumentLimitExceeded { limit, requested } => write!(
                formatter,
                "argument count {requested} exceeds runtime limit {limit}"
            ),
            RuntimeErrorKind::HeapSlotLimitExceeded { limit } => {
                write!(formatter, "heap slot limit {limit} exceeded")
            }
            RuntimeErrorKind::HeapByteLimitExceeded { limit } => {
                write!(formatter, "heap byte limit {limit} exceeded")
            }
            RuntimeErrorKind::ModuleCellLimitExceeded { limit } => {
                write!(formatter, "module cell limit {limit} exceeded")
            }
            RuntimeErrorKind::DynamicModuleLimitExceeded { limit } => {
                write!(formatter, "dynamic module limit {limit} exceeded")
            }
            RuntimeErrorKind::MicrotaskQueueLimitExceeded { limit } => {
                write!(formatter, "microtask queue limit {limit} exceeded")
            }
            RuntimeErrorKind::MicrotaskDrainReentry => {
                write!(formatter, "microtask drain is already active")
            }
            RuntimeErrorKind::TimerProviderFailure { message } => {
                write!(formatter, "timer provider failure: {message}")
            }
            RuntimeErrorKind::TimerCapacityExceeded { limit } => {
                write!(formatter, "timer capacity {limit} exceeded")
            }
            RuntimeErrorKind::TimerCheckpointReentry => {
                write!(formatter, "timer checkpoint is already active")
            }
            RuntimeErrorKind::InvalidDynamicScript { reason } => {
                write!(formatter, "invalid dynamic script: {reason}")
            }
            RuntimeErrorKind::TemporalDeadZone { module, binding } => write!(
                formatter,
                "module {} binding {} read before initialization",
                module.get(),
                binding.get()
            ),
            RuntimeErrorKind::ExternalModuleUnavailable { module, edge } => write!(
                formatter,
                "external module at module {} edge {} is unavailable",
                module.get(),
                edge.get()
            ),
            RuntimeErrorKind::DynamicImportEdgeMissing { module, specifier } => write!(
                formatter,
                "verified module {} has no dynamic edge for constant {}",
                module.get(),
                specifier.get()
            ),
            RuntimeErrorKind::InvalidVerifiedProgram {
                module,
                instruction,
            } => write!(
                formatter,
                "verified module {} contains impossible instruction {instruction:?}",
                module.get()
            ),
            RuntimeErrorKind::InvalidValue { value } => {
                write!(
                    formatter,
                    "malformed or foreign value {:#018x}",
                    value.to_bits()
                )
            }
            RuntimeErrorKind::InvalidRuntimeHeapReference { slot } => {
                write!(formatter, "runtime heap slot {slot} does not exist")
            }
            RuntimeErrorKind::ModuleEvaluationStalled { module } => write!(
                formatter,
                "module {} evaluation cannot complete: no pending microtask or live timer",
                module.get()
            ),
            RuntimeErrorKind::RegexpStepBudgetExceeded { limit } => {
                write!(formatter, "regular expression step budget {limit} exceeded")
            }
            RuntimeErrorKind::Cancelled => formatter.write_str("operation cancelled"),
        }
    }
}

impl Error for RuntimeError {}

/// Converts constants that need no runtime identity to ABI values. Strings and
/// bigints are materialized by `LoadConst` in the machine's slot heap.
#[must_use]
pub fn constant_value(constant: &Constant) -> Option<Value> {
    match constant {
        Constant::Number(bits) => Some(Value::number(bits.to_f64())),
        Constant::Int32(value) => Some(Value::int32(*value as u32)),
        Constant::String(_) | Constant::BigInt(_) => None,
        Constant::Boolean(value) => Some(Value::boolean(*value)),
        Constant::Null => Some(Value::NULL),
        Constant::Undefined => Some(Value::UNDEFINED),
    }
}

/// Interned property name. Each distinct string exists once per machine.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Atom(NonZeroU32);
impl Atom {
    fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}
/// Maps distinct property names to atoms. Atoms are never freed during a `Machine` lifetime.
#[derive(Clone, Debug, Default)]
struct AtomTable {
    map: HashMap<EcmaString, Atom>,
    strings: Vec<EcmaString>,
    utf8: Vec<Option<String>>,
    ascii: Vec<bool>,
    array_index: Vec<Option<u32>>,
}
impl AtomTable {
    fn intern(&mut self, text: EcmaString) -> Atom {
        if let Some(&atom) = self.map.get(&text) {
            return atom;
        }
        let next = u32::try_from(self.strings.len()).expect("atom count fits u32");
        let id = NonZeroU32::new(next + 1).expect("atom count fits u32");
        let atom = Atom(id);
        let is_ascii = text.as_units().iter().all(|&unit| unit < 0x80);
        let utf8 = text.to_utf8_strict().ok();
        let index = array_index(&text);
        self.map.insert(text.clone(), atom);
        self.strings.push(text);
        self.utf8.push(utf8);
        self.ascii.push(is_ascii);
        self.array_index.push(index);
        atom
    }
    fn intern_str(&mut self, text: &str) -> Atom {
        self.intern(EcmaString::encode(text))
    }
    fn find(&self, text: &str) -> Option<Atom> {
        self.map.get(&EcmaString::encode(text)).copied()
    }
    fn find_text(&self, text: &EcmaString) -> Option<Atom> {
        self.map.get(text).copied()
    }
    fn resolve(&self, atom: Atom) -> &EcmaString {
        &self.strings[atom.index()]
    }
    fn utf8(&self, atom: Atom) -> Option<&str> {
        self.utf8[atom.index()].as_deref()
    }
    fn is_ascii(&self, atom: Atom) -> bool {
        self.ascii[atom.index()]
    }
    fn array_index(&self, atom: Atom) -> Option<u32> {
        self.array_index[atom.index()]
    }
    fn eq_ascii(&self, atom: Atom, ascii: &str) -> bool {
        match self.utf8(atom) {
            Some(text) => text == ascii,
            None => false,
        }
    }
    fn charge_bytes(&self, atom: Atom) -> usize {
        self.strings[atom.index()]
            .len_units()
            .saturating_mul(2)
            .saturating_add(8)
    }
}
fn preintern_constant_name(atoms: &mut AtomTable, constants: &[Constant], id: ConstantId) {
    if let Some(Constant::String(text)) = constants.get(id.get() as usize) {
        atoms.intern(text.clone());
    }
}
#[derive(Clone, Copy)]
enum StaticDef {
    StringConst(ConstantId),
    Forward(Register),
}
fn static_key_register(instruction: &Instruction) -> Option<Register> {
    match *instruction {
        Instruction::GetProperty { key, .. }
        | Instruction::SetProperty { key, .. }
        | Instruction::DeleteProperty { key, .. }
        | Instruction::DefineAccessor { key, .. }
        | Instruction::DefineDataProperty { key, .. }
        | Instruction::LoadOwnDescriptorSlot { key, .. }
        | Instruction::DefineOwnDescriptorSlot { key, .. }
        | Instruction::WithHasBinding { key, .. }
        | Instruction::GetSuper { key, .. }
        | Instruction::SetSuper { key, .. } => Some(key),
        _ => None,
    }
}
fn preintern_static_keys(atoms: &mut AtomTable, constants: &[Constant], function: &Function) {
    let code = function.code();
    if code.is_empty() {
        return;
    }
    let registers = function.register_count() as usize;
    if registers == 0 {
        return;
    }
    if code
        .iter()
        .all(|instruction| static_key_register(instruction).is_none())
    {
        return;
    }
    let entry = function
        .capture_count()
        .saturating_add(function.parameter_count()) as usize;
    let mut analysis = StaticKeyAnalysis {
        rows: vec![StaticKeyRow::default(); registers],
        path: Vec::new(),
    };
    analysis.count_writes(entry, code);
    for instruction in code {
        analysis.record_def(instruction, constants);
    }
    for instruction in code {
        let Some(start) = static_key_register(instruction) else {
            continue;
        };
        let Some(id) = analysis.resolve(start) else {
            continue;
        };
        preintern_constant_name(atoms, constants, id);
    }
}
#[derive(Clone, Copy, Default)]
struct StaticKeyRow {
    writes: u8,
    def: Option<StaticDef>,
    resolved: Option<Option<ConstantId>>,
    in_path: bool,
}
struct StaticKeyAnalysis {
    rows: Vec<StaticKeyRow>,
    path: Vec<usize>,
}
impl StaticKeyAnalysis {
    fn count_writes(&mut self, entry: usize, code: &[Instruction]) {
        let entry = entry.min(self.rows.len());
        for row in &mut self.rows[..entry] {
            row.writes = 1;
        }
        for instruction in code {
            instruction.visit_writes(|register| {
                let index = register.get() as usize;
                if let Some(row) = self.rows.get_mut(index)
                    && row.writes < 2
                {
                    row.writes += 1;
                }
            });
        }
    }
    fn record_def(&mut self, instruction: &Instruction, constants: &[Constant]) {
        let (dst, def) = match *instruction {
            Instruction::LoadConst { dst, constant } => {
                if !matches!(
                    constants.get(constant.get() as usize),
                    Some(Constant::String(_))
                ) {
                    return;
                }
                (dst, StaticDef::StringConst(constant))
            }
            Instruction::Move { dst, src } => (dst, StaticDef::Forward(src)),
            Instruction::Unary {
                dst,
                op: UnaryOp::ToPropertyKey,
                operand,
            } => (dst, StaticDef::Forward(operand)),
            _ => return,
        };
        let index = dst.get() as usize;
        if let Some(row) = self.rows.get_mut(index)
            && row.writes == 1
        {
            row.def = Some(def);
        }
    }
    fn resolve(&mut self, start: Register) -> Option<ConstantId> {
        self.path.clear();
        let mut current = start;
        let result = loop {
            let index = current.get() as usize;
            let Some(row) = self.rows.get_mut(index) else {
                break None;
            };
            if row.writes != 1 || row.in_path {
                break None;
            }
            if let Some(cached) = row.resolved {
                break cached;
            }
            match row.def {
                None => {
                    row.resolved = Some(None);
                    break None;
                }
                Some(StaticDef::StringConst(id)) => {
                    row.resolved = Some(Some(id));
                    break Some(id);
                }
                Some(StaticDef::Forward(next)) => {
                    row.in_path = true;
                    self.path.push(index);
                    current = next;
                }
            }
        };
        for path in self.path.drain(..) {
            self.rows[path].resolved = Some(result);
            self.rows[path].in_path = false;
        }
        result
    }
}
fn preintern_module_code(atoms: &mut AtomTable, code: &Module<Verified>) {
    let constants = code.constants();
    for function in code.functions() {
        for instruction in function.code() {
            match instruction {
                Instruction::LoadGlobal { name, .. } | Instruction::TypeOfGlobal { name, .. } => {
                    preintern_constant_name(atoms, constants, *name);
                }
                Instruction::RequireGlobalBinding { name } => {
                    preintern_constant_name(atoms, constants, *name);
                }
                Instruction::StoreGlobal { name, .. } => {
                    preintern_constant_name(atoms, constants, *name);
                }
                _ => {}
            }
        }
    }
    for function in code.functions() {
        preintern_static_keys(atoms, constants, function);
    }
}
fn preintern_program_names(atoms: &mut AtomTable, program: &Program<Verified>) {
    for module in program.modules() {
        for export in module.exports() {
            preintern_constant_name(atoms, module.code.constants(), export.name);
        }
        preintern_module_code(atoms, &module.code);
    }
}
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum PropertyKey {
    Named(Atom),
    Symbol(u32),
    Private(u32),
}
impl PropertyKey {
    fn as_string<'a>(&self, atoms: &'a AtomTable) -> Option<&'a EcmaString> {
        match self {
            PropertyKey::Named(atom) => Some(atoms.resolve(*atom)),
            PropertyKey::Symbol(_) | PropertyKey::Private(_) => None,
        }
    }
    fn charge_bytes(&self, atoms: &AtomTable) -> usize {
        match self {
            PropertyKey::Named(atom) => atoms.charge_bytes(*atom),
            PropertyKey::Symbol(_) | PropertyKey::Private(_) => 16,
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
enum Property {
    Data {
        value: Value,
        writable: bool,
        enumerable: bool,
        configurable: bool,
    },
    Accessor {
        getter: Option<Value>,
        setter: Option<Value>,
        enumerable: bool,
        configurable: bool,
    },
}
impl Property {
    fn enumerable(&self) -> bool {
        match self {
            Self::Data { enumerable, .. } | Self::Accessor { enumerable, .. } => *enumerable,
        }
    }
    fn configurable(&self) -> bool {
        match self {
            Self::Data { configurable, .. } | Self::Accessor { configurable, .. } => *configurable,
        }
    }
    fn charge_bytes(&self) -> usize {
        match self {
            Self::Data { .. } => 0,
            Self::Accessor { .. } => std::mem::size_of::<Value>(),
        }
    }
}
#[derive(Clone, Debug)]
enum PropertyMap {
    Shaped {
        shape: ShapeId,
        slots: Vec<Property>,
    },
    Dictionary {
        entries: Vec<Option<(PropertyKey, Property)>>,
        index: HashMap<PropertyKey, u32>,
    },
}
impl Default for PropertyMap {
    fn default() -> Self {
        PropertyMap::Shaped {
            shape: ShapeId::ROOT,
            slots: Vec::new(),
        }
    }
}
impl PropertyMap {
    fn get(&self, shapes: &ShapeTable, key: &PropertyKey) -> Option<&Property> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                let slot = shapes.slot_of(*shape, key)?;
                slots.get(slot as usize)
            }
            PropertyMap::Dictionary { entries, index } => {
                let position = *index.get(key)?;
                entries[position as usize]
                    .as_ref()
                    .map(|(_, property)| property)
            }
        }
    }
    fn get_mut(&mut self, shapes: &ShapeTable, key: &PropertyKey) -> Option<&mut Property> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                let slot = shapes.slot_of(*shape, key)?;
                slots.get_mut(slot as usize)
            }
            PropertyMap::Dictionary { entries, index } => {
                let position = *index.get(key)?;
                entries[position as usize]
                    .as_mut()
                    .map(|(_, property)| property)
            }
        }
    }
    fn contains_key(&self, shapes: &ShapeTable, key: &PropertyKey) -> bool {
        self.get(shapes, key).is_some()
    }
    fn get_ascii(&self, shapes: &ShapeTable, atoms: &AtomTable, ascii: &str) -> Option<&Property> {
        debug_assert!(ascii.is_ascii());
        let atom = atoms.find(ascii)?;
        self.get(shapes, &PropertyKey::Named(atom))
    }
    fn insert(
        &mut self,
        shapes: &mut ShapeTable,
        key: PropertyKey,
        property: Property,
    ) -> Option<Property> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                if let Some(slot) = shapes.slot_of(*shape, &key) {
                    return Some(std::mem::replace(&mut slots[slot as usize], property));
                }
                if slots.len() >= SHAPED_CAPACITY {
                    let taken = std::mem::take(slots);
                    let mut dictionary = Self::to_dictionary(shapes, *shape, taken);
                    dictionary.insert(shapes, key, property);
                    *self = dictionary;
                    return None;
                }
                let next = shapes.transition(*shape, &key);
                slots.push(property);
                debug_assert_eq!(slots.len(), shapes.slot_count(next) as usize);
                *shape = next;
                None
            }
            PropertyMap::Dictionary { entries, index } => {
                if let Some(&position) = index.get(&key) {
                    let (_, current) = entries[position as usize]
                        .as_mut()
                        .expect("dictionary index names a live entry");
                    return Some(std::mem::replace(current, property));
                }
                Self::compact_dictionary(entries, index);
                let position = u32::try_from(entries.len()).expect("property count fits u32");
                entries.push(Some((key.clone(), property)));
                index.insert(key, position);
                None
            }
        }
    }
    fn remove(&mut self, shapes: &ShapeTable, key: &PropertyKey) -> Option<Property> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                shapes.slot_of(*shape, key)?;
                let taken = std::mem::take(slots);
                let mut dictionary = Self::to_dictionary(shapes, *shape, taken);
                let removed = dictionary.remove(shapes, key);
                *self = dictionary;
                removed
            }
            PropertyMap::Dictionary { entries, index } => {
                let position = index.remove(key)?;
                entries[position as usize]
                    .take()
                    .map(|(_, property)| property)
            }
        }
    }
    fn iter<'a>(&'a self, shapes: &'a ShapeTable) -> PropertyMapIter<'a> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                let keys = shapes.ordered_keys(*shape);
                debug_assert_eq!(keys.len(), slots.len());
                PropertyMapIter::Shaped {
                    keys: keys.into_iter(),
                    slots: slots.iter(),
                }
            }
            PropertyMap::Dictionary { entries, .. } => PropertyMapIter::Dictionary {
                entries: entries.iter(),
            },
        }
    }
    fn for_each_property_mut(&mut self, mut update: impl FnMut(&mut Property)) {
        match self {
            PropertyMap::Shaped { slots, .. } => {
                for property in slots.iter_mut() {
                    update(property);
                }
            }
            PropertyMap::Dictionary { entries, .. } => {
                for entry in entries.iter_mut().flatten() {
                    update(&mut entry.1);
                }
            }
        }
    }
    fn retain(
        &mut self,
        shapes: &ShapeTable,
        mut keep: impl FnMut(&PropertyKey, &Property) -> bool,
    ) {
        let dropped: Vec<PropertyKey> = self
            .iter(shapes)
            .filter(|&(key, property)| !keep(key, property))
            .map(|(key, _property)| key.clone())
            .collect();
        if dropped.is_empty() {
            return;
        }
        if let PropertyMap::Shaped { shape, slots } = self {
            let shape = *shape;
            let slots = std::mem::take(slots);
            *self = Self::to_dictionary(shapes, shape, slots);
        }
        for key in &dropped {
            self.remove(shapes, key);
        }
    }
    fn into_entries(self, shapes: &ShapeTable) -> Vec<(PropertyKey, Property)> {
        match self {
            PropertyMap::Shaped { shape, slots } => {
                let keys = shapes.ordered_keys(shape);
                debug_assert_eq!(keys.len(), slots.len());
                keys.into_iter().cloned().zip(slots).collect()
            }
            PropertyMap::Dictionary { entries, .. } => entries.into_iter().flatten().collect(),
        }
    }
    fn charge_bytes(&self, shapes: &ShapeTable, atoms: &AtomTable) -> usize {
        self.iter(shapes).fold(0, |bytes, (key, property)| {
            bytes
                .saturating_add(key.charge_bytes(atoms))
                .saturating_add(property.charge_bytes())
        })
    }
    fn to_dictionary(shapes: &ShapeTable, shape: ShapeId, slots: Vec<Property>) -> PropertyMap {
        let keys = shapes.ordered_keys(shape);
        debug_assert_eq!(keys.len(), slots.len());
        let mut entries = Vec::with_capacity(slots.len());
        let mut index = HashMap::new();
        for (offset, (key, property)) in keys.into_iter().cloned().zip(slots).enumerate() {
            let position = u32::try_from(offset).expect("property count fits u32");
            index.insert(key.clone(), position);
            entries.push(Some((key, property)));
        }
        PropertyMap::Dictionary { entries, index }
    }
    fn compact_dictionary(
        entries: &mut Vec<Option<(PropertyKey, Property)>>,
        index: &mut HashMap<PropertyKey, u32>,
    ) {
        let live = index.len();
        if entries.len().saturating_sub(live) <= live {
            return;
        }
        let mut compacted: Vec<Option<(PropertyKey, Property)>> = Vec::with_capacity(live + 1);
        index.clear();
        for slot in entries.drain(..).flatten() {
            let position = u32::try_from(compacted.len()).expect("property count fits u32");
            index.insert(slot.0.clone(), position);
            compacted.push(Some(slot));
        }
        *entries = compacted;
    }
}
enum PropertyMapIter<'a> {
    Shaped {
        keys: std::vec::IntoIter<&'a PropertyKey>,
        slots: std::slice::Iter<'a, Property>,
    },
    Dictionary {
        entries: std::slice::Iter<'a, Option<(PropertyKey, Property)>>,
    },
}
impl<'a> Iterator for PropertyMapIter<'a> {
    type Item = (&'a PropertyKey, &'a Property);
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PropertyMapIter::Shaped { keys, slots } => Some((keys.next()?, slots.next()?)),
            PropertyMapIter::Dictionary { entries } => {
                if let Some((key, property)) = entries.by_ref().flatten().next() {
                    return Some((key, property));
                }
                None
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IterationKind {
    Key(intrinsics::IteratorFamily),
    Value(intrinsics::IteratorFamily),
    Entry(intrinsics::IteratorFamily),
    /// A `%StringIteratorPrototype%` instance; `source` is its code points.
    StringCodePoint,
    /// A `%RegExpStringIteratorPrototype%` instance; `source` is its hidden state.
    RegExpString,
    /// An `Iterator` helper; `source` is its hidden state.
    IteratorHelper(intrinsics::builtins::iterator_helpers::Operation),
    /// A `%WrapForValidIteratorPrototype%` instance; `source` is its record.
    WrapForValid,
}

#[derive(Clone, Copy, Debug)]
struct CollectionEntry {
    order: u64,
    key: Value,
    value: Value,
    live: bool,
}

impl CollectionEntry {
    const BYTES: usize = std::mem::size_of::<Self>();
}

#[derive(Clone, Debug, Default)]
struct CollectionIndex {
    buckets: std::collections::HashMap<u64, Vec<usize>>,
}

impl CollectionIndex {
    const ENTRY_BYTES: usize = std::mem::size_of::<usize>();

    fn insert(&mut self, hash: u64, index: usize) {
        self.buckets.entry(hash).or_default().push(index);
    }

    fn clear(&mut self) {
        self.buckets.clear();
    }
}

/// Finds the live entry whose key equals `key`. The bucket is copied out
/// before any key is flattened, so the heap borrow never overlaps a write.
pub(crate) fn collection_lookup<H: Host>(
    machine: &mut Machine<'_, H>,
    slot: usize,
    key: Value,
) -> Option<usize> {
    let hash = collection_key_hash(machine, key);
    let candidates = {
        let HeapEntry::Collection { index, .. } = &machine.heap[slot] else {
            return None;
        };
        index.buckets.get(&hash).cloned()?
    };
    for candidate in candidates {
        let (live, entry_key) = {
            let HeapEntry::Collection { entries, .. } = &machine.heap[slot] else {
                return None;
            };
            let entry = entries.get(candidate)?;
            (entry.live, entry.key)
        };
        if live && machine.same_value_zero(entry_key, key) {
            return Some(candidate);
        }
    }
    None
}

fn collection_key_hash<H: Host>(machine: &mut Machine<'_, H>, key: Value) -> u64 {
    use std::hash::{Hash, Hasher};

    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    match key.decode() {
        Some(Decoded::Number(number)) => {
            0_u8.hash(&mut hasher);
            let normalized = if number.is_nan() {
                Value::CANON_NAN
            } else if number == 0.0 {
                0
            } else {
                number.to_bits()
            };
            normalized.hash(&mut hasher);
        }
        Some(Decoded::Int32(raw)) => {
            0_u8.hash(&mut hasher);
            f64::from(raw as i32).to_bits().hash(&mut hasher);
        }
        Some(Decoded::HeapRef(_)) => {
            if let Some(text) = machine.string_value(key) {
                1_u8.hash(&mut hasher);
                text.hash(&mut hasher);
            } else if let Ok(Some(index)) = machine.runtime_slot(key) {
                if let HeapEntry::BigInt(text) = &machine.heap[index] {
                    2_u8.hash(&mut hasher);
                    text.hash(&mut hasher);
                } else {
                    3_u8.hash(&mut hasher);
                    key.to_bits().hash(&mut hasher);
                }
            } else {
                3_u8.hash(&mut hasher);
                key.to_bits().hash(&mut hasher);
            }
        }
        _ => {
            4_u8.hash(&mut hasher);
            key.to_bits().hash(&mut hasher);
        }
    }
    hasher.finish()
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum IteratorNextPrepared {
    Ready {
        done: bool,
        value: Value,
    },
    Call {
        callee: Value,
        this_value: Value,
    },
    /// Calls the sync `next` method of an async-from-sync wrapper; the raw
    /// result must flow through the adapter continuation (ECMA-262 27.1.5)
    /// before it may be awaited.
    AsyncFromSyncCall {
        callee: Value,
        this_value: Value,
    },
}

#[derive(Clone, Debug)]
enum IteratorState {
    Keys(ForInIteratorState),
    Protocol { iterator: Value, next: Value },
}

/// Shared lazy `for`/`in` traversal state (ECMA-262 14.7.5.15
/// EnumerateObjectProperties): one prototype level at a time instead of an
/// eagerly collected whole-chain key list. The state lives inside the heap's
/// iterator entry so garbage collection can trace `current` between
/// user-code re-entry points such as proxy traps.
#[derive(Clone, Debug)]
struct ForInIteratorState {
    /// Object whose own keys are being walked; `None` once traversal is
    /// complete (including nullish sources, which start complete).
    current: Option<Value>,
    /// Whether the current object's slot claim and key snapshot were taken.
    object_was_visited: bool,
    /// Remaining string own keys of the current level, in own-key order.
    remaining: VecDeque<EcmaString>,
    /// Names already decided by a nearer level; they shadow farther levels.
    visited_names: BTreeSet<EcmaString>,
    /// Object slots already visited; a repeat is a malformed prototype cycle.
    visited_objects: BTreeSet<usize>,
}

#[derive(Clone, Debug)]
pub(crate) struct GeneratorStart {
    pub(crate) target: RuntimeFunction,
    pub(crate) captures: Vec<Value>,
    pub(crate) this_value: Value,
    pub(crate) new_target: Value,
    pub(crate) args: Vec<Value>,
    pub(crate) context: Option<Value>,
}

#[derive(Clone, Debug)]
pub(crate) struct SuspendedActivation {
    pub(crate) target: RuntimeFunction,
    pub(crate) registers: Vec<Value>,
    pub(crate) this_value: Value,
    pub(crate) new_target: Value,
    pub(crate) args: Vec<Value>,
    pub(crate) arguments_object: Option<Value>,
    pub(crate) resume_token: u32,
    pub(crate) context: Option<Value>,
}

#[derive(Clone, Debug)]
pub(crate) enum GeneratorState {
    SuspendedStart(GeneratorStart),
    Executing,
    Suspended(SuspendedActivation),
    Completed,
}

#[derive(Clone, Debug)]
pub(crate) enum GeneratorResume {
    Yield {
        value: Value,
        activation: SuspendedActivation,
    },
    Return(Value),
    Throw {
        value: Value,
        origin: ThrowOrigin,
    },
}
/// One resume request on an async generator plus the Promise handed back to
/// the caller that the request settles.
#[derive(Clone, Debug)]
pub(crate) struct AsyncGeneratorRequest {
    pub(crate) completion: GeneratorCompletion,
    pub(crate) capability: Value,
}

/// Lifecycle of a `HeapEntry::AsyncGenerator`. `AwaitingOperand` parks on an
/// `Await` inside the body; `AwaitingYield` parks awaiting a yielded operand;
/// `AwaitingResumption` parks while awaiting a return-resumption operand.
/// While executing or awaiting, the body is owned by the front FIFO request.
#[derive(Clone, Debug)]
pub(crate) enum AsyncGeneratorState {
    SuspendedStart(GeneratorStart),
    SuspendedYield(SuspendedActivation),
    Executing,
    AwaitingOperand(SuspendedActivation),
    AwaitingYield(SuspendedActivation),
    AwaitingResumption(SuspendedActivation),
    /// The body is gone; the front request's return value is being awaited.
    AwaitingReturn,
    Completed,
}

/// One step of driving an async-generator activation: it hit an `Await`, it
/// reached a `yield`, it returned, or it threw an uncaught value. This is the
/// union of `AsyncStep` and `GeneratorResume` produced by one drive call.
#[derive(Clone, Debug)]
pub(crate) enum AsyncGeneratorStep {
    Await {
        awaited: Value,
        activation: SuspendedActivation,
    },
    Yield {
        value: Value,
        activation: SuspendedActivation,
    },
    Return(Value),
    Throw {
        value: Value,
        origin: ThrowOrigin,
    },
}

/// Collapses a drive helper's `EvalFailure` into the fatal channel of a
/// Promise reaction job: runtime failures keep their kind; a throw-class
/// failure here is an invariant violation, since settling paths only reject
/// or resolve Promises rather than run user code.
fn async_generator_kind(generator: Value, failure: EvalFailure) -> RuntimeErrorKind {
    match failure {
        EvalFailure::Runtime(kind) => kind,
        _ => RuntimeErrorKind::InvalidValue { value: generator },
    }
}

/// One step of driving a detached async-function activation: it awaited a
/// value (and must suspend), it returned, or it threw an uncaught value.
#[derive(Clone, Debug)]
enum AsyncStep {
    Suspend {
        awaited: Value,
        activation: SuspendedActivation,
    },
    Return {
        value: Value,
        execution: Option<Execution>,
    },
    Throw(RuntimeError),
}

impl AsyncStep {
    fn held_value(&self) -> Option<Value> {
        match self {
            Self::Suspend { awaited, .. } => Some(*awaited),
            Self::Return { value, .. } => Some(*value),
            Self::Throw(error) => match &error.kind {
                RuntimeErrorKind::UncaughtThrow { value, .. } => Some(*value),
                _ => None,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum PromiseState {
    Pending {
        fulfill_reactions: Vec<PromiseReaction>,
        reject_reactions: Vec<PromiseReaction>,
    },
    Fulfilled {
        value: Value,
    },
    Rejected {
        reason: Value,
        origin: ThrowOrigin,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum PromiseCompletion {
    Fulfilled,
    Rejected,
}

#[derive(Clone, Debug)]
pub(crate) enum PromiseReaction {
    Fulfilled {
        handler: Value,
        derived: Value,
        context: Option<Value>,
    },
    Rejected {
        handler: Value,
        derived: Value,
        context: Option<Value>,
    },
    /// Resumes a suspended async activation on fulfillment. Carries only the
    /// heap `AsyncActivation` record handle; the awaited value arrives as the
    /// reaction value.
    AsyncFulfill {
        activation: Value,
        context: Option<Value>,
    },
    /// Resumes a suspended async activation on rejection. Carries only the
    /// heap `AsyncActivation` record handle; the rejection reason arrives as
    /// the reaction value.
    AsyncReject {
        activation: Value,
        context: Option<Value>,
    },
    /// Resumes a parked async generator on fulfillment of its awaited value.
    /// Carries only the `HeapEntry::AsyncGenerator` handle; the parked
    /// activation lives in the generator's own state.
    AsyncGeneratorFulfill {
        generator: Value,
        context: Option<Value>,
    },
    /// Resumes a parked async generator on rejection of its awaited value.
    AsyncGeneratorReject {
        generator: Value,
        context: Option<Value>,
    },
    /// Counts one fulfilled static dependency of an async-pending module.
    /// The last fulfillment starts the parent entry inline inside the
    /// reaction job.
    ModuleDepFulfill {
        parent: ModuleId,
        context: Option<Value>,
    },
    /// Propagates one rejected static dependency into its async-pending
    /// parent: the parent entry never runs and the parent settles with the
    /// same uncaught throw.
    ModuleDepReject {
        parent: ModuleId,
        context: Option<Value>,
    },
    /// Rebuilds the iterator result of an async-from-sync step: the reaction
    /// value is the already-unwrapped `value`; `done` was read from the sync
    /// result before any await.
    AsyncFromSyncFulfill {
        derived: Value,
        done: bool,
        context: Option<Value>,
    },
    /// Closes the synchronous iterator, then rejects the derived
    /// async-from-sync step promise with the original PromiseResolve rejection.
    AsyncFromSyncReject {
        derived: Value,
        sync_iterator: Value,
        context: Option<Value>,
    },

    /// Continues one suspended `AsyncDisposableStack` drain after an awaited
    /// disposer settles. The reaction owns the complete continuation so it can
    /// be consumed exactly once by the microtask executor.
    AsyncDisposeStep {
        stack: Value,
        pending_error: Option<Value>,
        capability: Value,
        rejected: bool,
        context: Option<Value>,
    },
    /// Resolves an `import()` promise when a local module evaluation fulfills.
    DynamicImportFulfill {
        promise: Value,
        target: ModuleId,
        context: Option<Value>,
    },
    /// Propagates a local module evaluation rejection to an `import()` promise.
    DynamicImportReject {
        promise: Value,
        context: Option<Value>,
    },
}

impl PromiseReaction {
    fn context(&self) -> Option<Value> {
        match self {
            Self::Fulfilled { context, .. }
            | Self::Rejected { context, .. }
            | Self::AsyncFulfill { context, .. }
            | Self::AsyncReject { context, .. }
            | Self::AsyncGeneratorFulfill { context, .. }
            | Self::AsyncGeneratorReject { context, .. }
            | Self::ModuleDepFulfill { context, .. }
            | Self::ModuleDepReject { context, .. }
            | Self::AsyncFromSyncFulfill { context, .. }
            | Self::AsyncFromSyncReject { context, .. }
            | Self::AsyncDisposeStep { context, .. }
            | Self::DynamicImportFulfill { context, .. }
            | Self::DynamicImportReject { context, .. } => *context,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum MicrotaskJob {
    Reaction {
        reaction: PromiseReaction,
        value: Value,
        origin: ThrowOrigin,
    },
    Thenable {
        promise: Value,
        thenable: Value,
        then: Value,
        context: Option<Value>,
    },
    Callback {
        callback: Value,
        context: Option<Value>,
    },
    FinalizationCleanup {
        registry: Value,
        context: Option<Value>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct QueuedMicrotask {
    job: MicrotaskJob,
    retained_bytes: usize,
}

impl QueuedMicrotask {
    fn uncharged(job: MicrotaskJob) -> Self {
        Self {
            job,
            retained_bytes: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MicrotaskExceptionPolicy {
    CollectAndContinue,
    StopAtFirst,
}

/// An exception reported by a microtask or timer callback.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallbackException {
    /// The value thrown by the callback.
    pub value: Value,
    /// The operation that produced the throw.
    pub origin: ThrowOrigin,
}

/// The result of one explicit microtask checkpoint.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MicrotaskDrain {
    /// The number of jobs removed from the queue and run.
    pub executed: usize,
    /// Callback exceptions, in FIFO execution order.
    pub uncaught: Vec<CallbackException>,
}

/// The result of one explicit timer checkpoint. At most one callback runs.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TimerRun {
    /// The number of timer callbacks run: `0` or `1`.
    pub executed: usize,
    /// Callback exceptions from the run callback, if it threw.
    pub uncaught: Vec<CallbackException>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TimerWait {
    Ready,
    Stale,
    Idle,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CollectionKind {
    Map,
    Set,
    WeakMap,
    WeakSet,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ArrayElementKind {
    Int32,
    Number,
    Any,
}

/// An array's element vector together with the kind that describes it.
pub(crate) struct ArrayVector<'a> {
    pub(crate) kind: &'a mut ArrayElementKind,
    pub(crate) elements: &'a mut Vec<Value>,
}

impl ArrayElementKind {
    fn of_value(value: Value) -> Self {
        match value.decode() {
            Some(Decoded::Int32(_)) => Self::Int32,
            Some(Decoded::Number(_)) => Self::Number,
            _ => Self::Any,
        }
    }

    pub(crate) fn including(self, value: Value) -> Self {
        self.max(Self::of_value(value))
    }

    pub(crate) fn for_elements(elements: &[Value]) -> Self {
        elements
            .iter()
            .fold(Self::Int32, |kind, value| kind.including(*value))
    }

    fn admits(self, value: Value) -> bool {
        self >= Self::of_value(value)
    }

    fn matches(self, elements: &[Value]) -> bool {
        elements.iter().all(|value| self.admits(*value))
    }
}

fn install_element_vector(heap: &mut Heap, array_slot: usize, elements: Vec<Value>) {
    let kind = ArrayElementKind::for_elements(&elements);
    let HeapEntry::Array {
        elements: current,
        kind: stored_kind,
        ..
    } = &mut heap[array_slot]
    else {
        unreachable!("element vector replacement requires an array slot");
    };
    *current = elements;
    *stored_kind = kind;
    debug_assert!(kind.matches(current));
}

/// A concatenation of this many UTF-16 units or more keeps its halves
/// instead of copying them.
const ROPE_MIN_UNITS: u32 = 32;
/// What a rope node itself costs: two halves and a length. Reading the units
/// later costs the flat text, which `flat_string` charges at that point.
const ROPE_NODE_BYTES: usize = 2 * std::mem::size_of::<Value>() + std::mem::size_of::<u32>();

#[derive(Clone, Debug)]
enum HeapEntry {
    Vacant,
    String(EcmaString),
    /// The two halves of a concatenation and its total length in UTF-16
    /// units. The halves are string or rope entries and are never written
    /// after creation; reading the units replaces this entry with `String`.
    Rope {
        left: Value,
        right: Value,
        len: u32,
    },
    BigInt(String),
    Object {
        properties: PropertyMap,
        prototype: Option<Value>,
        boxed_primitive: Option<Value>,
        extensible: bool,
    },
    Array {
        kind: ArrayElementKind,
        elements: Vec<Value>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
        length_writable: bool,
    },
    Function {
        module: ModuleId,
        function: FunctionId,
        captures: Vec<Value>,
        context: Option<Value>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// A `vm.Script` whose entry function retains its machine-owned dynamic module.
    Script {
        entry: Value,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    ModuleNamespace {
        module: ModuleId,
    },
    ExternalModuleNamespace {
        specifier: EcmaString,
    },
    HashState {
        algorithm: String,
        data: Vec<u8>,
        digested: bool,
        update: Value,
        digest: Value,
    },
    Symbol {
        description: EcmaString,
    },
    PrivateName {
        description: EcmaString,
    },
    RegExp {
        pattern: EcmaString,
        flags: EcmaString,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    Date {
        time: f64,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// Instances of the `Temporal` classes. The boxed record holds no `Value`,
    /// so tracing needs only the properties and prototype.
    Temporal {
        value: Box<temporal::TemporalObject>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// Instances of the `Intl` classes. The boxed record holds no `Value`;
    /// `bound` is the one value an instance keeps: the getter-created `format`
    /// or `compare`, or the input string of a `Segments` object or its iterator.
    Intl {
        value: Box<intl::IntlObject>,
        bound: Option<Value>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// Entries retain insertion positions. Deletion tombstones an entry so
    /// live iterators keep a stable order cursor; the index retains only
    /// integer positions and therefore introduces no GC roots.
    Collection {
        kind: CollectionKind,
        entries: Vec<CollectionEntry>,
        index: CollectionIndex,
        size: usize,
        next_order: u64,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    TypedArray {
        kind: ElementKind,
        buffer: Value,
        byte_offset: usize,
        byte_length: LengthSlot,
        array_length: LengthSlot,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    DataView {
        buffer: Value,
        byte_offset: usize,
        byte_length: LengthSlot,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    ArrayBuffer {
        data: intrinsics::builtins::arraybuffer::ArrayBufferData,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    SharedArrayBuffer {
        data: std::sync::Arc<intrinsics::builtins::arraybuffer::SharedBlock>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    WeakRef {
        target: Option<Value>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    FinalizationRegistry {
        cleanup_callback: Value,
        cells: Vec<intrinsics::builtins::weakref_finalization::FinalizationCell>,
        pending_holdings: VecDeque<Value>,
        cleanup_scheduled: bool,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    BuiltinIterator {
        source: Value,
        kind: IterationKind,
        position: Option<u64>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    Iterator {
        state: IteratorState,
    },
    Generator {
        state: GeneratorState,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// An `async function*` object: a FIFO of `.next()` requests plus a state
    /// machine that lets exactly the front request drive the body at a time.
    AsyncGenerator {
        state: AsyncGeneratorState,
        queue: VecDeque<AsyncGeneratorRequest>,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    AsyncFromSync {
        iterator: Value,
        next: Value,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// A synchronous or asynchronous explicit-resource stack. The state,
    /// disposal hint, and ordinary object header have one heap owner.
    DisposableStack {
        state: DisposalStackState,
        hint: DisposeHint,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    ProcessEnv {
        prototype: Option<Value>,
        extensible: bool,
    },
    Promise {
        state: PromiseState,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    /// A Node-compatible `Timeout` handle carrying its monotonic timer id,
    /// its active cancellation generation, and ordinary object property/prototype fields.
    Timeout {
        id: u64,
        /// The active generation for this id. A stale handle with a different
        /// generation cannot cancel a re-used id after an interval re-arms.
        generation: u64,
        properties: PropertyMap,
        prototype: Option<Value>,
        extensible: bool,
    },
    PromiseResolver {
        promise: Value,
        used: bool,
    },
    PromiseAll {
        resolve: Value,
        reject: Value,
        values: Vec<Value>,
        remaining: usize,
        settled: bool,
    },
    PromiseAllElement {
        aggregate: Value,
        index: usize,
        called: bool,
    },
    /// One suspended async activation together with the implicit result Promise
    /// it settles. Module entries also retain their terminal execution so
    /// evaluation does not publish before top-level await completes.
    AsyncActivation {
        activation: Option<SuspendedActivation>,
        promise: Value,
        module: Option<ModuleId>,
        completion: Option<Result<Execution, RuntimeError>>,
    },
    NativeFunction {
        callable: NativeCallable,
        properties: PropertyMap,
        extensible: bool,
        /// Explicit prototype override; `None` falls back to
        /// `%Function.prototype%` at read time (see `prototype_index`).
        /// Construct via [`HeapEntry::native_function`] so the intent is
        /// stated explicitly at every call site.
        prototype: Option<Value>,
    },
    Proxy {
        record: builtins::proxy::ProxyRecord,
    },
    /// A `Proxy.revocable` revoker. It stays callable and expandable, so it
    /// carries the ordinary property/prototype header; revocation only takes
    /// the retained proxy edge (see `ProxyRevokerRecord::for_each_value`).
    ProxyRevoker {
        record: builtins::proxy::ProxyRevokerRecord,
        properties: PropertyMap,
        extensible: bool,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum NativeCallable {
    Builtin(intrinsics::BuiltinId),
    Bound(Box<BoundCallable>),
}

#[derive(Clone, Debug)]
pub(crate) struct BoundCallable {
    pub(crate) target: Value,
    pub(crate) this_value: Value,
    pub(crate) arguments: Vec<Value>,
}

impl HeapEntry {
    fn initial_bytes(&self, shapes: &ShapeTable, atoms: &AtomTable) -> usize {
        match self {
            Self::Vacant => 0,
            Self::String(text)
            | Self::Symbol { description: text }
            | Self::PrivateName { description: text } => text.len_units().saturating_mul(2),
            Self::Rope { .. } => ROPE_NODE_BYTES,
            Self::BigInt(text) => text.len(),
            Self::RegExp { pattern, flags, .. } => pattern
                .len_units()
                .saturating_add(flags.len_units())
                .saturating_mul(2),
            Self::HashState {
                algorithm, data, ..
            } => algorithm.len() + data.len(),
            Self::Collection { size, .. } => size
                .saturating_mul(CollectionEntry::BYTES.saturating_add(CollectionIndex::ENTRY_BYTES))
                .saturating_add(1),
            Self::TypedArray { properties, .. } | Self::DataView { properties, .. } => {
                properties.charge_bytes(shapes, atoms).saturating_add(1)
            }
            Self::ArrayBuffer {
                data, properties, ..
            } => data
                .initial_bytes()
                .saturating_add(properties.charge_bytes(shapes, atoms))
                .saturating_add(1),
            Self::SharedArrayBuffer {
                data, properties, ..
            } => data
                .byte_length()
                .saturating_add(properties.charge_bytes(shapes, atoms))
                .saturating_add(1),
            Self::WeakRef { properties, .. } => {
                properties.charge_bytes(shapes, atoms).saturating_add(1)
            }
            Self::FinalizationRegistry {
                cells,
                pending_holdings,
                properties,
                ..
            } => cells
                .len()
                .saturating_mul(intrinsics::builtins::weakref_finalization::FinalizationCell::BYTES)
                .saturating_add(
                    pending_holdings
                        .len()
                        .saturating_mul(std::mem::size_of::<Value>()),
                )
                .saturating_add(properties.charge_bytes(shapes, atoms))
                .saturating_add(1),
            Self::NativeFunction {
                callable,
                properties,
                ..
            } => properties
                .charge_bytes(shapes, atoms)
                .saturating_add(match callable {
                    NativeCallable::Builtin(_) => 1,
                    NativeCallable::Bound(bound) => bound.arguments.len().saturating_add(1),
                }),
            Self::Proxy { .. } => 1,
            Self::ProxyRevoker { properties, .. } => {
                properties.charge_bytes(shapes, atoms).saturating_add(1)
            }
            Self::Generator { state, .. } => match state {
                GeneratorState::SuspendedStart(start) => start
                    .captures
                    .len()
                    .saturating_add(start.args.len())
                    .saturating_add(1),
                GeneratorState::Suspended(activation) => activation
                    .registers
                    .len()
                    .saturating_add(activation.args.len())
                    .saturating_add(1),
                GeneratorState::Executing | GeneratorState::Completed => 1,
            },
            Self::AsyncGenerator { state, queue, .. } => {
                let queued = queue
                    .len()
                    .saturating_mul(std::mem::size_of::<AsyncGeneratorRequest>());
                let state_bytes = match state {
                    AsyncGeneratorState::SuspendedStart(start) => start
                        .captures
                        .len()
                        .saturating_add(start.args.len())
                        .saturating_add(1),
                    AsyncGeneratorState::SuspendedYield(activation)
                    | AsyncGeneratorState::AwaitingOperand(activation)
                    | AsyncGeneratorState::AwaitingYield(activation)
                    | AsyncGeneratorState::AwaitingResumption(activation) => activation
                        .registers
                        .len()
                        .saturating_add(activation.args.len())
                        .saturating_add(1),
                    AsyncGeneratorState::Executing
                    | AsyncGeneratorState::AwaitingReturn
                    | AsyncGeneratorState::Completed => 1,
                };
                state_bytes.saturating_add(queued)
            }
            Self::AsyncFromSync { properties, .. } => properties.charge_bytes(shapes, atoms),
            Self::Object { properties, .. } | Self::Timeout { properties, .. } => {
                properties.charge_bytes(shapes, atoms).saturating_add(1)
            }
            Self::Array {
                elements,
                properties,
                ..
            } => elements
                .len()
                .saturating_mul(std::mem::size_of::<Value>())
                .saturating_add(properties.charge_bytes(shapes, atoms))
                .saturating_add(1),
            Self::Function { .. }
            | Self::Script { .. }
            | Self::ModuleNamespace { .. }
            | Self::ExternalModuleNamespace { .. }
            | Self::ProcessEnv { .. }
            | Self::Date { .. }
            | Self::Temporal { .. }
            | Self::Intl { .. }
            | Self::BuiltinIterator { .. }
            | Self::Iterator { .. }
            | Self::Promise { .. }
            | Self::DisposableStack { .. }
            | Self::PromiseResolver { .. }
            | Self::PromiseAll { .. }
            | Self::AsyncActivation { .. }
            | Self::PromiseAllElement { .. } => 1,
        }
    }

    /// Construct a `NativeFunction` with an explicit prototype override.
    ///
    /// Pass `None` to fall back to `%Function.prototype%` at read time
    /// (see [`Machine::prototype_index`]). Pass `Some(proto)` to inherit a
    /// specific prototype — `Function.prototype.bind` passes the target's
    /// prototype so the bound function inherits it. Routing every
    /// construction site through this function makes the `None`-means-
    /// fallback convention impossible to set by accident.
    pub(crate) fn native_function(
        callable: NativeCallable,
        properties: PropertyMap,
        prototype: Option<Value>,
    ) -> Self {
        Self::NativeFunction {
            callable,
            properties,
            extensible: true,
            prototype,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ReturnTo {
    /// The caller register receiving the result, or `None` to discard it (an
    /// accessor setter invocation produces no observable value).
    destination: Option<usize>,
    call_pc: usize,
    constructed: Option<Value>,
}

struct CallRequest<'a> {
    callee: Value,
    this_value: Value,
    arguments: &'a [Value],
    destination: Option<u32>,
    call_pc: usize,
    constructed: Option<Value>,
    new_target: Value,
}

pub(crate) struct BoundCall {
    pub(crate) target: Value,
    pub(crate) this_value: Value,
    pub(crate) arguments: Vec<Value>,
    pub(crate) new_target: Value,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct RuntimeFunction {
    pub(crate) module: ModuleId,
    pub(crate) function: FunctionId,
}

#[derive(Clone, Copy, Debug)]
struct ActivationRequest<'a> {
    target: RuntimeFunction,
    captures: &'a [Value],
    context: Option<Value>,
    this_value: Value,
    new_target: Value,
    arguments: &'a [Value],
    return_to: Option<ReturnTo>,
}

#[derive(Clone, Debug)]
struct Frame {
    module: ModuleId,
    function: usize,
    pc: usize,
    registers: Vec<Value>,
    return_to: Option<ReturnTo>,
    context: Option<Value>,
    outer_context: Option<Value>,
    this_value: Value,
    new_target: Value,
    args: Vec<Value>,
    arguments_object: Option<Value>,
}

impl Frame {
    fn new(metadata: &Function, request: ActivationRequest<'_>) -> Self {
        let mut registers = vec![Value::UNINITIALIZED; metadata.register_count() as usize];
        let capture_count = metadata.capture_count() as usize;
        for (index, slot) in registers.iter_mut().take(capture_count).enumerate() {
            *slot = request
                .captures
                .get(index)
                .copied()
                .unwrap_or(Value::UNDEFINED);
        }
        for (index, slot) in registers
            .iter_mut()
            .skip(capture_count)
            .take(metadata.parameter_count() as usize)
            .enumerate()
        {
            *slot = request
                .arguments
                .get(index)
                .copied()
                .unwrap_or(Value::UNDEFINED);
        }
        Self {
            module: request.target.module,
            function: request.target.function.get() as usize,
            pc: 0,
            registers,
            return_to: request.return_to,
            context: request.context,
            outer_context: None,
            this_value: request.this_value,
            new_target: request.new_target,
            args: request.arguments.to_vec(),
            arguments_object: None,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum EvalFailure {
    Throw(ThrowOrigin),
    ThrowValue(Value),
    Runtime(RuntimeErrorKind),
    ThrowValueOrigin { value: Value, origin: ThrowOrigin },
}

pub(crate) fn import_failure(error: &RuntimeError) -> EvalFailure {
    match &error.kind {
        RuntimeErrorKind::UncaughtThrow { value, origin, .. } => EvalFailure::ThrowValueOrigin {
            value: *value,
            origin: *origin,
        },
        kind => EvalFailure::Runtime(kind.clone()),
    }
}

/// Returns whether `specifier` uses a relative module-path prefix.
fn is_relative_module_specifier(specifier: &EcmaString) -> bool {
    let units = specifier.as_units();
    units.starts_with(&[u16::from(b'.'), u16::from(b'/')])
        || units.starts_with(&[u16::from(b'.'), u16::from(b'.'), u16::from(b'/')])
}

/// Totally normalizes a POSIX-like relative module-name path by collapsing empty,
/// `.`, and `..` components. Parent escapes past the first component are dropped
/// rather than rejected, so every input yields a name.
fn normalize_relative_module_name(name: &EcmaString) -> EcmaString {
    let slash = u16::from(b'/');
    let mut stack = Vec::new();
    for part in name.as_units().split(|&unit| unit == slash) {
        if part.is_empty() || part == [u16::from(b'.')] {
            continue;
        }
        if part == [u16::from(b'.'), u16::from(b'.')] {
            let _ = stack.pop();
            continue;
        }
        stack.push(part);
    }
    if stack.is_empty() {
        return EcmaString::default();
    }
    let mut units = Vec::with_capacity(name.len_units());
    for (index, part) in stack.into_iter().enumerate() {
        if index > 0 {
            units.push(slash);
        }
        units.extend_from_slice(part);
    }
    EcmaString::from_units(&units)
}

/// Resolves a relative specifier against the requester module's canonical directory.
fn resolve_relative_against_module_name(
    requester_name: &EcmaString,
    specifier: &EcmaString,
) -> EcmaString {
    let units = requester_name.as_units();
    let directory = match units.iter().rposition(|&unit| unit == u16::from(b'/')) {
        Some(index) => &units[..index],
        None => &[][..],
    };
    let mut joined = Vec::with_capacity(
        directory
            .len()
            .saturating_add(1)
            .saturating_add(specifier.len_units()),
    );
    if !directory.is_empty() {
        joined.extend_from_slice(directory);
        joined.push(u16::from(b'/'));
    }
    joined.extend_from_slice(specifier.as_units());
    normalize_relative_module_name(&EcmaString::from_units(&joined))
}

/// The outcome of resolving a property read.
#[derive(Clone, Debug)]
enum GetOutcome {
    /// A ready ABI value.
    Value(Value),
    /// Text that must be interned as a fresh heap string.
    Text(EcmaString),
    /// An accessor getter to invoke with the receiver as `this`.
    Getter(Value),
}

/// The outcome of resolving a property write.
#[derive(Clone, Debug)]
enum SetOutcome {
    Done,
    /// An accessor setter to invoke with the receiver as `this` and the value as
    /// its sole argument.
    Setter(Value),
}

/// Own-property lookup result during a prototype-chain walk.
#[derive(Clone, Debug)]
enum Found {
    Value(Value),
    Text(EcmaString),
    Getter(Value),
    Failure(RuntimeErrorKind),
    /// An accessor property with no getter resolves to `undefined`.
    NoGetter,
}

/// A classified callee, shared by the interpreter and the native engine so both
/// route calls through one decision. The native engine reimplements the frame
/// push but consumes this classifier verbatim.
#[derive(Clone, Debug)]
enum CalleeKind {
    Runtime {
        target: RuntimeFunction,
        captures: Vec<Value>,
        context: Option<Value>,
    },
    Builtin {
        id: intrinsics::BuiltinId,
    },
    Bound,
    Proxy,
    ProxyRevoker,
    NotCallable,
}

#[derive(Clone, Debug)]
struct TimerRecord {
    callback: Value,
    arguments: Vec<Value>,
    handle: Value,
    context: Option<Value>,
    deadline_ms: u64,
    sequence: u64,
    generation: u64,
    /// `Some(delay)` marks a repeating `setInterval` timer that re-arms with
    /// `delay` milliseconds after each fire; `None` is a one-shot `setTimeout`.
    interval_delay: Option<u32>,
}

/// The production bytecode interpreter.
pub struct Machine<'a, H: Host> {
    program: Option<&'a Program<Verified>>,
    module: &'a Module<Verified>,
    host: &'a mut H,
    limits: Limits,
    gc: gc::GcState,
    native_roots: Vec<Vec<Value>>,
    /// Recently compiled patterns. `exec` runs once per match of a global search,
    /// so recompiling on every call would make it cost a parse per match.
    /// Objects being joined, innermost last. A cycle passes through native code
    /// on every level, so no activation limit would stop it.
    array_join_stack: Vec<Value>,
    regexp_cache: Vec<(
        EcmaString,
        EcmaString,
        std::rc::Rc<intrinsics::builtins::regexp_v::CompiledV>,
    )>,
    /// Values kept strongly reachable for the current ECMAScript job by
    /// WeakRef construction/deref. Cleared exactly once at the outer job seam.
    kept_alive: Vec<Value>,
    /// What running builtins hold in Rust locals: everything they allocated or
    /// got back from user code. Calling user code can reach a collection, so
    /// these stay rooted until the builtin returns.
    builtin_temporaries: Vec<Value>,
    /// The latest results of `call_callback`, for loops that use each result
    /// once: `reduce` holds one at a time, and keeping them all would hold every
    /// intermediate.
    callback_results: Vec<Value>,
    /// Where the running builtin's results start in `callback_results`.
    results_floor: usize,
    /// A builtin is running, and not user code it called.
    in_builtin: bool,
    /// Microtask jobs that have left the queue and are still running.
    running_jobs: Vec<MicrotaskJob>,
    frames: Vec<Frame>,
    heap: Heap,
    slot_bytes: Vec<usize>,
    /// Freed bootstrap bytes that runtime mutations can reuse before they
    /// consume the runtime heap budget.
    intrinsic_slot_credits: Vec<usize>,
    machine_bytes: usize,
    intrinsic_slots: usize,
    vacant_count: usize,
    heap_bytes: usize,
    live_registers: usize,
    native_depth: usize,
    /// The native stack position where the machine was built, from which
    /// [`Limits::max_stack_bytes`] is measured.
    stack_base: usize,
    fuel: u64,
    global_object: Value,
    vm_context_marker: Value,
    /// The contextified global used only while executing `node:vm` code.
    ///
    /// `runInNewContext` creates a fresh `globalThis` for each call (or adopts
    /// the supplied context object) but the new context still shares this
    /// machine's intrinsic objects and prototype graph with the outer
    /// environment. `Object`, `Array`, `Object.prototype`, and similar builtins
    /// are identical across contexts, so guest code can mutate shared objects
    /// such as `Object.prototype`. This is not a separate realm and is not a
    /// security boundary.
    context_global: Option<Value>,
    last_completion: Option<Value>,
    /// Frame depths owned by native-to-runtime callback evaluations. A throw
    /// crossing this boundary returns to the native caller so the enclosing
    /// bytecode instruction resolves it at its own program counter.
    callback_boundaries: Vec<usize>,
    generator_boundaries: Vec<usize>,
    pending_generator_resume: Option<GeneratorResume>,
    async_boundaries: Vec<usize>,
    pending_async_suspend: Option<(Value, SuspendedActivation)>,
    microtasks: VecDeque<QueuedMicrotask>,
    /// Every pending `Atomics.waitAsync`, by the id in its `Waiter::Async`.
    async_waiters: BTreeMap<u64, intrinsics::builtins::atomics::AsyncWaiter>,
    next_async_waiter: u64,
    finalization_cleanup_queue: VecDeque<Value>,
    microtask_drain_active: bool,
    next_timer_id: Option<u64>,
    next_timer_sequence: Option<u64>,
    next_timer_generation: Option<u64>,
    timers: BTreeMap<u64, TimerRecord>,
    ready_timers: BTreeSet<(u64, u64)>,
    timer_watermark: Option<u64>,
    timer_checkpoint_active: bool,
    intrinsics: intrinsics::Intrinsics<H>,
    current_builtin_id: Option<intrinsics::BuiltinId>,
    current_new_target: Value,
    /// Cached heap index of the well-known `Symbol.hasInstance` symbol, used
    /// by `instance_of` to consult a user-defined `@@hasInstance` handler.
    /// Resolved lazily on the first `instanceof` so the hot common path pays
    /// only the single property lookup the spec requires.
    has_instance_symbol: Option<u32>,
    registry: ModuleRegistry,
    /// First machine-wide module ID reserved for host-compiled script modules.
    dynamic_base: usize,
    /// The last global a read found no binding for, which names it in a report.
    missing_global: Option<EcmaString>,
    /// Host-compiled programs retained for the machine lifetime so their
    /// closures remain executable after the originating Script object dies.
    dynamic: Vec<DynamicModule>,
    /// Intrinsic array (permanent GC root) retaining one frozen template
    /// object per tagged-template bytecode site. Element offsets are tracked in
    /// `template_sites`, so no cached Value lives only in Rust machine state.
    template_objects: Value,
    /// (module, function, pc) -> element offset into `template_objects`.
    template_sites: BTreeMap<(u32, u32, u32), usize>,
    /// Cooperative cancellation signal checked at fuel, microtask, timer, and
    /// quiescence checkpoints. A fresh token (never cancelled) preserves the
    /// behavior of the existing fresh-token wrapper APIs.
    cancel: CancellationToken,
    atoms: AtomTable,
    shapes: ShapeTable,
    property_sites: BTreeMap<(ModuleId, FunctionId), FunctionSites>,
}

#[derive(Clone, Debug)]
struct DynamicModule {
    program: Arc<Program<Verified>>,
    bytes: usize,
}

#[derive(Clone, Debug, Default)]
struct ModuleRegistry {
    modules: Vec<ModuleInstance>,
    cells: Vec<Cell>,
    external: BTreeMap<EcmaString, ExternalModuleInstance>,
    /// Canonical program module-name → [`ModuleId`] for bundled-local dynamic
    /// resolution. Keys are owned [`EcmaString`] values from program constants,
    /// so this table is rebuilt per instantiation and is not a GC root set.
    local_modules: BTreeMap<EcmaString, ModuleId>,
}

#[derive(Clone, Debug)]
struct ExternalModuleInstance {
    namespace: Value,
    exports: BTreeMap<EcmaString, ExternalExport>,
    internals: BTreeMap<&'static str, Value>,
}

#[derive(Clone, Copy, Debug)]
struct ExternalExport {
    value: Value,
    cell: Option<CellId>,
}

#[derive(Clone, Debug)]
struct ModuleInstance {
    binding_cells: Vec<Option<CellId>>,
    constant_cells: Vec<Option<CellId>>,
    /// Whether a constant names an import. One cell can have two names: a module
    /// that imports its own export reads the cell that it writes.
    constant_is_import: Vec<bool>,
    namespace: Option<Value>,
    state: ModuleState,
    import_meta: Option<Value>,
}

#[derive(Clone, Debug)]
enum ModuleState {
    Unevaluated,
    /// On the current synchronous module-DFS stack; re-entering it is a
    /// static cycle back-edge and never waits.
    Evaluating,
    /// Awaiting asynchronous progress off-stack: one shared evaluation record
    /// and Promise exist for the module's lifetime, and `pending_deps` counts
    /// static dependencies whose attached reactions have not fired yet. The
    /// record and Promise are allocated lazily, only when the entry suspends
    /// or a static dependency is already pending.
    EvaluatingAsync {
        record: Value,
        promise: Value,
        pending_deps: usize,
    },
    Evaluated(Result<(), RuntimeError>),
}

#[derive(Clone, Debug)]
pub(crate) enum ModuleEvaluation {
    Cycle,
    Evaluated(Result<(), RuntimeError>),
    Ready(Vec<ModuleId>),
}

/// The outcome of starting one module entry function.
#[derive(Clone, Debug)]
enum ModuleStart {
    /// The entry settled synchronously (fully sync entry, or an async entry
    /// whose first turn already reached Return/Throw).
    Settled(Result<Execution, RuntimeError>),
    /// The entry suspended (or its static dependencies are still pending);
    /// completion arrives through the shared evaluation record.
    Pending(ModulePending),
    /// The module was already evaluated, or re-entered on the same DFS stack
    /// (a static cycle back-edge); nothing ran and nothing is owed.
    Cached,
}

/// One module's lazily created evaluation record and shared Promise. The
/// record drives the activation; the Promise is handed to every pure dynamic
/// import executed while the module is in flight, so concurrent importers
/// observe the identical Promise object.
#[derive(Clone, Copy, Debug)]
struct ModulePending {
    record: Value,
    promise: Value,
}

/// The outcome of a pure dynamic `import()` edge: the raw namespace for a
/// settled or same-stack cyclic target, the shared evaluation Promise for an
/// in-flight async target, or the target's stored failure to rethrow at this
/// import site.
enum DynamicImport {
    Ready(Value),
    Pending(Value),
    Failed(RuntimeError),
}

/// Runtime-only dynamic import resolution deliberately retains the external
/// specifier rather than an edge id, because expression imports need no edge.
enum DynamicImportTarget {
    Local(ModuleId),
    External(EcmaString),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ImportTarget {
    Local(ModuleId),
    External(EdgeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CellId(usize);

#[derive(Clone, Copy, Debug)]
struct Cell {
    value: Value,
}

pub fn run<H: Host>(
    program: &Program<Verified>,
    host: &mut H,
    limits: &Limits,
) -> Result<ExecutionOutcome, RuntimeError> {
    Machine::new(program, host, limits.clone())
        .run()
        .map(|execution| execution.outcome)
}

impl<'a, H: Host> Machine<'a, H> {
    #[must_use]
    pub fn new(program: &'a Program<Verified>, host: &'a mut H, limits: Limits) -> Self {
        let module = &program
            .module(program.entry())
            .expect("verified program entry exists")
            .code;
        Self::build(
            Some(program),
            module,
            host,
            limits,
            CancellationToken::new(),
        )
    }

    /// Constructs a machine bound to a caller-supplied cancellation token.
    /// The token is checked at fuel, microtask, timer, and quiescence
    /// checkpoints; triggering it aborts execution with
    /// [`RuntimeErrorKind::Cancelled`].
    #[must_use]
    pub fn new_with_cancel(
        program: &'a Program<Verified>,
        host: &'a mut H,
        limits: Limits,
        cancel: CancellationToken,
    ) -> Self {
        let module = &program
            .module(program.entry())
            .expect("verified program entry exists")
            .code;
        Self::build(Some(program), module, host, limits, cancel)
    }

    fn build(
        program: Option<&'a Program<Verified>>,
        module: &'a Module<Verified>,
        host: &'a mut H,
        limits: Limits,
        cancel: CancellationToken,
    ) -> Self {
        let entry = module.entry().get() as usize;
        let module_id = program.map_or(ModuleId::new(0), Program::entry);
        let frame = Frame::new(
            &module.functions()[entry],
            ActivationRequest {
                target: RuntimeFunction {
                    module: module_id,
                    function: FunctionId::new(entry as u32),
                },
                captures: &[],
                context: None,
                this_value: Value::UNDEFINED,
                new_target: Value::UNDEFINED,
                arguments: &[],
                return_to: None,
            },
        );
        let live_registers = frame.registers.len();
        let mut heap = Heap::default();
        let mut atoms = AtomTable::default();
        let mut shapes = ShapeTable::new();
        let timers_available = host.timers().is_some();
        let script_compiler = host.script_compiler().is_some();
        let mut intrinsics = intrinsics::Intrinsics::<H>::initialize(
            &mut heap,
            &mut atoms,
            &mut shapes,
            timers_available,
            script_compiler,
        );
        let global_object = intrinsics
            .global("globalThis")
            .expect("host objects install globalThis");
        let installed_external = external_modules::install(
            &mut heap,
            &mut atoms,
            &mut shapes,
            &mut intrinsics.builtins,
            intrinsics.object_prototype,
            script_compiler,
        );
        if let Some(program) = program {
            preintern_program_names(&mut atoms, program);
        } else {
            preintern_module_code(&mut atoms, module);
        }
        let vm_context_marker = intrinsics::push(
            &mut heap,
            HeapEntry::PrivateName {
                description: EcmaString::encode("vm context"),
            },
        );
        let template_objects = intrinsics::push(
            &mut heap,
            HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&[]),
                elements: Vec::new(),
                properties: PropertyMap::default(),
                prototype: None,
                extensible: true,
                length_writable: true,
            },
        );
        let argv_text = host.argv().to_vec();
        let argv_values: Vec<Value> = argv_text
            .into_iter()
            .map(|text| intrinsics::push(&mut heap, HeapEntry::String(EcmaString::encode(&text))))
            .collect();
        let process = intrinsics
            .global("process")
            .expect("host objects install process");
        let Some(Decoded::HeapRef(process_id)) = process.decode() else {
            unreachable!("process is an engine object");
        };
        let process_index = process_id.slot() as usize - 1;
        let HeapEntry::Object { properties, .. } = &heap[process_index] else {
            unreachable!("process is an ordinary object");
        };
        let Some(Property::Data { value: argv, .. }) =
            properties.get_ascii(&shapes, &atoms, "argv")
        else {
            unreachable!("process owns argv");
        };
        let Some(Decoded::HeapRef(argv_id)) = argv.decode() else {
            unreachable!("process.argv is an engine array");
        };
        let argv_index = argv_id.slot() as usize - 1;
        install_element_vector(&mut heap, argv_index, argv_values);
        let intrinsic_slots = heap.len();
        heap.mark_old_prefix(intrinsic_slots);
        let slot_bytes = vec![0; intrinsic_slots];
        let intrinsic_slot_credits = vec![0; intrinsic_slots];
        let fuel = limits.fuel;
        Self {
            program,
            module,
            host,
            gc: gc::GcState::new(&limits),
            limits,
            native_roots: Vec::new(),
            regexp_cache: Vec::new(),
            array_join_stack: Vec::new(),
            kept_alive: Vec::new(),
            builtin_temporaries: Vec::new(),
            callback_results: Vec::new(),
            results_floor: 0,
            in_builtin: false,
            running_jobs: Vec::new(),
            fuel,
            frames: vec![frame],
            heap,
            slot_bytes,
            intrinsic_slot_credits,
            machine_bytes: 0,
            intrinsic_slots,
            vacant_count: 0,
            heap_bytes: 0,
            live_registers,
            native_depth: 0,
            stack_base: stack_position(),
            last_completion: None,
            callback_boundaries: Vec::new(),
            generator_boundaries: Vec::new(),
            pending_generator_resume: None,
            async_boundaries: Vec::new(),
            pending_async_suspend: None,
            microtasks: VecDeque::new(),
            async_waiters: BTreeMap::new(),
            next_async_waiter: 0,
            finalization_cleanup_queue: VecDeque::new(),
            microtask_drain_active: false,
            next_timer_id: Some(1),
            next_timer_sequence: Some(0),
            next_timer_generation: Some(0),
            timers: BTreeMap::new(),
            ready_timers: BTreeSet::new(),
            timer_watermark: None,
            timer_checkpoint_active: false,
            global_object,
            vm_context_marker,
            context_global: None,
            registry: ModuleRegistry {
                external: installed_external
                    .into_iter()
                    .map(|module| {
                        let mut exports: BTreeMap<_, _> = module
                            .exports
                            .into_iter()
                            .map(|(name, value)| (name, ExternalExport { value, cell: None }))
                            .collect();
                        exports.insert(
                            EcmaString::encode("default"),
                            ExternalExport {
                                value: module.namespace,
                                cell: None,
                            },
                        );
                        (
                            module.specifier,
                            ExternalModuleInstance {
                                namespace: module.namespace,
                                exports,
                                internals: module.internals,
                            },
                        )
                    })
                    .collect(),
                ..ModuleRegistry::default()
            },
            dynamic_base: program.map_or(1, |program| program.modules().len()),
            dynamic: Vec::new(),
            missing_global: None,
            template_objects,
            template_sites: BTreeMap::new(),
            current_builtin_id: None,
            current_new_target: Value::UNDEFINED,
            has_instance_symbol: None,
            intrinsics,
            cancel,
            atoms,
            shapes,
            property_sites: BTreeMap::new(),
        }
    }

    /// Evaluates the program, drives the automatic event loop to quiescence,
    /// and returns the synchronous [`Execution`] snapshot taken right after
    /// evaluation. Callbacks may mutate globals and append host output, but
    /// the returned value and entry register snapshot stay those of the
    /// synchronous evaluation.
    pub fn run(mut self) -> Result<Execution, RuntimeError> {
        let execution = match self.evaluate() {
            Ok(execution) => execution,
            Err(mut error) => {
                self.enrich_uncaught_throw(&mut error);
                return Err(error);
            }
        };
        if let Err(mut error) = self.run_to_quiescence() {
            self.enrich_uncaught_throw(&mut error);
            return Err(error);
        }
        Ok(execution)
    }

    /// Evaluates the program without draining queued microtasks.
    ///
    /// When the entry module suspends on top-level await, this drives the
    /// automatic event loop — microtask checkpoints first, then one timer
    /// turn at a time — only until the entry's evaluation Promise settles,
    /// and returns the entry [`Execution`] before any unrelated later timer.
    /// Timers still live at settlement stay queued for [`Self::run_to_quiescence`].
    /// An entry whose awaited work enqueues nothing and leaves no live timer
    /// fails with [`RuntimeErrorKind::ModuleEvaluationStalled`].
    ///
    /// Otherwise the machine remains available for an explicit
    /// [`Self::drain_microtasks`] checkpoint.
    pub fn evaluate(&mut self) -> Result<Execution, RuntimeError> {
        #[cfg(test)]
        self.gc.stress_from_environment();
        let result = (|| {
            if let Some(program) = self.program {
                let entry = program.entry();
                self.frames.clear();
                self.live_registers = 0;
                self.instantiate_modules()?;
                return self.evaluate_instantiated_module(entry);
            }
            Ok(self
                .run_loop(0)?
                .expect("the entry frame completes before the run loop stops"))
        })();
        self.clear_kept_alive_for_job();
        result
    }

    /// Evaluates one module of an already-instantiated program and returns
    /// its entry [`Execution`]. Runs the module DFS (synchronous fast paths
    /// stay synchronous) and, only when the entry suspends on top-level
    /// await, drives the bounded outer loop until the entry's evaluation
    /// Promise settles. Never calls `instantiate_modules` or
    /// `run_to_quiescence`: the native backend delegates whole async static
    /// graphs here, and `run` drains to quiescence afterwards.
    pub(crate) fn evaluate_instantiated_module(
        &mut self,
        module: ModuleId,
    ) -> Result<Execution, RuntimeError> {
        match self.evaluate_module(module)? {
            ModuleStart::Settled(result) => result,
            ModuleStart::Pending(pending) => self.drive_entry_to_settlement(pending, module),
            ModuleStart::Cached => Err(self.program_error(
                module,
                RuntimeErrorKind::InvalidVerifiedProgram {
                    module,
                    instruction: Instruction::Halt,
                },
            )),
        }
    }

    /// Drives the outer event loop for one pending root entry: microtasks run
    /// to emptiness, then one expired timer per turn, until the entry's
    /// evaluation Promise settles. The settlement check runs after every full
    /// microtask checkpoint and before any timer wait, so no wakeup is lost
    /// and no timer beyond the settling turn fires here. A never-settling
    /// entry with no live timer is a stall, not a hang.
    fn drive_entry_to_settlement(
        &mut self,
        pending: ModulePending,
        entry: ModuleId,
    ) -> Result<Execution, RuntimeError> {
        self.with_native_roots(&[pending.record, pending.promise], |machine| {
            machine.settle_pending_entry(pending, entry)
        })
    }

    fn settle_pending_entry(
        &mut self,
        pending: ModulePending,
        entry: ModuleId,
    ) -> Result<Execution, RuntimeError> {
        loop {
            self.drain_microtasks_automatic()?;
            if self
                .promise_is_settled(pending.promise)
                .map_err(|kind| self.program_error(entry, kind))?
            {
                break;
            }
            if !self.has_pending_timers() {
                return Err(self.program_error(
                    entry,
                    RuntimeErrorKind::ModuleEvaluationStalled { module: entry },
                ));
            }
            match self.wait_for_timer_expiry_state()? {
                TimerWait::Ready => {}
                TimerWait::Stale => continue,
                TimerWait::Idle => {
                    return Err(
                        self.checkpoint_error(RuntimeErrorKind::TimerProviderFailure {
                            message: "the timer provider lost a live machine timer".to_owned(),
                        }),
                    );
                }
            }
            let run = self.run_one_expired_timer()?;
            if let Some(exception) = run.uncaught.into_iter().next() {
                return Err(self.checkpoint_error(RuntimeErrorKind::UncaughtThrow {
                    value: exception.value,
                    origin: exception.origin,
                    constructor_name: None,
                    message: None,
                }));
            }
        }
        self.take_async_module_completion(pending.record, entry)
            .map_err(|kind| self.program_error(entry, kind))?
    }

    /// Runs at most one expired live timer callback.
    ///
    /// This explicit checkpoint never drains microtasks. Expiry reports only
    /// advance a monotonic watermark; visible delivery is ordered by the
    /// machine-owned `(deadline, sequence)` key.
    pub fn run_one_expired_timer(&mut self) -> Result<TimerRun, RuntimeError> {
        if self.timer_checkpoint_active {
            return Err(self.checkpoint_error(RuntimeErrorKind::TimerCheckpointReentry));
        }
        self.timer_checkpoint_active = true;
        let result = (|| {
            self.poll_timer_expiries()
                .map_err(|kind| self.checkpoint_error(kind))?;
            let Some(order) = self.ready_timers.first().copied() else {
                return Ok(TimerRun::default());
            };
            let Some(id) = self.timers.iter().find_map(|(id, timer)| {
                ((timer.deadline_ms, timer.sequence) == order).then_some(*id)
            }) else {
                return Err(self.checkpoint_error(RuntimeErrorKind::InvalidValue {
                    value: Value::UNDEFINED,
                }));
            };
            // Preserve both the ready key and live record when fuel is empty.
            self.consume_fuel(1)
                .map_err(|kind| self.checkpoint_error(kind))?;
            self.collect_if_pending();
            self.ready_timers.remove(&order);
            let timer = self
                .timers
                .get(&id)
                .expect("ready timer remains live until after fuel charging")
                .clone();
            let mut report = TimerRun {
                executed: 1,
                uncaught: Vec::new(),
            };
            let callback_result = self.with_active_context(timer.context, |machine| {
                machine.call_value(timer.callback, timer.handle, &timer.arguments)
            });
            self.clear_kept_alive_for_job();
            match callback_result {
                Ok(_) => {}
                Err(EvalFailure::Runtime(kind)) => {
                    self.timers.remove(&id);
                    return Err(self.checkpoint_error(kind));
                }
                Err(failure) => {
                    let rejection = self.promise_rejection_value(failure);
                    let (value, origin) = match rejection {
                        Ok(pair) => pair,
                        Err(EvalFailure::Runtime(kind)) => {
                            self.timers.remove(&id);
                            return Err(self.checkpoint_error(kind));
                        }
                        Err(_) => {
                            self.timers.remove(&id);
                            return Err(self.checkpoint_error(RuntimeErrorKind::InvalidValue {
                                value: timer.callback,
                            }));
                        }
                    };
                    report.uncaught.try_reserve(1).map_err(|_| {
                        self.checkpoint_error(RuntimeErrorKind::HeapByteLimitExceeded {
                            limit: self.limits.max_heap_bytes,
                        })
                    })?;
                    report.uncaught.push(CallbackException { value, origin });
                }
            }
            // Re-arm a repeating interval with the same id and handle so
            // JavaScript retains its original Timeout reference. A new
            // sequence orders the next fire behind any timer armed during the
            // callback. A provider failure here is fatal to the checkpoint.
            if self.timers.remove(&id).is_some()
                && let Some(delay_ms) = timer.interval_delay
            {
                let sequence = self
                    .next_timer_sequence
                    .take()
                    .ok_or(
                        self.checkpoint_error(RuntimeErrorKind::TimerCapacityExceeded {
                            limit: self.limits.max_timers,
                        }),
                    )?;
                self.next_timer_sequence = sequence.checked_add(1);
                let generation = self
                    .next_timer_generation
                    .take()
                    .ok_or(
                        self.checkpoint_error(RuntimeErrorKind::TimerCapacityExceeded {
                            limit: self.limits.max_timers,
                        }),
                    )?;
                self.next_timer_generation = generation.checked_add(1);
                let deadline_ms = match self.host.timers() {
                    Some(provider) => provider.schedule(id, delay_ms).map_err(|error| {
                        self.checkpoint_error(RuntimeErrorKind::TimerProviderFailure {
                            message: error.to_string(),
                        })
                    })?,
                    None => {
                        return Err(self.checkpoint_error(
                            RuntimeErrorKind::TimerProviderFailure {
                                message: "timer capability is unavailable".to_owned(),
                            },
                        ));
                    }
                };
                if deadline_ms <= self.timer_watermark.unwrap_or(0) {
                    self.ready_timers.insert((deadline_ms, sequence));
                }
                let handle_index = match self.runtime_slot(timer.handle) {
                    Ok(Some(index)) => index,
                    Ok(None) => {
                        return Err(self.checkpoint_error(RuntimeErrorKind::InvalidValue {
                            value: timer.handle,
                        }));
                    }
                    Err(kind) => return Err(self.checkpoint_error(kind)),
                };
                match &mut self.heap[handle_index] {
                    HeapEntry::Timeout {
                        generation: handle_generation,
                        ..
                    } => {
                        *handle_generation = generation;
                    }
                    _ => {
                        return Err(self.checkpoint_error(RuntimeErrorKind::InvalidValue {
                            value: timer.handle,
                        }));
                    }
                }
                self.timers.insert(
                    id,
                    TimerRecord {
                        callback: timer.callback,
                        arguments: timer.arguments,
                        handle: timer.handle,
                        context: timer.context,
                        deadline_ms,
                        sequence,
                        generation,
                        interval_delay: Some(delay_ms),
                    },
                );
            }
            Ok(report)
        })();
        self.timer_checkpoint_active = false;
        result
    }

    /// Blocks in the host provider until an expiry report is available.
    /// Returns whether at least one live timer became ready.
    fn wait_for_timer_expiry_state(&mut self) -> Result<TimerWait, RuntimeError> {
        if self.timer_checkpoint_active {
            return Err(self.checkpoint_error(RuntimeErrorKind::TimerCheckpointReentry));
        }
        if !self.ready_timers.is_empty() {
            return Ok(TimerWait::Ready);
        }
        self.check_cancel()
            .map_err(|kind| self.checkpoint_error(kind))?;
        let cancel = self.cancel.clone();
        self.timer_checkpoint_active = true;
        let result = (|| {
            let wakeup = match self.host.timers() {
                Some(provider) => provider.wait_expired(&cancel),
                None => return Ok(TimerWait::Idle),
            }
            .map_err(|error| {
                self.checkpoint_error(RuntimeErrorKind::TimerProviderFailure {
                    message: error.to_string(),
                })
            })?;
            let Some(wakeup) = wakeup else {
                return if cancel.is_cancelled() {
                    Err(self.checkpoint_error(RuntimeErrorKind::Cancelled))
                } else {
                    Ok(TimerWait::Idle)
                };
            };
            self.promote_timer_wakeup(wakeup);
            Ok(if self.ready_timers.is_empty() {
                TimerWait::Stale
            } else {
                TimerWait::Ready
            })
        })();
        self.timer_checkpoint_active = false;
        result
    }

    /// Public convenience wrapper around [`Self::wait_for_timer_expiry_state`].
    ///
    /// Returns `true` if at least one live timer became ready, `false` if the
    /// provider reports an empty or stale pending set, and aborts on provider
    /// failure or cancellation.
    pub fn wait_for_timer_expiry(&mut self) -> Result<bool, RuntimeError> {
        match self.wait_for_timer_expiry_state()? {
            TimerWait::Ready => Ok(true),
            TimerWait::Stale | TimerWait::Idle => Ok(false),
        }
    }

    /// Returns whether any machine-owned live timer remains.
    #[must_use]
    pub fn has_pending_timers(&self) -> bool {
        !self.timers.is_empty()
    }

    /// Drives the automatic event loop to quiescence after synchronous
    /// evaluation.
    ///
    /// Drains every queued microtask first. While a live machine timer
    /// remains, waits for one deadline to become ready, runs exactly one
    /// timer callback, and drains microtasks again. A timer created by a
    /// callback therefore waits for a later timer turn. The first uncaught
    /// `queueMicrotask` or timer callback exception stops the loop and becomes
    /// [`RuntimeErrorKind::UncaughtThrow`]; a timer exception is converted
    /// before any later drain, so its queued microtasks and later timers stay
    /// pending. Promise handler throws settle their derived promises and never
    /// abort the loop. Fatal runtime failures propagate unchanged.
    ///
    /// A stale report retries. A missing report or timer capability while a
    /// machine timer remains fails with [`RuntimeErrorKind::TimerProviderFailure`]
    /// instead of spinning. Existing fuel bounds recursive jobs and timers;
    /// exhausted work fails with [`RuntimeErrorKind::FuelExhausted`].
    pub(crate) fn run_to_quiescence(&mut self) -> Result<(), RuntimeError> {
        loop {
            self.drain_microtasks_automatic()?;
            self.check_cancel()
                .map_err(|kind| self.checkpoint_error(kind))?;
            if self.has_pending_timers() {
                match self.wait_for_timer_expiry_state()? {
                    TimerWait::Ready => {}
                    TimerWait::Stale => continue,
                    TimerWait::Idle => {
                        return Err(self.checkpoint_error(
                            RuntimeErrorKind::TimerProviderFailure {
                                message: "the timer provider lost a live machine timer".to_owned(),
                            },
                        ));
                    }
                }
                self.check_cancel()
                    .map_err(|kind| self.checkpoint_error(kind))?;
                let run = self.run_one_expired_timer()?;
                if let Some(exception) = run.uncaught.into_iter().next() {
                    return Err(self.checkpoint_error(RuntimeErrorKind::UncaughtThrow {
                        value: exception.value,
                        origin: exception.origin,
                        constructor_name: None,
                        message: None,
                    }));
                }
                continue;
            }
            return Ok(());
        }
    }

    pub(crate) fn schedule_timeout(
        &mut self,
        callback: Value,
        delay_ms: u32,
        arguments: Vec<Value>,
    ) -> Result<Value, EvalFailure> {
        self.schedule_timer(callback, delay_ms, arguments, None)
    }

    pub(crate) fn schedule_interval(
        &mut self,
        callback: Value,
        delay_ms: u32,
        arguments: Vec<Value>,
    ) -> Result<Value, EvalFailure> {
        self.schedule_timer(callback, delay_ms, arguments, Some(delay_ms))
    }

    fn schedule_timer(
        &mut self,
        callback: Value,
        delay_ms: u32,
        arguments: Vec<Value>,
        interval_delay: Option<u32>,
    ) -> Result<Value, EvalFailure> {
        if self.timers.len() >= self.limits.max_timers {
            return Err(EvalFailure::Runtime(
                RuntimeErrorKind::TimerCapacityExceeded {
                    limit: self.limits.max_timers,
                },
            ));
        }
        let id = self.next_timer_id.take().ok_or(EvalFailure::Runtime(
            RuntimeErrorKind::TimerCapacityExceeded {
                limit: self.limits.max_timers,
            },
        ))?;
        self.next_timer_id = id.checked_add(1);
        let sequence = self.next_timer_sequence.take().ok_or(EvalFailure::Runtime(
            RuntimeErrorKind::TimerCapacityExceeded {
                limit: self.limits.max_timers,
            },
        ))?;
        self.next_timer_sequence = sequence.checked_add(1);
        let generation = self
            .next_timer_generation
            .take()
            .ok_or(EvalFailure::Runtime(
                RuntimeErrorKind::TimerCapacityExceeded {
                    limit: self.limits.max_timers,
                },
            ))?;
        self.next_timer_generation = generation.checked_add(1);
        let deadline_ms = self
            .host
            .timers()
            .ok_or(EvalFailure::Runtime(
                RuntimeErrorKind::TimerProviderFailure {
                    message: "timer capability is unavailable".to_owned(),
                },
            ))?
            .schedule(id, delay_ms)
            .map_err(|error| {
                EvalFailure::Runtime(RuntimeErrorKind::TimerProviderFailure {
                    message: error.to_string(),
                })
            })?;
        let handle = match self.allocate(HeapEntry::Timeout {
            id,
            generation,
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.object_prototype),
            extensible: true,
        }) {
            Ok(handle) => handle,
            Err(kind) => {
                if let Some(provider) = self.host.timers() {
                    let _ = provider.cancel(id);
                }
                return Err(EvalFailure::Runtime(kind));
            }
        };
        self.timers.insert(
            id,
            TimerRecord {
                callback,
                arguments,
                handle,
                context: self.context_global,
                deadline_ms,
                sequence,
                generation,
                interval_delay,
            },
        );
        Ok(handle)
    }

    pub(crate) fn clear_timeout(&mut self, handle: Value) -> Result<(), EvalFailure> {
        let (id, request_generation) = match handle.decode() {
            Some(Decoded::Int32(raw)) if (raw as i32) > 0 => (u64::from(raw), None),
            Some(Decoded::Number(number))
                if number.is_finite()
                    && number > 0.0
                    && number.fract() == 0.0
                    && number < u64::MAX as f64 =>
            {
                (number as u64, None)
            }
            Some(Decoded::HeapRef(_)) => {
                match self.runtime_slot(handle).ok().flatten().and_then(|index| {
                    match &self.heap[index] {
                        HeapEntry::Timeout { id, generation, .. } => Some((*id, Some(*generation))),
                        _ => None,
                    }
                }) {
                    Some(pair) => pair,
                    None => return Ok(()),
                }
            }
            _ => return Ok(()),
        };
        let Some(live_record) = self.timers.get(&id) else {
            return Ok(());
        };
        // A bare number comes from a script, and an internal timeout is not its
        // to cancel. Only the runtime holds that timer's handle.
        if request_generation.is_none()
            && live_record.callback == self.intrinsics.builtins.wait_async_timeout()
        {
            return Ok(());
        }
        if let Some(request_generation) = request_generation
            && live_record.generation != request_generation
        {
            return Ok(());
        }
        let record = self.timers.remove(&id).unwrap();
        self.ready_timers
            .remove(&(record.deadline_ms, record.sequence));
        if let Some(provider) = self.host.timers() {
            provider.cancel(id).map_err(|error| {
                EvalFailure::Runtime(RuntimeErrorKind::TimerProviderFailure {
                    message: error.to_string(),
                })
            })?;
        }
        Ok(())
    }

    fn poll_timer_expiries(&mut self) -> Result<(), RuntimeErrorKind> {
        let mut wakeups = Vec::new();
        let Some(provider) = self.host.timers() else {
            return Ok(());
        };
        provider.poll_expired(&mut wakeups).map_err(|error| {
            RuntimeErrorKind::TimerProviderFailure {
                message: error.to_string(),
            }
        })?;
        // One live report authorizes every earlier deadline. Collapse a host
        // batch to one watermark instead of rescanning all live timers per report.
        if let Some(wakeup) = wakeups
            .into_iter()
            .filter(|wakeup| self.timers.contains_key(&wakeup.id))
            .max_by_key(|wakeup| wakeup.deadline_ms)
        {
            self.promote_timer_wakeup(wakeup);
        }
        Ok(())
    }

    fn promote_timer_wakeup(&mut self, wakeup: TimerWakeup) {
        // Unknown IDs are stale cancellation races and carry no authority to
        // advance the watermark.
        if !self.timers.contains_key(&wakeup.id) {
            return;
        }
        let watermark = self.timer_watermark.map_or(wakeup.deadline_ms, |current| {
            current.max(wakeup.deadline_ms)
        });
        self.timer_watermark = Some(watermark);
        for timer in self.timers.values() {
            if timer.deadline_ms <= watermark {
                self.ready_timers
                    .insert((timer.deadline_ms, timer.sequence));
            }
        }
    }

    /// Runs queued microtasks in FIFO order until the queue is empty.
    ///
    /// Jobs queued by another job run in the same checkpoint. Promise callback
    /// throws settle their derived promises. Throws from `queueMicrotask`
    /// callbacks are returned in [`MicrotaskDrain::uncaught`].
    pub fn drain_microtasks(&mut self) -> Result<MicrotaskDrain, RuntimeError> {
        self.drain_microtasks_core(MicrotaskExceptionPolicy::CollectAndContinue)
    }

    /// Automatic drain for the event loop: the first uncaught `queueMicrotask`
    /// callback exception stops the checkpoint and becomes
    /// [`RuntimeErrorKind::UncaughtThrow`], leaving later jobs queued. All
    /// other semantics match the public manual checkpoint.
    fn drain_microtasks_automatic(&mut self) -> Result<(), RuntimeError> {
        let report = self.drain_microtasks_core(MicrotaskExceptionPolicy::StopAtFirst)?;
        let Some(exception) = report.uncaught.into_iter().next() else {
            return Ok(());
        };
        Err(self.checkpoint_error(RuntimeErrorKind::UncaughtThrow {
            value: exception.value,
            origin: exception.origin,
            constructor_name: None,
            message: None,
        }))
    }

    /// Shared microtask checkpoint. Both drains share the reentry guard,
    /// fuel-before-pop charging, FIFO execution, Promise reaction semantics,
    /// fatal-error propagation, and flag cleanup. Manual drains collect every
    /// callback exception and continue; automatic drains stop after the first,
    /// leaving the rest of the queue untouched. The exceptionless path performs
    /// no allocation.
    fn drain_microtasks_core(
        &mut self,
        exception_policy: MicrotaskExceptionPolicy,
    ) -> Result<MicrotaskDrain, RuntimeError> {
        if self.microtask_drain_active {
            return Err(self.checkpoint_error(RuntimeErrorKind::MicrotaskDrainReentry));
        }
        self.microtask_drain_active = true;
        let result = (|| {
            let mut report = MicrotaskDrain::default();
            loop {
                self.schedule_finalization_cleanup_jobs()
                    .map_err(|kind| self.checkpoint_error(kind))?;
                if self.microtasks.front().is_none() {
                    break;
                }
                self.consume_fuel(1)
                    .map_err(|kind| self.checkpoint_error(kind))?;
                self.collect_if_pending();
                let queued = self
                    .microtasks
                    .pop_front()
                    .expect("the queued microtask remains present after fuel charging");
                self.refund_machine(queued.retained_bytes);
                report.executed = report.executed.saturating_add(1);
                let is_finalization_cleanup =
                    matches!(&queued.job, MicrotaskJob::FinalizationCleanup { .. });
                self.running_jobs.push(queued.job.clone());
                let job_result = self.execute_microtask_job(queued.job);
                self.running_jobs.pop();
                self.clear_kept_alive_for_job();
                let Some(exception) = job_result.map_err(|kind| self.checkpoint_error(kind))?
                else {
                    continue;
                };
                report.uncaught.try_reserve(1).map_err(|_| {
                    self.checkpoint_error(RuntimeErrorKind::HeapByteLimitExceeded {
                        limit: self.limits.max_heap_bytes,
                    })
                })?;
                report.uncaught.push(exception);
                if is_finalization_cleanup
                    || exception_policy == MicrotaskExceptionPolicy::StopAtFirst
                {
                    break;
                }
            }
            Ok(report)
        })();
        self.microtask_drain_active = false;
        result
    }

    fn checkpoint_error(&self, kind: RuntimeErrorKind) -> RuntimeError {
        let function = self.module.entry();
        let instruction = self.module.functions()[function.get() as usize]
            .code()
            .first()
            .copied()
            .unwrap_or(Instruction::Halt);
        RuntimeError {
            kind,
            function,
            pc: Pc::new(0),
            source: RuntimeSource {
                function_name: None,
                instruction,
            },
        }
    }

    /// Runs one popped microtask job. Promise reaction and thenable jobs
    /// settle their derived promises and never surface a callback exception;
    /// a `queueMicrotask` callback throw is classified and returned for the
    /// checkpoint to collect or stop on.
    fn execute_microtask_job(
        &mut self,
        job: MicrotaskJob,
    ) -> Result<Option<CallbackException>, RuntimeErrorKind> {
        match job {
            MicrotaskJob::Reaction {
                reaction,
                value,
                origin,
            } => {
                let context = reaction.context();
                self.with_active_context(context, |machine| {
                    machine.execute_promise_reaction(reaction, value, origin)
                })
                .map(|()| None)
            }
            MicrotaskJob::Thenable {
                promise,
                thenable,
                then,
                context,
            } => self
                .with_active_context(context, |machine| {
                    machine.execute_thenable_job(promise, thenable, then)
                })
                .map(|()| None),
            MicrotaskJob::Callback { callback, context } => self
                .with_active_context(context, |machine| {
                    machine.execute_callback_microtask(callback)
                }),
            MicrotaskJob::FinalizationCleanup { registry, context } => self
                .with_active_context(context, |machine| {
                    machine.execute_finalization_cleanup_job(registry)
                }),
        }
    }

    fn with_active_context<T>(
        &mut self,
        context: Option<Value>,
        operation: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = std::mem::replace(&mut self.context_global, context);
        let result = operation(self);
        self.context_global = previous;
        result
    }

    fn execute_callback_microtask(
        &mut self,
        callback: Value,
    ) -> Result<Option<CallbackException>, RuntimeErrorKind> {
        match self.call_value(callback, Value::UNDEFINED, &[]) {
            Ok(_) => Ok(None),
            Err(EvalFailure::Runtime(kind)) => Err(kind),
            Err(failure) => {
                let (value, origin) =
                    self.promise_rejection_value(failure)
                        .map_err(|failure| match failure {
                            EvalFailure::Runtime(kind) => kind,
                            _ => RuntimeErrorKind::InvalidValue { value: callback },
                        })?;
                Ok(Some(CallbackException { value, origin }))
            }
        }
    }

    fn execute_thenable_job(
        &mut self,
        promise: Value,
        thenable: Value,
        then: Value,
    ) -> Result<(), RuntimeErrorKind> {
        let record = self
            .create_promise_resolver(promise)
            .map_err(|failure| match failure {
                EvalFailure::Runtime(kind) => kind,
                _ => RuntimeErrorKind::InvalidValue { value: promise },
            })?;
        let (resolve_target, reject_target) = self.intrinsics.builtins.promise_resolver_targets();
        let resolve = self
            .create_promise_resolver_function(resolve_target, record)
            .map_err(|failure| match failure {
                EvalFailure::Runtime(kind) => kind,
                _ => RuntimeErrorKind::InvalidValue { value: record },
            })?;
        let reject = self
            .create_promise_resolver_function(reject_target, record)
            .map_err(|failure| match failure {
                EvalFailure::Runtime(kind) => kind,
                _ => RuntimeErrorKind::InvalidValue { value: record },
            })?;
        match self.call_value(then, thenable, &[resolve, reject]) {
            Ok(_) => Ok(()),
            Err(EvalFailure::Runtime(kind)) => Err(kind),
            Err(failure) => self
                .reject_promise_resolver_failure(record, failure)
                .map_err(|failure| match failure {
                    EvalFailure::Runtime(kind) => kind,
                    _ => RuntimeErrorKind::InvalidValue { value: record },
                }),
        }
    }

    fn execute_promise_reaction(
        &mut self,
        reaction: PromiseReaction,
        value: Value,
        origin: ThrowOrigin,
    ) -> Result<(), RuntimeErrorKind> {
        match reaction {
            PromiseReaction::Fulfilled {
                handler, derived, ..
            } => self.execute_promise_handler(
                handler,
                derived,
                value,
                origin,
                PromiseCompletion::Fulfilled,
            ),
            PromiseReaction::Rejected {
                handler, derived, ..
            } => self.execute_promise_handler(
                handler,
                derived,
                value,
                origin,
                PromiseCompletion::Rejected,
            ),
            PromiseReaction::AsyncFulfill { activation, .. } => {
                crate::vm::generator_async::resume_async_function(
                    self,
                    activation,
                    crate::vm::generator_async::AwaitSettlement::Fulfilled(value),
                )
            }
            PromiseReaction::AsyncReject { activation, .. } => {
                crate::vm::generator_async::resume_async_function(
                    self,
                    activation,
                    crate::vm::generator_async::AwaitSettlement::Rejected {
                        reason: value,
                        origin,
                    },
                )
            }
            PromiseReaction::AsyncGeneratorFulfill { generator, .. } => {
                self.resume_async_generator(generator, value, None)
            }
            PromiseReaction::AsyncGeneratorReject { generator, .. } => {
                self.resume_async_generator(generator, value, Some(origin))
            }
            PromiseReaction::ModuleDepFulfill { parent, .. } => {
                self.on_module_dep_fulfilled(parent)
            }
            PromiseReaction::ModuleDepReject { parent, .. } => {
                self.on_module_dep_rejected(parent, value, origin)
            }
            PromiseReaction::AsyncFromSyncFulfill { derived, done, .. } => {
                match self.iterator_result(value, done) {
                    Ok(result) => self.fulfill_promise(derived, result),
                    Err(EvalFailure::Runtime(kind)) => Err(kind),
                    Err(failure) => {
                        self.reject_promise_failure(derived, failure)
                            .map_err(|failure| match failure {
                                EvalFailure::Runtime(kind) => kind,
                                _ => RuntimeErrorKind::InvalidValue { value: derived },
                            })
                    }
                }
            }
            PromiseReaction::AsyncFromSyncReject {
                derived,
                sync_iterator,
                ..
            } => {
                self.close_protocol_iterator_preserving_abrupt(sync_iterator)?;
                self.reject_promise(derived, value, origin)
            }
            PromiseReaction::AsyncDisposeStep {
                stack,
                pending_error,
                capability,
                rejected,
                ..
            } => {
                let settled_error = rejected.then_some(value);
                match self.continue_async_disposal(stack, pending_error, settled_error, capability)
                {
                    Ok(()) => Ok(()),
                    Err(EvalFailure::Runtime(kind)) => Err(kind),
                    Err(failure) => {
                        self.reject_promise_failure(capability, failure)
                            .map_err(|failure| match failure {
                                EvalFailure::Runtime(kind) => kind,
                                _ => RuntimeErrorKind::InvalidValue { value: capability },
                            })
                    }
                }
            }
            PromiseReaction::DynamicImportFulfill {
                promise, target, ..
            } => {
                let namespace = self
                    .module_namespace(target, target)
                    .map_err(|error| error.kind)?;
                self.resolve_promise(promise, namespace)
            }
            PromiseReaction::DynamicImportReject { promise, .. } => {
                self.reject_promise(promise, value, origin)
            }
        }
    }

    fn execute_promise_handler(
        &mut self,
        handler: Value,
        derived: Value,
        value: Value,
        origin: ThrowOrigin,
        completion: PromiseCompletion,
    ) -> Result<(), RuntimeErrorKind> {
        if !self.is_callable(handler).map_err(|failure| match failure {
            EvalFailure::Runtime(kind) => kind,
            _ => RuntimeErrorKind::InvalidValue { value: handler },
        })? {
            return match completion {
                PromiseCompletion::Fulfilled => self.resolve_promise(derived, value),
                PromiseCompletion::Rejected => self.reject_promise(derived, value, origin),
            };
        }
        match self.call_value(handler, Value::UNDEFINED, &[value]) {
            Ok(result) => self.resolve_promise(derived, result),
            Err(EvalFailure::Runtime(kind)) => Err(kind),
            Err(failure) => self
                .reject_promise_failure(derived, failure)
                .map_err(|failure| match failure {
                    EvalFailure::Runtime(kind) => kind,
                    _ => RuntimeErrorKind::InvalidValue { value: derived },
                }),
        }
    }

    /// Counts down one fulfilled static dependency of an async-pending
    /// module. At zero the parent entry starts inline inside this reaction
    /// job; this is ordinary callback-shaped async execution (the same shape
    /// `resume_async` uses), never a nested event-loop checkpoint. A
    /// suspended entry keeps its shared pair in `state`; a settled entry
    /// writes [`ModuleState::Evaluated`] (its pair's Promise was already
    /// settled by `settle_async_step`); a fatal failure aborts the parent
    /// back to [`ModuleState::Unevaluated`] and stays fatal.
    fn on_module_dep_fulfilled(&mut self, parent: ModuleId) -> Result<(), RuntimeErrorKind> {
        let Some(pair) = self.take_module_async_pending(parent)? else {
            return Ok(());
        };
        match self.start_ready_entry(parent, Some(pair)) {
            ModuleStart::Settled(result) => {
                let step = match result {
                    Ok(execution) => Ok(AsyncStep::Return {
                        value: execution.value,
                        execution: Some(execution),
                    }),
                    Err(error) if matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }) => {
                        Ok(AsyncStep::Throw(error))
                    }
                    Err(error) => {
                        self.abort_module_evaluation(parent);
                        return Err(error.kind);
                    }
                };
                self.settle_async_step_rooted(pair.record, pair.promise, step)
                    .map_err(|failure| self.module_eval_failure(parent, failure).kind)
            }
            ModuleStart::Pending(_) => Ok(()),
            ModuleStart::Cached => unreachable!("a started entry is never cached"),
        }
    }

    /// Fails the parent without running its entry: the identical dependency
    /// throw is cached as the parent's stored failure, and the parent's
    /// shared evaluation Promise rejects with the same value.
    fn on_module_dep_rejected(
        &mut self,
        parent: ModuleId,
        value: Value,
        origin: ThrowOrigin,
    ) -> Result<(), RuntimeErrorKind> {
        let pending = match &self.registry.modules[parent.get() as usize].state {
            ModuleState::EvaluatingAsync {
                record, promise, ..
            } => ModulePending {
                record: *record,
                promise: *promise,
            },
            // The first rejection already settled or aborted the parent.
            _ => return Ok(()),
        };
        let error = self.program_error(
            parent,
            RuntimeErrorKind::UncaughtThrow {
                value,
                origin,
                constructor_name: None,
                message: None,
            },
        );
        self.store_async_module_completion(pending.record, Some(Err(error.clone())))
            .map_err(|failure| self.module_eval_failure(parent, failure).kind)?;
        self.settle_module_evaluation(parent, Err(error));
        self.reject_promise(pending.promise, value, origin)
    }

    /// Detaches an async-pending module's record/promise pair after
    /// decrementing its dependency count; `None` means a dependency already
    /// rejected the parent or its count has not reached zero.
    fn take_module_async_pending(
        &mut self,
        parent: ModuleId,
    ) -> Result<Option<ModulePending>, RuntimeErrorKind> {
        let ModuleState::EvaluatingAsync {
            record,
            promise,
            pending_deps,
        } = &mut self.registry.modules[parent.get() as usize].state
        else {
            // A sibling rejection already settled or aborted the parent.
            return Ok(None);
        };
        *pending_deps -= 1;
        let (record, promise) = (*record, *promise);
        if *pending_deps > 0 {
            return Ok(None);
        }
        Ok(Some(ModulePending { record, promise }))
    }

    /// Attaches the module dependency fulfill/reject pair to a dependency's
    /// evaluation Promise. Mirrors `await_promise`: an already-settled Promise
    /// enqueues the reaction directly at exactly one microtask tick, and the
    /// pending path charges and pushes without re-reading state, so no
    /// check-then-attach window exists.
    fn attach_module_reactions(
        &mut self,
        parent: ModuleId,
        promise: Value,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(promise)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: promise,
            }))?;
        let settled = match &self.heap[index] {
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            } => None,
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } => Some((true, *value, ThrowOrigin::Bytecode)),
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, origin },
                ..
            } => Some((false, *reason, *origin)),
            _ => {
                return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                    value: promise,
                }));
            }
        };
        if let Some((fulfilled, value, origin)) = settled {
            self.ensure_microtask_capacity(1)
                .map_err(EvalFailure::Runtime)?;
            let reaction = if fulfilled {
                PromiseReaction::ModuleDepFulfill {
                    parent,
                    context: self.context_global,
                }
            } else {
                PromiseReaction::ModuleDepReject {
                    parent,
                    context: self.context_global,
                }
            };
            self.microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                }));
            return Ok(());
        }
        self.charge_promise_reactions(index, 2)?;
        let context = self.context_global;
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("pending Promise state was checked before reaction registration");
        };
        fulfill_reactions.push(PromiseReaction::ModuleDepFulfill { parent, context });
        reject_reactions.push(PromiseReaction::ModuleDepReject { parent, context });
        Ok(())
    }

    /// Reports whether a Promise reached a terminal state. Used by the root
    /// drive loop after every full microtask checkpoint and before any timer
    /// wait, so settlement is never observed late.
    fn promise_is_settled(&self, promise: Value) -> Result<bool, RuntimeErrorKind> {
        let index = self
            .runtime_slot(promise)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: promise })?;
        match &self.heap[index] {
            HeapEntry::Promise { state, .. } => Ok(!matches!(state, PromiseState::Pending { .. })),
            _ => Err(RuntimeErrorKind::InvalidValue { value: promise }),
        }
    }

    pub(crate) fn enqueue_microtask_callback(
        &mut self,
        callback: Value,
    ) -> Result<(), EvalFailure> {
        self.ensure_microtask_capacity(1)
            .map_err(EvalFailure::Runtime)?;
        self.microtasks
            .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Callback {
                callback,
                context: self.context_global,
            }));
        Ok(())
    }

    fn ensure_microtask_capacity(&mut self, additional: usize) -> Result<(), RuntimeErrorKind> {
        if self
            .microtasks
            .len()
            .checked_add(additional)
            .is_none_or(|length| length > self.limits.max_microtasks)
        {
            return Err(RuntimeErrorKind::MicrotaskQueueLimitExceeded {
                limit: self.limits.max_microtasks,
            });
        }
        self.microtasks.try_reserve(additional).map_err(|_| {
            RuntimeErrorKind::HeapByteLimitExceeded {
                limit: self.limits.max_heap_bytes,
            }
        })
    }

    pub(crate) fn create_promise(&mut self) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::Promise {
            state: PromiseState::Pending {
                fulfill_reactions: Vec::new(),
                reject_reactions: Vec::new(),
            },
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.builtins.promise_prototype()),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn create_promise_resolver(&mut self, promise: Value) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::PromiseResolver {
            promise,
            used: false,
        })
        .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn create_promise_resolver_function(
        &mut self,
        target: Value,
        record: Value,
    ) -> Result<Value, EvalFailure> {
        let name = self
            .allocate(HeapEntry::String(EcmaString::encode("")))
            .map_err(EvalFailure::Runtime)?;
        let properties =
            intrinsics::function_properties(&mut self.atoms, &mut self.shapes, 1, name);
        self.allocate(HeapEntry::native_function(
            NativeCallable::Bound(Box::new(BoundCallable {
                target,
                this_value: Value::UNDEFINED,
                arguments: vec![record],
            })),
            properties,
            None,
        ))
        .map_err(EvalFailure::Runtime)
    }

    /// A native function that calls `target` with an undefined receiver and
    /// `arguments` prepended, as `Function.prototype.bind` would build it, but
    /// without looking up or running guest-replaceable `bind`.
    pub(crate) fn bound_native_function(
        &mut self,
        target: Value,
        arguments: Vec<Value>,
        name: &str,
    ) -> Result<Value, EvalFailure> {
        let name = self
            .allocate(HeapEntry::String(EcmaString::encode(name)))
            .map_err(EvalFailure::Runtime)?;
        let properties =
            intrinsics::function_properties(&mut self.atoms, &mut self.shapes, 0, name);
        self.allocate(HeapEntry::native_function(
            NativeCallable::Bound(Box::new(BoundCallable {
                target,
                this_value: Value::UNDEFINED,
                arguments,
            })),
            properties,
            Some(self.intrinsics.function_prototype),
        ))
        .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn resolve_promise_resolver(
        &mut self,
        record: Value,
        value: Value,
    ) -> Result<(), EvalFailure> {
        if let Some(promise) = self.use_promise_resolver(record)? {
            self.resolve_promise(promise, value)
                .map_err(EvalFailure::Runtime)?;
        }
        Ok(())
    }

    pub(crate) fn reject_promise_resolver(
        &mut self,
        record: Value,
        reason: Value,
    ) -> Result<(), EvalFailure> {
        if let Some(promise) = self.use_promise_resolver(record)? {
            self.reject_promise(promise, reason, ThrowOrigin::Bytecode)
                .map_err(EvalFailure::Runtime)?;
        }
        Ok(())
    }

    pub(crate) fn reject_promise_resolver_failure(
        &mut self,
        record: Value,
        failure: EvalFailure,
    ) -> Result<(), EvalFailure> {
        if let Some(promise) = self.use_promise_resolver(record)? {
            self.reject_promise_failure(promise, failure)?;
        }
        Ok(())
    }

    fn use_promise_resolver(&mut self, record: Value) -> Result<Option<Value>, EvalFailure> {
        let index = self
            .runtime_slot(record)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise resolver",
            }))?;
        let HeapEntry::PromiseResolver { promise, used } = &mut self.heap[index] else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise resolver",
            }));
        };
        if *used {
            return Ok(None);
        }
        *used = true;
        Ok(Some(*promise))
    }

    fn charge_promise_reactions(&mut self, index: usize, count: usize) -> Result<(), EvalFailure> {
        let bytes = std::mem::size_of::<PromiseReaction>()
            .checked_mul(count)
            .ok_or(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded {
                    limit: self.limits.max_heap_bytes,
                },
            ))?;
        self.charge_slot(index, bytes).map_err(EvalFailure::Runtime)
    }

    pub(crate) fn promise_then(
        &mut self,
        promise: Value,
        on_fulfilled: Value,
        on_rejected: Value,
    ) -> Result<Value, EvalFailure> {
        let index = self
            .runtime_slot(promise)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.prototype.then",
            }))?;
        let settled = match &self.heap[index] {
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            } => None,
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } => Some((true, *value, ThrowOrigin::Bytecode)),
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, origin },
                ..
            } => Some((false, *reason, *origin)),
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.prototype.then",
                }));
            }
        };
        let derived = self.create_promise()?;
        if let Some((fulfilled, value, origin)) = settled {
            self.ensure_microtask_capacity(1)
                .map_err(EvalFailure::Runtime)?;
            let reaction = if fulfilled {
                PromiseReaction::Fulfilled {
                    handler: on_fulfilled,
                    derived,
                    context: self.context_global,
                }
            } else {
                PromiseReaction::Rejected {
                    handler: on_rejected,
                    derived,
                    context: self.context_global,
                }
            };
            self.microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                }));
            return Ok(derived);
        }
        self.charge_promise_reactions(index, 2)?;
        let context = self.context_global;
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("pending Promise state was checked before derived allocation");
        };
        fulfill_reactions.push(PromiseReaction::Fulfilled {
            handler: on_fulfilled,
            derived,
            context,
        });
        reject_reactions.push(PromiseReaction::Rejected {
            handler: on_rejected,
            derived,
            context,
        });
        Ok(derived)
    }

    pub(crate) fn promise_resolve(&mut self, value: Value) -> Result<Value, EvalFailure> {
        if matches!(self.runtime_slot(value).map_err(EvalFailure::Runtime)?, Some(index) if matches!(self.heap[index], HeapEntry::Promise { .. }))
        {
            return Ok(value);
        }
        let promise = self.create_promise()?;
        self.resolve_promise(promise, value)
            .map_err(EvalFailure::Runtime)?;
        Ok(promise)
    }

    pub(crate) fn promise_all_with_resolve(
        &mut self,
        iterable: Value,
        resolve_method: Value,
        receiver: Value,
        capability_resolve: Value,
        capability_reject: Value,
    ) -> Result<(), EvalFailure> {
        let aggregate = self
            .allocate(HeapEntry::PromiseAll {
                resolve: capability_resolve,
                reject: capability_reject,
                values: Vec::new(),
                remaining: 1,
                settled: false,
            })
            .map_err(EvalFailure::Runtime)?;
        let iterator = match self.create_iterator(iterable, IteratorKind::Sync) {
            Ok(iterator) => iterator,
            Err(failure) => {
                self.mark_promise_all_settled(aggregate)?;
                self.call_promise_reject(capability_reject, failure)?;
                return Ok(());
            }
        };
        loop {
            let value = match self.iterator_next(iterator) {
                Ok((true, _)) => break,
                Ok((false, value)) => value,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            let index = match self.add_promise_all_element(aggregate) {
                Ok(index) => index,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            let element = match self
                .allocate(HeapEntry::PromiseAllElement {
                    aggregate,
                    index,
                    called: false,
                })
                .map_err(EvalFailure::Runtime)
            {
                Ok(element) => element,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            let fulfill_target = self.intrinsics.builtins.promise_all_target();
            let on_fulfilled = match self.create_promise_resolver_function(fulfill_target, element)
            {
                Ok(callback) => callback,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            let resolved = match self.call_value(resolve_method, receiver, &[value]) {
                Ok(resolved) => resolved,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            let then = match self.get_named_property(resolved, "then") {
                Ok(then) => then,
                Err(failure) => {
                    return self.reject_promise_all_abrupt(
                        aggregate,
                        capability_reject,
                        iterator,
                        failure,
                    );
                }
            };
            if let Err(failure) =
                self.call_value(then, resolved, &[on_fulfilled, capability_reject])
            {
                return self.reject_promise_all_abrupt(
                    aggregate,
                    capability_reject,
                    iterator,
                    failure,
                );
            }
        }
        if self.finish_promise_all(aggregate)? {
            let array = self.move_promise_all_values_to_array(aggregate)?;
            if let Err(failure) = self.call_value(capability_resolve, Value::UNDEFINED, &[array]) {
                self.call_promise_reject(capability_reject, failure)?;
            }
        }
        Ok(())
    }

    fn reject_promise_all_abrupt(
        &mut self,
        aggregate: Value,
        reject: Value,
        iterator: Value,
        failure: EvalFailure,
    ) -> Result<(), EvalFailure> {
        self.mark_promise_all_settled(aggregate)?;
        if let Err(EvalFailure::Runtime(kind)) = self.close_iterator(iterator) {
            return Err(EvalFailure::Runtime(kind));
        }
        self.call_promise_reject(reject, failure)
    }

    pub(crate) fn iterator_close_target(
        &mut self,
        iterator: Value,
    ) -> Result<Option<Value>, EvalFailure> {
        let Some(index) = self.runtime_slot(iterator).map_err(EvalFailure::Runtime)? else {
            return Ok(None);
        };
        match &self.heap[index] {
            HeapEntry::Iterator {
                state: IteratorState::Protocol { iterator, .. },
            }
            | HeapEntry::AsyncFromSync { iterator, .. } => Ok(Some(*iterator)),
            _ => Ok(None),
        }
    }

    pub(crate) fn close_iterator_raw(
        &mut self,
        iterator: Value,
    ) -> (Result<Value, EvalFailure>, bool) {
        let target = match self.iterator_close_target(iterator) {
            Ok(Some(target)) => target,
            Ok(None) => return (Ok(Value::UNDEFINED), false),
            Err(failure) => return (Err(failure), false),
        };
        let close = match self.get_named_property(target, "return") {
            Ok(close) => close,
            Err(failure) => return (Err(failure), false),
        };
        if matches!(close.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return (Ok(Value::UNDEFINED), false);
        }
        match self.is_callable(close) {
            Ok(true) => (self.call_value(close, target, &[]), true),
            Ok(false) => (
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "iterator return method is not callable",
                })),
                false,
            ),
            Err(failure) => (Err(failure), false),
        }
    }

    pub(crate) fn dispose_capture_raw(
        &mut self,
        src: Value,
        hint: DisposeHint,
    ) -> Result<(Value, u32), EvalFailure> {
        if matches!(src.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return Ok((Value::UNDEFINED, 0));
        }
        if !self.is_object(src) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "disposable resource is not an object",
            }));
        }

        let key = match hint {
            DisposeHint::Sync => {
                self.property_key_from_value(self.intrinsics.builtins.symbol_dispose())?
            }
            DisposeHint::Async => {
                self.property_key_from_value(self.intrinsics.builtins.symbol_async_dispose())?
            }
        };
        let method = self.get_property_key(src, &key)?;
        if !matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            if self.is_callable(method)? {
                return Ok((method, 1));
            }
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "disposal method is not callable",
            }));
        }
        if hint == DisposeHint::Sync {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "disposal method is not callable",
            }));
        }

        let key = self.property_key_from_value(self.intrinsics.builtins.symbol_dispose())?;
        let method = self.get_property_key(src, &key)?;
        if self.is_callable(method)? {
            Ok((method, 2))
        } else {
            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "disposal method is not callable",
            }))
        }
    }

    /// Object Environment Record `HasBinding` for a `with` binding object.
    ///
    /// Uses the realm-owned `%Symbol.unscopables%` intrinsic (never a user-global
    /// `Symbol` lookup), performs ordinary `Get`s with the correct receivers, and
    /// never caches the unscopables object or its named entry.
    pub(crate) fn with_has_binding(
        &mut self,
        object: Value,
        key: Value,
    ) -> Result<bool, EvalFailure> {
        let key = self.property_key_from_value(key)?;
        if !self.internal_has_property(object, &key)? {
            return Ok(false);
        }
        let unscopables_key =
            self.property_key_from_value(self.intrinsics.builtins.symbol_unscopables())?;
        let unscopables = self.get_property_key(object, &unscopables_key)?;
        if !self.is_object(unscopables) {
            return Ok(true);
        }
        let blocked = self.get_property_key(unscopables, &key)?;
        Ok(!self.truthy(blocked))
    }

    pub(crate) fn make_suppressed_error(
        &mut self,
        error: Value,
        suppressed: Value,
    ) -> Result<Value, EvalFailure> {
        let id = self
            .intrinsics
            .builtins
            .id_named("SuppressedError")
            .expect("SuppressedError builtin installs first");
        let mut properties = PropertyMap::default();
        for (name, value) in [("error", error), ("suppressed", suppressed)] {
            let atom = self.intern_str(name);
            properties.insert(
                &mut self.shapes,
                PropertyKey::Named(atom),
                Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: true,
                },
            );
        }
        properties.insert(
            &mut self.shapes,
            self.intrinsics.builtins.error_brand_key(),
            error_brand(),
        );
        self.allocate(HeapEntry::Object {
            properties,
            prototype: Some(self.intrinsics.error_prototype(id)),
            boxed_primitive: None,
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
    }

    fn close_iterator(&mut self, iterator: Value) -> Result<(), EvalFailure> {
        let (result, _) = self.close_iterator_raw(iterator);
        result.map(|_| ())
    }

    fn close_protocol_iterator(&mut self, iterator: Value) -> Result<(), EvalFailure> {
        let close = self.get_named_property(iterator, "return")?;
        if self.is_callable(close)? {
            let _ = self.call_value(close, iterator, &[])?;
        }
        Ok(())
    }

    /// A user's close throw cannot replace an existing abrupt completion.
    /// Engine failures remain fatal because execution cannot resume safely.
    fn close_protocol_iterator_preserving_abrupt(
        &mut self,
        iterator: Value,
    ) -> Result<(), RuntimeErrorKind> {
        match self.close_protocol_iterator(iterator) {
            Err(EvalFailure::Runtime(kind)) => Err(kind),
            Ok(())
            | Err(
                EvalFailure::Throw(_)
                | EvalFailure::ThrowValue(_)
                | EvalFailure::ThrowValueOrigin { .. },
            ) => Ok(()),
        }
    }

    fn mark_promise_all_settled(&mut self, aggregate: Value) -> Result<bool, EvalFailure> {
        let index = self
            .runtime_slot(aggregate)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        let HeapEntry::PromiseAll { settled, .. } = &mut self.heap[index] else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }));
        };
        let changed = !*settled;
        *settled = true;
        Ok(changed)
    }

    fn add_promise_all_element(&mut self, aggregate: Value) -> Result<usize, EvalFailure> {
        let index = self
            .runtime_slot(aggregate)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        let next_remaining = match &self.heap[index] {
            HeapEntry::PromiseAll {
                remaining,
                settled: false,
                ..
            } => remaining.checked_add(1).ok_or(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded {
                    limit: self.limits.max_heap_bytes,
                },
            ))?,
            HeapEntry::PromiseAll { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all target",
                }));
            }
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all target",
                }));
            }
        };
        self.ensure_allocation_capacity(0, std::mem::size_of::<Value>())
            .map_err(EvalFailure::Runtime)?;
        let HeapEntry::PromiseAll { values, .. } = &mut self.heap[index] else {
            unreachable!("Promise.all aggregate was checked before reserving value storage");
        };
        values.try_reserve(1).map_err(|_| {
            EvalFailure::Runtime(RuntimeErrorKind::HeapByteLimitExceeded {
                limit: self.limits.max_heap_bytes,
            })
        })?;
        self.charge_slot(index, std::mem::size_of::<Value>())
            .map_err(EvalFailure::Runtime)?;
        let HeapEntry::PromiseAll {
            values, remaining, ..
        } = &mut self.heap[index]
        else {
            unreachable!("Promise.all aggregate was checked before its heap charge");
        };
        let index = values.len();
        values.push(Value::UNDEFINED);
        *remaining = next_remaining;
        Ok(index)
    }

    fn finish_promise_all(&mut self, aggregate: Value) -> Result<bool, EvalFailure> {
        let index = self
            .runtime_slot(aggregate)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        let HeapEntry::PromiseAll {
            remaining, settled, ..
        } = &mut self.heap[index]
        else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }));
        };
        if *settled {
            return Ok(false);
        }
        *remaining -= 1;
        if *remaining != 0 {
            return Ok(false);
        }
        *settled = true;
        Ok(true)
    }

    fn move_promise_all_values_to_array(&mut self, aggregate: Value) -> Result<Value, EvalFailure> {
        let aggregate_index = self
            .runtime_slot(aggregate)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        if !matches!(self.heap[aggregate_index], HeapEntry::PromiseAll { .. }) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }));
        }
        let array = self.create_array(Vec::new())?;
        let array_index = self
            .runtime_slot(array)
            .map_err(EvalFailure::Runtime)?
            .expect("new runtime array has a runtime slot");
        let values = match &mut self.heap[aggregate_index] {
            HeapEntry::PromiseAll { values, .. } => std::mem::take(values),
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all target",
                }));
            }
        };
        let bytes = values.len().saturating_mul(std::mem::size_of::<Value>());
        self.replace_element_vector(array_index, values);
        self.transfer_slot_charge(aggregate_index, array_index, bytes);
        Ok(array)
    }

    pub(crate) fn resolve_promise_all_element(
        &mut self,
        element: Value,
        value: Value,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(element)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        let (aggregate, output_index) = {
            let HeapEntry::PromiseAllElement {
                aggregate,
                index: output_index,
                called,
            } = &mut self.heap[index]
            else {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all target",
                }));
            };
            if *called {
                return Ok(());
            }
            *called = true;
            (*aggregate, *output_index)
        };
        let aggregate_index = self
            .runtime_slot(aggregate)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Promise.all target",
            }))?;
        let (resolve, completed) = {
            let HeapEntry::PromiseAll {
                resolve,
                values,
                remaining,
                settled,
                ..
            } = &mut self.heap[aggregate_index]
            else {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Promise.all target",
                }));
            };
            if *settled {
                return Ok(());
            }
            values[output_index] = value;
            *remaining -= 1;
            let completed = *remaining == 0;
            if completed {
                *settled = true;
            }
            (*resolve, completed)
        };
        if completed {
            let array = self.move_promise_all_values_to_array(aggregate)?;
            let _ = self.call_value(resolve, Value::UNDEFINED, &[array])?;
        }
        Ok(())
    }

    fn create_array(&mut self, elements: Vec<Value>) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::Array {
            kind: ArrayElementKind::for_elements(&elements),
            elements,
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.array_prototype),
            extensible: true,
            length_writable: true,
        })
        .map_err(EvalFailure::Runtime)
    }

    fn resolve_promise(&mut self, promise: Value, value: Value) -> Result<(), RuntimeErrorKind> {
        if promise == value {
            return self
                .reject_promise_failure(
                    promise,
                    EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "Promise cannot resolve itself",
                    }),
                )
                .map_err(|failure| match failure {
                    EvalFailure::Runtime(kind) => kind,
                    _ => RuntimeErrorKind::InvalidValue { value: promise },
                });
        }
        if !self.is_object(value) {
            return self.fulfill_promise(promise, value);
        }
        let then = match self.get_named_property(value, "then") {
            Ok(then) => then,
            Err(EvalFailure::Runtime(kind)) => return Err(kind),
            Err(failure) => {
                return self.reject_promise_failure(promise, failure).map_err(
                    |failure| match failure {
                        EvalFailure::Runtime(kind) => kind,
                        _ => RuntimeErrorKind::InvalidValue { value: promise },
                    },
                );
            }
        };
        if !self.is_callable(then).map_err(|failure| match failure {
            EvalFailure::Runtime(kind) => kind,
            _ => RuntimeErrorKind::InvalidValue { value: then },
        })? {
            return self.fulfill_promise(promise, value);
        }
        self.ensure_microtask_capacity(1)?;
        self.microtasks
            .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Thenable {
                promise,
                thenable: value,
                then,
                context: self.context_global,
            }));
        Ok(())
    }

    /// Rejects `promise` with `reason`. Lazy engine-origin reasons
    /// (`UNDEFINED` + non-Bytecode origin) are materialized once here into a
    /// realm-intrinsic Error before settlement, so every rejection path
    /// (async functions, async generators, incompatible receivers, failed
    /// imports, reaction forwarding) stores an observable error object.
    /// Already-materialized and Bytecode-origin reasons retain identity.
    /// Already-settled promises are no-ops and do not allocate a reason.
    fn reject_promise(
        &mut self,
        promise: Value,
        reason: Value,
        origin: ThrowOrigin,
    ) -> Result<(), RuntimeErrorKind> {
        if catch_value_needs_materialization(reason, origin) {
            let index = self
                .runtime_slot(promise)?
                .ok_or(RuntimeErrorKind::InvalidValue { value: promise })?;
            match &self.heap[index] {
                HeapEntry::Promise {
                    state: PromiseState::Pending { .. },
                    ..
                } => {}
                HeapEntry::Promise { .. } => return Ok(()),
                _ => return Err(RuntimeErrorKind::InvalidValue { value: promise }),
            }
            let reason = self.materialize_engine_origin(origin)?;
            return self.settle_promise(promise, PromiseState::Rejected { reason, origin });
        }
        self.settle_promise(promise, PromiseState::Rejected { reason, origin })
    }

    fn fulfill_promise(&mut self, promise: Value, value: Value) -> Result<(), RuntimeErrorKind> {
        self.settle_promise(promise, PromiseState::Fulfilled { value })
    }

    fn settle_promise(
        &mut self,
        promise: Value,
        terminal: PromiseState,
    ) -> Result<(), RuntimeErrorKind> {
        let index = self
            .runtime_slot(promise)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: promise })?;
        let (reaction_count, pending_charge) = match &self.heap[index] {
            HeapEntry::Promise {
                state:
                    PromiseState::Pending {
                        fulfill_reactions,
                        reject_reactions,
                    },
                ..
            } => {
                let reaction_count = match &terminal {
                    PromiseState::Fulfilled { .. } => fulfill_reactions.len(),
                    PromiseState::Rejected { .. } => reject_reactions.len(),
                    PromiseState::Pending { .. } => unreachable!("Promise settlement is terminal"),
                };
                let pending_count = fulfill_reactions
                    .len()
                    .saturating_add(reject_reactions.len());
                (
                    reaction_count,
                    pending_count.saturating_mul(std::mem::size_of::<PromiseReaction>()),
                )
            }
            HeapEntry::Promise { .. } => return Ok(()),
            _ => return Err(RuntimeErrorKind::InvalidValue { value: promise }),
        };
        self.ensure_microtask_capacity(reaction_count)?;
        let reactions = match &mut self.heap[index] {
            HeapEntry::Promise { state, .. } => {
                let reactions = match state {
                    PromiseState::Pending {
                        fulfill_reactions,
                        reject_reactions,
                    } => match &terminal {
                        PromiseState::Fulfilled { .. } => std::mem::take(fulfill_reactions),
                        PromiseState::Rejected { .. } => std::mem::take(reject_reactions),
                        PromiseState::Pending { .. } => {
                            unreachable!("Promise settlement is terminal")
                        }
                    },
                    _ => return Ok(()),
                };
                *state = terminal.clone();
                reactions
            }
            _ => return Err(RuntimeErrorKind::InvalidValue { value: promise }),
        };
        let (value, origin) = match terminal {
            PromiseState::Fulfilled { value } => (value, ThrowOrigin::Bytecode),
            PromiseState::Rejected { reason, origin } => (reason, origin),
            PromiseState::Pending { .. } => unreachable!("Promise settlement is terminal"),
        };
        let queued_charge = reactions
            .len()
            .saturating_mul(std::mem::size_of::<PromiseReaction>());
        self.transfer_slot_to_machine(index, queued_charge);
        self.refund_slot(index, pending_charge.saturating_sub(queued_charge));
        for reaction in reactions {
            self.microtasks.push_back(QueuedMicrotask {
                job: MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                },
                retained_bytes: std::mem::size_of::<PromiseReaction>(),
            });
        }
        Ok(())
    }

    fn reject_promise_failure(
        &mut self,
        promise: Value,
        failure: EvalFailure,
    ) -> Result<(), EvalFailure> {
        let (reason, origin) = self.promise_rejection_value(failure)?;
        self.reject_promise(promise, reason, origin)
            .map_err(EvalFailure::Runtime)
    }

    fn call_promise_reject(
        &mut self,
        reject: Value,
        failure: EvalFailure,
    ) -> Result<(), EvalFailure> {
        let (reason, _) = self.promise_rejection_value(failure)?;
        let _ = self.call_value(reject, Value::UNDEFINED, &[reason])?;
        Ok(())
    }

    fn promise_rejection_value(
        &mut self,
        failure: EvalFailure,
    ) -> Result<(Value, ThrowOrigin), EvalFailure> {
        match failure {
            EvalFailure::ThrowValue(value) => Ok((value, ThrowOrigin::Bytecode)),
            EvalFailure::ThrowValueOrigin { value, origin } => Ok((value, origin)),
            EvalFailure::Throw(ThrowOrigin::Bytecode) => {
                Ok((Value::UNDEFINED, ThrowOrigin::Bytecode))
            }
            EvalFailure::Throw(origin) => {
                let value = self
                    .materialize_engine_origin(origin)
                    .map_err(EvalFailure::Runtime)?;
                Ok((value, origin))
            }
            EvalFailure::Runtime(kind) => Err(EvalFailure::Runtime(kind)),
        }
    }

    /// Builds a realm error object for a non-bytecode engine throw origin via
    /// installed error-constructor intrinsics (not user-global lookup).
    pub(crate) fn materialize_engine_origin(
        &mut self,
        origin: ThrowOrigin,
    ) -> Result<Value, RuntimeErrorKind> {
        let (name, message) = match origin {
            ThrowOrigin::TypeError { operation } => ("TypeError", operation),
            ThrowOrigin::RangeError { operation } => ("RangeError", operation),
            ThrowOrigin::ReferenceError { operation } => ("ReferenceError", operation),
            ThrowOrigin::UriError { operation } => ("URIError", operation),
            ThrowOrigin::Bytecode => {
                unreachable!("bytecode throws retain their original value")
            }
        };
        let id = self
            .intrinsics
            .builtins
            .id_named(name)
            .expect("error constructor is installed");
        match self.throw_error(id, EcmaString::encode(message)) {
            EvalFailure::ThrowValue(value) => Ok(value),
            EvalFailure::Runtime(kind) => Err(kind),
            _ => unreachable!("error materialization returns a thrown value"),
        }
    }

    /// Populates the `message` field of a [`RuntimeErrorKind::UncaughtThrow`],
    /// and its `constructor_name` field when the throw originated from guest
    /// bytecode ([`ThrowOrigin::Bytecode`]). Engine-originated throws
    /// (`TypeError`, `RangeError`, etc.) already name their constructor in
    /// the [`ThrowOrigin`] variant and are left as `None`.
    ///
    /// This must be called at every public boundary where an `UncaughtThrow`
    /// error crosses into code that no longer has access to the machine
    /// heap — the interpreter entry point and the native engine's
    /// `run`/`run_linked` methods.
    pub(crate) fn enrich_uncaught_throw(&mut self, error: &mut RuntimeError) {
        let RuntimeErrorKind::UncaughtThrow {
            value,
            origin,
            constructor_name,
            message,
        } = &mut error.kind
        else {
            return;
        };
        if message.is_none() {
            *message = match origin {
                ThrowOrigin::ReferenceError {
                    operation: "global is not defined",
                } => self.missing_global.as_ref().map(|name| {
                    EcmaString::encode(&format!("{} is not defined", name.to_utf8_lossy()))
                }),
                _ => self.resolve_thrown_message(*value),
            };
        }
        if *origin != ThrowOrigin::Bytecode {
            return;
        }
        if constructor_name.is_some() {
            return;
        }
        *constructor_name = self.resolve_thrown_constructor_name(*value).unwrap_or(None);
    }

    fn program(&self) -> &Program<Verified> {
        self.program
            .expect("module registry operations require a whole program")
    }

    fn module_code(&self, module: ModuleId) -> &Module<Verified> {
        let index = module.get() as usize;
        if index >= self.dynamic_base {
            return &self.dynamic[index - self.dynamic_base].program.modules()[0].code;
        }
        match self.program {
            Some(program) => {
                &program
                    .module(module)
                    .expect("verified module id remains in bounds")
                    .code
            }
            None => self.module,
        }
    }

    fn program_module(&self, module: ModuleId) -> &ProgramModule<Verified> {
        let index = module.get() as usize;
        if index >= self.dynamic_base {
            return &self.dynamic[index - self.dynamic_base].program.modules()[0];
        }
        self.program
            .and_then(|program| program.module(module))
            .expect("verified module id remains in bounds")
    }

    /// Validates host-provided code against this machine's classic-script realm.
    fn validate_dynamic_script(program: &Program<Verified>) -> Result<(), &'static str> {
        if program.modules().len() != 1 {
            return Err("script program must contain exactly one module");
        }
        if program.entry() != ModuleId::new(0) {
            return Err("script program entry must be module zero");
        }
        let module = &program.modules()[0];
        if !module.edges.is_empty() || !module.bindings.is_empty() || !module.exports.is_empty() {
            return Err("script program must not contain linkage metadata");
        }
        if module
            .code
            .functions()
            .iter()
            .flat_map(|function| function.code())
            .any(|instruction| {
                matches!(
                    instruction,
                    Instruction::Import { .. } | Instruction::Export { .. }
                )
            })
        {
            return Err("script program must not contain import or export instructions");
        }
        Ok(())
    }

    fn script_heap_cost(program: &Program<Verified>) -> usize {
        const MODULE_BYTES: usize = 64;
        const FUNCTION_BYTES: usize = 32;
        program.modules().iter().fold(0usize, |total, module| {
            let constant_bytes = module
                .code
                .constants()
                .iter()
                .fold(0usize, |bytes, constant| {
                    let payload = match constant {
                        Constant::String(text) => text.len_units().saturating_mul(2),
                        Constant::BigInt(value) => value.as_str().len(),
                        Constant::Number(_)
                        | Constant::Int32(_)
                        | Constant::Boolean(_)
                        | Constant::Null
                        | Constant::Undefined => 0,
                    };
                    bytes
                        .saturating_add(std::mem::size_of::<Constant>())
                        .saturating_add(payload)
                });
            let function_bytes =
                module
                    .code
                    .functions()
                    .iter()
                    .fold(0usize, |bytes, function| {
                        bytes
                            .saturating_add(FUNCTION_BYTES)
                            .saturating_add(
                                function
                                    .code()
                                    .len()
                                    .saturating_mul(std::mem::size_of::<Instruction>()),
                            )
                            .saturating_add(function.handlers().len().saturating_mul(
                                std::mem::size_of::<bamts_bytecode::ExceptionHandler>(),
                            ))
                    });
            total
                .saturating_add(MODULE_BYTES)
                .saturating_add(constant_bytes)
                .saturating_add(function_bytes)
                .saturating_add(module.code.verification_bytes())
        })
    }

    fn install_script_reserving(
        &mut self,
        program: Arc<Program<Verified>>,
        reserved_slots: usize,
        reserved_bytes: usize,
    ) -> Result<ModuleId, RuntimeErrorKind> {
        Self::validate_dynamic_script(&program)
            .map_err(|reason| RuntimeErrorKind::InvalidDynamicScript { reason })?;
        if self.dynamic.len() >= self.limits.max_dynamic_modules {
            return Err(RuntimeErrorKind::DynamicModuleLimitExceeded {
                limit: self.limits.max_dynamic_modules,
            });
        }
        let bytes = Self::script_heap_cost(&program);
        let retained_bytes =
            bytes
                .checked_add(reserved_bytes)
                .ok_or(RuntimeErrorKind::HeapByteLimitExceeded {
                    limit: self.limits.max_heap_bytes,
                })?;
        self.ensure_allocation_capacity(reserved_slots, retained_bytes)?;
        self.charge_machine(bytes)?;
        let index = self.dynamic_base.checked_add(self.dynamic.len()).ok_or(
            RuntimeErrorKind::DynamicModuleLimitExceeded {
                limit: self.limits.max_dynamic_modules,
            },
        )?;
        let module = ModuleId::new(u32::try_from(index).map_err(|_| {
            RuntimeErrorKind::DynamicModuleLimitExceeded {
                limit: self.limits.max_dynamic_modules,
            }
        })?);
        preintern_program_names(&mut self.atoms, &program);
        self.dynamic.push(DynamicModule { program, bytes });
        self.registry.modules.push(ModuleInstance {
            binding_cells: Vec::new(),
            constant_cells: Vec::new(),
            constant_is_import: Vec::new(),
            namespace: None,
            import_meta: None,
            state: ModuleState::Unevaluated,
        });
        debug_assert_eq!(
            self.dynamic
                .last()
                .expect("installed script remains retained")
                .bytes,
            bytes
        );
        debug_assert_eq!(
            self.registry.modules.len(),
            self.dynamic_base + self.dynamic.len()
        );
        Ok(module)
    }

    fn allocate_cell(&mut self, value: Value, module: ModuleId) -> Result<CellId, RuntimeError> {
        if self.registry.cells.len() >= self.limits.max_module_cells {
            return Err(self.program_error(
                module,
                RuntimeErrorKind::ModuleCellLimitExceeded {
                    limit: self.limits.max_module_cells,
                },
            ));
        }
        let id = CellId(self.registry.cells.len());
        self.registry.cells.push(Cell { value });
        Ok(id)
    }

    pub(crate) fn instantiate_modules(&mut self) -> Result<(), RuntimeError> {
        debug_assert!(
            self.dynamic.is_empty(),
            "module instantiation precedes dynamic script installation"
        );
        let program = self
            .program
            .expect("module registry operations require a whole program");
        self.registry.modules = program
            .modules()
            .iter()
            .map(|module| ModuleInstance {
                binding_cells: vec![None; module.bindings.len()],
                constant_is_import: vec![false; module.code.constants().len()],
                constant_cells: vec![None; module.code.constants().len()],
                namespace: None,
                import_meta: None,
                state: ModuleState::Unevaluated,
            })
            .collect();
        self.registry.local_modules = program
            .modules()
            .iter()
            .enumerate()
            .map(|(module_index, module)| {
                let name = match module.code.constants().get(module.name.get() as usize) {
                    Some(Constant::String(name)) => name.clone(),
                    _ => unreachable!("verified program module names are strings"),
                };
                (name, ModuleId::new(module_index as u32))
            })
            .collect();

        for module_index in 0..program.modules().len() {
            let module_id = ModuleId::new(module_index as u32);
            let bindings = program.modules()[module_index].bindings.clone();
            for (binding_index, binding) in bindings.into_iter().enumerate() {
                let initial = match binding.kind {
                    BindingKind::Hoisted => Some(Value::UNDEFINED),
                    BindingKind::Lexical => Some(Value::UNINITIALIZED),
                    BindingKind::Imported { .. } | BindingKind::Namespace { .. } => None,
                };
                if let Some(value) = initial {
                    let cell = self.allocate_cell(value, module_id)?;
                    self.registry.modules[module_index].binding_cells[binding_index] = Some(cell);
                }
            }
        }

        for module_index in 0..program.modules().len() {
            let module_id = ModuleId::new(module_index as u32);
            let bindings = program.modules()[module_index].bindings.clone();
            for (binding_index, binding) in bindings.into_iter().enumerate() {
                let cell = match binding.kind {
                    BindingKind::Hoisted | BindingKind::Lexical => continue,
                    BindingKind::Imported { edge, name } => {
                        let dependency = program.modules()[module_index].edges[edge.get() as usize];
                        match dependency.target {
                            EdgeTarget::External => {
                                let name = self.constant_text(module_id, name).clone();
                                self.external_export_cell(module_id, edge, &name)?
                            }
                            EdgeTarget::Local(target) => match program
                                .resolve_export(target, self.constant_text(module_id, name))
                            {
                                Some(ResolvedExport::Local { module, binding }) => {
                                    self.registry.modules[module.get() as usize].binding_cells
                                        [binding.get() as usize]
                                        .expect("own cells are allocated before aliases link")
                                }
                                Some(ResolvedExport::External { module, edge, name }) => {
                                    let name = self.constant_text(module, name).clone();
                                    self.external_export_cell(module, edge, &name)?
                                }
                                None => {
                                    return Err(self.program_error(
                                        module_id,
                                        RuntimeErrorKind::InvalidVerifiedProgram {
                                            module: module_id,
                                            instruction: Instruction::Import {
                                                dst: bamts_bytecode::Register::new(0),
                                                specifier: name,
                                            },
                                        },
                                    ));
                                }
                            },
                        }
                    }
                    BindingKind::Namespace { edge } => {
                        let dependency = program.modules()[module_index].edges[edge.get() as usize];
                        let namespace = match dependency.target {
                            EdgeTarget::Local(target) => {
                                self.module_namespace(target, module_id)?
                            }
                            EdgeTarget::External => self.external_namespace(module_id, edge)?,
                        };
                        self.allocate_cell(namespace, module_id)?
                    }
                };
                self.registry.modules[module_index].binding_cells[binding_index] = Some(cell);
            }
        }

        for module_index in 0..program.modules().len() {
            let bindings = &program.modules()[module_index].bindings;
            let constants = program.modules()[module_index].code.constants();
            for (constant_index, constant) in constants.iter().enumerate() {
                let Constant::String(name) = constant else {
                    continue;
                };
                if let Some((binding_index, binding)) =
                    bindings.iter().enumerate().find(|(_, binding)| {
                        self.constant_text(ModuleId::new(module_index as u32), binding.name) == name
                    })
                {
                    self.registry.modules[module_index].constant_cells[constant_index] =
                        self.registry.modules[module_index].binding_cells[binding_index];
                    self.registry.modules[module_index].constant_is_import[constant_index] = matches!(
                        binding.kind,
                        BindingKind::Imported { .. } | BindingKind::Namespace { .. }
                    );
                }
            }
        }
        Ok(())
    }

    fn load_import_meta(&mut self, module: ModuleId) -> Result<Value, RuntimeErrorKind> {
        let module_index = module.get() as usize;
        if let Some(value) = self.registry.modules[module_index].import_meta {
            return Ok(value);
        }
        let module_name = self
            .constant_text(module, self.program_module(module).name)
            .clone();
        let url = self.host.import_meta_url(&module_name);
        let url_key = PropertyKey::Named(self.intern_str("url"));
        let bytes = url
            .len_units()
            .saturating_mul(2)
            .saturating_add(url_key.charge_bytes(&self.atoms).saturating_add(1));
        self.ensure_allocation_capacity(2, bytes)?;
        let url_value = self.allocate(HeapEntry::String(url))?;
        let mut properties = PropertyMap::default();
        properties.insert(
            &mut self.shapes,
            url_key,
            Property::Data {
                value: url_value,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        );
        let value = self.allocate(HeapEntry::Object {
            properties,
            prototype: Some(self.intrinsics.object_prototype),
            boxed_primitive: None,
            extensible: true,
        })?;
        self.registry.modules[module_index].import_meta = Some(value);
        Ok(value)
    }

    fn module_namespace(
        &mut self,
        target: ModuleId,
        requester: ModuleId,
    ) -> Result<Value, RuntimeError> {
        if let Some(value) = self.registry.modules[target.get() as usize].namespace {
            return Ok(value);
        }
        let exported_names: Vec<EcmaString> = self
            .program_module(target)
            .exports
            .iter()
            .map(|export| self.constant_text(target, export.name).clone())
            .collect();
        for exported_name in exported_names {
            if let Some(ResolvedExport::External { module, edge, name }) =
                self.program().resolve_export(target, &exported_name)
            {
                let name = self.constant_text(module, name).clone();
                self.external_export_cell(module, edge, &name)?;
            }
        }
        let value = self
            .allocate(HeapEntry::ModuleNamespace { module: target })
            .map_err(|kind| self.program_error(requester, kind))?;
        self.registry.modules[target.get() as usize].namespace = Some(value);
        Ok(value)
    }

    fn external_specifier(&self, module: ModuleId, edge: EdgeId) -> Option<EcmaString> {
        let dependency = self.program_module(module).edges[edge.get() as usize];
        let specifier = self.constant_text(module, dependency.specifier);
        self.registry
            .external
            .contains_key(specifier)
            .then(|| specifier.clone())
    }

    fn external_namespace(
        &mut self,
        module: ModuleId,
        edge: EdgeId,
    ) -> Result<Value, RuntimeError> {
        let Some(specifier) = self.external_specifier(module, edge) else {
            return Err(self.program_error(
                module,
                RuntimeErrorKind::ExternalModuleUnavailable { module, edge },
            ));
        };
        let export_names: Vec<EcmaString> = self.registry.external[&specifier]
            .exports
            .keys()
            .cloned()
            .collect();
        for name in export_names {
            self.external_export_cell(module, edge, &name)?;
        }
        Ok(self.registry.external[&specifier].namespace)
    }

    fn external_export_cell(
        &mut self,
        module: ModuleId,
        edge: EdgeId,
        name: &EcmaString,
    ) -> Result<CellId, RuntimeError> {
        let Some(specifier) = self.external_specifier(module, edge) else {
            return Err(self.program_error(
                module,
                RuntimeErrorKind::ExternalModuleUnavailable { module, edge },
            ));
        };
        let Some(export) = self.registry.external[&specifier]
            .exports
            .get(name)
            .copied()
        else {
            return Err(self.program_error(
                module,
                RuntimeErrorKind::ExternalModuleUnavailable { module, edge },
            ));
        };
        if let Some(cell) = export.cell {
            return Ok(cell);
        }
        let cell = self.allocate_cell(export.value, module)?;
        self.registry
            .external
            .get_mut(&specifier)
            .expect("external module remains registered")
            .exports
            .get_mut(name)
            .expect("external export remains registered")
            .cell = Some(cell);
        Ok(cell)
    }

    pub(crate) fn resolve_import(
        &self,
        module: ModuleId,
        specifier: ConstantId,
    ) -> Result<ImportTarget, RuntimeErrorKind> {
        let name = self.constant_text(module, specifier);
        self.program_module(module)
            .edges
            .iter()
            .enumerate()
            .find(|(_, edge)| {
                edge.kind.has_dynamic() && self.constant_text(module, edge.specifier) == name
            })
            .map(|(index, edge)| match edge.target {
                EdgeTarget::Local(target) => ImportTarget::Local(target),
                EdgeTarget::External => ImportTarget::External(EdgeId::new(index as u32)),
            })
            .ok_or(RuntimeErrorKind::DynamicImportEdgeMissing { module, specifier })
    }

    pub(crate) fn imported_namespace(
        &mut self,
        requester: ModuleId,
        target: ImportTarget,
    ) -> Result<Value, RuntimeErrorKind> {
        match target {
            ImportTarget::Local(target) => self.module_namespace(target, requester),
            ImportTarget::External(edge) => self.external_namespace(requester, edge),
        }
        .map_err(|error| error.kind)
    }

    pub(crate) fn module_entry_suspends(&self, module: ModuleId) -> bool {
        let code = self.module_code(module);
        code.functions()[code.entry().get() as usize]
            .code()
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Await { .. }))
    }

    /// Returns whether any module reachable from `module` through static
    /// local edges has a top-level-await entry. The native backend uses this
    /// to delegate whole async static graphs to the interpreter while keeping
    /// fully synchronous graphs native.
    pub(crate) fn module_graph_suspends(&self, module: ModuleId) -> bool {
        let mut seen = Vec::new();
        let mut stack = vec![module];
        while let Some(next) = stack.pop() {
            let index = next.get() as usize;
            if index >= seen.len() {
                seen.resize(index + 1, false);
            }
            if seen[index] {
                continue;
            }
            seen[index] = true;
            if self.module_entry_suspends(next) {
                return true;
            }
            for edge in self.program_module(next).edges.iter() {
                if !edge.kind.has_static() {
                    continue;
                }
                if let EdgeTarget::Local(dependency) = edge.target {
                    stack.push(dependency);
                }
            }
        }
        false
    }

    /// Runs a module entry whose static dependencies have all settled. A
    /// fully synchronous entry completes inline; an async entry runs its
    /// first turn and either settles (its terminal turn owns module-state
    /// settlement through `settle_async_step`) or suspends into
    /// [`ModuleState::EvaluatingAsync`]. Never drains the event loop:
    /// driving belongs to the root `evaluate` machine.
    fn start_ready_entry(&mut self, module: ModuleId, pair: Option<ModulePending>) -> ModuleStart {
        if !self.module_entry_suspends(module) {
            return ModuleStart::Settled(self.run_sync_module_entry(module));
        }
        let pair = match pair {
            Some(pair) => pair,
            None => match self.create_module_async_pair(module) {
                Ok(pair) => pair,
                Err(failure) => {
                    return ModuleStart::Settled(Err(self.module_eval_failure(module, failure)));
                }
            },
        };
        let function = self.module_code(module).entry();
        let stop_depth = self.frames.len();
        if let Err(error) = self.push_frame(ActivationRequest {
            target: RuntimeFunction { module, function },
            captures: &[],
            context: None,
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            arguments: &[],
            return_to: None,
        }) {
            return ModuleStart::Settled(Err(error));
        }
        if let Err(failure) =
            self.drive_and_settle_async(pair.record, pair.promise, stop_depth, None)
        {
            let error = self.module_eval_failure(module, failure);
            if !matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }) {
                // A fatal failure before settlement leaves the module
                // retryable; throws are cached by the caller's settle.
                self.abort_module_evaluation(module);
            }
            return ModuleStart::Settled(Err(error));
        }
        match self.finish_module_start(module, pair) {
            Ok(start) => start,
            Err(error) => ModuleStart::Settled(Err(error)),
        }
    }

    /// Native-backend adapter: starts one module entry and, when it suspends,
    /// drives the bounded outer loop until the entry settles. Callers settle
    /// module state through `finish_module_evaluation`; only root evaluation
    /// contexts may reach this (no checkpoint may be active).
    pub(crate) fn run_module_entry(&mut self, module: ModuleId) -> Result<Execution, RuntimeError> {
        match self.start_ready_entry(module, None) {
            ModuleStart::Settled(result) => result,
            ModuleStart::Pending(pair) => self.drive_entry_to_settlement(pair, module),
            ModuleStart::Cached => unreachable!("a started entry is never cached"),
        }
    }

    /// Reads the terminal effect of one async entry's first turn: a recorded
    /// completion means the entry settled synchronously; otherwise it
    /// suspended and the module becomes async-pending on the shared pair.
    fn finish_module_start(
        &mut self,
        module: ModuleId,
        pair: ModulePending,
    ) -> Result<ModuleStart, RuntimeError> {
        if self
            .async_module_completion_stored(pair.record)
            .map_err(|kind| self.program_error(module, kind))?
        {
            let completion = self
                .take_async_module_completion(pair.record, module)
                .map_err(|kind| self.program_error(module, kind))?;
            return Ok(ModuleStart::Settled(completion));
        }
        self.registry.modules[module.get() as usize].state = ModuleState::EvaluatingAsync {
            record: pair.record,
            promise: pair.promise,
            pending_deps: 0,
        };
        Ok(ModuleStart::Pending(pair))
    }

    /// Allocates the one shared evaluation record/promise pair for a module.
    /// When the DFS tail already classified pending static dependencies, the
    /// pair lives in `state` and this only clones it.
    fn create_module_async_pair(&mut self, module: ModuleId) -> Result<ModulePending, EvalFailure> {
        if let ModuleState::EvaluatingAsync {
            record, promise, ..
        } = &self.registry.modules[module.get() as usize].state
        {
            return Ok(ModulePending {
                record: *record,
                promise: *promise,
            });
        }
        let promise = self.create_promise()?;
        let record = self.create_async_activation(promise, Some(module))?;
        Ok(ModulePending { record, promise })
    }

    /// Returns whether the entry's first turn already recorded a completion.
    fn async_module_completion_stored(&self, record: Value) -> Result<bool, RuntimeErrorKind> {
        let index = self
            .runtime_slot(record)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })?;
        let HeapEntry::AsyncActivation { completion, .. } = &self.heap[index] else {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        };
        Ok(completion.is_some())
    }

    fn run_sync_module_entry(&mut self, module: ModuleId) -> Result<Execution, RuntimeError> {
        let function = self.module_code(module).entry();
        let stop_depth = self.frames.len();
        self.push_frame(ActivationRequest {
            target: RuntimeFunction { module, function },
            captures: &[],
            context: None,
            this_value: Value::UNDEFINED,
            new_target: Value::UNDEFINED,
            arguments: &[],
            return_to: None,
        })?;
        let result = self.run_loop(stop_depth).and_then(|execution| {
            execution.ok_or_else(|| {
                self.program_error(
                    module,
                    RuntimeErrorKind::InvalidVerifiedProgram {
                        module,
                        instruction: Instruction::Halt,
                    },
                )
            })
        });
        if result.is_err() {
            self.unwind_frames_to(stop_depth);
        }
        result
    }

    fn module_eval_failure(&mut self, module: ModuleId, failure: EvalFailure) -> RuntimeError {
        match self.promise_rejection_value(failure) {
            Ok((value, origin)) => self.program_error(
                module,
                RuntimeErrorKind::UncaughtThrow {
                    value,
                    origin,
                    constructor_name: None,
                    message: None,
                },
            ),
            Err(EvalFailure::Runtime(kind)) => self.program_error(module, kind),
            Err(_) => unreachable!("failure materialization only fails at a runtime boundary"),
        }
    }

    fn evaluate_import(&mut self, module: ModuleId) -> Result<(), RuntimeError> {
        // A pending dependency hands the raw (possibly partial) namespace to
        // the executing entry; the shared evaluation Promise already carries
        // completion to any pure dynamic importer.
        self.evaluate_module(module).map(|_| ())
    }

    fn import_namespace(
        &mut self,
        requester: ModuleId,
        specifier: ConstantId,
    ) -> Result<Value, EvalFailure> {
        let target = self
            .resolve_import(requester, specifier)
            .map_err(EvalFailure::Runtime)?;
        let ImportTarget::Local(module) = target else {
            return self
                .imported_namespace(requester, target)
                .map_err(EvalFailure::Runtime);
        };
        if self.import_edge_has_static(requester, specifier) {
            // A static (or coalesced static+dynamic) edge always yields the
            // raw namespace: settled dependencies finished before this entry
            // ran, pending ones hand over the partial cycle namespace, and
            // stored failures rethrow at this site.
            self.evaluate_import(module)
                .map_err(|error| import_failure(&error))?;
            return self
                .imported_namespace(requester, target)
                .map_err(EvalFailure::Runtime);
        }
        match self.import_dynamic(requester, module)? {
            DynamicImport::Ready(value) | DynamicImport::Pending(value) => Ok(value),
            DynamicImport::Failed(error) => Err(import_failure(&error)),
        }
    }

    /// Pure dynamic import of a local module. Only an in-flight
    /// [`ModuleState::EvaluatingAsync`] target hands out its shared
    /// evaluation Promise, so every concurrent `import()` observes the
    /// identical Promise object; every other state yields the raw namespace
    /// or the stored failure.
    fn import_dynamic(
        &mut self,
        requester: ModuleId,
        target: ModuleId,
    ) -> Result<DynamicImport, EvalFailure> {
        match self.registry.modules[target.get() as usize].state.clone() {
            ModuleState::EvaluatingAsync { promise, .. } => Ok(DynamicImport::Pending(promise)),
            ModuleState::Evaluating | ModuleState::Evaluated(Ok(())) => self
                .imported_namespace(requester, ImportTarget::Local(target))
                .map(DynamicImport::Ready)
                .map_err(EvalFailure::Runtime),
            ModuleState::Evaluated(Err(error)) => Ok(DynamicImport::Failed(error)),
            ModuleState::Unevaluated => match self.evaluate_module(target) {
                Ok(ModuleStart::Settled(_)) | Ok(ModuleStart::Cached) => self
                    .imported_namespace(requester, ImportTarget::Local(target))
                    .map(DynamicImport::Ready)
                    .map_err(EvalFailure::Runtime),
                Ok(ModuleStart::Pending(pair)) => Ok(DynamicImport::Pending(pair.promise)),
                Err(error) => Ok(DynamicImport::Failed(error)),
            },
        }
    }

    /// Resolves a runtime `import()` specifier without requiring an edge.
    /// Declared requester edges take precedence, then exact external lookup.
    /// Relative `./` and `../` specifiers then resolve against the requester's
    /// canonical module directory through the bundled-local name map. Absolute
    /// and other opaque strings are never treated as local paths.
    fn resolve_dynamic_specifier(
        &self,
        requester: ModuleId,
        specifier: &EcmaString,
    ) -> Option<DynamicImportTarget> {
        if let Some(edge) = self
            .program_module(requester)
            .edges
            .iter()
            .find(|edge| self.constant_text(requester, edge.specifier) == specifier)
        {
            match edge.target {
                EdgeTarget::Local(target) => return Some(DynamicImportTarget::Local(target)),
                EdgeTarget::External if self.registry.external.contains_key(specifier) => {
                    return Some(DynamicImportTarget::External(specifier.clone()));
                }
                EdgeTarget::External => return None,
            }
        }
        if self.registry.external.contains_key(specifier) {
            return Some(DynamicImportTarget::External(specifier.clone()));
        }
        if !is_relative_module_specifier(specifier) {
            return None;
        }
        let requester_name = self.constant_text(requester, self.program_module(requester).name);
        let resolved = resolve_relative_against_module_name(requester_name, specifier);
        self.registry
            .local_modules
            .get(&resolved)
            .copied()
            .map(DynamicImportTarget::Local)
    }

    fn attach_dynamic_import_reactions(
        &mut self,
        evaluation: Value,
        promise: Value,
        target: ModuleId,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(evaluation)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "dynamic import evaluation promise",
            }))?;
        let state = match &self.heap[index] {
            HeapEntry::Promise { state, .. } => state.clone(),
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "dynamic import evaluation promise",
                }));
            }
        };
        let context = self.context_global;
        match state {
            PromiseState::Pending { .. } => {
                self.charge_promise_reactions(index, 2)?;
                let HeapEntry::Promise {
                    state:
                        PromiseState::Pending {
                            fulfill_reactions,
                            reject_reactions,
                        },
                    ..
                } = &mut self.heap[index]
                else {
                    unreachable!("promise state was cloned from pending");
                };
                fulfill_reactions.push(PromiseReaction::DynamicImportFulfill {
                    promise,
                    target,
                    context,
                });
                reject_reactions.push(PromiseReaction::DynamicImportReject { promise, context });
                Ok(())
            }
            PromiseState::Fulfilled { .. } => {
                let namespace = self
                    .module_namespace(target, target)
                    .map_err(|error| EvalFailure::Runtime(error.kind))?;
                self.resolve_promise(promise, namespace)
                    .map_err(EvalFailure::Runtime)
            }
            PromiseState::Rejected { reason, origin } => self
                .reject_promise(promise, reason, origin)
                .map_err(EvalFailure::Runtime),
        }
    }

    /// Evaluates `import(specifier)` in the runtime plane. It always returns a
    /// promise for ordinary resolution and coercion failures rather than
    /// throwing those failures synchronously.
    fn import_dynamic_expression(
        &mut self,
        requester: ModuleId,
        specifier: Value,
    ) -> Result<Value, EvalFailure> {
        let specifier = match self.coerce_string_observable(specifier) {
            Ok(specifier) => specifier,
            Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
            Err(failure) => {
                let promise = self.create_promise()?;
                self.reject_promise_failure(promise, failure)?;
                return Ok(promise);
            }
        };
        self.import_dynamic_resolved(requester, specifier)
    }

    pub(crate) fn import_dynamic_expression_with_attributes(
        &mut self,
        requester: ModuleId,
        specifier: Value,
        options: Value,
    ) -> Result<Value, EvalFailure> {
        let specifier = match self.coerce_string_observable(specifier) {
            Ok(specifier) => specifier,
            Err(EvalFailure::Runtime(kind)) => return Err(EvalFailure::Runtime(kind)),
            Err(failure) => {
                let promise = self.create_promise()?;
                self.reject_promise_failure(promise, failure)?;
                return Ok(promise);
            }
        };
        let attributes = match self.dynamic_import_attributes(options) {
            Ok(attributes) => attributes,
            Err(failure) => {
                let promise = self.create_promise()?;
                self.reject_promise_failure(promise, failure)?;
                return Ok(promise);
            }
        };
        if let Err(failure) = self.canonical_import_attributes(attributes) {
            let promise = self.create_promise()?;
            self.reject_promise_failure(promise, failure)?;
            return Ok(promise);
        }
        self.import_dynamic_resolved(requester, specifier)
    }

    fn import_dynamic_resolved(
        &mut self,
        requester: ModuleId,
        specifier: EcmaString,
    ) -> Result<Value, EvalFailure> {
        let Some(target) = self.resolve_dynamic_specifier(requester, &specifier) else {
            let promise = self.create_promise()?;
            self.reject_promise_failure(
                promise,
                EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "resolve dynamic module specifier",
                }),
            )?;
            return Ok(promise);
        };
        match target {
            DynamicImportTarget::External(specifier) => {
                let namespace = self.registry.external[&specifier].namespace;
                let promise = self.create_promise()?;
                self.resolve_promise(promise, namespace)
                    .map_err(EvalFailure::Runtime)?;
                Ok(promise)
            }
            DynamicImportTarget::Local(target) => match self.import_dynamic(requester, target)? {
                DynamicImport::Ready(namespace) => {
                    let promise = self.create_promise()?;
                    self.resolve_promise(promise, namespace)
                        .map_err(EvalFailure::Runtime)?;
                    Ok(promise)
                }
                DynamicImport::Pending(evaluation) => {
                    let promise = self.create_promise()?;
                    self.attach_dynamic_import_reactions(evaluation, promise, target)?;
                    Ok(promise)
                }
                DynamicImport::Failed(error) => {
                    let promise = self.create_promise()?;
                    self.reject_promise_failure(promise, import_failure(&error))?;
                    Ok(promise)
                }
            },
        }
    }

    fn dynamic_import_attributes(&mut self, options: Value) -> Result<Option<Value>, EvalFailure> {
        if options == Value::UNDEFINED {
            return Ok(None);
        }
        if !self.is_object(options) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "import options is not an object",
            }));
        }
        let with_key = PropertyKey::Named(self.intern_str("with"));
        let attributes = self.get_property_key(options, &with_key)?;
        if attributes != Value::UNDEFINED {
            return self.require_attributes_object(attributes);
        }
        let assert_key = PropertyKey::Named(self.intern_str("assert"));
        let attributes = self.get_property_key(options, &assert_key)?;
        self.require_attributes_object(attributes)
    }

    fn require_attributes_object(&self, attributes: Value) -> Result<Option<Value>, EvalFailure> {
        if attributes == Value::UNDEFINED {
            return Ok(None);
        }
        if !self.is_object(attributes) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "import attributes is not an object",
            }));
        }
        Ok(Some(attributes))
    }

    pub(crate) fn canonical_import_attributes(
        &mut self,
        attributes: Option<Value>,
    ) -> Result<(), EvalFailure> {
        let Some(attributes) = attributes else {
            return Ok(());
        };
        for key in self.internal_own_property_keys(attributes)? {
            if !self.own_property_is_enumerable(attributes, &key)? {
                continue;
            }
            let value = self.get_property_key(attributes, &key)?;
            if self.string_value(value).is_none() {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "import attribute value is not a string",
                }));
            }
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "import attributes are not supported by this host",
            }));
        }
        Ok(())
    }

    pub(crate) fn import_namespace_with_attributes(
        &mut self,
        requester: ModuleId,
        specifier: ConstantId,
        attributes: Value,
    ) -> Result<Value, EvalFailure> {
        self.canonical_import_attributes(Some(attributes))?;
        self.import_namespace(requester, specifier)
    }

    /// Reports whether the resolved dynamic edge also carries a static
    /// component; coalesced edges follow static namespace semantics.
    fn import_edge_has_static(&self, module: ModuleId, specifier: ConstantId) -> bool {
        let name = self.constant_text(module, specifier);
        self.program_module(module).edges.iter().any(|edge| {
            edge.kind.has_dynamic()
                && edge.kind.has_static()
                && self.constant_text(module, edge.specifier) == name
        })
    }

    /// Evaluates one module's static dependency graph and starts its entry.
    /// The DFS never drains the event loop: a dependency already in flight
    /// contributes one attached reaction per parent, and the module parks in
    /// [`ModuleState::EvaluatingAsync`] until the last dependency fulfills.
    /// Entry failures settle the module and propagate as `Err` exactly as
    /// before; [`ModuleStart::Pending`] replaces the old blocking wait.
    fn evaluate_module(&mut self, module: ModuleId) -> Result<ModuleStart, RuntimeError> {
        if let ModuleState::EvaluatingAsync {
            record, promise, ..
        } = &self.registry.modules[module.get() as usize].state
        {
            return Ok(ModuleStart::Pending(ModulePending {
                record: *record,
                promise: *promise,
            }));
        }
        let dependencies = match self.begin_module_evaluation(module)? {
            ModuleEvaluation::Cycle => return Ok(ModuleStart::Cached),
            ModuleEvaluation::Evaluated(result) => return result.map(|()| ModuleStart::Cached),
            ModuleEvaluation::Ready(dependencies) => dependencies,
        };
        let (pending_deps, pending_pair) = self.with_native_roots(&[], |machine| {
            machine.evaluate_dependencies(module, dependencies)
        })?;
        if pending_deps > 0 {
            let pair = pending_pair.expect("pending dependencies forced the shared pair");
            self.registry.modules[module.get() as usize].state = ModuleState::EvaluatingAsync {
                record: pair.record,
                promise: pair.promise,
                pending_deps,
            };
            return Ok(ModuleStart::Pending(pair));
        }
        let start = self.start_ready_entry(module, None);
        if let ModuleStart::Settled(result) = &start {
            // The async terminal turn already settled module state through
            // `settle_async_step`; `finish_module_evaluation` remains the
            // single state writer for synchronous entries.
            self.finish_module_evaluation(module, result.clone())?;
        }
        Ok(start)
    }

    /// Evaluates each static dependency of `module`, counting the pending
    /// ones. The shared pair is not in the module state until the count is
    /// known, so it stays in the innermost native root frame meanwhile.
    fn evaluate_dependencies(
        &mut self,
        module: ModuleId,
        dependencies: Vec<ModuleId>,
    ) -> Result<(usize, Option<ModulePending>), RuntimeError> {
        let mut pending_deps = 0usize;
        let mut pending_pair: Option<ModulePending> = None;
        for dependency in dependencies {
            match self.evaluate_module(dependency) {
                Ok(ModuleStart::Settled(_)) | Ok(ModuleStart::Cached) => {}
                Ok(ModuleStart::Pending(pair)) => {
                    if pending_pair.is_none() {
                        let shared = match self.create_module_async_pair(module) {
                            Ok(pair) => pair,
                            Err(failure) => {
                                return Err(self.module_alloc_failure(module, failure));
                            }
                        };
                        self.native_roots
                            .last_mut()
                            .expect("the caller pushed a native root frame")
                            .extend([shared.record, shared.promise]);
                        pending_pair = Some(shared);
                    }
                    if let Err(failure) = self.attach_module_reactions(module, pair.promise) {
                        return Err(self.module_alloc_failure(module, failure));
                    }
                    pending_deps += 1;
                }
                Err(error) => match self.finish_module_evaluation(module, Err(error)) {
                    Err(error) => return Err(error),
                    Ok(_) => unreachable!("a dependency failure stays an error"),
                },
            }
        }
        Ok((pending_deps, pending_pair))
    }

    /// Settles an allocation failure while starting or awaiting module
    /// evaluation: fatal kinds abort back to retryable [`ModuleState::Unevaluated`].
    fn module_alloc_failure(&mut self, module: ModuleId, failure: EvalFailure) -> RuntimeError {
        let error = self.module_eval_failure(module, failure);
        match self.finish_module_evaluation(module, Err(error)) {
            Err(error) => error,
            Ok(_) => unreachable!("an allocation failure stays an error"),
        }
    }

    pub(crate) fn begin_module_evaluation(
        &mut self,
        module: ModuleId,
    ) -> Result<ModuleEvaluation, RuntimeError> {
        match self.registry.modules[module.get() as usize].state.clone() {
            ModuleState::Evaluating | ModuleState::EvaluatingAsync { .. } => {
                return Ok(ModuleEvaluation::Cycle);
            }
            ModuleState::Evaluated(result) => return Ok(ModuleEvaluation::Evaluated(result)),
            ModuleState::Unevaluated => {}
        }
        self.registry.modules[module.get() as usize].state = ModuleState::Evaluating;

        let mut dependencies = Vec::new();
        for (edge_index, edge) in self
            .program_module(module)
            .edges
            .iter()
            .copied()
            .enumerate()
        {
            if !edge.kind.has_static() {
                continue;
            }
            match edge.target {
                EdgeTarget::Local(dependency) => dependencies.push(dependency),
                EdgeTarget::External
                    if self
                        .external_specifier(module, EdgeId::new(edge_index as u32))
                        .is_some() => {}
                EdgeTarget::External => {
                    let error = self.program_error(
                        module,
                        RuntimeErrorKind::ExternalModuleUnavailable {
                            module,
                            edge: EdgeId::new(edge_index as u32),
                        },
                    );
                    self.settle_module_evaluation(module, Err(error.clone()));
                    return Err(error);
                }
            }
        }
        Ok(ModuleEvaluation::Ready(dependencies))
    }

    pub(crate) fn finish_module_evaluation(
        &mut self,
        module: ModuleId,
        result: Result<Execution, RuntimeError>,
    ) -> Result<Execution, RuntimeError> {
        let stored = result.as_ref().map(|_| ()).map_err(Clone::clone);
        self.settle_module_evaluation(module, stored);
        result
    }

    pub(crate) fn settle_module_evaluation(
        &mut self,
        module: ModuleId,
        result: Result<(), RuntimeError>,
    ) {
        // Settled exactly once: an async terminal turn writes the terminal
        // state itself, and a later duplicate write (for example a native
        // caller's `finish_module_evaluation` after `run_module_entry`)
        // carries the identical stored result.
        if matches!(
            self.registry.modules[module.get() as usize].state,
            ModuleState::Evaluated(_)
        ) {
            return;
        }
        // A fatal error stores nothing, and it can reach a module that an inner turn
        // already aborted, so it comes before the check of the state.
        if matches!(&result, Err(error) if !matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }))
        {
            self.abort_module_evaluation(module);
            return;
        }
        debug_assert!(
            matches!(
                self.registry.modules[module.get() as usize].state,
                ModuleState::Evaluating | ModuleState::EvaluatingAsync { .. }
            ),
            "only an in-flight module settles"
        );
        self.registry.modules[module.get() as usize].state = ModuleState::Evaluated(result);
    }

    pub(crate) fn abort_module_evaluation(&mut self, module: ModuleId) {
        if matches!(
            self.registry.modules[module.get() as usize].state,
            ModuleState::Evaluating | ModuleState::EvaluatingAsync { .. }
        ) {
            self.registry.modules[module.get() as usize].state = ModuleState::Unevaluated;
        }
    }

    pub(crate) fn constant_text(&self, module: ModuleId, id: ConstantId) -> &EcmaString {
        match &self.module_code(module).constants()[id.get() as usize] {
            Constant::String(text) => text,
            _ => unreachable!("verified module names are strings"),
        }
    }

    fn program_error(&self, module: ModuleId, kind: RuntimeErrorKind) -> RuntimeError {
        let code = self.module_code(module);
        let function = code.entry().get() as usize;
        let instruction = code.functions()[function]
            .code()
            .first()
            .copied()
            .unwrap_or(Instruction::Halt);
        RuntimeError {
            kind,
            function: FunctionId::new(function as u32),
            pc: Pc::new(0),
            source: RuntimeSource {
                function_name: None,
                instruction,
            },
        }
    }

    fn run_loop(&mut self, stop_depth: usize) -> Result<Option<Execution>, RuntimeError> {
        if self.frames.len().saturating_add(self.native_depth) > self.limits.max_call_depth
            || self.native_stack_exhausted()
        {
            return Err(self.error_here(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            }));
        }
        if self.live_registers > self.limits.max_total_registers {
            return Err(self.error_here(RuntimeErrorKind::RegisterLimitExceeded {
                limit: self.limits.max_total_registers,
            }));
        }

        loop {
            let frame_index = self.frames.len() - 1;
            let (module_id, function_index, pc) = {
                let frame = &self.frames[frame_index];
                (frame.module, frame.function, frame.pc)
            };
            if let Err(kind) = self.consume_fuel(1) {
                return Err(self.error_at(kind, function_index, pc));
            }
            self.collect_if_pending();
            let instruction = self.module_code(module_id).functions()[function_index].code()[pc];

            match instruction {
                Instruction::LoadConst { dst, constant } => {
                    let value = self.load_constant(constant, function_index, pc)?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::Move { dst, src } => {
                    let value = self.read_register(frame_index, src.get());
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::Unary { dst, op, operand } => {
                    let value = self.read_register(frame_index, operand.get());
                    match self.eval_unary(op, value) {
                        Ok(result) => {
                            self.write_register(frame_index, dst.get(), result);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::Binary {
                    dst,
                    op,
                    left,
                    right,
                } => {
                    let left = self.read_register(frame_index, left.get());
                    let right = self.read_register(frame_index, right.get());
                    match self.eval_binary(op, left, right) {
                        Ok(result) => {
                            self.write_register(frame_index, dst.get(), result);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::CreateObject { dst } => {
                    let value = self
                        .allocate(HeapEntry::Object {
                            properties: PropertyMap::default(),
                            prototype: Some(self.intrinsics.object_prototype),
                            boxed_primitive: None,
                            extensible: true,
                        })
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::ToObject { dst, src } => {
                    let source = self.read_register(frame_index, src.get());
                    match self.value_to_object(source) {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::CreateArray { dst } => {
                    let value = self
                        .allocate(HeapEntry::Array {
                            kind: ArrayElementKind::for_elements(&[]),
                            elements: Vec::new(),
                            properties: PropertyMap::default(),
                            prototype: Some(self.intrinsics.array_prototype),
                            extensible: true,
                            length_writable: true,
                        })
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::CreateCell { dst } => {
                    let elements = vec![Value::UNINITIALIZED];
                    let value = self
                        .allocate(HeapEntry::Array {
                            kind: ArrayElementKind::for_elements(&elements),
                            elements,
                            properties: PropertyMap::default(),
                            prototype: Some(self.intrinsics.array_prototype),
                            extensible: true,
                            length_writable: true,
                        })
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::CreateClosure {
                    dst,
                    function,
                    captures,
                } => match self.read_captures(frame_index, captures.get(), function) {
                    Ok(captures) => {
                        let properties = self
                            .closure_properties(module_id, function)
                            .map_err(|kind| self.error_at(kind, function_index, pc))?;
                        let value = self
                            .allocate(HeapEntry::Function {
                                module: module_id,
                                function,
                                captures,
                                context: self.frames[frame_index].context,
                                properties,
                                prototype: Some(self.closure_prototype(module_id, function)),
                                extensible: true,
                            })
                            .map_err(|kind| self.error_at(kind, function_index, pc))?;
                        self.write_register(frame_index, dst.get(), value);
                        self.frames[frame_index].pc = pc + 1;
                    }
                    Err(failure) => self.resolve_failure(failure, pc)?,
                },
                Instruction::GetProperty { dst, object, key } => {
                    let object = self.read_register(frame_index, object.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.computed_property_key(object, key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    let hit = self.property_site_hit_get(
                        module_id,
                        FunctionId::new(function_index as u32),
                        pc,
                        object,
                        &key,
                    );
                    let result = match hit {
                        Some(value) => Ok(value),
                        None => {
                            let value = self.internal_get(object, &key, object);
                            if value.is_ok() {
                                self.property_site_record_get(
                                    module_id,
                                    FunctionId::new(function_index as u32),
                                    pc,
                                    object,
                                    &key,
                                );
                            }
                            value
                        }
                    };
                    match result {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::SetProperty { object, key, value } => {
                    let object = self.read_register(frame_index, object.get());
                    let value = self.read_register(frame_index, value.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.computed_property_key(object, key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    let hit = self.property_site_hit_set(
                        module_id,
                        FunctionId::new(function_index as u32),
                        pc,
                        object,
                        &key,
                        value,
                    );
                    let result = if hit.is_some() {
                        Ok(true)
                    } else {
                        let stored = self.internal_set(object, key.clone(), value, object);
                        if matches!(stored, Ok(true)) {
                            self.property_site_record_set(
                                module_id,
                                FunctionId::new(function_index as u32),
                                pc,
                                object,
                                &key,
                            );
                        }
                        stored
                    };
                    match result {
                        Ok(true) => self.frames[frame_index].pc = pc + 1,
                        Ok(false) if self.is_sloppy(module_id, function_index) => {
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Ok(false) => {
                            self.resolve_failure(
                                EvalFailure::Throw(ThrowOrigin::TypeError {
                                    operation: "assign to read only property",
                                }),
                                pc,
                            )?;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::DeleteProperty { dst, object, key } => {
                    let object = self.read_register(frame_index, object.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.computed_property_key(object, key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    let deleted = self.internal_delete(object, &key).and_then(|deleted| {
                        self.deletion_result(module_id, function_index, deleted)
                    });
                    match deleted {
                        Ok(deleted) => {
                            self.write_register(frame_index, dst.get(), Value::boolean(deleted));
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::DefineAccessor {
                    object,
                    key,
                    accessor,
                    kind,
                } => {
                    let object = self.read_register(frame_index, object.get());
                    let accessor = self.read_register(frame_index, accessor.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.observable_property_key(key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    match self.define_accessor(object, key, accessor, kind) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::DefineDataProperty { object, key, value } => {
                    let object = self.read_register(frame_index, object.get());
                    let value = self.read_register(frame_index, value.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.observable_property_key(key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    match self.define_descriptor(
                        object,
                        key,
                        Property::Data {
                            value,
                            writable: true,
                            enumerable: false,
                            configurable: true,
                        },
                    ) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::LoadOwnDescriptorSlot {
                    dst,
                    object,
                    key,
                    slot,
                } => {
                    let object = self.read_register(frame_index, object.get());
                    let key = self.read_register(frame_index, key.get());
                    match self.load_own_descriptor_slot(object, key, slot) {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::DefineOwnDescriptorSlot {
                    object,
                    key,
                    src,
                    slot,
                } => {
                    let object = self.read_register(frame_index, object.get());
                    let key = self.read_register(frame_index, key.get());
                    let src = self.read_register(frame_index, src.get());
                    match self.define_own_descriptor_slot(object, key, src, slot) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::Call {
                    dst,
                    callee,
                    this_value,
                    arguments,
                } => {
                    let callee = self.read_register(frame_index, callee.get());
                    let this_value = self.read_register(frame_index, this_value.get());
                    match self.read_arguments(frame_index, arguments.get()) {
                        Ok(arguments) => {
                            self.frames[frame_index].pc = pc + 1;
                            self.execute_call(CallRequest {
                                callee,
                                this_value,
                                arguments: &arguments,
                                destination: Some(dst.get()),
                                call_pc: pc,
                                constructed: None,
                                new_target: Value::UNDEFINED,
                            })?;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::Construct {
                    dst,
                    callee,
                    arguments,
                } => {
                    let callee = self.read_register(frame_index, callee.get());
                    match self.read_arguments(frame_index, arguments.get()) {
                        Ok(arguments) => {
                            self.frames[frame_index].pc = pc + 1;
                            self.execute_construct(callee, callee, &arguments, dst.get(), pc)?;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ConstructWithNewTarget {
                    dst,
                    callee,
                    new_target,
                    arguments,
                } => {
                    let callee = self.read_register(frame_index, callee.get());
                    let new_target = self.read_register(frame_index, new_target.get());
                    match self.read_arguments(frame_index, arguments.get()) {
                        Ok(arguments) => {
                            self.frames[frame_index].pc = pc + 1;
                            self.execute_construct(callee, new_target, &arguments, dst.get(), pc)?;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::LoadGlobal { dst, name } => match self.load_global(module_id, name) {
                    Ok(Some(value)) => {
                        self.write_register(frame_index, dst.get(), value);
                        self.frames[frame_index].pc = pc + 1;
                    }
                    Ok(None) => self.throw(
                        Value::UNDEFINED,
                        ThrowOrigin::ReferenceError {
                            operation: "global is not defined",
                        },
                        pc,
                    )?,
                    Err(failure) => self.resolve_failure(failure, pc)?,
                },
                Instruction::StoreGlobal { name, value } => {
                    let value = self.read_register(frame_index, value.get());
                    let sloppy = self.is_sloppy(module_id, function_index);
                    match self.store_global(module_id, name, value, sloppy) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::TypeOfGlobal { dst, name } => {
                    match self.load_global(module_id, name) {
                        Ok(value) => {
                            let text = value.map_or("undefined", |value| self.type_of(value));
                            let value = self
                                .allocate(HeapEntry::String(EcmaString::encode(text)))
                                .map_err(|kind| self.error_at(kind, function_index, pc))?;
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::LoadThis { dst } => {
                    let this_value = self.frames[frame_index].this_value;
                    match self.bind_this(module_id, function_index, this_value) {
                        Ok(value) => {
                            self.frames[frame_index].this_value = value;
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::LoadArguments { dst } => {
                    let value = self.materialize_arguments(frame_index, function_index, pc)?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::LoadNewTarget { dst } => {
                    let value = self.frames[frame_index].new_target;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::LoadImportMeta { dst } => {
                    let value = self
                        .load_import_meta(module_id)
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::ArrayPush { array, value } => {
                    let array = self.read_register(frame_index, array.get());
                    let value = self.read_register(frame_index, value.get());
                    match self.array_push(array, value) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ArrayExtend { array, iterable } => {
                    let array = self.read_register(frame_index, array.get());
                    let iterable = self.read_register(frame_index, iterable.get());
                    match self.array_extend(array, iterable) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ObjectSpread { target, source } => {
                    let target = self.read_register(frame_index, target.get());
                    let source = self.read_register(frame_index, source.get());
                    match self.object_spread(target, source) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::SetPrototype { object, prototype } => {
                    let object = self.read_register(frame_index, object.get());
                    let prototype = self.read_register(frame_index, prototype.get());
                    match self.set_prototype(object, prototype) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::CreatePrivateName { dst, description } => {
                    let description = self.constant_string(description).clone();
                    let value = self
                        .allocate(HeapEntry::PrivateName { description })
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::CreateRegExp {
                    dst,
                    pattern,
                    flags,
                } => {
                    let pattern = self.constant_string(pattern).clone();
                    let flags = self.constant_string(flags).clone();
                    let properties = intrinsics::builtins::initial_regexp_properties(
                        &mut self.atoms,
                        &mut self.shapes,
                    );
                    let value = self
                        .allocate(HeapEntry::RegExp {
                            pattern,
                            flags,
                            properties,
                            prototype: Some(self.intrinsics.regexp_prototype()),
                            extensible: true,
                        })
                        .map_err(|kind| self.error_at(kind, function_index, pc))?;
                    self.write_register(frame_index, dst.get(), value);
                    self.frames[frame_index].pc = pc + 1;
                }
                Instruction::GetIterator { dst, src, kind } => {
                    let src = self.read_register(frame_index, src.get());
                    match self.create_iterator(src, kind) {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::IteratorNext {
                    done,
                    value,
                    iterator,
                } => {
                    let iterator = self.read_register(frame_index, iterator.get());
                    match self.iterator_next(iterator) {
                        Ok((is_done, produced)) => {
                            self.write_register(frame_index, done.get(), Value::boolean(is_done));
                            self.write_register(frame_index, value.get(), produced);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::IteratorStep { dst, iterator } => {
                    let iterator = self.read_register(frame_index, iterator.get());
                    match self.iterator_step(iterator) {
                        Ok(result) => {
                            self.write_register(frame_index, dst.get(), result);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::IteratorResult {
                    done,
                    value,
                    result,
                } => {
                    let result = self.read_register(frame_index, result.get());
                    match self.iterator_result_parts(result) {
                        Ok((is_done, produced)) => {
                            self.write_register(frame_index, done.get(), Value::boolean(is_done));
                            self.write_register(frame_index, value.get(), produced);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::IteratorClose {
                    result,
                    called,
                    iterator,
                    mode,
                } => {
                    let iterator = self.read_register(frame_index, iterator.get());
                    let (close, was_called) = self.close_iterator_raw(iterator);
                    match (close, mode) {
                        (Ok(value), _) => {
                            self.write_register(
                                frame_index,
                                called.get(),
                                Value::boolean(was_called),
                            );
                            self.write_register(frame_index, result.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        (Err(EvalFailure::Runtime(kind)), _) => {
                            return Err(self.error_here_at(kind, pc));
                        }
                        (Err(failure), IteratorCloseMode::Propagate) => {
                            self.resolve_failure(failure, pc)?;
                        }
                        (Err(_), IteratorCloseMode::PreserveAbrupt) => {
                            self.write_register(
                                frame_index,
                                called.get(),
                                Value::boolean(was_called),
                            );
                            self.write_register(frame_index, result.get(), Value::UNDEFINED);
                            self.frames[frame_index].pc = pc + 1;
                        }
                    }
                }
                Instruction::RequireCloseResult { result, called } => {
                    let result = self.read_register(frame_index, result.get());
                    let called = self.read_register(frame_index, called.get());
                    if called == Value::TRUE && !self.is_object(result) {
                        self.resolve_failure(
                            EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "iterator.return() returned a non-object",
                            }),
                            pc,
                        )?;
                    } else {
                        self.frames[frame_index].pc = pc + 1;
                    }
                }
                Instruction::DisposeCapture {
                    method,
                    kind,
                    src,
                    hint,
                } => {
                    let src = self.read_register(frame_index, src.get());
                    match self.dispose_capture_raw(src, hint) {
                        Ok((captured_method, captured_kind)) => {
                            self.write_register(frame_index, method.get(), captured_method);
                            self.write_register(
                                frame_index,
                                kind.get(),
                                Value::int32(captured_kind),
                            );
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::SuppressError {
                    dst,
                    error,
                    suppressed,
                } => {
                    let error = self.read_register(frame_index, error.get());
                    let suppressed = self.read_register(frame_index, suppressed.get());
                    match self.make_suppressed_error(error, suppressed) {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::WithHasBinding { dst, object, key } => {
                    let object = self.read_register(frame_index, object.get());
                    let key = self.read_register(frame_index, key.get());
                    match self.with_has_binding(object, key) {
                        Ok(found) => {
                            self.write_register(frame_index, dst.get(), Value::boolean(found));
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::Jump { target } => {
                    self.frames[frame_index].pc = target.get() as usize;
                }
                Instruction::JumpIfTrue { condition, target } => {
                    let condition = self.read_register(frame_index, condition.get());
                    self.frames[frame_index].pc = if self.truthy(condition) {
                        target.get() as usize
                    } else {
                        pc + 1
                    };
                }
                Instruction::JumpIfFalse { condition, target } => {
                    let condition = self.read_register(frame_index, condition.get());
                    self.frames[frame_index].pc = if self.truthy(condition) {
                        pc + 1
                    } else {
                        target.get() as usize
                    };
                }
                Instruction::Return { value } => {
                    let value = self.read_register(frame_index, value.get());
                    if let Some(execution) = self.complete_frame(value) {
                        return Ok(Some(execution));
                    }
                    if self.frames.len() == stop_depth {
                        return Ok(None);
                    }
                }
                Instruction::Throw { value } => {
                    let value = self.read_register(frame_index, value.get());
                    self.throw(value, ThrowOrigin::Bytecode, pc)?;
                }
                Instruction::Await { src, .. }
                    if self
                        .async_boundaries
                        .last()
                        .is_some_and(|boundary| *boundary == frame_index) =>
                {
                    let awaited = self.read_register(frame_index, src.get());
                    let frame = self.frames.pop().expect("async activation is executing");
                    self.context_global = frame.outer_context;
                    self.pending_async_suspend = Some((
                        awaited,
                        SuspendedActivation {
                            target: RuntimeFunction {
                                module: frame.module,
                                function: FunctionId::new(frame.function as u32),
                            },
                            registers: frame.registers,
                            this_value: frame.this_value,
                            new_target: frame.new_target,
                            args: frame.args,
                            context: frame.context,
                            arguments_object: frame.arguments_object,
                            resume_token: pc as u32 + 1,
                        },
                    ));
                    return Ok(None);
                }
                Instruction::Suspend { src, .. }
                    if self
                        .generator_boundaries
                        .last()
                        .is_some_and(|boundary| *boundary == frame_index) =>
                {
                    let value = self.read_register(frame_index, src.get());
                    let frame = self
                        .frames
                        .pop()
                        .expect("generator activation is executing");
                    self.context_global = frame.outer_context;
                    self.pending_generator_resume = Some(GeneratorResume::Yield {
                        value,
                        activation: SuspendedActivation {
                            target: RuntimeFunction {
                                module: frame.module,
                                function: FunctionId::new(frame.function as u32),
                            },
                            registers: frame.registers,
                            this_value: frame.this_value,
                            new_target: frame.new_target,
                            args: frame.args,
                            arguments_object: frame.arguments_object,
                            context: frame.context,
                            resume_token: pc as u32 + 1,
                        },
                    });
                    return Ok(None);
                }
                Instruction::Suspend { .. } => {
                    self.throw_type("suspend outside an engine-owned event loop", pc)?;
                }
                Instruction::Await { .. } => {
                    self.throw_type("await outside an engine-owned event loop", pc)?;
                }
                Instruction::Import { dst, specifier } => {
                    match self.import_namespace(module_id, specifier) {
                        Ok(namespace) => {
                            self.write_register(frame_index, dst.get(), namespace);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ImportDynamic { dst, specifier } => {
                    let specifier = self.read_register(frame_index, specifier.get());
                    match self.import_dynamic_expression(module_id, specifier) {
                        Ok(promise) => {
                            self.write_register(frame_index, dst.get(), promise);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::GetSuper {
                    dst,
                    home,
                    receiver,
                    key,
                } => {
                    let home = self.read_register(frame_index, home.get());
                    let receiver = self.read_register(frame_index, receiver.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.observable_property_key(key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    match self.get_super(home, receiver, &key) {
                        Ok(value) => {
                            self.write_register(frame_index, dst.get(), value);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::SetSuper {
                    home,
                    receiver,
                    key,
                    value,
                } => {
                    let home = self.read_register(frame_index, home.get());
                    let receiver = self.read_register(frame_index, receiver.get());
                    let key_value = self.read_register(frame_index, key.get());
                    let key = match self.observable_property_key(key_value) {
                        Ok(key) => key,
                        Err(failure) => {
                            self.resolve_failure(failure, pc)?;
                            continue;
                        }
                    };
                    let value = self.read_register(frame_index, value.get());
                    match self.set_super(home, receiver, key, value) {
                        Ok(SetOutcome::Done) => self.frames[frame_index].pc = pc + 1,
                        Ok(SetOutcome::Setter(setter)) => {
                            self.frames[frame_index].pc = pc + 1;
                            self.execute_call(CallRequest {
                                callee: setter,
                                this_value: receiver,
                                arguments: &[value],
                                destination: None,
                                call_pc: pc,
                                constructed: None,
                                new_target: Value::UNDEFINED,
                            })?;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ImportAttributes {
                    dst,
                    specifier,
                    attributes,
                } => {
                    let attributes = self.read_register(frame_index, attributes.get());
                    match self.import_namespace_with_attributes(module_id, specifier, attributes) {
                        Ok(namespace) => {
                            self.write_register(frame_index, dst.get(), namespace);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ImportDynamicAttributes {
                    dst,
                    specifier,
                    attributes,
                } => {
                    let specifier = self.read_register(frame_index, specifier.get());
                    let attributes = self.read_register(frame_index, attributes.get());
                    match self
                        .import_dynamic_expression_with_attributes(module_id, specifier, attributes)
                    {
                        Ok(promise) => {
                            self.write_register(frame_index, dst.get(), promise);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::CopyDataProperties {
                    target,
                    source,
                    excluded,
                } => {
                    let target = self.read_register(frame_index, target.get());
                    let source = self.read_register(frame_index, source.get());
                    let excluded = self.read_register(frame_index, excluded.get());
                    match self.copy_data_properties(target, source, excluded) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::GetTemplateObject { dst, cooked, raw } => {
                    let cooked = self.read_register(frame_index, cooked.get());
                    let raw = self.read_register(frame_index, raw.get());
                    match self.template_object(cooked, raw) {
                        Ok(template) => {
                            self.write_register(frame_index, dst.get(), template);
                            self.frames[frame_index].pc = pc + 1;
                        }
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::RequireGlobalBinding { name } => {
                    match self.require_global_binding(module_id, name) {
                        Ok(()) => self.frames[frame_index].pc = pc + 1,
                        Err(failure) => self.resolve_failure(failure, pc)?,
                    }
                }
                Instruction::ThrowIntrinsicError { kind, message } => {
                    let failure = self.throw_intrinsic_error(module_id, kind, message);
                    self.resolve_failure(failure, pc)?;
                }
                Instruction::Export { .. } => {
                    return Err(self.error_here_at(
                        RuntimeErrorKind::InvalidVerifiedProgram {
                            module: module_id,
                            instruction,
                        },
                        pc,
                    ));
                }
                Instruction::Halt => {
                    if let Some(execution) = self.complete_frame(Value::UNDEFINED) {
                        return Ok(Some(execution));
                    }
                    if self.frames.len() == stop_depth {
                        return Ok(None);
                    }
                }
            }
        }
    }

    fn read_register(&self, frame: usize, register: u32) -> Value {
        self.frames[frame].registers[register as usize]
    }

    fn write_register(&mut self, frame: usize, register: u32, value: Value) {
        self.frames[frame].registers[register as usize] = value;
    }

    fn constant_string(&self, id: ConstantId) -> &EcmaString {
        self.constant_text(self.active_module_id(), id)
    }

    fn load_constant(
        &mut self,
        id: ConstantId,
        function: usize,
        pc: usize,
    ) -> Result<Value, RuntimeError> {
        self.load_constant_value(self.active_module_id(), id)
            .map_err(|kind| self.error_at(kind, function, pc))
    }

    fn allocate(&mut self, entry: HeapEntry) -> Result<Value, RuntimeErrorKind> {
        let bytes = entry.initial_bytes(&self.shapes, &self.atoms);
        self.ensure_allocation_capacity(1, bytes)?;
        self.sync_slot_ledger();
        let index = if let Some(index) = self.gc.free_slots.pop() {
            debug_assert!(index < self.heap.len());
            debug_assert!(index >= self.intrinsic_slots);
            self.heap.fill_vacant(index, entry);
            self.slot_bytes[index] = bytes;
            self.vacant_count -= 1;
            self.gc.young_reused.push(index);
            index
        } else {
            let index = self.heap.len();
            self.heap.push(entry);
            self.slot_bytes.push(bytes);
            index
        };
        self.heap_bytes += bytes;
        let slot = index as u32 + 1;
        let id = SlotId::from_parts(RUNTIME_HEAP_SEGMENT, slot)
            .expect("runtime segment and one-based slot are nonzero");
        self.request_garbage_collection();
        let value = Value::heap_ref(id);
        if self.in_builtin {
            self.builtin_temporaries.push(value);
        }
        Ok(value)
    }

    fn live_runtime_slots(&self) -> usize {
        self.heap.len() - self.intrinsic_slots - self.vacant_count
    }

    fn request_garbage_collection(&mut self) {
        self.gc
            .request_collection(self.heap_bytes, self.live_runtime_slots());
    }

    fn ensure_allocation_capacity(
        &self,
        additional_slots: usize,
        additional_bytes: usize,
    ) -> Result<(), RuntimeErrorKind> {
        let used_slots = self.live_runtime_slots();
        let slots_fit_limit = used_slots
            .checked_add(additional_slots)
            .is_some_and(|total| total <= self.limits.max_heap_slots);
        let slots_fit_value = self
            .heap
            .len()
            .checked_add(additional_slots)
            .is_some_and(|total| total <= u32::MAX as usize);
        if !slots_fit_limit || !slots_fit_value {
            return Err(RuntimeErrorKind::HeapSlotLimitExceeded {
                limit: self.limits.max_heap_slots,
            });
        }
        let bytes_fit = self
            .heap_bytes
            .checked_add(additional_bytes)
            .is_some_and(|total| total <= self.limits.max_heap_bytes);
        if !bytes_fit {
            return Err(RuntimeErrorKind::HeapByteLimitExceeded {
                limit: self.limits.max_heap_bytes,
            });
        }
        Ok(())
    }

    fn ensure_object_property_capacity(
        &self,
        property_bytes: usize,
    ) -> Result<(), RuntimeErrorKind> {
        let bytes =
            property_bytes
                .checked_add(1)
                .ok_or(RuntimeErrorKind::HeapByteLimitExceeded {
                    limit: self.limits.max_heap_bytes,
                })?;
        self.ensure_allocation_capacity(1, bytes)
    }
    pub(crate) fn charge_slot(
        &mut self,
        index: usize,
        bytes: usize,
    ) -> Result<(), RuntimeErrorKind> {
        self.sync_slot_ledger();
        let credited = self
            .intrinsic_slot_credits
            .get(index)
            .copied()
            .unwrap_or(0)
            .min(bytes);
        let charged = bytes - credited;
        self.ensure_allocation_capacity(0, charged)?;
        if let Some(credit) = self.intrinsic_slot_credits.get_mut(index) {
            *credit -= credited;
        }
        self.slot_bytes[index] += charged;
        self.heap_bytes += charged;
        self.request_garbage_collection();
        Ok(())
    }

    pub(crate) fn refund_slot(&mut self, index: usize, bytes: usize) {
        self.sync_slot_ledger();
        if let Some(credit) = self.intrinsic_slot_credits.get_mut(index) {
            let refunded = self.slot_bytes[index].min(bytes);
            self.slot_bytes[index] -= refunded;
            self.heap_bytes = self
                .heap_bytes
                .checked_sub(refunded)
                .expect("slot refund cannot exceed heap charge");
            *credit = credit
                .checked_add(bytes - refunded)
                .expect("intrinsic slot credit cannot overflow");
            return;
        }
        debug_assert!(self.slot_bytes[index] >= bytes);
        debug_assert!(self.heap_bytes >= bytes);
        self.slot_bytes[index] = self.slot_bytes[index]
            .checked_sub(bytes)
            .expect("slot refund cannot exceed its charge");
        self.heap_bytes = self
            .heap_bytes
            .checked_sub(bytes)
            .expect("slot refund cannot exceed heap charge");
    }

    fn transfer_slot_to_machine(&mut self, index: usize, bytes: usize) {
        self.sync_slot_ledger();
        self.slot_bytes[index] = self.slot_bytes[index]
            .checked_sub(bytes)
            .expect("slot transfer cannot exceed its charge");
        self.machine_bytes = self
            .machine_bytes
            .checked_add(bytes)
            .expect("machine charge cannot overflow");
    }

    fn transfer_slot_charge(&mut self, from: usize, to: usize, bytes: usize) {
        self.sync_slot_ledger();
        self.slot_bytes[from] = self.slot_bytes[from]
            .checked_sub(bytes)
            .expect("slot transfer cannot exceed its charge");
        self.slot_bytes[to] = self.slot_bytes[to]
            .checked_add(bytes)
            .expect("slot charge cannot overflow");
    }

    fn sync_slot_ledger(&mut self) {
        debug_assert!(self.slot_bytes.len() <= self.heap.len());
        self.slot_bytes.resize(self.heap.len(), 0);
    }

    pub(crate) fn charge_machine(&mut self, bytes: usize) -> Result<(), RuntimeErrorKind> {
        self.ensure_allocation_capacity(0, bytes)?;
        self.machine_bytes += bytes;
        self.heap_bytes += bytes;
        self.request_garbage_collection();
        Ok(())
    }

    fn refund_machine(&mut self, bytes: usize) {
        debug_assert!(self.machine_bytes >= bytes);
        debug_assert!(self.heap_bytes >= bytes);
        self.machine_bytes = self
            .machine_bytes
            .checked_sub(bytes)
            .expect("machine refund cannot exceed its charge");
        self.heap_bytes = self
            .heap_bytes
            .checked_sub(bytes)
            .expect("machine refund cannot exceed heap charge");
    }

    #[cfg(test)]
    fn assert_heap_ledger(&self) {
        assert_eq!(self.slot_bytes.len(), self.heap.len());
        assert_eq!(
            self.heap_bytes,
            self.machine_bytes + self.slot_bytes.iter().sum::<usize>()
        );
    }

    fn runtime_slot(&self, value: Value) -> Result<Option<usize>, RuntimeErrorKind> {
        let Some(decoded) = value.decode() else {
            return Err(RuntimeErrorKind::InvalidValue { value });
        };
        let Decoded::HeapRef(id) = decoded else {
            return Ok(None);
        };
        if id.segment() != RUNTIME_HEAP_SEGMENT {
            return Err(RuntimeErrorKind::InvalidValue { value });
        }
        let index = id.slot() as usize - 1;
        if index >= self.heap.len() || matches!(self.heap[index], HeapEntry::Vacant) {
            return Err(RuntimeErrorKind::InvalidRuntimeHeapReference { slot: id.slot() });
        }
        Ok(Some(index))
    }

    fn active_module_id(&self) -> ModuleId {
        self.frames
            .last()
            .map_or(ModuleId::new(0), |frame| frame.module)
    }

    pub(crate) fn load_global(
        &mut self,
        module: ModuleId,
        name: ConstantId,
    ) -> Result<Option<Value>, EvalFailure> {
        if let Some(cell) = self
            .registry
            .modules
            .get(module.get() as usize)
            .and_then(|instance| instance.constant_cells.get(name.get() as usize))
            .copied()
            .flatten()
        {
            let value = self.registry.cells[cell.0].value;
            if value.is_uninitialized() {
                return Err(self.uninitialized_read());
            }
            return Ok(Some(value));
        }
        let atom = self.global_name_atom(module, name);
        let key = PropertyKey::Named(atom);
        let global = self.context_global.unwrap_or(self.global_object);
        if self.internal_has_property(global, &key)? {
            return self.get_property_key(global, &key).map(Some);
        }
        self.missing_global = Some(self.resolve_atom(atom).clone());
        Ok(None)
    }

    /// `PutValue` on an unresolvable reference in strict code: a declarative
    /// global binding or any property the global object has, inherited ones
    /// included, is bound. No getter runs; a binding in its temporal dead
    /// zone throws the same `ReferenceError` a read would.
    pub(crate) fn require_global_binding(
        &mut self,
        module: ModuleId,
        name: ConstantId,
    ) -> Result<(), EvalFailure> {
        if let Some(cell) = self
            .registry
            .modules
            .get(module.get() as usize)
            .and_then(|instance| instance.constant_cells.get(name.get() as usize))
            .copied()
            .flatten()
        {
            if self.registry.cells[cell.0].value.is_uninitialized() {
                return Err(self.uninitialized_read());
            }
            return Ok(());
        }
        let atom = self.global_name_atom(module, name);
        let key = PropertyKey::Named(atom);
        let global = self.context_global.unwrap_or(self.global_object);
        if self.internal_has_property(global, &key)? {
            return Ok(());
        }
        let name = self.resolve_atom(atom).clone();
        let mut message = EcmaStringBuilder::new();
        for &unit in name.as_units() {
            message.push_unit(unit);
        }
        message.push_utf8(" is not defined");
        Err(self.intrinsic_error("ReferenceError", message.finish()))
    }

    fn intern(&mut self, text: EcmaString) -> Atom {
        self.atoms.intern(text)
    }
    /// The atom of a global-name constant. Program load interned every such
    /// name, so this is one lookup by reference; the text is copied only for a
    /// name load did not see.
    fn global_name_atom(&mut self, module: ModuleId, name: ConstantId) -> Atom {
        if let Some(atom) = self.atoms.find_text(self.constant_text(module, name)) {
            return atom;
        }
        let text = self.constant_text(module, name).to_owned();
        self.intern(text)
    }
    fn intern_str(&mut self, text: &str) -> Atom {
        self.atoms.intern_str(text)
    }
    fn resolve_atom(&self, atom: Atom) -> &EcmaString {
        self.atoms.resolve(atom)
    }
    pub(crate) fn computed_property_key(
        &mut self,
        object: Value,
        key: Value,
    ) -> Result<PropertyKey, EvalFailure> {
        if matches!(object.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "access a property of null or undefined",
            }));
        }
        self.observable_property_key(key)
    }

    /// The `[[Prototype]]` a new closure starts with, which depends on its kind.
    pub(crate) fn closure_prototype(&self, module: ModuleId, function: FunctionId) -> Value {
        let flags = self.module_code(module).functions()[function.get() as usize].flags();
        let builtins = &self.intrinsics.builtins;
        match (flags.is_async, flags.is_generator) {
            (false, false) => self.intrinsics.function_prototype,
            (false, true) => builtins.generator_function_prototype(),
            (true, false) => builtins.async_function_prototype(),
            (true, true) => builtins.async_generator_function_prototype(),
        }
    }

    /// The own properties a new closure starts with. A generator function owns
    /// the `prototype` object its kind requires, which the compiler emits only
    /// for constructors; every other property of a closure is materialized on
    /// demand.
    pub(crate) fn closure_properties(
        &mut self,
        module: ModuleId,
        function: FunctionId,
    ) -> Result<PropertyMap, RuntimeErrorKind> {
        let flags = self.module_code(module).functions()[function.get() as usize].flags();
        let mut properties = PropertyMap::default();
        if flags.is_generator {
            let builtins = &self.intrinsics.builtins;
            let parent = if flags.is_async {
                builtins.async_generator_prototype()
            } else {
                builtins.generator_prototype()
            };
            let value = self.allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(parent),
                extensible: true,
                boxed_primitive: None,
            })?;
            let prototype_key = PropertyKey::Named(self.intern_str("prototype"));
            properties.insert(
                &mut self.shapes,
                prototype_key,
                Property::Data {
                    value,
                    writable: true,
                    enumerable: false,
                    configurable: false,
                },
            );
        }
        Ok(properties)
    }

    /// A function's `length` and `name` come from its code until something could
    /// tell that from stored properties: a descriptor read, a key list, a delete or
    /// a redefinition stores them first, ahead of whatever is already stored.
    pub(crate) fn reify_function_properties(&mut self, index: usize) -> Result<(), EvalFailure> {
        let reified = self.intrinsics.builtins.function_reified_key();
        let name_key = PropertyKey::Named(self.intern_str("name"));
        let length_key = PropertyKey::Named(self.intern_str("length"));
        let HeapEntry::Function {
            module,
            function,
            properties,
            ..
        } = &self.heap[index]
        else {
            return Ok(());
        };
        if properties.contains_key(&self.shapes, &reified) {
            return Ok(());
        }
        let metadata = &self.module_code(*module).functions()[function.get() as usize];
        let length = (!properties.contains_key(&self.shapes, &length_key))
            .then(|| number_value(metadata.parameter_count() as f64));
        let name = (!properties.contains_key(&self.shapes, &name_key)).then(|| {
            metadata
                .name()
                .map(|id| self.constant_text(*module, id).clone())
                .unwrap_or_default()
        });
        let name = name
            .map(|text| self.allocate(HeapEntry::String(text)))
            .transpose()
            .map_err(EvalFailure::Runtime)?;
        let mut stored = PropertyMap::default();
        for (key, value) in [(length_key, length), (name_key, name)] {
            if let Some(value) = value {
                stored.insert(
                    &mut self.shapes,
                    key,
                    Property::Data {
                        value,
                        writable: false,
                        enumerable: false,
                        configurable: true,
                    },
                );
            }
        }
        stored.insert(
            &mut self.shapes,
            reified,
            Property::Data {
                value: Value::TRUE,
                writable: false,
                enumerable: false,
                configurable: false,
            },
        );
        let bytes = stored.charge_bytes(&self.shapes, &self.atoms);
        self.charge_slot(index, bytes)
            .map_err(EvalFailure::Runtime)?;
        let HeapEntry::Function { properties, .. } = &mut self.heap[index] else {
            unreachable!("function checked above");
        };
        for (key, property) in std::mem::take(properties).into_entries(&self.shapes) {
            stored.insert(&mut self.shapes, key, property);
        }
        *properties = stored;
        Ok(())
    }

    /// Whether a function is non-strict ECMAScript code.
    pub(crate) fn is_sloppy(&self, module: ModuleId, function: usize) -> bool {
        self.module_code(module).functions()[function]
            .flags()
            .is_sloppy
    }

    /// `OrdinaryCallBindThis` for the running function: a sloppy function sees
    /// the global object for a missing receiver and a wrapper for a primitive.
    /// Callers keep the result so a wrapper keeps its identity. Doing this at
    /// the first read cannot be observed, because `ToObject` runs no user code.
    pub(crate) fn bind_this(
        &mut self,
        module: ModuleId,
        function: usize,
        this_value: Value,
    ) -> Result<Value, EvalFailure> {
        if !self.is_sloppy(module, function) {
            return Ok(this_value);
        }
        if this_value == Value::UNDEFINED || this_value == Value::NULL {
            return Ok(self.context_global.unwrap_or(self.global_object));
        }
        self.value_to_object(this_value)
    }

    /// The value of a `delete` the running function performed. Strict code
    /// must not silently keep a property it asked to remove.
    pub(crate) fn deletion_result(
        &self,
        module: ModuleId,
        function: usize,
        deleted: bool,
    ) -> Result<bool, EvalFailure> {
        if deleted || self.is_sloppy(module, function) {
            return Ok(deleted);
        }
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "delete of an unconfigurable property",
        }))
    }

    pub(crate) fn store_global(
        &mut self,
        module: ModuleId,
        name: ConstantId,
        value: Value,
        sloppy: bool,
    ) -> Result<(), EvalFailure> {
        let cell = self
            .registry
            .modules
            .get(module.get() as usize)
            .and_then(|instance| instance.constant_cells.get(name.get() as usize))
            .copied()
            .flatten();
        if let Some(cell) = cell {
            if self.registry.modules[module.get() as usize].constant_is_import[name.get() as usize]
            {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "assign to immutable module binding",
                }));
            }
            self.registry.cells[cell.0].value = value;
        } else {
            let global = self.context_global.unwrap_or(self.global_object);
            let atom = self.global_name_atom(module, name);
            let key = PropertyKey::Named(atom);
            let stored = self.internal_set(global, key.clone(), value, global)?;
            // This instruction also carries global declarations, whose failure
            // always throws. Only an assignment can fail on an existing
            // property, and sloppy code ignores that; a missing property on a
            // non-extensible global is taken to be a declaration.
            if !stored && !(sloppy && self.has_own_property_key(global, &key)?) {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "assign to read only property",
                }));
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn test_set_global(&mut self, name: &str, value: Value) {
        let global = self.global_object;
        self.set_data_property(global, name, value)
            .expect("test global is writable");
    }

    #[cfg(test)]
    fn test_global(&self, name: &str) -> Option<Value> {
        let index = self.runtime_slot(self.global_object).ok()??;
        self.own_data_property(index, name)
    }

    /// Classifies a callee into the shared dispatch categories.
    fn callee_kind(&self, callee: Value) -> Result<CalleeKind, RuntimeErrorKind> {
        match self.runtime_slot(callee)? {
            Some(index) => match &self.heap[index] {
                HeapEntry::Function {
                    module,
                    function,
                    captures,
                    context,
                    ..
                } => Ok(CalleeKind::Runtime {
                    target: RuntimeFunction {
                        module: *module,
                        function: *function,
                    },
                    captures: captures.clone(),
                    context: *context,
                }),
                HeapEntry::NativeFunction { callable, .. } => match callable {
                    NativeCallable::Builtin(id) => Ok(CalleeKind::Builtin { id: *id }),
                    NativeCallable::Bound(_) => Ok(CalleeKind::Bound),
                },
                HeapEntry::Proxy { record } => {
                    if record.is_callable() {
                        Ok(CalleeKind::Proxy)
                    } else {
                        Ok(CalleeKind::NotCallable)
                    }
                }
                HeapEntry::ProxyRevoker { .. } => Ok(CalleeKind::ProxyRevoker),
                _ => Ok(CalleeKind::NotCallable),
            },
            None => Ok(CalleeKind::NotCallable),
        }
    }

    pub(crate) fn flatten_bound(
        &self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
        mut new_target: Value,
    ) -> Result<BoundCall, RuntimeErrorKind> {
        let mut target = callee;
        let mut receiver = this_value;
        let mut segments = Vec::new();
        let mut total = arguments.len();
        while let Some(index) = self.runtime_slot(target)? {
            let HeapEntry::NativeFunction {
                callable: NativeCallable::Bound(bound),
                ..
            } = &self.heap[index]
            else {
                break;
            };
            total = total.checked_add(bound.arguments.len()).ok_or(
                RuntimeErrorKind::ArgumentLimitExceeded {
                    limit: self.limits.max_argument_count,
                    requested: u32::MAX,
                },
            )?;
            if total > self.limits.max_argument_count as usize {
                return Err(RuntimeErrorKind::ArgumentLimitExceeded {
                    limit: self.limits.max_argument_count,
                    requested: u32::try_from(total).unwrap_or(u32::MAX),
                });
            }
            segments.push(bound.arguments.as_slice());
            receiver = bound.this_value;
            // BoundFunction [[Construct]]: each wrapper forwards newTarget to its
            // [[BoundTargetFunction]] only when newTarget is the wrapper itself.
            if new_target == target {
                new_target = bound.target;
            }
            target = bound.target;
        }
        let mut flattened = Vec::with_capacity(total);
        for segment in segments.iter().rev() {
            flattened.extend_from_slice(segment);
        }
        flattened.extend_from_slice(arguments);
        Ok(BoundCall {
            target,
            this_value: receiver,
            arguments: flattened,
            new_target,
        })
    }

    /// Materializes a constant into an ABI value, interning strings and bigints
    /// into the slot heap. Shared with the native engine.
    pub(crate) fn load_constant_value(
        &mut self,
        module: ModuleId,
        id: ConstantId,
    ) -> Result<Value, RuntimeErrorKind> {
        match &self.module_code(module).constants()[id.get() as usize] {
            Constant::String(text) => self.allocate(HeapEntry::String(text.clone())),
            Constant::BigInt(value) => self.allocate(HeapEntry::BigInt(value.as_str().to_owned())),
            constant => Ok(constant_value(constant).expect("non-heap constant")),
        }
    }

    /// Reads a call/construct arguments array from a register: it must hold a
    /// runtime array, whose length is capped by `max_argument_count`.
    fn read_arguments(&self, frame: usize, register: u32) -> Result<Vec<Value>, EvalFailure> {
        let value = self.read_register(frame, register);
        self.arguments_from_array(value)
    }

    /// Validates a call/construct arguments array value: it must be a runtime
    /// array whose length is capped by `max_argument_count`, with holes read as
    /// `undefined`. Shared with the native engine.
    fn arguments_from_array(&self, arguments: Value) -> Result<Vec<Value>, EvalFailure> {
        match self.runtime_slot(arguments).map_err(EvalFailure::Runtime)? {
            Some(index) => match &self.heap[index] {
                HeapEntry::Array { elements, .. } => {
                    if elements.len() as u64 > u64::from(self.limits.max_argument_count) {
                        return Err(EvalFailure::Runtime(
                            RuntimeErrorKind::ArgumentLimitExceeded {
                                limit: self.limits.max_argument_count,
                                requested: u32::try_from(elements.len()).unwrap_or(u32::MAX),
                            },
                        ));
                    }
                    Ok(elements
                        .iter()
                        .map(|value| {
                            if *value == Value::HOLE {
                                Value::UNDEFINED
                            } else {
                                *value
                            }
                        })
                        .collect())
                }
                _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "call arguments are not an array",
                })),
            },
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "call arguments are not an array",
            })),
        }
    }

    /// Reads a `CreateClosure` captures array: it must hold a runtime array whose
    /// length matches the target function's capture count.
    fn read_captures(
        &self,
        frame: usize,
        register: u32,
        function: FunctionId,
    ) -> Result<Vec<Value>, EvalFailure> {
        let value = self.read_register(frame, register);
        self.captures_from_array(self.active_module_id(), value, function)
    }

    /// Validates a `CreateClosure` captures array value: it must be a runtime
    /// array whose length matches the target function's capture count, with
    /// holes read as `undefined`. Shared with the native engine.
    pub(crate) fn captures_from_array(
        &self,
        module: ModuleId,
        captures: Value,
        function: FunctionId,
    ) -> Result<Vec<Value>, EvalFailure> {
        let expected =
            self.module_code(module).functions()[function.get() as usize].capture_count() as usize;
        match self.runtime_slot(captures).map_err(EvalFailure::Runtime)? {
            Some(index) => match &self.heap[index] {
                HeapEntry::Array { elements, .. } => {
                    if elements.len() != expected {
                        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "closure capture array arity",
                        }));
                    }
                    Ok(elements
                        .iter()
                        .map(|value| {
                            if *value == Value::HOLE {
                                Value::UNDEFINED
                            } else {
                                *value
                            }
                        })
                        .collect())
                }
                _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "closure captures are not an array",
                })),
            },
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "closure captures are not an array",
            })),
        }
    }

    /// A strict arguments object poisons `callee`; a sloppy one would name the
    /// function, which a frame does not hold.
    pub(crate) fn arguments_properties(&mut self, sloppy: bool) -> PropertyMap {
        let mut properties = PropertyMap::default();
        if !sloppy {
            let thrower = self.intrinsics.builtins.throw_type_error();
            let atom = self.intern_str("callee");
            properties.insert(
                &mut self.shapes,
                PropertyKey::Named(atom),
                Property::Accessor {
                    getter: Some(thrower),
                    setter: Some(thrower),
                    enumerable: false,
                    configurable: false,
                },
            );
        }
        properties
    }

    pub(crate) fn materialize_arguments(
        &mut self,
        frame: usize,
        function: usize,
        pc: usize,
    ) -> Result<Value, RuntimeError> {
        if let Some(existing) = self.frames[frame].arguments_object {
            return Ok(existing);
        }
        let args = self.frames[frame].args.clone();
        let properties =
            self.arguments_properties(self.is_sloppy(self.frames[frame].module, function));
        let value = self
            .allocate(HeapEntry::Array {
                kind: ArrayElementKind::for_elements(&args),
                elements: args,
                properties,
                prototype: Some(self.intrinsics.array_prototype),
                extensible: true,
                length_writable: true,
            })
            .map_err(|kind| self.error_at(kind, function, pc))?;
        self.frames[frame].arguments_object = Some(value);
        Ok(value)
    }

    fn push_frame(&mut self, request: ActivationRequest<'_>) -> Result<(), RuntimeError> {
        let target = request.target;
        let return_to = request.return_to;
        let function_index = target.function.get() as usize;
        let metadata = &self.module_code(target.module).functions()[function_index];
        let limit_error = |kind| match (self.frames.last(), return_to) {
            (Some(caller), Some(return_to)) => {
                self.error_at_in_module(kind, caller.module, caller.function, return_to.call_pc)
            }
            (_, None) => self.error_at_in_module(kind, target.module, function_index, 0),
            (None, Some(_)) => unreachable!("a returning frame has a caller"),
        };
        if self.call_depth_exhausted() {
            return Err(limit_error(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            }));
        }
        let next_registers = metadata.register_count() as usize;
        if self.live_registers.saturating_add(next_registers) > self.limits.max_total_registers {
            return Err(limit_error(RuntimeErrorKind::RegisterLimitExceeded {
                limit: self.limits.max_total_registers,
            }));
        }
        let mut frame = Frame::new(metadata, request);
        frame.outer_context = std::mem::replace(&mut self.context_global, request.context);
        self.live_registers += next_registers;
        self.frames.push(frame);
        Ok(())
    }

    pub(crate) fn consume_fuel(&mut self, amount: u64) -> Result<(), RuntimeErrorKind> {
        if self.cancel.is_cancelled() {
            return Err(RuntimeErrorKind::Cancelled);
        }
        if self.fuel < amount {
            self.fuel = 0;
            return Err(RuntimeErrorKind::FuelExhausted {
                limit: self.limits.fuel,
            });
        }
        self.fuel -= amount;
        Ok(())
    }

    /// Checks the cancellation token at a cooperative checkpoint. Returns
    /// [`RuntimeErrorKind::Cancelled`] when the token has been triggered.
    pub(crate) fn check_cancel(&self) -> Result<(), RuntimeErrorKind> {
        if self.cancel.is_cancelled() {
            Err(RuntimeErrorKind::Cancelled)
        } else {
            Ok(())
        }
    }

    /// Whether a call here passes the guest stack, so that it throws
    /// [`STACK_OVERFLOW`] in place of a new activation.
    pub(crate) fn stack_overflows(&self) -> bool {
        self.frames.len().saturating_add(self.native_depth) >= self.limits.max_stack_depth
            || self.native_stack_overflows()
    }

    /// Whether the native stack here passes [`Limits::max_stack_bytes`]. A builtin
    /// that calls a builtin adds no activation, so only this bounds that path.
    pub(crate) fn native_stack_overflows(&self) -> bool {
        self.native_stack_used() > self.limits.max_stack_bytes
    }

    /// Whether a new activation here ends the run: the host ceiling of
    /// [`Limits::max_call_depth`], or a native stack that is [`STACK_SLACK`] past
    /// the guest stack. Only a path that did not check [`Self::stack_overflows`]
    /// gets that far, and it ends with an error, not with a stack overflow.
    fn call_depth_exhausted(&self) -> bool {
        self.frames.len().saturating_add(self.native_depth) >= self.limits.max_call_depth
            || self.native_stack_exhausted()
    }

    fn native_stack_exhausted(&self) -> bool {
        self.native_stack_used() > self.limits.max_stack_bytes.saturating_add(STACK_SLACK)
    }

    fn native_stack_used(&self) -> usize {
        self.stack_base.saturating_sub(stack_position())
    }

    pub(crate) fn reserve_native_activation(
        &mut self,
        register_count: usize,
    ) -> Result<(), RuntimeErrorKind> {
        if self.call_depth_exhausted() {
            return Err(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            });
        }
        if self.live_registers.saturating_add(register_count) > self.limits.max_total_registers {
            return Err(RuntimeErrorKind::RegisterLimitExceeded {
                limit: self.limits.max_total_registers,
            });
        }
        self.native_depth += 1;
        self.live_registers += register_count;
        Ok(())
    }

    pub(crate) fn release_native_activation(&mut self, register_count: usize) {
        self.native_depth -= 1;
        self.live_registers -= register_count;
    }

    pub(crate) fn reserve_suspended_activation_registers(
        &mut self,
        register_count: usize,
    ) -> Result<(), RuntimeErrorKind> {
        if self.live_registers.saturating_add(register_count) > self.limits.max_total_registers {
            return Err(RuntimeErrorKind::RegisterLimitExceeded {
                limit: self.limits.max_total_registers,
            });
        }
        self.live_registers += register_count;
        Ok(())
    }

    pub(crate) fn release_suspended_activation_registers(&mut self, register_count: usize) {
        self.live_registers -= register_count;
    }

    pub(crate) fn enter_native_generator(&mut self) -> Result<(), RuntimeErrorKind> {
        if self.call_depth_exhausted() {
            return Err(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            });
        }
        self.native_depth += 1;
        Ok(())
    }

    pub(crate) fn leave_native_generator(&mut self) {
        self.native_depth -= 1;
    }

    /// Charges one `native_depth` slot for a proxy dispatch hop. Proxy-to-proxy
    /// forwarding never grows `frames.len()`, so without this charge a deep
    /// chain of transparent proxies would exhaust the process stack while the
    /// `frames.len() + native_depth` ceiling still had room.
    pub(crate) fn enter_proxy_dispatch(&mut self) -> Result<(), EvalFailure> {
        if self.stack_overflows() {
            return Err(EvalFailure::Throw(STACK_OVERFLOW));
        }
        if self.call_depth_exhausted() {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            }));
        }
        self.native_depth += 1;
        Ok(())
    }

    pub(crate) fn leave_proxy_dispatch(&mut self) {
        self.native_depth -= 1;
    }

    /// Runs `f` with one proxy-dispatch slot charged, releasing it on both the
    /// `Ok` and `Err` paths. Every proxy entry is `Result`-based, so no
    /// unwinding is relied upon and depth accounting stays balanced.
    pub(crate) fn with_proxy_dispatch<T>(
        &mut self,
        f: impl FnOnce(&mut Machine<'a, H>) -> Result<T, EvalFailure>,
    ) -> Result<T, EvalFailure> {
        self.enter_proxy_dispatch()?;
        let result = self.with_temporaries(f);
        self.leave_proxy_dispatch();
        result
    }

    /// Runs native code that holds values in Rust locals across user code,
    /// keeping what it allocates and what user code returns to it rooted.
    pub(crate) fn with_temporaries<T>(&mut self, body: impl FnOnce(&mut Machine<'a, H>) -> T) -> T {
        if self.in_builtin {
            return body(self);
        }
        self.in_builtin = true;
        let mark = self.builtin_temporaries.len();
        let floor = std::mem::replace(&mut self.results_floor, self.callback_results.len());
        let result = body(self);
        self.callback_results.truncate(self.results_floor);
        self.results_floor = floor;
        self.builtin_temporaries.truncate(mark);
        self.in_builtin = false;
        result
    }

    /// Roots values for native code outside a builtin; `release_temporaries`
    /// with the returned mark ends that.
    pub(crate) fn hold_temporaries(&mut self, values: &[Value]) -> usize {
        let mark = self.builtin_temporaries.len();
        self.builtin_temporaries.extend_from_slice(values);
        mark
    }

    pub(crate) fn release_temporaries(&mut self, mark: usize) {
        self.builtin_temporaries.truncate(mark);
    }

    /// Roots a call that a builtin forwarded. `apply` and `Reflect.apply` read
    /// their list into a Rust vector, and with the end of the builtin nothing
    /// else keeps those values. The next builtin can run user code, and it
    /// expects its caller to root what it is given.
    pub(crate) fn hold_forwarded_call(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) {
        self.builtin_temporaries.extend([callee, this_value]);
        self.builtin_temporaries.extend_from_slice(arguments);
    }

    /// Keeps a value a builtin just received until that builtin returns.
    pub(crate) fn keep_temporary(&mut self, value: Value) {
        if self.in_builtin && matches!(value.decode(), Some(Decoded::HeapRef(_))) {
            self.builtin_temporaries.push(value);
        }
    }

    fn keep_callback_result(&mut self, value: Value) {
        if !self.in_builtin || !matches!(value.decode(), Some(Decoded::HeapRef(_))) {
            return;
        }
        if self.callback_results.len() - self.results_floor == RECENT_CALLBACK_RESULTS {
            self.callback_results.remove(self.results_floor);
        }
        self.callback_results.push(value);
    }

    /// Runs user code for a builtin, which holds the result in a Rust local.
    fn call_user_code(
        &mut self,
        call: impl FnOnce(&mut Machine<'a, H>) -> Result<Value, EvalFailure>,
        keep: fn(&mut Self, Value),
    ) -> Result<Value, EvalFailure> {
        let in_builtin = std::mem::replace(&mut self.in_builtin, false);
        let result = call(self);
        self.in_builtin = in_builtin;
        match &result {
            Ok(value)
            | Err(EvalFailure::ThrowValue(value) | EvalFailure::ThrowValueOrigin { value, .. }) => {
                keep(self, *value);
            }
            Err(_) => {}
        }
        result
    }

    /// `call_value` for a loop over a user callback that is done with each result
    /// before the next call: `forEach`, `map`, `reduce` and their like. Only
    /// such a loop may use this; anything collecting results needs `call_value`.
    pub(crate) fn call_callback(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        self.call_user_code(
            |machine| machine.dispatch_call(callee, this_value, arguments),
            Self::keep_callback_result,
        )
    }

    /// Answers whether `value` has `[[Construct]]`. Builtin callees consult the
    /// realm's registration metadata (`BuiltinTable::is_constructable`), bound
    /// callees recurse into their target, runtime closures consult the
    /// compiler-emitted `FunctionFlags::is_constructable` bit, and proxies
    /// answer from the snapshot `ProxyCreate` took of their target.
    /// Whether `value` is a non-strict `function`, the one kind of function that
    /// the specification lets an implementation give `caller` and `arguments`.
    pub(crate) fn is_sloppy_ordinary_function(&self, value: Value) -> Result<bool, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        let HeapEntry::Function {
            module, function, ..
        } = &self.heap[index]
        else {
            return Ok(false);
        };
        let flags = self.module_code(*module).functions()[function.get() as usize].flags();
        Ok(flags.is_sloppy && flags.is_constructable && !flags.is_async && !flags.is_generator)
    }

    pub(crate) fn is_constructor(&self, value: Value) -> Result<bool, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        match &self.heap[index] {
            HeapEntry::Function {
                module, function, ..
            } => {
                let flags = self.module_code(*module).functions()[function.get() as usize].flags();
                Ok(flags.is_constructable)
            }
            HeapEntry::NativeFunction { callable, .. } => match callable {
                NativeCallable::Builtin(id) => Ok(self.intrinsics.builtins.is_constructable(*id)),
                NativeCallable::Bound(bound) => self.is_constructor(bound.target),
            },
            HeapEntry::Proxy { record } => Ok(record.is_constructor()),
            _ => Ok(false),
        }
    }

    /// Whether `value` is a `HeapEntry::Proxy` (the dispatch head; revokers are
    /// ordinary callable objects, not proxies).
    pub(crate) fn heap_entry_is_proxy_value(&self, value: Value) -> bool {
        matches!(
            self.runtime_slot(value),
            Ok(Some(index)) if matches!(self.heap[index], HeapEntry::Proxy { .. })
        )
    }

    fn execute_call(&mut self, request: CallRequest<'_>) -> Result<(), RuntimeError> {
        let mark = self.builtin_temporaries.len();
        let result = self.execute_call_forwarding(request);
        self.release_temporaries(mark);
        result
    }

    /// [`Machine::execute_call`], which releases what this holds for a forward.
    fn execute_call_forwarding(&mut self, request: CallRequest<'_>) -> Result<(), RuntimeError> {
        let CallRequest {
            callee,
            this_value,
            arguments,
            destination,
            call_pc,
            constructed,
            new_target,
        } = request;
        let mut callee = callee;
        let mut this_value = this_value;
        let mut arguments = Cow::Borrowed(arguments);
        loop {
            match self.callee_kind(callee) {
                Ok(CalleeKind::Runtime {
                    target,
                    captures,
                    context,
                }) => {
                    if self.stack_overflows() {
                        return self.resolve_failure(EvalFailure::Throw(STACK_OVERFLOW), call_pc);
                    }
                    let flags = self.module_code(target.module).functions()
                        [target.function.get() as usize]
                        .flags();
                    if flags.is_generator {
                        let start = GeneratorStart {
                            target,
                            captures,
                            context,
                            this_value,
                            new_target,
                            args: arguments.as_ref().to_vec(),
                        };
                        return match self.start_generator(start, flags) {
                            Ok(generator) => {
                                if let Some(register) = destination {
                                    self.write_register(self.frames.len() - 1, register, generator);
                                }
                                Ok(())
                            }
                            Err(failure) => self.resolve_failure(failure, call_pc),
                        };
                    }
                    if flags.is_async && !flags.is_generator {
                        return match crate::vm::generator_async::start_async_function(
                            self,
                            target,
                            &captures,
                            context,
                            this_value,
                            new_target,
                            arguments.as_ref(),
                        ) {
                            Ok(promise) => {
                                if let Some(register) = destination {
                                    self.write_register(self.frames.len() - 1, register, promise);
                                }
                                Ok(())
                            }
                            Err(failure) => self.resolve_failure(failure, call_pc),
                        };
                    }
                    return self.push_frame(ActivationRequest {
                        target,
                        captures: &captures,
                        context,
                        this_value,
                        new_target,
                        arguments: arguments.as_ref(),
                        return_to: Some(ReturnTo {
                            destination: destination.map(|register| register as usize),
                            call_pc,
                            constructed,
                        }),
                    });
                }
                Ok(CalleeKind::Builtin { id }) => {
                    match self.call_builtin(id, this_value, arguments.as_ref(), false) {
                        Ok(intrinsics::BuiltinOutcome::Value(value)) => {
                            if let Some(register) = destination {
                                self.write_register(self.frames.len() - 1, register, value);
                            }
                            return Ok(());
                        }
                        Ok(intrinsics::BuiltinOutcome::Call {
                            callee: next,
                            this_value: next_this,
                            arguments: next_arguments,
                        }) => {
                            self.hold_forwarded_call(next, next_this, &next_arguments);
                            callee = next;
                            this_value = next_this;
                            arguments = Cow::Owned(next_arguments);
                        }
                        Ok(intrinsics::BuiltinOutcome::GeneratorResume {
                            generator,
                            completion,
                        }) => match self.resume_generator(generator, completion) {
                            Ok(value) => {
                                if let Some(register) = destination {
                                    self.write_register(self.frames.len() - 1, register, value);
                                }
                                return Ok(());
                            }
                            Err(failure) => return self.resolve_failure(failure, call_pc),
                        },
                        Ok(intrinsics::BuiltinOutcome::AsyncGeneratorResume {
                            generator,
                            completion,
                        }) => match self.enqueue_async_generator_request(generator, completion) {
                            Ok(value) => {
                                if let Some(register) = destination {
                                    self.write_register(self.frames.len() - 1, register, value);
                                }
                                return Ok(());
                            }
                            Err(failure) => return self.resolve_failure(failure, call_pc),
                        },
                        Err(failure) => return self.resolve_failure(failure, call_pc),
                    }
                }
                Ok(CalleeKind::Bound) => {
                    let bound = self
                        .flatten_bound(callee, this_value, arguments.as_ref(), Value::UNDEFINED)
                        .map_err(|kind| self.error_here_at(kind, call_pc))?;
                    callee = bound.target;
                    if constructed.is_none() {
                        this_value = bound.this_value;
                    }
                    arguments = Cow::Owned(bound.arguments);
                }
                Ok(CalleeKind::Proxy) => {
                    let arguments = arguments.as_ref().to_vec();
                    match self.with_proxy_dispatch(|machine| {
                        crate::builtins::proxy::call(machine, callee, this_value, &arguments)
                    }) {
                        Ok(value) => {
                            if let Some(register) = destination {
                                self.write_register(self.frames.len() - 1, register, value);
                            }
                            return Ok(());
                        }
                        Err(failure) => return self.resolve_failure(failure, call_pc),
                    }
                }
                Ok(CalleeKind::ProxyRevoker) => {
                    match crate::builtins::proxy::call_revoker(self, callee) {
                        Ok(value) => {
                            if let Some(register) = destination {
                                self.write_register(self.frames.len() - 1, register, value);
                            }
                            return Ok(());
                        }
                        Err(failure) => return self.resolve_failure(failure, call_pc),
                    }
                }
                Ok(CalleeKind::NotCallable) => return self.throw_type("call", call_pc),
                Err(kind) => return Err(self.error_here_at(kind, call_pc)),
            }
        }
    }

    fn execute_construct(
        &mut self,
        callee: Value,
        new_target: Value,
        arguments: &[Value],
        destination: u32,
        call_pc: usize,
    ) -> Result<(), RuntimeError> {
        let mut callee = callee;
        let mut new_target = new_target;
        let mut arguments = Cow::Borrowed(arguments);
        if matches!(self.callee_kind(callee), Ok(CalleeKind::Bound)) {
            let bound = self
                .flatten_bound(callee, Value::UNDEFINED, arguments.as_ref(), new_target)
                .map_err(|kind| self.error_here_at(kind, call_pc))?;
            new_target = bound.new_target;
            callee = bound.target;
            arguments = Cow::Owned(bound.arguments);
        }
        if matches!(
            self.callee_kind(callee),
            Ok(CalleeKind::Proxy | CalleeKind::ProxyRevoker)
        ) {
            return match self.internal_construct(callee, arguments.as_ref(), new_target) {
                Ok(value) => {
                    self.write_register(self.frames.len() - 1, destination, value);
                    Ok(())
                }
                Err(failure) => self.resolve_failure(failure, call_pc),
            };
        }
        match self.is_constructor(callee) {
            Ok(true) => {}
            Ok(false) => return self.throw_type("construct", call_pc),
            Err(failure) => return self.resolve_failure(failure, call_pc),
        }
        let index = match self.runtime_slot(callee) {
            Ok(Some(index)) => index,
            Ok(None) => return self.throw_type("construct", call_pc),
            Err(kind) => return Err(self.error_here_at(kind, call_pc)),
        };
        let builtin = match &self.heap[index] {
            HeapEntry::NativeFunction {
                callable: NativeCallable::Builtin(id),
                ..
            } => Some(*id),
            _ => None,
        };
        if let Some(id) = builtin {
            return match self.call_builtin_with_new_target(
                id,
                Value::UNDEFINED,
                arguments.as_ref(),
                true,
                new_target,
            ) {
                Ok(intrinsics::BuiltinOutcome::Value(value)) => {
                    self.write_register(self.frames.len() - 1, destination, value);
                    Ok(())
                }
                Ok(
                    intrinsics::BuiltinOutcome::Call { .. }
                    | intrinsics::BuiltinOutcome::GeneratorResume { .. }
                    | intrinsics::BuiltinOutcome::AsyncGeneratorResume { .. },
                ) => self.throw_type("construct", call_pc),
                Err(failure) => self.resolve_failure(failure, call_pc),
            };
        }
        if !matches!(
            self.heap[index],
            HeapEntry::Function { .. } | HeapEntry::NativeFunction { .. }
        ) {
            return self.throw_type("construct", call_pc);
        }
        if let HeapEntry::Function {
            module, function, ..
        } = self.heap[index]
            && !self.module_code(module).functions()[function.get() as usize]
                .flags()
                .is_constructable
        {
            return self.throw_type("construct", call_pc);
        }
        let object = match self.allocate_constructed_receiver(new_target) {
            Ok(object) => object,
            Err(failure) => return self.resolve_failure(failure, call_pc),
        };
        self.execute_call(CallRequest {
            callee,
            this_value: object,
            arguments: arguments.as_ref(),
            destination: Some(destination),
            call_pc,
            constructed: Some(object),
            new_target,
        })
    }

    pub(crate) fn constructed_prototype(&mut self, callee: Value) -> Result<Value, EvalFailure> {
        let index = self
            .runtime_slot(callee)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: callee,
            }))?;
        let key = PropertyKey::Named(self.intern_str("prototype"));
        let base = self.value_for_runtime_index(index)?;
        let prototype = self.internal_get(base, &key, callee)?;
        Ok(if self.is_object(prototype) {
            prototype
        } else {
            self.intrinsics.object_prototype
        })
    }

    fn allocate_constructed_receiver(&mut self, callee: Value) -> Result<Value, EvalFailure> {
        let prototype = self.constructed_prototype(callee)?;
        self.allocate_constructed_receiver_with(prototype)
            .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn allocate_constructed_receiver_with(
        &mut self,
        prototype: Value,
    ) -> Result<Value, RuntimeErrorKind> {
        self.allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            boxed_primitive: None,
            extensible: true,
        })
    }

    pub(crate) fn store_element(&mut self, array_slot: usize, index: usize, value: Value) {
        let HeapEntry::Array { elements, kind, .. } = &mut self.heap[array_slot] else {
            unreachable!("element store requires an array slot");
        };
        let next_kind = kind.including(value);
        debug_assert!(next_kind.admits(value));
        if index == elements.len() {
            elements.push(value);
        } else {
            elements[index] = value;
        }
        *kind = next_kind;
        if elements.len() <= 64 {
            debug_assert!(next_kind.matches(elements));
        }
    }

    pub(crate) fn replace_element_vector(&mut self, array_slot: usize, elements: Vec<Value>) {
        install_element_vector(&mut self.heap, array_slot, elements);
    }

    pub(crate) fn array_elements(&self, value: Value) -> Result<Option<Vec<Value>>, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(None);
        };
        match &self.heap[index] {
            HeapEntry::Array { elements, .. } => Ok(Some(elements.clone())),
            _ => Ok(None),
        }
    }

    /// Returns the array length without cloning the element vector.
    pub(crate) fn array_len(&self, value: Value) -> Result<Option<usize>, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(None);
        };
        match &self.heap[index] {
            HeapEntry::Array { elements, .. } => Ok(Some(elements.len())),
            _ => Ok(None),
        }
    }

    /// The element at `index` when `array` holds only numbers and `index` is an
    /// in-bounds Int32; `None` otherwise, so the caller falls back to the
    /// generic read.
    pub(crate) fn array_element_number(&self, array: Value, index: Value) -> Option<Value> {
        let slot = self.runtime_slot(array).ok().flatten()?;
        let position = usize::try_from(index.as_int32()?).ok()?;
        match &self.heap[slot] {
            HeapEntry::Array { kind, elements, .. } if *kind != ArrayElementKind::Any => {
                elements.get(position).copied()
            }
            _ => None,
        }
    }

    #[cfg(test)]
    fn array_element_kind(&self, value: Value) -> Option<ArrayElementKind> {
        let index = self.runtime_slot(value).ok().flatten()?;
        match &self.heap[index] {
            HeapEntry::Array { kind, .. } => Some(*kind),
            _ => None,
        }
    }

    pub(crate) fn array_length(&self, value: Value) -> Result<usize, EvalFailure> {
        self.array_len(value)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "array method called on incompatible receiver",
            }))
    }

    pub(crate) fn replace_array_elements(
        &mut self,
        value: Value,
        elements: Vec<Value>,
    ) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "array method called on incompatible receiver",
            }));
        };
        let old_length = match &self.heap[index] {
            HeapEntry::Array { elements, .. } => elements.len(),
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "array method called on incompatible receiver",
                }));
            }
        };
        let element_bytes = std::mem::size_of::<Value>();
        let growth = elements
            .len()
            .saturating_sub(old_length)
            .saturating_mul(element_bytes);
        self.charge_slot(index, growth)
            .map_err(EvalFailure::Runtime)?;
        let released = old_length
            .saturating_sub(elements.len())
            .saturating_mul(element_bytes);
        self.replace_element_vector(index, elements);
        self.refund_slot(index, released);
        Ok(())
    }

    /// The UTF-16 units of a string or rope entry. A rope is walked with an
    /// explicit stack and the entry is replaced by its flat text, so later
    /// reads copy nothing.
    pub(crate) fn flat_string(&mut self, slot: usize) -> EcmaString {
        if let HeapEntry::String(text) = &self.heap[slot] {
            return text.clone();
        }
        let HeapEntry::Rope { left, right, len } = &self.heap[slot] else {
            unreachable!("flat_string reads a string or rope entry");
        };
        let (left, right, len) = (*left, *right, *len as usize);
        let mut units = Vec::with_capacity(len);
        let mut stack = vec![right, left];
        while let Some(value) = stack.pop() {
            let child = self
                .runtime_slot(value)
                .ok()
                .flatten()
                .expect("rope halves are runtime string entries");
            match &self.heap[child] {
                HeapEntry::String(text) => units.extend_from_slice(text.as_units()),
                HeapEntry::Rope { left, right, .. } => {
                    stack.push(*right);
                    stack.push(*left);
                }
                _ => unreachable!("rope halves are string entries"),
            }
        }
        debug_assert_eq!(units.len(), len);
        let text = EcmaString::from_units(&units);
        self.heap[slot] = HeapEntry::String(text.clone());
        self.charge_flattened_rope(slot, len);
        text
    }

    /// Moves a flattened rope's charge from its node cost to its flat text. The
    /// creation check already required room for this text; the heap may have
    /// grown since, in which case the next allocation reports the limit.
    fn charge_flattened_rope(&mut self, slot: usize, len: usize) {
        self.sync_slot_ledger();
        let extra = len.saturating_mul(2).saturating_sub(ROPE_NODE_BYTES);
        self.slot_bytes[slot] += extra;
        self.heap_bytes += extra;
        self.request_garbage_collection();
    }

    /// The UTF-16 length of a string or rope entry, without flattening it.
    pub(crate) fn string_len(&self, slot: usize) -> usize {
        match &self.heap[slot] {
            HeapEntry::String(text) => text.len_units(),
            HeapEntry::Rope { len, .. } => *len as usize,
            _ => unreachable!("string_len reads a string or rope entry"),
        }
    }

    /// Whether the entry at `slot` is still an unflattened rope.
    #[cfg(test)]
    fn is_rope(&self, slot: usize) -> bool {
        matches!(self.heap[slot], HeapEntry::Rope { .. })
    }

    /// The heap slot of a value holding a string or a rope.
    fn string_slot(&self, value: Value) -> Option<usize> {
        let index = self.runtime_slot(value).ok().flatten()?;
        matches!(
            &self.heap[index],
            HeapEntry::String(_) | HeapEntry::Rope { .. }
        )
        .then_some(index)
    }

    pub(crate) fn string_value(&mut self, value: Value) -> Option<EcmaString> {
        let index = self.string_slot(value)?;
        Some(self.flat_string(index))
    }

    pub(crate) fn get_named_property(
        &mut self,
        object: Value,
        name: &str,
    ) -> Result<Value, EvalFailure> {
        self.get_property_ascii(object, name)
    }

    fn get_property_ascii(&mut self, object: Value, name: &str) -> Result<Value, EvalFailure> {
        debug_assert!(name.is_ascii());
        if let Some(atom) = self.atoms.find(name) {
            return self.internal_get(object, &PropertyKey::Named(atom), object);
        }
        self.get_property_never_interned(object, name)
    }
    /// Reads a name that was never interned. No ordinary map can hold it,
    /// so only exotic reads observe it and anything else is absent.
    /// Exotic nodes fall back to the interning path, which stays correct.
    fn get_property_never_interned(
        &mut self,
        object: Value,
        name: &str,
    ) -> Result<Value, EvalFailure> {
        let slot = self.runtime_slot(object).map_err(EvalFailure::Runtime)?;
        let start = match slot {
            Some(index) => Some(index),
            None => match object.decode() {
                Some(Decoded::Boolean(_)) => self
                    .runtime_slot(self.intrinsics.boolean_prototype)
                    .map_err(EvalFailure::Runtime)?,
                Some(Decoded::Number(_) | Decoded::Int32(_)) => self
                    .runtime_slot(self.intrinsics.number_prototype)
                    .map_err(EvalFailure::Runtime)?,
                _ => return Ok(Value::UNDEFINED),
            },
        };
        let Some(mut node) = start else {
            return Ok(Value::UNDEFINED);
        };
        for _ in 0..=self.heap.len() {
            if matches!(self.heap[node], HeapEntry::Proxy { .. })
                || Self::observes_fresh_name(&self.heap[node])
            {
                let atom = self.intern_str(name);
                return self.internal_get(object, &PropertyKey::Named(atom), object);
            }
            match self.prototype_index(node)? {
                Some(next) => node = next,
                None => return Ok(Value::UNDEFINED),
            }
        }
        Ok(Value::UNDEFINED)
    }
    /// Reports whether `entry` can observe a property name that was never
    /// interned: exotic string, element, function, namespace, boxed, and
    /// environment reads key on the name text rather than the atom.
    fn observes_fresh_name(entry: &HeapEntry) -> bool {
        match entry {
            HeapEntry::Object {
                boxed_primitive: Some(_),
                ..
            }
            | HeapEntry::String(_)
            | HeapEntry::Rope { .. }
            | HeapEntry::Array { .. }
            | HeapEntry::TypedArray { .. }
            | HeapEntry::Function { .. }
            | HeapEntry::ModuleNamespace { .. }
            | HeapEntry::ExternalModuleNamespace { .. }
            | HeapEntry::HashState { .. }
            | HeapEntry::ProcessEnv { .. } => true,
            HeapEntry::Vacant
            | HeapEntry::BigInt(_)
            | HeapEntry::Object {
                boxed_primitive: None,
                ..
            }
            | HeapEntry::Script { .. }
            | HeapEntry::Symbol { .. }
            | HeapEntry::PrivateName { .. }
            | HeapEntry::RegExp { .. }
            | HeapEntry::Date { .. }
            | HeapEntry::Temporal { .. }
            | HeapEntry::Intl { .. }
            | HeapEntry::Collection { .. }
            | HeapEntry::DataView { .. }
            | HeapEntry::ArrayBuffer { .. }
            | HeapEntry::SharedArrayBuffer { .. }
            | HeapEntry::WeakRef { .. }
            | HeapEntry::FinalizationRegistry { .. }
            | HeapEntry::BuiltinIterator { .. }
            | HeapEntry::Iterator { .. }
            | HeapEntry::Generator { .. }
            | HeapEntry::AsyncGenerator { .. }
            | HeapEntry::AsyncFromSync { .. }
            | HeapEntry::DisposableStack { .. }
            | HeapEntry::Promise { .. }
            | HeapEntry::Timeout { .. }
            | HeapEntry::PromiseResolver { .. }
            | HeapEntry::PromiseAll { .. }
            | HeapEntry::PromiseAllElement { .. }
            | HeapEntry::AsyncActivation { .. }
            | HeapEntry::NativeFunction { .. }
            | HeapEntry::Proxy { .. }
            | HeapEntry::ProxyRevoker { .. } => false,
        }
    }

    pub(crate) fn get_property_key(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<Value, EvalFailure> {
        self.internal_get(object, key, object)
    }

    pub(crate) fn set_data_property_key(
        &mut self,
        object: Value,
        key: PropertyKey,
        value: Value,
    ) -> Result<(), EvalFailure> {
        if !self.internal_set(object, key, value, object)? {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "assign to read only property",
            }));
        }
        Ok(())
    }

    pub(crate) fn set_data_property(
        &mut self,
        object: Value,
        name: &str,
        value: Value,
    ) -> Result<(), EvalFailure> {
        let key = PropertyKey::Named(self.intern_str(name));
        self.set_data_property_key(object, key, value)
    }

    /// `CreateDataProperty` — defines an own data property directly, bypassing
    /// the prototype chain and any inherited setters. Used by JSON.parse and
    /// JSON.stringify where the spec mandates `[[DefineOwnProperty]]` semantics
    /// rather than `[[Set]]`.
    pub(crate) fn create_data_property_key(
        &mut self,
        object: Value,
        key: PropertyKey,
        value: Value,
    ) -> Result<(), EvalFailure> {
        self.define_descriptor(
            object,
            key,
            Property::Data {
                value,
                writable: true,
                enumerable: true,
                configurable: true,
            },
        )
    }

    pub(crate) fn is_callable(&self, value: Value) -> Result<bool, EvalFailure> {
        Ok(!matches!(
            self.callee_kind(value).map_err(EvalFailure::Runtime)?,
            CalleeKind::NotCallable
        ))
    }

    pub(crate) fn box_primitive(&mut self, value: Value) -> Result<Value, EvalFailure> {
        let prototype = match value.decode() {
            Some(Decoded::Boolean(_)) => self.intrinsics.boolean_prototype,
            Some(Decoded::Number(_) | Decoded::Int32(_)) => self.intrinsics.number_prototype,
            Some(Decoded::HeapRef(_)) => match self
                .runtime_slot(value)
                .map_err(EvalFailure::Runtime)?
                .map(|index| &self.heap[index])
            {
                Some(HeapEntry::String(_) | HeapEntry::Rope { .. }) => {
                    self.intrinsics.string_prototype
                }
                Some(HeapEntry::BigInt(_)) => self.intrinsics.builtins.bigint_prototype(),
                Some(HeapEntry::Symbol { .. }) => self.intrinsics.builtins.symbol_prototype(),
                _ => self.intrinsics.object_prototype,
            },
            _ => self.intrinsics.object_prototype,
        };
        self.allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(prototype),
            boxed_primitive: Some(value),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn value_to_object(&mut self, value: Value) -> Result<Value, EvalFailure> {
        if matches!(
            value.decode(),
            Some(Decoded::Undefined | Decoded::Null | Decoded::Hole | Decoded::Uninitialized)
                | None
        ) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "convert nullish value to object",
            }));
        }
        let heap_primitive = self
            .runtime_slot(value)
            .map_err(EvalFailure::Runtime)?
            .is_some_and(|index| {
                matches!(
                    self.heap[index],
                    HeapEntry::String(_)
                        | HeapEntry::Rope { .. }
                        | HeapEntry::BigInt(_)
                        | HeapEntry::Symbol { .. }
                        | HeapEntry::PrivateName { .. }
                )
            });
        if heap_primitive {
            return self.box_primitive(value);
        }
        if self.is_object(value) {
            return Ok(value);
        }
        self.box_primitive(value)
    }

    /// The string inside a String exotic object.
    fn boxed_string(&mut self, index: usize) -> Option<EcmaString> {
        let primitive = match &self.heap[index] {
            HeapEntry::Object {
                boxed_primitive: Some(primitive),
                ..
            } => *primitive,
            _ => return None,
        };
        self.string_value(primitive)
    }

    /// `StringGetOwnProperty`, plus the `length` every String exotic object owns.
    pub(crate) fn string_exotic_property(
        &mut self,
        index: usize,
        key: &PropertyKey,
    ) -> Result<Option<Property>, EvalFailure> {
        let found = self
            .boxed_string(index)
            .and_then(|text| string_own_get(&text, &self.atoms, key));
        let (value, enumerable) = match found {
            Some(Found::Value(length)) => (length, false),
            Some(Found::Text(unit)) => {
                let unit = self
                    .allocate(HeapEntry::String(unit))
                    .map_err(EvalFailure::Runtime)?;
                (unit, true)
            }
            _ => return Ok(None),
        };
        Ok(Some(Property::Data {
            value,
            writable: false,
            enumerable,
            configurable: false,
        }))
    }

    pub(crate) fn unbox_primitive_or_self(&self, value: Value) -> Result<Value, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(value);
        };
        match self.heap[index] {
            HeapEntry::Object {
                boxed_primitive: Some(primitive),
                ..
            } => Ok(primitive),
            _ => Ok(value),
        }
    }

    pub(crate) fn unbox_primitive(
        &self,
        value: Value,
        operation: &'static str,
    ) -> Result<Value, EvalFailure> {
        let unboxed = self.unbox_primitive_or_self(value)?;
        if unboxed == value && self.is_object(value) {
            Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
        } else {
            Ok(unboxed)
        }
    }

    pub(crate) fn current_builtin_id(&self) -> Option<intrinsics::BuiltinId> {
        self.current_builtin_id
    }

    /// The `new.target` value scoped to the currently executing builtin
    /// constructor, or `Value::UNDEFINED` outside builtin construction.
    pub(crate) fn current_new_target(&self) -> Value {
        self.current_new_target
    }

    /// Clears the WeakRef same-job strong roots at an outer ECMAScript job
    /// boundary, refunding their machine-retained byte charge exactly once.
    pub(crate) fn clear_kept_alive_for_job(&mut self) {
        self.refund_machine(
            self.kept_alive
                .len()
                .saturating_mul(std::mem::size_of::<Value>()),
        );
        self.kept_alive.clear();
    }

    /// A thrown error of the intrinsic constructor `id` with `message`, with
    /// the own properties the constructor itself gives a new error.
    pub(crate) fn throw_error(
        &mut self,
        id: intrinsics::BuiltinId,
        message: EcmaString,
    ) -> EvalFailure {
        let object = match self.allocate(HeapEntry::Object {
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.error_prototype(id)),
            boxed_primitive: None,
            extensible: true,
        }) {
            Ok(value) => value,
            Err(kind) => return EvalFailure::Runtime(kind),
        };
        let name = self.intrinsics.builtins.get(id).name;
        match builtins::initialize_error(self, object, name, Some(&message)) {
            Ok(()) => EvalFailure::ThrowValue(object),
            Err(failure) => failure,
        }
    }

    /// A thrown error object built from the realm's own `constructor`
    /// intrinsic, whatever guest code has since stored in the global binding
    /// of that name.
    pub(crate) fn intrinsic_error(
        &mut self,
        constructor: &str,
        message: EcmaString,
    ) -> EvalFailure {
        let id = self
            .intrinsics
            .builtins
            .id_named(constructor)
            .expect("error constructor is installed");
        self.throw_error(id, message)
    }

    /// The failure of [`Instruction::ThrowIntrinsicError`]: the realm's
    /// intrinsic `kind` error with the module's string constant `message`.
    pub(crate) fn throw_intrinsic_error(
        &mut self,
        module: ModuleId,
        kind: IntrinsicErrorKind,
        message: ConstantId,
    ) -> EvalFailure {
        let message = self.constant_text(module, message).clone();
        self.intrinsic_error(kind.constructor_name(), message)
    }

    pub(crate) fn has_own_property_key(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<bool, EvalFailure> {
        let Some(index) = self.runtime_slot(object).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        Ok(self.own_get(index, key).is_some())
    }

    pub(crate) fn internal_construct(
        &mut self,
        callee: Value,
        arguments: &[Value],
        new_target: Value,
    ) -> Result<Value, EvalFailure> {
        self.call_user_code(
            |machine| machine.dispatch_construct(callee, arguments, new_target),
            Self::keep_temporary,
        )
    }

    fn dispatch_construct(
        &mut self,
        callee: Value,
        arguments: &[Value],
        new_target: Value,
    ) -> Result<Value, EvalFailure> {
        match self.callee_kind(callee).map_err(EvalFailure::Runtime)? {
            CalleeKind::Builtin { id } => {
                match self.call_builtin_with_new_target(
                    id,
                    Value::UNDEFINED,
                    arguments,
                    true,
                    new_target,
                )? {
                    intrinsics::BuiltinOutcome::Value(value) => Ok(value),
                    _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "construct",
                    })),
                }
            }
            CalleeKind::Runtime {
                target,
                captures,
                context,
            } => {
                let flags = self.module_code(target.module).functions()
                    [target.function.get() as usize]
                    .flags();
                if !flags.is_constructable {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "construct",
                    }));
                }
                if self.stack_overflows() {
                    return Err(EvalFailure::Throw(STACK_OVERFLOW));
                }
                let object = self.allocate_constructed_receiver(new_target)?;
                let stop_depth = self.frames.len();
                // Native code calling back has no interpreter frame here, and
                // the construction still has to answer with `object`.
                let return_to = Some(ReturnTo {
                    destination: None,
                    call_pc: self.frames.last().map_or(0, |frame| frame.pc),
                    constructed: Some(object),
                });
                self.push_frame(ActivationRequest {
                    target,
                    captures: &captures,
                    context,
                    this_value: object,
                    new_target,
                    arguments,
                    return_to,
                })
                .map_err(|error| EvalFailure::Runtime(error.kind))?;
                self.callback_boundaries.push(stop_depth);
                let result = self.run_loop(stop_depth);
                self.callback_boundaries
                    .pop()
                    .expect("nested constructor callback owns its unwind boundary");
                match result {
                    Ok(None) => self.last_completion.take().ok_or(EvalFailure::Runtime(
                        RuntimeErrorKind::InvalidValue { value: object },
                    )),
                    // With no activation to return to, `complete_frame` hands back
                    // the raw completion, so the receiver rule applies here.
                    Ok(Some(execution)) if self.is_object(execution.value) => Ok(execution.value),
                    Ok(Some(_)) => Ok(object),
                    Err(error) => {
                        self.unwind_frames_to(stop_depth);
                        match error.kind {
                            RuntimeErrorKind::UncaughtThrow { value, origin, .. } => {
                                Err(EvalFailure::ThrowValueOrigin { value, origin })
                            }
                            kind => Err(EvalFailure::Runtime(kind)),
                        }
                    }
                }
            }
            CalleeKind::Bound => {
                let bound = self
                    .flatten_bound(callee, Value::UNDEFINED, arguments, new_target)
                    .map_err(EvalFailure::Runtime)?;
                self.internal_construct(bound.target, &bound.arguments, bound.new_target)
            }
            CalleeKind::Proxy => self.with_proxy_dispatch(|machine| {
                crate::builtins::proxy::construct(machine, callee, arguments, new_target)
            }),
            CalleeKind::ProxyRevoker | CalleeKind::NotCallable => {
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "construct",
                }))
            }
        }
    }

    /// `construct_value` is the `new_target = callee` construct entry used by
    /// engine-internal construction; the canonical entry is
    /// [`Machine::internal_construct`].
    pub(crate) fn construct_value(
        &mut self,
        callee: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        self.internal_construct(callee, arguments, callee)
    }

    pub(crate) fn call_value(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        self.call_user_code(
            |machine| machine.dispatch_call(callee, this_value, arguments),
            Self::keep_temporary,
        )
    }

    fn dispatch_call(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        let mark = self.builtin_temporaries.len();
        let result = self.dispatch_call_forwarding(callee, this_value, arguments);
        self.release_temporaries(mark);
        result
    }

    /// [`Machine::dispatch_call`], which releases what this holds for a forward.
    fn dispatch_call_forwarding(
        &mut self,
        callee: Value,
        this_value: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        let mut callee = callee;
        let mut this_value = this_value;
        let mut arguments = Cow::Borrowed(arguments);
        loop {
            match self.callee_kind(callee).map_err(EvalFailure::Runtime)? {
                CalleeKind::Builtin { id } => {
                    match self.call_builtin(id, this_value, arguments.as_ref(), false)? {
                        intrinsics::BuiltinOutcome::Value(value) => return Ok(value),
                        intrinsics::BuiltinOutcome::Call {
                            callee: next,
                            this_value: next_this,
                            arguments: next_arguments,
                        } => {
                            self.hold_forwarded_call(next, next_this, &next_arguments);
                            callee = next;
                            this_value = next_this;
                            arguments = Cow::Owned(next_arguments);
                        }
                        intrinsics::BuiltinOutcome::GeneratorResume {
                            generator,
                            completion,
                        } => return self.resume_generator(generator, completion),
                        intrinsics::BuiltinOutcome::AsyncGeneratorResume {
                            generator,
                            completion,
                        } => return self.enqueue_async_generator_request(generator, completion),
                    }
                }
                CalleeKind::Runtime {
                    target,
                    captures,
                    context,
                } => {
                    if self.stack_overflows() {
                        return Err(EvalFailure::Throw(STACK_OVERFLOW));
                    }
                    let flags = self.module_code(target.module).functions()
                        [target.function.get() as usize]
                        .flags();
                    if flags.is_generator {
                        let start = GeneratorStart {
                            target,
                            context,
                            captures,
                            this_value,
                            new_target: Value::UNDEFINED,
                            args: arguments.as_ref().to_vec(),
                        };
                        return self.start_generator(start, flags);
                    }
                    if flags.is_async && !flags.is_generator {
                        return crate::vm::generator_async::start_async_function(
                            self,
                            target,
                            &captures,
                            context,
                            this_value,
                            Value::UNDEFINED,
                            arguments.as_ref(),
                        );
                    }
                    let stop_depth = self.frames.len();
                    let return_to = self.frames.last().map(|frame| ReturnTo {
                        destination: None,
                        call_pc: frame.pc,
                        constructed: None,
                    });
                    self.push_frame(ActivationRequest {
                        target,
                        captures: &captures,
                        context,
                        this_value,
                        new_target: Value::UNDEFINED,
                        arguments: arguments.as_ref(),
                        return_to,
                    })
                    .map_err(|error| EvalFailure::Runtime(error.kind))?;
                    self.callback_boundaries.push(stop_depth);
                    let result = self.run_loop(stop_depth);
                    self.callback_boundaries
                        .pop()
                        .expect("nested runtime callback owns its unwind boundary");
                    return match result {
                        Ok(None) => self.last_completion.take().ok_or(EvalFailure::Runtime(
                            RuntimeErrorKind::InvalidValue {
                                value: Value::UNDEFINED,
                            },
                        )),
                        Ok(Some(execution)) => Ok(execution.value),
                        Err(error) => {
                            self.unwind_frames_to(stop_depth);
                            match error.kind {
                                RuntimeErrorKind::UncaughtThrow { value, origin, .. } => {
                                    Err(EvalFailure::ThrowValueOrigin { value, origin })
                                }
                                kind => Err(EvalFailure::Runtime(kind)),
                            }
                        }
                    };
                }
                CalleeKind::Bound => {
                    let bound = self
                        .flatten_bound(callee, this_value, arguments.as_ref(), Value::UNDEFINED)
                        .map_err(EvalFailure::Runtime)?;
                    callee = bound.target;
                    this_value = bound.this_value;
                    arguments = Cow::Owned(bound.arguments);
                }
                CalleeKind::Proxy => {
                    return self.with_proxy_dispatch(|machine| {
                        crate::builtins::proxy::call(
                            machine,
                            callee,
                            this_value,
                            arguments.as_ref(),
                        )
                    });
                }
                CalleeKind::ProxyRevoker => {
                    return crate::builtins::proxy::call_revoker(self, callee);
                }
                CalleeKind::NotCallable => {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "call",
                    }));
                }
            }
        }
    }

    fn unwind_frames_to(&mut self, depth: usize) {
        while self.frames.len() > depth {
            let frame = self.frames.pop().expect("frame depth was checked");
            self.context_global = frame.outer_context;
            self.live_registers -= frame.registers.len();
        }
    }

    fn complete_frame(&mut self, returned: Value) -> Option<Execution> {
        let frame = self.frames.pop().expect("an activation is executing");
        self.context_global = frame.outer_context;
        self.live_registers -= frame.registers.len();
        match frame.return_to {
            None => {
                let outcome = ExecutionOutcome {
                    stdout: Vec::new(),
                    exit_code: 0,
                };
                Some(Execution {
                    outcome,
                    value: returned,
                    link: returned,
                    entry_registers: frame.registers,
                })
            }
            Some(return_to) => {
                let value = match return_to.constructed {
                    Some(object) if !self.is_object(returned) => object,
                    _ => returned,
                };
                if let Some(destination) = return_to.destination {
                    self.frames.last_mut().expect("callee has caller").registers[destination] =
                        value;
                } else {
                    self.last_completion = Some(value);
                }
                None
            }
        }
    }

    fn resolve_failure(&mut self, failure: EvalFailure, pc: usize) -> Result<(), RuntimeError> {
        match failure {
            EvalFailure::Throw(origin) => self.throw(Value::UNDEFINED, origin, pc),
            EvalFailure::ThrowValue(value) => self.throw(value, ThrowOrigin::Bytecode, pc),
            EvalFailure::ThrowValueOrigin { value, origin } => self.throw(value, origin, pc),
            EvalFailure::Runtime(kind) => Err(self.error_here_at(kind, pc)),
        }
    }

    fn throw_type(&mut self, operation: &'static str, pc: usize) -> Result<(), RuntimeError> {
        self.throw(Value::UNDEFINED, ThrowOrigin::TypeError { operation }, pc)
    }

    fn throw(
        &mut self,
        value: Value,
        origin: ThrowOrigin,
        faulting_pc: usize,
    ) -> Result<(), RuntimeError> {
        let site_module = self
            .frames
            .last()
            .expect("an activation is executing")
            .module;
        let site_function = self
            .frames
            .last()
            .expect("an activation is executing")
            .function;
        let mut search_pc = faulting_pc;
        loop {
            if self
                .callback_boundaries
                .last()
                .is_some_and(|boundary| self.frames.len() == *boundary)
            {
                return Err(self.error_at_in_module(
                    RuntimeErrorKind::UncaughtThrow {
                        value,
                        origin,
                        constructor_name: None,
                        message: None,
                    },
                    site_module,
                    site_function,
                    faulting_pc,
                ));
            }
            let frame_index = self.frames.len() - 1;
            let function_index = self.frames[frame_index].function;
            let module = self.frames[frame_index].module;
            let function = &self.module_code(module).functions()[function_index];
            if let Some(handler) = innermost_handler(function, search_pc) {
                // Bytecode throws and already-materialized engine errors keep
                // their supplied value. Only an unmaterialized (UNDEFINED)
                // non-Bytecode origin allocates an intrinsic error object.
                let catch_value = if catch_value_needs_materialization(value, origin) {
                    self.materialize_engine_origin(origin).map_err(|kind| {
                        self.error_at_in_module(kind, site_module, site_function, faulting_pc)
                    })?
                } else {
                    value
                };
                let frame = &mut self.frames[frame_index];
                frame.registers[handler.catch_register.get() as usize] = catch_value;
                frame.pc = handler.handler.get() as usize;
                return Ok(());
            }
            let frame = self.frames.pop().expect("throw walks live frames");
            self.context_global = frame.outer_context;
            self.live_registers -= frame.registers.len();
            match frame.return_to {
                Some(return_to) => search_pc = return_to.call_pc,
                None => {
                    return Err(self.error_at_in_module(
                        RuntimeErrorKind::UncaughtThrow {
                            value,
                            origin,
                            constructor_name: None,
                            message: None,
                        },
                        site_module,
                        site_function,
                        faulting_pc,
                    ));
                }
            }
        }
    }

    fn error_here(&self, kind: RuntimeErrorKind) -> RuntimeError {
        let frame = self.frames.last().expect("an activation is executing");
        self.error_at(kind, frame.function, frame.pc)
    }

    fn error_here_at(&self, kind: RuntimeErrorKind, pc: usize) -> RuntimeError {
        let function = self
            .frames
            .last()
            .expect("an activation is executing")
            .function;
        self.error_at(kind, function, pc)
    }

    fn error_at(&self, kind: RuntimeErrorKind, function: usize, pc: usize) -> RuntimeError {
        self.error_at_in_module(kind, self.active_module_id(), function, pc)
    }

    pub(crate) fn error_at_in_module(
        &self,
        kind: RuntimeErrorKind,
        module: ModuleId,
        function: usize,
        pc: usize,
    ) -> RuntimeError {
        let code = self.module_code(module);
        let metadata = &code.functions()[function];
        let function_name =
            metadata
                .name()
                .and_then(|id| match &code.constants()[id.get() as usize] {
                    Constant::String(name) => Some(name.clone()),
                    _ => None,
                });
        RuntimeError {
            kind,
            function: FunctionId::new(function as u32),
            pc: Pc::new(pc as u32),
            source: RuntimeSource {
                function_name,
                instruction: metadata.code()[pc],
            },
        }
    }

    // ---- property keys -----------------------------------------------------

    /// Normalizes a register value into a property key. A runtime string borrows
    /// its text; a private name yields its slot identity; everything else is
    /// coerced with `ToString`.
    fn property_key_from_value(&mut self, value: Value) -> Result<PropertyKey, EvalFailure> {
        if let Some(index) = self.string_slot(value) {
            let text = self.flat_string(index);
            return Ok(PropertyKey::Named(self.atoms.intern(text)));
        }
        match self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
            Some(index) => match &self.heap[index] {
                HeapEntry::Symbol { .. } => Ok(PropertyKey::Symbol(index as u32)),
                HeapEntry::PrivateName { .. } => Ok(PropertyKey::Private(index as u32)),
                _ => {
                    let text = self.value_to_string(value, 0)?;
                    Ok(PropertyKey::Named(self.atoms.intern(text)))
                }
            },
            None => {
                let text = self.value_to_string(value, 0)?;
                Ok(PropertyKey::Named(self.atoms.intern(text)))
            }
        }
    }

    // ---- property get ------------------------------------------------------

    fn resolve_get(
        &mut self,
        object: Value,
        key: &PropertyKey,
        receiver: Value,
    ) -> Result<GetOutcome, EvalFailure> {
        let slot = self.runtime_slot(object).map_err(EvalFailure::Runtime)?;
        let start = match slot {
            Some(index) => {
                if matches!(self.heap[index], HeapEntry::ProcessEnv { .. }) {
                    let PropertyKey::Named(name) = key else {
                        return Ok(GetOutcome::Value(Value::UNDEFINED));
                    };
                    let key_str = self.atoms.utf8(*name).map(|text| text.to_owned());
                    let text = key_str
                        .as_deref()
                        .and_then(|name| self.host.env(name))
                        .map(EcmaString::encode);
                    return match text {
                        Some(text) => self
                            .allocate(HeapEntry::String(text))
                            .map(GetOutcome::Value)
                            .map_err(EvalFailure::Runtime),
                        None => Ok(GetOutcome::Value(Value::UNDEFINED)),
                    };
                }
                if let Some(found) = self.primitive_get(index, key) {
                    return self.found_outcome(found);
                }
                match self.heap[index] {
                    HeapEntry::String(_) | HeapEntry::Rope { .. } => self
                        .runtime_slot(self.intrinsics.string_prototype)
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::BigInt(_) => self
                        .runtime_slot(self.intrinsics.builtins.bigint_prototype())
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::PrivateName { .. } => self
                        .runtime_slot(self.intrinsics.object_prototype)
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::Symbol { .. } => self
                        .runtime_slot(self.intrinsics.builtins.symbol_prototype())
                        .map_err(EvalFailure::Runtime)?,
                    _ => Some(index),
                }
            }
            None => {
                let prototype = match object.decode() {
                    Some(Decoded::Boolean(_)) => self.intrinsics.boolean_prototype,
                    Some(Decoded::Number(_) | Decoded::Int32(_)) => {
                        self.intrinsics.number_prototype
                    }
                    _ => return Ok(GetOutcome::Value(Value::UNDEFINED)),
                };
                self.runtime_slot(prototype).map_err(EvalFailure::Runtime)?
            }
        };
        let Some(mut node) = start else {
            return Ok(GetOutcome::Value(Value::UNDEFINED));
        };
        for _ in 0..=self.heap.len() {
            if !matches!(key, PropertyKey::Private(_))
                && matches!(self.heap[node], HeapEntry::Proxy { .. })
            {
                let value =
                    self.internal_get(self.value_for_runtime_index(node)?, key, receiver)?;
                return Ok(GetOutcome::Value(value));
            }
            if let PropertyKey::Named(name) = key
                && let HeapEntry::TypedArray { .. } = &self.heap[node]
                && let Some(typed_index) = typedarray::typed_array_index(self.atoms.resolve(*name))
            {
                let view = self.value_for_runtime_index(node)?;
                let value = match typed_index {
                    Some(offset) => typedarray::read_element(self, view, offset)?,
                    None => Value::UNDEFINED,
                };
                return Ok(GetOutcome::Value(value));
            }
            if let Some(found) = self.own_get(node, key) {
                return self.found_outcome(found);
            }
            match self.prototype_index(node)? {
                Some(next) => node = next,
                None => return Ok(GetOutcome::Value(Value::UNDEFINED)),
            }
        }
        Ok(GetOutcome::Value(Value::UNDEFINED))
    }

    fn resolve_get_atom(
        &mut self,
        object: Value,
        atom: Atom,
        receiver: Value,
    ) -> Result<GetOutcome, EvalFailure> {
        debug_assert!(self.atoms.is_ascii(atom));
        let slot = self.runtime_slot(object).map_err(EvalFailure::Runtime)?;
        let start = match slot {
            Some(index) => {
                if matches!(self.heap[index], HeapEntry::ProcessEnv { .. }) {
                    return match self
                        .atoms
                        .utf8(atom)
                        .and_then(|name| self.host.env(name))
                        .map(EcmaString::encode)
                    {
                        Some(text) => self
                            .allocate(HeapEntry::String(text))
                            .map(GetOutcome::Value)
                            .map_err(EvalFailure::Runtime),
                        None => Ok(GetOutcome::Value(Value::UNDEFINED)),
                    };
                }
                let is_string = matches!(
                    &self.heap[index],
                    HeapEntry::String(_) | HeapEntry::Rope { .. }
                );
                if is_string && self.atoms.eq_ascii(atom, "length") {
                    let len = self.string_len(index);
                    return Ok(GetOutcome::Value(number_value(len as f64)));
                }
                if is_string && let Some(offset) = self.atoms.array_index(atom) {
                    let text = self.flat_string(index);
                    if let Some(unit) = text.unit_at(offset as usize) {
                        return Ok(GetOutcome::Text(EcmaString::from_units(&[unit])));
                    }
                }
                match self.heap[index] {
                    HeapEntry::String(_) | HeapEntry::Rope { .. } => self
                        .runtime_slot(self.intrinsics.string_prototype)
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::BigInt(_) => self
                        .runtime_slot(self.intrinsics.builtins.bigint_prototype())
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::PrivateName { .. } => self
                        .runtime_slot(self.intrinsics.object_prototype)
                        .map_err(EvalFailure::Runtime)?,
                    HeapEntry::Symbol { .. } => self
                        .runtime_slot(self.intrinsics.builtins.symbol_prototype())
                        .map_err(EvalFailure::Runtime)?,
                    _ => Some(index),
                }
            }
            None => {
                let prototype = match object.decode() {
                    Some(Decoded::Boolean(_)) => self.intrinsics.boolean_prototype,
                    Some(Decoded::Number(_) | Decoded::Int32(_)) => {
                        self.intrinsics.number_prototype
                    }
                    _ => return Ok(GetOutcome::Value(Value::UNDEFINED)),
                };
                self.runtime_slot(prototype).map_err(EvalFailure::Runtime)?
            }
        };
        let ascii_key = PropertyKey::Named(atom);
        let Some(mut node) = start else {
            return Ok(GetOutcome::Value(Value::UNDEFINED));
        };
        for _ in 0..=self.heap.len() {
            if matches!(self.heap[node], HeapEntry::Proxy { .. }) {
                let base = self.value_for_runtime_index(node)?;
                let value = self.internal_get(base, &ascii_key, receiver)?;
                return Ok(GetOutcome::Value(value));
            }
            if let HeapEntry::TypedArray { .. } = &self.heap[node]
                && let Some(typed_index) = typedarray::typed_array_index(self.atoms.resolve(atom))
            {
                let view = self.value_for_runtime_index(node)?;
                let value = match typed_index {
                    Some(offset) => typedarray::read_element(self, view, offset)?,
                    None => Value::UNDEFINED,
                };
                return Ok(GetOutcome::Value(value));
            }
            if let Some(found) = self.own_get_atom(node, atom) {
                return self.found_outcome(found);
            }
            match self.prototype_index(node)? {
                Some(next) => node = next,
                None => return Ok(GetOutcome::Value(Value::UNDEFINED)),
            }
        }
        Ok(GetOutcome::Value(Value::UNDEFINED))
    }
    fn found_outcome(&mut self, found: Found) -> Result<GetOutcome, EvalFailure> {
        match found {
            Found::Value(Value::UNINITIALIZED) => Err(self.uninitialized_read()),
            Found::Value(value) => Ok(GetOutcome::Value(value)),
            Found::Text(text) => Ok(GetOutcome::Text(text)),
            Found::Getter(getter) => Ok(GetOutcome::Getter(getter)),
            Found::Failure(kind) => Err(self.read_failure(kind)),
            Found::NoGetter => Ok(GetOutcome::Value(Value::UNDEFINED)),
        }
    }

    /// The `ReferenceError` of a read before a binding is initialized.
    fn uninitialized_read(&mut self) -> EvalFailure {
        let id = self
            .intrinsics
            .builtins
            .id_named("ReferenceError")
            .expect("ReferenceError intrinsic is installed");
        match self.throw_error(
            id,
            EcmaString::encode("Cannot access lexical binding before initialization"),
        ) {
            EvalFailure::ThrowValue(value) => EvalFailure::ThrowValueOrigin {
                value,
                origin: ThrowOrigin::ReferenceError {
                    operation: "lexical binding is uninitialized",
                },
            },
            failure => failure,
        }
    }

    /// The failure of a read. A program can catch a read before initialization, and
    /// any other kind ends it.
    pub(crate) fn read_failure(&mut self, kind: RuntimeErrorKind) -> EvalFailure {
        match kind {
            RuntimeErrorKind::TemporalDeadZone { .. } => self.uninitialized_read(),
            kind => EvalFailure::Runtime(kind),
        }
    }

    /// Bounds-resolved element count of the TypedArray at `index`. Detached
    /// or out-of-bounds views expose zero accessible elements.
    fn typed_array_length_at(&self, index: usize) -> Option<usize> {
        let view = self.value_for_runtime_index(index).ok()?;
        let bounds = typedarray::typed_array_bounds(self, view).ok()?;
        (!bounds.out_of_bounds).then_some(bounds.element_length)
    }

    fn primitive_get(&mut self, index: usize, key: &PropertyKey) -> Option<Found> {
        if !matches!(
            &self.heap[index],
            HeapEntry::String(_) | HeapEntry::Rope { .. }
        ) {
            return None;
        }
        if let PropertyKey::Named(atom) = key
            && self.atoms.eq_ascii(*atom, "length")
        {
            return Some(Found::Value(number_value(self.string_len(index) as f64)));
        }
        let text = self.flat_string(index);
        string_own_get(&text, &self.atoms, key)
    }

    fn own_get_atom(&mut self, index: usize, atom: Atom) -> Option<Found> {
        debug_assert!(self.atoms.is_ascii(atom));
        let boxed_text = match &self.heap[index] {
            HeapEntry::Object {
                boxed_primitive: Some(primitive),
                ..
            } => self.string_slot(*primitive),
            _ => None,
        };
        let boxed_text = boxed_text.map(|slot| self.flat_string(slot));
        match &self.heap[index] {
            HeapEntry::Object {
                properties,
                boxed_primitive,
                ..
            } => {
                if let Some(found) =
                    property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
                {
                    return Some(found);
                }
                if boxed_primitive.is_some() {
                    return boxed_text.as_ref().and_then(|text| {
                        string_own_get(text, &self.atoms, &PropertyKey::Named(atom))
                    });
                }
                None
            }
            HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Timeout { properties, .. }
            | HeapEntry::ProxyRevoker { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. } => {
                property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
            }
            HeapEntry::DataView { properties, .. } => {
                property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
            }
            HeapEntry::Array {
                elements,
                properties,
                ..
            } => {
                if self.atoms.eq_ascii(atom, "length") {
                    return Some(Found::Value(number_value(elements.len() as f64)));
                }
                if let Some(offset) = self.atoms.array_index(atom)
                    && let Some(element) = elements.get(offset as usize)
                    && *element != Value::HOLE
                {
                    return Some(Found::Value(*element));
                }
                property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
            }
            HeapEntry::TypedArray { properties, .. } => {
                if let Some(typed_index) = typedarray::typed_array_index(self.atoms.resolve(atom)) {
                    return typed_index
                        .zip(self.typed_array_length_at(index))
                        .is_some_and(|(offset, length)| offset < length)
                        .then_some(Found::Value(Value::UNDEFINED));
                }
                property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
            }
            HeapEntry::Function {
                module,
                function,
                properties,
                ..
            } => {
                if let Some(found) =
                    property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
                {
                    return Some(found);
                }
                if properties.contains_key(
                    &self.shapes,
                    &self.intrinsics.builtins.function_reified_key(),
                ) {
                    return None;
                }
                let metadata = &self.module_code(*module).functions()[function.get() as usize];
                if self.atoms.eq_ascii(atom, "length") {
                    return Some(Found::Value(
                        number_value(metadata.parameter_count() as f64),
                    ));
                }
                if self.atoms.eq_ascii(atom, "name") {
                    return Some(Found::Text(
                        metadata
                            .name()
                            .map(|id| self.constant_text(*module, id).clone())
                            .unwrap_or_default(),
                    ));
                }
                None
            }
            HeapEntry::ModuleNamespace { module } => {
                let key = self
                    .program_module(*module)
                    .exports
                    .iter()
                    .map(|export| self.constant_text(*module, export.name))
                    .find(|candidate| {
                        self.atoms
                            .utf8(atom)
                            .is_some_and(|name| candidate.eq_ascii(name))
                    })?
                    .clone();
                match self.namespace_export(*module, &key) {
                    Ok(Some(value)) => Some(Found::Value(value)),
                    Ok(None) => None,
                    Err(kind) => Some(Found::Failure(kind)),
                }
            }
            HeapEntry::ExternalModuleNamespace { specifier } => {
                let export = self.registry.external[specifier].exports.iter().find_map(
                    |(candidate, export)| {
                        self.atoms
                            .utf8(atom)
                            .is_some_and(|name| candidate.eq_ascii(name))
                            .then_some(export)
                    },
                )?;
                Some(Found::Value(export.cell.map_or(export.value, |cell| {
                    self.registry.cells[cell.0].value
                })))
            }
            HeapEntry::RegExp { properties, .. } => {
                property_lookup(properties, &self.shapes, &PropertyKey::Named(atom))
            }
            HeapEntry::HashState { update, digest, .. } if self.atoms.eq_ascii(atom, "update") => {
                Some(Found::Value(*update))
            }
            HeapEntry::HashState { digest, .. } if self.atoms.eq_ascii(atom, "digest") => {
                Some(Found::Value(*digest))
            }
            HeapEntry::HashState { .. } => None,
            HeapEntry::ProcessEnv { .. }
            | HeapEntry::String(_)
            | HeapEntry::Rope { .. }
            | HeapEntry::BigInt(_)
            | HeapEntry::Symbol { .. }
            | HeapEntry::PrivateName { .. }
            | HeapEntry::Iterator { .. }
            | HeapEntry::PromiseResolver { .. }
            | HeapEntry::PromiseAll { .. }
            | HeapEntry::AsyncActivation { .. }
            | HeapEntry::Proxy { .. }
            | HeapEntry::PromiseAllElement { .. } => None,
            HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
        }
    }

    /// Looks up an own property of the heap entry at `index`, returning `None`
    /// when the key is absent so the caller may continue up the prototype chain.
    fn own_get(&mut self, index: usize, key: &PropertyKey) -> Option<Found> {
        let is_string = matches!(
            &self.heap[index],
            HeapEntry::String(_) | HeapEntry::Rope { .. }
        );
        if is_string
            && let PropertyKey::Named(atom) = key
            && self.atoms.eq_ascii(*atom, "length")
        {
            return Some(Found::Value(number_value(self.string_len(index) as f64)));
        }
        let boxed = match &self.heap[index] {
            HeapEntry::Object {
                properties,
                boxed_primitive: Some(primitive),
                ..
            } => {
                if let Some(found) = property_lookup(properties, &self.shapes, key) {
                    return Some(found);
                }
                Some(*primitive)
            }
            _ => None,
        };
        if let Some(primitive) = boxed
            && let Some(slot) = self.string_slot(primitive)
        {
            if let PropertyKey::Named(atom) = key
                && self.atoms.eq_ascii(*atom, "length")
            {
                return Some(Found::Value(number_value(self.string_len(slot) as f64)));
            }
            let text = self.flat_string(slot);
            return string_own_get(&text, &self.atoms, key);
        }
        let direct_text =
            (is_string && matches!(key, PropertyKey::Named(_))).then(|| self.flat_string(index));
        match &self.heap[index] {
            HeapEntry::Object { properties, .. } => {
                if let Some(found) = property_lookup(properties, &self.shapes, key) {
                    return Some(found);
                }
                None
            }
            HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Timeout { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::ProxyRevoker { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. } => {
                property_lookup(properties, &self.shapes, key)
            }
            HeapEntry::DataView { properties, .. } => {
                property_lookup(properties, &self.shapes, key)
            }
            HeapEntry::Array {
                elements,
                properties,
                ..
            } => {
                if let PropertyKey::Named(atom) = key {
                    if self.atoms.eq_ascii(*atom, "length") {
                        return Some(Found::Value(number_value(elements.len() as f64)));
                    }
                    if let Some(offset) = self.atoms.array_index(*atom)
                        && let Some(element) = elements.get(offset as usize)
                        && *element != Value::HOLE
                    {
                        return Some(Found::Value(*element));
                    }
                }
                property_lookup(properties, &self.shapes, key)
            }
            HeapEntry::TypedArray { properties, .. } => {
                if let PropertyKey::Named(atom) = key
                    && let Some(typed_index) =
                        typedarray::typed_array_index(self.atoms.resolve(*atom))
                {
                    return typed_index
                        .zip(self.typed_array_length_at(index))
                        .is_some_and(|(offset, length)| offset < length)
                        .then_some(Found::Value(Value::UNDEFINED));
                }
                property_lookup(properties, &self.shapes, key)
            }
            HeapEntry::Function {
                module,
                function,
                properties,
                ..
            } => {
                if let Some(found) = property_lookup(properties, &self.shapes, key) {
                    return Some(found);
                }
                if let PropertyKey::Named(atom) = key
                    && !properties.contains_key(
                        &self.shapes,
                        &self.intrinsics.builtins.function_reified_key(),
                    )
                {
                    let metadata = &self.module_code(*module).functions()[function.get() as usize];
                    if self.atoms.eq_ascii(*atom, "length") {
                        return Some(Found::Value(
                            number_value(metadata.parameter_count() as f64),
                        ));
                    }
                    if self.atoms.eq_ascii(*atom, "name") {
                        return Some(Found::Text(
                            metadata
                                .name()
                                .map(|id| self.constant_text(*module, id).clone())
                                .unwrap_or_default(),
                        ));
                    }
                }
                None
            }
            HeapEntry::ModuleNamespace { module } => {
                let PropertyKey::Named(atom) = key else {
                    return None;
                };
                match self.namespace_export(*module, self.atoms.resolve(*atom)) {
                    Ok(Some(value)) => Some(Found::Value(value)),
                    Ok(None) => None,
                    Err(kind) => Some(Found::Failure(kind)),
                }
            }
            HeapEntry::ExternalModuleNamespace { specifier } => {
                let PropertyKey::Named(atom) = key else {
                    return None;
                };
                let export = self.registry.external[specifier]
                    .exports
                    .get(self.atoms.resolve(*atom))?;
                Some(Found::Value(export.cell.map_or(export.value, |cell| {
                    self.registry.cells[cell.0].value
                })))
            }
            HeapEntry::NativeFunction { properties, .. } => {
                property_lookup(properties, &self.shapes, key)
            }
            HeapEntry::RegExp { properties, .. } => property_lookup(properties, &self.shapes, key),
            HeapEntry::HashState { update, digest, .. } => {
                let PropertyKey::Named(atom) = key else {
                    return None;
                };
                if self.atoms.eq_ascii(*atom, "update") {
                    Some(Found::Value(*update))
                } else if self.atoms.eq_ascii(*atom, "digest") {
                    Some(Found::Value(*digest))
                } else {
                    None
                }
            }
            HeapEntry::String(_) | HeapEntry::Rope { .. } => direct_text
                .as_ref()
                .and_then(|text| string_own_get(text, &self.atoms, key)),
            HeapEntry::ProcessEnv { .. }
            | HeapEntry::BigInt(_)
            | HeapEntry::Symbol { .. }
            | HeapEntry::PrivateName { .. }
            | HeapEntry::Iterator { .. }
            | HeapEntry::PromiseResolver { .. }
            | HeapEntry::PromiseAll { .. }
            | HeapEntry::AsyncActivation { .. }
            | HeapEntry::Proxy { .. }
            | HeapEntry::PromiseAllElement { .. } => None,
            HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
        }
    }

    fn namespace_export(
        &self,
        module: ModuleId,
        name: &EcmaString,
    ) -> Result<Option<Value>, RuntimeErrorKind> {
        if module.get() as usize >= self.dynamic_base {
            return Ok(None);
        }
        match self.program().resolve_export(module, name) {
            Some(ResolvedExport::Local { module, binding }) => {
                let cell = self.registry.modules[module.get() as usize].binding_cells
                    [binding.get() as usize]
                    .expect("verified export resolves to a linked cell");
                let value = self.registry.cells[cell.0].value;
                if value.is_uninitialized() {
                    Err(RuntimeErrorKind::TemporalDeadZone { module, binding })
                } else {
                    Ok(Some(value))
                }
            }
            Some(ResolvedExport::External { module, edge, name }) => {
                let Some(specifier) = self.external_specifier(module, edge) else {
                    return Err(RuntimeErrorKind::ExternalModuleUnavailable { module, edge });
                };
                let name = self.constant_text(module, name);
                let Some(export) = self.registry.external[&specifier].exports.get(name) else {
                    return Err(RuntimeErrorKind::ExternalModuleUnavailable { module, edge });
                };
                let Some(cell) = export.cell else {
                    return Err(RuntimeErrorKind::ExternalModuleUnavailable { module, edge });
                };
                Ok(Some(self.registry.cells[cell.0].value))
            }
            None => Ok(None),
        }
    }

    #[cfg(test)]
    fn own_data_property(&self, index: usize, name: &str) -> Option<Value> {
        let properties = match &self.heap[index] {
            HeapEntry::Object { properties, .. }
            | HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::Array { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::TypedArray { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::ProxyRevoker { properties, .. }
            | HeapEntry::Timeout { properties, .. } => properties,
            _ => return None,
        };
        match properties.get_ascii(&self.shapes, &self.atoms, name) {
            Some(Property::Data { value, .. }) => Some(*value),
            _ => None,
        }
    }

    fn prototype_index(&self, index: usize) -> Result<Option<usize>, EvalFailure> {
        let prototype = match &self.heap[index] {
            HeapEntry::Object { prototype, .. }
            | HeapEntry::Generator { prototype, .. }
            | HeapEntry::AsyncGenerator { prototype, .. }
            | HeapEntry::AsyncFromSync { prototype, .. }
            | HeapEntry::Script { prototype, .. }
            | HeapEntry::Array { prototype, .. }
            | HeapEntry::Function { prototype, .. }
            | HeapEntry::RegExp { prototype, .. }
            | HeapEntry::Date { prototype, .. }
            | HeapEntry::Temporal { prototype, .. }
            | HeapEntry::Intl { prototype, .. }
            | HeapEntry::BuiltinIterator { prototype, .. }
            | HeapEntry::Collection { prototype, .. }
            | HeapEntry::TypedArray { prototype, .. }
            | HeapEntry::ArrayBuffer { prototype, .. }
            | HeapEntry::SharedArrayBuffer { prototype, .. }
            | HeapEntry::DataView { prototype, .. }
            | HeapEntry::Promise { prototype, .. }
            | HeapEntry::WeakRef { prototype, .. }
            | HeapEntry::FinalizationRegistry { prototype, .. }
            | HeapEntry::DisposableStack { prototype, .. }
            | HeapEntry::Timeout { prototype, .. }
            | HeapEntry::ProcessEnv { prototype, .. } => *prototype,
            HeapEntry::ProxyRevoker { .. } => Some(self.intrinsics.function_prototype),
            HeapEntry::NativeFunction { prototype, .. } => {
                prototype.or(Some(self.intrinsics.function_prototype))
            }
            _ => None,
        };
        match prototype {
            Some(value) => self.runtime_slot(value).map_err(EvalFailure::Runtime),
            None => Ok(None),
        }
    }

    fn value_for_runtime_index(&self, index: usize) -> Result<Value, EvalFailure> {
        let slot = u32::try_from(index + 1).map_err(|_| {
            EvalFailure::Throw(ThrowOrigin::RangeError {
                operation: "runtime heap slot exceeds u32",
            })
        })?;
        Ok(Value::heap_ref(
            SlotId::from_parts(RUNTIME_HEAP_SEGMENT, slot).expect("runtime heap slot is nonzero"),
        ))
    }

    fn super_base(&mut self, home: Value) -> Result<Value, EvalFailure> {
        let home_index = self
            .runtime_slot(home)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "super home object is not an object",
            }))?;
        match self.internal_get_prototype_of(self.value_for_runtime_index(home_index)?)? {
            Some(base) => Ok(base),
            None => Ok(Value::NULL),
        }
    }

    pub(crate) fn inherits_from_prototype(
        &self,
        value: Value,
        prototype: Value,
    ) -> Result<bool, EvalFailure> {
        let Some(mut current) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        let Some(target) = self.runtime_slot(prototype).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        let mut traversed = 0;
        while let Some(next) = self.prototype_index(current)? {
            if next == target {
                return Ok(true);
            }
            current = next;
            traversed += 1;
            if traversed > self.heap.len() {
                return Ok(false);
            }
        }
        Ok(false)
    }

    // ---- property set ------------------------------------------------------

    fn resolve_set(
        &mut self,
        object: Value,
        key: PropertyKey,
        value: Value,
        receiver: Value,
    ) -> Result<bool, EvalFailure> {
        let wrapper = self.value_to_object(object)?;
        if wrapper != object {
            return self.resolve_set(wrapper, key, value, receiver);
        }
        let index = match self.runtime_slot(object).map_err(EvalFailure::Runtime)? {
            Some(index) => index,
            None => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set property on primitive",
                }));
            }
        };
        if matches!(self.heap[index], HeapEntry::ModuleNamespace { .. }) {
            return Ok(false);
        }
        if matches!(self.heap[index], HeapEntry::ProcessEnv { .. }) {
            let PropertyKey::Named(name) = &key else {
                return Ok(true);
            };
            let Some(name) = self.atoms.utf8(*name).map(|name| name.to_owned()) else {
                return Ok(true);
            };
            let text = self.to_string(value)?;
            let text = crate::host_objects::env_value_text_lossy(&text);
            self.host.set_env(&name, &text);
            return Ok(true);
        }
        if matches!(self.heap[index], HeapEntry::TypedArray { .. })
            && matches!(&key, PropertyKey::Named(name) if typedarray::typed_array_index(self.atoms.resolve(*name)).is_some())
        {
            self.set_own_data(index, key, value)?;
            return Ok(true);
        }
        let mut node_index = index;
        let mut guard = 0;
        loop {
            if !matches!(key, PropertyKey::Private(_))
                && matches!(self.heap[node_index], HeapEntry::Proxy { .. })
            {
                return self.internal_set(
                    self.value_for_runtime_index(node_index)?,
                    key,
                    value,
                    receiver,
                );
            }
            let node = self.value_for_runtime_index(node_index)?;
            if let Some(descriptor) = self.own_descriptor(node, &key)? {
                return Ok(match descriptor {
                    Property::Accessor {
                        setter: Some(setter),
                        ..
                    } => {
                        self.call_value(setter, receiver, &[value])?;
                        true
                    }
                    Property::Accessor { setter: None, .. } => false,
                    Property::Data { writable: true, .. } => {
                        return self.ordinary_set_receiver(receiver, key, value);
                    }
                    Property::Data {
                        writable: false, ..
                    } => false,
                });
            }
            match self.prototype_index(node_index)? {
                Some(next) => node_index = next,
                None => break,
            }
            guard += 1;
            if guard > self.heap.len() + 1 {
                break;
            }
        }
        self.ordinary_set_receiver(receiver, key, value)
    }

    /// OrdinarySetWithOwnDescriptor's receiver tail: inspect the receiver's own
    /// descriptor and either update its value in place, reject, or create a
    /// fully attributed data property. A non-object receiver rejects.
    fn ordinary_set_receiver(
        &mut self,
        receiver: Value,
        key: PropertyKey,
        value: Value,
    ) -> Result<bool, EvalFailure> {
        if !self.is_object(receiver) {
            return Ok(false);
        }
        let Some(existing) = self.internal_get_own_property(receiver, &key)? else {
            // (d) absent — CreateDataProperty with full attributes. Ordinary
            // receivers take the stored-property path so Array element writes
            // and TypedArray virtual writes land in the right slot.
            if !self.internal_is_extensible(receiver)? {
                return Ok(false);
            }
            if self.heap_entry_is_proxy_value(receiver) {
                return self
                    .internal_define_own_property(
                        receiver,
                        key,
                        crate::builtins::property_descriptor::PropertyDescriptor {
                            value: Some(value),
                            writable: Some(true),
                            enumerable: Some(true),
                            configurable: Some(true),
                            ..Default::default()
                        },
                    )
                    .map(|_| true);
            }
            let Some(index) = self.object_slot(receiver)? else {
                return Ok(false);
            };
            self.set_own_data(index, key, value)?;
            return Ok(true);
        };
        if existing.is_accessor() || existing.writable == Some(false) {
            return Ok(false);
        }
        // (c) existing writable data — value-only update, attributes preserved.
        if self.heap_entry_is_proxy_value(receiver) {
            return self
                .internal_define_own_property(
                    receiver,
                    key,
                    crate::builtins::property_descriptor::PropertyDescriptor {
                        value: Some(value),
                        writable: Some(true),
                        enumerable: Some(existing.enumerable == Some(true)),
                        configurable: Some(existing.configurable == Some(true)),
                        ..Default::default()
                    },
                )
                .map(|_| true);
        }
        // Ordinary receiver: the stored-property fast path keeps the exact
        // attributes and handles Array element / TypedArray virtual writes.
        let Some(index) = self.object_slot(receiver)? else {
            return Ok(false);
        };
        if self.is_array_length_key(index, &key) {
            let descriptor = crate::builtins::property_descriptor::PropertyDescriptor {
                value: Some(value),
                ..Default::default()
            };
            return self.array_define_length(index, descriptor);
        }
        self.set_own_data(index, key, value)?;
        Ok(true)
    }

    /// The heap slot of `value` when it is an object. A primitive receiver is
    /// valid in `[[Set]]`, but it can hold nothing.
    fn object_slot(&self, value: Value) -> Result<Option<usize>, EvalFailure> {
        let slot = self.runtime_slot(value).map_err(EvalFailure::Runtime)?;
        Ok(slot.filter(|index| {
            !matches!(
                self.heap[*index],
                HeapEntry::String(_)
                    | HeapEntry::Rope { .. }
                    | HeapEntry::BigInt(_)
                    | HeapEntry::Symbol { .. }
            )
        }))
    }

    /// The site index of the instruction at `pc` in `(module, function)`.
    /// A non-site instruction, an unknown function, or an out-of-range pc
    /// yields none and the caller stays on the generic path.
    fn get_cache_slot(
        &mut self,
        module: ModuleId,
        function: FunctionId,
        pc: usize,
        which: Which,
    ) -> Option<usize> {
        if !self.property_sites.contains_key(&(module, function)) {
            let code = self.module_code(module).functions()[function.get() as usize].code();
            self.property_sites
                .insert((module, function), FunctionSites::build(code));
        }
        let sites = self.property_sites.get_mut(&(module, function))?;
        let index = match which {
            Which::Get => sites.gets.get_mut(pc)?,
            Which::Set => sites.sets.get_mut(pc)?,
        };
        if !index.usable() {
            return None;
        }
        Some(pc)
    }

    #[cfg(test)]
    pub(crate) fn function_sites(
        &mut self,
        module: ModuleId,
        function: FunctionId,
    ) -> &mut FunctionSites {
        if !self.property_sites.contains_key(&(module, function)) {
            let code = self.module_code(module).functions()[function.get() as usize].code();
            self.property_sites
                .insert((module, function), FunctionSites::build(code));
        }
        self.property_sites
            .get_mut(&(module, function))
            .expect("site table was just built")
    }

    /// The cached own-data value of `key` on `receiver` at `site`, or none
    /// when the site is empty, megamorphic, or the receiver does not match
    /// a cached shape and key.
    pub(crate) fn property_site_hit_get(
        &mut self,
        module: ModuleId,
        function: FunctionId,
        site: usize,
        receiver: Value,
        key: &PropertyKey,
    ) -> Option<Value> {
        let site_index = self.get_cache_slot(module, function, site, Which::Get)?;
        let index = self.runtime_slot(receiver).ok().flatten()?;

        {
            let HeapEntry::Object {
                properties,
                boxed_primitive: None,
                ..
            } = &self.heap[index]
            else {
                return None;
            };
            let PropertyMap::Shaped { shape, slots } = properties else {
                return None;
            };
            let site_state = &self.property_sites[&(module, function)].gets[site_index];
            if !site_state.matches(*shape, key) {
                return None;
            }
            let slot = self.shapes.slot_of(*shape, key)?;
            match slots.get(slot as usize) {
                Some(Property::Data { value, .. }) if *value != Value::UNINITIALIZED => {
                    Some(*value)
                }
                _ => None,
            }
        }
    }

    /// Records `(shape, key)` at `site` when the generic read found the key
    /// as an own data property of a plain shaped object.
    pub(crate) fn property_site_record_get(
        &mut self,
        module: ModuleId,
        function: FunctionId,
        site: usize,
        receiver: Value,
        key: &PropertyKey,
    ) {
        let Some(site_index) = self.get_cache_slot(module, function, site, Which::Get) else {
            return;
        };
        let Some(index) = self.runtime_slot(receiver).ok().flatten() else {
            return;
        };
        let Some(shape) = (match &self.heap[index] {
            HeapEntry::Object {
                properties: PropertyMap::Shaped { shape, .. },
                boxed_primitive: None,
                ..
            } => Some(*shape),
            _ => None,
        }) else {
            return;
        };
        match self.own_get(index, key) {
            Some(Found::Value(value)) if value != Value::UNINITIALIZED => {}
            Some(Found::Text(_)) => {}
            _ => return,
        }
        let sites = self
            .property_sites
            .get_mut(&(module, function))
            .expect("site table was built above");
        sites.gets[site_index].record(shape, key.clone());
    }

    /// Writes `value` through the cache at `site` when the receiver matches
    /// a cached shape and key holding own writable data. Returns whether
    /// the cache handled the store.
    pub(crate) fn property_site_hit_set(
        &mut self,
        module: ModuleId,
        function: FunctionId,
        site: usize,
        receiver: Value,
        key: &PropertyKey,
        value: Value,
    ) -> Option<()> {
        let site_index = self.get_cache_slot(module, function, site, Which::Set)?;
        let index = self.runtime_slot(receiver).ok().flatten()?;
        let (shape, slot, property) = {
            let HeapEntry::Object {
                properties,
                boxed_primitive: None,
                ..
            } = &self.heap[index]
            else {
                return None;
            };
            let PropertyMap::Shaped { shape, slots } = properties else {
                return None;
            };
            let site_state = &self.property_sites[&(module, function)].sets[site_index];
            if !site_state.matches(*shape, key) {
                return None;
            }
            let slot = self.shapes.slot_of(*shape, key)?;
            match slots.get(slot as usize)? {
                Property::Data {
                    writable: true,
                    enumerable,
                    configurable,
                    ..
                } => (
                    *shape,
                    slot,
                    Property::Data {
                        value,
                        writable: true,
                        enumerable: *enumerable,
                        configurable: *configurable,
                    },
                ),
                _ => return None,
            }
        };
        let HeapEntry::Object { properties, .. } = &mut self.heap[index] else {
            unreachable!("object brand was checked above")
        };
        let PropertyMap::Shaped {
            shape: current,
            slots,
        } = properties
        else {
            unreachable!("shaped map was checked above")
        };
        debug_assert_eq!(*current, shape);
        slots[slot as usize] = property;
        Some(())
    }

    /// Records `(shape, key)` at `site` when the key is already an own
    /// writable data property of a plain shaped object, so a later store
    /// keeps its attributes and never adds a property.
    pub(crate) fn property_site_record_set(
        &mut self,
        module: ModuleId,
        function: FunctionId,
        site: usize,
        receiver: Value,
        key: &PropertyKey,
    ) {
        let Some(site_index) = self.get_cache_slot(module, function, site, Which::Set) else {
            return;
        };
        let Some(index) = self.runtime_slot(receiver).ok().flatten() else {
            return;
        };
        let mut cacheable = None;
        if let HeapEntry::Object {
            properties: PropertyMap::Shaped { shape, slots },
            boxed_primitive: None,
            ..
        } = &self.heap[index]
            && let Some(slot) = self.shapes.slot_of(*shape, key)
            && let Some(Property::Data { writable: true, .. }) = slots.get(slot as usize)
        {
            cacheable = Some((*shape, slot));
        }
        let Some((shape, _slot)) = cacheable else {
            return;
        };
        let sites = self
            .property_sites
            .get_mut(&(module, function))
            .expect("site table was built above");
        sites.sets[site_index].record(shape, key.clone());
    }

    pub(crate) fn set_super(
        &mut self,
        home: Value,
        receiver: Value,
        key: PropertyKey,
        value: Value,
    ) -> Result<SetOutcome, EvalFailure> {
        let base = self.super_base(home)?;
        if base == Value::NULL {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "set super property through null prototype",
            }));
        }
        let mut node = base;
        let mut guard = 0;
        loop {
            if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(node) {
                return if self.internal_set(node, key, value, receiver)? {
                    Ok(SetOutcome::Done)
                } else {
                    Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "assign to read only super property",
                    }))
                };
            }
            if let Some(descriptor) = self.own_descriptor(node, &key)? {
                match descriptor {
                    Property::Accessor {
                        setter: Some(setter),
                        ..
                    } => return Ok(SetOutcome::Setter(setter)),
                    Property::Accessor { setter: None, .. } => {
                        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "set super property without setter",
                        }));
                    }
                    Property::Data {
                        writable: false, ..
                    } => {
                        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "assign to read only super property",
                        }));
                    }
                    Property::Data { writable: true, .. } => break,
                }
            }
            let Some(index) = self.runtime_slot(node).map_err(EvalFailure::Runtime)? else {
                break;
            };
            match self.prototype_index(index)? {
                Some(next) => node = self.value_for_runtime_index(next)?,
                None => break,
            }
            guard += 1;
            if guard > self.heap.len() + 1 {
                break;
            }
        }
        if !self.is_object(receiver) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "set super property on primitive",
            }));
        }
        if !self.ordinary_set_receiver(receiver, key, value)? {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "assign to read only super property",
            }));
        }
        Ok(SetOutcome::Done)
    }

    pub(crate) fn get_super(
        &mut self,
        home: Value,
        receiver: Value,
        key: &PropertyKey,
    ) -> Result<Value, EvalFailure> {
        let base = self.super_base(home)?;
        if base == Value::NULL {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "get super property through null prototype",
            }));
        }
        self.internal_get(base, key, receiver)
    }

    pub(crate) fn is_array_length_key(&self, index: usize, key: &PropertyKey) -> bool {
        matches!(key, PropertyKey::Named(name) if self.atoms.eq_ascii(*name, "length"))
            && matches!(self.heap[index], HeapEntry::Array { .. })
    }

    /// `ToUint32` and then `ToNumber`, which both run user code and must agree.
    fn array_length_value(&mut self, value: Value) -> Result<usize, EvalFailure> {
        let first = self.coerce_number_observable(value)?;
        let second = self.coerce_number_observable(value)?;
        let length = numeric_f64(first).map_or(0, to_uint32);
        if numeric_f64(second) == Some(f64::from(length)) {
            Ok(length as usize)
        } else {
            Err(EvalFailure::Throw(ThrowOrigin::RangeError {
                operation: "set array length",
            }))
        }
    }

    /// `ArraySetLength`. A non-configurable element stops a truncation there,
    /// which is reported as `false` after the elements above it have gone.
    pub(crate) fn array_define_length(
        &mut self,
        index: usize,
        descriptor: crate::builtins::property_descriptor::PropertyDescriptor,
    ) -> Result<bool, EvalFailure> {
        let length = descriptor
            .value
            .map(|value| self.array_length_value(value))
            .transpose()?;
        let HeapEntry::Array {
            elements,
            length_writable,
            ..
        } = &self.heap[index]
        else {
            unreachable!("array_define_length requires an array");
        };
        let (old_length, writable) = (elements.len(), *length_writable);
        if descriptor.is_accessor()
            || descriptor.enumerable == Some(true)
            || descriptor.configurable == Some(true)
            || (!writable
                && (descriptor.writable == Some(true)
                    || length.is_some_and(|length| length != old_length)))
        {
            return Ok(false);
        }
        let reached = match length {
            Some(length) if length != old_length => self.resize_array(index, length)?,
            _ => true,
        };
        if descriptor.writable == Some(false)
            && let HeapEntry::Array {
                length_writable, ..
            } = &mut self.heap[index]
        {
            *length_writable = false;
        }
        Ok(reached)
    }

    /// Resizes with the heap accounting, and says whether `length` was reached.
    fn resize_array(&mut self, index: usize, length: usize) -> Result<bool, EvalFailure> {
        let old_length_and_bytes =
            |entry: &HeapEntry, shapes: &ShapeTable, atoms: &AtomTable| match entry {
                HeapEntry::Array {
                    elements,
                    properties,
                    ..
                } => (elements.len(), properties.charge_bytes(shapes, atoms)),
                _ => unreachable!("resize_array requires an array"),
            };
        let (old_length, old_property_bytes) =
            old_length_and_bytes(&self.heap[index], &self.shapes, &self.atoms);
        let growth = length
            .saturating_sub(old_length)
            .saturating_mul(std::mem::size_of::<Value>());
        self.charge_slot(index, growth)
            .map_err(EvalFailure::Runtime)?;
        let HeapEntry::Array {
            elements,
            properties,
            kind,
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("resize_array requires an array");
        };
        let reached = apply_array_length(
            kind,
            elements,
            properties,
            &self.atoms,
            length,
            &self.shapes,
        );
        let (new_length, new_property_bytes) =
            old_length_and_bytes(&self.heap[index], &self.shapes, &self.atoms);
        let released = old_length
            .saturating_sub(new_length)
            .saturating_mul(std::mem::size_of::<Value>())
            .saturating_add(old_property_bytes.saturating_sub(new_property_bytes));
        self.refund_slot(index, released);
        Ok(reached)
    }

    fn set_own_data(
        &mut self,
        index: usize,
        key: PropertyKey,
        value: Value,
    ) -> Result<(), EvalFailure> {
        if let PropertyKey::Named(name) = &key
            && let Some(typed_index) = typedarray::typed_array_index(self.atoms.resolve(*name))
            && matches!(self.heap[index], HeapEntry::TypedArray { .. })
        {
            let Some(offset) = typed_index else {
                return Ok(());
            };
            let view = self.value_for_runtime_index(index)?;
            typedarray::write_element(self, view, offset, value)?;
            return Ok(());
        }
        if self.is_array_length_key(index, &key) {
            let descriptor = crate::builtins::property_descriptor::PropertyDescriptor {
                value: Some(value),
                ..Default::default()
            };
            return if self.array_define_length(index, descriptor)? {
                Ok(())
            } else {
                Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set array length",
                }))
            };
        }
        if let HeapEntry::Array {
            elements,
            length_writable,
            ..
        } = &self.heap[index]
            && let Some(offset) = key.as_string(&self.atoms).and_then(array_index)
            && offset as usize >= elements.len()
            && !*length_writable
        {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "add index beyond non-writable array length",
            }));
        }
        let (properties, extensible, virtual_exists) = match &self.heap[index] {
            HeapEntry::Object {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Generator {
                properties,
                extensible,
                ..
            }
            | HeapEntry::AsyncGenerator {
                properties,
                extensible,
                ..
            }
            | HeapEntry::AsyncFromSync {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Script {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Function {
                properties,
                extensible,
                ..
            }
            | HeapEntry::NativeFunction {
                properties,
                extensible,
                ..
            }
            | HeapEntry::RegExp {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Date {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Temporal {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Intl {
                properties,
                extensible,
                ..
            }
            | HeapEntry::BuiltinIterator {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Collection {
                properties,
                extensible,
                ..
            }
            | HeapEntry::TypedArray {
                properties,
                extensible,
                ..
            }
            | HeapEntry::ArrayBuffer {
                properties,
                extensible,
                ..
            }
            | HeapEntry::SharedArrayBuffer {
                properties,
                extensible,
                ..
            }
            | HeapEntry::DataView {
                properties,
                extensible,
                ..
            }
            | HeapEntry::Promise {
                properties,
                extensible,
                ..
            }
            | HeapEntry::WeakRef {
                properties,
                extensible,
                ..
            }
            | HeapEntry::FinalizationRegistry {
                properties,
                extensible,
                ..
            }
            | HeapEntry::DisposableStack {
                properties,
                extensible,
                ..
            }
            | HeapEntry::ProxyRevoker {
                properties,
                extensible,
                ..
            } => (Some(properties), *extensible, false),
            HeapEntry::Array {
                elements,
                properties,
                extensible,
                ..
            } => {
                let virtual_exists = key.as_string(&self.atoms).is_some_and(|name| {
                    name.eq_ascii("length")
                        || array_index(name).is_some_and(|offset| {
                            elements
                                .get(offset as usize)
                                .is_some_and(|element| *element != Value::HOLE)
                        })
                });
                (Some(properties), *extensible, virtual_exists)
            }
            _ => (None, true, false),
        };
        if let Some(property) = properties.and_then(|properties| properties.get(&self.shapes, &key))
        {
            match property {
                Property::Data {
                    writable: false, ..
                }
                | Property::Accessor { .. } => {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "assign to read only property",
                    }));
                }
                Property::Data { writable: true, .. } => {}
            }
        } else if !extensible && !virtual_exists {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "add property to non-extensible object",
            }));
        }

        let growth = match &self.heap[index] {
            HeapEntry::Object { properties, .. }
            | HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::TypedArray { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::ProxyRevoker { properties, .. }
            | HeapEntry::Timeout { properties, .. } => {
                usize::from(!properties.contains_key(&self.shapes, &key))
                    * key.charge_bytes(&self.atoms)
            }
            HeapEntry::Array {
                elements,
                properties,
                ..
            } => match &key {
                PropertyKey::Named(name) if self.atoms.eq_ascii(*name, "length") => 0,
                PropertyKey::Named(name) => {
                    if let Some(offset) = self.atoms.array_index(*name) {
                        (offset as usize + 1)
                            .saturating_sub(elements.len())
                            .saturating_mul(std::mem::size_of::<Value>())
                    } else {
                        usize::from(!properties.contains_key(&self.shapes, &key))
                            * key.charge_bytes(&self.atoms)
                    }
                }
                PropertyKey::Symbol(_) | PropertyKey::Private(_) => {
                    usize::from(!properties.contains_key(&self.shapes, &key))
                        * key.charge_bytes(&self.atoms)
                }
            },
            HeapEntry::Proxy { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set property on proxy",
                }));
            }
            HeapEntry::String(_) | HeapEntry::Rope { .. } | HeapEntry::BigInt(_) => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set property on primitive",
                }));
            }
            HeapEntry::Symbol { .. }
            | HeapEntry::PrivateName { .. }
            | HeapEntry::Iterator { .. }
            | HeapEntry::PromiseResolver { .. }
            | HeapEntry::PromiseAll { .. }
            | HeapEntry::AsyncActivation { .. }
            | HeapEntry::PromiseAllElement { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set property on non-object",
                }));
            }
            HeapEntry::ProcessEnv { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set internal process environment",
                }));
            }
            HeapEntry::ModuleNamespace { .. } | HeapEntry::ExternalModuleNamespace { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "assign to module namespace",
                }));
            }
            HeapEntry::HashState { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "assign to hash state",
                }));
            }
            HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
        };
        self.charge_slot(index, growth)
            .map_err(EvalFailure::Runtime)?;
        let direct_store = match &mut self.heap[index] {
            HeapEntry::Object { properties, .. }
            | HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::TypedArray { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::ProxyRevoker { properties, .. }
            | HeapEntry::Timeout { properties, .. } => {
                let descriptor = match properties.get(&self.shapes, &key) {
                    Some(Property::Data {
                        writable,
                        enumerable,
                        configurable,
                        ..
                    }) => Property::Data {
                        value,
                        writable: *writable,
                        enumerable: *enumerable,
                        configurable: *configurable,
                    },
                    _ => Property::Data {
                        value,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                };
                properties.insert(&mut self.shapes, key, descriptor);
                None
            }
            HeapEntry::Array {
                elements,
                properties,
                kind,
                length_writable,
                ..
            } => {
                let mut direct_store = None;
                match key {
                    PropertyKey::Named(name) => {
                        if let Some(offset) = self.atoms.array_index(name) {
                            let offset = offset as usize;
                            if elements.len() < offset {
                                array_set_length(
                                    ArrayVector { kind, elements },
                                    properties,
                                    &self.atoms,
                                    *length_writable,
                                    number_value((offset + 1) as f64),
                                    "set array index",
                                    &self.shapes,
                                )?;
                            }
                            let key = PropertyKey::Named(name);
                            if let Some(Property::Data { value: stored, .. }) =
                                properties.get_mut(&self.shapes, &key)
                            {
                                *stored = value;
                            } else {
                                direct_store = Some(offset);
                            }
                        } else {
                            let key = PropertyKey::Named(name);
                            let descriptor = match properties.get(&self.shapes, &key) {
                                Some(Property::Data {
                                    writable,
                                    enumerable,
                                    configurable,
                                    ..
                                }) => Property::Data {
                                    value,
                                    writable: *writable,
                                    enumerable: *enumerable,
                                    configurable: *configurable,
                                },
                                _ => Property::Data {
                                    value,
                                    writable: true,
                                    enumerable: true,
                                    configurable: true,
                                },
                            };
                            properties.insert(&mut self.shapes, key, descriptor);
                        }
                    }
                    identity @ (PropertyKey::Symbol(_) | PropertyKey::Private(_)) => {
                        let descriptor = match properties.get(&self.shapes, &identity) {
                            Some(Property::Data {
                                writable,
                                enumerable,
                                configurable,
                                ..
                            }) => Property::Data {
                                value,
                                writable: *writable,
                                enumerable: *enumerable,
                                configurable: *configurable,
                            },
                            _ => Property::Data {
                                value,
                                writable: true,
                                enumerable: true,
                                configurable: true,
                            },
                        };
                        properties.insert(&mut self.shapes, identity, descriptor);
                    }
                }
                direct_store
            }
            HeapEntry::ProcessEnv { .. } => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set internal process environment",
                }));
            }
            _ => unreachable!("primitive and identity entries rejected above"),
        };
        if let Some(offset) = direct_store {
            self.store_element(index, offset, value);
        }
        Ok(())
    }

    fn define_accessor(
        &mut self,
        object: Value,
        key: PropertyKey,
        accessor: Value,
        kind: AccessorKind,
    ) -> Result<(), EvalFailure> {
        match self.runtime_slot(object).map_err(EvalFailure::Runtime)? {
            Some(index) => {
                if let PropertyKey::Named(name) = &key
                    && typedarray::typed_array_index(self.atoms.resolve(*name)).is_some()
                    && matches!(self.heap[index], HeapEntry::TypedArray { .. })
                {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "define accessor on typed array index",
                    }));
                }
                let growth = match &self.heap[index] {
                    HeapEntry::Object {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Generator {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::AsyncGenerator {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::AsyncFromSync {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Script {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Array {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Function {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::NativeFunction {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::RegExp {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Date {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Temporal {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Intl {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::BuiltinIterator {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Collection {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::TypedArray {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::ArrayBuffer {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::SharedArrayBuffer {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::DataView {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::Promise {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::WeakRef {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::FinalizationRegistry {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::DisposableStack {
                        properties,
                        extensible,
                        ..
                    }
                    | HeapEntry::ProxyRevoker {
                        properties,
                        extensible,
                        ..
                    } => {
                        let existing = properties.get(&self.shapes, &key);
                        if existing.is_some_and(|property| !property.configurable())
                            || (existing.is_none() && !extensible)
                        {
                            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "define accessor on non-configurable object",
                            }));
                        }
                        match existing {
                            None => key
                                .charge_bytes(&self.atoms)
                                .saturating_add(std::mem::size_of::<Value>()),
                            Some(Property::Data { .. }) => std::mem::size_of::<Value>(),
                            Some(Property::Accessor { .. }) => 0,
                        }
                    }
                    _ => {
                        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "define accessor on primitive",
                        }));
                    }
                };
                self.charge_slot(index, growth)
                    .map_err(EvalFailure::Runtime)?;
                let properties = match &mut self.heap[index] {
                    HeapEntry::Object { properties, .. }
                    | HeapEntry::Generator { properties, .. }
                    | HeapEntry::AsyncGenerator { properties, .. }
                    | HeapEntry::AsyncFromSync { properties, .. }
                    | HeapEntry::Script { properties, .. }
                    | HeapEntry::Array { properties, .. }
                    | HeapEntry::Function { properties, .. }
                    | HeapEntry::NativeFunction { properties, .. }
                    | HeapEntry::RegExp { properties, .. }
                    | HeapEntry::Date { properties, .. }
                    | HeapEntry::Temporal { properties, .. }
                    | HeapEntry::Intl { properties, .. }
                    | HeapEntry::BuiltinIterator { properties, .. }
                    | HeapEntry::Collection { properties, .. }
                    | HeapEntry::TypedArray { properties, .. }
                    | HeapEntry::ArrayBuffer { properties, .. }
                    | HeapEntry::SharedArrayBuffer { properties, .. }
                    | HeapEntry::DataView { properties, .. }
                    | HeapEntry::Promise { properties, .. }
                    | HeapEntry::WeakRef { properties, .. }
                    | HeapEntry::FinalizationRegistry { properties, .. }
                    | HeapEntry::ProxyRevoker { properties, .. }
                    | HeapEntry::DisposableStack { properties, .. } => properties,
                    _ => unreachable!("validated object cannot change heap entry kind"),
                };
                match properties.get_mut(&self.shapes, &key) {
                    Some(Property::Accessor { getter, setter, .. }) => {
                        if kind.is_getter() {
                            *getter = Some(accessor);
                        } else {
                            *setter = Some(accessor);
                        }
                    }
                    Some(Property::Data { .. }) | None => {
                        let (getter, setter) = if kind.is_getter() {
                            (Some(accessor), None)
                        } else {
                            (None, Some(accessor))
                        };
                        properties.insert(
                            &mut self.shapes,
                            key,
                            Property::Accessor {
                                getter,
                                setter,
                                enumerable: kind.is_enumerable(),
                                configurable: true,
                            },
                        );
                    }
                }
                Ok(())
            }
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "define accessor on host object",
            })),
        }
    }

    pub(crate) fn internal_delete(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<bool, EvalFailure> {
        if !matches!(key, PropertyKey::Private(_)) && self.heap_entry_is_proxy_value(object) {
            return self.with_proxy_dispatch(|machine| {
                crate::builtins::proxy::delete(machine, object, key)
            });
        }
        match self.runtime_slot(object).map_err(EvalFailure::Runtime)? {
            Some(index) => {
                let boxed = self.boxed_string(index);
                if boxed.is_some_and(|text| string_own_get(&text, &self.atoms, key).is_some()) {
                    return Ok(false);
                }
                self.reify_function_properties(index)?;
                if let PropertyKey::Named(name) = key
                    && let Some(typed_index) =
                        typedarray::typed_array_index(self.atoms.resolve(*name))
                    && matches!(self.heap[index], HeapEntry::TypedArray { .. })
                {
                    let view = self.value_for_runtime_index(index)?;
                    let bounds = typedarray::typed_array_bounds(self, view)?;
                    return Ok(typed_index.is_none_or(|offset| {
                        bounds.out_of_bounds || offset >= bounds.element_length
                    }));
                }
                let (released, hole_store) = match &mut self.heap[index] {
                    HeapEntry::Object { properties, .. }
                    | HeapEntry::Generator { properties, .. }
                    | HeapEntry::AsyncGenerator { properties, .. }
                    | HeapEntry::AsyncFromSync { properties, .. }
                    | HeapEntry::Script { properties, .. }
                    | HeapEntry::Function { properties, .. }
                    | HeapEntry::NativeFunction { properties, .. }
                    | HeapEntry::RegExp { properties, .. }
                    | HeapEntry::Date { properties, .. }
                    | HeapEntry::Temporal { properties, .. }
                    | HeapEntry::Intl { properties, .. }
                    | HeapEntry::BuiltinIterator { properties, .. }
                    | HeapEntry::Collection { properties, .. }
                    | HeapEntry::TypedArray { properties, .. }
                    | HeapEntry::ArrayBuffer { properties, .. }
                    | HeapEntry::SharedArrayBuffer { properties, .. }
                    | HeapEntry::DataView { properties, .. }
                    | HeapEntry::Promise { properties, .. }
                    | HeapEntry::WeakRef { properties, .. }
                    | HeapEntry::FinalizationRegistry { properties, .. }
                    | HeapEntry::DisposableStack { properties, .. }
                    | HeapEntry::ProxyRevoker { properties, .. }
                    | HeapEntry::Timeout { properties, .. } => {
                        let Some(property) = properties.get(&self.shapes, key) else {
                            return Ok(true);
                        };
                        if !property.configurable() {
                            return Ok(false);
                        }
                        let released = key
                            .charge_bytes(&self.atoms)
                            .saturating_add(property.charge_bytes());
                        properties.remove(&self.shapes, key);
                        (released, None)
                    }
                    HeapEntry::Proxy { .. } => (0, None),
                    HeapEntry::Array {
                        elements,
                        properties,
                        ..
                    } => {
                        if let Some(property) = properties.get(&self.shapes, key) {
                            if !property.configurable() {
                                return Ok(false);
                            }
                            let released = key
                                .charge_bytes(&self.atoms)
                                .saturating_add(property.charge_bytes());
                            properties.remove(&self.shapes, key);
                            (released, None)
                        } else {
                            let mut hole_store = None;
                            if let PropertyKey::Named(name) = key {
                                if self.atoms.eq_ascii(*name, "length") {
                                    return Ok(false);
                                }
                                if let Some(offset) = self.atoms.array_index(*name)
                                    && elements.get(offset as usize).is_some()
                                {
                                    hole_store = Some(offset as usize);
                                }
                            }
                            (0, hole_store)
                        }
                    }
                    // An environment variable is always configurable, so this
                    // succeeds whether or not the variable was set, as in Node.
                    HeapEntry::ProcessEnv { .. } => {
                        if let PropertyKey::Named(name) = key
                            && let Some(name) = self.atoms.utf8(*name)
                        {
                            self.host.delete_env(name);
                        }
                        return Ok(true);
                    }
                    HeapEntry::String(_)
                    | HeapEntry::Rope { .. }
                    | HeapEntry::BigInt(_)
                    | HeapEntry::Symbol { .. }
                    | HeapEntry::PrivateName { .. }
                    | HeapEntry::Iterator { .. }
                    | HeapEntry::PromiseResolver { .. }
                    | HeapEntry::PromiseAll { .. }
                    | HeapEntry::AsyncActivation { .. }
                    | HeapEntry::PromiseAllElement { .. }
                    | HeapEntry::HashState { .. } => return Ok(true),
                    HeapEntry::ModuleNamespace { .. }
                    | HeapEntry::ExternalModuleNamespace { .. } => return Ok(false),
                    HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
                };
                if let Some(offset) = hole_store {
                    self.store_element(index, offset, Value::HOLE);
                }
                self.refund_slot(index, released);
                Ok(true)
            }
            None => Ok(true),
        }
    }

    pub(crate) fn internal_has_property(
        &mut self,
        object: Value,
        key: &PropertyKey,
    ) -> Result<bool, EvalFailure> {
        match self.runtime_slot(object).map_err(EvalFailure::Runtime)? {
            Some(index) => {
                if !matches!(key, PropertyKey::Private(_))
                    && matches!(self.heap[index], HeapEntry::Proxy { .. })
                {
                    return self.with_proxy_dispatch(|machine| {
                        crate::builtins::proxy::has_property(machine, object, key)
                    });
                }
                if matches!(self.heap[index], HeapEntry::ProcessEnv { .. }) {
                    let PropertyKey::Named(name) = key else {
                        return Ok(false);
                    };
                    return Ok(self
                        .atoms
                        .utf8(*name)
                        .is_some_and(|name| self.host.env(name).is_some()));
                }
                if matches!(key, PropertyKey::Private(_)) {
                    return Ok(self.own_get(index, key).is_some());
                }
                let mut node = index;
                let mut guard = 0;
                loop {
                    if matches!(self.heap[node], HeapEntry::Proxy { .. }) {
                        return self
                            .internal_has_property(self.value_for_runtime_index(node)?, key);
                    }
                    if self.own_get(node, key).is_some() {
                        return Ok(true);
                    }
                    match self.prototype_index(node)? {
                        Some(next) => {
                            node = next;
                            guard += 1;
                            if guard > self.heap.len() + 1 {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false),
                    }
                }
            }
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "in",
            })),
        }
    }

    // ---- aggregates & prototypes ------------------------------------------

    pub(crate) fn array_push(&mut self, array: Value, value: Value) -> Result<(), EvalFailure> {
        match self.runtime_slot(array).map_err(EvalFailure::Runtime)? {
            Some(index) => {
                let (offset, extensible, length_writable) = match &self.heap[index] {
                    HeapEntry::Array {
                        elements,
                        extensible,
                        length_writable,
                        ..
                    } => (elements.len(), *extensible, *length_writable),
                    _ => {
                        return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "push on non-array",
                        }));
                    }
                };
                if !length_writable {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "push beyond non-writable array length",
                    }));
                }
                if !extensible {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "add property to non-extensible object",
                    }));
                }
                if offset >= u32::MAX as usize {
                    return Err(EvalFailure::Throw(ThrowOrigin::RangeError {
                        operation: "push beyond maximum array length",
                    }));
                }
                self.charge_slot(index, std::mem::size_of::<Value>())
                    .map_err(EvalFailure::Runtime)?;
                self.store_element(index, offset, value);
                Ok(())
            }
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "push on non-array",
            })),
        }
    }

    fn array_extend(&mut self, array: Value, iterable: Value) -> Result<(), EvalFailure> {
        self.with_temporaries(|machine| {
            let iterator = machine.create_iterator(iterable, IteratorKind::Sync)?;
            loop {
                let (done, value) = machine.iterator_next(iterator)?;
                if done {
                    return Ok(());
                }
                machine.array_push(array, value)?;
            }
        })
    }

    fn object_spread(&mut self, target: Value, source: Value) -> Result<(), EvalFailure> {
        self.with_temporaries(|machine| machine.spread_properties(target, source))
    }

    fn spread_properties(&mut self, target: Value, source: Value) -> Result<(), EvalFailure> {
        let target_index = match self.runtime_slot(target).map_err(EvalFailure::Runtime)? {
            Some(index)
                if matches!(
                    self.heap[index],
                    HeapEntry::Object { .. }
                        | HeapEntry::Generator { .. }
                        | HeapEntry::AsyncGenerator { .. }
                        | HeapEntry::Script { .. }
                        | HeapEntry::Array { .. }
                        | HeapEntry::Promise { .. }
                ) =>
            {
                index
            }
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "object spread target is not an object",
                }));
            }
        };
        let keys = self.internal_own_property_keys(source)?;
        for key in keys {
            if !self.own_property_is_enumerable(source, &key)? {
                continue;
            }
            let value = self.get_property_key(source, &key)?;
            self.set_own_data(target_index, key, value)?;
        }
        Ok(())
    }

    pub(crate) fn copy_data_properties(
        &mut self,
        target: Value,
        source: Value,
        excluded: Value,
    ) -> Result<(), EvalFailure> {
        if !self.is_object(target) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "object rest target is not an object",
            }));
        }
        let excluded_keys = self.excluded_property_keys(excluded)?;
        for key in self.internal_own_property_keys(source)? {
            if excluded_keys.contains(&key) {
                continue;
            }
            if !self.own_property_is_enumerable(source, &key)? {
                continue;
            }
            let value = self.get_property_key(source, &key)?;
            // CreateDataPropertyOrThrow: [[DefineOwnProperty]] with a full
            // data descriptor; a proxy target observes the defineProperty
            // trap and a false is fatal.
            if !self.internal_define_own_property(
                target,
                key,
                crate::builtins::property_descriptor::PropertyDescriptor {
                    value: Some(value),
                    writable: Some(true),
                    enumerable: Some(true),
                    configurable: Some(true),
                    ..Default::default()
                },
            )? {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "cannot create property on non-extensible target",
                }));
            }
        }
        Ok(())
    }

    fn excluded_property_keys(&mut self, excluded: Value) -> Result<Vec<PropertyKey>, EvalFailure> {
        let Some(index) = self.runtime_slot(excluded).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "object rest excluded keys is not an array",
            }));
        };
        let HeapEntry::Array { elements, .. } = &self.heap[index] else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "object rest excluded keys is not an array",
            }));
        };
        let elements = elements.clone();
        let mut keys = Vec::with_capacity(elements.len());
        for element in elements {
            if element != Value::HOLE {
                keys.push(self.property_key_from_value(element)?);
            }
        }
        Ok(keys)
    }

    pub(crate) fn template_object(
        &mut self,
        cooked: Value,
        raw: Value,
    ) -> Result<Value, EvalFailure> {
        let site = {
            let frame = self
                .frames
                .last()
                .expect("template object executes inside a frame");
            (frame.module.get(), frame.function as u32, frame.pc as u32)
        };
        self.template_object_at(site, cooked, raw)
    }

    pub(crate) fn template_object_at(
        &mut self,
        site: (u32, u32, u32),
        cooked: Value,
        raw: Value,
    ) -> Result<Value, EvalFailure> {
        let cache_index = self
            .runtime_slot(self.template_objects)
            .map_err(EvalFailure::Runtime)?
            .expect("template object cache is an engine array");
        if let Some(offset) = self.template_sites.get(&site) {
            let HeapEntry::Array { elements, .. } = &self.heap[cache_index] else {
                unreachable!("template object cache is an engine array");
            };
            return Ok(elements[*offset]);
        }
        for array in [cooked, raw] {
            let Some(index) = self.runtime_slot(array).map_err(EvalFailure::Runtime)? else {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "template strings is not an array",
                }));
            };
            if !matches!(self.heap[index], HeapEntry::Array { .. }) {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "template strings is not an array",
                }));
            }
        }
        let raw_key = PropertyKey::Named(self.intern_str("raw"));
        self.define_descriptor(
            cooked,
            raw_key,
            Property::Data {
                value: raw,
                writable: false,
                enumerable: false,
                configurable: false,
            },
        )?;
        self.freeze_template_array(raw)?;
        self.freeze_template_array(cooked)?;
        let HeapEntry::Array { elements, .. } = &self.heap[cache_index] else {
            unreachable!("template object cache is an engine array");
        };
        let offset = elements.len();
        self.array_push(self.template_objects, cooked)?;
        self.template_sites.insert(site, offset);
        Ok(cooked)
    }

    fn freeze_template_array(&mut self, array: Value) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(array)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "template strings is not an array",
            }))?;
        let HeapEntry::Array {
            properties,
            extensible,
            length_writable,
            ..
        } = &mut self.heap[index]
        else {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "template strings is not an array",
            }));
        };
        *extensible = false;
        *length_writable = false;
        properties.for_each_property_mut(|property| match property {
            Property::Data {
                writable,
                configurable,
                ..
            } => {
                *writable = false;
                *configurable = false;
            }
            Property::Accessor { configurable, .. } => *configurable = false,
        });
        Ok(())
    }

    fn set_prototype(&mut self, object: Value, prototype: Value) -> Result<(), EvalFailure> {
        let prototype = match self.runtime_slot(prototype).map_err(EvalFailure::Runtime)? {
            Some(_) => Some(prototype),
            None => match prototype.decode() {
                Some(Decoded::Null) => None,
                Some(Decoded::HeapRef(_)) => Some(prototype),
                _ => {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "set prototype to non-object",
                    }));
                }
            },
        };
        match self.runtime_slot(object).map_err(EvalFailure::Runtime)? {
            Some(index) => match &mut self.heap[index] {
                HeapEntry::Object {
                    prototype: slot, ..
                }
                | HeapEntry::Generator {
                    prototype: slot, ..
                }
                | HeapEntry::AsyncGenerator {
                    prototype: slot, ..
                }
                | HeapEntry::Script {
                    prototype: slot, ..
                }
                | HeapEntry::Array {
                    prototype: slot, ..
                }
                | HeapEntry::Function {
                    prototype: slot, ..
                }
                | HeapEntry::RegExp {
                    prototype: slot, ..
                }
                | HeapEntry::Date {
                    prototype: slot, ..
                }
                | HeapEntry::Temporal {
                    prototype: slot, ..
                }
                | HeapEntry::Intl {
                    prototype: slot, ..
                }
                | HeapEntry::BuiltinIterator {
                    prototype: slot, ..
                }
                | HeapEntry::Collection {
                    prototype: slot, ..
                }
                | HeapEntry::TypedArray {
                    prototype: slot, ..
                }
                | HeapEntry::ArrayBuffer {
                    prototype: slot, ..
                }
                | HeapEntry::SharedArrayBuffer {
                    prototype: slot, ..
                }
                | HeapEntry::DataView {
                    prototype: slot, ..
                }
                | HeapEntry::Promise {
                    prototype: slot, ..
                }
                | HeapEntry::WeakRef {
                    prototype: slot, ..
                }
                | HeapEntry::FinalizationRegistry {
                    prototype: slot, ..
                }
                | HeapEntry::DisposableStack {
                    prototype: slot, ..
                }
                | HeapEntry::ProcessEnv {
                    prototype: slot, ..
                }
                | HeapEntry::Timeout {
                    prototype: slot, ..
                }
                | HeapEntry::NativeFunction {
                    prototype: slot, ..
                } => {
                    *slot = prototype;
                    Ok(())
                }
                _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "set prototype on primitive",
                })),
            },
            None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "set prototype on host object",
            })),
        }
    }

    /// Calls a generator function. When its parameters can run code, the
    /// compiler ended its prologue with a `Suspend`, and running to that point
    /// now lets a throw from a parameter reach the caller.
    pub(crate) fn start_generator(
        &mut self,
        start: GeneratorStart,
        flags: bamts_bytecode::FunctionFlags,
    ) -> Result<Value, EvalFailure> {
        if flags.is_async {
            let generator = self
                .create_async_generator(start)
                .map_err(EvalFailure::Runtime)?;
            if flags.binds_at_call {
                self.run_async_generator_prologue(generator)?;
            }
            return Ok(generator);
        }
        let generator = self.create_generator(start).map_err(EvalFailure::Runtime)?;
        if flags.binds_at_call {
            self.resume_generator(generator, GeneratorCompletion::Normal(Value::UNDEFINED))?;
        }
        Ok(generator)
    }

    /// Runs an async generator to the `Suspend` that ends its prologue. No
    /// request is queued yet, so the stop settles nothing; the first request
    /// resumes it the way any later one resumes a `yield`.
    fn run_async_generator_prologue(&mut self, generator: Value) -> Result<(), EvalFailure> {
        let AsyncGeneratorState::SuspendedStart(start) =
            self.take_async_generator_state(generator)?
        else {
            unreachable!("a new async generator is suspended at its start")
        };
        let stop_depth = self.frames.len();
        let return_to = self.frames.last().map(|frame| ReturnTo {
            destination: None,
            call_pc: frame.pc,
            constructed: None,
        });
        let pushed = self
            .push_frame(ActivationRequest {
                target: start.target,
                captures: &start.captures,
                context: start.context,
                this_value: start.this_value,
                new_target: start.new_target,
                arguments: &start.args,
                return_to,
            })
            .map_err(|error| EvalFailure::Runtime(error.kind));
        let step = pushed.and_then(|()| self.drive_async_generator_activation(stop_depth, None));
        match step {
            Ok(AsyncGeneratorStep::Yield { activation, .. }) => self
                .replace_async_generator_state(
                    generator,
                    AsyncGeneratorState::SuspendedYield(activation),
                )
                .map_err(EvalFailure::Runtime),
            Ok(AsyncGeneratorStep::Throw { value, origin }) => {
                self.complete_async_generator(generator)?;
                Err(EvalFailure::ThrowValueOrigin { value, origin })
            }
            Ok(AsyncGeneratorStep::Await { .. } | AsyncGeneratorStep::Return(_)) => {
                unreachable!("parameters cannot await, and the prologue ends at a Suspend")
            }
            Err(failure) => {
                self.complete_async_generator(generator)?;
                Err(failure)
            }
        }
    }

    pub(crate) fn create_generator(
        &mut self,
        start: GeneratorStart,
    ) -> Result<Value, RuntimeErrorKind> {
        self.allocate(HeapEntry::Generator {
            state: GeneratorState::SuspendedStart(start),
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.builtins.generator_prototype()),
            extensible: true,
        })
    }

    fn resume_generator(
        &mut self,
        generator: Value,
        completion: GeneratorCompletion,
    ) -> Result<Value, EvalFailure> {
        if self.stack_overflows() {
            return Err(EvalFailure::Throw(STACK_OVERFLOW));
        }
        let operation =
            crate::vm::generator_async::prepare_generator_operation(self, generator, completion)?;
        let stop_depth = self.frames.len();
        let return_to = self.frames.last().map(|frame| ReturnTo {
            destination: None,
            call_pc: frame.pc,
            constructed: None,
        });
        let prepared = match operation {
            crate::vm::generator_async::PreparedGeneratorOperation::Start { start, .. } => self
                .push_frame(ActivationRequest {
                    target: start.target,
                    captures: &start.captures,
                    context: start.context,
                    this_value: start.this_value,
                    new_target: start.new_target,
                    arguments: &start.args,
                    return_to,
                })
                .map_err(|error| EvalFailure::Runtime(error.kind)),
            crate::vm::generator_async::PreparedGeneratorOperation::Resume {
                activation,
                completion,
            } => self.push_resumed_generator_frame(activation, completion, return_to),
            crate::vm::generator_async::PreparedGeneratorOperation::Complete(value) => {
                return self.iterator_result(value, true);
            }
            crate::vm::generator_async::PreparedGeneratorOperation::Raise { value, origin } => {
                return Err(EvalFailure::ThrowValueOrigin { value, origin });
            }
        };
        if let Err(failure) = prepared {
            self.settle_generator_completed(generator)?;
            return Err(failure);
        }
        let resumed = self.run_generator_activation(stop_depth)?;
        match resumed {
            GeneratorResume::Yield { value, activation } => {
                self.settle_generator_yield(generator, value, activation)
            }
            GeneratorResume::Return(value) => {
                self.settle_generator_completed(generator)?;
                self.iterator_result(value, true)
            }
            GeneratorResume::Throw { value, origin } => {
                self.settle_generator_completed(generator)?;
                Err(EvalFailure::ThrowValueOrigin { value, origin })
            }
        }
    }

    fn push_resumed_generator_frame(
        &mut self,
        activation: SuspendedActivation,
        completion: GeneratorCompletion,
        return_to: Option<ReturnTo>,
    ) -> Result<(), EvalFailure> {
        if self.call_depth_exhausted() {
            self.release_suspended_activation_registers(activation.registers.len());
            return Err(EvalFailure::Runtime(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            }));
        }
        let suspend_pc = activation
            .resume_token
            .checked_sub(1)
            .expect("suspended generator token is nonzero") as usize;
        let instruction = self.module_code(activation.target.module).functions()
            [activation.target.function.get() as usize]
            .code()[suspend_pc];
        let (dst, resume, mode) = match instruction {
            Instruction::Suspend {
                dst,
                src: _,
                resume,
                mode,
            } => (dst, resume, Some(mode)),
            Instruction::Await {
                dst,
                src: _,
                resume,
            } => (dst, resume, None),
            _ => unreachable!("generator resume token names a suspension instruction"),
        };
        let mut frame = Frame {
            module: activation.target.module,
            function: activation.target.function.get() as usize,
            pc: resume.get() as usize,
            registers: activation.registers,
            return_to,
            this_value: activation.this_value,
            new_target: activation.new_target,
            args: activation.args,
            arguments_object: activation.arguments_object,
            context: activation.context,
            outer_context: None,
        };
        frame.registers[dst.get() as usize] = completion.value();
        if let Some(mode) = mode {
            frame.registers[mode.get() as usize] = Value::int32(completion.mode());
        }
        frame.outer_context = std::mem::replace(&mut self.context_global, frame.context);
        self.frames.push(frame);
        Ok(())
    }

    fn run_generator_activation(
        &mut self,
        stop_depth: usize,
    ) -> Result<GeneratorResume, EvalFailure> {
        self.last_completion = None;
        self.pending_generator_resume = None;
        self.callback_boundaries.push(stop_depth);
        self.generator_boundaries.push(stop_depth);
        let result = self.run_loop(stop_depth);
        self.generator_boundaries
            .pop()
            .expect("generator execution owns its suspend boundary");
        self.callback_boundaries
            .pop()
            .expect("generator execution owns its unwind boundary");

        match result {
            Ok(Some(execution)) => Ok(GeneratorResume::Return(execution.value)),
            Ok(None) => {
                if let Some(resume) = self.pending_generator_resume.take() {
                    return Ok(resume);
                }
                let value = self.last_completion.take().unwrap_or(Value::UNDEFINED);
                Ok(GeneratorResume::Return(value))
            }
            Err(error) => {
                self.unwind_frames_to(stop_depth);
                match error.kind {
                    RuntimeErrorKind::UncaughtThrow { value, origin, .. } => {
                        Ok(GeneratorResume::Throw { value, origin })
                    }
                    kind => Err(EvalFailure::Runtime(kind)),
                }
            }
        }
    }

    pub(crate) fn settle_generator_yield(
        &mut self,
        generator: Value,
        value: Value,
        activation: SuspendedActivation,
    ) -> Result<Value, EvalFailure> {
        let register_count = activation.registers.len();
        let result = match self.iterator_result(value, false) {
            Ok(result) => result,
            Err(failure) => {
                self.release_suspended_activation_registers(register_count);
                self.replace_executing_generator(generator, GeneratorState::Completed)?;
                return Err(failure);
            }
        };
        if let Err(failure) =
            self.replace_executing_generator(generator, GeneratorState::Suspended(activation))
        {
            self.release_suspended_activation_registers(register_count);
            return Err(failure);
        }
        Ok(result)
    }

    pub(crate) fn settle_generator_completed(
        &mut self,
        generator: Value,
    ) -> Result<(), EvalFailure> {
        self.replace_executing_generator(generator, GeneratorState::Completed)
    }

    fn replace_executing_generator(
        &mut self,
        generator: Value,
        next: GeneratorState,
    ) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        let HeapEntry::Generator { state, .. } = &mut self.heap[index] else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        if !matches!(state, GeneratorState::Executing) {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        }
        *state = next;
        Ok(())
    }

    /// Starts an ordinary async function: creates the implicit result Promise,
    /// drives the body synchronously to its first `await` or completion under a
    /// detached suspend boundary, and returns the Promise. A `return` resolves
    /// it and an escaping throw rejects it; a runtime limit failure stays fatal.
    pub(crate) fn start_async_call(
        &mut self,
        target: RuntimeFunction,
        captures: &[Value],
        context: Option<Value>,
        this_value: Value,
        new_target: Value,
        arguments: &[Value],
    ) -> Result<Value, EvalFailure> {
        let promise = self.create_promise()?;
        let record = self.create_async_activation(promise, None)?;
        let stop_depth = self.frames.len();
        let return_to = self.frames.last().map(|frame| ReturnTo {
            destination: None,
            call_pc: frame.pc,
            constructed: None,
        });
        self.push_frame(ActivationRequest {
            target,
            captures,
            context,
            this_value,
            new_target,
            arguments,
            return_to,
        })
        .map_err(|error| EvalFailure::Runtime(error.kind))?;
        self.drive_and_settle_async(record, promise, stop_depth, None)?;
        Ok(promise)
    }

    /// Runs one async step and settles it. The result Promise, the activation
    /// record and the step's value live in Rust locals across code that can
    /// collect, so they stay rooted until the step is settled.
    fn drive_and_settle_async(
        &mut self,
        record: Value,
        promise: Value,
        stop_depth: usize,
        inject: Option<(Value, ThrowOrigin, usize)>,
    ) -> Result<(), EvalFailure> {
        self.with_native_roots(&[record, promise], |machine| {
            let step = machine.drive_async_activation(stop_depth, inject);
            machine.settle_async_step_keeping_value(record, promise, step)
        })
    }

    fn settle_async_step_rooted(
        &mut self,
        record: Value,
        promise: Value,
        step: Result<AsyncStep, EvalFailure>,
    ) -> Result<(), EvalFailure> {
        self.with_native_roots(&[record, promise], |machine| {
            machine.settle_async_step_keeping_value(record, promise, step)
        })
    }

    /// Settles inside the innermost native root frame, adding the step's value
    /// to it first.
    fn settle_async_step_keeping_value(
        &mut self,
        record: Value,
        promise: Value,
        step: Result<AsyncStep, EvalFailure>,
    ) -> Result<(), EvalFailure> {
        if let Some(value) = step.as_ref().ok().and_then(AsyncStep::held_value) {
            self.native_roots
                .last_mut()
                .expect("the caller pushed a native root frame")
                .push(value);
        }
        self.settle_async_step(record, promise, step)
    }

    /// Resumes a suspended async activation inside its Promise reaction job. On
    /// fulfillment the awaited value is written to `Suspend.dst`; on rejection
    /// the reason is thrown at the `Suspend` pc so a covering `try`/`catch`
    /// runs. The activation is one-shot; a second resume is a hard error.
    fn resume_async(
        &mut self,
        record: Value,
        value: Value,
        rejection: Option<ThrowOrigin>,
    ) -> Result<(), RuntimeErrorKind> {
        let promise = self.async_activation_promise(record)?;
        let module_entry = self.async_activation_module(record)?.is_some();
        let activation = self.take_async_activation(record)?;
        let register_count = activation.registers.len();
        if self.call_depth_exhausted() {
            self.release_suspended_activation_registers(register_count);
            return Err(RuntimeErrorKind::CallDepthExceeded {
                limit: self.limits.max_call_depth,
            });
        }
        let suspend_pc = activation
            .resume_token
            .checked_sub(1)
            .expect("suspended async token is nonzero") as usize;
        let instruction = self.module_code(activation.target.module).functions()
            [activation.target.function.get() as usize]
            .code()[suspend_pc];
        let (Instruction::Suspend { dst, resume, .. } | Instruction::Await { dst, resume, .. }) =
            instruction
        else {
            unreachable!("async resume token names a suspension instruction");
        };
        let stop_depth = self.frames.len();
        let return_to = if module_entry {
            None
        } else {
            self.frames.last().map(|frame| ReturnTo {
                destination: None,
                call_pc: frame.pc,
                constructed: None,
            })
        };
        let mut frame = Frame {
            module: activation.target.module,
            function: activation.target.function.get() as usize,
            pc: resume.get() as usize,
            registers: activation.registers,
            return_to,
            this_value: activation.this_value,
            new_target: activation.new_target,
            args: activation.args,
            arguments_object: activation.arguments_object,
            context: activation.context,
            outer_context: None,
        };
        let inject = match rejection {
            None => {
                frame.registers[dst.get() as usize] = value;
                None
            }
            Some(origin) => Some((value, origin, suspend_pc)),
        };
        frame.outer_context = std::mem::replace(&mut self.context_global, frame.context);
        self.frames.push(frame);
        match self.drive_and_settle_async(record, promise, stop_depth, inject) {
            Ok(()) => Ok(()),
            Err(EvalFailure::Runtime(kind)) => {
                // A fatal failure during a module entry's resume leaves the
                // module retryable instead of stuck in flight.
                if let Ok(Some(module)) = self.async_activation_module(record) {
                    self.abort_module_evaluation(module);
                }
                Err(kind)
            }
            Err(_) => Err(RuntimeErrorKind::InvalidValue { value: record }),
        }
    }

    /// Runs the interpreter loop for a detached async activation under one
    /// suspend and one unwind boundary, optionally injecting a rejection at the
    /// resumed `Suspend` pc first. It reports the awaited value on suspension,
    /// the returned value on completion, or an uncaught throw; runtime limit
    /// failures propagate as fatal `EvalFailure::Runtime`.
    fn drive_async_activation(
        &mut self,
        stop_depth: usize,
        inject: Option<(Value, ThrowOrigin, usize)>,
    ) -> Result<AsyncStep, EvalFailure> {
        self.last_completion = None;
        self.pending_async_suspend = None;
        self.callback_boundaries.push(stop_depth);
        self.async_boundaries.push(stop_depth);
        let result = match inject {
            None => self.run_loop(stop_depth),
            Some((value, origin, faulting_pc)) => match self.throw(value, origin, faulting_pc) {
                Ok(()) => self.run_loop(stop_depth),
                Err(error) => Err(error),
            },
        };
        self.async_boundaries
            .pop()
            .expect("async execution owns its suspend boundary");
        self.callback_boundaries
            .pop()
            .expect("async execution owns its unwind boundary");
        match result {
            Ok(Some(execution)) => Ok(AsyncStep::Return {
                value: execution.value,
                execution: Some(execution),
            }),
            Ok(None) => {
                if let Some((awaited, activation)) = self.pending_async_suspend.take() {
                    Ok(AsyncStep::Suspend {
                        awaited,
                        activation,
                    })
                } else {
                    Ok(AsyncStep::Return {
                        value: self.last_completion.take().unwrap_or(Value::UNDEFINED),
                        execution: None,
                    })
                }
            }
            Err(error) => {
                self.unwind_frames_to(stop_depth);
                match &error.kind {
                    RuntimeErrorKind::UncaughtThrow { .. } => Ok(AsyncStep::Throw(error)),
                    _ => Err(EvalFailure::Runtime(error.kind)),
                }
            }
        }
    }

    /// Settles the result Promise (or arms the next await) for one async step.
    fn settle_async_step(
        &mut self,
        record: Value,
        promise: Value,
        step: Result<AsyncStep, EvalFailure>,
    ) -> Result<(), EvalFailure> {
        match step {
            Ok(AsyncStep::Suspend {
                awaited,
                activation,
            }) => {
                let register_count = activation.registers.len();
                let result = self
                    .store_async_activation(record, activation)
                    .and_then(|()| self.await_promise(awaited, record));
                if result.is_err() {
                    let released = self
                        .take_async_activation(record)
                        .map_or(register_count, |stored| stored.registers.len());
                    self.release_suspended_activation_registers(released);
                }
                result
            }
            Ok(AsyncStep::Return { value, execution }) => {
                self.store_async_module_completion(record, execution.map(Ok))?;
                let module = self
                    .async_activation_module(record)
                    .map_err(EvalFailure::Runtime)?;
                let Some(module) = module else {
                    return self
                        .resolve_promise(promise, value)
                        .map_err(EvalFailure::Runtime);
                };
                // Module terminal settlement: the shared evaluation Promise
                // fulfills with the namespace (so every in-flight dynamic
                // importer unwraps it through `await`), and the module state
                // stores the success — exactly once, before any reaction
                // observing the settlement can run.
                let namespace = self
                    .module_namespace(module, module)
                    .map_err(|error| EvalFailure::Runtime(error.kind))?;
                self.fulfill_promise(promise, namespace)
                    .map_err(EvalFailure::Runtime)?;
                self.settle_module_evaluation(module, Ok(()));
                Ok(())
            }
            Ok(AsyncStep::Throw(error)) => {
                let RuntimeErrorKind::UncaughtThrow { value, origin, .. } = error.kind.clone()
                else {
                    unreachable!("async throws retain an uncaught-throw error");
                };
                self.store_async_module_completion(record, Some(Err(error.clone())))?;
                let module = self
                    .async_activation_module(record)
                    .map_err(EvalFailure::Runtime)?;
                if let Some(module) = module {
                    // The identical uncaught throw is cached as the module's
                    // stored failure and rejects the shared evaluation
                    // Promise once.
                    self.settle_module_evaluation(module, Err(error));
                }
                // Normalize through promise_rejection_value: engine-origin
                // Throw(origin) materializes once; ThrowValue /
                // ThrowValueOrigin keep their supplied values.
                let failure = if catch_value_needs_materialization(value, origin) {
                    EvalFailure::Throw(origin)
                } else if matches!(origin, ThrowOrigin::Bytecode) {
                    EvalFailure::ThrowValue(value)
                } else {
                    EvalFailure::ThrowValueOrigin { value, origin }
                };
                self.reject_promise_failure(promise, failure)
            }
            Err(failure) => Err(failure),
        }
    }

    /// Creates a lazy `async function*` object. Calling the function runs no
    /// body code; the first `.next()` starts the activation.
    pub(crate) fn create_async_generator(
        &mut self,
        start: GeneratorStart,
    ) -> Result<Value, RuntimeErrorKind> {
        self.allocate(HeapEntry::AsyncGenerator {
            state: AsyncGeneratorState::SuspendedStart(start),
            queue: VecDeque::new(),
            properties: PropertyMap::default(),
            prototype: Some(self.intrinsics.builtins.async_generator_prototype()),
            extensible: true,
        })
    }

    /// `%AsyncGeneratorPrototype%.next`: never throws synchronously. An
    /// incompatible receiver rejects the returned Promise; otherwise the
    /// request joins the FIFO and the front request drives the body when the
    /// generator is idle.
    pub(crate) fn enqueue_async_generator_request(
        &mut self,
        generator: Value,
        completion: GeneratorCompletion,
    ) -> Result<Value, EvalFailure> {
        if self.stack_overflows() {
            return Err(EvalFailure::Throw(STACK_OVERFLOW));
        }
        let capability = self.create_promise()?;
        let operation = completion.operation().async_receiver_error();
        let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)? else {
            self.reject_promise(
                capability,
                Value::UNDEFINED,
                ThrowOrigin::TypeError { operation },
            )
            .map_err(EvalFailure::Runtime)?;
            return Ok(capability);
        };
        let HeapEntry::AsyncGenerator { state, queue, .. } = &mut self.heap[index] else {
            self.reject_promise(
                capability,
                Value::UNDEFINED,
                ThrowOrigin::TypeError { operation },
            )
            .map_err(EvalFailure::Runtime)?;
            return Ok(capability);
        };
        queue.push_back(AsyncGeneratorRequest {
            completion,
            capability,
        });
        let should_drive = !matches!(
            crate::vm::async_iterators::async_generator_plan((&*state).into(), completion),
            crate::vm::async_iterators::AsyncGeneratorPlan::EnqueueOnly
        );
        if should_drive && let Err(failure) = self.drive_async_generator(generator) {
            let (reason, origin, fatal) = match failure {
                EvalFailure::Runtime(kind) => (Value::UNDEFINED, ThrowOrigin::Bytecode, Some(kind)),
                failure => {
                    let (reason, origin) = self.promise_rejection_value(failure)?;
                    (reason, origin, None)
                }
            };
            let request = self.pop_async_generator_front(generator)?;
            self.reject_promise(request.capability, reason, origin)
                .map_err(EvalFailure::Runtime)?;
            let drained = self.drive_async_generator(generator);
            if let Some(kind) = fatal {
                return Err(EvalFailure::Runtime(kind));
            }
            drained?;
        }
        Ok(capability)
    }

    /// Iteratively serves the request queue. At most one request drives the
    /// body at a time: a drive either parks the generator in `AwaitingOperand`
    /// or `AwaitingYield` (returning until a Promise reaction resumes it), or
    /// settles the front request and loops to serve the next one. A completed
    /// generator drains every queued request with `{value: undefined,
    /// done: true}`.
    pub(crate) fn drive_async_generator(&mut self, generator: Value) -> Result<(), EvalFailure> {
        loop {
            let plan = {
                let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)?
                else {
                    return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                        value: generator,
                    }));
                };
                let HeapEntry::AsyncGenerator { state, queue, .. } = &self.heap[index] else {
                    return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                        value: generator,
                    }));
                };
                let Some(request) = queue.front() else {
                    return Ok(());
                };
                crate::vm::async_iterators::async_generator_plan(state.into(), request.completion)
            };

            use crate::vm::async_iterators::AsyncGeneratorPlan;
            match plan {
                AsyncGeneratorPlan::EnqueueOnly => return Ok(()),
                AsyncGeneratorPlan::DrainNext => {
                    let request = self.pop_async_generator_front(generator)?;
                    let result = self.iterator_result(Value::UNDEFINED, true)?;
                    self.resolve_promise(request.capability, result)
                        .map_err(EvalFailure::Runtime)?;
                }
                AsyncGeneratorPlan::DrainThrow { value, origin } => {
                    let request = self.pop_async_generator_front(generator)?;
                    self.reject_promise(request.capability, value, origin)
                        .map_err(EvalFailure::Runtime)?;
                }
                AsyncGeneratorPlan::AwaitReturn(value) => {
                    self.take_async_generator_state(generator)?;
                    let result = self
                        .replace_async_generator_state(
                            generator,
                            AsyncGeneratorState::AwaitingReturn,
                        )
                        .map_err(EvalFailure::Runtime)
                        .and_then(|()| self.await_promise_for_generator(value, generator));
                    if result.is_err() {
                        self.complete_async_generator(generator)?;
                    }
                    return result;
                }
                AsyncGeneratorPlan::SettleThrow { value, origin } => {
                    self.take_async_generator_state(generator)?;
                    let request = self.pop_async_generator_front(generator)?;
                    self.complete_async_generator(generator)?;
                    self.reject_promise(request.capability, value, origin)
                        .map_err(EvalFailure::Runtime)?;
                }
                AsyncGeneratorPlan::StartDrive => {
                    let state = self.take_async_generator_state(generator)?;
                    let AsyncGeneratorState::SuspendedStart(start) = state else {
                        unreachable!("async generator plan selected a non-start state")
                    };
                    let stop_depth = self.frames.len();
                    let return_to = self.frames.last().map(|frame| ReturnTo {
                        destination: None,
                        call_pc: frame.pc,
                        constructed: None,
                    });
                    let pushed = self
                        .push_frame(ActivationRequest {
                            target: start.target,
                            captures: &start.captures,
                            context: start.context,
                            this_value: start.this_value,
                            new_target: start.new_target,
                            arguments: &start.args,
                            return_to,
                        })
                        .map_err(|error| EvalFailure::Runtime(error.kind));
                    let step = match pushed {
                        Ok(()) => self.drive_async_generator_activation(stop_depth, None),
                        Err(failure) => Err(failure),
                    };
                    self.settle_async_generator_step(generator, step)?;
                }
                AsyncGeneratorPlan::AwaitResumption(value) => {
                    let state = self.take_async_generator_state(generator)?;
                    let AsyncGeneratorState::SuspendedYield(activation) = state else {
                        unreachable!("async generator plan selected a non-yield state")
                    };
                    let register_count = activation.registers.len();
                    let result = self
                        .replace_async_generator_state(
                            generator,
                            AsyncGeneratorState::AwaitingResumption(activation),
                        )
                        .map_err(EvalFailure::Runtime)
                        .and_then(|()| self.await_promise_for_generator(value, generator));
                    if result.is_err() {
                        self.release_suspended_activation_registers(register_count);
                        self.complete_async_generator(generator)?;
                    }
                    return result;
                }
                AsyncGeneratorPlan::Drive(completion) => {
                    let state = self.take_async_generator_state(generator)?;
                    let AsyncGeneratorState::SuspendedYield(activation) = state else {
                        unreachable!("async generator plan selected a non-yield state")
                    };
                    let stop_depth = self.frames.len();
                    let return_to = self.frames.last().map(|frame| ReturnTo {
                        destination: None,
                        call_pc: frame.pc,
                        constructed: None,
                    });
                    let step = self
                        .push_resumed_generator_frame(activation, completion, return_to)
                        .and_then(|()| self.drive_async_generator_activation(stop_depth, None));
                    self.settle_async_generator_step(generator, step)?;
                }
            }
        }
    }

    /// Runs the body of an async generator from the current frame top under
    /// callback, async, AND generator boundaries at one depth. The `Await`
    /// opcode routes itself to the async suspension slot and `Suspend` (yield)
    /// to the generator slot, so one frame can be driven by both stacks.
    fn drive_async_generator_activation(
        &mut self,
        stop_depth: usize,
        inject: Option<(Value, ThrowOrigin, usize)>,
    ) -> Result<AsyncGeneratorStep, EvalFailure> {
        self.last_completion = None;
        self.pending_async_suspend = None;
        self.pending_generator_resume = None;
        self.callback_boundaries.push(stop_depth);
        self.async_boundaries.push(stop_depth);
        self.generator_boundaries.push(stop_depth);
        let result = match inject {
            None => self.run_loop(stop_depth),
            Some((value, origin, faulting_pc)) => match self.throw(value, origin, faulting_pc) {
                Ok(()) => self.run_loop(stop_depth),
                Err(error) => Err(error),
            },
        };
        self.generator_boundaries
            .pop()
            .expect("async generator execution owns its yield boundary");
        self.async_boundaries
            .pop()
            .expect("async generator execution owns its await boundary");
        self.callback_boundaries
            .pop()
            .expect("async generator execution owns its unwind boundary");
        match result {
            Ok(Some(execution)) => Ok(AsyncGeneratorStep::Return(execution.value)),
            Ok(None) => {
                if let Some((awaited, activation)) = self.pending_async_suspend.take() {
                    return Ok(AsyncGeneratorStep::Await {
                        awaited,
                        activation,
                    });
                }
                if let Some(GeneratorResume::Yield { value, activation }) =
                    self.pending_generator_resume.take()
                {
                    return Ok(AsyncGeneratorStep::Yield { value, activation });
                }
                let value = self.last_completion.take().unwrap_or(Value::UNDEFINED);
                Ok(AsyncGeneratorStep::Return(value))
            }
            Err(error) => {
                self.unwind_frames_to(stop_depth);
                match error.kind {
                    RuntimeErrorKind::UncaughtThrow { value, origin, .. } => {
                        Ok(AsyncGeneratorStep::Throw { value, origin })
                    }
                    kind => Err(EvalFailure::Runtime(kind)),
                }
            }
        }
    }

    /// Settles one drive step. `Await` and `Yield` park the generator and arm
    /// Promise reactions without touching the queue; a return parks in
    /// `AwaitingReturn` and awaits the return value before the front request
    /// settles; a throw pops the front request, rejects it, and completes the
    /// generator so the drive loop drains the remainder. Every failure path
    /// releases the suspended registers and completes the generator.
    fn settle_async_generator_step(
        &mut self,
        generator: Value,
        step: Result<AsyncGeneratorStep, EvalFailure>,
    ) -> Result<(), EvalFailure> {
        match step {
            Ok(AsyncGeneratorStep::Await {
                awaited,
                activation,
            }) => {
                let register_count = activation.registers.len();
                let result = self
                    .replace_async_generator_state(
                        generator,
                        AsyncGeneratorState::AwaitingOperand(activation),
                    )
                    .map_err(EvalFailure::Runtime)
                    .and_then(|()| self.await_promise_for_generator(awaited, generator));
                if result.is_err() {
                    self.release_suspended_activation_registers(register_count);
                    self.complete_async_generator(generator)?;
                }
                result
            }
            Ok(AsyncGeneratorStep::Yield { value, activation }) => {
                let register_count = activation.registers.len();
                let result = self
                    .replace_async_generator_state(
                        generator,
                        AsyncGeneratorState::AwaitingYield(activation),
                    )
                    .map_err(EvalFailure::Runtime)
                    .and_then(|()| self.await_promise_for_generator(value, generator));
                if result.is_err() {
                    self.release_suspended_activation_registers(register_count);
                    self.complete_async_generator(generator)?;
                }
                result
            }
            Ok(AsyncGeneratorStep::Return(value)) => {
                // AsyncGeneratorAwaitReturn: the return value is awaited
                // before the front request settles `done: true`; the body is
                // gone, so no activation registers stay charged. The queue is
                // untouched until the awaited value settles the front request.
                let result = self
                    .replace_async_generator_state(generator, AsyncGeneratorState::AwaitingReturn)
                    .map_err(EvalFailure::Runtime)
                    .and_then(|()| self.await_promise_for_generator(value, generator));
                if result.is_err() {
                    self.complete_async_generator(generator)?;
                }
                result
            }
            Ok(AsyncGeneratorStep::Throw { value, origin }) => {
                let request = self.pop_async_generator_front(generator)?;
                self.complete_async_generator(generator)?;
                self.reject_promise(request.capability, value, origin)
                    .map_err(EvalFailure::Runtime)
            }
            Err(failure) => {
                self.complete_async_generator(generator)?;
                Err(failure)
            }
        }
    }

    /// Resolves the awaited (or yielded) value through Promise resolution and
    /// attaches the two generator resume reactions. An already-settled Promise
    /// costs exactly one microtask tick, mirroring `await_promise`.
    fn await_promise_for_generator(
        &mut self,
        awaited: Value,
        generator: Value,
    ) -> Result<(), EvalFailure> {
        let promise = self.promise_resolve(awaited)?;
        let index = self
            .runtime_slot(promise)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: promise,
            }))?;
        let settled = match &self.heap[index] {
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            } => None,
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } => Some((true, *value, ThrowOrigin::Bytecode)),
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, origin },
                ..
            } => Some((false, *reason, *origin)),
            _ => {
                return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                    value: promise,
                }));
            }
        };
        if let Some((fulfilled, value, origin)) = settled {
            self.ensure_microtask_capacity(1)
                .map_err(EvalFailure::Runtime)?;
            let reaction = if fulfilled {
                PromiseReaction::AsyncGeneratorFulfill {
                    generator,
                    context: self.context_global,
                }
            } else {
                PromiseReaction::AsyncGeneratorReject {
                    generator,
                    context: self.context_global,
                }
            };
            self.microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                }));
            return Ok(());
        }
        self.charge_promise_reactions(index, 2)?;
        let context = self.context_global;
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("pending Promise state was checked before reaction registration");
        };
        fulfill_reactions.push(PromiseReaction::AsyncGeneratorFulfill { generator, context });
        reject_reactions.push(PromiseReaction::AsyncGeneratorReject { generator, context });
        Ok(())
    }

    /// Resumes a parked async generator inside its Promise reaction job.
    /// Fulfillment of an `Await` operand writes the value to `Await.dst`;
    /// fulfillment of a `yield` operand settles the front request with
    /// `{value, done: false}`; fulfillment of a returned value settles the
    /// front request with `{value, done: true}` and drains the queue. Either
    /// rejection injects the throw at the suspension pc so a covering
    /// `try`/`catch` runs, except a rejected return value, which rejects the
    /// front request and drains the queue. Any other state is a hard
    /// invariant violation.
    fn resume_async_generator(
        &mut self,
        generator: Value,
        value: Value,
        rejection: Option<ThrowOrigin>,
    ) -> Result<(), RuntimeErrorKind> {
        let state = self
            .take_async_generator_state(generator)
            .map_err(|failure| async_generator_kind(generator, failure))?;
        match (state, rejection) {
            (AsyncGeneratorState::AwaitingYield(activation), None) => {
                let request = self
                    .pop_async_generator_front(generator)
                    .map_err(|failure| async_generator_kind(generator, failure))?;
                let register_count = activation.registers.len();
                match self.iterator_result(value, false) {
                    Err(failure) => {
                        self.release_suspended_activation_registers(register_count);
                        self.complete_async_generator(generator)
                            .map_err(|failure| async_generator_kind(generator, failure))?;
                        self.reject_promise_failure(request.capability, failure)
                            .map_err(|failure| async_generator_kind(generator, failure))
                    }
                    Ok(result) => {
                        if let Err(kind) = self.replace_async_generator_state(
                            generator,
                            AsyncGeneratorState::SuspendedYield(activation),
                        ) {
                            self.release_suspended_activation_registers(register_count);
                            return Err(kind);
                        }
                        self.resolve_promise(request.capability, result)?;
                        self.drive_async_generator(generator)
                            .map_err(|failure| async_generator_kind(generator, failure))
                    }
                }
            }
            (AsyncGeneratorState::AwaitingReturn, rejection) => {
                let request = self
                    .pop_async_generator_front(generator)
                    .map_err(|failure| async_generator_kind(generator, failure))?;
                self.complete_async_generator(generator)
                    .map_err(|failure| async_generator_kind(generator, failure))?;
                match rejection {
                    Some(origin) => self.reject_promise(request.capability, value, origin)?,
                    None => {
                        let result = self
                            .iterator_result(value, true)
                            .map_err(|failure| async_generator_kind(generator, failure))?;
                        self.resolve_promise(request.capability, result)?;
                    }
                }
                self.drive_async_generator(generator)
                    .map_err(|failure| async_generator_kind(generator, failure))
            }
            (AsyncGeneratorState::AwaitingOperand(activation), None) => self
                .drive_resumed_async_generator(
                    generator,
                    activation,
                    GeneratorCompletion::Normal(value),
                    None,
                ),
            (AsyncGeneratorState::AwaitingOperand(activation), Some(origin)) => {
                let suspend_pc = activation
                    .resume_token
                    .checked_sub(1)
                    .expect("suspended async generator token is nonzero")
                    as usize;
                self.drive_resumed_async_generator(
                    generator,
                    activation,
                    GeneratorCompletion::Normal(Value::UNDEFINED),
                    Some((value, origin, suspend_pc)),
                )
            }
            (AsyncGeneratorState::AwaitingResumption(activation), None) => self
                .drive_resumed_async_generator(
                    generator,
                    activation,
                    GeneratorCompletion::Return(value),
                    None,
                ),
            (AsyncGeneratorState::AwaitingResumption(activation), Some(origin)) => {
                // The suspension is a Suspend instruction with a mode
                // register; re-enter with Throw(value) and let the
                // compiler's inline abrupt dispatch handle it — no inject.
                self.drive_resumed_async_generator(
                    generator,
                    activation,
                    GeneratorCompletion::Throw { value, origin },
                    None,
                )
            }
            (AsyncGeneratorState::AwaitingYield(activation), Some(origin)) => {
                let suspend_pc = activation
                    .resume_token
                    .checked_sub(1)
                    .expect("suspended async generator token is nonzero")
                    as usize;
                self.drive_resumed_async_generator(
                    generator,
                    activation,
                    GeneratorCompletion::Normal(Value::UNDEFINED),
                    Some((value, origin, suspend_pc)),
                )
            }
            (
                state @ (AsyncGeneratorState::SuspendedStart(_)
                | AsyncGeneratorState::SuspendedYield(_)
                | AsyncGeneratorState::Completed),
                _,
            ) => {
                let register_count = match &state {
                    AsyncGeneratorState::SuspendedYield(activation) => activation.registers.len(),
                    _ => 0,
                };
                self.release_suspended_activation_registers(register_count);
                self.complete_async_generator(generator)
                    .map_err(|failure| async_generator_kind(generator, failure))?;
                Err(RuntimeErrorKind::InvalidValue { value: generator })
            }
            (AsyncGeneratorState::Executing, _) => {
                unreachable!("take_async_generator_state rejects an executing generator")
            }
        }
    }

    /// Pushes a parked activation back on the frame stack and drives it under
    /// the three-boundary activation runner, then settles the step against
    /// the request queue. On fulfillment the awaited value lands in the
    /// suspension's `dst`; on rejection the throw is injected at the
    /// suspension pc and `dst` stays undefined, mirroring `resume_async`.
    fn drive_resumed_async_generator(
        &mut self,
        generator: Value,
        activation: SuspendedActivation,
        completion: GeneratorCompletion,
        inject: Option<(Value, ThrowOrigin, usize)>,
    ) -> Result<(), RuntimeErrorKind> {
        let stop_depth = self.frames.len();
        let return_to = self.frames.last().map(|frame| ReturnTo {
            destination: None,
            call_pc: frame.pc,
            constructed: None,
        });
        let step = self
            .push_resumed_generator_frame(activation, completion, return_to)
            .and_then(|()| self.drive_async_generator_activation(stop_depth, inject));
        match self.settle_async_generator_step(generator, step) {
            // A completing step (throw) leaves the queue for the drain loop;
            // a parking step makes the drain loop return immediately.
            Ok(()) => self
                .drive_async_generator(generator)
                .map_err(|failure| async_generator_kind(generator, failure)),
            Err(EvalFailure::Runtime(kind)) => Err(kind),
            Err(_) => Err(RuntimeErrorKind::InvalidValue { value: generator }),
        }
    }

    /// Takes the generator state out of an `Awaiting*` park (or any resumable
    /// state), leaving `Executing` behind. A resume in a non-resumable state
    /// is a hard invalid-state error, mirroring `take_async_activation`.
    fn take_async_generator_state(
        &mut self,
        generator: Value,
    ) -> Result<AsyncGeneratorState, EvalFailure> {
        let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        let HeapEntry::AsyncGenerator { state, .. } = &mut self.heap[index] else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        match std::mem::replace(state, AsyncGeneratorState::Executing) {
            AsyncGeneratorState::Executing => {
                Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                    value: generator,
                }))
            }
            taken => Ok(taken),
        }
    }

    /// Pops the front `.next()` request, which the current drive settles
    /// exactly once. The queue is never popped by await/yield parking.
    fn pop_async_generator_front(
        &mut self,
        generator: Value,
    ) -> Result<AsyncGeneratorRequest, EvalFailure> {
        let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        let HeapEntry::AsyncGenerator { queue, .. } = &mut self.heap[index] else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        queue
            .pop_front()
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }))
    }

    fn replace_async_generator_state(
        &mut self,
        generator: Value,
        next: AsyncGeneratorState,
    ) -> Result<(), RuntimeErrorKind> {
        let Some(index) = self.runtime_slot(generator)? else {
            return Err(RuntimeErrorKind::InvalidValue { value: generator });
        };
        let HeapEntry::AsyncGenerator { state, .. } = &mut self.heap[index] else {
            return Err(RuntimeErrorKind::InvalidValue { value: generator });
        };
        if !matches!(state, AsyncGeneratorState::Executing) {
            return Err(RuntimeErrorKind::InvalidValue { value: generator });
        }
        *state = next;
        Ok(())
    }

    fn complete_async_generator(&mut self, generator: Value) -> Result<(), EvalFailure> {
        let Some(index) = self.runtime_slot(generator).map_err(EvalFailure::Runtime)? else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        let HeapEntry::AsyncGenerator { state, .. } = &mut self.heap[index] else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: generator,
            }));
        };
        *state = AsyncGeneratorState::Completed;
        Ok(())
    }

    /// Resolves the awaited value through Promise resolution and attaches the
    /// two direct resume reactions that point only at the activation record. An
    /// already-settled Promise costs exactly one microtask tick.
    fn await_promise(&mut self, awaited: Value, record: Value) -> Result<(), EvalFailure> {
        let promise = self.promise_resolve(awaited)?;
        let index = self
            .runtime_slot(promise)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: promise,
            }))?;
        let settled = match &self.heap[index] {
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            } => None,
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } => Some((true, *value, ThrowOrigin::Bytecode)),
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, origin },
                ..
            } => Some((false, *reason, *origin)),
            _ => {
                return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                    value: promise,
                }));
            }
        };
        if let Some((fulfilled, value, origin)) = settled {
            self.ensure_microtask_capacity(1)
                .map_err(EvalFailure::Runtime)?;
            let reaction = if fulfilled {
                PromiseReaction::AsyncFulfill {
                    activation: record,
                    context: self.context_global,
                }
            } else {
                PromiseReaction::AsyncReject {
                    activation: record,
                    context: self.context_global,
                }
            };
            self.microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                }));
            return Ok(());
        }
        self.charge_promise_reactions(index, 2)?;
        let context = self.context_global;
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("pending Promise state was checked before reaction registration");
        };
        fulfill_reactions.push(PromiseReaction::AsyncFulfill {
            activation: record,
            context,
        });
        reject_reactions.push(PromiseReaction::AsyncReject {
            activation: record,
            context,
        });
        Ok(())
    }

    fn create_async_activation(
        &mut self,
        promise: Value,
        module: Option<ModuleId>,
    ) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::AsyncActivation {
            activation: None,
            promise,
            module,
            completion: None,
        })
        .map_err(EvalFailure::Runtime)
    }

    fn store_async_module_completion(
        &mut self,
        record: Value,
        completed: Option<Result<Execution, RuntimeError>>,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(record)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: record,
            }))?;
        let HeapEntry::AsyncActivation {
            module, completion, ..
        } = &mut self.heap[index]
        else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: record,
            }));
        };
        if module.is_none() {
            return Ok(());
        }
        let completed = completed.ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
            value: record,
        }))?;
        if completion.is_some() {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: record,
            }));
        }
        *completion = Some(completed);
        Ok(())
    }

    fn store_async_activation(
        &mut self,
        record: Value,
        activation: SuspendedActivation,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(record)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: record,
            }))?;
        let HeapEntry::AsyncActivation {
            activation: slot, ..
        } = &mut self.heap[index]
        else {
            return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: record,
            }));
        };
        *slot = Some(activation);
        Ok(())
    }

    /// Takes the one suspended activation out of the record, making resume
    /// one-shot. A second take (a second resume) is a hard invalid-state error.
    fn take_async_activation(
        &mut self,
        record: Value,
    ) -> Result<SuspendedActivation, RuntimeErrorKind> {
        let index = self
            .runtime_slot(record)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })?;
        let HeapEntry::AsyncActivation {
            activation: slot, ..
        } = &mut self.heap[index]
        else {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        };
        slot.take()
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })
    }

    fn async_activation_promise(&self, record: Value) -> Result<Value, RuntimeErrorKind> {
        let index = self
            .runtime_slot(record)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })?;
        let HeapEntry::AsyncActivation { promise, .. } = &self.heap[index] else {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        };
        Ok(*promise)
    }

    fn async_activation_module(&self, record: Value) -> Result<Option<ModuleId>, RuntimeErrorKind> {
        let index = self
            .runtime_slot(record)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })?;
        let HeapEntry::AsyncActivation { module, .. } = &self.heap[index] else {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        };
        Ok(*module)
    }

    fn take_async_module_completion(
        &mut self,
        record: Value,
        module: ModuleId,
    ) -> Result<Result<Execution, RuntimeError>, RuntimeErrorKind> {
        let index = self
            .runtime_slot(record)?
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })?;
        let HeapEntry::AsyncActivation {
            module: owner,
            completion,
            ..
        } = &mut self.heap[index]
        else {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        };
        if *owner != Some(module) {
            return Err(RuntimeErrorKind::InvalidValue { value: record });
        }
        completion
            .take()
            .ok_or(RuntimeErrorKind::InvalidValue { value: record })
    }

    pub(crate) fn iterator_result(
        &mut self,
        value: Value,
        done: bool,
    ) -> Result<Value, EvalFailure> {
        let result = self
            .allocate(HeapEntry::Object {
                properties: PropertyMap::default(),
                prototype: Some(self.intrinsics.object_prototype),
                boxed_primitive: None,
                extensible: true,
            })
            .map_err(EvalFailure::Runtime)?;
        let value_key = PropertyKey::Named(self.intern_str("value"));
        self.create_data_property_key(result, value_key, value)?;
        let done_key = PropertyKey::Named(self.intern_str("done"));
        self.create_data_property_key(result, done_key, Value::boolean(done))?;
        Ok(result)
    }

    // ---- iterators ---------------------------------------------------------

    fn create_iterator(&mut self, src: Value, kind: IteratorKind) -> Result<Value, EvalFailure> {
        if kind == IteratorKind::Keys {
            let state = self.for_in_iterator_state(src)?;
            return self
                .allocate(HeapEntry::Iterator {
                    state: IteratorState::Keys(state),
                })
                .map_err(EvalFailure::Runtime);
        }

        let (method, from_sync) = match kind {
            IteratorKind::Async => {
                let key =
                    self.property_key_from_value(self.intrinsics.builtins.symbol_async_iterator())?;
                let method = self.get_property_key(src, &key)?;
                if matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
                    let key =
                        self.property_key_from_value(self.intrinsics.builtins.symbol_iterator())?;
                    (self.get_property_key(src, &key)?, true)
                } else {
                    (method, false)
                }
            }
            IteratorKind::Sync => {
                let key =
                    self.property_key_from_value(self.intrinsics.builtins.symbol_iterator())?;
                (self.get_property_key(src, &key)?, false)
            }
            IteratorKind::Keys => unreachable!("key iteration returns before method lookup"),
        };
        if !self.is_callable(method)? {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "value is not iterable",
            }));
        }
        let iterator = self.call_value(method, src, &[])?;
        if !self.is_object(iterator) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator method returned a non-object",
            }));
        }
        let next = self.get_named_property(iterator, "next")?;
        if from_sync {
            self.create_async_from_sync_iterator(iterator, next)
        } else {
            self.create_protocol_iterator(iterator, next)
        }
    }

    pub(crate) fn create_protocol_iterator(
        &mut self,
        iterator: Value,
        next: Value,
    ) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::Iterator {
            state: IteratorState::Protocol { iterator, next },
        })
        .map_err(EvalFailure::Runtime)
    }

    /// Allocates the async-from-sync adapter record (ECMA-262 27.1.5) for an
    /// async iterator lookup that fell back to `Symbol.iterator`.
    pub(crate) fn create_async_from_sync_iterator(
        &mut self,
        iterator: Value,
        next: Value,
    ) -> Result<Value, EvalFailure> {
        self.allocate(HeapEntry::AsyncFromSync {
            iterator,
            next,
            properties: PropertyMap::default(),
            prototype: Some(
                self.intrinsics
                    .builtins
                    .async_from_sync_iterator_prototype(),
            ),
            extensible: true,
        })
        .map_err(EvalFailure::Runtime)
    }

    fn own_property_keys(&mut self, src: Value) -> Result<Vec<PropertyKey>, EvalFailure> {
        match self.runtime_slot(src).map_err(EvalFailure::Runtime)? {
            Some(index) => match &self.heap[index] {
                HeapEntry::Proxy { .. } => Ok(Vec::new()),
                HeapEntry::ProxyRevoker { properties, .. } => {
                    Ok(ordered_property_keys(properties, &self.shapes, &self.atoms))
                }
                HeapEntry::TypedArray { properties, .. } => {
                    let length = self.typed_array_length_at(index).unwrap_or_default();
                    let ordered = ordered_property_keys(properties, &self.shapes, &self.atoms);
                    let filtered: Vec<PropertyKey> = ordered
                        .into_iter()
                        .filter(|key| match key {
                            PropertyKey::Named(atom) => {
                                typedarray::typed_array_index(self.atoms.resolve(*atom)).is_none()
                            }
                            _ => true,
                        })
                        .collect();
                    let mut keys = Vec::with_capacity(length.saturating_add(filtered.len()));
                    for i in 0..length {
                        keys.push(PropertyKey::Named(self.intern_str(&i.to_string())));
                    }
                    keys.extend(filtered);
                    Ok(keys)
                }
                HeapEntry::Object { properties, .. }
                | HeapEntry::WeakRef { properties, .. }
                | HeapEntry::FinalizationRegistry { properties, .. }
                | HeapEntry::Generator { properties, .. }
                | HeapEntry::AsyncGenerator { properties, .. }
                | HeapEntry::AsyncFromSync { properties, .. }
                | HeapEntry::Script { properties, .. }
                | HeapEntry::Function { properties, .. }
                | HeapEntry::NativeFunction { properties, .. }
                | HeapEntry::RegExp { properties, .. }
                | HeapEntry::Date { properties, .. }
                | HeapEntry::Temporal { properties, .. }
                | HeapEntry::Intl { properties, .. }
                | HeapEntry::BuiltinIterator { properties, .. }
                | HeapEntry::Collection { properties, .. }
                | HeapEntry::Promise { properties, .. }
                | HeapEntry::DisposableStack { properties, .. }
                | HeapEntry::Timeout { properties, .. }
                | HeapEntry::ArrayBuffer { properties, .. }
                | HeapEntry::SharedArrayBuffer { properties, .. }
                | HeapEntry::DataView { properties, .. } => {
                    Ok(ordered_property_keys(properties, &self.shapes, &self.atoms))
                }
                HeapEntry::Array {
                    elements,
                    properties,
                    ..
                } => {
                    let holes: Vec<usize> = elements
                        .iter()
                        .enumerate()
                        .filter(|(_, element)| **element != Value::HOLE)
                        .map(|(offset, _)| offset)
                        .collect();
                    let ordered = ordered_property_keys(properties, &self.shapes, &self.atoms);
                    let mut suffix = Vec::new();
                    let mut extra: Vec<(usize, PropertyKey)> = Vec::new();
                    for key in ordered {
                        let offset_opt = match key {
                            PropertyKey::Named(atom) => self.atoms.array_index(atom),
                            _ => None,
                        };
                        match offset_opt {
                            Some(offset) => {
                                let offset_usize = offset as usize;
                                if elements
                                    .get(offset_usize)
                                    .is_some_and(|element| *element != Value::HOLE)
                                {
                                    continue;
                                }
                                extra.push((offset_usize, key));
                            }
                            None => suffix.push(key),
                        }
                    }
                    let mut indices: Vec<(usize, PropertyKey)> =
                        Vec::with_capacity(holes.len().saturating_add(extra.len()));
                    for offset in holes {
                        indices.push((
                            offset,
                            PropertyKey::Named(self.intern_str(&offset.to_string())),
                        ));
                    }
                    indices.extend(extra);
                    indices.sort_unstable_by_key(|(offset, _)| *offset);
                    let length = PropertyKey::Named(self.intern_str("length"));
                    Ok(indices
                        .into_iter()
                        .map(|(_, key)| key)
                        .chain(std::iter::once(length))
                        .chain(suffix)
                        .collect())
                }
                HeapEntry::String(_) | HeapEntry::Rope { .. } => {
                    let len = self.string_len(index);
                    let mut keys = Vec::with_capacity(len);
                    for i in 0..len {
                        keys.push(PropertyKey::Named(self.intern_str(&i.to_string())));
                    }
                    Ok(keys)
                }
                HeapEntry::ModuleNamespace { module } => {
                    let module_id = *module;
                    let mut names: Vec<EcmaString> = self
                        .program_module(module_id)
                        .exports
                        .iter()
                        .map(|export| self.constant_text(module_id, export.name).clone())
                        .collect();
                    names.sort();
                    let mut keys = Vec::with_capacity(names.len());
                    for name in names {
                        keys.push(PropertyKey::Named(self.intern(name)));
                    }
                    Ok(keys)
                }
                HeapEntry::ExternalModuleNamespace { specifier } => {
                    let spec = specifier.clone();
                    let names: Vec<EcmaString> = self.registry.external[&spec]
                        .exports
                        .keys()
                        .cloned()
                        .collect();
                    let mut keys = Vec::with_capacity(names.len());
                    for name in names {
                        keys.push(PropertyKey::Named(self.intern(name)));
                    }
                    Ok(keys)
                }
                HeapEntry::ProcessEnv { .. }
                | HeapEntry::BigInt(_)
                | HeapEntry::Symbol { .. }
                | HeapEntry::PrivateName { .. }
                | HeapEntry::HashState { .. }
                | HeapEntry::Iterator { .. }
                | HeapEntry::PromiseResolver { .. }
                | HeapEntry::PromiseAll { .. }
                | HeapEntry::AsyncActivation { .. }
                | HeapEntry::PromiseAllElement { .. } => Ok(Vec::new()),
                HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
            },
            None => Ok(Vec::new()),
        }
    }

    fn own_property_is_enumerable(
        &mut self,
        src: Value,
        key: &PropertyKey,
    ) -> Result<bool, EvalFailure> {
        let Some(index) = self.runtime_slot(src).map_err(EvalFailure::Runtime)? else {
            return Ok(false);
        };
        if matches!(self.heap[index], HeapEntry::Proxy { .. })
            && !matches!(key, PropertyKey::Private(_))
        {
            return Ok(self
                .internal_get_own_property(src, key)?
                .is_some_and(|descriptor| descriptor.enumerable == Some(true)));
        }
        if let Some(text) = self.boxed_string(index)
            && string_has_index(&text, &self.atoms, key)
        {
            return Ok(true);
        }
        Ok(match &self.heap[index] {
            HeapEntry::Array {
                elements,
                properties,
                ..
            } => properties.get(&self.shapes, key).map_or_else(
                || {
                    key.as_string(&self.atoms).is_some_and(|name| {
                        array_index(name).is_some_and(|offset| {
                            elements
                                .get(offset as usize)
                                .is_some_and(|element| *element != Value::HOLE)
                        })
                    })
                },
                Property::enumerable,
            ),
            HeapEntry::String(_) | HeapEntry::Rope { .. } => {
                let text = self.flat_string(index);
                string_has_index(&text, &self.atoms, key)
            }
            HeapEntry::TypedArray { properties, .. } => {
                properties.get(&self.shapes, key).map_or_else(
                    || {
                        key.as_string(&self.atoms)
                            .and_then(typedarray::typed_array_index)
                            .flatten()
                            .is_some_and(|offset| {
                                self.typed_array_length_at(index)
                                    .is_some_and(|length| offset < length)
                            })
                    },
                    Property::enumerable,
                )
            }
            HeapEntry::ModuleNamespace { .. } | HeapEntry::ExternalModuleNamespace { .. } => {
                matches!(key, PropertyKey::Named(_))
            }
            HeapEntry::Object { properties, .. }
            | HeapEntry::Generator { properties, .. }
            | HeapEntry::AsyncGenerator { properties, .. }
            | HeapEntry::AsyncFromSync { properties, .. }
            | HeapEntry::Script { properties, .. }
            | HeapEntry::Function { properties, .. }
            | HeapEntry::NativeFunction { properties, .. }
            | HeapEntry::RegExp { properties, .. }
            | HeapEntry::Date { properties, .. }
            | HeapEntry::Temporal { properties, .. }
            | HeapEntry::Intl { properties, .. }
            | HeapEntry::BuiltinIterator { properties, .. }
            | HeapEntry::Collection { properties, .. }
            | HeapEntry::Promise { properties, .. }
            | HeapEntry::WeakRef { properties, .. }
            | HeapEntry::FinalizationRegistry { properties, .. }
            | HeapEntry::DisposableStack { properties, .. }
            | HeapEntry::Timeout { properties, .. }
            | HeapEntry::ArrayBuffer { properties, .. }
            | HeapEntry::SharedArrayBuffer { properties, .. }
            | HeapEntry::DataView { properties, .. } => properties
                .get(&self.shapes, key)
                .is_some_and(Property::enumerable),
            _ => false,
        })
    }

    fn enumerable_keys(&mut self, src: Value) -> Result<Vec<EcmaString>, EvalFailure> {
        let mut names = Vec::new();
        for key in self.internal_own_property_keys(src)? {
            if !self.own_property_is_enumerable(src, &key)? {
                continue;
            }
            if let PropertyKey::Named(name) = key {
                names.push(self.atoms.resolve(name).clone());
            }
        }
        Ok(names)
    }

    /// Builds the initial `for`/`in` state: nullish sources are already
    /// complete, and every other primitive is boxed through `value_to_object`
    /// (ECMA-262 14.7.5.15 step 1-2).
    fn for_in_iterator_state(&mut self, src: Value) -> Result<ForInIteratorState, EvalFailure> {
        let current = match src.decode() {
            Some(Decoded::Undefined | Decoded::Null) => None,
            _ => Some(self.value_to_object(src)?),
        };
        Ok(ForInIteratorState {
            current,
            object_was_visited: false,
            remaining: VecDeque::new(),
            visited_names: BTreeSet::new(),
            visited_objects: BTreeSet::new(),
        })
    }

    /// Executes one `for`/`in` step against the Keys iterator at
    /// `iterator_index`, returning the next enumerable string key, or `None`
    /// once traversal is exhausted. All state stays in the heap entry so the
    /// current object remains traced while proxy traps run user code.
    fn for_in_next(&mut self, iterator_index: usize) -> Result<Option<EcmaString>, EvalFailure> {
        loop {
            let Some(current) = self.for_in_current(iterator_index)? else {
                return Ok(None);
            };
            if !self.for_in_enter_level(iterator_index, current)? {
                // A repeated object slot means a malformed prototype cycle;
                // traversal stops safely instead of looping unboundedly.
                return Ok(None);
            }
            while let Some((name, shadowed)) = self.for_in_pop_name(iterator_index)? {
                if shadowed {
                    continue;
                }
                let key = PropertyKey::Named(self.intern(name.clone()));
                match self.internal_get_own_property(current, &key)? {
                    // Deleted before its visit: the name does not enter
                    // visited_names, so an inherited name may still surface.
                    None => {}
                    Some(descriptor) if descriptor.enumerable == Some(true) => {
                        self.for_in_record_name(iterator_index, name.clone())?;
                        return Ok(Some(name));
                    }
                    // Present but non-enumerable: recorded so it shadows the
                    // same name on farther prototypes, but never yielded.
                    Some(_) => self.for_in_record_name(iterator_index, name)?,
                }
            }
            let prototype = self.internal_get_prototype_of(current)?;
            match &mut self.heap[iterator_index] {
                HeapEntry::Iterator {
                    state: IteratorState::Keys(state),
                } => {
                    state.current = prototype;
                    state.object_was_visited = false;
                }
                _ => {
                    return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "iterator next on non-iterator",
                    }));
                }
            }
        }
    }

    fn for_in_current(&self, iterator_index: usize) -> Result<Option<Value>, EvalFailure> {
        match &self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(state),
            } => Ok(state.current),
            _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            })),
        }
    }

    /// Claims the current object's slot and snapshots its string own keys once
    /// per level. Returns `false` when the slot was already visited, marking
    /// the iterator complete.
    fn for_in_enter_level(
        &mut self,
        iterator_index: usize,
        current: Value,
    ) -> Result<bool, EvalFailure> {
        let already_entered = match &self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(state),
            } => state.object_was_visited,
            _ => {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "iterator next on non-iterator",
                }));
            }
        };
        if already_entered {
            return Ok(true);
        }
        let unvisited = match self.runtime_slot(current).map_err(EvalFailure::Runtime)? {
            Some(slot) => match &mut self.heap[iterator_index] {
                HeapEntry::Iterator {
                    state: IteratorState::Keys(state),
                } => {
                    if state.visited_objects.insert(slot) {
                        true
                    } else {
                        // Repeated object slot: a malformed prototype cycle.
                        state.current = None;
                        false
                    }
                }
                _ => false,
            },
            None => false,
        };
        if !unvisited {
            return Ok(false);
        }
        let keys = self.internal_own_property_keys(current)?;
        let names: VecDeque<EcmaString> = keys
            .into_iter()
            .filter_map(|key| match key {
                PropertyKey::Named(name) => Some(self.atoms.resolve(name).clone()),
                PropertyKey::Symbol(_) | PropertyKey::Private(_) => None,
            })
            .collect();
        match &mut self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(state),
            } => {
                state.object_was_visited = true;
                state.remaining = names;
                Ok(true)
            }
            _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            })),
        }
    }

    /// Pops the next pending name of the current level together with whether
    /// a nearer level already decided it (`visited_names`).
    fn for_in_pop_name(
        &mut self,
        iterator_index: usize,
    ) -> Result<Option<(EcmaString, bool)>, EvalFailure> {
        match &mut self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(state),
            } => Ok(match state.remaining.pop_front() {
                Some(name) => {
                    let shadowed = state.visited_names.contains(&name);
                    Some((name, shadowed))
                }
                None => None,
            }),
            _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            })),
        }
    }

    fn for_in_record_name(
        &mut self,
        iterator_index: usize,
        name: EcmaString,
    ) -> Result<(), EvalFailure> {
        match &mut self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(state),
            } => {
                state.visited_names.insert(name);
                Ok(())
            }
            _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            })),
        }
    }

    fn iterator_next(&mut self, iterator: Value) -> Result<(bool, Value), EvalFailure> {
        // Fused sync consumption reads the raw result directly; the
        // async-from-sync adapter wraps only the `for await` step path.
        let result = match self.prepare_iterator_next(iterator)? {
            IteratorNextPrepared::Ready { done, value } => self.iterator_result(value, done)?,
            IteratorNextPrepared::Call { callee, this_value }
            | IteratorNextPrepared::AsyncFromSyncCall { callee, this_value } => {
                self.call_value(callee, this_value, &[])?
            }
        };
        self.iterator_result_parts(result)
    }

    /// Spec `IteratorNext`: performs the `next()` call (or takes the recorded
    /// key of a Keys iterator) and returns the raw result with NO object
    /// check. `for await` needs the raw Promise before awaiting it.
    pub(crate) fn iterator_step(&mut self, iterator: Value) -> Result<Value, EvalFailure> {
        match self.prepare_iterator_next(iterator)? {
            IteratorNextPrepared::Ready { done, value } => self.iterator_result(value, done),
            IteratorNextPrepared::Call { callee, this_value } => {
                self.call_value(callee, this_value, &[])
            }
            IteratorNextPrepared::AsyncFromSyncCall { callee, this_value } => {
                let result = self.call_value(callee, this_value, &[]);
                self.async_from_sync_continuation(this_value, result)
            }
        }
    }

    /// Spec `IteratorComplete` + `IteratorValue`: an iterator result that is
    /// not an Object is a TypeError, otherwise reads `done` (truthiness) and
    /// `value`. A done result carries `undefined` for the value, matching the
    /// fused sync path's behaviour.
    pub(crate) fn iterator_result_parts(
        &mut self,
        result: Value,
    ) -> Result<(bool, Value), EvalFailure> {
        if !self.is_object(result) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator result is not an object",
            }));
        }
        let done = self.get_named_property(result, "done")?;
        if self.truthy(done) {
            return Ok((true, Value::UNDEFINED));
        }
        let value = self.get_named_property(result, "value")?;
        self.keep_temporary(value);
        Ok((false, value))
    }

    /// ECMA-262 27.1.5.2.2 `AsyncFromSyncIteratorContinuation`: parses the
    /// raw sync iterator-result object before any await, PromiseResolves only
    /// its `value`, and settles a derived step promise with a freshly built
    /// `{ value: unwrapped, done }` result. The raw result object itself is
    /// never assimilated. A failed synchronous step closes the sync iterator;
    /// rejection while unwrapping its value propagates without closing. Shared
    /// by the interpreter and native helper path so every backend agrees.
    pub(crate) fn async_from_sync_iterator_method(
        &mut self,
        adapter: Value,
        operation: vm::generator_async::GeneratorOperation,
        value: Value,
    ) -> Result<Value, EvalFailure> {
        let carrier = self
            .runtime_slot(adapter)
            .map_err(EvalFailure::Runtime)?
            .and_then(|index| match &self.heap[index] {
                HeapEntry::AsyncFromSync { iterator, next, .. } => Some((*iterator, *next)),
                _ => None,
            });
        let Some((iterator, next)) = carrier else {
            let rejected = self.create_promise()?;
            self.reject_promise(
                rejected,
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "AsyncFromSyncIterator method called on incompatible receiver",
                },
            )
            .map_err(EvalFailure::Runtime)?;
            return Ok(rejected);
        };
        let method = match operation {
            vm::generator_async::GeneratorOperation::Next => next,
            vm::generator_async::GeneratorOperation::Return => {
                self.get_named_property(iterator, "return")?
            }
            vm::generator_async::GeneratorOperation::Throw => {
                self.get_named_property(iterator, "throw")?
            }
        };
        if matches!(method.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            let settled = self.create_promise()?;
            match operation {
                vm::generator_async::GeneratorOperation::Return => {
                    let result = self.iterator_result(value, true)?;
                    self.resolve_promise(settled, result)
                        .map_err(EvalFailure::Runtime)?;
                }
                vm::generator_async::GeneratorOperation::Throw => {
                    self.reject_promise(
                        settled,
                        Value::UNDEFINED,
                        ThrowOrigin::TypeError {
                            operation: "sync iterator has no throw method",
                        },
                    )
                    .map_err(EvalFailure::Runtime)?;
                }
                vm::generator_async::GeneratorOperation::Next => unreachable!(),
            }
            return Ok(settled);
        }
        if !self.is_callable(method)? {
            let rejected = self.create_promise()?;
            self.reject_promise(
                rejected,
                Value::UNDEFINED,
                ThrowOrigin::TypeError {
                    operation: "sync iterator method is not callable",
                },
            )
            .map_err(EvalFailure::Runtime)?;
            return Ok(rejected);
        }
        let result = self.call_value(method, iterator, &[value]);
        self.async_from_sync_continuation(iterator, result)
    }

    pub(crate) fn async_from_sync_continuation(
        &mut self,
        sync_iterator: Value,
        result: Result<Value, EvalFailure>,
    ) -> Result<Value, EvalFailure> {
        let derived = self.create_promise()?;
        match result.and_then(|result| self.async_from_sync_result_parts(result)) {
            Err(failure) => {
                self.close_protocol_iterator_preserving_abrupt(sync_iterator)
                    .map_err(EvalFailure::Runtime)?;
                self.reject_promise_failure(derived, failure)?;
            }
            Ok((done, value)) => {
                let resolved = self.promise_resolve(value)?;
                self.attach_async_from_sync_reactions(derived, resolved, done, sync_iterator)?;
            }
        }
        Ok(derived)
    }

    /// `IteratorComplete` + `IteratorValue` for the async-from-sync adapter:
    /// unlike the fused sync path, `value` is read even when the result is
    /// done, matching the spec continuation.
    fn async_from_sync_result_parts(
        &mut self,
        result: Value,
    ) -> Result<(bool, Value), EvalFailure> {
        if !self.is_object(result) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator result is not an object",
            }));
        }
        let done = self.get_named_property(result, "done")?;
        let done = self.truthy(done);
        let value = self.get_named_property(result, "value")?;
        Ok((done, value))
    }

    /// Attaches the two adapter reactions to the PromiseResolved step value,
    /// mirroring `promise_then`'s settled/pending split and its reaction and
    /// microtask charging.
    fn attach_async_from_sync_reactions(
        &mut self,
        derived: Value,
        resolved: Value,
        done: bool,
        sync_iterator: Value,
    ) -> Result<(), EvalFailure> {
        let index = self
            .runtime_slot(resolved)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value: resolved,
            }))?;
        let settled = match &self.heap[index] {
            HeapEntry::Promise {
                state: PromiseState::Pending { .. },
                ..
            } => None,
            HeapEntry::Promise {
                state: PromiseState::Fulfilled { value },
                ..
            } => Some((true, *value, ThrowOrigin::Bytecode)),
            HeapEntry::Promise {
                state: PromiseState::Rejected { reason, origin },
                ..
            } => Some((false, *reason, *origin)),
            _ => {
                return Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                    value: resolved,
                }));
            }
        };
        if let Some((fulfilled, value, origin)) = settled {
            self.ensure_microtask_capacity(1)
                .map_err(EvalFailure::Runtime)?;
            let reaction = if fulfilled {
                PromiseReaction::AsyncFromSyncFulfill {
                    derived,
                    done,
                    context: self.context_global,
                }
            } else {
                PromiseReaction::AsyncFromSyncReject {
                    derived,
                    sync_iterator,
                    context: self.context_global,
                }
            };
            self.microtasks
                .push_back(QueuedMicrotask::uncharged(MicrotaskJob::Reaction {
                    reaction,
                    value,
                    origin,
                }));
            return Ok(());
        }
        self.charge_promise_reactions(index, 2)?;
        let context = self.context_global;
        let HeapEntry::Promise {
            state:
                PromiseState::Pending {
                    fulfill_reactions,
                    reject_reactions,
                },
            ..
        } = &mut self.heap[index]
        else {
            unreachable!("pending Promise state was checked before reaction registration");
        };
        fulfill_reactions.push(PromiseReaction::AsyncFromSyncFulfill {
            derived,
            done,
            context,
        });
        reject_reactions.push(PromiseReaction::AsyncFromSyncReject {
            derived,
            sync_iterator,
            context,
        });
        Ok(())
    }

    pub(crate) fn prepare_iterator_next(
        &mut self,
        iterator: Value,
    ) -> Result<IteratorNextPrepared, EvalFailure> {
        let iterator_index = self
            .runtime_slot(iterator)
            .map_err(EvalFailure::Runtime)?
            .ok_or(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            }))?;
        match &self.heap[iterator_index] {
            HeapEntry::Iterator {
                state: IteratorState::Keys(_),
            } => {
                let stepped = self.for_in_next(iterator_index)?;
                let Some(name) = stepped else {
                    return Ok(IteratorNextPrepared::Ready {
                        done: true,
                        value: Value::UNDEFINED,
                    });
                };
                let value = self
                    .allocate(HeapEntry::String(name))
                    .map_err(EvalFailure::Runtime)?;
                Ok(IteratorNextPrepared::Ready { done: false, value })
            }
            HeapEntry::Iterator {
                state: IteratorState::Protocol { iterator, next },
            } => Ok(IteratorNextPrepared::Call {
                callee: *next,
                this_value: *iterator,
            }),
            HeapEntry::AsyncFromSync { iterator, next, .. } => {
                Ok(IteratorNextPrepared::AsyncFromSyncCall {
                    callee: *next,
                    this_value: *iterator,
                })
            }
            _ => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "iterator next on non-iterator",
            })),
        }
    }

    pub(crate) fn iterable_values(&mut self, source: Value) -> Result<Vec<Value>, EvalFailure> {
        let depth = self.native_roots.len();
        let iterator = self.create_iterator(source, IteratorKind::Sync)?;
        self.push_native_roots(depth, &[iterator]);
        let result: Result<Vec<Value>, EvalFailure> = (|| {
            let mut values = Vec::new();
            loop {
                self.refresh_native_roots_with(depth, |roots| {
                    roots.push(iterator);
                    roots.extend_from_slice(&values);
                });
                let (done, value) = self.iterator_next(iterator)?;
                if done {
                    return Ok(values);
                }
                values.push(value);
                self.refresh_native_roots_with(depth, |roots| {
                    roots.push(iterator);
                    roots.extend_from_slice(&values);
                });
                let bytes = values
                    .len()
                    .checked_mul(std::mem::size_of::<Value>())
                    .ok_or(EvalFailure::Runtime(
                        RuntimeErrorKind::HeapByteLimitExceeded {
                            limit: self.limits.max_heap_bytes,
                        },
                    ))?;
                self.ensure_allocation_capacity(1, bytes)
                    .map_err(EvalFailure::Runtime)?;
            }
        })();
        self.pop_native_roots(depth);
        result
    }

    // ---- operators & coercions --------------------------------------------

    fn eval_unary(&mut self, op: UnaryOp, operand: Value) -> Result<Value, EvalFailure> {
        match op {
            UnaryOp::Void => Ok(Value::UNDEFINED),
            UnaryOp::TypeOf => {
                let text = EcmaString::encode(self.type_of(operand));
                self.allocate(HeapEntry::String(text))
                    .map_err(EvalFailure::Runtime)
            }
            UnaryOp::Plus => self.coerce_number_observable(operand),
            UnaryOp::Negate => {
                let operand = self.coerce_primitive_observable(operand, false)?;
                if let Some(value) = intrinsics::builtins::bigint::unary_minus(self, operand)? {
                    return Ok(value);
                }
                let number =
                    numeric_f64(self.to_number(operand)?).expect("ToNumber returns numeric");
                Ok(number_value(-number))
            }
            UnaryOp::BitwiseNot => {
                let operand = self.coerce_primitive_observable(operand, false)?;
                if let Some(value) = intrinsics::builtins::bigint::bitwise_not(self, operand)? {
                    return Ok(value);
                }
                Ok(Value::int32(
                    (!to_int32(numeric_f64(self.to_number(operand)?).unwrap())) as u32,
                ))
            }
            UnaryOp::LogicalNot => Ok(Value::boolean(!self.truthy(operand))),
            UnaryOp::ToString => {
                if self.string_value(operand).is_some() {
                    return Ok(operand);
                }
                let text = self.coerce_string_observable(operand)?;
                self.allocate(HeapEntry::String(text))
                    .map_err(EvalFailure::Runtime)
            }
            UnaryOp::ToPropertyKey => {
                if !self.is_object(operand) {
                    return Ok(operand);
                }
                let key = self.observable_property_key(operand)?;
                intrinsics::builtins::reflect::property_key_value(self, key)
            }
        }
    }

    fn eval_binary(
        &mut self,
        op: BinaryOp,
        left: Value,
        right: Value,
    ) -> Result<Value, EvalFailure> {
        // Converting one operand can run user code while the other's primitive
        // is only a Rust local.
        if self.is_object(left) || self.is_object(right) {
            return self.with_temporaries(|machine| machine.binary_values(op, left, right));
        }
        self.binary_values(op, left, right)
    }

    fn binary_values(
        &mut self,
        op: BinaryOp,
        left: Value,
        right: Value,
    ) -> Result<Value, EvalFailure> {
        match op {
            BinaryOp::StrictEqual => Ok(Value::boolean(self.strict_equal(left, right))),
            BinaryOp::StrictNotEqual => Ok(Value::boolean(!self.strict_equal(left, right))),
            BinaryOp::Equal | BinaryOp::NotEqual => {
                let equal = self.abstract_equal(left, right)?;
                Ok(Value::boolean(if op == BinaryOp::Equal {
                    equal
                } else {
                    !equal
                }))
            }
            BinaryOp::LessThan
            | BinaryOp::LessThanOrEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterThanOrEqual => {
                let ordering = self.relational_compare(left, right)?;
                let result = match (op, ordering) {
                    (_, None) => false,
                    (BinaryOp::LessThan, Some(order)) => order == Ordering::Less,
                    (BinaryOp::LessThanOrEqual, Some(order)) => order != Ordering::Greater,
                    (BinaryOp::GreaterThan, Some(order)) => order == Ordering::Greater,
                    (BinaryOp::GreaterThanOrEqual, Some(order)) => order != Ordering::Less,
                    _ => unreachable!(),
                };
                Ok(Value::boolean(result))
            }
            BinaryOp::InstanceOf => self.instance_of(left, right).map(Value::boolean),
            BinaryOp::In => {
                let key = self.observable_property_key(left)?;
                self.internal_has_property(right, &key).map(Value::boolean)
            }
            BinaryOp::Add => self.add(left, right),
            BinaryOp::Subtract
            | BinaryOp::Multiply
            | BinaryOp::Divide
            | BinaryOp::Remainder
            | BinaryOp::Exponent
            | BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
            | BinaryOp::UnsignedShiftRight => self.numeric_binary(op, left, right),
        }
    }

    fn add(&mut self, left: Value, right: Value) -> Result<Value, EvalFailure> {
        let left = self.coerce_primitive_default(left)?;
        let right = self.coerce_primitive_default(right)?;
        let left_is_string = self.string_slot(left).is_some();
        let right_is_string = self.string_slot(right).is_some();
        if left_is_string || right_is_string {
            let left = self.coerce_string_value(left)?;
            let right = self.coerce_string_value(right)?;
            return self.concat_string_values(left, right);
        }
        if let Some(sum) = intrinsics::builtins::bigint::binary_op(
            self,
            intrinsics::builtins::bigint::BigIntBinaryOp::Add,
            left,
            right,
        )? {
            return Ok(sum);
        }
        let left = numeric_f64(self.to_number(left)?).unwrap();
        let right = numeric_f64(self.to_number(right)?).unwrap();
        Ok(number_value(left + right))
    }

    fn numeric_binary(
        &mut self,
        op: BinaryOp,
        left: Value,
        right: Value,
    ) -> Result<Value, EvalFailure> {
        // ToNumeric, left first: an object operand runs its `valueOf` here, and
        // the operator only ever sees primitives after this.
        let left = self.coerce_primitive_observable(left, false)?;
        let right = self.coerce_primitive_observable(right, false)?;
        if let Some(result) =
            intrinsics::builtins::bigint::binary_op(self, bigint_binary_op(op), left, right)?
        {
            return Ok(result);
        }
        let left = numeric_f64(self.to_number(left)?).unwrap();
        let right = numeric_f64(self.to_number(right)?).unwrap();
        let value = match op {
            BinaryOp::Subtract => number_value(left - right),
            BinaryOp::Multiply => number_value(left * right),
            BinaryOp::Divide => Value::number(left / right),
            BinaryOp::Remainder => Value::number(left % right),
            BinaryOp::Exponent => Value::number(number_exponentiate(left, right)),
            BinaryOp::BitAnd => Value::int32((to_int32(left) & to_int32(right)) as u32),
            BinaryOp::BitOr => Value::int32((to_int32(left) | to_int32(right)) as u32),
            BinaryOp::BitXor => Value::int32((to_int32(left) ^ to_int32(right)) as u32),
            BinaryOp::ShiftLeft => {
                Value::int32(to_int32(left).wrapping_shl(to_uint32(right) & 31) as u32)
            }
            BinaryOp::ShiftRight => {
                Value::int32((to_int32(left) >> (to_uint32(right) & 31)) as u32)
            }
            BinaryOp::UnsignedShiftRight => {
                number_value((to_uint32(left) >> (to_uint32(right) & 31)) as f64)
            }
            _ => unreachable!("numeric binary operator partition"),
        };
        Ok(value)
    }

    fn coercion_is_primitive(&self, value: Value) -> Result<bool, EvalFailure> {
        let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? else {
            return Ok(true);
        };
        Ok(matches!(
            self.heap[index],
            HeapEntry::String(_)
                | HeapEntry::Rope { .. }
                | HeapEntry::BigInt(_)
                | HeapEntry::Symbol { .. }
                | HeapEntry::PrivateName { .. }
        ))
    }

    pub(crate) fn coerce_primitive_default(&mut self, value: Value) -> Result<Value, EvalFailure> {
        self.coerce_primitive_with_hint(value, "default", false)
    }

    pub(crate) fn coerce_primitive_observable(
        &mut self,
        value: Value,
        prefer_string: bool,
    ) -> Result<Value, EvalFailure> {
        let hint = if prefer_string { "string" } else { "number" };
        self.coerce_primitive_with_hint(value, hint, prefer_string)
    }

    /// ToPrimitive. `hint` is what a `Symbol.toPrimitive` method receives, and
    /// `prefer_string` orders the two ordinary methods when there is none.
    fn coerce_primitive_with_hint(
        &mut self,
        value: Value,
        hint: &str,
        prefer_string: bool,
    ) -> Result<Value, EvalFailure> {
        if self.coercion_is_primitive(value)? {
            return Ok(value);
        }
        let key = self.property_key_from_value(self.intrinsics.builtins.symbol_to_primitive())?;
        let exotic = self.get_property_key(value, &key)?;
        if !matches!(exotic.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            if !self.is_callable(exotic)? {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "Symbol.toPrimitive is not a function",
                }));
            }
            let hint = self
                .allocate(HeapEntry::String(EcmaString::encode(hint)))
                .map_err(EvalFailure::Runtime)?;
            let primitive = self.call_value(exotic, value, &[hint])?;
            if self.coercion_is_primitive(primitive)? {
                return Ok(primitive);
            }
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "Symbol.toPrimitive returned an object",
            }));
        }
        self.ordinary_to_primitive(value, prefer_string)
    }

    /// `OrdinaryToPrimitive`: the two ordinary methods, in hint order.
    pub(crate) fn ordinary_to_primitive(
        &mut self,
        value: Value,
        prefer_string: bool,
    ) -> Result<Value, EvalFailure> {
        let methods = if prefer_string {
            ["toString", "valueOf"]
        } else {
            ["valueOf", "toString"]
        };
        for name in methods {
            let method = self.get_named_property(value, name)?;
            if !self.is_callable(method)? {
                continue;
            }
            let primitive = self.call_value(method, value, &[])?;
            if self.coercion_is_primitive(primitive)? {
                return Ok(primitive);
            }
        }
        Err(EvalFailure::Throw(ThrowOrigin::TypeError {
            operation: "cannot convert object to primitive",
        }))
    }

    pub(crate) fn coerce_string_observable(
        &mut self,
        value: Value,
    ) -> Result<EcmaString, EvalFailure> {
        let primitive = self.coerce_primitive_observable(value, true)?;
        self.to_string(primitive)
    }

    /// Coerces a primitive to a string value, keeping an existing string or
    /// rope instead of reallocating its text.
    pub(crate) fn coerce_string_value(&mut self, value: Value) -> Result<Value, EvalFailure> {
        if self.string_slot(value).is_some() {
            return Ok(value);
        }
        let text = self.to_string(value)?;
        self.allocate(HeapEntry::String(text))
            .map_err(EvalFailure::Runtime)
    }

    /// Concatenates two string values. An empty operand yields the other
    /// value, and a result of `ROPE_MIN_UNITS` or more keeps its halves.
    pub(crate) fn concat_string_values(
        &mut self,
        left: Value,
        right: Value,
    ) -> Result<Value, EvalFailure> {
        let left_len =
            u32::try_from(self.string_len(self.string_slot(left).expect("left is a string")))
                .expect("a string length fits in u32");
        let right_len =
            u32::try_from(self.string_len(self.string_slot(right).expect("right is a string")))
                .expect("a string length fits in u32");
        if left_len == 0 {
            return Ok(right);
        }
        if right_len == 0 {
            return Ok(left);
        }
        let len = left_len.checked_add(right_len).ok_or(EvalFailure::Runtime(
            RuntimeErrorKind::HeapByteLimitExceeded {
                limit: self.limits.max_heap_bytes,
            },
        ))?;
        if len >= ROPE_MIN_UNITS {
            self.ensure_allocation_capacity(1, (len as usize).saturating_mul(2))
                .map_err(EvalFailure::Runtime)?;
            return self
                .allocate(HeapEntry::Rope { left, right, len })
                .map_err(EvalFailure::Runtime);
        }
        let left_slot = self.string_slot(left).expect("left is a string");
        let right_slot = self.string_slot(right).expect("right is a string");
        let left_text = self.flat_string(left_slot);
        let right_text = self.flat_string(right_slot);
        let mut builder = EcmaStringBuilder::with_capacity(len as usize);
        for &unit in left_text.as_units() {
            builder.push_unit(unit);
        }
        for &unit in right_text.as_units() {
            builder.push_unit(unit);
        }
        self.allocate(HeapEntry::String(builder.finish()))
            .map_err(EvalFailure::Runtime)
    }

    pub(crate) fn coerce_number_observable(&mut self, value: Value) -> Result<Value, EvalFailure> {
        let primitive = self.coerce_primitive_observable(value, false)?;
        self.to_number(primitive)
    }

    #[expect(
        clippy::wrong_self_convention,
        reason = "ToNumber flattens rope operands, which needs the machine mutably"
    )]
    fn to_number(&mut self, value: Value) -> Result<Value, EvalFailure> {
        if let Some(index) = self.string_slot(value) {
            let text = self.flat_string(index);
            return Ok(number_value(parse_number(&text)));
        }
        if let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
            let elements = match &self.heap[index] {
                HeapEntry::Array { elements, .. } => Some(elements.clone()),
                _ => None,
            };
            if let Some(elements) = elements {
                return match elements.len() {
                    0 => Ok(Value::int32(0)),
                    1 => self.to_number(elements[0]),
                    _ => Ok(Value::number(f64::NAN)),
                };
            }
        }
        match value.decode() {
            Some(Decoded::Number(_)) | Some(Decoded::Int32(_)) => self.to_primitive(value),
            Some(Decoded::Undefined) => Ok(Value::number(f64::NAN)),
            Some(Decoded::Null) => Ok(Value::int32(0)),
            Some(Decoded::Boolean(value)) => Ok(Value::int32(u32::from(value))),
            Some(Decoded::Hole) | Some(Decoded::Uninitialized) => Ok(Value::number(f64::NAN)),
            Some(Decoded::HeapRef(_)) => {
                match self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
                    Some(index) => match &self.heap[index] {
                        HeapEntry::String(_) | HeapEntry::Rope { .. } => {
                            unreachable!("string values coerce before the heap match")
                        }
                        HeapEntry::Array { .. } => {
                            unreachable!("array values coerce before the heap match")
                        }
                        HeapEntry::BigInt(_) => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                            operation: "convert bigint to number",
                        })),
                        HeapEntry::Proxy { .. } | HeapEntry::ProxyRevoker { .. } => {
                            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "convert proxy to number",
                            }))
                        }
                        HeapEntry::Symbol { .. } | HeapEntry::PrivateName { .. } => {
                            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "convert symbol to number",
                            }))
                        }
                        HeapEntry::Object { .. }
                        | HeapEntry::Generator { .. }
                        | HeapEntry::AsyncGenerator { .. }
                        | HeapEntry::AsyncFromSync { .. }
                        | HeapEntry::Script { .. }
                        | HeapEntry::Function { .. }
                        | HeapEntry::ModuleNamespace { .. }
                        | HeapEntry::ExternalModuleNamespace { .. }
                        | HeapEntry::HashState { .. }
                        | HeapEntry::NativeFunction { .. }
                        | HeapEntry::RegExp { .. }
                        | HeapEntry::Date { .. }
                        | HeapEntry::Temporal { .. }
                        | HeapEntry::Intl { .. }
                        | HeapEntry::BuiltinIterator { .. }
                        | HeapEntry::Collection { .. }
                        | HeapEntry::TypedArray { .. }
                        | HeapEntry::ArrayBuffer { .. }
                        | HeapEntry::SharedArrayBuffer { .. }
                        | HeapEntry::DataView { .. }
                        | HeapEntry::Promise { .. }
                        | HeapEntry::DisposableStack { .. }
                        | HeapEntry::PromiseResolver { .. }
                        | HeapEntry::PromiseAll { .. }
                        | HeapEntry::AsyncActivation { .. }
                        | HeapEntry::PromiseAllElement { .. }
                        | HeapEntry::ProcessEnv { .. }
                        | HeapEntry::Iterator { .. }
                        | HeapEntry::Timeout { .. }
                        | HeapEntry::WeakRef { .. }
                        | HeapEntry::FinalizationRegistry { .. } => Ok(Value::number(f64::NAN)),
                        HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
                    },
                    None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "coerce host object to number",
                    })),
                }
            }
            None => Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value,
            })),
        }
    }

    fn truthy(&self, value: Value) -> bool {
        match value.decode() {
            Some(Decoded::Number(number)) => number != 0.0 && !number.is_nan(),
            Some(Decoded::Int32(value)) => value != 0,
            Some(Decoded::Undefined | Decoded::Null | Decoded::Hole | Decoded::Uninitialized)
            | None => false,
            Some(Decoded::Boolean(value)) => value,
            Some(Decoded::HeapRef(_)) => match self.runtime_slot(value) {
                Ok(Some(index)) => match &self.heap[index] {
                    HeapEntry::String(text) => !text.is_empty(),
                    HeapEntry::Rope { len, .. } => *len != 0,
                    HeapEntry::BigInt(text) => text != "0",
                    HeapEntry::Object { .. }
                    | HeapEntry::Generator { .. }
                    | HeapEntry::AsyncGenerator { .. }
                    | HeapEntry::AsyncFromSync { .. }
                    | HeapEntry::Script { .. }
                    | HeapEntry::Array { .. }
                    | HeapEntry::Function { .. }
                    | HeapEntry::ModuleNamespace { .. }
                    | HeapEntry::ExternalModuleNamespace { .. }
                    | HeapEntry::HashState { .. }
                    | HeapEntry::NativeFunction { .. }
                    | HeapEntry::Symbol { .. }
                    | HeapEntry::PrivateName { .. }
                    | HeapEntry::RegExp { .. }
                    | HeapEntry::Date { .. }
                    | HeapEntry::Temporal { .. }
                    | HeapEntry::Intl { .. }
                    | HeapEntry::BuiltinIterator { .. }
                    | HeapEntry::Collection { .. }
                    | HeapEntry::TypedArray { .. }
                    | HeapEntry::ArrayBuffer { .. }
                    | HeapEntry::SharedArrayBuffer { .. }
                    | HeapEntry::DataView { .. }
                    | HeapEntry::Promise { .. }
                    | HeapEntry::DisposableStack { .. }
                    | HeapEntry::PromiseResolver { .. }
                    | HeapEntry::PromiseAll { .. }
                    | HeapEntry::AsyncActivation { .. }
                    | HeapEntry::PromiseAllElement { .. }
                    | HeapEntry::ProcessEnv { .. }
                    | HeapEntry::Iterator { .. }
                    | HeapEntry::Timeout { .. }
                    | HeapEntry::WeakRef { .. }
                    | HeapEntry::FinalizationRegistry { .. }
                    | HeapEntry::Proxy { .. }
                    | HeapEntry::ProxyRevoker { .. } => true,
                    HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
                },
                Ok(None) => true,
                Err(_) => false,
            },
        }
    }

    fn type_of(&self, value: Value) -> &'static str {
        match value.decode() {
            Some(Decoded::Undefined | Decoded::Hole | Decoded::Uninitialized) | None => "undefined",
            Some(Decoded::Number(_) | Decoded::Int32(_)) => "number",
            Some(Decoded::Null) => "object",
            Some(Decoded::Boolean(_)) => "boolean",
            Some(Decoded::HeapRef(_)) => match self.runtime_slot(value) {
                Ok(Some(index)) => match &self.heap[index] {
                    HeapEntry::String(_) | HeapEntry::Rope { .. } => "string",
                    HeapEntry::BigInt(_) => "bigint",
                    HeapEntry::Function { .. } | HeapEntry::NativeFunction { .. } => "function",
                    HeapEntry::Symbol { .. } => "symbol",
                    HeapEntry::PrivateName { .. } => "object",
                    HeapEntry::Proxy { .. } => {
                        if self.is_callable(value).unwrap_or(false) {
                            "function"
                        } else {
                            "object"
                        }
                    }
                    HeapEntry::ProxyRevoker { .. } => "function",
                    HeapEntry::Object { .. }
                    | HeapEntry::Generator { .. }
                    | HeapEntry::AsyncGenerator { .. }
                    | HeapEntry::AsyncFromSync { .. }
                    | HeapEntry::Script { .. }
                    | HeapEntry::Array { .. }
                    | HeapEntry::ModuleNamespace { .. }
                    | HeapEntry::ExternalModuleNamespace { .. }
                    | HeapEntry::HashState { .. }
                    | HeapEntry::RegExp { .. }
                    | HeapEntry::Date { .. }
                    | HeapEntry::Temporal { .. }
                    | HeapEntry::Intl { .. }
                    | HeapEntry::BuiltinIterator { .. }
                    | HeapEntry::Collection { .. }
                    | HeapEntry::TypedArray { .. }
                    | HeapEntry::ArrayBuffer { .. }
                    | HeapEntry::SharedArrayBuffer { .. }
                    | HeapEntry::DataView { .. }
                    | HeapEntry::Promise { .. }
                    | HeapEntry::DisposableStack { .. }
                    | HeapEntry::PromiseResolver { .. }
                    | HeapEntry::PromiseAll { .. }
                    | HeapEntry::AsyncActivation { .. }
                    | HeapEntry::PromiseAllElement { .. }
                    | HeapEntry::ProcessEnv { .. }
                    | HeapEntry::Iterator { .. }
                    | HeapEntry::Timeout { .. }
                    | HeapEntry::WeakRef { .. }
                    | HeapEntry::FinalizationRegistry { .. } => "object",
                    HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
                },
                _ => "object",
            },
        }
    }

    fn strict_equal(&mut self, left: Value, right: Value) -> bool {
        match (left.decode(), right.decode()) {
            (Some(Decoded::Number(a)), Some(Decoded::Number(b))) => a == b,
            (Some(Decoded::Number(a)), Some(Decoded::Int32(b)))
            | (Some(Decoded::Int32(b)), Some(Decoded::Number(a))) => a == f64::from(b as i32),
            (Some(Decoded::Int32(a)), Some(Decoded::Int32(b))) => a == b,
            (Some(Decoded::HeapRef(_)), Some(Decoded::HeapRef(_))) => {
                let (left_slot, right_slot) =
                    match (self.runtime_slot(left), self.runtime_slot(right)) {
                        (Ok(Some(a)), Ok(Some(b))) => (a, b),
                        _ => return left == right,
                    };
                if let (Some(a), Some(b)) = (self.string_slot(left), self.string_slot(right)) {
                    return self.flat_string(a) == self.flat_string(b);
                }
                match (&self.heap[left_slot], &self.heap[right_slot]) {
                    (HeapEntry::BigInt(a), HeapEntry::BigInt(b)) => a == b,
                    _ => left == right,
                }
            }
            _ => left == right,
        }
    }

    fn abstract_equal(&mut self, left: Value, right: Value) -> Result<bool, EvalFailure> {
        if self.strict_equal(left, right) {
            return Ok(true);
        }
        let left_nullish = matches!(
            left.decode(),
            Some(Decoded::Null | Decoded::Undefined | Decoded::Hole | Decoded::Uninitialized)
                | None
        );
        let right_nullish = matches!(
            right.decode(),
            Some(Decoded::Null | Decoded::Undefined | Decoded::Hole | Decoded::Uninitialized)
                | None
        );
        if left_nullish || right_nullish {
            return Ok(left_nullish && right_nullish);
        }
        let left_object = self.is_object(left);
        let right_object = self.is_object(right);
        if left_object && !right_object {
            let primitive = self.coerce_primitive_default(left)?;
            return self.abstract_equal(primitive, right);
        }
        if !left_object && right_object {
            let primitive = self.coerce_primitive_default(right)?;
            return self.abstract_equal(left, primitive);
        }
        if let Some(equal) = intrinsics::builtins::bigint::loose_equals(self, left, right)? {
            return Ok(equal);
        }
        let left_number = self.to_number(left);
        let right_number = self.to_number(right);
        match (left_number, right_number) {
            (Ok(left), Ok(right)) => Ok(numeric_f64(left).unwrap() == numeric_f64(right).unwrap()),
            _ => Ok(false),
        }
    }

    fn relational_compare(
        &mut self,
        left: Value,
        right: Value,
    ) -> Result<Option<Ordering>, EvalFailure> {
        let left = self.coerce_primitive_observable(left, false)?;
        let right = self.coerce_primitive_observable(right, false)?;
        if let (Some(left), Some(right)) = (self.string_text(left), self.string_text(right)) {
            return Ok(Some(left.cmp(&right)));
        }
        if let Some(ordering) = intrinsics::builtins::bigint::compare(self, left, right)? {
            return Ok(ordering);
        }
        let left = numeric_f64(self.to_number(left)?).unwrap();
        let right = numeric_f64(self.to_number(right)?).unwrap();
        Ok(left.partial_cmp(&right))
    }

    /// `value instanceof constructor` per ECMA-262 §13.10.3 InstanceofOperator.
    ///
    /// The right-hand side is first consulted for a callable
    /// `Symbol.hasInstance`; when present and callable it is called with
    /// `value` and its result coerced to boolean. Only when `@@hasInstance`
    /// is absent (or nullish) does the operator fall back to the ordinary
    /// prototype-chain check. A present-but-non-callable handler is a
    /// TypeError, matching `GetMethod`.
    fn instance_of(&mut self, value: Value, constructor: Value) -> Result<bool, EvalFailure> {
        if !self.is_object(constructor) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "instanceof",
            }));
        }
        let key = self.has_instance_key()?;
        let handler = self.get_property_key(constructor, &key)?;
        if matches!(handler.decode(), Some(Decoded::Undefined | Decoded::Null)) {
            if !self.is_callable(constructor)? {
                return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                    operation: "instanceof",
                }));
            }
            return self.ordinary_has_instance(value, constructor);
        }
        // GetMethod: a present, non-nullish handler must be callable.
        if !self.is_callable(handler)? {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "instanceof Symbol.hasInstance is not callable",
            }));
        }
        let result = self.call_value(handler, constructor, &[value])?;
        Ok(self.to_boolean(result))
    }

    /// `OrdinaryHasInstance` (ECMA-262 §7.3.20): walks `value`'s prototype
    /// chain for the constructor's own `prototype` object, matching by heap
    /// identity. A bound function defers to `instanceof` on its target, and a
    /// non-callable receiver is simply not a constructor of anything.
    fn ordinary_has_instance(
        &mut self,
        value: Value,
        constructor: Value,
    ) -> Result<bool, EvalFailure> {
        if !self.is_callable(constructor)? {
            return Ok(false);
        }
        if let Some(index) = self
            .runtime_slot(constructor)
            .map_err(EvalFailure::Runtime)?
            && let HeapEntry::NativeFunction {
                callable: NativeCallable::Bound(bound),
                ..
            } = &self.heap[index]
        {
            let target = bound.target;
            return self.instance_of(value, target);
        }
        if !self.is_object(value) {
            return Ok(false);
        }
        let prototype_key = PropertyKey::Named(self.intern_str("prototype"));
        let prototype = self.internal_get(constructor, &prototype_key, constructor)?;
        if !self.is_object(prototype) {
            return Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                operation: "instanceof prototype is not an object",
            }));
        }
        let target_slot = self.runtime_slot(prototype).map_err(EvalFailure::Runtime)?;
        let mut node = match self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
            Some(node) => node,
            None => return Ok(false),
        };
        let mut guard = 0;
        loop {
            if Some(node) == target_slot {
                return Ok(true);
            }
            match self.internal_get_prototype_of(self.value_for_runtime_index(node)?)? {
                Some(next) => {
                    node = self
                        .runtime_slot(next)
                        .map_err(EvalFailure::Runtime)?
                        .ok_or(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                            value: next,
                        }))?;
                    guard += 1;
                    if guard > self.heap.len() + 1 {
                        return Ok(false);
                    }
                }
                None => return Ok(false),
            }
        }
    }

    /// Resolves and caches the `PropertyKey` for the well-known
    /// `Symbol.hasInstance` symbol. The symbol is a read-only,
    /// non-configurable property of the `Symbol` constructor installed once
    /// during intrinsic initialization, so its heap index is stable for the
    /// machine's lifetime; caching it keeps the per-`instanceof` cost to the
    /// single property lookup the spec requires rather than re-deriving the
    /// symbol key on every call.
    fn has_instance_key(&mut self) -> Result<PropertyKey, EvalFailure> {
        if let Some(index) = self.has_instance_symbol {
            return Ok(PropertyKey::Symbol(index));
        }
        let symbol_constructor = self
            .intrinsics
            .global("Symbol")
            .expect("Symbol intrinsics install before instanceof");
        let index = self
            .runtime_slot(symbol_constructor)
            .map_err(EvalFailure::Runtime)?
            .expect("Symbol constructor is an engine object");
        let has_instance = self.intern_str("hasInstance");
        let symbol = match self.own_get_atom(index, has_instance) {
            Some(Found::Value(value)) => value,
            _ => unreachable!("Symbol.hasInstance is a readonly data property"),
        };
        let symbol_index = self
            .runtime_slot(symbol)
            .map_err(EvalFailure::Runtime)?
            .expect("Symbol.hasInstance is an engine symbol") as u32;
        self.has_instance_symbol = Some(symbol_index);
        Ok(PropertyKey::Symbol(symbol_index))
    }

    fn value_to_string(&mut self, value: Value, depth: usize) -> Result<EcmaString, EvalFailure> {
        if depth >= 32 {
            return Ok(EcmaString::default());
        }
        if let Some(index) = self.string_slot(value) {
            return Ok(self.flat_string(index));
        }
        if let Some(index) = self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
            let elements = match &self.heap[index] {
                HeapEntry::Array { elements, .. } => Some(elements.clone()),
                _ => None,
            };
            if let Some(elements) = elements {
                let mut text = EcmaStringBuilder::new();
                for (position, element) in elements.iter().copied().enumerate() {
                    if position != 0 {
                        text.push_unit(u16::from(b','));
                    }
                    if element != Value::HOLE
                        && element != Value::NULL
                        && element != Value::UNDEFINED
                    {
                        for &unit in self.value_to_string(element, depth + 1)?.as_units() {
                            text.push_unit(unit);
                        }
                    }
                }
                return Ok(text.finish());
            }
        }
        let ascii = |text: String| EcmaString::encode(&text);
        match value.decode() {
            Some(Decoded::Number(number)) => Ok(ascii(Self::ordinary_number_to_string(number))),
            Some(Decoded::Int32(raw)) => Ok(ascii((raw as i32).to_string())),
            Some(Decoded::Undefined | Decoded::Uninitialized) => {
                Ok(EcmaString::encode("undefined"))
            }
            Some(Decoded::Null) => Ok(EcmaString::encode("null")),
            Some(Decoded::Boolean(value)) => {
                Ok(EcmaString::encode(if value { "true" } else { "false" }))
            }
            Some(Decoded::Hole) => Ok(EcmaString::default()),
            Some(Decoded::HeapRef(_)) => {
                match self.runtime_slot(value).map_err(EvalFailure::Runtime)? {
                    Some(index) => match &self.heap[index] {
                        HeapEntry::String(_) | HeapEntry::Rope { .. } => {
                            unreachable!("string values convert before the heap match")
                        }
                        HeapEntry::BigInt(text) => Ok(EcmaString::encode(text)),
                        HeapEntry::Proxy { .. } => Ok(EcmaString::encode("[object Object]")),
                        HeapEntry::ProxyRevoker { .. } => {
                            Ok(EcmaString::encode("function () { [native code] }"))
                        }
                        HeapEntry::Object { .. }
                        | HeapEntry::Generator { .. }
                        | HeapEntry::AsyncGenerator { .. }
                        | HeapEntry::AsyncFromSync { .. }
                        | HeapEntry::Script { .. }
                        | HeapEntry::Date { .. }
                        | HeapEntry::Temporal { .. }
                        | HeapEntry::Intl { .. }
                        | HeapEntry::BuiltinIterator { .. }
                        | HeapEntry::Collection { .. }
                        | HeapEntry::TypedArray { .. }
                        | HeapEntry::ArrayBuffer { .. }
                        | HeapEntry::SharedArrayBuffer { .. }
                        | HeapEntry::DataView { .. }
                        | HeapEntry::Promise { .. }
                        | HeapEntry::DisposableStack { .. }
                        | HeapEntry::PromiseResolver { .. }
                        | HeapEntry::PromiseAll { .. }
                        | HeapEntry::AsyncActivation { .. }
                        | HeapEntry::PromiseAllElement { .. }
                        | HeapEntry::ModuleNamespace { .. }
                        | HeapEntry::ExternalModuleNamespace { .. }
                        | HeapEntry::ProcessEnv { .. }
                        | HeapEntry::Iterator { .. }
                        | HeapEntry::Timeout { .. }
                        | HeapEntry::HashState { .. }
                        | HeapEntry::WeakRef { .. }
                        | HeapEntry::FinalizationRegistry { .. } => {
                            Ok(EcmaString::encode("[object Object]"))
                        }
                        HeapEntry::RegExp { pattern, flags, .. } => {
                            let mut builder = EcmaStringBuilder::with_capacity(
                                pattern
                                    .len_units()
                                    .saturating_add(flags.len_units())
                                    .saturating_add(2),
                            );
                            builder.push_unit(u16::from(b'/'));
                            for &unit in pattern.as_units() {
                                builder.push_unit(unit);
                            }
                            builder.push_unit(u16::from(b'/'));
                            for &unit in flags.as_units() {
                                builder.push_unit(unit);
                            }
                            Ok(builder.finish())
                        }
                        HeapEntry::Symbol { .. } => {
                            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "convert symbol to string",
                            }))
                        }
                        HeapEntry::PrivateName { .. } => {
                            Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                                operation: "convert private name to string",
                            }))
                        }
                        HeapEntry::Function {
                            module, function, ..
                        } => {
                            let flags = self.module_code(*module).functions()
                                [function.get() as usize]
                                .flags();
                            Ok(EcmaString::encode(
                                match (flags.is_async, flags.is_generator) {
                                    (true, true) => "async function* () { [bytecode] }",
                                    (true, false) => "async function () { [bytecode] }",
                                    (false, true) => "function* () { [bytecode] }",
                                    (false, false) => "function () { [bytecode] }",
                                },
                            ))
                        }
                        HeapEntry::NativeFunction { .. } => {
                            Ok(EcmaString::encode("function () { [native code] }"))
                        }
                        HeapEntry::Array { .. } => {
                            unreachable!("array values convert before the heap match")
                        }
                        HeapEntry::Vacant => unreachable!("runtime_slot rejects vacant slots"),
                    },
                    None => Err(EvalFailure::Throw(ThrowOrigin::TypeError {
                        operation: "coerce host object to string",
                    })),
                }
            }
            None => Err(EvalFailure::Runtime(RuntimeErrorKind::InvalidValue {
                value,
            })),
        }
    }

    fn string_text(&mut self, value: Value) -> Option<EcmaString> {
        let index = self.string_slot(value)?;
        Some(self.flat_string(index))
    }

    fn is_object(&self, value: Value) -> bool {
        match self.runtime_slot(value) {
            Ok(Some(index)) => !matches!(
                self.heap[index],
                HeapEntry::String(_)
                    | HeapEntry::Rope { .. }
                    | HeapEntry::BigInt(_)
                    | HeapEntry::Symbol { .. }
                    | HeapEntry::PrivateName { .. }
                    | HeapEntry::PromiseResolver { .. }
                    | HeapEntry::PromiseAll { .. }
                    | HeapEntry::AsyncActivation { .. }
                    | HeapEntry::PromiseAllElement { .. }
            ),
            Ok(None) => matches!(value.decode(), Some(Decoded::HeapRef(_))),
            Err(_) => false,
        }
    }
}

fn ordered_property_keys(
    properties: &PropertyMap,
    shapes: &ShapeTable,
    atoms: &AtomTable,
) -> Vec<PropertyKey> {
    let mut indices = Vec::new();
    let mut strings = Vec::new();
    let mut symbols = Vec::new();
    for (key, _) in properties.iter(shapes) {
        match key {
            PropertyKey::Named(atom) => match atoms.array_index(*atom) {
                Some(index) => indices.push((index, key.clone())),
                None => strings.push(key.clone()),
            },
            PropertyKey::Symbol(_) => symbols.push(key.clone()),
            PropertyKey::Private(_) => {}
        }
    }
    indices.sort_unstable_by_key(|(index, _)| *index);
    indices
        .into_iter()
        .map(|(_, key)| key)
        .chain(strings)
        .chain(symbols)
        .collect()
}

fn property_lookup(
    properties: &PropertyMap,
    shapes: &ShapeTable,
    key: &PropertyKey,
) -> Option<Found> {
    match properties.get(shapes, key) {
        Some(Property::Data { value, .. }) => Some(Found::Value(*value)),
        Some(Property::Accessor { getter, .. }) => Some(match getter {
            Some(getter) => Found::Getter(*getter),
            None => Found::NoGetter,
        }),
        None => None,
    }
}

fn innermost_handler(function: &Function, pc: usize) -> Option<bamts_bytecode::ExceptionHandler> {
    function
        .handlers()
        .iter()
        .copied()
        .filter(|handler| handler.start.get() as usize <= pc && pc < handler.end.get() as usize)
        .max_by(|left, right| {
            left.start
                .get()
                .cmp(&right.start.get())
                .then_with(|| right.end.get().cmp(&left.end.get()))
        })
}

/// The catch-value guard shared by the interpreter and the native engine:
/// bytecode throws and already-materialized (non-`UNDEFINED`) engine values
/// keep their identity; only a still-lazy (`UNDEFINED`) non-bytecode origin is
/// materialized into a realm-intrinsic error object at the catch boundary.
pub(crate) fn catch_value_needs_materialization(value: Value, origin: ThrowOrigin) -> bool {
    !matches!(origin, ThrowOrigin::Bytecode) && value == Value::UNDEFINED
}

fn numeric_f64(value: Value) -> Option<f64> {
    match value.decode()? {
        Decoded::Number(number) => Some(number),
        Decoded::Int32(raw) => Some(f64::from(raw as i32)),
        _ => None,
    }
}

/// What an error object stores under the `[[ErrorData]]` brand key.
fn error_brand() -> Property {
    Property::Data {
        value: Value::TRUE,
        writable: false,
        enumerable: false,
        configurable: false,
    }
}

/// The compact encoding for a whole Number. `-0` stays a double: Int32 has no
/// negative zero, and `1 / -0` and `Object.is` can both tell the difference.
fn number_value(number: f64) -> Value {
    // An int32 has no negative zero, so that one integral value stays a double.
    if number.is_finite()
        && number.fract() == 0.0
        && number >= f64::from(i32::MIN)
        && number <= f64::from(i32::MAX)
        && !(number == 0.0 && number.is_sign_negative())
    {
        Value::int32(number as i32 as u32)
    } else {
        Value::number(number)
    }
}

/// `Number::exponentiate`, which differs from `powf` for a base of 1 or -1 and a
/// NaN or infinite exponent.
pub(crate) fn number_exponentiate(base: f64, exponent: f64) -> f64 {
    if exponent.is_nan() || (base.abs() == 1.0 && exponent.is_infinite()) {
        f64::NAN
    } else {
        base.powf(exponent)
    }
}

fn parse_number(text: &EcmaString) -> f64 {
    let Ok(text) = text.to_utf8_strict() else {
        return f64::NAN;
    };
    intrinsics::builtins::string_to_number(&text)
}

fn to_uint32(number: f64) -> u32 {
    if !number.is_finite() || number == 0.0 {
        0
    } else {
        number.trunc().rem_euclid(4_294_967_296.0) as u32
    }
}

fn to_int32(number: f64) -> i32 {
    to_uint32(number) as i32
}

fn array_index_ascii(key: &str) -> Option<u32> {
    if !key.is_ascii() || key.is_empty() || (key.len() > 1 && key.as_bytes()[0] == b'0') {
        return None;
    }
    let mut index = 0_u32;
    for byte in key.bytes() {
        if !byte.is_ascii_digit() {
            return None;
        }
        index = index.checked_mul(10)?.checked_add(u32::from(byte - b'0'))?;
    }
    (index != u32::MAX).then_some(index)
}

fn array_index(key: &EcmaString) -> Option<u32> {
    let units = key.as_units();
    if units.is_empty() || (units.len() > 1 && units[0] == u16::from(b'0')) {
        return None;
    }
    let mut index = 0_u32;
    for &unit in units {
        if !(u16::from(b'0')..=u16::from(b'9')).contains(&unit) {
            return None;
        }
        index = index
            .checked_mul(10)?
            .checked_add(u32::from(unit - u16::from(b'0')))?;
    }
    (index != u32::MAX).then_some(index)
}

fn string_has_index(text: &EcmaString, atoms: &AtomTable, key: &PropertyKey) -> bool {
    match key {
        PropertyKey::Named(atom) => atoms
            .array_index(*atom)
            .is_some_and(|offset| (offset as usize) < text.len_units()),
        _ => false,
    }
}
fn string_own_get(text: &EcmaString, atoms: &AtomTable, key: &PropertyKey) -> Option<Found> {
    let PropertyKey::Named(atom) = key else {
        return None;
    };
    let name = atoms.utf8(*atom)?;
    string_own_get_ascii(text, name)
}

fn string_own_get_ascii(text: &EcmaString, name: &str) -> Option<Found> {
    if name == "length" {
        return Some(Found::Value(number_value(text.len_units() as f64)));
    }
    let offset = array_index_ascii(name)?;
    let unit = text.unit_at(offset as usize)?;
    Some(Found::Text(EcmaString::from_units(&[unit])))
}

fn exact_array_length(value: Value) -> Option<usize> {
    let number = numeric_f64(value)?;
    if number.is_finite() && number >= 0.0 && number.fract() == 0.0 && number <= u32::MAX as f64 {
        Some(number as usize)
    } else {
        None
    }
}

/// Resizes to `length`, stopping above the highest non-configurable element, and
/// says whether the whole of `length` was reached.
pub(crate) fn apply_array_length(
    kind: &mut ArrayElementKind,
    elements: &mut Vec<Value>,
    properties: &mut PropertyMap,
    atoms: &AtomTable,
    length: usize,
    shapes: &ShapeTable,
) -> bool {
    let grew = length > elements.len();
    if length >= elements.len() {
        elements.resize(length, Value::HOLE);
        if grew {
            *kind = kind.including(Value::HOLE);
        }
        debug_assert!(kind.matches(elements));
        return true;
    }
    let blocked = properties
        .iter(shapes)
        .filter_map(|(key, property)| {
            (!property.configurable())
                .then(|| key.as_string(atoms).and_then(array_index))
                .flatten()
        })
        .map(|offset| offset as usize)
        .filter(|offset| *offset >= length)
        .max();
    let effective_length = blocked.map_or(length, |offset| offset + 1);
    properties.retain(shapes, |key, _| {
        key.as_string(atoms)
            .and_then(array_index)
            .is_none_or(|offset| (offset as usize) < effective_length)
    });
    elements.resize(effective_length, Value::HOLE);
    debug_assert!(kind.matches(elements));
    blocked.is_none()
}

pub(crate) fn array_set_length(
    vector: ArrayVector<'_>,
    properties: &mut PropertyMap,
    atoms: &AtomTable,
    length_writable: bool,
    value: Value,
    operation: &'static str,
    shapes: &ShapeTable,
) -> Result<(), EvalFailure> {
    let length = exact_array_length(value)
        .ok_or(EvalFailure::Throw(ThrowOrigin::RangeError { operation }))?;
    if !length_writable {
        return Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }));
    }
    if apply_array_length(
        vector.kind,
        vector.elements,
        properties,
        atoms,
        length,
        shapes,
    ) {
        Ok(())
    } else {
        Err(EvalFailure::Throw(ThrowOrigin::TypeError { operation }))
    }
}

fn bigint_binary_op(op: BinaryOp) -> intrinsics::builtins::bigint::BigIntBinaryOp {
    use intrinsics::builtins::bigint::BigIntBinaryOp;

    match op {
        BinaryOp::Subtract => BigIntBinaryOp::Subtract,
        BinaryOp::Multiply => BigIntBinaryOp::Multiply,
        BinaryOp::Divide => BigIntBinaryOp::Divide,
        BinaryOp::Remainder => BigIntBinaryOp::Remainder,
        BinaryOp::Exponent => BigIntBinaryOp::Exponentiate,
        BinaryOp::BitAnd => BigIntBinaryOp::BitAnd,
        BinaryOp::BitOr => BigIntBinaryOp::BitOr,
        BinaryOp::BitXor => BigIntBinaryOp::BitXor,
        BinaryOp::ShiftLeft => BigIntBinaryOp::LeftShift,
        BinaryOp::ShiftRight => BigIntBinaryOp::RightShift,
        BinaryOp::UnsignedShiftRight => BigIntBinaryOp::UnsignedRightShift,
        _ => unreachable!("numeric binary operator partition"),
    }
}

pub(crate) fn unary_from_selector(op: u32) -> Option<UnaryOp> {
    match op {
        0 => Some(UnaryOp::Void),
        1 => Some(UnaryOp::TypeOf),
        2 => Some(UnaryOp::Plus),
        3 => Some(UnaryOp::Negate),
        4 => Some(UnaryOp::BitwiseNot),
        5 => Some(UnaryOp::LogicalNot),
        6 => Some(UnaryOp::ToString),
        7 => Some(UnaryOp::ToPropertyKey),
        _ => None,
    }
}

pub(crate) fn binary_from_selector(op: u32) -> Option<BinaryOp> {
    match op {
        0 => Some(BinaryOp::Add),
        1 => Some(BinaryOp::Subtract),
        2 => Some(BinaryOp::Multiply),
        3 => Some(BinaryOp::Divide),
        4 => Some(BinaryOp::Remainder),
        5 => Some(BinaryOp::Exponent),
        6 => Some(BinaryOp::BitAnd),
        7 => Some(BinaryOp::BitOr),
        8 => Some(BinaryOp::BitXor),
        9 => Some(BinaryOp::ShiftLeft),
        10 => Some(BinaryOp::ShiftRight),
        11 => Some(BinaryOp::UnsignedShiftRight),
        12 => Some(BinaryOp::Equal),
        13 => Some(BinaryOp::NotEqual),
        14 => Some(BinaryOp::StrictEqual),
        15 => Some(BinaryOp::StrictNotEqual),
        16 => Some(BinaryOp::LessThan),
        17 => Some(BinaryOp::LessThanOrEqual),
        18 => Some(BinaryOp::GreaterThan),
        19 => Some(BinaryOp::GreaterThanOrEqual),
        20 => Some(BinaryOp::InstanceOf),
        21 => Some(BinaryOp::In),
        _ => None,
    }
}

pub(crate) fn iterator_kind_from_selector(kind: u32) -> Option<IteratorKind> {
    match kind {
        0 => Some(IteratorKind::Sync),
        1 => Some(IteratorKind::Async),
        2 => Some(IteratorKind::Keys),
        _ => None,
    }
}

pub(crate) fn accessor_from_selector(kind: u32) -> Option<AccessorKind> {
    match kind {
        0 => Some(AccessorKind::Getter),
        1 => Some(AccessorKind::Setter),
        2 => Some(AccessorKind::ClassGetter),
        3 => Some(AccessorKind::ClassSetter),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod shape_property_tests {
    use super::*;

    struct XorShift64(u64);

    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0 | 1;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % (n as u64).max(1)) as usize
        }
    }

    struct Oracle(Vec<(PropertyKey, Property)>);

    impl Oracle {
        fn insert(&mut self, key: PropertyKey, property: Property) {
            if let Some(slot) = self.0.iter().position(|(candidate, _)| *candidate == key) {
                self.0[slot].1 = property;
            } else {
                self.0.push((key, property));
            }
        }

        fn remove(&mut self, key: &PropertyKey) {
            if let Some(slot) = self.0.iter().position(|(candidate, _)| candidate == key) {
                self.0.remove(slot);
            }
        }
    }

    fn check(map: &PropertyMap, shapes: &ShapeTable, oracle: &Oracle) {
        let live: Vec<(PropertyKey, Property)> = map
            .iter(shapes)
            .map(|(key, property)| (key.clone(), property.clone()))
            .collect();
        assert_eq!(live, oracle.0);
    }

    fn canned(rng: &mut XorShift64) -> Property {
        match rng.below(6) {
            0 => Property::Data {
                value: Value::int32(u32::try_from(rng.below(100)).expect("canned value fits u32")),
                writable: true,
                enumerable: true,
                configurable: true,
            },
            1 => Property::Data {
                value: Value::int32(u32::try_from(rng.below(100)).expect("canned value fits u32")),
                writable: false,
                enumerable: true,
                configurable: false,
            },
            2 => Property::Data {
                value: Value::TRUE,
                writable: false,
                enumerable: false,
                configurable: false,
            },
            3 => Property::Accessor {
                getter: Some(Value::int32(1)),
                setter: None,
                enumerable: true,
                configurable: true,
            },
            4 => Property::Accessor {
                getter: None,
                setter: Some(Value::int32(2)),
                enumerable: false,
                configurable: true,
            },
            _ => Property::Data {
                value: Value::UNDEFINED,
                writable: true,
                enumerable: false,
                configurable: true,
            },
        }
    }

    #[test]
    fn shaped_map_matches_oracle_through_define_set_delete_and_redefine() {
        let mut rng = XorShift64(0x9E3779B97F4A7C15);
        for _ in 0..10_000 {
            let mut atoms = AtomTable::default();
            let mut shapes = ShapeTable::new();
            let mut keys: Vec<PropertyKey> = Vec::new();
            for text in ["0", "1", "2", "3", "10", "42", "100", "999"] {
                let atom = atoms.intern_str(text);
                assert_eq!(
                    atoms.array_index(atom),
                    Some(text.parse().expect("index parses"))
                );
                keys.push(PropertyKey::Named(atom));
            }
            for index in 0..12 {
                keys.push(PropertyKey::Named(atoms.intern_str(&format!("k{index}"))));
            }
            for symbol in 0..4 {
                keys.push(PropertyKey::Symbol(1000 + symbol));
            }
            for private in 0..4 {
                keys.push(PropertyKey::Private(2000 + private));
            }
            let mut map = PropertyMap::default();
            let mut oracle = Oracle(Vec::new());
            let operations = 1 + rng.below(64);
            for _ in 0..operations {
                let key = keys[rng.below(keys.len())].clone();
                match rng.below(10) {
                    0 => {
                        map.remove(&shapes, &key);
                        oracle.remove(&key);
                    }
                    1 => {
                        map.remove(&shapes, &key);
                        oracle.remove(&key);
                        let property = canned(&mut rng);
                        map.insert(&mut shapes, key.clone(), property.clone());
                        oracle.insert(key, property);
                    }
                    2 => {
                        let first = canned(&mut rng);
                        map.insert(&mut shapes, key.clone(), first.clone());
                        oracle.insert(key.clone(), first.clone());
                        let mut second = canned(&mut rng);
                        while second == first {
                            second = canned(&mut rng);
                        }
                        map.insert(&mut shapes, key.clone(), second.clone());
                        oracle.insert(key, second);
                    }
                    _ => {
                        let property = canned(&mut rng);
                        map.insert(&mut shapes, key.clone(), property.clone());
                        oracle.insert(key, property);
                    }
                }
                check(&map, &shapes, &oracle);
            }
        }
    }

    #[test]
    fn dictionary_transition_matches_oracle_past_shape_capacity() {
        let mut atoms = AtomTable::default();
        let mut shapes = ShapeTable::new();
        let mut map = PropertyMap::default();
        let mut oracle = Oracle(Vec::new());
        for index in 0..70 {
            let key = PropertyKey::Named(atoms.intern_str(&format!("w{index}")));
            let property = Property::Data {
                value: Value::int32(u32::try_from(index).expect("sequence index fits u32")),
                writable: true,
                enumerable: true,
                configurable: true,
            };
            map.insert(&mut shapes, key.clone(), property.clone());
            oracle.insert(key, property);
            check(&map, &shapes, &oracle);
        }
        for index in (0..70).step_by(3) {
            let key = PropertyKey::Named(atoms.intern_str(&format!("w{index}")));
            map.remove(&shapes, &key);
            oracle.remove(&key);
            check(&map, &shapes, &oracle);
        }
    }

    #[test]
    fn dictionary_compacts_tombstones_under_add_delete_churn() {
        let mut atoms = AtomTable::default();
        let mut shapes = ShapeTable::new();
        let mut map = PropertyMap::default();
        let mut oracle = Oracle(Vec::new());
        for index in 0..70 {
            let key = PropertyKey::Named(atoms.intern_str(&format!("w{index}")));
            let property = Property::Data {
                value: Value::int32(u32::try_from(index).expect("sequence index fits u32")),
                writable: true,
                enumerable: true,
                configurable: true,
            };
            map.insert(&mut shapes, key.clone(), property.clone());
            oracle.insert(key, property);
        }
        let churn = PropertyKey::Named(atoms.intern_str("churn"));
        for round in 0..100_000 {
            let property = Property::Data {
                value: Value::int32(u32::try_from(round % 100).expect("churn value fits u32")),
                writable: true,
                enumerable: true,
                configurable: true,
            };
            map.insert(&mut shapes, churn.clone(), property.clone());
            oracle.insert(churn.clone(), property);
            map.remove(&shapes, &churn);
            oracle.remove(&churn);
            if round % 1000 == 0 {
                check(&map, &shapes, &oracle);
            }
        }
        check(&map, &shapes, &oracle);
        let PropertyMap::Dictionary { entries, index } = &map else {
            panic!("past capacity stays dictionary");
        };
        let live = index.len();
        assert_eq!(live, oracle.0.len());
        assert!(
            entries.len() <= 2 * live + 1,
            "entries {} with live {live}",
            entries.len()
        );
    }
    #[test]
    fn equal_insertion_orders_share_one_shape() {
        let mut atoms = AtomTable::default();
        let mut shapes = ShapeTable::new();
        let keys: Vec<PropertyKey> = ["a", "b", "c", "d"]
            .iter()
            .map(|name| PropertyKey::Named(atoms.intern_str(name)))
            .collect();
        let mut first = PropertyMap::default();
        let mut second = PropertyMap::default();
        for key in &keys {
            let property = Property::Data {
                value: Value::int32(1),
                writable: true,
                enumerable: true,
                configurable: true,
            };
            first.insert(&mut shapes, key.clone(), property.clone());
            second.insert(&mut shapes, key.clone(), property);
        }
        let (PropertyMap::Shaped { shape: former, .. }, PropertyMap::Shaped { shape: latter, .. }) =
            (&first, &second)
        else {
            panic!("small maps stay shaped");
        };
        assert_eq!(former, latter);
        let former_keys: Vec<PropertyKey> =
            first.iter(&shapes).map(|(key, _)| key.clone()).collect();
        let latter_keys: Vec<PropertyKey> =
            second.iter(&shapes).map(|(key, _)| key.clone()).collect();
        assert_eq!(former_keys, latter_keys);
        assert_eq!(former_keys, keys);
    }
}

#[cfg(test)]
mod rope_string_tests {
    use super::*;
    use crate::tests::{TestHost, function, verified};

    struct XorShift64(u64);
    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0 | 1;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n.max(1)
        }
    }

    fn rope_limits() -> Limits {
        Limits {
            max_heap_slots: 1 << 22,
            max_heap_bytes: usize::MAX >> 2,
            fuel: u64::MAX,
            ..Limits::default()
        }
    }

    fn with_rope_machine(test: impl FnOnce(&mut Machine<'_, TestHost>)) {
        let program = verified(
            vec![],
            vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, rope_limits());
        test(&mut machine);
    }

    fn empty_string(machine: &mut Machine<'_, TestHost>) -> Value {
        machine
            .allocate(HeapEntry::String(EcmaString::default()))
            .expect("empty string allocation succeeds")
    }

    fn push_piece(machine: &mut Machine<'_, TestHost>, text: &str) -> Value {
        machine
            .allocate(HeapEntry::String(EcmaString::encode(text)))
            .expect("piece allocation succeeds")
    }

    #[test]
    fn concat_sequence_matches_a_flat_code_unit_oracle() {
        with_rope_machine(|machine| {
            let mut rng = XorShift64(0x9E37_79B9_7F4A_7C15);
            let mut oracle: Vec<u16> = Vec::new();
            let mut value = empty_string(machine);
            for _ in 0..10_000 {
                let len = rng.below(7) + 1;
                let mut piece = String::new();
                for _ in 0..len {
                    piece.push(char::from(b'a' + rng.below(26) as u8));
                }
                let piece_value = push_piece(machine, &piece);
                oracle.extend(piece.encode_utf16());
                value = machine
                    .concat_string_values(value, piece_value)
                    .expect("concatenation succeeds");
                let slot = machine.string_slot(value).expect("result is a string");
                assert_eq!(machine.string_len(slot), oracle.len());
                assert_eq!(machine.type_of(value), "string");
                let flat = machine.flat_string(slot);
                assert_eq!(flat.as_units(), oracle.as_slice());
                assert!(!machine.is_rope(slot));
                let offset = rng.below(oracle.len() as u64) as usize;
                assert_eq!(flat.unit_at(offset), oracle.get(offset).copied());
                let oracle_value = machine
                    .allocate(HeapEntry::String(EcmaString::from_units(&oracle)))
                    .expect("oracle allocation succeeds");
                assert!(machine.strict_equal(value, oracle_value));
                let mut altered = oracle.clone();
                let last = altered.len() - 1;
                altered[last] = if altered[last] == u16::from(b'z') {
                    u16::from(b'y')
                } else {
                    u16::from(b'z')
                };
                let altered_value = machine
                    .allocate(HeapEntry::String(EcmaString::from_units(&altered)))
                    .expect("altered allocation succeeds");
                assert!(!machine.strict_equal(value, altered_value));
            }
            assert!(oracle.len() > 32);
        });
    }

    #[test]
    fn deep_left_and_right_leaning_ropes_flatten_without_recursion() {
        with_rope_machine(|machine| {
            for left_leaning in [true, false] {
                let mut value = push_piece(machine, "a");
                let mut expected = String::from("a");
                for position in 1..100_000u32 {
                    let piece_text = if position % 2 == 0 { "b" } else { "c" };
                    let piece = push_piece(machine, piece_text);
                    value = if left_leaning {
                        expected.push_str(piece_text);
                        machine
                            .concat_string_values(value, piece)
                            .expect("left concatenation succeeds")
                    } else {
                        expected.insert_str(0, piece_text);
                        machine
                            .concat_string_values(piece, value)
                            .expect("right concatenation succeeds")
                    };
                }
                let slot = machine.string_slot(value).expect("chain is a string");
                assert!(machine.is_rope(slot));
                assert_eq!(machine.string_len(slot), expected.len());
                let flat = machine.flat_string(slot);
                assert_eq!(flat.as_units(), expected.encode_utf16().collect::<Vec<_>>());
                assert_eq!(flat.unit_at(0), expected.encode_utf16().next());
                assert_eq!(
                    flat.unit_at(expected.len() - 1),
                    expected.encode_utf16().last()
                );
                assert!(!machine.is_rope(slot));
            }
        });
    }

    #[test]
    fn reading_length_does_not_flatten_a_rope() {
        with_rope_machine(|machine| {
            let left = push_piece(machine, "0123456789abcdef");
            let right = push_piece(machine, "0123456789abcdef");
            let value = machine
                .concat_string_values(left, right)
                .expect("concatenation succeeds");
            let slot = machine.string_slot(value).expect("result is a string");
            assert!(machine.is_rope(slot));
            let length_key = PropertyKey::Named(machine.intern_str("length"));
            let found = machine.own_get(slot, &length_key);
            let Some(Found::Value(length)) = found else {
                panic!("a rope exposes its length as a value");
            };
            assert_eq!(length, number_value(32.0));
            assert!(machine.is_rope(slot));
            assert_eq!(machine.string_len(slot), 32);
        });
    }

    #[test]
    fn short_concatenations_stay_flat_and_empty_operands_reuse_the_other_value() {
        with_rope_machine(|machine| {
            let left = push_piece(machine, "abc");
            let right = push_piece(machine, "de");
            let value = machine
                .concat_string_values(left, right)
                .expect("short concatenation succeeds");
            let slot = machine.string_slot(value).expect("result is a string");
            assert!(!machine.is_rope(slot));
            assert!(machine.flat_string(slot).eq_ascii("abcde"));

            let empty = empty_string(machine);
            assert_eq!(
                machine
                    .concat_string_values(left, empty)
                    .expect("empty right succeeds"),
                left
            );
            assert_eq!(
                machine
                    .concat_string_values(empty, right)
                    .expect("empty left succeeds"),
                right
            );
        });
    }

    #[test]
    fn rope_values_hash_and_intern_like_their_flat_text() {
        with_rope_machine(|machine| {
            let left = push_piece(machine, "0123456789abcdef");
            let right = push_piece(machine, "0123456789abcdef");
            let rope = machine
                .concat_string_values(left, right)
                .expect("concatenation succeeds");
            let flat = push_piece(machine, "0123456789abcdef0123456789abcdef");
            assert!(machine.is_rope(machine.string_slot(rope).unwrap()));
            assert_eq!(
                collection_key_hash(machine, rope),
                collection_key_hash(machine, flat)
            );
            assert!(machine.same_value_zero(rope, flat));
            assert!(machine.strict_equal(rope, flat));
            assert_eq!(
                machine.property_key_from_value(rope).unwrap(),
                machine.property_key_from_value(flat).unwrap()
            );
        });
    }

    #[test]
    fn a_long_append_chain_stays_within_the_default_heap_limit() {
        let program = verified(
            vec![],
            vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
        );
        let mut host = TestHost;
        let mut machine = Machine::new(&program, &mut host, Limits::default());
        let dot = push_piece(&mut machine, ".");
        let mut value = empty_string(&mut machine);
        for _ in 0..10_000 {
            value = machine
                .concat_string_values(value, dot)
                .expect("an append fits the default heap limit");
        }
        let slot = machine.string_slot(value).expect("chain is a string");
        assert_eq!(machine.string_len(slot), 10_000);
        let flat = machine.flat_string(slot);
        assert!(flat.as_units().iter().all(|&unit| unit == u16::from(b'.')));
        machine.assert_heap_ledger();
    }

    #[test]
    fn a_rope_longer_than_the_remaining_heap_is_refused() {
        let program = verified(
            vec![],
            vec![function(0, 0, vec![Instruction::Halt], Vec::new())],
        );
        let mut host = TestHost;
        let limits = Limits {
            max_heap_bytes: 16 << 10,
            ..Limits::default()
        };
        let mut machine = Machine::new(&program, &mut host, limits);
        let half = push_piece(&mut machine, &"a".repeat(1_500));
        let other = push_piece(&mut machine, &"b".repeat(1_500));
        let joined = machine
            .concat_string_values(half, other)
            .expect("3000 units fit in the remaining heap");
        assert!(matches!(
            machine.concat_string_values(joined, joined),
            Err(EvalFailure::Runtime(
                RuntimeErrorKind::HeapByteLimitExceeded { .. }
            ))
        ));
        machine.assert_heap_ledger();
    }
}
