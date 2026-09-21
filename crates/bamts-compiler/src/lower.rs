#![allow(clippy::too_many_lines)]
use crate::enum_plan::{EnumFacts, EnumMemberPlan, EnumScalar, EnumValue};
use crate::jsx_desugar::JsxSourceDesugarPlan;
use crate::literal::{
    BigIntTextError, MAX_BIGINT_CONVERSION_LIMB_OPS, canonical_bigint_text, cook_escapes,
    number_value, string_value,
};
use crate::namespace_plan::{ContainerAcquisition, NamespaceFacts};
pub use crate::program::{
    ExecutableModuleProvenance, ExecutableProgram, ProgramLowerError, ProgramLowerErrorKind,
    ProgramLowerPhase, lower_program,
};
use crate::source::{ScriptKind, SourceId, TextRange, Utf16Pos};
use crate::syntax::{
    ArrayBindingElement, ArrayElement, ArrowFunction, AssignmentArrayElement, AssignmentExpression,
    AssignmentMemberTarget, AssignmentObjectProperty, AssignmentOperator, AssignmentTarget,
    AssignmentTargetNode, AwaitExpression, BinaryExpression, BinaryOperator, BindingPattern, Block,
    BlockNode, BooleanLiteralNode, CallArgument, CallExpression, ClassDeclaration, ClassMember,
    ConditionalExpression, DecoratorNode, DoWhileStatement, EnumDeclaration, ExportDeclaration,
    ExportDefaultValue, ExportNamedDeclaration, ExportSpecifierMode, Expr, Expression, ForBinding,
    ForInStatement, ForInitializer, ForOfMode, ForOfStatement, ForStatement, FunctionBody,
    FunctionLike, IdentifierNode, IfStatement, ImportBinding, ImportDeclaration,
    ImportSpecifierMode, LabeledStatement, Literal, LogicalExpression, LogicalOperator,
    MemberExpression, MemberProperty, MetaProperty, ModuleExportName, NamespaceDeclaration,
    NamespaceName, NewExpression, NodeId, NodeKind, NumericLiteralNode, ObjectLiteral,
    ObjectMember, ParameterNode, Pattern, PrivateIdentifierNode, PropertyModifier, PropertyName,
    RegexLiteralNode, SourceFile, Statement, Stmt, StringLiteralNode, SwitchStatement,
    TemplateElementNode, TemplateLiteral, TokenKind, UnaryOperator, UpdateExpression,
    UpdateOperator, VariableDeclaration, VariableKind, WhileStatement, WithStatement,
    YieldExpression,
};
use bamts_bytecode::{
    AccessorKind, BigIntLiteral, BinaryOp, Constant, ConstantId, DescriptorSlot, DisposeHint,
    EcmaString, ExceptionHandler, Function, FunctionFlags, FunctionId, Instruction,
    IteratorCloseMode, IteratorKind, MAX_BIGINT_BYTES, MAX_CONSTANTS, MAX_FUNCTIONS,
    MAX_INSTRUCTIONS, MAX_REGISTERS, Module, NumberBits, Pc, RESUME_RETURN, RESUME_THROW, Register,
    UnaryOp, Verified, VerifyError,
};
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;
fn zero_range() -> TextRange {
    match TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO) {
        Ok(range) => range,
        Err(_) => unreachable!("Utf16Pos::ZERO is never after itself"),
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct LowerOptions {
    pub javascript_compatibility: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LoweringGoal {
    Module,
    ProgramModule,
    ClassicScript,
}
const MAX_BODY_INSTRUCTIONS: usize = MAX_INSTRUCTIONS as usize - 2;
const MAX_STRING_UNITS: usize = 1 << 20;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LowerError {
    pub source: SourceId,
    pub range: TextRange,
    pub kind: LowerErrorKind,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LowerErrorKind {
    JavaScriptSourceNeedsCompatibility {
        script_kind: ScriptKind,
    },
    JsonSourceNotExecutable,
    MissingSyntax {
        expected: NodeKind,
    },
    InvalidNumericLiteral,
    InvalidBigIntLiteral,
    InvalidRegexLiteral,
    IllFormedMetadataString,
    ImportDeclarationInScript,
    ExportDeclarationInScript,
    ImportMetaInScript,
    ReturnOutsideFunction,
    InvalidControlFlow {
        operation: &'static str,
    },
    /// A direct operation requires a runtime object, but its receiver is an
    /// elided `const enum`.
    ConstEnumOperation {
        operation: ConstEnumOperation,
    },
    /// A runtime construct the current instruction set cannot express.
    Unsupported(UnsupportedConstruct),
    /// A structural production capacity ran out.
    Capacity(CapacityLimit),
    /// The assembled module failed bytecode verification. Lowering maintains
    /// every verifier invariant by construction, so this is defensive.
    Verify(VerifyError),
}
/// Operations that cannot target an elided `const enum`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstEnumOperation {
    Read,
    Write,
    Delete,
    OptionalAccess,
}
/// Runtime syntax this instruction set cannot express faithfully.
/// Every variant names one rejected construct; there is no catch-all.
/// None of these occur in the executable corpus.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnsupportedConstruct {
    /// An `await` or `await using` appears outside an async context.
    UsingDeclaration,
    /// A runtime `enum` reached lowering without checker-produced facts.
    EnumDeclaration,
    /// A runtime `namespace`/`module` block.
    NamespaceDeclaration,
    /// A runtime `import x = require(...)` / `import x = ns` declaration.
    RuntimeImportEquals,
    /// A runtime `export * from ...` (no dynamic per-name re-export).
    RuntimeExportAll,
    /// A parameter decorator (legacy-only; not part of the TC39 decorator model).
    ParameterDecorator,
    /// A constructor decorator (legacy-only; not part of the TC39 decorator model).
    ConstructorDecorator,
}
/// The exhausted structural capacity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CapacityLimit {
    Registers,
    Constants,
    Functions,
    Instructions,
    StringUnits,
    BigIntBytes,
    BigIntWork,
    Captures,
    ControlTargets,
}
impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "lowering failed in source {} at {}..{}: {}",
            self.source.get(),
            self.range.start().get(),
            self.range.end().get(),
            self.kind
        )
    }
}
impl fmt::Display for LowerErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::JavaScriptSourceNeedsCompatibility { script_kind } => write!(
                f,
                "{script_kind:?} source requires LowerOptions::javascript_compatibility"
            ),
            Self::JsonSourceNotExecutable => f.write_str("JSON sources are not executable"),
            Self::MissingSyntax { expected } => {
                write!(f, "parser recovery produced a missing {expected:?}")
            }
            Self::InvalidNumericLiteral => f.write_str("numeric literal has no cooked value"),
            Self::InvalidBigIntLiteral => f.write_str("bigint literal has no canonical value"),
            Self::InvalidRegexLiteral => f.write_str("regular-expression literal is malformed"),
            Self::IllFormedMetadataString => {
                f.write_str("module metadata string is not well-formed UTF-16")
            }
            Self::ImportDeclarationInScript => {
                f.write_str("`import` declaration in a classic script")
            }
            Self::ExportDeclarationInScript => {
                f.write_str("`export` declaration in a classic script")
            }
            Self::ImportMetaInScript => f.write_str("`import.meta` in a classic script"),
            Self::ReturnOutsideFunction => f.write_str("return statement outside of a function"),
            Self::InvalidControlFlow { operation } => {
                write!(f, "invalid control flow: {operation}")
            }
            Self::ConstEnumOperation { operation } => {
                write!(f, "invalid const enum operation: {operation}")
            }
            Self::Unsupported(construct) => {
                write!(f, "unsupported runtime semantics: {construct}")
            }
            Self::Capacity(limit) => write!(f, "bytecode capacity exhausted: {limit}"),
            Self::Verify(error) => write!(f, "assembled module failed verification: {error}"),
        }
    }
}
impl fmt::Display for ConstEnumOperation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Read => "member read",
            Self::Write => "member write",
            Self::Delete => "member delete",
            Self::OptionalAccess => "optional member access",
        };
        f.write_str(text)
    }
}
impl fmt::Display for UnsupportedConstruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::UsingDeclaration => "`await` or `await using` outside an async context",
            Self::EnumDeclaration => "unchecked runtime `enum` declaration",
            Self::NamespaceDeclaration => "runtime `namespace` declaration",
            Self::RuntimeImportEquals => "runtime `import =` declaration",
            Self::RuntimeExportAll => "runtime `export *` declaration",
            Self::ParameterDecorator => "parameter decorator",
            Self::ConstructorDecorator => "constructor decorator",
        };
        f.write_str(text)
    }
}
impl fmt::Display for CapacityLimit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Registers => "too many registers in one function",
            Self::Constants => "too many pooled constants",
            Self::Functions => "too many functions",
            Self::Instructions => "too many instructions in one function",
            Self::StringUnits => "string constant exceeds the deterministic pool code-unit ceiling",
            Self::BigIntBytes => "bigint constant exceeds the canonical decoder byte ceiling",
            Self::BigIntWork => "bigint radix conversion exceeds its deterministic work ceiling",
            Self::Captures => "too many captured variables in one closure",
            Self::ControlTargets => "too many nested control-flow targets",
        };
        f.write_str(text)
    }
}
impl Error for LowerError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            LowerErrorKind::Verify(error) => Some(error),
            _ => None,
        }
    }
}
/// Lowers a parsed source file directly to a verified bytecode module.
///
/// Top-level statements become the entry function; every nested function
/// becomes one additional module function. The returned module has passed
/// [`Module::verify`].
///
/// # Errors
/// Returns a typed [`LowerError`] for an unsupported source kind, a parser
/// recovery node, an inexpressible runtime construct, an exhausted capacity, or
/// (defensively) a verification failure.
pub fn lower(file: &SourceFile, options: LowerOptions) -> Result<Module<Verified>, LowerError> {
    let enum_facts = EnumFacts::unchecked();
    let namespace_facts = NamespaceFacts::unchecked();
    lower_checked(file, options, &enum_facts, &namespace_facts)
}
/// Lowers one already checked source file to a verified bytecode module.
pub(crate) fn lower_checked(
    file: &SourceFile,
    options: LowerOptions,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
) -> Result<Module<Verified>, LowerError> {
    let module = assemble_checked(file, options, enum_facts, namespace_facts)?;
    module.verify().map_err(|error| LowerError {
        source: file.source_id(),
        range: file.range(),
        kind: LowerErrorKind::Verify(error),
    })
}
/// Assembles a checked module without the final verification pass.
pub(crate) fn assemble_checked(
    file: &SourceFile,
    options: LowerOptions,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
) -> Result<Module<bamts_bytecode::Unverified>, LowerError> {
    assemble_with_linkage_strings(
        file,
        options,
        &[],
        None,
        LoweringGoal::Module,
        enum_facts,
        namespace_facts,
    )
}
pub(crate) fn assemble_program_module(
    file: &SourceFile,
    options: LowerOptions,
    linkage_strings: &[String],
    jsx_plan: Option<&JsxSourceDesugarPlan>,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
) -> Result<Module<bamts_bytecode::Unverified>, LowerError> {
    assemble_with_linkage_strings(
        file,
        options,
        linkage_strings,
        jsx_plan,
        LoweringGoal::ProgramModule,
        enum_facts,
        namespace_facts,
    )
}
/// Assembles a classic script without the final verification pass.
pub(crate) fn assemble_classic_script_named(
    file: &SourceFile,
    options: LowerOptions,
    module_name: &str,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
) -> Result<Module<bamts_bytecode::Unverified>, LowerError> {
    assemble_with_linkage_strings(
        file,
        options,
        &[module_name.to_owned()],
        None,
        LoweringGoal::ClassicScript,
        enum_facts,
        namespace_facts,
    )
}
fn assemble_with_linkage_strings(
    file: &SourceFile,
    options: LowerOptions,
    linkage_strings: &[String],
    jsx_plan: Option<&JsxSourceDesugarPlan>,
    goal: LoweringGoal,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
) -> Result<Module<bamts_bytecode::Unverified>, LowerError> {
    validate_script_kind(file, options)?;
    let mut builder = ModuleBuilder {
        source: file.source_id(),
        constants: Vec::new(),
        functions: Vec::new(),
    };
    for value in linkage_strings {
        builder.intern(Constant::String(EcmaString::encode(value)), file.range())?;
    }
    let entry = builder.reserve_function(file.range())?;
    let mut context = FunctionContext::new_top_level(
        file,
        jsx_plan,
        goal,
        enum_facts,
        namespace_facts,
        namespace_facts.symbols(),
    );
    let completion = if goal == LoweringGoal::ClassicScript {
        let completion = context.alloc_register(file.range())?;
        let undefined = context.undefined(&mut builder, file.range())?;
        context.move_to(file.range(), completion, undefined)?;
        context.completion = Some(completion);
        Some(completion)
    } else {
        None
    };
    context.lower_top_level(&mut builder, file.statements())?;
    match completion {
        Some(value) => context.emit(file.range(), Instruction::Return { value })?,
        None => context.emit(file.range(), Instruction::Halt)?,
    };
    let assembled = context.into_function(None, FunctionFlags::default());
    builder.fill_function(entry, assembled);
    let functions = builder
        .functions
        .into_iter()
        .map(|slot| slot.expect("every reserved function slot is filled before assembly"))
        .collect();
    Ok(Module::new(builder.constants, functions, entry))
}
fn validate_script_kind(file: &SourceFile, options: LowerOptions) -> Result<(), LowerError> {
    let kind = match file.script_kind() {
        ScriptKind::TypeScript | ScriptKind::TypeScriptReact => return Ok(()),
        ScriptKind::JavaScript | ScriptKind::JavaScriptReact => {
            if options.javascript_compatibility {
                return Ok(());
            }
            LowerErrorKind::JavaScriptSourceNeedsCompatibility {
                script_kind: file.script_kind(),
            }
        }
        ScriptKind::Json => LowerErrorKind::JsonSourceNotExecutable,
    };
    Err(LowerError {
        source: file.source_id(),
        range: file.range(),
        kind,
    })
}
/// Module-wide constant pool and function table.
struct ModuleBuilder {
    source: SourceId,
    constants: Vec<Constant>,
    functions: Vec<Option<Function>>,
}
impl ModuleBuilder {
    fn error(&self, range: TextRange, kind: LowerErrorKind) -> LowerError {
        LowerError {
            source: self.source,
            range,
            kind,
        }
    }
    /// Interns one constant, deduplicated, in deterministic first-use order.
    fn intern(&mut self, constant: Constant, range: TextRange) -> Result<ConstantId, LowerError> {
        if let Constant::String(value) = &constant
            && value.len_units() > MAX_STRING_UNITS
        {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::StringUnits)));
        }
        if let Some(position) = self
            .constants
            .iter()
            .position(|existing| *existing == constant)
        {
            return Ok(ConstantId::new(position as u32));
        }
        if self.constants.len() >= MAX_CONSTANTS as usize {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::Constants)));
        }
        let id = ConstantId::new(self.constants.len() as u32);
        self.constants.push(constant);
        Ok(id)
    }
    fn reserve_function(&mut self, range: TextRange) -> Result<FunctionId, LowerError> {
        if self.functions.len() >= MAX_FUNCTIONS as usize {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::Functions)));
        }
        let id = FunctionId::new(self.functions.len() as u32);
        self.functions.push(None);
        Ok(id)
    }
    fn fill_function(&mut self, id: FunctionId, function: Function) {
        self.functions[id.get() as usize] = Some(function);
    }
}
/// What a resolved name denotes inside the current function. Its storage kind is
/// fixed at declaration and never changes.
#[derive(Clone, Copy)]
enum Binding {
    /// A value living in a fixed register (the binding's home).
    Local(Register),
    Cell(Register),
    ConstEnum(crate::checker::SymbolId),
}
type BindingSite = (usize, usize);
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum BindingIdentity {
    Function(String),
    Lexical(BindingSite),
}
#[derive(Default)]
struct CapturePlan {
    captured: HashSet<BindingIdentity>,
    runtime_cells: HashSet<BindingIdentity>,
}
fn scan_instance_init_free_vars(scanner: &mut FreeVarScanner<'_>, instance_steps: &[InstanceInit]) {
    for step in instance_steps {
        match step {
            InstanceInit::PlainField { initializer, .. } => {
                if let Some(initializer) = initializer {
                    scanner.scan_expression(initializer);
                }
            }
            InstanceInit::Decorated {
                initializer: Some(initializer),
                ..
            } => {
                if let Some(initializer) = initializer {
                    scanner.scan_expression(initializer);
                }
            }
            InstanceInit::Decorated {
                initializer: None, ..
            } => {}
        }
    }
}
impl CapturePlan {
    fn captures(&self, name: &str, site: BindingSite, declaration_scope: DeclarationScope) -> bool {
        self.captured
            .contains(&binding_identity(name, site, declaration_scope))
    }
    fn requires_cell(
        &self,
        name: &str,
        site: BindingSite,
        declaration_scope: DeclarationScope,
    ) -> bool {
        let identity = binding_identity(name, site, declaration_scope);
        self.captured.contains(&identity) || self.runtime_cells.contains(&identity)
    }
}
#[derive(Clone)]
struct ImmediateDeclaration<'a> {
    name: String,
    site: BindingSite,
    range: TextRange,
    kind: ImmediateDeclarationKind<'a>,
}
#[derive(Clone, Copy)]
enum ImmediateDeclarationKind<'a> {
    Lexical,
    Function(&'a FunctionLike),
}
fn binding_identity(
    name: &str,
    site: BindingSite,
    declaration_scope: DeclarationScope,
) -> BindingIdentity {
    match declaration_scope {
        DeclarationScope::Function => BindingIdentity::Function(name.to_owned()),
        DeclarationScope::Lexical | DeclarationScope::Iteration => BindingIdentity::Lexical(site),
    }
}
fn binding_site(range: TextRange) -> BindingSite {
    (range.start().get(), range.end().get())
}
#[derive(Clone, Copy)]
enum DeclarationScope {
    Function,
    Lexical,
    Iteration,
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ContainerKind {
    Enum,
    Namespace,
}
#[derive(Clone, Copy)]
struct Container {
    symbol: crate::checker::SymbolId,
    object: Register,
    kind: ContainerKind,
}
#[derive(Clone, Copy)]
struct WithRegion {
    site: BindingSite,
    object: Register,
    scope_depth: usize,
}
/// Snapshot of one `with` object-environment HasBinding decision.
/// Used for GetValue-style consumers (reads, typeof, delete, direct-call `this`).
/// Assignment/update PutValue must not reuse this across an RHS: Node re-resolves
/// the binding after the RHS completes (see lower_identifier_assignment).
#[derive(Clone, Copy)]
struct WithBase {
    base: Register,
    found: Register,
    key: Register,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CaptureKey {
    /// Free outer binding plus the live `with` sites that still precede it at
    /// capture time (`floor < region.scope_depth`). Empty when the binding
    /// shadows every live with region (e.g. a lexical declared inside a with
    /// body) or when no with region is active. Nested with regions need this
    /// per-site relation; a single boolean cannot distinguish them.
    Name(String, Vec<BindingSite>),
    This,
    ThisCell,
    Arguments,
    NewTarget,
    Parent(Register),
    ClassElements(Register),
    Cell(Register),
    Container(crate::checker::SymbolId, ContainerKind, Register),
    WithObject(BindingSite, Register),
}
#[derive(Clone, Copy)]
enum ArgumentsSource {
    Own,
    Captured(Register),
    None,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ControlTargetKind {
    Iteration,
    Switch,
    Label,
}
struct ControlTarget {
    breaks: Vec<Pc>,
    continues: Vec<Pc>,
    kind: ControlTargetKind,
    labels: Vec<String>,
}
struct IterationLowering<'a> {
    range: TextRange,
    subject: Register,
    kind: IteratorKind,
    binding: &'a ForBinding,
    body: &'a Stmt,
    labels: Vec<String>,
}
/// Completion kinds routed through a `finally` block.
const COMPLETION_NORMAL: i32 = 0;
const COMPLETION_RETURN: i32 = 1;
const COMPLETION_THROW: i32 = 2;
const COMPLETION_BREAK: i32 = 3;
const COMPLETION_CONTINUE: i32 = 4;
/// What a live `finally_stack` frame protects.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FinallyKind {
    /// A user `try`/`finally` block.
    Finalizer,
    /// Compiler-owned cleanup for a captured explicit resource.
    Disposal,
    /// The iterator cleanup of the `for`/`of` loop whose control target is
    /// `loop_target`. A `continue` naming that same loop resumes iteration
    /// without closing, so it bypasses this frame.
    IteratorCleanup { loop_target: usize },
}
/// A live `finally` block: the completion state registers and the pending
/// jumps into the finally entry that must be patched once its PC is known.
struct FinallyFrame {
    kind: FinallyKind,
    kind_reg: Register,
    value_reg: Register,
    target_reg: Register,
    pending: Vec<Pc>,
    /// Control-target depth when this finally was entered. A jump whose target
    /// predates the finally must route through it.
    control_depth: usize,
    /// Statically observed `(completion kind, target index)` pairs.
    targets: Vec<(i32, usize)>,
}
/// A captured resource whose protected region remains open until its statement list exits.
#[derive(Clone, Copy, Debug)]
struct DisposalRecord {
    range: TextRange,
    value: Register,
    method: Register,
    capture_kind: Register,
    hint: DisposeHint,
    body_start: Pc,
}
struct LoweredMemberDecorators {
    key: Register,
    decorators: Vec<Register>,
}
/// A member decorator application deferred until after the source-order member
/// traversal so the four stage buckets can drain in pinned order.
enum DeferredMemberDecoration {
    Method {
        range: TextRange,
        target: Register,
        key: Register,
        slot: DescriptorSlot,
        decorators: Vec<Register>,
        context: Register,
        state_cell: Register,
    },
    Field {
        range: TextRange,
        decorators: Vec<Register>,
        context: Register,
        init_chain: Register,
        state_cell: Register,
    },
    AutoAccessor {
        range: TextRange,
        target: Register,
        key: Register,
        decorators: Vec<Register>,
        context: Register,
        init_chain: Register,
        state_cell: Register,
    },
}
/// Staged member decorator applications drained in pinned order:
/// static callable, instance callable, static field, instance field.
#[derive(Default)]
struct MemberDecorationStages {
    static_callables: Vec<DeferredMemberDecoration>,
    instance_callables: Vec<DeferredMemberDecoration>,
    static_fields: Vec<DeferredMemberDecoration>,
    instance_fields: Vec<DeferredMemberDecoration>,
}
/// The role a synthetic `access` closure plays over its captured key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AccessRole {
    Has,
    Get,
    Set,
}
/// How a standard member decorator observes and rewrites its element.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MemberDecorationKind {
    Method,
    Getter,
    Setter,
    Field,
    AutoAccessor,
}
impl MemberDecorationKind {
    fn context_name(self) -> &'static str {
        match self {
            Self::Method => "method",
            Self::Getter => "getter",
            Self::Setter => "setter",
            Self::Field => "field",
            Self::AutoAccessor => "accessor",
        }
    }
}
#[derive(Clone)]
enum InstanceInit {
    PlainField {
        slot: u32,
        initializer: Option<Box<Expr>>,
    },
    Decorated {
        slot: u32,
        initializer: Option<Option<Box<Expr>>>,
    },
}
enum StaticInit {
    Field {
        property: Box<crate::syntax::ClassProperty>,
        key: Register,
        init_chain: Register,
        extra_inits: Register,
    },
    AutoAccessor {
        initializer: Option<Box<Expr>>,
        backing_key: Register,
        init_chain: Register,
        extra_inits: Register,
    },
    MemberExtras {
        extra_inits: Register,
    },
    Block(BlockNode),
}
struct FunctionContext<'a> {
    file: &'a SourceFile,
    jsx_plan: Option<&'a JsxSourceDesugarPlan>,
    enum_facts: &'a EnumFacts,
    namespace_facts: &'a NamespaceFacts,
    symbols: &'a [crate::checker::Symbol],
    /// Live checked enum and namespace objects, outermost to innermost.
    /// Identifier substitution compares checker symbol identities, never text.
    containers: Vec<Container>,
    /// Live `with` object environments, outermost to innermost. A `with` object
    /// is an ordinary register value captured through `CaptureKey`; lexical exit,
    /// including an abrupt completion, only pops this compile-time view.
    with_regions: Vec<WithRegion>,
    /// Names installed solely as `CaptureKey::Name` restores, mapped to the
    /// with-region sites that must still precede that binding. Restored names
    /// sit at scope index 0 beside captured `with` regions (`scope_depth: 0`);
    /// only the listed sites remain applicable for that name. A later function-
    /// scoped `declare` of the same name (parameter / var) removes the entry so
    /// the local binding correctly shadows every captured region.
    captured_names: HashMap<String, Vec<BindingSite>>,
    code: Vec<Instruction>,
    registers: u32,
    capture_count: u32,
    parameter_count: u32,
    scopes: Vec<HashMap<String, Binding>>,
    /// Cells allocated before a declaration-owned initializer or body is built,
    /// indexed by the scanner's exact binding identity.
    predeclared_cells: HashMap<BindingIdentity, Register>,
    capture_plan: CapturePlan,
    control_targets: Vec<ControlTarget>,
    handlers: Vec<ExceptionHandler>,
    finally_stack: Vec<FinallyFrame>,
    disposal_stack: Vec<DisposalRecord>,
    top_level: bool,
    /// Whether this activation is an `async` function (not top-level await).
    is_async: bool,
    /// Whether this activation is an `async generator`: `yield*` delegates
    /// through the async iterator protocol only inside one.
    is_async_generator: bool,
    goal: LoweringGoal,
    completion: Option<Register>,
    completion_pool: Vec<Register>,
    completion_depth: usize,
    this_capture: Option<Register>,
    this_cell: Option<Register>,
    derived_super_guard: Option<Register>,
    instance_steps: Vec<InstanceInit>,
    new_target_capture: Option<Register>,
    parent_constructor_capture: Option<Register>,
    class_elements: Option<Register>,
    arguments_source: ArgumentsSource,
}
impl<'a> FunctionContext<'a> {
    fn new_top_level(
        file: &'a SourceFile,
        jsx_plan: Option<&'a JsxSourceDesugarPlan>,
        goal: LoweringGoal,
        enum_facts: &'a EnumFacts,
        namespace_facts: &'a NamespaceFacts,
        symbols: &'a [crate::checker::Symbol],
    ) -> Self {
        let capture_plan = CapturePlan::for_statements(file, jsx_plan, file.statements());
        Self {
            jsx_plan,
            file,
            enum_facts,
            namespace_facts,
            symbols,
            containers: Vec::new(),
            with_regions: Vec::new(),
            captured_names: HashMap::new(),
            code: Vec::new(),
            registers: 0,
            capture_count: 0,
            parameter_count: 0,
            scopes: vec![HashMap::new()],
            predeclared_cells: HashMap::new(),
            capture_plan,
            control_targets: Vec::new(),
            handlers: Vec::new(),
            finally_stack: Vec::new(),
            disposal_stack: Vec::new(),
            top_level: true,
            is_async: false,
            is_async_generator: false,
            goal,
            completion: None,
            completion_pool: Vec::new(),
            completion_depth: 0,
            this_capture: None,
            this_cell: None,
            derived_super_guard: None,
            instance_steps: Vec::new(),
            new_target_capture: None,
            parent_constructor_capture: None,
            class_elements: None,
            arguments_source: ArgumentsSource::None,
        }
    }
    /// Whether `await`, `await using`, or async disposal awaits are legal here.
    /// Module top level supports top-level await; classic scripts do not.
    fn can_await(&self) -> bool {
        self.is_async || (self.top_level && self.goal != LoweringGoal::ClassicScript)
    }
    fn into_function(self, name: Option<ConstantId>, flags: FunctionFlags) -> Function {
        Function::new(
            name,
            self.capture_count,
            self.parameter_count,
            self.registers,
            flags,
            self.code,
            self.handlers,
        )
    }
    fn error(&self, range: TextRange, kind: LowerErrorKind) -> LowerError {
        LowerError {
            source: self.file.source_id(),
            range,
            kind,
        }
    }
    fn unsupported(&self, range: TextRange, construct: UnsupportedConstruct) -> LowerError {
        self.error(range, LowerErrorKind::Unsupported(construct))
    }
    fn reject_decorators(
        &self,
        decorators: &[DecoratorNode],
        construct: UnsupportedConstruct,
    ) -> Result<(), LowerError> {
        if let Some(decorator) = decorators.first() {
            return Err(self.unsupported(decorator.range(), construct));
        }
        Ok(())
    }
    fn reject_parameter_decorators(&self, parameters: &[ParameterNode]) -> Result<(), LowerError> {
        for parameter in parameters {
            self.reject_decorators(
                &parameter.data().decorators,
                UnsupportedConstruct::ParameterDecorator,
            )?;
        }
        Ok(())
    }
    fn missing(&self, range: TextRange, expected: NodeKind) -> LowerError {
        self.error(range, LowerErrorKind::MissingSyntax { expected })
    }
    fn emit(&mut self, range: TextRange, instruction: Instruction) -> Result<Pc, LowerError> {
        if self.code.len() >= MAX_BODY_INSTRUCTIONS {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::Instructions)));
        }
        let pc = Pc::new(self.code.len() as u32);
        self.code.push(instruction);
        Ok(pc)
    }
    fn next_pc(&self) -> Pc {
        Pc::new(self.code.len() as u32)
    }
    fn patch_jump(&mut self, at: Pc, target: Pc) {
        match &mut self.code[at.get() as usize] {
            Instruction::Jump { target: slot }
            | Instruction::JumpIfTrue { target: slot, .. }
            | Instruction::JumpIfFalse { target: slot, .. } => *slot = target,
            other => unreachable!("patch target of non-jump instruction: {other:?}"),
        }
    }
    fn alloc_register(&mut self, range: TextRange) -> Result<Register, LowerError> {
        if self.registers >= MAX_REGISTERS {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::Registers)));
        }
        let register = Register::new(self.registers);
        self.registers += 1;
        Ok(register)
    }
    fn load_constant(
        &mut self,
        builder: &mut ModuleBuilder,
        constant: Constant,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        let id = builder.intern(constant, range)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::LoadConst { dst, constant: id })?;
        Ok(dst)
    }
    fn undefined(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        self.load_constant(builder, Constant::Undefined, range)
    }
    fn string_reg(
        &mut self,
        builder: &mut ModuleBuilder,
        value: EcmaString,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        self.load_constant(builder, Constant::String(value), range)
    }
    fn move_to(
        &mut self,
        range: TextRange,
        dst: Register,
        src: Register,
    ) -> Result<(), LowerError> {
        self.emit(range, Instruction::Move { dst, src })?;
        Ok(())
    }
    fn lower_normalizing_statement(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        lower: impl FnOnce(&mut Self, &mut ModuleBuilder) -> Result<(), LowerError>,
    ) -> Result<(), LowerError> {
        let Some(outer) = self.completion else {
            return lower(self, builder);
        };
        let depth = self.completion_depth;
        let inner = match self.completion_pool.get(depth).copied() {
            Some(register) => register,
            None => {
                let register = self.alloc_register(range)?;
                self.completion_pool.push(register);
                register
            }
        };
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, inner, undefined)?;
        self.completion = Some(inner);
        self.completion_depth += 1;
        let result = lower(self, builder);
        self.completion_depth -= 1;
        self.completion = Some(outer);
        result?;
        self.move_to(range, outer, inner)
    }
    fn lower_without_completion(
        &mut self,
        builder: &mut ModuleBuilder,
        lower: impl FnOnce(&mut Self, &mut ModuleBuilder) -> Result<(), LowerError>,
    ) -> Result<(), LowerError> {
        let completion = self.completion.take();
        let result = lower(self, builder);
        self.completion = completion;
        result
    }
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }
    fn resolve(&self, name: &str) -> Option<Binding> {
        self.resolve_indexed(name).map(|(_, binding)| binding)
    }
    fn resolve_indexed(&self, name: &str) -> Option<(usize, Binding)> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, scope)| scope.get(name).copied().map(|binding| (index, binding)))
    }
    fn declare(&mut self, name: String, binding: Binding, declaration_scope: DeclarationScope) {
        if matches!(declaration_scope, DeclarationScope::Function) {
            self.captured_names.remove(&name);
        }
        let scope = match declaration_scope {
            DeclarationScope::Function => self
                .scopes
                .first_mut()
                .expect("a function context always holds its root scope"),
            DeclarationScope::Lexical | DeclarationScope::Iteration => self
                .scopes
                .last_mut()
                .expect("a function context always holds at least one scope"),
        };
        scope.insert(name, binding);
    }
    fn generated_text(&self, id: NodeId) -> Option<&str> {
        self.jsx_plan.and_then(|plan| plan.generated_text.get(id))
    }
    fn identifier_text(&self, identifier: &IdentifierNode) -> Result<String, LowerError> {
        if let Some(text) = self.generated_text(identifier.id()) {
            return Ok(text.to_owned());
        }
        let token = identifier.data().token();
        if token.is_missing() {
            return Err(self.missing(identifier.range(), NodeKind::Identifier));
        }
        let Some(text) = self.file.identifier_text(token) else {
            return Err(self.missing(identifier.range(), NodeKind::Identifier));
        };
        Ok(text.into_owned())
    }
    fn private_text(&self, private: &PrivateIdentifierNode) -> Result<String, LowerError> {
        let token = private.data().token();
        if token.is_missing() {
            return Err(self.missing(private.range(), NodeKind::PrivateIdentifier));
        }
        let Some(text) = self.file.token_text(token) else {
            return Err(self.missing(private.range(), NodeKind::PrivateIdentifier));
        };
        Ok(text.to_owned())
    }
    fn declare_initialized(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        value: Register,
        range: TextRange,
        site: BindingSite,
        declaration_scope: DeclarationScope,
    ) -> Result<(), LowerError> {
        if self.top_level && !matches!(declaration_scope, DeclarationScope::Iteration) {
            let id = builder.intern(Constant::String(EcmaString::encode(name)), range)?;
            self.emit(range, Instruction::StoreGlobal { name: id, value })?;
            return Ok(());
        }
        if self.capture_plan.captures(name, site, declaration_scope) {
            let cell = self.alloc_register(range)?;
            self.emit(range, Instruction::CreateArray { dst: cell })?;
            self.emit(range, Instruction::ArrayPush { array: cell, value })?;
            self.declare(name.to_owned(), Binding::Cell(cell), declaration_scope);
        } else {
            let home = self.alloc_register(range)?;
            self.move_to(range, home, value)?;
            self.declare(name.to_owned(), Binding::Local(home), declaration_scope);
        }
        Ok(())
    }
    fn predeclare_captured_binding(
        &mut self,
        name: &str,
        range: TextRange,
        site: BindingSite,
        declaration_scope: DeclarationScope,
    ) -> Result<(), LowerError> {
        if self.top_level
            || !self
                .capture_plan
                .requires_cell(name, site, declaration_scope)
        {
            return Ok(());
        }
        let identity = binding_identity(name, site, declaration_scope);
        if self.predeclared_cells.contains_key(&identity) {
            return Ok(());
        }
        if matches!(declaration_scope, DeclarationScope::Function)
            && let Some(Binding::Cell(cell)) = self
                .scopes
                .first()
                .and_then(|scope| scope.get(name).copied())
        {
            self.predeclared_cells.insert(identity, cell);
            return Ok(());
        }
        let cell = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateCell { dst: cell })?;
        self.declare(name.to_owned(), Binding::Cell(cell), declaration_scope);
        self.predeclared_cells.insert(identity, cell);
        Ok(())
    }
    fn predeclare_captured_pattern(
        &mut self,
        pattern: &Pattern,
        declaration_scope: DeclarationScope,
    ) -> Result<(), LowerError> {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                self.predeclare_captured_binding(
                    &name,
                    identifier.range(),
                    binding_site(identifier.range()),
                    declaration_scope,
                )
            }
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.predeclare_captured_pattern(&property.binding, declaration_scope)?;
                }
                Ok(())
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(pattern) = element {
                        self.predeclare_captured_pattern(pattern, declaration_scope)?;
                    }
                }
                Ok(())
            }
            BindingPattern::Assignment(assignment) => {
                self.predeclare_captured_pattern(&assignment.left, declaration_scope)
            }
            BindingPattern::Rest(rest) => {
                self.predeclare_captured_pattern(&rest.argument, declaration_scope)
            }
            BindingPattern::Missing(_) => Ok(()),
        }
    }
    fn predeclare_class_expression_binding(
        &mut self,
        name: &str,
        range: TextRange,
        site: BindingSite,
    ) -> Result<Register, LowerError> {
        let identity = binding_identity(name, site, DeclarationScope::Lexical);
        if let Some(cell) = self.predeclared_cells.get(&identity).copied() {
            return Ok(cell);
        }
        let cell = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateCell { dst: cell })?;
        self.declare(
            name.to_owned(),
            Binding::Cell(cell),
            DeclarationScope::Lexical,
        );
        self.predeclared_cells.insert(identity, cell);
        Ok(cell)
    }
    fn cell_value(
        &mut self,
        builder: &mut ModuleBuilder,
        cell: Register,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        let key = self.load_constant(builder, Constant::Int32(0), range)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst,
                object: cell,
                key,
            },
        )?;
        Ok(dst)
    }
    fn store_cell(
        &mut self,
        builder: &mut ModuleBuilder,
        cell: Register,
        value: Register,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let key = self.load_constant(builder, Constant::Int32(0), range)?;
        self.emit(
            range,
            Instruction::SetProperty {
                object: cell,
                key,
                value,
            },
        )?;
        Ok(())
    }
    fn rebind_iteration_cell(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let Some(Binding::Cell(cell)) = self.resolve(name) else {
            return Ok(());
        };
        let value = self.cell_value(builder, cell, range)?;
        self.emit(range, Instruction::CreateArray { dst: cell })?;
        self.emit(range, Instruction::ArrayPush { array: cell, value })?;
        Ok(())
    }
    fn declaration_names(&self, declaration: &VariableDeclaration) -> Vec<String> {
        let mut names = Vec::new();
        for declarator in &declaration.declarations {
            collect_pattern_names(self.file, &declarator.data().binding, &mut names);
        }
        names
    }
    fn rebind_iteration_cells(
        &mut self,
        builder: &mut ModuleBuilder,
        names: &[String],
        range: TextRange,
    ) -> Result<(), LowerError> {
        for name in names {
            self.rebind_iteration_cell(builder, name, range)?;
        }
        Ok(())
    }
    fn store_binding(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        value: Register,
        range: TextRange,
        site: BindingSite,
        declaration_scope: DeclarationScope,
    ) -> Result<(), LowerError> {
        let identity = binding_identity(name, site, declaration_scope);
        if let Some(cell) = self.predeclared_cells.get(&identity).copied() {
            return self.store_cell(builder, cell, value, range);
        }
        if matches!(declaration_scope, DeclarationScope::Function)
            && let Some(binding) = self
                .scopes
                .first()
                .and_then(|scope| scope.get(name).copied())
        {
            return match binding {
                Binding::Local(home) => self.move_to(range, home, value),
                Binding::Cell(cell) => self.store_cell(builder, cell, value, range),
                Binding::ConstEnum(_) => Err(self.error(
                    range,
                    LowerErrorKind::ConstEnumOperation {
                        operation: ConstEnumOperation::Write,
                    },
                )),
            };
        }
        self.declare_initialized(builder, name, value, range, site, declaration_scope)
    }
    fn hoist_vars(
        &mut self,
        builder: &mut ModuleBuilder,
        statements: &[Stmt],
        range: TextRange,
    ) -> Result<(), LowerError> {
        if self.top_level {
            return Ok(());
        }
        let mut names = Vec::new();
        collect_var_names(self.file, statements, &mut names);
        let mut seen = HashSet::new();
        for name in names {
            if !seen.insert(name.clone()) {
                continue;
            }
            if self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(&name))
            {
                continue;
            }
            let id = builder.intern(Constant::Undefined, range)?;
            if self
                .capture_plan
                .captures(&name, binding_site(range), DeclarationScope::Function)
            {
                let value = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::LoadConst {
                        dst: value,
                        constant: id,
                    },
                )?;
                let cell = self.alloc_register(range)?;
                self.emit(range, Instruction::CreateArray { dst: cell })?;
                self.emit(range, Instruction::ArrayPush { array: cell, value })?;
                self.declare(name, Binding::Cell(cell), DeclarationScope::Function);
            } else {
                let home = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::LoadConst {
                        dst: home,
                        constant: id,
                    },
                )?;
                self.declare(name, Binding::Local(home), DeclarationScope::Function);
            }
        }
        Ok(())
    }
    /// Whether a live with region still precedes `name` given the binding floor.
    /// Captured names restored at scope 0 consult `captured_names` so nested
    /// closures preserve per-site precedence across further capture boundaries.
    fn with_region_applies(&self, name: &str, floor: Option<usize>, region: &WithRegion) -> bool {
        match floor {
            None => true,
            Some(index) if index < region.scope_depth => true,
            // Captured outer names share scope index 0 with captured with
            // regions but must not shadow the sites listed for that name;
            // params/vars clear `captured_names` in `declare` and do shadow.
            Some(0)
                if region.scope_depth == 0
                    && self
                        .captured_names
                        .get(name)
                        .is_some_and(|sites| sites.contains(&region.site)) =>
            {
                true
            }
            Some(_) => false,
        }
    }
    /// With-region sites that still precede `name` in this context. Used as
    /// `CaptureKey::Name` provenance so a further nested closure keeps the same
    /// per-site relation the current frame would consult.
    fn preceding_with_sites(&self, name: &str) -> Vec<BindingSite> {
        let floor = self.resolve_indexed(name).map(|(index, _)| index);
        self.with_regions
            .iter()
            .filter(|region| self.with_region_applies(name, floor, region))
            .map(|region| region.site)
            .collect()
    }
    fn applicable_with_regions(&self, name: &str) -> Vec<Register> {
        if self.with_regions.is_empty() {
            return Vec::new();
        }
        let floor = self.resolve_indexed(name).map(|(index, _)| index);
        self.with_regions
            .iter()
            .rev()
            .filter(|region| self.with_region_applies(name, floor, region))
            .map(|region| region.object)
            .collect()
    }
    /// Runs the live with-region membership walk for `name` and returns a
    /// snapshot for the *current* lookup. Callers that evaluate an RHS before
    /// PutValue must invoke this again at write time rather than reusing a
    /// pre-RHS snapshot (Node re-resolves PutValue after the RHS).
    fn freeze_with_base(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        range: TextRange,
    ) -> Result<Option<WithBase>, LowerError> {
        let objects = self.applicable_with_regions(name);
        if objects.is_empty() {
            return Ok(None);
        }
        let key = self.string_reg(builder, EcmaString::encode(name), range)?;
        let undef = self.undefined(builder, range)?;
        let fals = self.load_constant(builder, Constant::Boolean(false), range)?;
        let tru = self.load_constant(builder, Constant::Boolean(true), range)?;
        let base = self.alloc_register(range)?;
        self.move_to(range, base, undef)?;
        let found = self.alloc_register(range)?;
        self.move_to(range, found, fals)?;
        let mut done = Vec::new();
        for object in objects {
            let has = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::WithHasBinding {
                    dst: has,
                    object,
                    key,
                },
            )?;
            let miss = self.emit(
                range,
                Instruction::JumpIfFalse {
                    condition: has,
                    target: Pc::new(0),
                },
            )?;
            self.move_to(range, base, object)?;
            self.move_to(range, found, tru)?;
            done.push(self.emit(range, Instruction::Jump { target: Pc::new(0) })?);
            self.patch_jump(miss, self.next_pc());
        }
        let join = self.next_pc();
        for jump in done {
            self.patch_jump(jump, join);
        }
        Ok(Some(WithBase { base, found, key }))
    }
    fn with_read_from(
        &mut self,
        builder: &mut ModuleBuilder,
        frozen: WithBase,
        name: &str,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        let result = self.alloc_register(range)?;
        let miss = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: frozen.found,
                target: Pc::new(0),
            },
        )?;
        let value = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: value,
                object: frozen.base,
                key: frozen.key,
            },
        )?;
        self.move_to(range, result, value)?;
        let skip = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(miss, self.next_pc());
        let fallback = self.read_name_static(builder, name, range)?;
        self.move_to(range, result, fallback)?;
        self.patch_jump(skip, self.next_pc());
        Ok(result)
    }
    fn with_write_to(
        &mut self,
        builder: &mut ModuleBuilder,
        frozen: WithBase,
        name: &str,
        value: Register,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let miss = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: frozen.found,
                target: Pc::new(0),
            },
        )?;
        self.emit(
            range,
            Instruction::SetProperty {
                object: frozen.base,
                key: frozen.key,
                value,
            },
        )?;
        let skip = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(miss, self.next_pc());
        self.assign_name_static(builder, name, value, range)?;
        self.patch_jump(skip, self.next_pc());
        Ok(())
    }
    fn read_name_static(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        if let Some(binding) = self.resolve(name) {
            return match binding {
                Binding::Local(register) => Ok(register),
                Binding::Cell(cell) => self.cell_value(builder, cell, range),
                Binding::ConstEnum(_) => Err(self.error(
                    range,
                    LowerErrorKind::ConstEnumOperation {
                        operation: ConstEnumOperation::Read,
                    },
                )),
            };
        }
        if name == "arguments"
            && let Some(register) = self.arguments_value(builder, range)?
        {
            return Ok(register);
        }
        if name == "undefined" {
            return self.undefined(builder, range);
        }
        let id = builder.intern(Constant::String(EcmaString::encode(name)), range)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::LoadGlobal { dst, name: id })?;
        Ok(dst)
    }
    fn assign_name_static(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        value: Register,
        range: TextRange,
    ) -> Result<(), LowerError> {
        if let Some(binding) = self.resolve(name) {
            return match binding {
                Binding::Local(home) => self.move_to(range, home, value),
                Binding::Cell(cell) => {
                    let _ = self.cell_value(builder, cell, range)?;
                    self.store_cell(builder, cell, value, range)
                }
                Binding::ConstEnum(_) => Err(self.error(
                    range,
                    LowerErrorKind::ConstEnumOperation {
                        operation: ConstEnumOperation::Write,
                    },
                )),
            };
        }
        let id = builder.intern(Constant::String(EcmaString::encode(name)), range)?;
        self.emit(range, Instruction::StoreGlobal { name: id, value })?;
        Ok(())
    }
    fn read_name(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        if let Some(frozen) = self.freeze_with_base(builder, name, range)? {
            return self.with_read_from(builder, frozen, name, range);
        }
        self.read_name_static(builder, name, range)
    }
    fn assign_name(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &str,
        value: Register,
        range: TextRange,
    ) -> Result<(), LowerError> {
        if let Some(frozen) = self.freeze_with_base(builder, name, range)? {
            return self.with_write_to(builder, frozen, name, value, range);
        }
        self.assign_name_static(builder, name, value, range)
    }
    fn this_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        if let Some(cell) = self.this_cell {
            return self.cell_value(builder, cell, range);
        }
        if let Some(register) = self.this_capture {
            return Ok(register);
        }
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::LoadThis { dst })?;
        Ok(dst)
    }
    fn new_target_value(&mut self, range: TextRange) -> Result<Register, LowerError> {
        if let Some(register) = self.new_target_capture {
            return Ok(register);
        }
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::LoadNewTarget { dst })?;
        Ok(dst)
    }
    fn arguments_value(
        &mut self,
        _builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<Option<Register>, LowerError> {
        match self.arguments_source {
            ArgumentsSource::Own => {
                let dst = self.alloc_register(range)?;
                self.emit(range, Instruction::LoadArguments { dst })?;
                Ok(Some(dst))
            }
            ArgumentsSource::Captured(register) => Ok(Some(register)),
            ArgumentsSource::None => Ok(None),
        }
    }
    fn lower_top_level(
        &mut self,
        builder: &mut ModuleBuilder,
        statements: &[Stmt],
    ) -> Result<(), LowerError> {
        self.instantiate_declarations(builder, statements, false)?;
        self.lower_statement_list(builder, statements)
    }
    fn lower_statement_list(
        &mut self,
        builder: &mut ModuleBuilder,
        statements: &[Stmt],
    ) -> Result<(), LowerError> {
        self.close_statement_list(builder, |context, builder| {
            for statement in statements {
                context.lower_statement(builder, statement)?;
            }
            Ok(())
        })
    }
    fn close_statement_list(
        &mut self,
        builder: &mut ModuleBuilder,
        body: impl FnOnce(&mut Self, &mut ModuleBuilder) -> Result<(), LowerError>,
    ) -> Result<(), LowerError> {
        let disposal_base = self.disposal_stack.len();
        if let Err(error) = body(self, builder) {
            self.abandon_disposals(disposal_base);
            return Err(error);
        }
        self.close_disposals(builder, disposal_base)
    }
    fn abandon_disposals(&mut self, disposal_base: usize) {
        while self.disposal_stack.len() > disposal_base {
            self.disposal_stack.pop();
            let frame = self.finally_stack.pop().expect("disposal frame present");
            debug_assert_eq!(frame.kind, FinallyKind::Disposal);
        }
    }
    fn instantiate_declarations(
        &mut self,
        builder: &mut ModuleBuilder,
        statements: &[Stmt],
        switch_scope: bool,
    ) -> Result<(), LowerError> {
        let declarations = collect_immediate_declarations(self.file, statements);
        for declaration in &declarations {
            if matches!(&declaration.kind, ImmediateDeclarationKind::Lexical)
                && (switch_scope
                    || self.capture_plan.requires_cell(
                        &declaration.name,
                        declaration.site,
                        DeclarationScope::Lexical,
                    ))
            {
                self.predeclare_captured_binding(
                    &declaration.name,
                    declaration.range,
                    declaration.site,
                    DeclarationScope::Lexical,
                )?;
            }
        }
        for declaration in declarations {
            if let ImmediateDeclarationKind::Function(function) = declaration.kind {
                self.instantiate_function_declaration(
                    builder,
                    declaration.range,
                    &declaration.name,
                    declaration.site,
                    function,
                )?;
            }
        }
        Ok(())
    }
    fn lower_statement(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
    ) -> Result<(), LowerError> {
        let range = statement.range();
        match statement.data() {
            Statement::Interface(_) | Statement::TypeAlias(_) | Statement::Declare(_) => Ok(()),
            Statement::Import(import) => self.lower_import(builder, range, import),
            Statement::ImportEquals(import) => {
                if self.goal == LoweringGoal::ClassicScript {
                    return Err(self.error(range, LowerErrorKind::ImportDeclarationInScript));
                }
                if import.is_type_only
                    || (self.goal == LoweringGoal::ProgramModule
                        && matches!(
                            &import.reference,
                            crate::syntax::ExternalModuleReference::Require(_)
                        ))
                {
                    Ok(())
                } else if matches!(
                    &import.reference,
                    crate::syntax::ExternalModuleReference::Qualified(_)
                ) {
                    self.lower_import_equals(builder, statement, range, import)
                } else {
                    Err(self.unsupported(range, UnsupportedConstruct::RuntimeImportEquals))
                }
            }
            Statement::Export(export) => {
                self.lower_export(builder, range, export)?;
                if let ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) = export
                {
                    self.publish_namespace_exports(builder, inner)?;
                }
                Ok(())
            }
            Statement::Variable(declaration) => {
                self.lower_variable_declaration(builder, declaration)?;
                self.publish_namespace_exports(builder, statement)
            }
            Statement::Function(_) => self.publish_namespace_exports(builder, statement),
            Statement::Class(class) => {
                self.lower_class_declaration(builder, range, class, None)?;
                self.publish_namespace_exports(builder, statement)
            }
            Statement::Enum(declaration) => {
                self.lower_enum_declaration(builder, statement, declaration)?;
                self.publish_namespace_exports(builder, statement)
            }
            Statement::Namespace(declaration) => {
                self.lower_namespace_declaration(builder, statement, declaration)
            }
            Statement::Block(block) => {
                self.push_scope();
                let result = self.lower_block(builder, block.data());
                self.pop_scope();
                result
            }
            Statement::Empty => Ok(()),
            Statement::Expression(expression) => {
                let value = self.lower_expression(builder, &expression.expression)?;
                if let Some(completion) = self.completion {
                    self.move_to(range, completion, value)?;
                }
                Ok(())
            }
            Statement::If(if_statement) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_if(builder, if_statement)
                })
            }
            Statement::Switch(switch) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_switch(builder, range, switch, Vec::new())
                })
            }
            Statement::For(for_statement) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_for(builder, for_statement, Vec::new())
                })
            }
            Statement::ForIn(for_in) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_for_in(builder, range, for_in, Vec::new())
                })
            }
            Statement::ForOf(for_of) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_for_of(builder, range, for_of, Vec::new())
                })
            }
            Statement::While(while_statement) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_while(builder, while_statement, Vec::new())
                })
            }
            Statement::DoWhile(do_while) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_do_while(builder, do_while, Vec::new())
                })
            }
            Statement::Try(try_statement) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_try(builder, range, try_statement)
                })
            }
            Statement::With(statement) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_with(builder, range, statement)
                })
            }
            Statement::Labeled(labeled) => {
                self.lower_normalizing_statement(builder, range, |this, builder| {
                    this.lower_labeled(builder, range, labeled)
                })
            }
            Statement::Break(jump) => {
                let label = jump
                    .label
                    .as_ref()
                    .map(|label| self.identifier_text(label))
                    .transpose()?;
                self.lower_break(builder, range, label.as_deref())
            }
            Statement::Continue(jump) => {
                let label = jump
                    .label
                    .as_ref()
                    .map(|label| self.identifier_text(label))
                    .transpose()?;
                self.lower_continue(builder, range, label.as_deref())
            }
            Statement::Return(return_statement) => {
                if self.top_level {
                    return Err(self.error(range, LowerErrorKind::ReturnOutsideFunction));
                }
                let value = match &return_statement.argument {
                    Some(expression) => self.lower_expression(builder, expression)?,
                    None => self.undefined(builder, range)?,
                };
                if self.route_through_finally(
                    builder,
                    range,
                    COMPLETION_RETURN,
                    Some(value),
                    None,
                )? {
                    return Ok(());
                }
                self.emit_function_return(builder, range, value)?;
                Ok(())
            }
            Statement::Throw(throw) => {
                let value = self.lower_expression(builder, &throw.argument)?;
                self.emit(range, Instruction::Throw { value })?;
                Ok(())
            }
            Statement::Debugger => Ok(()),
            Statement::Missing(missing) => Err(self.missing(range, missing.expected())),
        }
    }
    fn lower_block(
        &mut self,
        builder: &mut ModuleBuilder,
        block: &Block,
    ) -> Result<(), LowerError> {
        self.instantiate_declarations(builder, &block.statements, false)?;
        self.lower_statement_list(builder, &block.statements)
    }
    fn lower_nested(&mut self, builder: &mut ModuleBuilder, body: &Stmt) -> Result<(), LowerError> {
        self.push_scope();
        let result = self.lower_statement(builder, body);
        self.pop_scope();
        result
    }
    fn lower_with(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        statement: &WithStatement,
    ) -> Result<(), LowerError> {
        let value = self.lower_expression(builder, &statement.object)?;
        let object = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::ToObject {
                dst: object,
                src: value,
            },
        )?;
        self.push_scope();
        self.with_regions.push(WithRegion {
            site: binding_site(range),
            object,
            scope_depth: self.scopes.len() - 1,
        });
        let result = self.lower_statement(builder, &statement.body);
        let popped = self.with_regions.pop();
        debug_assert!(popped.is_some_and(|region| region.object == object));
        self.pop_scope();
        result
    }
    fn lower_labeled(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        labeled: &LabeledStatement,
    ) -> Result<(), LowerError> {
        let mut labels = vec![self.identifier_text(&labeled.label)?];
        let mut body = labeled.body.as_ref();
        while let Statement::Labeled(nested) = body.data() {
            labels.push(self.identifier_text(&nested.label)?);
            body = nested.body.as_ref();
        }
        match body.data() {
            Statement::Switch(statement) => self.lower_switch(builder, range, statement, labels),
            Statement::For(statement) => self.lower_for(builder, statement, labels),
            Statement::ForIn(statement) => self.lower_for_in(builder, range, statement, labels),
            Statement::ForOf(statement) => self.lower_for_of(builder, range, statement, labels),
            Statement::While(statement) => self.lower_while(builder, statement, labels),
            Statement::DoWhile(statement) => self.lower_do_while(builder, statement, labels),
            _ => self.lower_label_target(builder, range, body, labels),
        }
    }
    fn lower_label_target(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        body: &Stmt,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        self.push_control_target(range, ControlTargetKind::Label, labels)?;
        let result = self.lower_statement(builder, body);
        let target = self
            .control_targets
            .pop()
            .expect("labeled statement target is balanced");
        result?;
        let exit = self.next_pc();
        for jump in target.breaks {
            self.patch_jump(jump, exit);
        }
        Ok(())
    }
    fn push_control_target(
        &mut self,
        range: TextRange,
        kind: ControlTargetKind,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        i32::try_from(self.control_targets.len()).map_err(|_| {
            self.error(
                range,
                LowerErrorKind::Capacity(CapacityLimit::ControlTargets),
            )
        })?;
        self.control_targets.push(ControlTarget {
            breaks: Vec::new(),
            continues: Vec::new(),
            kind,
            labels,
        });
        Ok(())
    }
    fn break_target(&self, range: TextRange, label: Option<&str>) -> Result<usize, LowerError> {
        let target = match label {
            Some(label) => self
                .control_targets
                .iter()
                .rposition(|target| target.labels.iter().any(|candidate| candidate == label)),
            None => self
                .control_targets
                .iter()
                .rposition(|target| target.kind != ControlTargetKind::Label),
        };
        target.ok_or_else(|| {
            self.error(
                range,
                LowerErrorKind::InvalidControlFlow {
                    operation: "break target is not live",
                },
            )
        })
    }
    fn continue_target(&self, range: TextRange, label: Option<&str>) -> Result<usize, LowerError> {
        let target = match label {
            Some(label) => self
                .control_targets
                .iter()
                .rposition(|target| target.labels.iter().any(|candidate| candidate == label)),
            None => self
                .control_targets
                .iter()
                .rposition(|target| target.kind == ControlTargetKind::Iteration),
        }
        .ok_or_else(|| {
            self.error(
                range,
                LowerErrorKind::InvalidControlFlow {
                    operation: "continue target is not live",
                },
            )
        })?;
        if self.control_targets[target].kind != ControlTargetKind::Iteration {
            return Err(self.error(
                range,
                LowerErrorKind::InvalidControlFlow {
                    operation: "continue target is not an iteration statement",
                },
            ));
        }
        Ok(target)
    }
    fn lower_if(
        &mut self,
        builder: &mut ModuleBuilder,
        if_statement: &IfStatement,
    ) -> Result<(), LowerError> {
        let range = if_statement.test.range();
        let condition = self.lower_expression(builder, &if_statement.test)?;
        let to_else = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition,
                target: Pc::new(0),
            },
        )?;
        self.lower_nested(builder, &if_statement.consequent)?;
        match &if_statement.alternate {
            Some(alternate) => {
                let to_end = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                let else_pc = self.next_pc();
                self.patch_jump(to_else, else_pc);
                self.lower_nested(builder, alternate)?;
                let end_pc = self.next_pc();
                self.patch_jump(to_end, end_pc);
            }
            None => {
                let end_pc = self.next_pc();
                self.patch_jump(to_else, end_pc);
            }
        }
        Ok(())
    }
    fn lower_while(
        &mut self,
        builder: &mut ModuleBuilder,
        while_statement: &WhileStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let range = while_statement.test.range();
        let head = self.next_pc();
        let condition = self.lower_expression(builder, &while_statement.test)?;
        let exit_jump = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition,
                target: Pc::new(0),
            },
        )?;
        self.push_control_target(range, ControlTargetKind::Iteration, labels)?;
        self.lower_nested(builder, &while_statement.body)?;
        self.emit(range, Instruction::Jump { target: head })?;
        let exit = self.next_pc();
        self.patch_jump(exit_jump, exit);
        let frame = self.control_targets.pop().expect("loop frame is balanced");
        for jump in frame.breaks {
            self.patch_jump(jump, exit);
        }
        for jump in frame.continues {
            self.patch_jump(jump, head);
        }
        Ok(())
    }
    fn lower_do_while(
        &mut self,
        builder: &mut ModuleBuilder,
        do_while: &DoWhileStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let range = do_while.test.range();
        let head = self.next_pc();
        self.push_control_target(range, ControlTargetKind::Iteration, labels)?;
        self.lower_nested(builder, &do_while.body)?;
        let test_pc = self.next_pc();
        let condition = self.lower_expression(builder, &do_while.test)?;
        self.emit(
            range,
            Instruction::JumpIfTrue {
                condition,
                target: head,
            },
        )?;
        let exit = self.next_pc();
        let frame = self.control_targets.pop().expect("loop frame is balanced");
        for jump in frame.breaks {
            self.patch_jump(jump, exit);
        }
        for jump in frame.continues {
            self.patch_jump(jump, test_pc);
        }
        Ok(())
    }
    fn lower_for(
        &mut self,
        builder: &mut ModuleBuilder,
        for_statement: &ForStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        self.push_scope();
        let result = self.lower_for_inner(builder, for_statement, labels);
        self.pop_scope();
        result
    }
    fn lower_for_inner(
        &mut self,
        builder: &mut ModuleBuilder,
        for_statement: &ForStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let per_iteration_names = match &for_statement.initializer {
            Some(ForInitializer::Variable(declaration))
                if matches!(declaration.kind, VariableKind::Let | VariableKind::Const) =>
            {
                self.declaration_names(declaration)
            }
            _ => Vec::new(),
        };
        if let Some(initializer) = &for_statement.initializer {
            match initializer {
                ForInitializer::Variable(declaration) => {
                    if matches!(declaration.kind, VariableKind::Let | VariableKind::Const) {
                        self.lower_iteration_variable_declaration(builder, declaration)?;
                    } else {
                        self.lower_variable_declaration(builder, declaration)?;
                    }
                }
                ForInitializer::Expression(expression) => {
                    self.lower_expression(builder, expression)?;
                }
            }
        }
        let head = self.next_pc();
        let exit_jump = match &for_statement.test {
            Some(test) => {
                let condition = self.lower_expression(builder, test)?;
                Some(self.emit(
                    test.range(),
                    Instruction::JumpIfFalse {
                        condition,
                        target: Pc::new(0),
                    },
                )?)
            }
            None => None,
        };
        self.push_control_target(
            head_range(for_statement),
            ControlTargetKind::Iteration,
            labels,
        )?;
        self.lower_nested(builder, &for_statement.body)?;
        let update_pc = self.next_pc();
        self.rebind_iteration_cells(builder, &per_iteration_names, head_range(for_statement))?;
        if let Some(update) = &for_statement.update {
            self.lower_expression(builder, update)?;
        }
        self.emit(
            head_range(for_statement),
            Instruction::Jump { target: head },
        )?;
        let exit = self.next_pc();
        if let Some(jump) = exit_jump {
            self.patch_jump(jump, exit);
        }
        let frame = self.control_targets.pop().expect("loop frame is balanced");
        for jump in frame.breaks {
            self.patch_jump(jump, exit);
        }
        for jump in frame.continues {
            self.patch_jump(jump, update_pc);
        }
        Ok(())
    }
    fn lower_for_in(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        for_in: &ForInStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let subject = self.lower_expression(builder, &for_in.object)?;
        self.lower_iteration(
            builder,
            IterationLowering {
                range,
                subject,
                kind: IteratorKind::Keys,
                binding: &for_in.binding,
                body: &for_in.body,
                labels,
            },
        )
    }
    fn lower_for_of(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        for_of: &ForOfStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let subject = self.lower_expression(builder, &for_of.iterable)?;
        let kind = match for_of.mode {
            ForOfMode::Sync => IteratorKind::Sync,
            ForOfMode::Async => IteratorKind::Async,
        };
        self.lower_iteration(
            builder,
            IterationLowering {
                range,
                subject,
                kind,
                binding: &for_of.binding,
                body: &for_of.body,
                labels,
            },
        )
    }
    fn lower_iteration(
        &mut self,
        builder: &mut ModuleBuilder,
        lowering: IterationLowering<'_>,
    ) -> Result<(), LowerError> {
        let IterationLowering {
            range,
            subject,
            kind,
            binding,
            body,
            labels,
        } = lowering;
        let cleanup = kind != IteratorKind::Keys;
        let scope_depth = self.scopes.len();
        let control_depth = self.control_targets.len();
        let finally_depth = self.finally_stack.len();
        self.push_scope();
        let result = (|| {
            let iterator = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::GetIterator {
                    dst: iterator,
                    src: subject,
                    kind,
                },
            )?;
            let completion = if cleanup {
                let kind_reg = self.alloc_register(range)?;
                let value_reg = self.alloc_register(range)?;
                let target_reg = self.alloc_register(range)?;
                let normal =
                    self.load_constant(builder, Constant::Int32(COMPLETION_NORMAL), range)?;
                self.move_to(range, kind_reg, normal)?;
                self.move_to(range, target_reg, normal)?;
                let undefined = self.undefined(builder, range)?;
                self.move_to(range, value_reg, undefined)?;
                Some((kind_reg, value_reg, target_reg))
            } else {
                None
            };
            let done = self.alloc_register(range)?;
            let value = self.alloc_register(range)?;
            let head = self.next_pc();
            if kind == IteratorKind::Async {
                // `for await`: step the async iterator to its raw (thenable)
                // result, suspend until it settles, then read `done`/`value` from
                // the settled iterator result object. The awaited register is
                // defined by `Await` on the resume edge, which is exactly the
                // fall-through pc `IteratorResult` executes at.
                let step = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::IteratorStep {
                        dst: step,
                        iterator,
                    },
                )?;
                let settled = self.emit_await(range, step)?;
                self.emit(
                    range,
                    Instruction::IteratorResult {
                        done,
                        value,
                        result: settled,
                    },
                )?;
            } else {
                self.emit(
                    range,
                    Instruction::IteratorNext {
                        done,
                        value,
                        iterator,
                    },
                )?;
            }
            let exit_jump = self.emit(
                range,
                Instruction::JumpIfTrue {
                    condition: done,
                    target: Pc::new(0),
                },
            )?;
            self.push_control_target(range, ControlTargetKind::Iteration, labels)?;
            let loop_target = self.control_targets.len() - 1;
            if let Some((kind_reg, value_reg, target_reg)) = completion {
                self.finally_stack.push(FinallyFrame {
                    kind: FinallyKind::IteratorCleanup { loop_target },
                    kind_reg,
                    value_reg,
                    target_reg,
                    pending: Vec::new(),
                    control_depth: self.control_targets.len(),
                    targets: Vec::new(),
                });
            }
            let body_start = self.next_pc();
            // Fresh per-iteration scope for the loop binding. Resource loop-head
            // bindings capture inside a close_statement_list so each iteration
            // disposes before the next step / continue, while still sitting
            // under the iterator-cleanup handler.
            self.push_scope();
            let body_result = self.close_statement_list(builder, |context, builder| {
                if let ForBinding::Variable(declaration) = binding {
                    match declaration.kind {
                        VariableKind::Using => {
                            context.capture_disposable(builder, range, value, DisposeHint::Sync)?;
                        }
                        VariableKind::AwaitUsing => {
                            if !context.can_await() {
                                return Err(context
                                    .unsupported(range, UnsupportedConstruct::UsingDeclaration));
                            }
                            context.capture_disposable(
                                builder,
                                range,
                                value,
                                DisposeHint::Async,
                            )?;
                        }
                        _ => {}
                    }
                }
                context.bind_for_binding(builder, binding, value, range)?;
                context.lower_statement(builder, body)
            });
            self.pop_scope();
            body_result?;
            self.emit(range, Instruction::Jump { target: head })?;
            let body_end = self.next_pc();
            if let Some((kind_reg, value_reg, target_reg)) = completion {
                let handler = if body_end.get() != body_start.get() {
                    let catch_register = self.alloc_register(range)?;
                    let handler_pc = self.next_pc();
                    self.push_finally_completion(
                        builder,
                        range,
                        COMPLETION_THROW,
                        Some(catch_register),
                    )?;
                    Some((handler_pc, catch_register))
                } else {
                    None
                };
                let frame = self
                    .finally_stack
                    .pop()
                    .expect("iterator cleanup frame present");
                let cleanup_pc = self.next_pc();
                for jump in frame.pending {
                    self.patch_jump(jump, cleanup_pc);
                }
                if let Some((handler_pc, catch_register)) = handler {
                    self.handlers.push(ExceptionHandler {
                        start: body_start,
                        end: body_end,
                        handler: handler_pc,
                        catch_register,
                    });
                }
                let propagate =
                    self.emit_int32_guard(builder, range, kind_reg, COMPLETION_THROW)?;
                let preserve_result = self.alloc_register(range)?;
                let preserve_called = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::IteratorClose {
                        result: preserve_result,
                        called: preserve_called,
                        iterator,
                        mode: IteratorCloseMode::PreserveAbrupt,
                    },
                )?;
                let swallow = if kind == IteratorKind::Async {
                    let await_pc = self.next_pc();
                    self.emit_await(range, preserve_result)?;
                    let catch_register = self.alloc_register(range)?;
                    Some((await_pc, catch_register))
                } else {
                    None
                };
                let dispatch_jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                let propagate_pc = self.next_pc();
                self.patch_jump(propagate, propagate_pc);
                let propagate_result = self.alloc_register(range)?;
                let propagate_called = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::IteratorClose {
                        result: propagate_result,
                        called: propagate_called,
                        iterator,
                        mode: IteratorCloseMode::Propagate,
                    },
                )?;
                let checked_result = if kind == IteratorKind::Async {
                    self.emit_await(range, propagate_result)?
                } else {
                    propagate_result
                };
                self.emit(
                    range,
                    Instruction::RequireCloseResult {
                        result: checked_result,
                        called: propagate_called,
                    },
                )?;
                let dispatch_pc = self.next_pc();
                self.patch_jump(dispatch_jump, dispatch_pc);
                if let Some((await_pc, catch_register)) = swallow {
                    self.handlers.push(ExceptionHandler {
                        start: await_pc,
                        end: Pc::new(await_pc.get() + 1),
                        handler: dispatch_pc,
                        catch_register,
                    });
                }
                self.emit_finally_dispatch(
                    builder,
                    range,
                    kind_reg,
                    value_reg,
                    target_reg,
                    &frame.targets,
                )?;
            }
            let exit = self.next_pc();
            self.patch_jump(exit_jump, exit);
            let frame = self.control_targets.pop().expect("loop frame is balanced");
            for jump in frame.breaks {
                self.patch_jump(jump, exit);
            }
            for jump in frame.continues {
                self.patch_jump(jump, head);
            }
            Ok(())
        })();
        self.scopes.truncate(scope_depth);
        self.control_targets.truncate(control_depth);
        self.finally_stack.truncate(finally_depth);
        result
    }
    fn bind_for_binding(
        &mut self,
        builder: &mut ModuleBuilder,
        binding: &ForBinding,
        value: Register,
        range: TextRange,
    ) -> Result<(), LowerError> {
        match binding {
            ForBinding::Variable(declaration) => {
                let declaration_scope = match declaration.kind {
                    VariableKind::Var => DeclarationScope::Function,
                    VariableKind::Let
                    | VariableKind::Const
                    | VariableKind::Using
                    | VariableKind::AwaitUsing => DeclarationScope::Iteration,
                };
                let declarator = declaration
                    .declarations
                    .first()
                    .ok_or_else(|| self.missing(range, NodeKind::VariableDeclarator))?;
                self.bind_pattern(
                    builder,
                    &declarator.data().binding,
                    value,
                    declaration_scope,
                )
            }
            ForBinding::Target(target) => self.assign_target(builder, target, value),
        }
    }
    fn lower_break(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        label: Option<&str>,
    ) -> Result<(), LowerError> {
        let target = self.break_target(range, label)?;
        if self.route_through_finally(builder, range, COMPLETION_BREAK, None, Some(target))? {
            return Ok(());
        }
        let jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.control_targets[target].breaks.push(jump);
        Ok(())
    }
    fn lower_continue(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        label: Option<&str>,
    ) -> Result<(), LowerError> {
        let target = self.continue_target(range, label)?;
        if self.route_through_finally(builder, range, COMPLETION_CONTINUE, None, Some(target))? {
            return Ok(());
        }
        let jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.control_targets[target].continues.push(jump);
        Ok(())
    }
    /// Routes an abrupt completion through the innermost enclosing `finally`
    /// when its resolved target predates that frame.
    fn route_through_finally(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        kind: i32,
        value: Option<Register>,
        target: Option<usize>,
    ) -> Result<bool, LowerError> {
        let Some((frame_kind, kind_reg, value_reg, target_reg, depth)) =
            self.finally_stack.last().map(|frame| {
                (
                    frame.kind,
                    frame.kind_reg,
                    frame.value_reg,
                    frame.target_reg,
                    frame.control_depth,
                )
            })
        else {
            return Ok(false);
        };
        if let FinallyKind::IteratorCleanup { loop_target } = frame_kind
            && kind == COMPLETION_CONTINUE
            && target == Some(loop_target)
        {
            return Ok(false);
        }
        if target.is_some_and(|target| target >= depth) {
            return Ok(false);
        }
        let marker = self.load_constant(builder, Constant::Int32(kind), range)?;
        self.move_to(range, kind_reg, marker)?;
        if let Some(value) = value {
            self.move_to(range, value_reg, value)?;
        }
        if let Some(target) = target {
            let target = i32::try_from(target).map_err(|_| {
                self.error(
                    range,
                    LowerErrorKind::Capacity(CapacityLimit::ControlTargets),
                )
            })?;
            let marker = self.load_constant(builder, Constant::Int32(target), range)?;
            self.move_to(range, target_reg, marker)?;
        }
        let jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        let frame = self
            .finally_stack
            .last_mut()
            .expect("finally frame present");
        frame.pending.push(jump);
        if frame.kind == FinallyKind::Disposal {
            frame.targets.push((COMPLETION_NORMAL, usize::MAX));
        }
        if let Some(target) = target {
            let completion = (kind, target);
            if !frame.targets.contains(&completion) {
                frame.targets.push(completion);
            }
        }
        Ok(true)
    }
    fn lower_switch(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        switch: &SwitchStatement,
        labels: Vec<String>,
    ) -> Result<(), LowerError> {
        let discriminant = self.lower_expression(builder, &switch.discriminant)?;
        self.push_scope();
        let switch_statements = switch
            .cases
            .iter()
            .flat_map(|case| case.data().consequent.iter().cloned())
            .collect::<Vec<_>>();
        self.instantiate_declarations(builder, &switch_statements, true)?;
        self.push_control_target(range, ControlTargetKind::Switch, labels)?;
        let mut case_jumps: Vec<Option<Pc>> = Vec::with_capacity(switch.cases.len());
        let mut default_index = None;
        for (index, case) in switch.cases.iter().enumerate() {
            match &case.data().test {
                Some(test) => {
                    let value = self.lower_expression(builder, test)?;
                    let matched = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::Binary {
                            dst: matched,
                            op: BinaryOp::StrictEqual,
                            left: discriminant,
                            right: value,
                        },
                    )?;
                    let jump = self.emit(
                        range,
                        Instruction::JumpIfTrue {
                            condition: matched,
                            target: Pc::new(0),
                        },
                    )?;
                    case_jumps.push(Some(jump));
                }
                None => {
                    default_index = Some(index);
                    case_jumps.push(None);
                }
            }
        }
        let no_match_jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        let mut body_starts: Vec<Pc> = Vec::with_capacity(switch.cases.len());
        for case in &switch.cases {
            let start = self.next_pc();
            body_starts.push(start);
            for statement in &case.data().consequent {
                self.lower_statement(builder, statement)?;
            }
        }
        let exit = self.next_pc();
        for (jump, start) in case_jumps.iter().zip(body_starts.iter()) {
            if let Some(jump) = jump {
                self.patch_jump(*jump, *start);
            }
        }
        match default_index {
            Some(index) => self.patch_jump(no_match_jump, body_starts[index]),
            None => self.patch_jump(no_match_jump, exit),
        }
        let frame = self
            .control_targets
            .pop()
            .expect("switch break frame is balanced");
        for jump in frame.breaks {
            self.patch_jump(jump, exit);
        }
        self.pop_scope();
        Ok(())
    }
    fn lower_try(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        try_statement: &crate::syntax::TryStatement,
    ) -> Result<(), LowerError> {
        let has_finally = try_statement
            .finalizer
            .as_ref()
            .is_some_and(|finalizer| !finalizer.data().statements.is_empty());
        if has_finally {
            return self.lower_try_finally(builder, range, try_statement);
        }
        let Some(handler_clause) = &try_statement.handler else {
            self.push_scope();
            let result = self.lower_block(builder, try_statement.block.data());
            self.pop_scope();
            return result;
        };
        let start = self.next_pc();
        self.push_scope();
        let block_result = self.lower_block(builder, try_statement.block.data());
        self.pop_scope();
        block_result?;
        let end = self.next_pc();
        if end.get() == start.get() {
            return Ok(());
        }
        let over_catch = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        let catch_register = self.alloc_register(range)?;
        let handler_pc = self.next_pc();
        if let Some(completion) = self.completion {
            let undefined = self.undefined(builder, range)?;
            self.move_to(range, completion, undefined)?;
        }
        self.push_scope();
        let clause = handler_clause.data();
        if let Some(binding) = &clause.binding {
            let bind_result =
                self.bind_pattern(builder, binding, catch_register, DeclarationScope::Lexical);
            if let Err(error) = bind_result {
                self.pop_scope();
                return Err(error);
            }
        }
        let catch_result = self.lower_block(builder, clause.body.data());
        self.pop_scope();
        catch_result?;
        let after = self.next_pc();
        self.patch_jump(over_catch, after);
        self.handlers.push(ExceptionHandler {
            start,
            end,
            handler: handler_pc,
            catch_register,
        });
        Ok(())
    }
    /// Lowers `try`/`finally` (with an optional `catch`) by routing every
    /// completion of the protected body through the finally block, then
    /// dispatching the recorded completion after it runs.
    fn lower_try_finally(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        try_statement: &crate::syntax::TryStatement,
    ) -> Result<(), LowerError> {
        let finalizer = try_statement
            .finalizer
            .as_ref()
            .expect("lower_try_finally is only called with a non-empty finalizer");
        let kind_reg = self.alloc_register(range)?;
        let value_reg = self.alloc_register(range)?;
        let target_reg = self.alloc_register(range)?;
        let normal = self.load_constant(builder, Constant::Int32(COMPLETION_NORMAL), range)?;
        self.move_to(range, kind_reg, normal)?;
        self.move_to(range, target_reg, normal)?;
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, value_reg, undefined)?;
        self.finally_stack.push(FinallyFrame {
            kind: FinallyKind::Finalizer,
            kind_reg,
            value_reg,
            target_reg,
            pending: Vec::new(),
            control_depth: self.control_targets.len(),
            targets: Vec::new(),
        });
        let start = self.next_pc();
        self.push_scope();
        let body_result = self.lower_block(builder, try_statement.block.data());
        self.pop_scope();
        if let Err(error) = body_result {
            self.finally_stack.pop();
            return Err(error);
        }
        let end = self.next_pc();
        // Normal completion of the try body routes to the finally.
        self.push_finally_completion(builder, range, COMPLETION_NORMAL, None)?;
        let handler = if end.get() == start.get() {
            None
        } else {
            let catch_register = self.alloc_register(range)?;
            let handler_pc = self.next_pc();
            if let Some(handler_clause) = &try_statement.handler {
                if let Some(completion) = self.completion {
                    let undefined = self.undefined(builder, range)?;
                    self.move_to(range, completion, undefined)?;
                }
                self.push_scope();
                let clause = handler_clause.data();
                if let Some(binding) = &clause.binding {
                    let bind_result = self.bind_pattern(
                        builder,
                        binding,
                        catch_register,
                        DeclarationScope::Lexical,
                    );
                    if let Err(error) = bind_result {
                        self.pop_scope();
                        self.finally_stack.pop();
                        return Err(error);
                    }
                }
                let catch_result = self.lower_block(builder, clause.body.data());
                self.pop_scope();
                if let Err(error) = catch_result {
                    self.finally_stack.pop();
                    return Err(error);
                }
                self.push_finally_completion(builder, range, COMPLETION_NORMAL, None)?;
            } else {
                // No catch: record the thrown value and re-raise after finally.
                self.push_finally_completion(
                    builder,
                    range,
                    COMPLETION_THROW,
                    Some(catch_register),
                )?;
            }
            Some((catch_register, handler_pc))
        };
        let frame = self.finally_stack.pop().expect("finally frame present");
        let finally_pc = self.next_pc();
        for jump in &frame.pending {
            self.patch_jump(*jump, finally_pc);
        }
        if let Some((catch_register, handler_pc)) = handler {
            self.handlers.push(ExceptionHandler {
                start,
                end,
                handler: handler_pc,
                catch_register,
            });
        }
        self.push_scope();
        let finally_result = self.lower_without_completion(builder, |this, builder| {
            this.lower_block(builder, finalizer.data())
        });
        self.pop_scope();
        finally_result?;
        self.emit_finally_dispatch(
            builder,
            range,
            kind_reg,
            value_reg,
            target_reg,
            &frame.targets,
        )
    }
    /// Records a completion (sets the state registers) and jumps to the pending
    /// finally entry.
    fn push_finally_completion(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        kind: i32,
        value: Option<Register>,
    ) -> Result<(), LowerError> {
        let (kind_reg, value_reg) = {
            let frame = self.finally_stack.last().expect("finally frame present");
            (frame.kind_reg, frame.value_reg)
        };
        let marker = self.load_constant(builder, Constant::Int32(kind), range)?;
        self.move_to(range, kind_reg, marker)?;
        if let Some(value) = value {
            self.move_to(range, value_reg, value)?;
        }
        let jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.finally_stack
            .last_mut()
            .expect("finally frame present")
            .pending
            .push(jump);
        Ok(())
    }
    /// After a finally block runs, resumes the recorded completion.
    fn emit_finally_dispatch(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        kind_reg: Register,
        value_reg: Register,
        target_reg: Register,
        targets: &[(i32, usize)],
    ) -> Result<(), LowerError> {
        // return
        let skip = self.emit_int32_guard(builder, range, kind_reg, COMPLETION_RETURN)?;
        if !self.route_through_finally(builder, range, COMPLETION_RETURN, Some(value_reg), None)? {
            self.emit_function_return(builder, range, value_reg)?;
        }
        let after = self.next_pc();
        self.patch_jump(skip, after);
        // throw stays direct so an enclosing catch can observe it.
        let skip = self.emit_int32_guard(builder, range, kind_reg, COMPLETION_THROW)?;
        self.emit(range, Instruction::Throw { value: value_reg })?;
        let after = self.next_pc();
        self.patch_jump(skip, after);
        for &(kind, target) in targets {
            let kind_skip = self.emit_int32_guard(builder, range, kind_reg, kind)?;
            if target == usize::MAX {
                debug_assert_eq!(kind, COMPLETION_NORMAL);
                let after = self.next_pc();
                self.patch_jump(kind_skip, after);
                continue;
            }
            let target_id = i32::try_from(target).map_err(|_| {
                self.error(
                    range,
                    LowerErrorKind::Capacity(CapacityLimit::ControlTargets),
                )
            })?;
            let target_skip = self.emit_int32_guard(builder, range, target_reg, target_id)?;
            if !self.route_through_finally(builder, range, kind, None, Some(target))? {
                let jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                if target >= self.control_targets.len() {
                    return Err(self.error(
                        range,
                        LowerErrorKind::InvalidControlFlow {
                            operation: "finally target is no longer live",
                        },
                    ));
                }
                let target = &mut self.control_targets[target];
                match kind {
                    COMPLETION_BREAK => target.breaks.push(jump),
                    COMPLETION_CONTINUE => target.continues.push(jump),
                    _ => unreachable!("only jump completions carry target ids"),
                }
            }
            let after = self.next_pc();
            self.patch_jump(target_skip, after);
            self.patch_jump(kind_skip, after);
        }
        Ok(())
    }
    /// Emits `if register != value { jump skip }`, returning the skip jump to
    /// patch past the guarded completion.
    fn emit_int32_guard(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        register: Register,
        value: i32,
    ) -> Result<Pc, LowerError> {
        let marker = self.load_constant(builder, Constant::Int32(value), range)?;
        let matched = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: matched,
                op: BinaryOp::StrictEqual,
                left: register,
                right: marker,
            },
        )?;
        self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: matched,
                target: Pc::new(0),
            },
        )
    }
    /// Emits `if register == value { jump skip }`, returning the skip jump to
    /// patch past a body that should run only when the register differs.
    fn emit_int32_skip_if(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        register: Register,
        value: i32,
    ) -> Result<Pc, LowerError> {
        let marker = self.load_constant(builder, Constant::Int32(value), range)?;
        let matched = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: matched,
                op: BinaryOp::StrictEqual,
                left: register,
                right: marker,
            },
        )?;
        self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: matched,
                target: Pc::new(0),
            },
        )
    }
    fn lower_variable_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        declaration: &VariableDeclaration,
    ) -> Result<(), LowerError> {
        let declaration_scope = match declaration.kind {
            VariableKind::Var => DeclarationScope::Function,
            VariableKind::Let
            | VariableKind::Const
            | VariableKind::Using
            | VariableKind::AwaitUsing => DeclarationScope::Lexical,
        };
        if declaration.kind == VariableKind::AwaitUsing && !self.can_await() {
            let range = declaration
                .declarations
                .first()
                .map_or_else(zero_range, |declarator| declarator.range());
            return Err(self.unsupported(range, UnsupportedConstruct::UsingDeclaration));
        }
        for declarator in &declaration.declarations {
            let range = declarator.range();
            let data = declarator.data();
            self.predeclare_captured_pattern(&data.binding, declaration_scope)?;
            let value = match &data.initializer {
                Some(initializer) => self.lower_expression(builder, initializer)?,
                None => {
                    // A bare declaration (`let x;`) binds undefined.
                    self.undefined(builder, range)?
                }
            };
            match declaration.kind {
                VariableKind::Using => {
                    self.capture_disposable(builder, range, value, DisposeHint::Sync)?;
                }
                VariableKind::AwaitUsing => {
                    self.capture_disposable(builder, range, value, DisposeHint::Async)?;
                }
                _ => {}
            }
            self.bind_pattern(builder, &data.binding, value, declaration_scope)?;
        }
        Ok(())
    }
    /// Captures a disposer immediately and opens its protected region.
    /// Initializer evaluation and method lookup therefore each happen exactly once.
    fn capture_disposable(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
        hint: DisposeHint,
    ) -> Result<(), LowerError> {
        let method = self.alloc_register(range)?;
        let capture_kind = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::DisposeCapture {
                method,
                kind: capture_kind,
                src: value,
                hint,
            },
        )?;
        let kind_reg = self.alloc_register(range)?;
        let value_reg = self.alloc_register(range)?;
        let target_reg = self.alloc_register(range)?;
        let normal = self.load_constant(builder, Constant::Int32(COMPLETION_NORMAL), range)?;
        self.move_to(range, kind_reg, normal)?;
        self.move_to(range, target_reg, normal)?;
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, value_reg, undefined)?;
        self.finally_stack.push(FinallyFrame {
            kind: FinallyKind::Disposal,
            kind_reg,
            value_reg,
            target_reg,
            pending: Vec::new(),
            control_depth: self.control_targets.len(),
            targets: Vec::new(),
        });
        self.disposal_stack.push(DisposalRecord {
            range,
            value,
            method,
            capture_kind,
            hint,
            body_start: self.next_pc(),
        });
        Ok(())
    }
    /// Closes all resources opened since `base`, innermost first.
    fn close_disposals(
        &mut self,
        builder: &mut ModuleBuilder,
        base: usize,
    ) -> Result<(), LowerError> {
        while self.disposal_stack.len() > base {
            self.close_disposable(builder)?;
        }
        Ok(())
    }
    fn close_disposable(&mut self, builder: &mut ModuleBuilder) -> Result<(), LowerError> {
        let resource = self
            .disposal_stack
            .pop()
            .expect("close_disposable requires an active resource");
        let body_end = self.next_pc();
        self.push_finally_completion(builder, resource.range, COMPLETION_NORMAL, None)?;
        let handler = if body_end.get() == resource.body_start.get() {
            None
        } else {
            let catch_register = self.alloc_register(resource.range)?;
            let handler_pc = self.next_pc();
            self.push_finally_completion(
                builder,
                resource.range,
                COMPLETION_THROW,
                Some(catch_register),
            )?;
            Some((catch_register, handler_pc))
        };
        let frame = self.finally_stack.pop().expect("disposal frame present");
        debug_assert_eq!(frame.kind, FinallyKind::Disposal);
        let disposal_pc = self.next_pc();
        for jump in &frame.pending {
            self.patch_jump(*jump, disposal_pc);
        }
        if let Some((catch_register, handler_pc)) = handler {
            self.handlers.push(ExceptionHandler {
                start: resource.body_start,
                end: body_end,
                handler: handler_pc,
                catch_register,
            });
        }
        self.emit_disposal(builder, resource, frame.kind_reg, frame.value_reg)?;
        self.emit_finally_dispatch(
            builder,
            resource.range,
            frame.kind_reg,
            frame.value_reg,
            frame.target_reg,
            &frame.targets,
        )
    }
    /// Emits disposal for one captured resource.
    ///
    /// Sync: skip nullish kinds, invoke the disposer under an exception handler.
    /// Async formal branch pattern:
    ///   awaited = undefined
    ///   skip Call when kind == 0
    ///   after Call, copy result into awaited only when kind != 2
    ///   Await(awaited)
    /// so kind 0 and sync-fallback kind 2 both await undefined (ignoring any
    /// rejected Promise from @@dispose), while kind 1 awaits the call result.
    /// The exception handler covers Call + Await; SuppressError chains disposer
    /// failures into an in-flight throw completion.
    fn emit_disposal(
        &mut self,
        builder: &mut ModuleBuilder,
        resource: DisposalRecord,
        kind_reg: Register,
        value_reg: Register,
    ) -> Result<(), LowerError> {
        let range = resource.range;
        if resource.hint == DisposeHint::Sync {
            let skip_nullish = self.emit_int32_skip_if(builder, range, resource.capture_kind, 0)?;
            let dispose_start = self.next_pc();
            let arguments = self.alloc_register(range)?;
            self.emit(range, Instruction::CreateArray { dst: arguments })?;
            let result = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Call {
                    dst: result,
                    callee: resource.method,
                    this_value: resource.value,
                    arguments,
                },
            )?;
            let dispose_end = self.next_pc();
            let after_success = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
            self.emit_disposal_handler(
                builder,
                range,
                kind_reg,
                value_reg,
                dispose_start,
                dispose_end,
                after_success,
                Some(skip_nullish),
            )?;
            return Ok(());
        }

        // Async disposal (formal branch pattern).
        let awaited = self.alloc_register(range)?;
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, awaited, undefined)?;
        // kind == 0: skip the disposer call; awaited stays undefined.
        let skip_call = self.emit_int32_skip_if(builder, range, resource.capture_kind, 0)?;
        let dispose_start = self.next_pc();
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        let result = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst: result,
                callee: resource.method,
                this_value: resource.value,
                arguments,
            },
        )?;
        // kind == 2: call @@dispose but ignore its return; keep awaited undefined.
        // kind == 1: await the call result.
        let skip_copy = self.emit_int32_skip_if(builder, range, resource.capture_kind, 2)?;
        self.move_to(range, awaited, result)?;
        self.patch_jump(skip_copy, self.next_pc());
        // kind == 0 lands here with awaited == undefined, still under the handler.
        self.patch_jump(skip_call, self.next_pc());
        self.emit_await(range, awaited)?;
        let dispose_end = self.next_pc();
        let after_success = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.emit_disposal_handler(
            builder,
            range,
            kind_reg,
            value_reg,
            dispose_start,
            dispose_end,
            after_success,
            None,
        )?;
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn emit_disposal_handler(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        kind_reg: Register,
        value_reg: Register,
        dispose_start: Pc,
        dispose_end: Pc,
        after_success: Pc,
        skip_nullish: Option<Pc>,
    ) -> Result<(), LowerError> {
        let catch_register = self.alloc_register(range)?;
        let handler_pc = self.next_pc();
        let plain = self.emit_int32_guard(builder, range, kind_reg, COMPLETION_THROW)?;
        let chained = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::SuppressError {
                dst: chained,
                error: catch_register,
                suppressed: value_reg,
            },
        )?;
        self.move_to(range, value_reg, chained)?;
        let to_set = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        let plain_pc = self.next_pc();
        self.patch_jump(plain, plain_pc);
        self.move_to(range, value_reg, catch_register)?;
        let set_pc = self.next_pc();
        self.patch_jump(to_set, set_pc);
        let throw_kind = self.load_constant(builder, Constant::Int32(COMPLETION_THROW), range)?;
        self.move_to(range, kind_reg, throw_kind)?;
        let after = self.next_pc();
        if let Some(skip_nullish) = skip_nullish {
            self.patch_jump(skip_nullish, after);
        }
        self.patch_jump(after_success, after);
        self.handlers.push(ExceptionHandler {
            start: dispose_start,
            end: dispose_end,
            handler: handler_pc,
            catch_register,
        });
        Ok(())
    }
    fn lower_enum_scalar(
        &mut self,
        builder: &mut ModuleBuilder,
        scalar: &EnumScalar,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        match scalar {
            EnumScalar::Number(value) => {
                self.load_constant(builder, Constant::Number(*value), range)
            }
            EnumScalar::String(value) => {
                self.load_constant(builder, Constant::String(value.clone()), range)
            }
        }
    }
    fn lower_enum_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
        declaration: &EnumDeclaration,
    ) -> Result<(), LowerError> {
        if declaration.is_const {
            let Some(symbol) = self.enum_facts.declaration_symbol(statement.id()) else {
                return Ok(());
            };
            let name = self.identifier_text(&declaration.name)?;
            self.declare(name, Binding::ConstEnum(symbol), DeclarationScope::Lexical);
            return Ok(());
        }
        let plan = self
            .enum_facts
            .declaration(statement.id())
            .cloned()
            .ok_or_else(|| {
                self.unsupported(statement.range(), UnsupportedConstruct::EnumDeclaration)
            })?;
        let symbol = self
            .enum_facts
            .declaration_symbol(statement.id())
            .ok_or_else(|| {
                self.unsupported(statement.range(), UnsupportedConstruct::EnumDeclaration)
            })?;
        let name = self.identifier_text(&declaration.name)?;
        let object = self.read_name(builder, &name, statement.range())?;
        let reuse = self.emit(
            statement.range(),
            Instruction::JumpIfTrue {
                condition: object,
                target: Pc::new(0),
            },
        )?;
        self.emit(statement.range(), Instruction::CreateObject { dst: object })?;
        self.assign_name(builder, &name, object, statement.range())?;
        self.patch_jump(reuse, self.next_pc());
        self.containers.push(Container {
            symbol,
            object,
            kind: ContainerKind::Enum,
        });
        for (member, member_plan) in declaration.members.iter().zip(plan.members()) {
            let EnumMemberPlan::Valid { value, .. } = member_plan else {
                continue;
            };
            let member_range = member.range();
            let key = self.string_reg(
                builder,
                member_plan
                    .name()
                    .cloned()
                    .expect("valid enum member has name"),
                member_range,
            )?;
            let value = match value {
                EnumValue::Constant(scalar) => {
                    self.lower_enum_scalar(builder, scalar, member_range)?
                }
                EnumValue::Runtime => {
                    let initializer = member
                        .data()
                        .initializer
                        .as_ref()
                        .ok_or_else(|| self.missing(member_range, NodeKind::EnumMember))?;
                    self.lower_expression(builder, initializer)?
                }
            };
            self.emit(
                member_range,
                Instruction::SetProperty { object, key, value },
            )?;
            if member_plan.reverse() {
                let reverse_name = self.string_reg(
                    builder,
                    member_plan
                        .name()
                        .cloned()
                        .expect("valid enum member has name"),
                    member_range,
                )?;
                self.emit(
                    member_range,
                    Instruction::SetProperty {
                        object,
                        key: value,
                        value: reverse_name,
                    },
                )?;
            }
        }
        let popped = self.containers.pop();
        debug_assert!(popped.is_some_and(|container| {
            container.symbol == symbol && container.kind == ContainerKind::Enum
        }));
        Ok(())
    }
    fn lower_namespace_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
        declaration: &NamespaceDeclaration,
    ) -> Result<(), LowerError> {
        let plan = self
            .namespace_facts
            .declaration(statement.id())
            .ok_or_else(|| {
                self.unsupported(
                    statement.range(),
                    UnsupportedConstruct::NamespaceDeclaration,
                )
            })?;
        if !plan.is_value_bearing() {
            return Ok(());
        }
        let symbol = self
            .namespace_facts
            .declaration_symbol(statement.id())
            .ok_or_else(|| {
                self.unsupported(
                    statement.range(),
                    UnsupportedConstruct::NamespaceDeclaration,
                )
            })?;
        let NamespaceName::Identifier {
            name: name_node, ..
        } = &declaration.name
        else {
            return Ok(());
        };
        let name = self.identifier_text(name_node)?;
        // Reuse one register across the `existing || (existing = {})` diamond so
        // the jump-if-present path still has a definite object value (same shape
        // as runtime enum container init).
        let object = match plan.acquisition() {
            ContainerAcquisition::Binding => {
                let object = self.read_name(builder, &name, statement.range())?;
                let reuse = self.emit(
                    statement.range(),
                    Instruction::JumpIfTrue {
                        condition: object,
                        target: Pc::new(0),
                    },
                )?;
                self.emit(statement.range(), Instruction::CreateObject { dst: object })?;
                self.assign_name(builder, &name, object, statement.range())?;
                self.patch_jump(reuse, self.next_pc());
                object
            }
            ContainerAcquisition::Member { parent } => {
                let parent_object = self
                    .containers
                    .iter()
                    .rev()
                    .find(|container| container.symbol == parent)
                    .map(|container| container.object)
                    .ok_or_else(|| {
                        self.unsupported(
                            statement.range(),
                            UnsupportedConstruct::NamespaceDeclaration,
                        )
                    })?;
                let key = self.string_reg(builder, EcmaString::encode(&name), statement.range())?;
                let object = self.alloc_register(statement.range())?;
                self.emit(
                    statement.range(),
                    Instruction::GetProperty {
                        dst: object,
                        object: parent_object,
                        key,
                    },
                )?;
                let reuse = self.emit(
                    statement.range(),
                    Instruction::JumpIfTrue {
                        condition: object,
                        target: Pc::new(0),
                    },
                )?;
                self.emit(statement.range(), Instruction::CreateObject { dst: object })?;
                self.emit(
                    statement.range(),
                    Instruction::SetProperty {
                        object: parent_object,
                        key,
                        value: object,
                    },
                )?;
                self.patch_jump(reuse, self.next_pc());
                object
            }
        };
        self.containers.push(Container {
            symbol,
            object,
            kind: ContainerKind::Namespace,
        });
        let captures = self.compute_captures(&[], LoweredBody::Block(&declaration.body), false);
        let id = builder.reserve_function(statement.range())?;
        self.build_function_into(
            builder,
            id,
            statement.range(),
            None,
            &[],
            LoweredBody::Block(&declaration.body),
            FunctionFlags::default(),
            &captures,
            false,
        )?;
        let closure = self.materialize_closure(builder, statement.range(), id, &captures)?;
        let this_value = self.undefined(builder, statement.range())?;
        let arguments = self.alloc_register(statement.range())?;
        self.emit(
            statement.range(),
            Instruction::CreateArray { dst: arguments },
        )?;
        self.emit(
            statement.range(),
            Instruction::ArrayPush {
                array: arguments,
                value: object,
            },
        )?;
        let result = self.alloc_register(statement.range())?;
        self.emit(
            statement.range(),
            Instruction::Call {
                dst: result,
                callee: closure,
                this_value,
                arguments,
            },
        )?;
        let popped = self.containers.pop();
        debug_assert!(popped.is_some_and(|container| {
            container.symbol == symbol && container.kind == ContainerKind::Namespace
        }));
        Ok(())
    }
    fn publish_namespace_exports(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
    ) -> Result<(), LowerError> {
        // Namespace declarations install their own exported members while their
        // IIFE body is lowered (via the exported inner statements below). Nested
        // namespaces are attached to their parent through Member acquisition.
        if self.namespace_facts.declaration(statement.id()).is_some() {
            return Ok(());
        }
        // Exported `var`/`function`/`class`/`enum` statements inside a namespace
        // copy each local binding onto the active container object.
        let member_exports = self
            .namespace_facts
            .exports_for_member_declaration(statement.id());
        if member_exports.is_empty() {
            return Ok(());
        }
        for (container_symbol, export) in member_exports {
            let object = self
                .containers
                .iter()
                .rev()
                .find(|container| container.symbol == container_symbol)
                .map(|container| container.object)
                .ok_or_else(|| {
                    self.unsupported(
                        statement.range(),
                        UnsupportedConstruct::NamespaceDeclaration,
                    )
                })?;
            // Both Property and LocalAndProperty initialize from the local
            // binding created by the exported declaration. Property-only
            // members are then read back through the container (`member_use`).
            let value =
                self.read_name(builder, &export.name().to_utf8_lossy(), statement.range())?;
            let key = self.string_reg(builder, export.name().clone(), statement.range())?;
            self.emit(
                statement.range(),
                Instruction::SetProperty { object, key, value },
            )?;
        }
        Ok(())
    }
    #[allow(dead_code)]
    fn namespace_container_value(
        &mut self,
        builder: &mut ModuleBuilder,
        symbol: crate::checker::SymbolId,
        name: &EcmaString,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        let object = self
            .containers
            .iter()
            .rev()
            .find(|container| container.symbol == symbol)
            .map(|container| container.object)
            .ok_or_else(|| self.unsupported(range, UnsupportedConstruct::NamespaceDeclaration))?;
        let key = self.string_reg(builder, name.clone(), range)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::GetProperty { dst, object, key })?;
        Ok(dst)
    }
    fn namespace_member_site(&self, use_id: NodeId) -> Option<(Register, EcmaString)> {
        self.namespace_facts.member_use(use_id).and_then(|member| {
            self.containers
                .iter()
                .rev()
                .find(|container| container.symbol == member.container())
                .map(|container| (container.object, member.name().clone()))
        })
    }
    fn lower_iteration_variable_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        declaration: &VariableDeclaration,
    ) -> Result<(), LowerError> {
        debug_assert!(matches!(
            declaration.kind,
            VariableKind::Let | VariableKind::Const
        ));
        for declarator in &declaration.declarations {
            let range = declarator.range();
            let data = declarator.data();
            self.predeclare_captured_pattern(&data.binding, DeclarationScope::Iteration)?;
            let value = match &data.initializer {
                Some(initializer) => self.lower_expression(builder, initializer)?,
                None => self.undefined(builder, range)?,
            };
            self.bind_pattern(builder, &data.binding, value, DeclarationScope::Iteration)?;
        }
        Ok(())
    }
    fn instantiate_function_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: &str,
        site: BindingSite,
        function: &FunctionLike,
    ) -> Result<(), LowerError> {
        if function.body.is_none() {
            return Ok(());
        }
        self.predeclare_captured_binding(name, range, site, DeclarationScope::Function)?;
        let closure = self.build_constructible_function_value(
            builder,
            range,
            Some(name.to_owned()),
            function,
        )?;
        self.store_binding(
            builder,
            name,
            closure,
            range,
            site,
            DeclarationScope::Function,
        )
    }
    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------
    fn lower_expression(
        &mut self,
        builder: &mut ModuleBuilder,
        expression: &Expr,
    ) -> Result<Register, LowerError> {
        let range = expression.range();
        if let Some(replacement) = self
            .jsx_plan
            .and_then(|plan| plan.expression_desugars.get(&expression.id()))
            .cloned()
        {
            return self.lower_expression(builder, &replacement);
        }
        if let Some(scalar) = self.enum_facts.const_use(expression.id()).cloned() {
            if matches!(expression.data(), Expression::Member(member) if member.optional) {
                return Err(self.const_enum_operation(range, ConstEnumOperation::OptionalAccess));
            }
            return self.lower_enum_scalar(builder, &scalar, range);
        }
        if Self::has_optional_chain(expression) {
            return self
                .lower_optional_chain(builder, expression)
                .map(|(value, _)| value);
        }
        match expression.data() {
            Expression::JsxElement(_)
            | Expression::JsxFragment(_)
            | Expression::JsxSelfClosingElement(_) => {
                Err(self.missing(range, NodeKind::JsxElement))
            }
            Expression::Identifier(identifier) => {
                if let Some((object, name)) = self.namespace_member_site(expression.id()) {
                    let key = self.string_reg(builder, name, range)?;
                    let dst = self.alloc_register(range)?;
                    self.emit(range, Instruction::GetProperty { dst, object, key })?;
                    return Ok(dst);
                }
                let active_member =
                    self.enum_facts
                        .member_use(expression.id())
                        .and_then(|member| {
                            self.containers
                                .iter()
                                .rev()
                                .find(|container| container.symbol == member.enum_symbol())
                                .map(|container| (container.object, member.name().clone()))
                        });
                if let Some((object, name)) = active_member {
                    let key = self.string_reg(builder, name, range)?;
                    let dst = self.alloc_register(range)?;
                    self.emit(range, Instruction::GetProperty { dst, object, key })?;
                    return Ok(dst);
                }
                let name = self.identifier_text(identifier)?;
                self.read_name(builder, &name, range)
            }
            Expression::This => self.this_value(builder, range),
            // A bare `super` expression is rejected by the checker
            // (BAMTS-C024). Calls intercept `super(...)` before reaching here,
            // so only diagnosed sources lower a bare `super`; give it the
            // inert `undefined` value.
            Expression::Super => self.undefined(builder, range),
            Expression::Literal(literal) => self.lower_literal(builder, range, literal),
            Expression::Template(template) => self.lower_template(builder, range, template),
            Expression::TaggedTemplate(tagged) => {
                self.lower_tagged_template(builder, range, tagged)
            }
            Expression::Array(array) => self.lower_array(builder, range, array),
            Expression::Object(object) => self.lower_object(builder, range, object),
            Expression::Function(function) => {
                self.build_constructible_function_value(builder, range, None, &function.function)
            }
            Expression::Class(class) => {
                let name = class
                    .class
                    .name
                    .as_ref()
                    .map(|identifier| {
                        self.identifier_text(identifier)
                            .map(|name| (name, binding_site(identifier.range())))
                    })
                    .transpose()?;
                self.lower_class_value(
                    builder,
                    range,
                    &class.class,
                    None,
                    name.as_ref().map(|(name, site)| (name.as_str(), *site)),
                )
            }
            Expression::Arrow(arrow) => self.lower_arrow(builder, range, arrow),
            Expression::Call(call) => self.lower_call(builder, range, call),
            Expression::Member(_) => {
                let (_, value) = self.lower_member(builder, range, expression)?;
                Ok(value)
            }
            Expression::New(new) => self.lower_new(builder, range, new),
            Expression::Await(await_expression) => {
                self.lower_await(builder, range, await_expression)
            }
            Expression::Yield(yield_expression) => {
                self.lower_yield(builder, range, yield_expression)
            }
            Expression::Unary(unary) => self.lower_unary(builder, range, unary),
            Expression::Update(update) => self.lower_update(builder, range, update),
            Expression::Binary(binary) => self.lower_binary(builder, range, binary),
            Expression::Logical(logical) => self.lower_logical(builder, range, logical),
            Expression::Conditional(conditional) => {
                self.lower_conditional(builder, range, conditional)
            }
            Expression::Assignment(assignment) => self.lower_assignment(builder, range, assignment),
            Expression::Sequence(sequence) => {
                let mut last = None;
                for expression in &sequence.expressions {
                    last = Some(self.lower_expression(builder, expression)?);
                }
                match last {
                    Some(register) => Ok(register),
                    None => self.undefined(builder, range),
                }
            }
            Expression::Parenthesized(inner) => self.lower_expression(builder, inner),
            Expression::As(as_expression) => {
                self.lower_expression(builder, &as_expression.expression)
            }
            Expression::Satisfies(satisfies) => {
                self.lower_expression(builder, &satisfies.expression)
            }
            Expression::TypeAssertion(assertion) => {
                self.lower_expression(builder, &assertion.expression)
            }
            Expression::NonNull(non_null) => self.lower_expression(builder, &non_null.expression),
            Expression::Import(import) => self.lower_import_expression(builder, range, import),
            Expression::Meta(meta) => match meta {
                MetaProperty::NewTarget => self.new_target_value(range),
                MetaProperty::ImportMeta => {
                    if self.goal == LoweringGoal::ClassicScript {
                        return Err(self.error(range, LowerErrorKind::ImportMetaInScript));
                    }
                    let dst = self.alloc_register(range)?;
                    self.emit(range, Instruction::LoadImportMeta { dst })?;
                    Ok(dst)
                }
            },
            Expression::Missing(missing) => Err(self.missing(range, missing.expected())),
        }
    }
    fn lower_unary(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        unary: &crate::syntax::UnaryExpression,
    ) -> Result<Register, LowerError> {
        let op = match unary.operator {
            UnaryOperator::Void => {
                self.lower_expression(builder, &unary.argument)?;
                return self.undefined(builder, range);
            }
            UnaryOperator::Delete => return self.lower_delete(builder, range, &unary.argument),
            UnaryOperator::Typeof => return self.lower_typeof(builder, range, &unary.argument),
            UnaryOperator::Plus => UnaryOp::Plus,
            UnaryOperator::Minus => UnaryOp::Negate,
            UnaryOperator::Not => UnaryOp::LogicalNot,
            UnaryOperator::BitNot => UnaryOp::BitwiseNot,
        };
        let operand = self.lower_expression(builder, &unary.argument)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::Unary { dst, op, operand })?;
        Ok(dst)
    }
    /// `typeof x` never throws for a free/undeclared name, so a bare-identifier
    /// operand that resolves to the environment uses [`Instruction::TypeOfGlobal`].
    fn lower_typeof(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        argument: &Expr,
    ) -> Result<Register, LowerError> {
        if let Expression::Identifier(identifier) = argument.data() {
            let name = self.identifier_text(identifier)?;
            if let Some(frozen) = self.freeze_with_base(builder, &name, range)? {
                let result = self.alloc_register(range)?;
                let miss = self.emit(
                    range,
                    Instruction::JumpIfFalse {
                        condition: frozen.found,
                        target: Pc::new(0),
                    },
                )?;
                let value = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetProperty {
                        dst: value,
                        object: frozen.base,
                        key: frozen.key,
                    },
                )?;
                let typed = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Unary {
                        dst: typed,
                        op: UnaryOp::TypeOf,
                        operand: value,
                    },
                )?;
                self.move_to(range, result, typed)?;
                let skip = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                self.patch_jump(miss, self.next_pc());
                let resolved = self.resolve(&name).is_some()
                    || (name == "arguments"
                        && !matches!(self.arguments_source, ArgumentsSource::None))
                    || name == "undefined";
                if resolved {
                    let operand = self.read_name_static(builder, &name, range)?;
                    let typed = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::Unary {
                            dst: typed,
                            op: UnaryOp::TypeOf,
                            operand,
                        },
                    )?;
                    self.move_to(range, result, typed)?;
                } else {
                    let id = builder.intern(Constant::String(EcmaString::encode(&name)), range)?;
                    let typed = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::TypeOfGlobal {
                            dst: typed,
                            name: id,
                        },
                    )?;
                    self.move_to(range, result, typed)?;
                }
                self.patch_jump(skip, self.next_pc());
                return Ok(result);
            }
            let resolved = self.resolve(&name).is_some()
                || (name == "arguments" && !matches!(self.arguments_source, ArgumentsSource::None))
                || name == "undefined";
            if !resolved {
                let id = builder.intern(Constant::String(EcmaString::encode(&name)), range)?;
                let dst = self.alloc_register(range)?;
                self.emit(range, Instruction::TypeOfGlobal { dst, name: id })?;
                return Ok(dst);
            }
        }
        let operand = self.lower_expression(builder, argument)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Unary {
                dst,
                op: UnaryOp::TypeOf,
                operand,
            },
        )?;
        Ok(dst)
    }
    fn lower_delete(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        argument: &Expr,
    ) -> Result<Register, LowerError> {
        if self.is_direct_const_enum_member(argument)? {
            return Err(self.const_enum_operation(range, ConstEnumOperation::Delete));
        }
        match argument.data() {
            Expression::Member(member) => {
                if Self::has_optional_chain(argument) {
                    return self.lower_optional_delete(builder, range, member);
                }
                let object = self.lower_expression(builder, &member.object)?;
                let key = self.member_key(builder, &member.property)?;
                let dst = self.alloc_register(range)?;
                self.emit(range, Instruction::DeleteProperty { dst, object, key })?;
                Ok(dst)
            }
            Expression::Parenthesized(inner) => self.lower_delete(builder, range, inner),
            Expression::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                if let Some(frozen) = self.freeze_with_base(builder, &name, range)? {
                    let result = self.alloc_register(range)?;
                    let miss = self.emit(
                        range,
                        Instruction::JumpIfFalse {
                            condition: frozen.found,
                            target: Pc::new(0),
                        },
                    )?;
                    let deleted = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::DeleteProperty {
                            dst: deleted,
                            object: frozen.base,
                            key: frozen.key,
                        },
                    )?;
                    self.move_to(range, result, deleted)?;
                    let skip = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                    self.patch_jump(miss, self.next_pc());
                    let fals = self.load_constant(builder, Constant::Boolean(false), range)?;
                    self.move_to(range, result, fals)?;
                    self.patch_jump(skip, self.next_pc());
                    return Ok(result);
                }
                self.load_constant(builder, Constant::Boolean(false), range)
            }
            // `delete x` of a binding is a no-op returning false in strict/module
            // code (bindings are non-configurable).
            _ => self.load_constant(builder, Constant::Boolean(false), range),
        }
    }
    fn lower_optional_delete(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        member: &MemberExpression,
    ) -> Result<Register, LowerError> {
        let result = self.alloc_register(range)?;
        let truthy = self.load_constant(builder, Constant::Boolean(true), range)?;
        self.move_to(range, result, truthy)?;
        let mut skips = Vec::new();
        let (object, _) = self.lower_chain_reference(builder, &member.object, &mut skips)?;
        if member.optional {
            self.skip_nullish_chain(builder, range, object, &mut skips)?;
        }
        let key = self.member_key(builder, &member.property)?;
        let deleted = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::DeleteProperty {
                dst: deleted,
                object,
                key,
            },
        )?;
        self.move_to(range, result, deleted)?;
        let end = self.next_pc();
        for skip in skips {
            self.patch_jump(skip, end);
        }
        Ok(result)
    }
    fn lower_binary(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        binary: &BinaryExpression,
    ) -> Result<Register, LowerError> {
        let op = map_binary_operator(binary.operator);
        let left = self.lower_expression(builder, &binary.left)?;
        let right = self.lower_expression(builder, &binary.right)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst,
                op,
                left,
                right,
            },
        )?;
        Ok(dst)
    }
    fn lower_logical(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        logical: &LogicalExpression,
    ) -> Result<Register, LowerError> {
        let result = self.alloc_register(range)?;
        let left = self.lower_expression(builder, &logical.left)?;
        self.move_to(range, result, left)?;
        let short_circuit = self.branch_on_short_circuit(builder, range, logical.operator, left)?;
        let right = self.lower_expression(builder, &logical.right)?;
        self.move_to(range, result, right)?;
        let end = self.next_pc();
        self.patch_jump(short_circuit, end);
        Ok(result)
    }
    /// Emits the branch that keeps the left operand of a short-circuit
    /// operator, returning the placeholder jump to patch to the merge.
    fn branch_on_short_circuit(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        operator: LogicalOperator,
        left: Register,
    ) -> Result<Pc, LowerError> {
        match operator {
            LogicalOperator::And => self.emit(
                range,
                Instruction::JumpIfFalse {
                    condition: left,
                    target: Pc::new(0),
                },
            ),
            LogicalOperator::Or => self.emit(
                range,
                Instruction::JumpIfTrue {
                    condition: left,
                    target: Pc::new(0),
                },
            ),
            LogicalOperator::Nullish => {
                let is_nullish = self.compute_nullish(builder, range, left)?;
                self.emit(
                    range,
                    Instruction::JumpIfFalse {
                        condition: is_nullish,
                        target: Pc::new(0),
                    },
                )
            }
        }
    }
    /// Computes whether `value` is `null` or `undefined` (`value == null`).
    fn compute_nullish(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
    ) -> Result<Register, LowerError> {
        let null = self.load_constant(builder, Constant::Null, range)?;
        let is_null = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_null,
                op: BinaryOp::Equal,
                left: value,
                right: null,
            },
        )?;
        Ok(is_null)
    }
    fn lower_conditional(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        conditional: &ConditionalExpression,
    ) -> Result<Register, LowerError> {
        let result = self.alloc_register(range)?;
        let condition = self.lower_expression(builder, &conditional.test)?;
        let to_alternate = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition,
                target: Pc::new(0),
            },
        )?;
        let consequent = self.lower_expression(builder, &conditional.consequent)?;
        self.move_to(range, result, consequent)?;
        let to_end = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        let alternate_pc = self.next_pc();
        self.patch_jump(to_alternate, alternate_pc);
        let alternate = self.lower_expression(builder, &conditional.alternate)?;
        self.move_to(range, result, alternate)?;
        let end = self.next_pc();
        self.patch_jump(to_end, end);
        Ok(result)
    }
    // ------------------------------------------------------------------
    // Assignment and update
    // ------------------------------------------------------------------
    fn lower_assignment(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        assignment: &AssignmentExpression,
    ) -> Result<Register, LowerError> {
        match assignment.left.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                self.lower_identifier_assignment(builder, range, &name, assignment)
            }
            AssignmentTarget::Member(member) => {
                if self.is_const_enum_member_target(&assignment.left, &member.object)? {
                    return Err(self.const_enum_operation(range, ConstEnumOperation::Write));
                }
                self.lower_member_assignment(builder, range, member, assignment)
            }
            AssignmentTarget::Object(_) | AssignmentTarget::Array(_) => {
                // Destructuring assignment applies only for `=`.
                if compound_operator(assignment.operator).is_some() {
                    return Err(
                        self.missing(assignment.left.range(), NodeKind::AssignmentExpression)
                    );
                }
                let value = self.lower_expression(builder, &assignment.right)?;
                self.assign_target(builder, &assignment.left, value)?;
                Ok(value)
            }
            AssignmentTarget::Missing(missing) => {
                Err(self.missing(assignment.left.range(), missing.expected()))
            }
            AssignmentTarget::Invalid(_) => {
                Err(self.missing(assignment.left.range(), NodeKind::AssignmentExpression))
            }
        }
    }
    fn lower_identifier_assignment(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: &str,
        assignment: &AssignmentExpression,
    ) -> Result<Register, LowerError> {
        // Node/ECMA PutValue for with bindings re-resolves after the RHS. Do not
        // freeze a WithBase across the RHS; reads use read_name and writes use
        // assign_name so each performs a fresh membership walk.
        match compound_operator(assignment.operator) {
            None => {
                let value = self.lower_expression(builder, &assignment.right)?;
                self.assign_name(builder, name, value, range)?;
                Ok(value)
            }
            Some(CompoundOp::Arithmetic(op)) => {
                let current = self.read_name(builder, name, range)?;
                let right = self.lower_expression(builder, &assignment.right)?;
                let result = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Binary {
                        dst: result,
                        op,
                        left: current,
                        right,
                    },
                )?;
                self.assign_name(builder, name, result, range)?;
                Ok(result)
            }
            Some(CompoundOp::Logical(op)) => {
                let result = self.alloc_register(range)?;
                let current = self.read_name(builder, name, range)?;
                self.move_to(range, result, current)?;
                let skip = self.branch_on_short_circuit(builder, range, op, current)?;
                let value = self.lower_expression(builder, &assignment.right)?;
                self.assign_name(builder, name, value, range)?;
                self.move_to(range, result, value)?;
                let end = self.next_pc();
                self.patch_jump(skip, end);
                Ok(result)
            }
        }
    }
    fn lower_member_assignment(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        member: &AssignmentMemberTarget,
        assignment: &AssignmentExpression,
    ) -> Result<Register, LowerError> {
        let object = self.lower_expression(builder, &member.object)?;
        let key = self.member_key(builder, &member.property)?;
        match compound_operator(assignment.operator) {
            None => {
                let value = self.lower_expression(builder, &assignment.right)?;
                self.emit(range, Instruction::SetProperty { object, key, value })?;
                Ok(value)
            }
            Some(CompoundOp::Arithmetic(op)) => {
                let current = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetProperty {
                        dst: current,
                        object,
                        key,
                    },
                )?;
                let right = self.lower_expression(builder, &assignment.right)?;
                let result = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Binary {
                        dst: result,
                        op,
                        left: current,
                        right,
                    },
                )?;
                self.emit(
                    range,
                    Instruction::SetProperty {
                        object,
                        key,
                        value: result,
                    },
                )?;
                Ok(result)
            }
            Some(CompoundOp::Logical(op)) => {
                let result = self.alloc_register(range)?;
                let current = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetProperty {
                        dst: current,
                        object,
                        key,
                    },
                )?;
                self.move_to(range, result, current)?;
                let skip = self.branch_on_short_circuit(builder, range, op, current)?;
                let value = self.lower_expression(builder, &assignment.right)?;
                self.emit(range, Instruction::SetProperty { object, key, value })?;
                self.move_to(range, result, value)?;
                let end = self.next_pc();
                self.patch_jump(skip, end);
                Ok(result)
            }
        }
    }
    fn lower_update(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        update: &UpdateExpression,
    ) -> Result<Register, LowerError> {
        let op = match update.operator {
            UpdateOperator::Increment => BinaryOp::Add,
            UpdateOperator::Decrement => BinaryOp::Subtract,
        };
        match update.argument.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                // GetValue then PutValue: re-resolve the write so a deleted with
                // binding between read and write matches Node (PutValue after).
                let current = self.read_name(builder, &name, range)?;
                let old = self.alloc_register(range)?;
                self.move_to(range, old, current)?;
                let one = self.load_constant(builder, Constant::Int32(1), range)?;
                let updated = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Binary {
                        dst: updated,
                        op,
                        left: old,
                        right: one,
                    },
                )?;
                self.assign_name(builder, &name, updated, range)?;
                Ok(if update.prefix { updated } else { old })
            }
            AssignmentTarget::Member(member) => {
                if self.is_const_enum_member_target(&update.argument, &member.object)? {
                    return Err(self.const_enum_operation(range, ConstEnumOperation::Write));
                }
                let object = self.lower_expression(builder, &member.object)?;
                let key = self.member_key(builder, &member.property)?;
                let old = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetProperty {
                        dst: old,
                        object,
                        key,
                    },
                )?;
                let one = self.load_constant(builder, Constant::Int32(1), range)?;
                let updated = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Binary {
                        dst: updated,
                        op,
                        left: old,
                        right: one,
                    },
                )?;
                self.emit(
                    range,
                    Instruction::SetProperty {
                        object,
                        key,
                        value: updated,
                    },
                )?;
                Ok(if update.prefix { updated } else { old })
            }
            AssignmentTarget::Object(_) | AssignmentTarget::Array(_) => {
                Err(self.missing(update.argument.range(), NodeKind::UpdateExpression))
            }
            AssignmentTarget::Missing(missing) => {
                Err(self.missing(update.argument.range(), missing.expected()))
            }
            AssignmentTarget::Invalid(_) => {
                Err(self.missing(update.argument.range(), NodeKind::UpdateExpression))
            }
        }
    }
    /// `await x` suspends on `x` ([`Instruction::Await`], distinct from the
    /// `yield` form's [`Instruction::Suspend`]) and resumes with the settled
    fn lower_await(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        await_expression: &AwaitExpression,
    ) -> Result<Register, LowerError> {
        let src = self.lower_expression(builder, &await_expression.argument)?;
        self.emit_await(range, src)
    }
    fn lower_yield(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        yield_expression: &YieldExpression,
    ) -> Result<Register, LowerError> {
        if yield_expression.delegate {
            return self.lower_yield_delegate(builder, range, yield_expression);
        }
        let src = match &yield_expression.argument {
            Some(expression) => self.lower_expression(builder, expression)?,
            None => self.undefined(builder, range)?,
        };
        self.emit_suspend(builder, range, src)
    }
    fn lower_yield_delegate(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        yield_expression: &YieldExpression,
    ) -> Result<Register, LowerError> {
        let subject = match &yield_expression.argument {
            Some(expression) => self.lower_expression(builder, expression)?,
            None => self.undefined(builder, range)?,
        };
        if self.is_async_generator {
            return self.lower_yield_delegate_async(builder, range, subject);
        }
        let iterator = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetIterator {
                dst: iterator,
                src: subject,
                kind: IteratorKind::Sync,
            },
        )?;
        let done = self.alloc_register(range)?;
        let value = self.alloc_register(range)?;
        let result = self.alloc_register(range)?;
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, result, undefined)?;
        let head = self.next_pc();
        self.emit(
            range,
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            },
        )?;
        let exit_jump = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        let resumed = self.emit_suspend(builder, range, value)?;
        self.move_to(range, result, resumed)?;
        self.emit(range, Instruction::Jump { target: head })?;
        let exit = self.next_pc();
        self.patch_jump(exit_jump, exit);
        self.move_to(range, result, value)?;
        Ok(result)
    }
    /// Lowering for `yield*` inside an async generator (ECMA-262 27.5.3.7).
    ///
    /// Acquires the delegated iterator through `Symbol.asyncIterator`
    /// (falling back to `Symbol.iterator` inside `GetIterator`), awaits every
    /// raw `next()` result before unpacking it, and forwards abrupt `throw` /
    /// `return` requests to the delegated iterator's own methods. The single
    /// `Suspend` re-enters at a mode dispatch: `next` resumes the loop with the
    /// resumed value, while `throw`/`return` arms forward `received` (written
    /// before the dispatch) and their inner completion is awaited before it
    /// settles the generator.
    fn lower_yield_delegate_async(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        subject: Register,
    ) -> Result<Register, LowerError> {
        let iterator = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetIterator {
                dst: iterator,
                src: subject,
                kind: IteratorKind::Async,
            },
        )?;
        let undefined = self.undefined(builder, range)?;
        let received = self.alloc_register(range)?;
        self.move_to(range, received, undefined)?;
        let value = self.alloc_register(range)?;

        // Delegated next(): acquire the raw (possibly promised) result, settle
        // it, then unpack done/value; IteratorResult rejects non-objects.
        let head = self.next_pc();
        let step = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorStep {
                dst: step,
                iterator,
            },
        )?;
        let settled = self.emit_await(range, step)?;
        let done = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorResult {
                done,
                value,
                result: settled,
            },
        )?;
        let done_exit = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        self.move_to(range, received, value)?;
        let to_yield = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;

        let do_return = self.next_pc();
        let return_to_yield =
            self.lower_delegate_return_arm(builder, range, iterator, received, value)?;
        let do_throw = self.next_pc();
        let throw_to_yield =
            self.lower_delegate_throw_arm(builder, range, iterator, received, value)?;

        // Yield the delegated value and re-enter on the resume edge, where the
        // engine-written mode selects the next arm.
        let yield_point = self.next_pc();
        self.patch_jump(to_yield, yield_point);
        self.patch_jump(return_to_yield, yield_point);
        self.patch_jump(throw_to_yield, yield_point);
        let resumed = self.alloc_register(range)?;
        let mode = self.alloc_register(range)?;
        let resume = Pc::new(self.code.len() as u32 + 1);
        self.emit(
            range,
            Instruction::Suspend {
                dst: resumed,
                src: received,
                resume,
                mode,
            },
        )?;
        self.move_to(range, received, resumed)?;
        let skip_throw = self.emit_int32_guard(builder, range, mode, RESUME_THROW)?;
        self.emit(range, Instruction::Jump { target: do_throw })?;
        let after_throw = self.next_pc();
        self.patch_jump(skip_throw, after_throw);
        let skip_return = self.emit_int32_guard(builder, range, mode, RESUME_RETURN)?;
        self.emit(range, Instruction::Jump { target: do_return })?;
        let after_return = self.next_pc();
        self.patch_jump(skip_return, after_return);
        self.emit(range, Instruction::Jump { target: head })?;

        // The delegated iterator finished: its awaited value is the value of
        // the whole `yield*` expression.
        let done_target = self.next_pc();
        self.patch_jump(done_exit, done_target);
        let final_value = self.emit_await(range, value)?;
        let result = self.alloc_register(range)?;
        self.move_to(range, result, final_value)?;
        let exit_jump = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;

        let exit = self.next_pc();
        self.patch_jump(exit_jump, exit);
        Ok(result)
    }
    /// Emits one inner-completion return: await the settled inner value and
    /// route it through any enclosing `finally` before completing.
    fn lower_delegate_done_return(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
    ) -> Result<(), LowerError> {
        let final_value = self.emit_await(range, value)?;
        if !self.route_through_finally(
            builder,
            range,
            COMPLETION_RETURN,
            Some(final_value),
            None,
        )? {
            self.emit_function_return(builder, range, final_value)?;
        }
        Ok(())
    }
    /// Emits the `received.[[Type]] is return` arm of the async `yield*` loop.
    ///
    /// With a callable `return` method the received value is forwarded and the
    /// awaited result is yielded back into the loop; without one the received
    /// value completes the generator after an await. Returns the jump that
    /// re-enters the yield point after a non-done forwarded result.
    fn lower_delegate_return_arm(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        iterator: Register,
        received: Register,
        value: Register,
    ) -> Result<Pc, LowerError> {
        let method = self.alloc_register(range)?;
        let return_key = self.string_reg(builder, EcmaString::encode("return"), range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: method,
                object: iterator,
                key: return_key,
            },
        )?;
        let undefined = self.undefined(builder, range)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: method,
                right: undefined,
            },
        )?;
        let no_method = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        self.emit(
            range,
            Instruction::ArrayPush {
                array: arguments,
                value: received,
            },
        )?;
        let raw = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst: raw,
                callee: method,
                this_value: iterator,
                arguments,
            },
        )?;
        let settled = self.emit_await(range, raw)?;
        let done = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorResult {
                done,
                value,
                result: settled,
            },
        )?;
        let inner_done = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        self.move_to(range, received, value)?;
        let to_yield = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;

        // No `return` method: the received value itself completes the
        // generator once awaited.
        let no_method_target = self.next_pc();
        self.patch_jump(no_method, no_method_target);
        self.lower_delegate_done_return(builder, range, received)?;

        let inner_done_target = self.next_pc();
        self.patch_jump(inner_done, inner_done_target);
        self.lower_delegate_done_return(builder, range, value)?;
        Ok(to_yield)
    }
    /// Emits the `received.[[Type]] is throw` arm of the async `yield*` loop.
    ///
    /// With a callable `throw` method the thrown value is forwarded and a
    /// non-done result is yielded back into the loop; without one the
    /// iterator is closed (close failures win over the pending throw) and the
    /// thrown value re-raises into the generator body. Returns the jump that
    /// re-enters the yield point after a non-done forwarded result.
    fn lower_delegate_throw_arm(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        iterator: Register,
        received: Register,
        value: Register,
    ) -> Result<Pc, LowerError> {
        let method = self.alloc_register(range)?;
        let throw_key = self.string_reg(builder, EcmaString::encode("throw"), range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: method,
                object: iterator,
                key: throw_key,
            },
        )?;
        let undefined = self.undefined(builder, range)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: method,
                right: undefined,
            },
        )?;
        let no_method = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        self.emit(
            range,
            Instruction::ArrayPush {
                array: arguments,
                value: received,
            },
        )?;
        let raw = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst: raw,
                callee: method,
                this_value: iterator,
                arguments,
            },
        )?;
        let settled = self.emit_await(range, raw)?;
        let done = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorResult {
                done,
                value,
                result: settled,
            },
        )?;
        let inner_done = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        self.move_to(range, received, value)?;
        let to_yield = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;

        // No `throw` method: close the iterator (awaiting its close result and
        // rejecting non-object close results) and re-raise the pending throw.
        let close_target = self.next_pc();
        self.patch_jump(no_method, close_target);
        let close_result = self.alloc_register(range)?;
        let close_called = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorClose {
                result: close_result,
                called: close_called,
                iterator,
                mode: IteratorCloseMode::Propagate,
            },
        )?;
        let settled_close = self.emit_await(range, close_result)?;
        self.emit(
            range,
            Instruction::RequireCloseResult {
                result: settled_close,
                called: close_called,
            },
        )?;
        self.emit(range, Instruction::Throw { value: received })?;

        let inner_done_target = self.next_pc();
        self.patch_jump(inner_done, inner_done_target);
        self.lower_delegate_done_return(builder, range, value)?;
        Ok(to_yield)
    }
    fn emit_suspend(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        src: Register,
    ) -> Result<Register, LowerError> {
        let dst = self.alloc_register(range)?;
        let mode = self.alloc_register(range)?;
        let resume = Pc::new(self.code.len() as u32 + 1);
        self.emit(
            range,
            Instruction::Suspend {
                dst,
                src,
                resume,
                mode,
            },
        )?;

        let skip_throw = self.emit_int32_guard(builder, range, mode, RESUME_THROW)?;
        self.emit(range, Instruction::Throw { value: dst })?;
        let after_throw = self.next_pc();
        self.patch_jump(skip_throw, after_throw);

        let skip_return = self.emit_int32_guard(builder, range, mode, RESUME_RETURN)?;
        if !self.route_through_finally(builder, range, COMPLETION_RETURN, Some(dst), None)? {
            self.emit_function_return(builder, range, dst)?;
        }
        let after_return = self.next_pc();
        self.patch_jump(skip_return, after_return);
        Ok(dst)
    }
    fn emit_await(&mut self, range: TextRange, src: Register) -> Result<Register, LowerError> {
        if !self.can_await() {
            return Err(self.unsupported(range, UnsupportedConstruct::UsingDeclaration));
        }
        let dst = self.alloc_register(range)?;
        let resume = Pc::new(self.code.len() as u32 + 1);
        self.emit(range, Instruction::Await { dst, src, resume })?;
        Ok(dst)
    }
    fn lower_member(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        expression: &Expr,
    ) -> Result<(Register, Register), LowerError> {
        let Expression::Member(member) = expression.data() else {
            unreachable!("lower_member requires an Expression::Member");
        };
        if let Some(scalar) = self.enum_facts.const_use(expression.id()).cloned() {
            if member.optional {
                return Err(self.const_enum_operation(range, ConstEnumOperation::OptionalAccess));
            }
            let object = self.undefined(builder, range)?;
            let value = self.lower_enum_scalar(builder, &scalar, range)?;
            return Ok((object, value));
        }
        if self.const_enum_symbol(&member.object)?.is_some() {
            let operation = if member.optional {
                ConstEnumOperation::OptionalAccess
            } else {
                ConstEnumOperation::Read
            };
            return Err(self.const_enum_operation(range, operation));
        }
        let object = self.lower_expression(builder, &member.object)?;
        let key = self.member_key(builder, &member.property)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::GetProperty { dst, object, key })?;
        Ok((object, dst))
    }
    fn has_optional_chain(mut expression: &Expr) -> bool {
        loop {
            expression = match expression.data() {
                Expression::Member(member) => {
                    if member.optional {
                        return true;
                    }
                    &member.object
                }
                Expression::Call(call) => {
                    if call.optional {
                        return true;
                    }
                    &call.callee
                }
                Expression::NonNull(non_null) => &non_null.expression,
                // Parentheses end a chain; a TS non-null assertion does not.
                _ => return false,
            };
        }
    }

    /// Every optional link jumps past the whole chain, including computed keys
    /// and call arguments. The pair retains a property reference's receiver.
    fn lower_optional_chain(
        &mut self,
        builder: &mut ModuleBuilder,
        expression: &Expr,
    ) -> Result<(Register, Register), LowerError> {
        let range = expression.range();
        let result = self.undefined(builder, range)?;
        let receiver = self.undefined(builder, range)?;
        let mut skips = Vec::new();
        let (value, this_value) = self.lower_chain_reference(builder, expression, &mut skips)?;
        self.move_to(range, receiver, this_value)?;
        self.move_to(range, result, value)?;
        let end = self.next_pc();
        for skip in skips {
            self.patch_jump(skip, end);
        }
        Ok((result, receiver))
    }

    fn skip_nullish_chain(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
        skips: &mut Vec<Pc>,
    ) -> Result<(), LowerError> {
        let condition = self.compute_nullish(builder, range, value)?;
        skips.push(self.emit(
            range,
            Instruction::JumpIfTrue {
                condition,
                target: Pc::new(0),
            },
        )?);
        Ok(())
    }

    fn lower_chain_reference(
        &mut self,
        builder: &mut ModuleBuilder,
        expression: &Expr,
        skips: &mut Vec<Pc>,
    ) -> Result<(Register, Register), LowerError> {
        let range = expression.range();
        if !Self::has_optional_chain(expression) {
            return self.lower_callee(builder, range, expression);
        }
        if self.is_direct_const_enum_member(expression)? {
            return Err(self.const_enum_operation(range, ConstEnumOperation::OptionalAccess));
        }
        match expression.data() {
            Expression::Member(member) => {
                let (object, _) = self.lower_chain_reference(builder, &member.object, skips)?;
                if member.optional {
                    self.skip_nullish_chain(builder, range, object, skips)?;
                }
                let key = self.member_key(builder, &member.property)?;
                let dst = self.alloc_register(range)?;
                self.emit(range, Instruction::GetProperty { dst, object, key })?;
                Ok((dst, object))
            }
            Expression::Call(call) => {
                if self.is_direct_const_enum_member(&call.callee)? {
                    return Err(
                        self.const_enum_operation(range, ConstEnumOperation::OptionalAccess)
                    );
                }
                let (callee, this_value) =
                    self.lower_chain_reference(builder, &call.callee, skips)?;
                if call.optional {
                    self.skip_nullish_chain(builder, range, callee, skips)?;
                }
                let arguments = self.build_arguments(builder, range, &call.arguments)?;
                let dst = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::Call {
                        dst,
                        callee,
                        this_value,
                        arguments,
                    },
                )?;
                Ok((dst, self.undefined(builder, range)?))
            }
            Expression::NonNull(non_null) => {
                self.lower_chain_reference(builder, &non_null.expression, skips)
            }
            _ => unreachable!("optional chains contain only member, call, and non-null links"),
        }
    }
    fn lower_call(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        call: &CallExpression,
    ) -> Result<Register, LowerError> {
        if matches!(call.callee.data(), Expression::Super) {
            return self.lower_derived_super(builder, range, call);
        }
        if self.is_direct_const_enum_member(&call.callee)? {
            return Err(self.const_enum_operation(range, ConstEnumOperation::Read));
        }
        let (callee, this_value) = self.lower_callee(builder, range, &call.callee)?;
        let arguments = self.build_arguments(builder, range, &call.arguments)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst,
                callee,
                this_value,
                arguments,
            },
        )?;
        Ok(dst)
    }
    fn lower_callee(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        callee: &Expr,
    ) -> Result<(Register, Register), LowerError> {
        let mut callee = callee;
        while let Expression::Parenthesized(inner) = callee.data() {
            callee = inner;
        }
        if Self::has_optional_chain(callee) {
            return self.lower_optional_chain(builder, callee);
        }
        match callee.data() {
            Expression::Member(member) if !member.optional => {
                if matches!(member.object.data(), Expression::Super) {
                    let this_value = self.this_value(builder, range)?;
                    let object = this_value;
                    let key = self.member_key(builder, &member.property)?;
                    let value = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::GetProperty {
                            dst: value,
                            object,
                            key,
                        },
                    )?;
                    return Ok((value, this_value));
                }
                let (object, value) = self.lower_member(builder, callee.range(), callee)?;
                Ok((value, object))
            }
            Expression::Super => {
                let this_value = self.this_value(builder, range)?;
                Ok((this_value, this_value))
            }
            _ => {
                let mut target = callee;
                while let Expression::Parenthesized(inner) = target.data() {
                    target = inner;
                }
                if let Expression::Identifier(identifier) = target.data() {
                    let name = self.identifier_text(identifier)?;
                    if let Some(frozen) = self.freeze_with_base(builder, &name, range)? {
                        let callee_reg = self.alloc_register(range)?;
                        let this_reg = self.alloc_register(range)?;
                        let miss = self.emit(
                            range,
                            Instruction::JumpIfFalse {
                                condition: frozen.found,
                                target: Pc::new(0),
                            },
                        )?;
                        // Put the with object into `this_reg` first so GetProperty and
                        // Call share the same receiver register on the matched path.
                        self.move_to(range, this_reg, frozen.base)?;
                        let value = self.alloc_register(range)?;
                        self.emit(
                            range,
                            Instruction::GetProperty {
                                dst: value,
                                object: this_reg,
                                key: frozen.key,
                            },
                        )?;
                        self.move_to(range, callee_reg, value)?;
                        let skip = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                        self.patch_jump(miss, self.next_pc());
                        let fallback = self.read_name_static(builder, &name, range)?;
                        self.move_to(range, callee_reg, fallback)?;
                        let undef = self.undefined(builder, range)?;
                        self.move_to(range, this_reg, undef)?;
                        self.patch_jump(skip, self.next_pc());
                        return Ok((callee_reg, this_reg));
                    }
                }
                let callee = self.lower_expression(builder, callee)?;
                let this_value = self.undefined(builder, range)?;
                Ok((callee, this_value))
            }
        }
    }
    fn lower_new(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        new: &NewExpression,
    ) -> Result<Register, LowerError> {
        if self.is_direct_const_enum_member(&new.callee)? {
            return Err(self.const_enum_operation(range, ConstEnumOperation::Read));
        }
        let callee = self.lower_expression(builder, &new.callee)?;
        let arguments = self.build_arguments(builder, range, &new.arguments)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Construct {
                dst,
                callee,
                arguments,
            },
        )?;
        Ok(dst)
    }
    fn const_enum_operation(&self, range: TextRange, operation: ConstEnumOperation) -> LowerError {
        self.error(range, LowerErrorKind::ConstEnumOperation { operation })
    }
    fn const_enum_symbol(
        &self,
        expression: &Expr,
    ) -> Result<Option<crate::checker::SymbolId>, LowerError> {
        match expression.data() {
            Expression::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                Ok(match self.resolve(&name) {
                    Some(Binding::ConstEnum(symbol)) => Some(symbol),
                    _ => None,
                })
            }
            Expression::Parenthesized(inner) => self.const_enum_symbol(inner),
            Expression::As(as_expression) => self.const_enum_symbol(&as_expression.expression),
            Expression::Satisfies(satisfies) => self.const_enum_symbol(&satisfies.expression),
            Expression::TypeAssertion(assertion) => self.const_enum_symbol(&assertion.expression),
            Expression::NonNull(non_null) => self.const_enum_symbol(&non_null.expression),
            _ => Ok(None),
        }
    }
    fn is_const_enum_member_target(
        &self,
        target: &AssignmentTargetNode,
        object: &Expr,
    ) -> Result<bool, LowerError> {
        Ok(self.enum_facts.is_const_enum_member_target(target.id())
            || self.const_enum_symbol(object)?.is_some())
    }
    fn is_direct_const_enum_member(&self, expression: &Expr) -> Result<bool, LowerError> {
        match expression.data() {
            Expression::Parenthesized(inner) => self.is_direct_const_enum_member(inner),
            Expression::As(as_expression) => {
                self.is_direct_const_enum_member(&as_expression.expression)
            }
            Expression::Satisfies(satisfies) => {
                self.is_direct_const_enum_member(&satisfies.expression)
            }
            Expression::TypeAssertion(assertion) => {
                self.is_direct_const_enum_member(&assertion.expression)
            }
            Expression::NonNull(non_null) => self.is_direct_const_enum_member(&non_null.expression),
            Expression::Member(member) => Ok(self.enum_facts.const_use(expression.id()).is_some()
                || self.const_enum_symbol(&member.object)?.is_some()),
            _ => Ok(false),
        }
    }
    fn build_arguments(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        arguments: &[CallArgument],
    ) -> Result<Register, LowerError> {
        let array = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: array })?;
        for argument in arguments {
            match argument {
                CallArgument::Expression(expression) => {
                    let value = self.lower_expression(builder, expression)?;
                    self.emit(range, Instruction::ArrayPush { array, value })?;
                }
                CallArgument::Spread(spread) => {
                    let iterable = self.lower_expression(builder, &spread.argument)?;
                    self.emit(range, Instruction::ArrayExtend { array, iterable })?;
                }
                CallArgument::Missing(missing) => {
                    return Err(self.error(
                        zero_range(),
                        LowerErrorKind::MissingSyntax {
                            expected: missing.expected(),
                        },
                    ));
                }
            }
        }
        Ok(array)
    }
    fn call_with_registers(
        &mut self,
        range: TextRange,
        callee: Register,
        this_value: Register,
        values: &[Register],
    ) -> Result<Register, LowerError> {
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        for &value in values {
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: arguments,
                    value,
                },
            )?;
        }
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst,
                callee,
                this_value,
                arguments,
            },
        )?;
        Ok(dst)
    }
    fn lower_array(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        array: &crate::syntax::ArrayLiteral,
    ) -> Result<Register, LowerError> {
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst })?;
        for element in &array.elements {
            match element {
                ArrayElement::Expression(expression) => {
                    let value = self.lower_expression(builder, expression)?;
                    self.emit(range, Instruction::ArrayPush { array: dst, value })?;
                }
                ArrayElement::Spread(spread) => {
                    let iterable = self.lower_expression(builder, &spread.argument)?;
                    self.emit(
                        range,
                        Instruction::ArrayExtend {
                            array: dst,
                            iterable,
                        },
                    )?;
                }
                ArrayElement::Elision => {
                    let hole = self.undefined(builder, range)?;
                    self.emit(
                        range,
                        Instruction::ArrayPush {
                            array: dst,
                            value: hole,
                        },
                    )?;
                }
                ArrayElement::Missing(missing) => {
                    return Err(self.missing(range, missing.expected()));
                }
            }
        }
        Ok(dst)
    }
    fn lower_object(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        object: &ObjectLiteral,
    ) -> Result<Register, LowerError> {
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst })?;
        for member in &object.members {
            match member.data() {
                ObjectMember::Property(property) => {
                    let key = self.property_key(builder, &property.name)?;
                    let value = self.lower_expression(builder, &property.value)?;
                    self.install_property(
                        builder,
                        member.range(),
                        dst,
                        key,
                        value,
                        property.modifier,
                    )?;
                }
                ObjectMember::Method(method) => {
                    let key = self.property_key(builder, &method.name)?;
                    let value =
                        self.build_function_value(builder, member.range(), None, &method.function)?;
                    self.install_property(
                        builder,
                        member.range(),
                        dst,
                        key,
                        value,
                        method.modifier,
                    )?;
                }
                ObjectMember::Spread(spread) => {
                    let source = self.lower_expression(builder, &spread.argument)?;
                    self.emit(
                        member.range(),
                        Instruction::ObjectSpread {
                            target: dst,
                            source,
                        },
                    )?;
                }
                ObjectMember::Missing(missing) => {
                    return Err(self.missing(member.range(), missing.expected()));
                }
            }
        }
        Ok(dst)
    }
    fn install_property(
        &mut self,
        _builder: &mut ModuleBuilder,
        range: TextRange,
        object: Register,
        key: Register,
        value: Register,
        modifier: PropertyModifier,
    ) -> Result<(), LowerError> {
        match modifier {
            PropertyModifier::None => {
                self.emit(range, Instruction::SetProperty { object, key, value })?;
            }
            PropertyModifier::Get => {
                self.emit(
                    range,
                    Instruction::DefineAccessor {
                        object,
                        key,
                        accessor: value,
                        kind: AccessorKind::Getter,
                    },
                )?;
            }
            PropertyModifier::Set => {
                self.emit(
                    range,
                    Instruction::DefineAccessor {
                        object,
                        key,
                        accessor: value,
                        kind: AccessorKind::Setter,
                    },
                )?;
            }
        }
        Ok(())
    }
    fn set_named_entry(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        object: Register,
        name: &str,
        value: Register,
    ) -> Result<(), LowerError> {
        let key = self.string_reg(builder, EcmaString::encode(name), range)?;
        self.emit(range, Instruction::SetProperty { object, key, value })?;
        Ok(())
    }
    fn set_named_flag(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        object: Register,
        name: &str,
        value: bool,
    ) -> Result<(), LowerError> {
        let value = self.load_constant(builder, Constant::Boolean(value), range)?;
        self.set_named_entry(builder, range, object, name, value)
    }
    fn raise_type_error(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        // Always call a fresh known non-callable. Never pass a user-returned
        // value here: a callable invalid decorator return would run user code
        // instead of throwing an engine TypeError.
        let dummy = self.load_constant(builder, Constant::Boolean(true), range)?;
        let undefined = self.undefined(builder, range)?;
        let _ = self.call_with_registers(range, dummy, undefined, &[])?;
        Ok(())
    }
    fn accept_replacement_callable(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        returned: Register,
        slot: Register,
    ) -> Result<(), LowerError> {
        let undefined = self.undefined(builder, range)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: returned,
                right: undefined,
            },
        )?;
        let inspect = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let done_keep = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(inspect, self.next_pc());
        let return_type = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Unary {
                dst: return_type,
                op: UnaryOp::TypeOf,
                operand: returned,
            },
        )?;
        let function_type = self.string_reg(builder, EcmaString::encode("function"), range)?;
        let is_function = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_function,
                op: BinaryOp::StrictEqual,
                left: return_type,
                right: function_type,
            },
        )?;
        let accept = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_function,
                target: Pc::new(0),
            },
        )?;
        self.raise_type_error(builder, range)?;
        let done_error = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(accept, self.next_pc());
        self.move_to(range, slot, returned)?;
        let after = self.next_pc();
        self.patch_jump(done_keep, after);
        self.patch_jump(done_error, after);
        Ok(())
    }
    fn collect_optional_callable(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        returned: Register,
        collected: Register,
    ) -> Result<Register, LowerError> {
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, collected, undefined)?;
        let collected_flag = self.alloc_register(range)?;
        let flag_false = self.load_constant(builder, Constant::Boolean(false), range)?;
        self.move_to(range, collected_flag, flag_false)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: returned,
                right: undefined,
            },
        )?;
        let inspect = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let done_keep = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(inspect, self.next_pc());
        let return_type = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Unary {
                dst: return_type,
                op: UnaryOp::TypeOf,
                operand: returned,
            },
        )?;
        let function_type = self.string_reg(builder, EcmaString::encode("function"), range)?;
        let is_function = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_function,
                op: BinaryOp::StrictEqual,
                left: return_type,
                right: function_type,
            },
        )?;
        let accept = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_function,
                target: Pc::new(0),
            },
        )?;
        self.raise_type_error(builder, range)?;
        let done_error = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(accept, self.next_pc());
        self.move_to(range, collected, returned)?;
        let flag_true = self.load_constant(builder, Constant::Boolean(true), range)?;
        self.move_to(range, collected_flag, flag_true)?;
        let after = self.next_pc();
        self.patch_jump(done_keep, after);
        self.patch_jump(done_error, after);
        Ok(collected_flag)
    }
    fn build_access_closure(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        key: Register,
        role: AccessRole,
    ) -> Result<Register, LowerError> {
        let captures = [CaptureKey::Parent(key)];
        let parameter_count = match role {
            AccessRole::Set => 2,
            AccessRole::Get | AccessRole::Has => 1,
        };
        self.build_synthetic_function(
            builder,
            range,
            None,
            &captures,
            parameter_count,
            move |inner, builder, parameters| {
                let key = Register::new(0);
                let object = parameters[0];
                match role {
                    AccessRole::Get => {
                        let dst = inner.alloc_register(range)?;
                        inner.emit(range, Instruction::GetProperty { dst, object, key })?;
                        Ok(dst)
                    }
                    AccessRole::Set => {
                        let value = parameters[1];
                        inner.emit(range, Instruction::SetProperty { object, key, value })?;
                        inner.undefined(builder, range)
                    }
                    AccessRole::Has => {
                        let dst = inner.alloc_register(range)?;
                        inner.emit(
                            range,
                            Instruction::Binary {
                                dst,
                                op: BinaryOp::In,
                                left: key,
                                right: object,
                            },
                        )?;
                        Ok(dst)
                    }
                }
            },
        )
    }
    fn build_access_object(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        key: Register,
        kind: MemberDecorationKind,
    ) -> Result<Register, LowerError> {
        let access = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst: access })?;
        let has = self.build_access_closure(builder, range, key, AccessRole::Has)?;
        self.set_named_entry(builder, range, access, "has", has)?;
        let (include_get, include_set) = match kind {
            MemberDecorationKind::Method | MemberDecorationKind::Getter => (true, false),
            MemberDecorationKind::Setter => (false, true),
            MemberDecorationKind::Field | MemberDecorationKind::AutoAccessor => (true, true),
        };
        if include_get {
            let get = self.build_access_closure(builder, range, key, AccessRole::Get)?;
            self.set_named_entry(builder, range, access, "get", get)?;
        }
        if include_set {
            let set = self.build_access_closure(builder, range, key, AccessRole::Set)?;
            self.set_named_entry(builder, range, access, "set", set)?;
        }
        Ok(access)
    }
    fn build_add_initializer(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        queue: Register,
        state_cell: Register,
    ) -> Result<Register, LowerError> {
        let captures = [CaptureKey::Parent(queue), CaptureKey::Cell(state_cell)];
        self.build_synthetic_function(
            builder,
            range,
            None,
            &captures,
            1,
            move |inner, builder, parameters| {
                let queue = Register::new(0);
                let state_cell = Register::new(1);
                let callback = parameters[0];
                let accepted = inner.undefined(builder, range)?;
                let state = inner.cell_value(builder, state_cell, range)?;
                let still_open = inner.emit(
                    range,
                    Instruction::JumpIfFalse {
                        condition: state,
                        target: Pc::new(0),
                    },
                )?;
                inner.raise_type_error(builder, range)?;
                let closed_done = inner.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                inner.patch_jump(still_open, inner.next_pc());
                let callback_type = inner.alloc_register(range)?;
                inner.emit(
                    range,
                    Instruction::Unary {
                        dst: callback_type,
                        op: UnaryOp::TypeOf,
                        operand: callback,
                    },
                )?;
                let function_type =
                    inner.string_reg(builder, EcmaString::encode("function"), range)?;
                let is_function = inner.alloc_register(range)?;
                inner.emit(
                    range,
                    Instruction::Binary {
                        dst: is_function,
                        op: BinaryOp::StrictEqual,
                        left: callback_type,
                        right: function_type,
                    },
                )?;
                let accept = inner.emit(
                    range,
                    Instruction::JumpIfTrue {
                        condition: is_function,
                        target: Pc::new(0),
                    },
                )?;
                inner.raise_type_error(builder, range)?;
                let bad_done = inner.emit(range, Instruction::Jump { target: Pc::new(0) })?;
                inner.patch_jump(accept, inner.next_pc());
                inner.emit(
                    range,
                    Instruction::ArrayPush {
                        array: queue,
                        value: callback,
                    },
                )?;
                let after = inner.next_pc();
                inner.patch_jump(closed_done, after);
                inner.patch_jump(bad_done, after);
                Ok(accepted)
            },
        )
    }
    fn member_context_name(
        &mut self,
        builder: &mut ModuleBuilder,
        _range: TextRange,
        name: &PropertyName,
        evaluated_key: Register,
    ) -> Result<Register, LowerError> {
        match name {
            PropertyName::Identifier(identifier) => {
                let text = self.identifier_text(identifier)?;
                self.string_reg(builder, EcmaString::encode(&text), identifier.range())
            }
            PropertyName::String(string) => {
                let value = self.string_literal_value(string)?;
                self.string_reg(builder, value, string.range())
            }
            PropertyName::Number(number) => {
                let key = numeric_key_text(self, number)?;
                self.string_reg(builder, EcmaString::encode(&key), number.range())
            }
            PropertyName::Private(private) => {
                let text = self.private_text(private)?;
                self.string_reg(builder, EcmaString::encode(&text), private.range())
            }
            PropertyName::Computed(_) => Ok(evaluated_key),
            PropertyName::Missing(missing) => Err(self.error(
                zero_range(),
                LowerErrorKind::MissingSyntax {
                    expected: missing.expected(),
                },
            )),
        }
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "member decoration context build shares class lowering registers and metadata"
    )]
    fn build_member_context(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: &PropertyName,
        evaluated_key: Register,
        is_static: bool,
        kind: MemberDecorationKind,
        queue: Register,
        state_cell: Register,
    ) -> Result<Register, LowerError> {
        let context = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst: context })?;
        let kind_value =
            self.string_reg(builder, EcmaString::encode(kind.context_name()), range)?;
        self.set_named_entry(builder, range, context, "kind", kind_value)?;
        let name_value = self.member_context_name(builder, range, name, evaluated_key)?;
        self.set_named_entry(builder, range, context, "name", name_value)?;
        self.set_named_flag(builder, range, context, "static", is_static)?;
        let is_private = matches!(name, PropertyName::Private(_));
        self.set_named_flag(builder, range, context, "private", is_private)?;
        let access = self.build_access_object(builder, range, evaluated_key, kind)?;
        self.set_named_entry(builder, range, context, "access", access)?;
        let add_initializer = self.build_add_initializer(builder, range, queue, state_cell)?;
        self.set_named_entry(builder, range, context, "addInitializer", add_initializer)?;
        Ok(context)
    }
    fn lower_literal(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        literal: &Literal,
    ) -> Result<Register, LowerError> {
        match literal {
            Literal::Number(number) => self.lower_numeric_literal(builder, number),
            Literal::String(string) => {
                let value = self.string_literal_value(string)?;
                self.string_reg(builder, value, range)
            }
            Literal::Boolean(boolean) => {
                let value = self.boolean_literal_value(boolean)?;
                self.load_constant(builder, Constant::Boolean(value), range)
            }
            Literal::Null(_) => self.load_constant(builder, Constant::Null, range),
            Literal::BigInt(_) => self.lower_bigint_literal(builder, range, literal),
            Literal::Regex(regex) => self.lower_regex_literal(builder, range, regex),
        }
    }
    fn lower_template(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        template: &TemplateLiteral,
    ) -> Result<Register, LowerError> {
        let cooked = self.cooked_template_parts(template)?;
        let first = cooked.first().cloned().unwrap_or_default();
        let mut acc = self.string_reg(builder, first, range)?;
        for (index, expression) in template.expressions.iter().enumerate() {
            let value = self.lower_expression(builder, expression)?;
            let joined = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Binary {
                    dst: joined,
                    op: BinaryOp::Add,
                    left: acc,
                    right: value,
                },
            )?;
            acc = joined;
            let chunk = cooked.get(index + 1).cloned().unwrap_or_default();
            let chunk_reg = self.string_reg(builder, chunk, range)?;
            let joined = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Binary {
                    dst: joined,
                    op: BinaryOp::Add,
                    left: acc,
                    right: chunk_reg,
                },
            )?;
            acc = joined;
        }
        Ok(acc)
    }
    fn lower_tagged_template(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        tagged: &crate::syntax::TaggedTemplateExpression,
    ) -> Result<Register, LowerError> {
        let (callee, this_value) = self.lower_callee(builder, range, &tagged.tag)?;
        let cooked = self.cooked_template_parts(&tagged.template)?;
        let raw = self.raw_template_parts(&tagged.template)?;
        let strings = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: strings })?;
        for part in &cooked {
            let value = self.string_reg(builder, part.clone(), range)?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: strings,
                    value,
                },
            )?;
        }
        let raw_array = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: raw_array })?;
        for part in &raw {
            let value = self.string_reg(builder, part.clone(), range)?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: raw_array,
                    value,
                },
            )?;
        }
        let raw_key = self.string_reg(builder, EcmaString::encode("raw"), range)?;
        self.emit(
            range,
            Instruction::SetProperty {
                object: strings,
                key: raw_key,
                value: raw_array,
            },
        )?;
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        self.emit(
            range,
            Instruction::ArrayPush {
                array: arguments,
                value: strings,
            },
        )?;
        for expression in &tagged.template.expressions {
            let value = self.lower_expression(builder, expression)?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: arguments,
                    value,
                },
            )?;
        }
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst,
                callee,
                this_value,
                arguments,
            },
        )?;
        Ok(dst)
    }
    fn cooked_template_parts(
        &self,
        template: &TemplateLiteral,
    ) -> Result<Vec<EcmaString>, LowerError> {
        template
            .elements
            .iter()
            .map(|element| self.template_element_text(element, true))
            .collect()
    }
    fn raw_template_parts(
        &self,
        template: &TemplateLiteral,
    ) -> Result<Vec<EcmaString>, LowerError> {
        template
            .elements
            .iter()
            .map(|element| self.template_element_text(element, false))
            .collect()
    }
    fn template_element_text(
        &self,
        element: &TemplateElementNode,
        cook: bool,
    ) -> Result<EcmaString, LowerError> {
        let token = element.data().token();
        if token.is_missing() {
            return Ok(EcmaString::default());
        }
        let Some(text) = self.file.token_text(token) else {
            return Ok(EcmaString::default());
        };
        let interior = trim_template_delimiters(text, token.kind());
        if cook {
            Ok(cook_escapes(interior))
        } else {
            Ok(EcmaString::encode(interior))
        }
    }
    fn lower_regex_literal(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        regex: &RegexLiteralNode,
    ) -> Result<Register, LowerError> {
        let token = regex.data().token();
        if token.is_missing() {
            return Err(self.missing(range, NodeKind::RegexLiteral));
        }
        let lexeme = self
            .file
            .token_text(token)
            .ok_or_else(|| self.error(range, LowerErrorKind::InvalidRegexLiteral))?;
        let (pattern, flags) = split_regex(lexeme)
            .ok_or_else(|| self.error(range, LowerErrorKind::InvalidRegexLiteral))?;
        let pattern_id = builder.intern(Constant::String(EcmaString::encode(&pattern)), range)?;
        let flags_id = builder.intern(Constant::String(EcmaString::encode(&flags)), range)?;
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateRegExp {
                dst,
                pattern: pattern_id,
                flags: flags_id,
            },
        )?;
        Ok(dst)
    }
    fn lower_bigint_literal(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        literal: &Literal,
    ) -> Result<Register, LowerError> {
        let Literal::BigInt(node) = literal else {
            unreachable!("lower_bigint_literal only handles bigint literals");
        };
        let token = node.data().token();
        if token.is_missing() {
            return Err(self.missing(range, NodeKind::BigIntLiteral));
        }
        let lexeme = self
            .file
            .token_text(token)
            .ok_or_else(|| self.error(range, LowerErrorKind::InvalidBigIntLiteral))?;
        let canonical = canonical_bigint_text(
            lexeme,
            MAX_BIGINT_BYTES as usize,
            MAX_BIGINT_CONVERSION_LIMB_OPS,
        )
        .map_err(|error| {
            self.error(
                range,
                match error {
                    BigIntTextError::Invalid => LowerErrorKind::InvalidBigIntLiteral,
                    BigIntTextError::Bytes => LowerErrorKind::Capacity(CapacityLimit::BigIntBytes),
                    BigIntTextError::Work => LowerErrorKind::Capacity(CapacityLimit::BigIntWork),
                },
            )
        })?;
        let value = BigIntLiteral::new(canonical)
            .ok_or_else(|| self.error(range, LowerErrorKind::InvalidBigIntLiteral))?;
        self.load_constant(builder, Constant::BigInt(value), range)
    }
    fn lower_numeric_literal(
        &mut self,
        builder: &mut ModuleBuilder,
        number: &NumericLiteralNode,
    ) -> Result<Register, LowerError> {
        let range = number.range();
        let token = number.data().token();
        if token.is_missing() {
            return Err(self.missing(range, NodeKind::NumericLiteral));
        }
        let lexeme = self
            .generated_text(number.id())
            .or_else(|| self.file.token_text(token).filter(|text| !text.is_empty()));
        let lexeme =
            lexeme.ok_or_else(|| self.error(range, LowerErrorKind::InvalidNumericLiteral))?;
        let value = number_value(lexeme)
            .ok_or_else(|| self.error(range, LowerErrorKind::InvalidNumericLiteral))?;
        self.load_constant(builder, number_constant(value), range)
    }
    fn string_literal_value(&self, string: &StringLiteralNode) -> Result<EcmaString, LowerError> {
        let range = string.range();
        if let Some(text) = self.generated_text(string.id()) {
            return Ok(EcmaString::encode(text));
        }
        let token = string.data().token();
        let missing = || self.missing(range, NodeKind::StringLiteral);
        if token.is_missing() {
            return Err(missing());
        }
        let text = self.file.token_text(token).ok_or_else(missing)?;
        string_value(text).ok_or_else(missing)
    }
    fn boolean_literal_value(&self, boolean: &BooleanLiteralNode) -> Result<bool, LowerError> {
        let token = boolean.data().token();
        match token.kind() {
            TokenKind::KwTrue if !token.is_missing() => Ok(true),
            TokenKind::KwFalse if !token.is_missing() => Ok(false),
            _ => Err(self.missing(boolean.range(), NodeKind::BooleanLiteral)),
        }
    }
    fn member_key(
        &mut self,
        builder: &mut ModuleBuilder,
        property: &MemberProperty,
    ) -> Result<Register, LowerError> {
        match property {
            MemberProperty::Named(identifier) => {
                let name = self.identifier_text(identifier)?;
                self.string_reg(builder, EcmaString::encode(&name), identifier.range())
            }
            MemberProperty::Computed(expression) => self.lower_expression(builder, expression),
            MemberProperty::Private(private) => {
                let name = self.private_text(private)?;
                self.read_name(builder, &name, private.range())
            }
        }
    }
    fn property_key(
        &mut self,
        builder: &mut ModuleBuilder,
        name: &PropertyName,
    ) -> Result<Register, LowerError> {
        match name {
            PropertyName::Identifier(identifier) => {
                let text = self.identifier_text(identifier)?;
                self.string_reg(builder, EcmaString::encode(&text), identifier.range())
            }
            PropertyName::String(string) => {
                let value = self.string_literal_value(string)?;
                self.string_reg(builder, value, string.range())
            }
            PropertyName::Number(number) => {
                let key = numeric_key_text(self, number)?;
                self.string_reg(builder, EcmaString::encode(&key), number.range())
            }
            PropertyName::Computed(expression) => self.lower_expression(builder, expression),
            PropertyName::Private(private) => {
                let name = self.private_text(private)?;
                self.read_name(builder, &name, private.range())
            }
            PropertyName::Missing(missing) => Err(self.error(
                zero_range(),
                LowerErrorKind::MissingSyntax {
                    expected: missing.expected(),
                },
            )),
        }
    }
    fn lower_import(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        import: &ImportDeclaration,
    ) -> Result<(), LowerError> {
        if self.goal == LoweringGoal::ClassicScript {
            return Err(self.error(range, LowerErrorKind::ImportDeclarationInScript));
        }
        if import.type_only || self.goal == LoweringGoal::ProgramModule {
            return Ok(());
        }
        let specifier = self.string_literal_value(&import.source)?;
        let specifier_id = builder.intern(Constant::String(specifier), range)?;
        let module = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Import {
                dst: module,
                specifier: specifier_id,
            },
        )?;
        let Some(clause) = &import.clause else {
            return Ok(());
        };
        if let Some(default) = &clause.default {
            let name = self.identifier_text(default)?;
            let value = self.get_named(builder, range, module, "default")?;
            self.store_binding(
                builder,
                &name,
                value,
                range,
                binding_site(default.range()),
                DeclarationScope::Function,
            )?;
        }
        match &clause.binding {
            Some(ImportBinding::Namespace(identifier)) => {
                let name = self.identifier_text(identifier)?;
                self.store_binding(
                    builder,
                    &name,
                    module,
                    range,
                    binding_site(identifier.range()),
                    DeclarationScope::Function,
                )?;
            }
            Some(ImportBinding::Named(specifiers)) => {
                for specifier in specifiers {
                    let data = specifier.data();
                    if matches!(data.mode, ImportSpecifierMode::TypeOnly)
                        || self.enum_facts.is_elided_import_specifier(specifier.id())
                    {
                        continue;
                    }
                    let local = self.identifier_text(&data.local)?;
                    let imported = self.module_export_name(&data.imported)?;
                    let value = self.get_named(builder, range, module, &imported)?;
                    self.store_binding(
                        builder,
                        &local,
                        value,
                        range,
                        binding_site(data.local.range()),
                        DeclarationScope::Function,
                    )?;
                }
            }
            None => {}
        }
        Ok(())
    }
    fn lower_import_equals(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
        range: TextRange,
        import: &crate::syntax::ImportEqualsDeclaration,
    ) -> Result<(), LowerError> {
        let crate::syntax::ExternalModuleReference::Qualified(_) = &import.reference else {
            if import.is_type_only {
                return Ok(());
            }
            return Err(self.unsupported(range, UnsupportedConstruct::RuntimeImportEquals));
        };
        let Some(path) = self.namespace_facts.qualified_import_path(statement.id()) else {
            if import.is_type_only {
                return Ok(());
            }
            return Err(self.unsupported(range, UnsupportedConstruct::RuntimeImportEquals));
        };
        let Some((&first, members)) = path.split_first() else {
            return Err(self.unsupported(range, UnsupportedConstruct::RuntimeImportEquals));
        };
        let mut value = if let Some(container) = self
            .containers
            .iter()
            .rev()
            .find(|container| container.symbol == first)
        {
            container.object
        } else if self.namespace_root_has_runtime_container(first) {
            let name = self.symbols[first.get() as usize].name().to_owned();
            self.read_name(builder, name.as_ref(), range)?
        } else {
            return Ok(());
        };
        for member in members {
            let name = self.symbols[member.get() as usize].name().to_owned();
            value = self.get_named(builder, range, value, &name)?;
        }
        let local = self.identifier_text(&import.local)?;
        self.store_binding(
            builder,
            &local,
            value,
            range,
            binding_site(import.local.range()),
            DeclarationScope::Function,
        )
    }
    fn namespace_root_has_runtime_container(&self, symbol: crate::checker::SymbolId) -> bool {
        if !matches!(
            self.symbols[symbol.get() as usize].kind(),
            crate::checker::SymbolKind::Namespace
        ) {
            return true;
        }
        self.namespace_facts
            .merged_declarations(symbol)
            .iter()
            .any(|declaration| {
                self.namespace_facts
                    .declaration(*declaration)
                    .is_some_and(crate::namespace_plan::NamespacePlan::is_value_bearing)
            })
    }
    fn lower_import_expression(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        import: &crate::syntax::ImportExpression,
    ) -> Result<Register, LowerError> {
        let specifier = self.lower_expression(builder, &import.source)?;
        if let Some(options) = &import.options {
            self.lower_expression(builder, options)?;
        }
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::ImportDynamic { dst, specifier })?;
        Ok(dst)
    }
    fn get_named(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        object: Register,
        name: &str,
    ) -> Result<Register, LowerError> {
        let key = self.string_reg(builder, EcmaString::encode(name), range)?;
        let dst = self.alloc_register(range)?;
        self.emit(range, Instruction::GetProperty { dst, object, key })?;
        Ok(dst)
    }
    fn materialize_empty_exported_namespace(
        &mut self,
        builder: &mut ModuleBuilder,
        statement: &Stmt,
    ) -> Result<(), LowerError> {
        let Statement::Namespace(declaration) = statement.data() else {
            return Ok(());
        };
        let Some(plan) = self.namespace_facts.declaration(statement.id()) else {
            return Ok(());
        };
        if plan.is_value_bearing()
            || !matches!(plan.acquisition(), ContainerAcquisition::Binding)
            || !declaration.body.data().statements.is_empty()
        {
            return Ok(());
        }
        let NamespaceName::Identifier {
            name: name_node, ..
        } = &declaration.name
        else {
            return Ok(());
        };
        let name = self.identifier_text(name_node)?;
        let object = self.read_name(builder, &name, statement.range())?;
        let reuse = self.emit(
            statement.range(),
            Instruction::JumpIfTrue {
                condition: object,
                target: Pc::new(0),
            },
        )?;
        self.emit(statement.range(), Instruction::CreateObject { dst: object })?;
        self.assign_name(builder, &name, object, statement.range())?;
        self.patch_jump(reuse, self.next_pc());
        Ok(())
    }
    fn export_binding(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        local: &str,
        exported: &str,
    ) -> Result<(), LowerError> {
        if self.goal == LoweringGoal::ProgramModule {
            return Ok(());
        }
        let src = self.read_name(builder, local, range)?;
        let name = builder.intern(Constant::String(EcmaString::encode(exported)), range)?;
        self.emit(range, Instruction::Export { name, src })?;
        Ok(())
    }
    fn export_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        exported: &str,
        src: Register,
    ) -> Result<(), LowerError> {
        if self.goal == LoweringGoal::ProgramModule {
            debug_assert_eq!(exported, "default");
            return self.store_binding(
                builder,
                "*default*",
                src,
                range,
                binding_site(range),
                DeclarationScope::Lexical,
            );
        }
        let name = builder.intern(Constant::String(EcmaString::encode(exported)), range)?;
        self.emit(range, Instruction::Export { name, src })?;
        Ok(())
    }
    fn lower_export(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        export: &ExportDeclaration,
    ) -> Result<(), LowerError> {
        if self.goal == LoweringGoal::ClassicScript {
            return Err(self.error(range, LowerErrorKind::ExportDeclarationInScript));
        }
        match export {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(statement)) => {
                self.lower_statement(builder, statement)?;
                self.materialize_empty_exported_namespace(builder, statement)?;
                for name in declared_names(self.file, statement) {
                    self.export_binding(builder, range, &name, &name)?;
                }
                Ok(())
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source,
                ..
            }) => {
                if *type_only || self.goal == LoweringGoal::ProgramModule {
                    return Ok(());
                }
                if let Some(source) = source {
                    let specifier = self.string_literal_value(source)?;
                    let specifier_id = builder.intern(Constant::String(specifier), range)?;
                    let module = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::Import {
                            dst: module,
                            specifier: specifier_id,
                        },
                    )?;
                    for specifier in specifiers {
                        let data = specifier.data();
                        if matches!(data.mode, ExportSpecifierMode::TypeOnly) {
                            continue;
                        }
                        let local = self.module_export_name(&data.local)?;
                        let exported = self.module_export_name(&data.exported)?;
                        let value = self.get_named(builder, range, module, &local)?;
                        self.export_value(builder, range, &exported, value)?;
                    }
                    return Ok(());
                }
                for specifier in specifiers {
                    let data = specifier.data();
                    if matches!(data.mode, ExportSpecifierMode::TypeOnly) {
                        continue;
                    }
                    let local = self.module_export_name(&data.local)?;
                    let exported = self.module_export_name(&data.exported)?;
                    self.export_binding(builder, range, &local, &exported)?;
                }
                Ok(())
            }
            ExportDeclaration::All(all) => {
                if all.type_only || self.goal == LoweringGoal::ProgramModule {
                    Ok(())
                } else {
                    Err(self.unsupported(range, UnsupportedConstruct::RuntimeExportAll))
                }
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Expression(expression) => {
                    let value = self.lower_expression(builder, expression)?;
                    self.export_value(builder, range, "default", value)
                }
                ExportDefaultValue::Function(function) => {
                    if function.body.is_none() {
                        return Ok(());
                    }
                    if let Some(identifier) = &function.name {
                        let name = self.identifier_text(identifier)?;
                        let closure = self.read_name(builder, &name, range)?;
                        self.export_value(builder, range, "default", closure)
                    } else {
                        let closure = self
                            .build_constructible_function_value(builder, range, None, function)?;
                        self.export_value(builder, range, "default", closure)
                    }
                }
                ExportDefaultValue::Class(class) => {
                    let value = self.lower_class_value(builder, range, class, None, None)?;
                    if let Some(identifier) = &class.name {
                        let name = self.identifier_text(identifier)?;
                        self.store_binding(
                            builder,
                            &name,
                            value,
                            range,
                            binding_site(identifier.range()),
                            DeclarationScope::Lexical,
                        )?;
                    }
                    self.export_value(builder, range, "default", value)
                }
                ExportDefaultValue::Missing(missing) => {
                    Err(self.missing(range, missing.expected()))
                }
                ExportDefaultValue::Interface(_) => Ok(()),
            },
            ExportDeclaration::Assignment(expression) => {
                let value = self.lower_expression(builder, expression)?;
                self.store_binding(
                    builder,
                    "*export=*",
                    value,
                    range,
                    binding_site(range),
                    DeclarationScope::Lexical,
                )
            }
        }
    }
    fn module_export_name(&self, name: &ModuleExportName) -> Result<String, LowerError> {
        match name {
            ModuleExportName::Identifier(identifier) => self.identifier_text(identifier),
            ModuleExportName::String(string) => self
                .string_literal_value(string)?
                .to_utf8_strict()
                .map_err(|_| self.error(string.range(), LowerErrorKind::IllFormedMetadataString)),
            ModuleExportName::Missing(missing) => Err(self.error(
                zero_range(),
                LowerErrorKind::MissingSyntax {
                    expected: missing.expected(),
                },
            )),
        }
    }
    fn bind_pattern(
        &mut self,
        builder: &mut ModuleBuilder,
        pattern: &Pattern,
        value: Register,
        declaration_scope: DeclarationScope,
    ) -> Result<(), LowerError> {
        let range = pattern.range();
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                self.store_binding(
                    builder,
                    &name,
                    value,
                    range,
                    binding_site(identifier.range()),
                    declaration_scope,
                )
            }
            BindingPattern::Object(object) => {
                let mut taken: Vec<Register> = Vec::new();
                for property in &object.properties {
                    if let BindingPattern::Rest(rest) = property.binding.data() {
                        let rest_value = self.rest_object(builder, range, value, &taken)?;
                        self.bind_pattern(builder, &rest.argument, rest_value, declaration_scope)?;
                        continue;
                    }
                    let key = self.property_key(builder, &property.name)?;
                    taken.push(key);
                    let element = self.alloc_register(range)?;
                    self.emit(
                        range,
                        Instruction::GetProperty {
                            dst: element,
                            object: value,
                            key,
                        },
                    )?;
                    let element = match &property.initializer {
                        Some(default) => self.apply_default(builder, range, element, default)?,
                        None => element,
                    };
                    self.bind_pattern(builder, &property.binding, element, declaration_scope)?;
                }
                Ok(())
            }
            BindingPattern::Array(array) => {
                let iterator = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetIterator {
                        dst: iterator,
                        src: value,
                        kind: IteratorKind::Sync,
                    },
                )?;
                for element in &array.elements {
                    match element {
                        ArrayBindingElement::Elision => {
                            self.iterator_step_discard(range, iterator)?;
                        }
                        ArrayBindingElement::Binding(inner) => {
                            if let BindingPattern::Rest(rest) = inner.data() {
                                let rest_value = self.rest_array(builder, range, iterator)?;
                                self.bind_pattern(
                                    builder,
                                    &rest.argument,
                                    rest_value,
                                    declaration_scope,
                                )?;
                            } else {
                                let (element_value, default) = self.destructure_element(inner);
                                let value = self.iterator_step_value(builder, range, iterator)?;
                                let value = match default {
                                    Some(default) => {
                                        self.apply_default(builder, range, value, default)?
                                    }
                                    None => value,
                                };
                                let _ = element_value;
                                self.bind_pattern(builder, inner, value, declaration_scope)?;
                            }
                        }
                        ArrayBindingElement::Missing(missing) => {
                            return Err(self.missing(range, missing.expected()));
                        }
                    }
                }
                Ok(())
            }
            BindingPattern::Assignment(assignment) => {
                let value = self.apply_default(builder, range, value, &assignment.right)?;
                self.bind_pattern(builder, &assignment.left, value, declaration_scope)
            }
            BindingPattern::Rest(rest) => {
                self.bind_pattern(builder, &rest.argument, value, declaration_scope)
            }
            BindingPattern::Missing(missing) => Err(self.missing(range, missing.expected())),
        }
    }
    fn destructure_element<'p>(&self, pattern: &'p Pattern) -> (&'p Pattern, Option<&'p Expr>) {
        if let BindingPattern::Assignment(assignment) = pattern.data() {
            (&assignment.left, Some(&assignment.right))
        } else {
            (pattern, None)
        }
    }
    fn apply_default(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
        default: &Expr,
    ) -> Result<Register, LowerError> {
        let result = self.alloc_register(range)?;
        self.move_to(range, result, value)?;
        let undefined = self.undefined(builder, range)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: value,
                right: undefined,
            },
        )?;
        let skip = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let default_value = self.lower_expression(builder, default)?;
        self.move_to(range, result, default_value)?;
        let end = self.next_pc();
        self.patch_jump(skip, end);
        Ok(result)
    }
    fn iterator_step_discard(
        &mut self,
        range: TextRange,
        iterator: Register,
    ) -> Result<(), LowerError> {
        let done = self.alloc_register(range)?;
        let value = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            },
        )?;
        Ok(())
    }
    fn iterator_step_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        iterator: Register,
    ) -> Result<Register, LowerError> {
        let done = self.alloc_register(range)?;
        let value = self.alloc_register(range)?;
        let result = self.alloc_register(range)?;
        let undefined = self.undefined(builder, range)?;
        self.move_to(range, result, undefined)?;
        self.emit(
            range,
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            },
        )?;
        let skip = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        self.move_to(range, result, value)?;
        let end = self.next_pc();
        self.patch_jump(skip, end);
        Ok(result)
    }
    fn rest_array(
        &mut self,
        _builder: &mut ModuleBuilder,
        range: TextRange,
        iterator: Register,
    ) -> Result<Register, LowerError> {
        let array = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: array })?;
        let done = self.alloc_register(range)?;
        let value = self.alloc_register(range)?;
        let head = self.next_pc();
        self.emit(
            range,
            Instruction::IteratorNext {
                done,
                value,
                iterator,
            },
        )?;
        let exit = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: done,
                target: Pc::new(0),
            },
        )?;
        self.emit(range, Instruction::ArrayPush { array, value })?;
        self.emit(range, Instruction::Jump { target: head })?;
        let exit_pc = self.next_pc();
        self.patch_jump(exit, exit_pc);
        Ok(array)
    }
    fn rest_object(
        &mut self,
        _builder: &mut ModuleBuilder,
        range: TextRange,
        object: Register,
        taken: &[Register],
    ) -> Result<Register, LowerError> {
        let rest = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst: rest })?;
        self.emit(
            range,
            Instruction::ObjectSpread {
                target: rest,
                source: object,
            },
        )?;
        for key in taken {
            let discarded = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::DeleteProperty {
                    dst: discarded,
                    object: rest,
                    key: *key,
                },
            )?;
        }
        Ok(rest)
    }
    fn assign_target(
        &mut self,
        builder: &mut ModuleBuilder,
        target: &AssignmentTargetNode,
        value: Register,
    ) -> Result<(), LowerError> {
        let range = target.range();
        match target.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.identifier_text(identifier)?;
                self.assign_name(builder, &name, value, range)
            }
            AssignmentTarget::Member(member) => {
                if self.is_const_enum_member_target(target, &member.object)? {
                    return Err(self.const_enum_operation(range, ConstEnumOperation::Write));
                }
                let object = self.lower_expression(builder, &member.object)?;
                let key = self.member_key(builder, &member.property)?;
                self.emit(range, Instruction::SetProperty { object, key, value })?;
                Ok(())
            }
            AssignmentTarget::Object(object) => {
                let mut taken: Vec<Register> = Vec::new();
                for property in &object.properties {
                    self.assign_object_property(builder, range, value, property, &mut taken)?;
                }
                Ok(())
            }
            AssignmentTarget::Array(array) => {
                let iterator = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::GetIterator {
                        dst: iterator,
                        src: value,
                        kind: IteratorKind::Sync,
                    },
                )?;
                for element in &array.elements {
                    match element {
                        AssignmentArrayElement::Elision => {
                            self.iterator_step_discard(range, iterator)?;
                        }
                        AssignmentArrayElement::Target(inner) => {
                            let element = self.iterator_step_value(builder, range, iterator)?;
                            self.assign_target(builder, inner, element)?;
                        }
                        AssignmentArrayElement::Missing(missing) => {
                            return Err(self.missing(range, missing.expected()));
                        }
                    }
                }
                Ok(())
            }
            AssignmentTarget::Missing(missing) => Err(self.missing(range, missing.expected())),
            AssignmentTarget::Invalid(_) => {
                Err(self.missing(range, NodeKind::AssignmentExpression))
            }
        }
    }
    fn assign_object_property(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        source: Register,
        property: &AssignmentObjectProperty,
        taken: &mut Vec<Register>,
    ) -> Result<(), LowerError> {
        let key = self.property_key(builder, &property.name)?;
        taken.push(key);
        let element = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: element,
                object: source,
                key,
            },
        )?;
        let element = match &property.initializer {
            Some(default) => self.apply_default(builder, range, element, default)?,
            None => element,
        };
        self.assign_target(builder, &property.target, element)
    }
    fn lower_arrow(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        arrow: &ArrowFunction,
    ) -> Result<Register, LowerError> {
        let flags = FunctionFlags {
            is_async: arrow.is_async,
            is_generator: false,
            is_constructable: false,
        };
        let captures =
            self.compute_captures(&arrow.parameters, LoweredBody::Arrow(&arrow.body), true);
        let id = builder.reserve_function(range)?;
        self.build_function_into(
            builder,
            id,
            range,
            None,
            &arrow.parameters,
            LoweredBody::Arrow(&arrow.body),
            flags,
            &captures,
            true,
        )?;
        self.materialize_closure(builder, range, id, &captures)
    }
    fn build_constructible_function_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: Option<String>,
        function: &FunctionLike,
    ) -> Result<Register, LowerError> {
        let flags = FunctionFlags {
            is_async: function.is_async,
            is_generator: function.is_generator,
            is_constructable: !function.is_async && !function.is_generator,
        };
        let closure =
            self.build_function_value_with_flags(builder, range, name, function, flags)?;
        if !function.is_async && !function.is_generator {
            let prototype = self.alloc_register(range)?;
            self.emit(range, Instruction::CreateObject { dst: prototype })?;
            let constructor_key =
                self.string_reg(builder, EcmaString::encode("constructor"), range)?;
            self.emit(
                range,
                Instruction::SetProperty {
                    object: prototype,
                    key: constructor_key,
                    value: closure,
                },
            )?;
            let prototype_key = self.string_reg(builder, EcmaString::encode("prototype"), range)?;
            self.emit(
                range,
                Instruction::SetProperty {
                    object: closure,
                    key: prototype_key,
                    value: prototype,
                },
            )?;
        }
        Ok(closure)
    }
    fn build_function_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: Option<String>,
        function: &FunctionLike,
    ) -> Result<Register, LowerError> {
        let flags = FunctionFlags {
            is_async: function.is_async,
            is_generator: function.is_generator,
            is_constructable: false,
        };
        self.build_function_value_with_flags(builder, range, name, function, flags)
    }

    fn build_function_value_with_flags(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: Option<String>,
        function: &FunctionLike,
        flags: FunctionFlags,
    ) -> Result<Register, LowerError> {
        let body = function
            .body
            .as_ref()
            .ok_or_else(|| self.missing(range, NodeKind::BlockStatement))?;
        let captures =
            self.compute_captures(&function.parameters, LoweredBody::Function(body), false);
        let id = builder.reserve_function(range)?;
        self.build_function_into(
            builder,
            id,
            range,
            name,
            &function.parameters,
            LoweredBody::Function(body),
            flags,
            &captures,
            false,
        )?;
        self.materialize_closure(builder, range, id, &captures)
    }
    #[allow(clippy::too_many_arguments)]
    fn build_function_into(
        &mut self,
        builder: &mut ModuleBuilder,
        id: FunctionId,
        range: TextRange,
        name: Option<String>,
        parameters: &[ParameterNode],
        body: LoweredBody<'_>,
        flags: FunctionFlags,
        captures: &[CaptureKey],
        is_arrow: bool,
    ) -> Result<(), LowerError> {
        self.reject_parameter_decorators(parameters)?;
        let capture_plan = CapturePlan::for_function(self.file, self.jsx_plan, parameters, body);
        let mut inner = FunctionContext {
            file: self.file,
            jsx_plan: self.jsx_plan,
            enum_facts: self.enum_facts,
            namespace_facts: self.namespace_facts,
            symbols: self.symbols,
            containers: Vec::new(),
            with_regions: Vec::new(),
            captured_names: HashMap::new(),
            code: Vec::new(),
            registers: 0,
            capture_count: 0,
            parameter_count: 0,
            scopes: vec![HashMap::new()],
            predeclared_cells: HashMap::new(),
            capture_plan,
            control_targets: Vec::new(),
            handlers: Vec::new(),
            finally_stack: Vec::new(),
            disposal_stack: Vec::new(),
            top_level: false,
            is_async: flags.is_async,
            is_async_generator: flags.is_async && flags.is_generator,
            goal: self.goal,
            completion: None,
            completion_pool: Vec::new(),
            completion_depth: 0,
            this_capture: None,
            this_cell: None,
            derived_super_guard: None,
            instance_steps: Vec::new(),
            new_target_capture: None,
            parent_constructor_capture: None,
            class_elements: None,
            arguments_source: if is_arrow {
                ArgumentsSource::None
            } else {
                ArgumentsSource::Own
            },
        };
        // Leading capture registers.
        for capture in captures {
            let register = inner.alloc_register(range)?;
            inner.capture_count += 1;
            match capture {
                CaptureKey::Name(name, sites) => {
                    inner.declare(
                        name.clone(),
                        Binding::Cell(register),
                        DeclarationScope::Function,
                    );
                    inner.captured_names.insert(name.clone(), sites.clone());
                }
                CaptureKey::This => inner.this_capture = Some(register),
                CaptureKey::ThisCell => inner.this_cell = Some(register),
                CaptureKey::Arguments => {
                    inner.arguments_source = ArgumentsSource::Captured(register);
                }
                CaptureKey::NewTarget => inner.new_target_capture = Some(register),
                CaptureKey::Parent(_) => inner.parent_constructor_capture = Some(register),
                CaptureKey::ClassElements(_) => inner.class_elements = Some(register),
                CaptureKey::Cell(_) => {}
                CaptureKey::Container(symbol, kind, _) => inner.containers.push(Container {
                    symbol: *symbol,
                    object: register,
                    kind: *kind,
                }),
                CaptureKey::WithObject(site, _) => inner.with_regions.push(WithRegion {
                    site: *site,
                    object: register,
                    scope_depth: 0,
                }),
            }
        }
        // The function name binds to a self-closure register only when needed;
        // named function expressions refer to themselves via the environment
        // in this model, so no extra binding is required here.
        let (parameter_slots, rest_index) = inner.allocate_parameter_slots(parameters, range)?;
        inner.bind_parameters(builder, parameters, range, &parameter_slots, rest_index)?;
        if let LoweredBody::Function(FunctionBody::Block(block))
        | LoweredBody::Arrow(FunctionBody::Block(block)) = body
        {
            inner.hoist_vars(builder, &block.data().statements, range)?;
        } else if let LoweredBody::Block(block) = body {
            inner.hoist_vars(builder, &block.data().statements, range)?;
        }
        match body {
            LoweredBody::Function(FunctionBody::Block(block))
            | LoweredBody::Arrow(FunctionBody::Block(block))
            | LoweredBody::Block(block) => {
                inner.lower_block(builder, block.data())?;
                inner.emit_return_undefined(builder, range)?;
            }
            LoweredBody::Arrow(FunctionBody::Expression(expression)) => {
                let value = inner.lower_expression(builder, expression)?;
                inner.emit(range, Instruction::Return { value })?;
            }
            LoweredBody::Function(FunctionBody::Expression(_)) => {
                return Err(self.missing(range, NodeKind::BlockStatement));
            }
            LoweredBody::Function(FunctionBody::Missing(missing))
            | LoweredBody::Arrow(FunctionBody::Missing(missing)) => {
                return Err(self.missing(range, missing.expected()));
            }
        }
        let name_constant = match name {
            Some(name) => Some(builder.intern(Constant::String(EcmaString::encode(&name)), range)?),
            None => None,
        };
        let assembled = inner.into_function(name_constant, flags);
        builder.fill_function(id, assembled);
        Ok(())
    }
    /// Builds a compiler-generated closure with no source AST: decorator
    /// context accessors, `addInitializer` callbacks, and auto-accessor
    /// getters/setters. Captures then parameters are allocated as leading
    /// registers in the same order ordinary closures use, so a synthetic body
    /// interoperates with every capture-resolution path unchanged. The body
    /// callback receives the explicit parameter register handles and yields
    /// the register holding the return value, so every generated function has
    /// exactly one valid `Return`.
    fn build_synthetic_function(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: Option<String>,
        captures: &[CaptureKey],
        parameter_count: u32,
        emit_body: impl FnOnce(
            &mut FunctionContext,
            &mut ModuleBuilder,
            &[Register],
        ) -> Result<Register, LowerError>,
    ) -> Result<Register, LowerError> {
        let id = builder.reserve_function(range)?;
        let mut inner = FunctionContext {
            file: self.file,
            jsx_plan: self.jsx_plan,
            enum_facts: self.enum_facts,
            namespace_facts: self.namespace_facts,
            symbols: self.symbols,
            containers: Vec::new(),
            with_regions: Vec::new(),
            captured_names: HashMap::new(),
            code: Vec::new(),
            registers: 0,
            capture_count: 0,
            parameter_count: 0,
            scopes: vec![HashMap::new()],
            predeclared_cells: HashMap::new(),
            capture_plan: CapturePlan::default(),
            control_targets: Vec::new(),
            handlers: Vec::new(),
            finally_stack: Vec::new(),
            disposal_stack: Vec::new(),
            top_level: false,
            is_async: false,
            is_async_generator: false,
            goal: self.goal,
            completion: None,
            completion_pool: Vec::new(),
            completion_depth: 0,
            this_capture: None,
            this_cell: None,
            derived_super_guard: None,
            instance_steps: Vec::new(),
            new_target_capture: None,
            parent_constructor_capture: None,
            class_elements: None,
            arguments_source: ArgumentsSource::Own,
        };
        // Leading capture registers, in the same order the materialized
        // captures array pushes them.
        for capture in captures {
            let register = inner.alloc_register(range)?;
            inner.capture_count += 1;
            match capture {
                CaptureKey::Name(name, sites) => {
                    inner.declare(
                        name.clone(),
                        Binding::Cell(register),
                        DeclarationScope::Function,
                    );
                    inner.captured_names.insert(name.clone(), sites.clone());
                }
                CaptureKey::This => inner.this_capture = Some(register),
                CaptureKey::ThisCell => inner.this_cell = Some(register),
                CaptureKey::Arguments => {
                    inner.arguments_source = ArgumentsSource::Captured(register);
                }
                CaptureKey::NewTarget => inner.new_target_capture = Some(register),
                CaptureKey::Parent(_) => inner.parent_constructor_capture = Some(register),
                CaptureKey::ClassElements(_) => inner.class_elements = Some(register),
                CaptureKey::Cell(_) => {}
                CaptureKey::Container(symbol, kind, _) => inner.containers.push(Container {
                    symbol: *symbol,
                    object: register,
                    kind: *kind,
                }),
                CaptureKey::WithObject(site, _) => inner.with_regions.push(WithRegion {
                    site: *site,
                    object: register,
                    scope_depth: 0,
                }),
            }
        }
        // Leading parameter registers immediately after the captures.
        let mut parameters = Vec::with_capacity(parameter_count as usize);
        for _ in 0..parameter_count {
            parameters.push(inner.alloc_register(range)?);
            inner.parameter_count += 1;
        }
        let value = emit_body(&mut inner, builder, &parameters)?;
        inner.emit(range, Instruction::Return { value })?;
        let name_constant = match name {
            Some(name) => Some(builder.intern(Constant::String(EcmaString::encode(&name)), range)?),
            None => None,
        };
        let assembled = inner.into_function(name_constant, FunctionFlags::default());
        builder.fill_function(id, assembled);
        self.materialize_closure(builder, range, id, captures)
    }
    /// Reserves the activation's leading positional parameter registers before
    fn allocate_parameter_slots(
        &mut self,
        parameters: &[ParameterNode],
        range: TextRange,
    ) -> Result<(Vec<Register>, Option<usize>), LowerError> {
        let rest_index = parameters.iter().position(|parameter| {
            matches!(parameter.data().binding.data(), BindingPattern::Rest(_))
        });
        let fixed = rest_index.unwrap_or(parameters.len());
        let mut slots = Vec::with_capacity(fixed);
        for _ in 0..fixed {
            slots.push(self.alloc_register(range)?);
            self.parameter_count += 1;
        }
        Ok((slots, rest_index))
    }
    fn bind_parameters(
        &mut self,
        builder: &mut ModuleBuilder,
        parameters: &[ParameterNode],
        range: TextRange,
        slots: &[Register],
        rest_index: Option<usize>,
    ) -> Result<(), LowerError> {
        let fixed = slots.len();
        let mut undefined_seed = None;
        for (index, parameter) in parameters.iter().enumerate() {
            let mut names = Vec::new();
            collect_pattern_names(self.file, &parameter.data().binding, &mut names);
            for name in names {
                if !self.capture_plan.captures(
                    &name,
                    binding_site(parameter.range()),
                    DeclarationScope::Function,
                ) || self
                    .scopes
                    .first()
                    .is_some_and(|scope| scope.contains_key(&name))
                {
                    continue;
                }
                let seed = if index < fixed
                    && matches!(
                        parameter.data().binding.data(),
                        BindingPattern::Identifier(identifier)
                            if identifier_name(self.file, identifier).as_deref() == Some(&name)
                    ) {
                    slots[index]
                } else if let Some(seed) = undefined_seed {
                    seed
                } else {
                    let seed = self.undefined(builder, parameter.range())?;
                    undefined_seed = Some(seed);
                    seed
                };
                let cell = self.alloc_register(parameter.range())?;
                self.emit(parameter.range(), Instruction::CreateArray { dst: cell })?;
                self.emit(
                    parameter.range(),
                    Instruction::ArrayPush {
                        array: cell,
                        value: seed,
                    },
                )?;
                self.declare(name, Binding::Cell(cell), DeclarationScope::Function);
            }
        }
        for (index, parameter) in parameters.iter().take(fixed).enumerate() {
            let data = parameter.data();
            let slot = slots[index];
            let value = match &data.initializer {
                Some(default) => self.apply_default(builder, parameter.range(), slot, default)?,
                None => slot,
            };
            self.bind_pattern(builder, &data.binding, value, DeclarationScope::Function)?;
        }
        if let Some(rest_index) = rest_index {
            let parameter = &parameters[rest_index];
            let rest_argument = match parameter.data().binding.data() {
                BindingPattern::Rest(rest) => &rest.argument,
                _ => unreachable!("rest_index points at a rest binding"),
            };
            let rest = self.collect_rest_parameter(builder, range, fixed as u32)?;
            self.bind_pattern(builder, rest_argument, rest, DeclarationScope::Function)?;
        }
        Ok(())
    }
    fn collect_rest_parameter(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        fixed: u32,
    ) -> Result<Register, LowerError> {
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::LoadArguments { dst: arguments })?;
        let iterator = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetIterator {
                dst: iterator,
                src: arguments,
                kind: IteratorKind::Sync,
            },
        )?;
        for _ in 0..fixed {
            self.iterator_step_discard(range, iterator)?;
        }
        self.rest_array(builder, range, iterator)
    }
    fn emit_return_undefined(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let value = self.undefined(builder, range)?;
        self.emit(range, Instruction::Return { value })?;
        Ok(())
    }
    fn emit_function_return(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
    ) -> Result<(), LowerError> {
        if self.this_cell.is_none() || self.parent_constructor_capture.is_none() {
            self.emit(range, Instruction::Return { value })?;
            return Ok(());
        }
        self.emit_derived_constructor_return(builder, range, value)
    }
    fn emit_derived_constructor_return(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        value: Register,
    ) -> Result<(), LowerError> {
        let selected = self.alloc_register(range)?;
        let kind = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Unary {
                dst: kind,
                op: UnaryOp::TypeOf,
                operand: value,
            },
        )?;
        let object_kind = self.string_reg(builder, EcmaString::encode("object"), range)?;
        let is_object = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_object,
                op: BinaryOp::StrictEqual,
                left: kind,
                right: object_kind,
            },
        )?;
        let to_function = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: is_object,
                target: Pc::new(0),
            },
        )?;
        let null = self.load_constant(builder, Constant::Null, range)?;
        let is_null = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_null,
                op: BinaryOp::StrictEqual,
                left: value,
                right: null,
            },
        )?;
        let null_is_throw = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_null,
                target: Pc::new(0),
            },
        )?;
        let object_selected = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(to_function, self.next_pc());
        let function_kind = self.string_reg(builder, EcmaString::encode("function"), range)?;
        let is_function = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_function,
                op: BinaryOp::StrictEqual,
                left: kind,
                right: function_kind,
            },
        )?;
        let function_selected = self.emit(
            range,
            Instruction::JumpIfTrue {
                condition: is_function,
                target: Pc::new(0),
            },
        )?;
        let undefined_kind = self.string_reg(builder, EcmaString::encode("undefined"), range)?;
        let is_undefined = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: is_undefined,
                op: BinaryOp::StrictEqual,
                left: kind,
                right: undefined_kind,
            },
        )?;
        let other_primitive = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: is_undefined,
                target: Pc::new(0),
            },
        )?;
        let receiver = self.this_value(builder, range)?;
        self.move_to(range, selected, receiver)?;
        let selected_done = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(object_selected, self.next_pc());
        self.patch_jump(function_selected, self.next_pc());
        self.move_to(range, selected, value)?;
        self.patch_jump(selected_done, self.next_pc());
        let done = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
        self.patch_jump(null_is_throw, self.next_pc());
        self.patch_jump(other_primitive, self.next_pc());
        let arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: arguments })?;
        let this_value = self.undefined(builder, range)?;
        let unreachable = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst: unreachable,
                callee: value,
                this_value,
                arguments,
            },
        )?;
        self.move_to(range, selected, unreachable)?;
        self.patch_jump(done, self.next_pc());
        self.emit(range, Instruction::Return { value: selected })?;
        Ok(())
    }
    fn materialize_closure(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        id: FunctionId,
        captures: &[CaptureKey],
    ) -> Result<Register, LowerError> {
        if captures.len() > MAX_REGISTERS as usize {
            return Err(self.error(range, LowerErrorKind::Capacity(CapacityLimit::Captures)));
        }
        let array = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: array })?;
        for capture in captures {
            let value = self.capture_value(builder, range, capture)?;
            self.emit(range, Instruction::ArrayPush { array, value })?;
        }
        let dst = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateClosure {
                dst,
                function: id,
                captures: array,
            },
        )?;
        Ok(dst)
    }
    fn capture_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        capture: &CaptureKey,
    ) -> Result<Register, LowerError> {
        match capture {
            CaptureKey::Name(name, _) => match self.resolve(name) {
                Some(Binding::Cell(cell)) => Ok(cell),
                Some(Binding::Local(_)) => {
                    panic!("capture plan resolved named capture `{name}` to Local")
                }
                Some(Binding::ConstEnum(_)) => {
                    Err(self.const_enum_operation(range, ConstEnumOperation::Read))
                }
                None => Err(self.error(
                    range,
                    LowerErrorKind::MissingSyntax {
                        expected: NodeKind::Identifier,
                    },
                )),
            },
            CaptureKey::This => self.this_value(builder, range),
            CaptureKey::ThisCell => match self.this_cell {
                Some(cell) => Ok(cell),
                // `compute_captures` requests `ThisCell` only when this
                // context owns a derived `this` cell, so this arm is
                // defensive against a broken capture-plan invariant.
                None => self.this_value(builder, range),
            },
            CaptureKey::Arguments => match self.arguments_value(builder, range)? {
                Some(register) => Ok(register),
                None => self.undefined(builder, range),
            },
            CaptureKey::NewTarget => self.new_target_value(range),
            CaptureKey::Parent(parent) => Ok(*parent),
            CaptureKey::ClassElements(table) => Ok(*table),
            CaptureKey::Cell(cell) => Ok(*cell),
            CaptureKey::Container(_, _, object) | CaptureKey::WithObject(_, object) => Ok(*object),
        }
    }
    fn compute_captures(
        &self,
        parameters: &[ParameterNode],
        body: LoweredBody<'_>,
        is_arrow: bool,
    ) -> Vec<CaptureKey> {
        let mut scanner = FreeVarScanner::new(self.file, self.jsx_plan);
        scanner.scan_function(parameters, body, is_arrow);
        let mut captures = Vec::new();
        for name in &scanner.free {
            if matches!(self.resolve(name), Some(Binding::ConstEnum(_))) {
                continue;
            }
            if self.resolve(name).is_some() {
                captures.push(CaptureKey::Name(
                    name.clone(),
                    self.preceding_with_sites(name),
                ));
            }
        }
        if is_arrow {
            if scanner.uses_this {
                captures.push(if self.this_cell.is_some() {
                    CaptureKey::ThisCell
                } else {
                    CaptureKey::This
                });
            }
            if scanner.uses_arguments {
                captures.push(CaptureKey::Arguments);
            }
            if scanner.uses_new_target {
                captures.push(CaptureKey::NewTarget);
            }
        }
        for container in &self.containers {
            captures.push(CaptureKey::Container(
                container.symbol,
                container.kind,
                container.object,
            ));
        }
        if !scanner.free.is_empty() {
            for region in &self.with_regions {
                captures.push(CaptureKey::WithObject(region.site, region.object));
            }
        }
        captures
    }
    // ------------------------------------------------------------------
    // Classes
    // ------------------------------------------------------------------
    fn lower_class_declaration(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        class: &ClassDeclaration,
        forced_name: Option<&str>,
    ) -> Result<(), LowerError> {
        let name = match forced_name {
            Some(name) => Some(name.to_owned()),
            None => match &class.name {
                Some(identifier) => Some(self.identifier_text(identifier)?),
                None => None,
            },
        };
        self.lower_class_value(builder, range, class, name.as_deref(), None)?;
        Ok(())
    }
    fn lower_member_decorator_inputs(
        &mut self,
        builder: &mut ModuleBuilder,
        class: &ClassDeclaration,
    ) -> Result<HashMap<NodeId, LoweredMemberDecorators>, LowerError> {
        let mut lowered = HashMap::new();
        for member in &class.members {
            let (name, decorators) = match member.data() {
                ClassMember::Method(method) if method.function.body.is_some() => {
                    (&method.name, &method.function.decorators)
                }
                ClassMember::Property(property)
                    if !property.modifiers.is_abstract && !property.modifiers.is_declare =>
                {
                    (&property.name, &property.decorators)
                }
                ClassMember::AutoAccessor(accessor)
                    if !accessor.modifiers.is_abstract && !accessor.modifiers.is_declare =>
                {
                    (&accessor.name, &accessor.decorators)
                }
                _ => continue,
            };
            let mut values = Vec::with_capacity(decorators.len());
            for decorator in decorators {
                values.push(self.lower_expression(builder, &decorator.data().expression)?);
            }
            let key = self.property_key(builder, name)?;
            lowered.insert(
                member.id(),
                LoweredMemberDecorators {
                    key,
                    decorators: values,
                },
            );
        }
        Ok(lowered)
    }
    /// Computes callable-extra prefix steps, source-order field/accessor steps,
    /// and the class-element slot count reserved before constructor lowering.
    fn plan_instance_inits(
        &self,
        class: &ClassDeclaration,
        member_decorators: &HashMap<NodeId, LoweredMemberDecorators>,
    ) -> (Vec<InstanceInit>, u32) {
        let mut steps = Vec::new();
        let mut slots = 0u32;
        for member in &class.members {
            match member.data() {
                ClassMember::Property(property)
                    if !property.modifiers.is_static
                        && !property.modifiers.is_abstract
                        && !property.modifiers.is_declare =>
                {
                    let decorated = member_decorators
                        .get(&member.id())
                        .is_some_and(|d| !d.decorators.is_empty());
                    if decorated {
                        steps.push(InstanceInit::Decorated {
                            slot: slots,
                            initializer: Some(property.initializer.clone()),
                        });
                        slots += 1;
                    } else {
                        steps.push(InstanceInit::PlainField {
                            slot: slots,
                            initializer: property.initializer.clone(),
                        });
                        slots += 1;
                    }
                }
                ClassMember::AutoAccessor(accessor)
                    if !accessor.modifiers.is_static
                        && !accessor.modifiers.is_abstract
                        && !accessor.modifiers.is_declare =>
                {
                    steps.push(InstanceInit::Decorated {
                        slot: slots,
                        initializer: Some(accessor.initializer.clone()),
                    });
                    slots += 1;
                }
                ClassMember::Method(method)
                    if !method.modifiers.is_static
                        && method.function.body.is_some()
                        && member_decorators
                            .get(&member.id())
                            .is_some_and(|d| !d.decorators.is_empty()) =>
                {
                    steps.push(InstanceInit::Decorated {
                        slot: slots,
                        initializer: None,
                    });
                    slots += 1;
                }
                _ => {}
            }
        }
        (steps, slots)
    }
    fn run_extra_initializers(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        receiver: Register,
        queue: Register,
    ) -> Result<(), LowerError> {
        let length = self.get_named(builder, range, queue, "length")?;
        let index = self.alloc_register(range)?;
        let zero = self.load_constant(builder, Constant::Int32(0), range)?;
        self.move_to(range, index, zero)?;
        let one = self.load_constant(builder, Constant::Int32(1), range)?;
        let loop_top = self.next_pc();
        let in_bounds = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: in_bounds,
                op: BinaryOp::LessThan,
                left: index,
                right: length,
            },
        )?;
        let exit = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: in_bounds,
                target: Pc::new(0),
            },
        )?;
        let element_key = self.move_to_index_key(builder, range, index)?;
        let callback = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: callback,
                object: queue,
                key: element_key,
            },
        )?;
        let no_arguments = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: no_arguments })?;
        let result = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Call {
                dst: result,
                callee: callback,
                this_value: receiver,
                arguments: no_arguments,
            },
        )?;
        let next = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: next,
                op: BinaryOp::Add,
                left: index,
                right: one,
            },
        )?;
        self.move_to(range, index, next)?;
        self.emit(range, Instruction::Jump { target: loop_top })?;
        self.patch_jump(exit, self.next_pc());
        Ok(())
    }
    fn move_to_index_key(
        &mut self,
        _builder: &mut ModuleBuilder,
        range: TextRange,
        index: Register,
    ) -> Result<Register, LowerError> {
        let key = self.alloc_register(range)?;
        self.move_to(range, key, index)?;
        Ok(key)
    }
    fn run_initializer_chain(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        receiver: Register,
        chain: Register,
        initial: Register,
    ) -> Result<Register, LowerError> {
        let value = self.alloc_register(range)?;
        self.move_to(range, value, initial)?;
        let length = self.get_named(builder, range, chain, "length")?;
        let index = self.alloc_register(range)?;
        let zero = self.load_constant(builder, Constant::Int32(0), range)?;
        self.move_to(range, index, zero)?;
        let one = self.load_constant(builder, Constant::Int32(1), range)?;
        let loop_top = self.next_pc();
        let in_bounds = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: in_bounds,
                op: BinaryOp::LessThan,
                left: index,
                right: length,
            },
        )?;
        let exit = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: in_bounds,
                target: Pc::new(0),
            },
        )?;
        let element_key = self.move_to_index_key(builder, range, index)?;
        let initializer = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: initializer,
                object: chain,
                key: element_key,
            },
        )?;
        let next_value = self.call_with_registers(range, initializer, receiver, &[value])?;
        self.move_to(range, value, next_value)?;
        let next = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::Binary {
                dst: next,
                op: BinaryOp::Add,
                left: index,
                right: one,
            },
        )?;
        self.move_to(range, index, next)?;
        self.emit(range, Instruction::Jump { target: loop_top })?;
        self.patch_jump(exit, self.next_pc());
        Ok(value)
    }
    fn run_static_init(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        raw_ctor: Register,
        final_class: Register,
        step: &StaticInit,
    ) -> Result<(), LowerError> {
        match step {
            StaticInit::Field {
                property,
                key,
                init_chain,
                extra_inits,
            } => {
                let raw = match &property.initializer {
                    Some(initializer) => self.lower_expression(builder, initializer)?,
                    None => self.undefined(builder, range)?,
                };
                let value =
                    self.run_initializer_chain(builder, range, final_class, *init_chain, raw)?;
                self.emit(
                    range,
                    Instruction::SetProperty {
                        object: raw_ctor,
                        key: *key,
                        value,
                    },
                )?;
                self.run_extra_initializers(builder, range, final_class, *extra_inits)?;
                Ok(())
            }
            StaticInit::AutoAccessor {
                initializer,
                backing_key,
                init_chain,
                extra_inits,
            } => {
                let raw = match initializer {
                    Some(initializer) => self.lower_expression(builder, initializer)?,
                    None => self.undefined(builder, range)?,
                };
                let value =
                    self.run_initializer_chain(builder, range, final_class, *init_chain, raw)?;
                self.emit(
                    range,
                    Instruction::SetProperty {
                        object: raw_ctor,
                        key: *backing_key,
                        value,
                    },
                )?;
                self.run_extra_initializers(builder, range, final_class, *extra_inits)?;
                Ok(())
            }
            StaticInit::MemberExtras { extra_inits } => {
                self.run_extra_initializers(builder, range, final_class, *extra_inits)
            }
            StaticInit::Block(block) => {
                self.push_scope();
                let result = self.lower_block(builder, block.data());
                self.pop_scope();
                result
            }
        }
    }
    fn lower_class_value(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        class: &ClassDeclaration,
        declaration_name: Option<&str>,
        expression_name: Option<(&str, BindingSite)>,
    ) -> Result<Register, LowerError> {
        let class_decorators = class
            .decorators
            .iter()
            .map(|decorator| self.lower_expression(builder, &decorator.data().expression))
            .collect::<Result<Vec<_>, _>>()?;
        let expression_cell = if let Some((name, site)) = expression_name {
            self.push_scope();
            Some(self.predeclare_class_expression_binding(name, range, site)?)
        } else {
            None
        };
        let parent = match &class.extends {
            Some(heritage) => Some(self.lower_expression(builder, &heritage.expression)?),
            None => None,
        };
        let declaration_target = if let Some(name) = declaration_name {
            let site = class
                .name
                .as_ref()
                .map_or(binding_site(range), |identifier| {
                    binding_site(identifier.range())
                });
            self.predeclare_captured_binding(name, range, site, DeclarationScope::Lexical)?;
            let identity = binding_identity(name, site, DeclarationScope::Lexical);
            if self.top_level {
                None
            } else if let Some(cell) = self.predeclared_cells.get(&identity).copied() {
                Some(Binding::Cell(cell))
            } else {
                let home = self.alloc_register(range)?;
                self.declare(
                    name.to_owned(),
                    Binding::Local(home),
                    DeclarationScope::Lexical,
                );
                Some(Binding::Local(home))
            }
        } else {
            None
        };
        let class_body_cell = if let Some(cell) = expression_cell {
            Some(cell)
        } else {
            self.push_scope();
            if let Some(identifier) = &class.name {
                let name = self.identifier_text(identifier)?;
                let cell = self.alloc_register(range)?;
                self.emit(range, Instruction::CreateCell { dst: cell })?;
                self.declare(name, Binding::Cell(cell), DeclarationScope::Lexical);
                Some(cell)
            } else {
                None
            }
        };
        self.create_private_names(builder, range, class)?;
        let constructor = self.find_constructor(class);
        let member_decorators = self.lower_member_decorator_inputs(builder, class)?;
        let (instance_steps, instance_slots) = self.plan_instance_inits(class, &member_decorators);
        let class_elements = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateArray {
                dst: class_elements,
            },
        )?;
        for _ in 0..instance_slots {
            let record = self.alloc_register(range)?;
            self.emit(range, Instruction::CreateArray { dst: record })?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: class_elements,
                    value: record,
                },
            )?;
        }
        let owned_class_name = match &class.name {
            Some(identifier) => Some(self.identifier_text(identifier)?),
            None => None,
        };
        let source_name = owned_class_name.as_deref().or(declaration_name);
        let ctor = self.build_constructor(
            builder,
            range,
            constructor,
            parent,
            &instance_steps,
            if instance_slots == 0 {
                None
            } else {
                Some(class_elements)
            },
            source_name,
        )?;
        let prototype = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst: prototype })?;
        if let Some(parent) = parent {
            let parent_prototype = self.get_named(builder, range, parent, "prototype")?;
            self.emit(
                range,
                Instruction::SetPrototype {
                    object: prototype,
                    prototype: parent_prototype,
                },
            )?;
            self.emit(
                range,
                Instruction::SetPrototype {
                    object: ctor,
                    prototype: parent,
                },
            )?;
        }
        let prototype_key = self.string_reg(builder, EcmaString::encode("prototype"), range)?;
        self.emit(
            range,
            Instruction::DefineDataProperty {
                object: ctor,
                key: prototype_key,
                value: prototype,
            },
        )?;
        let constructor_key = self.string_reg(builder, EcmaString::encode("constructor"), range)?;
        self.emit(
            range,
            Instruction::DefineDataProperty {
                object: prototype,
                key: constructor_key,
                value: ctor,
            },
        )?;
        if let Some(cell) = class_body_cell {
            self.store_cell(builder, cell, ctor, range)?;
        }
        let mut next_instance_slot = 0u32;
        let mut static_inits: Vec<StaticInit> = Vec::new();
        let mut stages = MemberDecorationStages::default();
        for member in &class.members {
            self.lower_class_member(
                builder,
                ctor,
                prototype,
                class_elements,
                member,
                member_decorators.get(&member.id()),
                &mut stages,
                &mut next_instance_slot,
                &mut static_inits,
            )?;
        }
        self.apply_member_decoration_stages(builder, stages)?;
        let class_extra_inits = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateArray {
                dst: class_extra_inits,
            },
        )?;
        let class_state_cell = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateCell {
                dst: class_state_cell,
            },
        )?;
        let open = self.load_constant(builder, Constant::Boolean(false), range)?;
        self.store_cell(builder, class_state_cell, open, range)?;
        let final_class = self.apply_class_decorators(
            builder,
            range,
            &class_decorators,
            ctor,
            source_name,
            class_extra_inits,
            class_state_cell,
        )?;
        let closed = self.load_constant(builder, Constant::Boolean(true), range)?;
        self.store_cell(builder, class_state_cell, closed, range)?;
        if let Some(cell) = class_body_cell {
            self.store_cell(builder, cell, final_class, range)?;
        }
        // Static writes target the raw constructor, while the evaluated class
        // body sees the replacement as `this`. Callable MemberExtras run first
        // on `final_class`, then the remaining static timeline.
        let previous_this = self.this_capture;
        self.this_capture = Some(final_class);
        let mut static_result = Ok(());
        let static_order = static_inits
            .iter()
            .filter(|step| matches!(step, StaticInit::MemberExtras { .. }))
            .chain(
                static_inits
                    .iter()
                    .filter(|step| !matches!(step, StaticInit::MemberExtras { .. })),
            );
        for step in static_order {
            if let Err(error) = self.run_static_init(builder, range, ctor, final_class, step) {
                static_result = Err(error);
                break;
            }
        }
        self.this_capture = previous_this;
        static_result?;
        self.run_extra_initializers(builder, range, final_class, class_extra_inits)?;
        if let Some(name) = declaration_name {
            match declaration_target {
                Some(Binding::Local(home)) => self.move_to(range, home, final_class)?,
                Some(Binding::Cell(cell)) => self.store_cell(builder, cell, final_class, range)?,
                Some(Binding::ConstEnum(_)) => {
                    return Err(self.const_enum_operation(range, ConstEnumOperation::Write));
                }
                None => {
                    debug_assert!(self.top_level);
                    let id = builder.intern(Constant::String(EcmaString::encode(name)), range)?;
                    self.emit(
                        range,
                        Instruction::StoreGlobal {
                            name: id,
                            value: final_class,
                        },
                    )?;
                }
            }
        }
        self.pop_scope();
        Ok(final_class)
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "class decorator application shares the decoration queue and state cell"
    )]
    fn apply_class_decorators(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        decorators: &[Register],
        initial: Register,
        name: Option<&str>,
        queue: Register,
        state_cell: Register,
    ) -> Result<Register, LowerError> {
        if decorators.is_empty() {
            return Ok(initial);
        }
        let current = self.alloc_register(range)?;
        self.move_to(range, current, initial)?;
        let undefined = self.undefined(builder, range)?;
        let context = self.class_decorator_context(builder, range, name, queue, state_cell)?;
        for &decorator in decorators.iter().rev() {
            let returned =
                self.call_with_registers(range, decorator, undefined, &[current, context])?;
            self.accept_replacement_callable(builder, range, returned, current)?;
        }
        Ok(current)
    }
    fn class_decorator_context(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        name: Option<&str>,
        queue: Register,
        state_cell: Register,
    ) -> Result<Register, LowerError> {
        let context = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateObject { dst: context })?;
        let class_kind = self.string_reg(builder, EcmaString::encode("class"), range)?;
        self.set_named_entry(builder, range, context, "kind", class_kind)?;
        let name_value = match name {
            Some(name) => self.string_reg(builder, EcmaString::encode(name), range)?,
            None => self.undefined(builder, range)?,
        };
        self.set_named_entry(builder, range, context, "name", name_value)?;
        let add_initializer = self.build_add_initializer(builder, range, queue, state_cell)?;
        self.set_named_entry(builder, range, context, "addInitializer", add_initializer)?;
        Ok(context)
    }
    fn find_constructor<'c>(
        &self,
        class: &'c ClassDeclaration,
    ) -> Option<&'c crate::syntax::ConstructorDeclaration> {
        class.members.iter().find_map(|member| match member.data() {
            ClassMember::Constructor(constructor) => Some(constructor),
            _ => None,
        })
    }
    /// Creates the class's declared private names as register-local bindings so
    fn create_private_names(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        class: &ClassDeclaration,
    ) -> Result<(), LowerError> {
        let mut seen = HashSet::new();
        for member in &class.members {
            let name = match member.data() {
                ClassMember::Method(method) => &method.name,
                ClassMember::Property(property) => &property.name,
                ClassMember::AutoAccessor(accessor) => &accessor.name,
                _ => continue,
            };
            if let PropertyName::Private(private) = name {
                let text = self.private_text(private)?;
                if !seen.insert(text.clone()) {
                    continue;
                }
                let description =
                    builder.intern(Constant::String(EcmaString::encode(&text)), range)?;
                let value = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::CreatePrivateName {
                        dst: value,
                        description,
                    },
                )?;
                if self.capture_plan.captures(
                    &text,
                    binding_site(private.range()),
                    DeclarationScope::Lexical,
                ) {
                    let cell = self.alloc_register(range)?;
                    self.emit(range, Instruction::CreateArray { dst: cell })?;
                    self.emit(range, Instruction::ArrayPush { array: cell, value })?;
                    self.declare(text, Binding::Cell(cell), DeclarationScope::Lexical);
                } else {
                    self.declare(text, Binding::Local(value), DeclarationScope::Lexical);
                }
            }
        }
        Ok(())
    }
    fn fresh_backing_private_name(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<Register, LowerError> {
        let description =
            builder.intern(Constant::String(EcmaString::encode("#accessor")), range)?;
        let value = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreatePrivateName {
                dst: value,
                description,
            },
        )?;
        Ok(value)
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "constructor lowering needs parent/instance/element stage inputs"
    )]
    fn build_constructor(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        constructor: Option<&crate::syntax::ConstructorDeclaration>,
        parent: Option<Register>,
        instance_steps: &[InstanceInit],
        class_elements: Option<Register>,
        source_name: Option<&str>,
    ) -> Result<Register, LowerError> {
        let (parameters, body_block): (&[ParameterNode], Option<&Block>) = match constructor {
            Some(constructor) => {
                self.reject_decorators(
                    &constructor.decorators,
                    UnsupportedConstruct::ConstructorDecorator,
                )?;
                (&constructor.parameters, Some(constructor.body.data()))
            }
            None => (&[], None),
        };
        self.reject_parameter_decorators(parameters)?;
        let captures = self.compute_constructor_captures(
            parameters,
            body_block,
            instance_steps,
            parent,
            class_elements,
        );
        let id = builder.reserve_function(range)?;
        self.build_constructor_into(
            builder,
            id,
            range,
            parameters,
            body_block,
            &captures,
            parent.is_some(),
            instance_steps,
            source_name,
        )?;
        self.materialize_closure(builder, range, id, &captures)
    }
    fn compute_constructor_captures(
        &self,
        parameters: &[ParameterNode],
        body: Option<&Block>,
        instance_steps: &[InstanceInit],
        parent: Option<Register>,
        class_elements: Option<Register>,
    ) -> Vec<CaptureKey> {
        let mut scanner = FreeVarScanner::new(self.file, self.jsx_plan);
        scanner.preseed_parameters(parameters);
        if let Some(block) = body {
            scanner.preseed_vars(&block.statements);
        }
        scanner.scan_parameter_initializers(parameters);
        if let Some(block) = body {
            for statement in &block.statements {
                scanner.scan_statement(statement);
            }
        }
        scan_instance_init_free_vars(&mut scanner, instance_steps);
        let mut captures = Vec::new();
        for name in &scanner.free {
            if matches!(self.resolve(name), Some(Binding::ConstEnum(_))) {
                continue;
            }
            if self.resolve(name).is_some() {
                captures.push(CaptureKey::Name(
                    name.clone(),
                    self.preceding_with_sites(name),
                ));
            }
        }
        if let Some(parent) = parent {
            captures.push(CaptureKey::Parent(parent));
        }
        if let Some(table) = class_elements {
            captures.push(CaptureKey::ClassElements(table));
        }
        for container in &self.containers {
            captures.push(CaptureKey::Container(
                container.symbol,
                container.kind,
                container.object,
            ));
        }
        if !scanner.free.is_empty() {
            for region in &self.with_regions {
                captures.push(CaptureKey::WithObject(region.site, region.object));
            }
        }
        captures
    }
    fn initialize_instance_fields(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let steps = self.instance_steps.clone();
        if steps.is_empty() {
            return Ok(());
        }
        let table = self.class_elements;
        // Method/getter/setter extras are Decorated { initializer: None }.
        // Drain them as a prefix; field/auto-accessor steps keep source order.
        let ordered = steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    InstanceInit::Decorated {
                        initializer: None,
                        ..
                    }
                )
            })
            .chain(steps.iter().filter(|step| {
                !matches!(
                    step,
                    InstanceInit::Decorated {
                        initializer: None,
                        ..
                    }
                )
            }));
        for step in ordered {
            match step {
                InstanceInit::PlainField { slot, initializer } => {
                    let table = table.expect("plain instance field requires the element table");
                    let record = self.read_table_slot(builder, range, table, *slot)?;
                    let key = self.read_slot_entry(builder, range, record, 0)?;
                    let this_value = self.this_value(builder, range)?;
                    let value = match initializer {
                        Some(initializer) => self.lower_expression(builder, initializer)?,
                        None => self.undefined(builder, range)?,
                    };
                    self.emit(
                        range,
                        Instruction::SetProperty {
                            object: this_value,
                            key,
                            value,
                        },
                    )?;
                }
                InstanceInit::Decorated { slot, initializer } => {
                    let table = table.expect("decorated instance step requires the element table");
                    let record = self.read_table_slot(builder, range, table, *slot)?;
                    let key = self.read_slot_entry(builder, range, record, 0)?;
                    let init_chain = self.read_slot_entry(builder, range, record, 1)?;
                    let extra_inits = self.read_slot_entry(builder, range, record, 2)?;
                    let this_value = self.this_value(builder, range)?;
                    if let Some(initializer) = initializer {
                        let raw = match initializer {
                            Some(expression) => self.lower_expression(builder, expression)?,
                            None => self.undefined(builder, range)?,
                        };
                        let value = self
                            .run_initializer_chain(builder, range, this_value, init_chain, raw)?;
                        self.emit(
                            range,
                            Instruction::SetProperty {
                                object: this_value,
                                key,
                                value,
                            },
                        )?;
                    }
                    self.run_extra_initializers(builder, range, this_value, extra_inits)?;
                }
            }
        }
        Ok(())
    }
    fn read_table_slot(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        table: Register,
        slot: u32,
    ) -> Result<Register, LowerError> {
        let index = self.load_constant(builder, Constant::Int32(slot as i32), range)?;
        let record = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: record,
                object: table,
                key: index,
            },
        )?;
        Ok(record)
    }
    fn read_slot_entry(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        record: Register,
        entry: u32,
    ) -> Result<Register, LowerError> {
        let index = self.load_constant(builder, Constant::Int32(entry as i32), range)?;
        let value = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::GetProperty {
                dst: value,
                object: record,
                key: index,
            },
        )?;
        Ok(value)
    }
    fn guard_derived_super(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        let Some(guard) = self.derived_super_guard else {
            return Ok(());
        };
        let first_call = self.emit(
            range,
            Instruction::JumpIfFalse {
                condition: guard,
                target: Pc::new(0),
            },
        )?;
        let fault = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateCell { dst: fault })?;
        self.cell_value(builder, fault, range)?;
        self.patch_jump(first_call, self.next_pc());
        Ok(())
    }
    fn mark_derived_super_initialized(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        if let Some(guard) = self.derived_super_guard {
            let initialized = self.load_constant(builder, Constant::Boolean(true), range)?;
            self.move_to(range, guard, initialized)?;
        }
        Ok(())
    }
    fn lower_derived_super(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        call: &CallExpression,
    ) -> Result<Register, LowerError> {
        self.guard_derived_super(builder, range)?;
        let (Some(parent), Some(this_cell)) = (self.parent_constructor_capture, self.this_cell)
        else {
            // `super(...)` outside a derived constructor body is rejected by
            // the checker (BAMTS-C025/C026/C027). Keep argument side effects
            // and yield the inert `undefined` value for diagnosed sources.
            self.build_arguments(builder, range, &call.arguments)?;
            return self.undefined(builder, range);
        };
        let arguments = self.build_arguments(builder, range, &call.arguments)?;
        let new_target = self.new_target_value(range)?;
        let result = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::ConstructWithNewTarget {
                dst: result,
                callee: parent,
                new_target,
                arguments,
            },
        )?;
        self.store_cell(builder, this_cell, result, range)?;
        self.mark_derived_super_initialized(builder, range)?;
        self.initialize_instance_fields(builder, range)?;
        Ok(result)
    }
    fn lower_implicit_derived_super(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(), LowerError> {
        self.guard_derived_super(builder, range)?;
        // `compute_constructor_captures` always captures the parent for a
        // derived constructor, and `build_constructor_into` always installs
        // the derived `this` cell and the constructor's own `arguments`
        // before this call; all three bindings are structural invariants.
        let (Some(parent), Some(this_cell), Some(arguments)) = (
            self.parent_constructor_capture,
            self.this_cell,
            self.arguments_value(builder, range)?,
        ) else {
            debug_assert!(
                false,
                "derived constructor lost its parent, this cell, or arguments"
            );
            return Ok(());
        };
        let call_arguments = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::CreateArray {
                dst: call_arguments,
            },
        )?;
        self.emit(
            range,
            Instruction::ArrayExtend {
                array: call_arguments,
                iterable: arguments,
            },
        )?;
        let new_target = self.new_target_value(range)?;
        let result = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::ConstructWithNewTarget {
                dst: result,
                callee: parent,
                new_target,
                arguments: call_arguments,
            },
        )?;
        self.store_cell(builder, this_cell, result, range)?;
        self.mark_derived_super_initialized(builder, range)?;
        self.initialize_instance_fields(builder, range)
    }
    #[allow(clippy::too_many_arguments)]
    fn build_constructor_into(
        &mut self,
        builder: &mut ModuleBuilder,
        id: FunctionId,
        range: TextRange,
        parameters: &[ParameterNode],
        body: Option<&Block>,
        captures: &[CaptureKey],
        derived: bool,
        instance_steps: &[InstanceInit],
        source_name: Option<&str>,
    ) -> Result<(), LowerError> {
        let capture_plan = CapturePlan::for_constructor(
            self.file,
            self.jsx_plan,
            parameters,
            body,
            instance_steps,
        );
        let mut inner = FunctionContext {
            file: self.file,
            jsx_plan: self.jsx_plan,
            enum_facts: self.enum_facts,
            namespace_facts: self.namespace_facts,
            symbols: self.symbols,
            containers: Vec::new(),
            with_regions: Vec::new(),
            captured_names: HashMap::new(),
            code: Vec::new(),
            registers: 0,
            capture_count: 0,
            parameter_count: 0,
            scopes: vec![HashMap::new()],
            predeclared_cells: HashMap::new(),
            capture_plan,
            control_targets: Vec::new(),
            handlers: Vec::new(),
            finally_stack: Vec::new(),
            disposal_stack: Vec::new(),
            top_level: false,
            is_async: false,
            is_async_generator: false,
            goal: self.goal,
            completion: None,
            completion_pool: Vec::new(),
            completion_depth: 0,
            this_capture: None,
            this_cell: None,
            derived_super_guard: None,
            instance_steps: instance_steps.to_vec(),
            new_target_capture: None,
            parent_constructor_capture: None,
            class_elements: None,
            arguments_source: ArgumentsSource::Own,
        };
        for capture in captures {
            let register = inner.alloc_register(range)?;
            inner.capture_count += 1;
            match capture {
                CaptureKey::Name(name, sites) => {
                    inner.declare(
                        name.clone(),
                        Binding::Cell(register),
                        DeclarationScope::Function,
                    );
                    inner.captured_names.insert(name.clone(), sites.clone());
                }
                CaptureKey::Parent(_) => inner.parent_constructor_capture = Some(register),
                CaptureKey::ClassElements(_) => inner.class_elements = Some(register),
                CaptureKey::Cell(_) => {}
                CaptureKey::Container(symbol, kind, _) => inner.containers.push(Container {
                    symbol: *symbol,
                    object: register,
                    kind: *kind,
                }),
                CaptureKey::WithObject(site, _) => inner.with_regions.push(WithRegion {
                    site: *site,
                    object: register,
                    scope_depth: 0,
                }),
                CaptureKey::This
                | CaptureKey::ThisCell
                | CaptureKey::Arguments
                | CaptureKey::NewTarget => {
                    unreachable!("constructors do not capture arrow-only bindings")
                }
            }
        }
        let (parameter_slots, rest_index) = inner.allocate_parameter_slots(parameters, range)?;
        if derived {
            let cell = inner.alloc_register(range)?;
            inner.emit(range, Instruction::CreateCell { dst: cell })?;
            inner.this_cell = Some(cell);
            if body.is_some() {
                let guard = inner.alloc_register(range)?;
                let pending = inner.load_constant(builder, Constant::Boolean(false), range)?;
                inner.move_to(range, guard, pending)?;
                inner.derived_super_guard = Some(guard);
            }
        }
        inner.bind_parameters(builder, parameters, range, &parameter_slots, rest_index)?;
        if let Some(block) = body {
            inner.hoist_vars(builder, &block.statements, range)?;
        }
        if derived {
            if let Some(block) = body {
                inner.lower_block(builder, block)?;
            } else {
                inner.lower_implicit_derived_super(builder, range)?;
            }
        } else {
            inner.initialize_instance_fields(builder, range)?;
            if let Some(block) = body {
                inner.lower_block(builder, block)?;
            }
        }
        if derived {
            let value = inner.undefined(builder, range)?;
            inner.emit_function_return(builder, range, value)?;
        } else {
            inner.emit_return_undefined(builder, range)?;
        }
        let name_constant = match source_name {
            Some(name) => Some(builder.intern(Constant::String(EcmaString::encode(name)), range)?),
            None => None,
        };
        let assembled = inner.into_function(
            name_constant,
            FunctionFlags {
                is_constructable: true,
                ..FunctionFlags::default()
            },
        );
        builder.fill_function(id, assembled);
        Ok(())
    }
    fn new_decoration_queues(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
    ) -> Result<(Register, Register, Register), LowerError> {
        let init_chain = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: init_chain })?;
        let extra_inits = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateArray { dst: extra_inits })?;
        let state_cell = self.alloc_register(range)?;
        self.emit(range, Instruction::CreateCell { dst: state_cell })?;
        let open = self.load_constant(builder, Constant::Boolean(false), range)?;
        self.store_cell(builder, state_cell, open, range)?;
        Ok((init_chain, extra_inits, state_cell))
    }
    fn close_decoration(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        state_cell: Register,
    ) -> Result<(), LowerError> {
        let closed = self.load_constant(builder, Constant::Boolean(true), range)?;
        self.store_cell(builder, state_cell, closed, range)
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "instance slot fill writes key and init chain registers into the table"
    )]
    fn fill_instance_slot(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        table: Register,
        slot: u32,
        key: Register,
        init_chain: Register,
        extra_inits: Register,
    ) -> Result<(), LowerError> {
        let record = self.read_table_slot(builder, range, table, slot)?;
        for value in [key, init_chain, extra_inits] {
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: record,
                    value,
                },
            )?;
        }
        Ok(())
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "method decorator application shares target/key/slot/context registers"
    )]
    fn apply_method_decorators(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        target: Register,
        key: Register,
        slot: DescriptorSlot,
        decorators: &[Register],
        context: Register,
    ) -> Result<(), LowerError> {
        let current = self.alloc_register(range)?;
        self.emit(
            range,
            Instruction::LoadOwnDescriptorSlot {
                dst: current,
                object: target,
                key,
                slot,
            },
        )?;
        let undefined = self.undefined(builder, range)?;
        for &decorator in decorators.iter().rev() {
            let returned =
                self.call_with_registers(range, decorator, undefined, &[current, context])?;
            self.accept_replacement_callable(builder, range, returned, current)?;
        }
        self.emit(
            range,
            Instruction::DefineOwnDescriptorSlot {
                object: target,
                key,
                src: current,
                slot,
            },
        )?;
        Ok(())
    }
    fn apply_field_decorators(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        decorators: &[Register],
        context: Register,
        init_chain: Register,
    ) -> Result<(), LowerError> {
        // Apply inner-to-outer, but TypeScript prepends each returned initializer, so
        // the runtime chain must run outer-to-inner. Collect during application, then
        // push onto `init_chain` in reverse collection order.
        let undefined = self.undefined(builder, range)?;
        let mut collected_inits = Vec::new();
        for &decorator in decorators.iter().rev() {
            let returned =
                self.call_with_registers(range, decorator, undefined, &[undefined, context])?;
            let collected = self.alloc_register(range)?;
            let accepted = self.collect_optional_callable(builder, range, returned, collected)?;
            collected_inits.push((accepted, collected));
        }
        for &(accepted, collected) in collected_inits.iter().rev() {
            let skip = self.emit(
                range,
                Instruction::JumpIfFalse {
                    condition: accepted,
                    target: Pc::new(0),
                },
            )?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: init_chain,
                    value: collected,
                },
            )?;
            self.patch_jump(skip, self.next_pc());
        }
        Ok(())
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "auto-accessor decorator application threads get/set/init-chain registers"
    )]
    fn apply_auto_accessor_decorators(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        decorators: &[Register],
        context: Register,
        initial_get: Register,
        initial_set: Register,
        init_chain: Register,
    ) -> Result<(Register, Register), LowerError> {
        // Same outer-then-inner init composition as fields: collect during
        // inner-to-outer application, then append to the runtime chain in reverse.
        let current_get = self.alloc_register(range)?;
        self.move_to(range, current_get, initial_get)?;
        let current_set = self.alloc_register(range)?;
        self.move_to(range, current_set, initial_set)?;
        let undefined = self.undefined(builder, range)?;
        let object_type = self.string_reg(builder, EcmaString::encode("object"), range)?;
        let mut collected_inits = Vec::new();
        for &decorator in decorators.iter().rev() {
            let collected = self.alloc_register(range)?;
            let accepted_init = self.alloc_register(range)?;
            self.move_to(range, collected, undefined)?;
            let flag_false = self.load_constant(builder, Constant::Boolean(false), range)?;
            self.move_to(range, accepted_init, flag_false)?;
            collected_inits.push((accepted_init, collected));
            let pair = self.alloc_register(range)?;
            self.emit(range, Instruction::CreateObject { dst: pair })?;
            self.set_named_entry(builder, range, pair, "get", current_get)?;
            self.set_named_entry(builder, range, pair, "set", current_set)?;
            let returned =
                self.call_with_registers(range, decorator, undefined, &[pair, context])?;
            let is_undefined = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Binary {
                    dst: is_undefined,
                    op: BinaryOp::StrictEqual,
                    left: returned,
                    right: undefined,
                },
            )?;
            let inspect = self.emit(
                range,
                Instruction::JumpIfFalse {
                    condition: is_undefined,
                    target: Pc::new(0),
                },
            )?;
            let keep = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
            self.patch_jump(inspect, self.next_pc());
            let returned_type = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Unary {
                    dst: returned_type,
                    op: UnaryOp::TypeOf,
                    operand: returned,
                },
            )?;
            let is_object = self.alloc_register(range)?;
            self.emit(
                range,
                Instruction::Binary {
                    dst: is_object,
                    op: BinaryOp::StrictEqual,
                    left: returned_type,
                    right: object_type,
                },
            )?;
            let accepted_object = self.emit(
                range,
                Instruction::JumpIfTrue {
                    condition: is_object,
                    target: Pc::new(0),
                },
            )?;
            self.raise_type_error(builder, range)?;
            let errored = self.emit(range, Instruction::Jump { target: Pc::new(0) })?;
            self.patch_jump(accepted_object, self.next_pc());
            let new_get = self.get_named(builder, range, returned, "get")?;
            self.accept_replacement_callable(builder, range, new_get, current_get)?;
            let new_set = self.get_named(builder, range, returned, "set")?;
            self.accept_replacement_callable(builder, range, new_set, current_set)?;
            let init = self.get_named(builder, range, returned, "init")?;
            let accepted = self.collect_optional_callable(builder, range, init, collected)?;
            self.move_to(range, accepted_init, accepted)?;
            let after = self.next_pc();
            self.patch_jump(keep, after);
            self.patch_jump(errored, after);
        }
        for &(accepted, collected) in collected_inits.iter().rev() {
            let skip = self.emit(
                range,
                Instruction::JumpIfFalse {
                    condition: accepted,
                    target: Pc::new(0),
                },
            )?;
            self.emit(
                range,
                Instruction::ArrayPush {
                    array: init_chain,
                    value: collected,
                },
            )?;
            self.patch_jump(skip, self.next_pc());
        }
        Ok((current_get, current_set))
    }
    fn build_auto_accessor_pair(
        &mut self,
        builder: &mut ModuleBuilder,
        range: TextRange,
        backing_key: Register,
    ) -> Result<(Register, Register), LowerError> {
        // Installed accessors receive their object through `this`.  This is
        // deliberately separate from `context.access`, whose closures take it
        // as their first explicit argument.
        let captures = [CaptureKey::Parent(backing_key)];
        let get = self.build_synthetic_function(
            builder,
            range,
            None,
            &captures,
            0,
            move |inner, builder, _parameters| {
                let key = Register::new(0);
                let object = inner.this_value(builder, range)?;
                let dst = inner.alloc_register(range)?;
                inner.emit(range, Instruction::GetProperty { dst, object, key })?;
                Ok(dst)
            },
        )?;
        let set = self.build_synthetic_function(
            builder,
            range,
            None,
            &captures,
            1,
            move |inner, builder, parameters| {
                let key = Register::new(0);
                let value = parameters[0];
                let object = inner.this_value(builder, range)?;
                inner.emit(range, Instruction::SetProperty { object, key, value })?;
                inner.undefined(builder, range)
            },
        )?;
        Ok((get, set))
    }
    fn apply_deferred_member_decoration(
        &mut self,
        builder: &mut ModuleBuilder,
        decoration: DeferredMemberDecoration,
    ) -> Result<(), LowerError> {
        match decoration {
            DeferredMemberDecoration::Method {
                range,
                target,
                key,
                slot,
                decorators,
                context,
                state_cell,
            } => {
                self.apply_method_decorators(
                    builder,
                    range,
                    target,
                    key,
                    slot,
                    &decorators,
                    context,
                )?;
                self.close_decoration(builder, range, state_cell)
            }
            DeferredMemberDecoration::Field {
                range,
                decorators,
                context,
                init_chain,
                state_cell,
            } => {
                self.apply_field_decorators(builder, range, &decorators, context, init_chain)?;
                self.close_decoration(builder, range, state_cell)
            }
            DeferredMemberDecoration::AutoAccessor {
                range,
                target,
                key,
                decorators,
                context,
                init_chain,
                state_cell,
            } => {
                let initial_get = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::LoadOwnDescriptorSlot {
                        dst: initial_get,
                        object: target,
                        key,
                        slot: DescriptorSlot::Getter,
                    },
                )?;
                let initial_set = self.alloc_register(range)?;
                self.emit(
                    range,
                    Instruction::LoadOwnDescriptorSlot {
                        dst: initial_set,
                        object: target,
                        key,
                        slot: DescriptorSlot::Setter,
                    },
                )?;
                let (final_get, final_set) = self.apply_auto_accessor_decorators(
                    builder,
                    range,
                    &decorators,
                    context,
                    initial_get,
                    initial_set,
                    init_chain,
                )?;
                self.emit(
                    range,
                    Instruction::DefineOwnDescriptorSlot {
                        object: target,
                        key,
                        src: final_get,
                        slot: DescriptorSlot::Getter,
                    },
                )?;
                self.emit(
                    range,
                    Instruction::DefineOwnDescriptorSlot {
                        object: target,
                        key,
                        src: final_set,
                        slot: DescriptorSlot::Setter,
                    },
                )?;
                self.close_decoration(builder, range, state_cell)
            }
        }
    }
    fn apply_member_decoration_stages(
        &mut self,
        builder: &mut ModuleBuilder,
        mut stages: MemberDecorationStages,
    ) -> Result<(), LowerError> {
        for decoration in stages.static_callables.drain(..) {
            self.apply_deferred_member_decoration(builder, decoration)?;
        }
        for decoration in stages.instance_callables.drain(..) {
            self.apply_deferred_member_decoration(builder, decoration)?;
        }
        for decoration in stages.static_fields.drain(..) {
            self.apply_deferred_member_decoration(builder, decoration)?;
        }
        for decoration in stages.instance_fields.drain(..) {
            self.apply_deferred_member_decoration(builder, decoration)?;
        }
        Ok(())
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "class member lowering shares ctor/prototype/decoration stage state"
    )]
    fn lower_class_member(
        &mut self,
        builder: &mut ModuleBuilder,
        ctor: Register,
        prototype: Register,
        class_elements: Register,
        member: &crate::syntax::ClassMemberNode,
        decorators: Option<&LoweredMemberDecorators>,
        stages: &mut MemberDecorationStages,
        next_instance_slot: &mut u32,
        static_inits: &mut Vec<StaticInit>,
    ) -> Result<(), LowerError> {
        let range = member.range();
        match member.data() {
            ClassMember::Constructor(_) => Ok(()),
            ClassMember::Method(method) => {
                if method.function.body.is_none() {
                    return Ok(());
                }
                let is_static = method.modifiers.is_static;
                let target = if is_static { ctor } else { prototype };
                let key = match decorators {
                    Some(lowered) => lowered.key,
                    None => self.property_key(builder, &method.name)?,
                };
                let value = self.build_function_value(builder, range, None, &method.function)?;
                self.install_property(builder, range, target, key, value, method.modifier)?;
                let Some(lowered) = decorators.filter(|d| !d.decorators.is_empty()) else {
                    return Ok(());
                };
                let (kind, slot) = match method.modifier {
                    PropertyModifier::None => (MemberDecorationKind::Method, DescriptorSlot::Value),
                    PropertyModifier::Get => (MemberDecorationKind::Getter, DescriptorSlot::Getter),
                    PropertyModifier::Set => (MemberDecorationKind::Setter, DescriptorSlot::Setter),
                };
                let (init_chain, extra_inits, state_cell) =
                    self.new_decoration_queues(builder, range)?;
                let context = self.build_member_context(
                    builder,
                    range,
                    &method.name,
                    key,
                    is_static,
                    kind,
                    extra_inits,
                    state_cell,
                )?;
                let decoration = DeferredMemberDecoration::Method {
                    range,
                    target,
                    key,
                    slot,
                    decorators: lowered.decorators.clone(),
                    context,
                    state_cell,
                };
                if is_static {
                    stages.static_callables.push(decoration);
                    static_inits.push(StaticInit::MemberExtras { extra_inits });
                } else {
                    stages.instance_callables.push(decoration);
                    let slot = *next_instance_slot;
                    *next_instance_slot += 1;
                    self.fill_instance_slot(
                        builder,
                        range,
                        class_elements,
                        slot,
                        key,
                        init_chain,
                        extra_inits,
                    )?;
                }
                Ok(())
            }
            ClassMember::Property(property) => {
                if property.modifiers.is_abstract || property.modifiers.is_declare {
                    return Ok(());
                }
                let is_static = property.modifiers.is_static;
                let Some(lowered) = decorators else {
                    return Ok(());
                };
                if lowered.decorators.is_empty() {
                    if is_static {
                        let (init_chain, extra_inits, _) =
                            self.new_decoration_queues(builder, range)?;
                        static_inits.push(StaticInit::Field {
                            property: Box::new(property.clone()),
                            key: lowered.key,
                            init_chain,
                            extra_inits,
                        });
                    } else {
                        let slot = *next_instance_slot;
                        *next_instance_slot += 1;
                        let record = self.read_table_slot(builder, range, class_elements, slot)?;
                        self.emit(
                            range,
                            Instruction::ArrayPush {
                                array: record,
                                value: lowered.key,
                            },
                        )?;
                    }
                    return Ok(());
                }
                let (init_chain, extra_inits, state_cell) =
                    self.new_decoration_queues(builder, range)?;
                let context = self.build_member_context(
                    builder,
                    range,
                    &property.name,
                    lowered.key,
                    is_static,
                    MemberDecorationKind::Field,
                    extra_inits,
                    state_cell,
                )?;
                let decoration = DeferredMemberDecoration::Field {
                    range,
                    decorators: lowered.decorators.clone(),
                    context,
                    init_chain,
                    state_cell,
                };
                if is_static {
                    stages.static_fields.push(decoration);
                    static_inits.push(StaticInit::Field {
                        property: Box::new(property.clone()),
                        key: lowered.key,
                        init_chain,
                        extra_inits,
                    });
                } else {
                    stages.instance_fields.push(decoration);
                    let slot = *next_instance_slot;
                    *next_instance_slot += 1;
                    self.fill_instance_slot(
                        builder,
                        range,
                        class_elements,
                        slot,
                        lowered.key,
                        init_chain,
                        extra_inits,
                    )?;
                }
                Ok(())
            }
            ClassMember::AutoAccessor(accessor) => {
                if accessor.modifiers.is_abstract || accessor.modifiers.is_declare {
                    return Ok(());
                }
                let is_static = accessor.modifiers.is_static;
                let target = if is_static { ctor } else { prototype };
                let backing_key = self.fresh_backing_private_name(builder, range)?;
                let (generated_get, generated_set) =
                    self.build_auto_accessor_pair(builder, range, backing_key)?;
                let public_key = match decorators {
                    Some(lowered) => lowered.key,
                    None => self.property_key(builder, &accessor.name)?,
                };
                self.emit(
                    range,
                    Instruction::DefineAccessor {
                        object: target,
                        key: public_key,
                        accessor: generated_get,
                        kind: AccessorKind::Getter,
                    },
                )?;
                self.emit(
                    range,
                    Instruction::DefineAccessor {
                        object: target,
                        key: public_key,
                        accessor: generated_set,
                        kind: AccessorKind::Setter,
                    },
                )?;
                let Some(lowered) = decorators.filter(|d| !d.decorators.is_empty()) else {
                    let (init_chain, extra_inits, _) =
                        self.new_decoration_queues(builder, range)?;
                    if is_static {
                        static_inits.push(StaticInit::AutoAccessor {
                            initializer: accessor.initializer.clone(),
                            backing_key,
                            init_chain,
                            extra_inits,
                        });
                    } else {
                        let slot = *next_instance_slot;
                        *next_instance_slot += 1;
                        self.fill_instance_slot(
                            builder,
                            range,
                            class_elements,
                            slot,
                            backing_key,
                            init_chain,
                            extra_inits,
                        )?;
                    }
                    return Ok(());
                };
                let (init_chain, extra_inits, state_cell) =
                    self.new_decoration_queues(builder, range)?;
                let context = self.build_member_context(
                    builder,
                    range,
                    &accessor.name,
                    public_key,
                    is_static,
                    MemberDecorationKind::AutoAccessor,
                    extra_inits,
                    state_cell,
                )?;
                let decoration = DeferredMemberDecoration::AutoAccessor {
                    range,
                    target,
                    key: public_key,
                    decorators: lowered.decorators.clone(),
                    context,
                    init_chain,
                    state_cell,
                };
                if is_static {
                    stages.static_callables.push(decoration);
                    static_inits.push(StaticInit::AutoAccessor {
                        initializer: accessor.initializer.clone(),
                        backing_key,
                        init_chain,
                        extra_inits,
                    });
                } else {
                    stages.instance_callables.push(decoration);
                    let slot = *next_instance_slot;
                    *next_instance_slot += 1;
                    self.fill_instance_slot(
                        builder,
                        range,
                        class_elements,
                        slot,
                        backing_key,
                        init_chain,
                        extra_inits,
                    )?;
                }
                Ok(())
            }
            ClassMember::StaticBlock(block) => {
                static_inits.push(StaticInit::Block(block.clone()));
                Ok(())
            }
            ClassMember::IndexSignature(_) => Ok(()),
            ClassMember::Missing(missing) => Err(self.missing(range, missing.expected())),
        }
    }
}
#[derive(Clone, Copy)]
enum LoweredBody<'a> {
    Function(&'a FunctionBody),
    Arrow(&'a FunctionBody),
    Block(&'a BlockNode),
}
#[derive(Clone)]
struct ScannedBinding {
    identity: BindingIdentity,
    owner_depth: u32,
}
struct FreeVarScanner<'a> {
    file: &'a SourceFile,
    jsx_plan: Option<&'a JsxSourceDesugarPlan>,
    bound: Vec<HashMap<String, ScannedBinding>>,
    function_roots: Vec<usize>,
    free: BTreeSet<String>,
    captured: HashSet<BindingIdentity>,
    runtime_cells: HashSet<BindingIdentity>,
    initialized: HashSet<BindingIdentity>,
    uses_this: bool,
    uses_arguments: bool,
    uses_new_target: bool,
    fn_boundary: u32,
    function_depth: u32,
}
impl CapturePlan {
    fn for_statements(
        file: &SourceFile,
        jsx_plan: Option<&JsxSourceDesugarPlan>,
        statements: &[Stmt],
    ) -> Self {
        let mut scanner = FreeVarScanner::new(file, jsx_plan);
        scanner.preseed_vars(statements);
        scanner.predeclare_immediate(statements, false);
        for statement in statements {
            scanner.scan_statement(statement);
        }
        Self {
            captured: scanner.captured,
            runtime_cells: scanner.runtime_cells,
        }
    }
    fn for_function(
        file: &SourceFile,
        jsx_plan: Option<&JsxSourceDesugarPlan>,
        parameters: &[ParameterNode],
        body: LoweredBody<'_>,
    ) -> Self {
        let mut scanner = FreeVarScanner::new(file, jsx_plan);
        scanner.scan_function(parameters, body, false);
        Self {
            captured: scanner.captured,
            runtime_cells: scanner.runtime_cells,
        }
    }
    fn for_constructor(
        file: &SourceFile,
        jsx_plan: Option<&JsxSourceDesugarPlan>,
        parameters: &[ParameterNode],
        body: Option<&Block>,
        instance_steps: &[InstanceInit],
    ) -> Self {
        let mut scanner = FreeVarScanner::new(file, jsx_plan);
        scanner.preseed_parameters(parameters);
        if let Some(block) = body {
            scanner.preseed_vars(&block.statements);
            scanner.predeclare_immediate(&block.statements, false);
        }
        scanner.scan_parameter_initializers(parameters);
        if let Some(block) = body {
            for statement in &block.statements {
                scanner.scan_statement(statement);
            }
        }
        scan_instance_init_free_vars(&mut scanner, instance_steps);
        Self {
            captured: scanner.captured,
            runtime_cells: scanner.runtime_cells,
        }
    }
}
impl<'a> FreeVarScanner<'a> {
    fn new(file: &'a SourceFile, jsx_plan: Option<&'a JsxSourceDesugarPlan>) -> Self {
        Self {
            file,
            jsx_plan,
            bound: vec![HashMap::new()],
            function_roots: vec![0],
            free: BTreeSet::new(),
            captured: HashSet::new(),
            runtime_cells: HashSet::new(),
            initialized: HashSet::new(),
            uses_this: false,
            uses_arguments: false,
            uses_new_target: false,
            fn_boundary: 0,
            function_depth: 0,
        }
    }
    fn scan_function(
        &mut self,
        parameters: &[ParameterNode],
        body: LoweredBody<'_>,
        _is_arrow: bool,
    ) {
        self.preseed_parameters(parameters);
        if let LoweredBody::Function(FunctionBody::Block(block))
        | LoweredBody::Arrow(FunctionBody::Block(block))
        | LoweredBody::Block(block) = body
        {
            self.preseed_vars(&block.data().statements);
            self.predeclare_immediate(&block.data().statements, false);
        }
        self.scan_parameter_initializers(parameters);
        match body {
            LoweredBody::Function(FunctionBody::Block(block))
            | LoweredBody::Arrow(FunctionBody::Block(block))
            | LoweredBody::Block(block) => {
                for statement in &block.data().statements {
                    self.scan_statement(statement);
                }
            }
            LoweredBody::Arrow(FunctionBody::Expression(expression))
            | LoweredBody::Function(FunctionBody::Expression(expression)) => {
                self.scan_expression(expression);
            }
            _ => {}
        }
    }
    fn push(&mut self) {
        self.bound.push(HashMap::new());
    }
    fn pop(&mut self) {
        self.bound.pop();
    }
    fn bind_function(&mut self, name: String) {
        let root = *self
            .function_roots
            .last()
            .expect("scanner always has a function root");
        self.bound[root]
            .entry(name.clone())
            .or_insert(ScannedBinding {
                identity: BindingIdentity::Function(name),
                owner_depth: self.function_depth,
            });
    }
    fn bind_lexical(&mut self, name: String, range: TextRange) {
        if let Some(scope) = self.bound.last_mut() {
            scope.insert(
                name,
                ScannedBinding {
                    identity: BindingIdentity::Lexical(binding_site(range)),
                    owner_depth: self.function_depth,
                },
            );
        }
    }
    fn resolve_binding(&self, name: &str) -> Option<&ScannedBinding> {
        self.bound.iter().rev().find_map(|scope| scope.get(name))
    }
    fn scan_property_name(&mut self, name: &PropertyName) {
        match name {
            PropertyName::Computed(expression) => self.scan_expression(expression),
            PropertyName::Private(private) => {
                if let Some(text) = private_name(self.file, private) {
                    self.use_name(&text);
                }
            }
            _ => {}
        }
    }
    fn use_name(&mut self, name: &str) {
        if name == "arguments" {
            if self.fn_boundary == 0 {
                self.uses_arguments = true;
            }
            return;
        }
        if let Some(binding) = self.resolve_binding(name).cloned() {
            if binding.owner_depth == 0 && !self.initialized.contains(&binding.identity) {
                self.runtime_cells.insert(binding.identity.clone());
            }
            if self.function_depth > binding.owner_depth && binding.owner_depth == 0 {
                self.captured.insert(binding.identity);
            }
        } else {
            self.free.insert(name.to_owned());
        }
    }
    fn predeclare_immediate(&mut self, statements: &[Stmt], switch_scope: bool) {
        for declaration in collect_immediate_declarations(self.file, statements) {
            match declaration.kind {
                ImmediateDeclarationKind::Function(_) => {
                    let identity = BindingIdentity::Function(declaration.name.clone());
                    self.bind_function(declaration.name);
                    self.initialized.insert(identity);
                }
                ImmediateDeclarationKind::Lexical => {
                    let identity = BindingIdentity::Lexical(declaration.site);
                    self.bind_lexical(declaration.name, declaration.range);
                    if switch_scope {
                        self.runtime_cells.insert(identity);
                    }
                }
            }
        }
    }
    fn initialize_pattern(&mut self, pattern: &Pattern, declaration_scope: DeclarationScope) {
        let mut names = Vec::new();
        collect_pattern_names(self.file, pattern, &mut names);
        for name in names {
            if let Some(binding) = self.resolve_binding(&name)
                && (matches!(declaration_scope, DeclarationScope::Function)
                    || binding.owner_depth == self.function_depth)
            {
                self.initialized.insert(binding.identity.clone());
            }
        }
    }
    fn preseed_parameters(&mut self, parameters: &[ParameterNode]) {
        for parameter in parameters {
            let mut names = Vec::new();
            collect_pattern_names(self.file, &parameter.data().binding, &mut names);
            for name in names {
                self.bind_function(name.clone());
                self.initialized.insert(BindingIdentity::Function(name));
            }
        }
    }
    fn preseed_vars(&mut self, statements: &[Stmt]) {
        let mut names = Vec::new();
        collect_var_names(self.file, statements, &mut names);
        for name in names {
            self.bind_function(name.clone());
            self.initialized.insert(BindingIdentity::Function(name));
        }
    }
    fn scan_parameter_initializers(&mut self, parameters: &[ParameterNode]) {
        for parameter in parameters {
            let data = parameter.data();
            if let Some(initializer) = &data.initializer {
                self.scan_expression(initializer);
            }
            self.scan_pattern_effects(&data.binding);
        }
    }
    fn scan_pattern_effects(&mut self, pattern: &Pattern) {
        match pattern.data() {
            BindingPattern::Identifier(_) | BindingPattern::Missing(_) => {}
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    if let PropertyName::Computed(expression) = &property.name {
                        self.scan_expression(expression);
                    }
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                    self.scan_pattern_effects(&property.binding);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(inner) = element {
                        self.scan_pattern_effects(inner);
                    }
                }
            }
            BindingPattern::Rest(rest) => self.scan_pattern_effects(&rest.argument),
            BindingPattern::Assignment(assignment) => {
                self.scan_expression(&assignment.right);
                self.scan_pattern_effects(&assignment.left);
            }
        }
    }
    fn bind_pattern(&mut self, pattern: &Pattern, declaration_scope: DeclarationScope) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                if let Some(text) = identifier_name(self.file, identifier) {
                    match declaration_scope {
                        DeclarationScope::Function => self.bind_function(text),
                        DeclarationScope::Lexical | DeclarationScope::Iteration => {
                            self.bind_lexical(text, identifier.range());
                        }
                    }
                }
            }
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.bind_pattern(&property.binding, declaration_scope);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(inner) = element {
                        self.bind_pattern(inner, declaration_scope);
                    }
                }
            }
            BindingPattern::Rest(rest) => self.bind_pattern(&rest.argument, declaration_scope),
            BindingPattern::Assignment(assignment) => {
                self.bind_pattern(&assignment.left, declaration_scope);
            }
            BindingPattern::Missing(_) => {}
        }
    }
    fn scan_statement(&mut self, statement: &Stmt) {
        match statement.data() {
            Statement::Variable(declaration) => {
                let scope = match declaration.kind {
                    VariableKind::Var => DeclarationScope::Function,
                    _ => DeclarationScope::Lexical,
                };
                for declarator in &declaration.declarations {
                    if let Some(initializer) = &declarator.data().initializer {
                        self.scan_expression(initializer);
                    }
                    self.scan_pattern_effects(&declarator.data().binding);
                    self.initialize_pattern(&declarator.data().binding, scope);
                }
            }
            Statement::Function(declaration) => {
                self.scan_function_like(&declaration.function);
            }
            Statement::Class(class) => {
                self.scan_class_heritage(class);
                if let Some(name) = &class.name
                    && let Some(text) = identifier_name(self.file, name)
                    && let Some(binding) = self.resolve_binding(&text)
                {
                    self.initialized.insert(binding.identity.clone());
                }
                self.scan_class(class);
            }
            Statement::Expression(expression) => self.scan_expression(&expression.expression),
            Statement::Return(statement) => {
                if let Some(argument) = &statement.argument {
                    self.scan_expression(argument);
                }
            }
            Statement::Throw(statement) => self.scan_expression(&statement.argument),
            Statement::If(statement) => {
                self.scan_expression(&statement.test);
                self.scan_statement(&statement.consequent);
                if let Some(alternate) = &statement.alternate {
                    self.scan_statement(alternate);
                }
            }
            Statement::Block(block) => {
                self.push();
                self.predeclare_immediate(&block.data().statements, false);
                for statement in &block.data().statements {
                    self.scan_statement(statement);
                }
                self.pop();
            }
            Statement::While(statement) => {
                self.scan_expression(&statement.test);
                self.scan_statement(&statement.body);
            }
            Statement::DoWhile(statement) => {
                self.scan_statement(&statement.body);
                self.scan_expression(&statement.test);
            }
            Statement::For(statement) => {
                self.push();
                if let Some(initializer) = &statement.initializer {
                    match initializer {
                        ForInitializer::Variable(declaration) => {
                            let scope = match declaration.kind {
                                VariableKind::Var => DeclarationScope::Function,
                                _ => DeclarationScope::Lexical,
                            };
                            for declarator in &declaration.declarations {
                                self.bind_pattern(&declarator.data().binding, scope);
                                if let Some(init) = &declarator.data().initializer {
                                    self.scan_expression(init);
                                }
                                self.scan_pattern_effects(&declarator.data().binding);
                                self.initialize_pattern(&declarator.data().binding, scope);
                            }
                        }
                        ForInitializer::Expression(expression) => self.scan_expression(expression),
                    }
                }
                if let Some(test) = &statement.test {
                    self.scan_expression(test);
                }
                if let Some(update) = &statement.update {
                    self.scan_expression(update);
                }
                self.scan_statement(&statement.body);
                self.pop();
            }
            Statement::ForIn(statement) => {
                self.push();
                self.scan_expression(&statement.object);
                self.scan_for_binding(&statement.binding);
                self.scan_statement(&statement.body);
                self.pop();
            }
            Statement::ForOf(statement) => {
                self.push();
                self.scan_expression(&statement.iterable);
                self.scan_for_binding(&statement.binding);
                self.scan_statement(&statement.body);
                self.pop();
            }
            Statement::Switch(statement) => {
                self.scan_expression(&statement.discriminant);
                self.push();
                let statements = statement
                    .cases
                    .iter()
                    .flat_map(|case| case.data().consequent.iter().cloned())
                    .collect::<Vec<_>>();
                self.predeclare_immediate(&statements, true);
                for case in &statement.cases {
                    if let Some(test) = &case.data().test {
                        self.scan_expression(test);
                    }
                    for statement in &case.data().consequent {
                        self.scan_statement(statement);
                    }
                }
                self.pop();
            }
            Statement::Try(statement) => {
                self.push();
                self.predeclare_immediate(&statement.block.data().statements, false);
                for statement in &statement.block.data().statements {
                    self.scan_statement(statement);
                }
                self.pop();
                if let Some(handler) = &statement.handler {
                    self.push();
                    if let Some(binding) = &handler.data().binding {
                        self.bind_pattern(binding, DeclarationScope::Lexical);
                        self.initialize_pattern(binding, DeclarationScope::Lexical);
                    }
                    self.predeclare_immediate(&handler.data().body.data().statements, false);
                    for statement in &handler.data().body.data().statements {
                        self.scan_statement(statement);
                    }
                    self.pop();
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.push();
                    self.predeclare_immediate(&finalizer.data().statements, false);
                    for statement in &finalizer.data().statements {
                        self.scan_statement(statement);
                    }
                    self.pop();
                }
            }
            Statement::Labeled(statement) => self.scan_statement(&statement.body),
            Statement::With(statement) => {
                self.scan_expression(&statement.object);
                self.push();
                self.scan_statement(&statement.body);
                self.pop();
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                statement,
            ))) => self.scan_statement(statement),
            Statement::Export(ExportDeclaration::Assignment(expression)) => {
                self.scan_expression(expression)
            }
            Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
                ExportDefaultValue::Expression(expression) => self.scan_expression(expression),
                ExportDefaultValue::Function(function) => {
                    if function.body.is_some()
                        && let Some(name) = &function.name
                        && let Some(text) = identifier_name(self.file, name)
                    {
                        self.bind_function(text);
                    }
                    self.scan_function_like(function);
                }
                ExportDefaultValue::Class(class) => {
                    self.scan_class_heritage(class);
                    if let Some(name) = &class.name
                        && let Some(text) = identifier_name(self.file, name)
                    {
                        self.bind_lexical(text, name.range());
                    }
                    self.scan_class(class);
                }
                ExportDefaultValue::Missing(_) => {}
                ExportDefaultValue::Interface(_) => {}
            },
            Statement::Enum(declaration) if !declaration.is_const => {
                for member in &declaration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.scan_expression(initializer);
                    }
                }
            }
            Statement::Namespace(declaration) => {
                let name = declaration
                    .name
                    .as_identifier()
                    .and_then(|n| identifier_name(self.file, n));
                if let Some(name) = name.clone() {
                    self.bind_function(name);
                }
                self.fn_boundary += 1;
                self.function_depth += 1;
                self.push();
                self.function_roots.push(self.bound.len() - 1);
                self.preseed_vars(&declaration.body.data().statements);
                self.predeclare_immediate(&declaration.body.data().statements, false);
                if let Some(name) = &name {
                    self.use_name(name);
                }
                for statement in &declaration.body.data().statements {
                    self.scan_statement(statement);
                }
                self.function_roots.pop();
                self.pop();
                self.function_depth -= 1;
                self.fn_boundary -= 1;
            }
            _ => {}
        }
    }
    fn scan_for_binding(&mut self, binding: &ForBinding) {
        match binding {
            ForBinding::Variable(declaration) => {
                let scope = match declaration.kind {
                    VariableKind::Var => DeclarationScope::Function,
                    _ => DeclarationScope::Iteration,
                };
                for declarator in &declaration.declarations {
                    self.bind_pattern(&declarator.data().binding, scope);
                    self.scan_pattern_effects(&declarator.data().binding);
                }
            }
            ForBinding::Target(target) => self.scan_assignment_target(target),
        }
    }
    fn scan_function_like(&mut self, function: &FunctionLike) {
        self.fn_boundary += 1;
        self.function_depth += 1;
        self.push();
        self.function_roots.push(self.bound.len() - 1);
        self.preseed_parameters(&function.parameters);
        if let Some(FunctionBody::Block(block)) = &function.body {
            self.preseed_vars(&block.data().statements);
            self.predeclare_immediate(&block.data().statements, false);
        }
        self.scan_parameter_initializers(&function.parameters);
        if let Some(body) = &function.body {
            match body {
                FunctionBody::Block(block) => {
                    for statement in &block.data().statements {
                        self.scan_statement(statement);
                    }
                }
                FunctionBody::Expression(expression) => self.scan_expression(expression),
                FunctionBody::Missing(_) => {}
            }
        }
        self.function_roots.pop();
        self.pop();
        self.function_depth -= 1;
        self.fn_boundary -= 1;
    }
    fn scan_arrow(&mut self, arrow: &ArrowFunction) {
        self.function_depth += 1;
        self.push();
        self.function_roots.push(self.bound.len() - 1);
        self.preseed_parameters(&arrow.parameters);
        if let FunctionBody::Block(block) = &arrow.body {
            self.preseed_vars(&block.data().statements);
            self.predeclare_immediate(&block.data().statements, false);
        }
        self.scan_parameter_initializers(&arrow.parameters);
        match &arrow.body {
            FunctionBody::Block(block) => {
                for statement in &block.data().statements {
                    self.scan_statement(statement);
                }
            }
            FunctionBody::Expression(expression) => self.scan_expression(expression),
            FunctionBody::Missing(_) => {}
        }
        self.function_roots.pop();
        self.pop();
        self.function_depth -= 1;
    }
    fn scan_class_heritage(&mut self, class: &ClassDeclaration) {
        if let Some(heritage) = &class.extends {
            self.scan_expression(&heritage.expression);
        }
    }
    fn scan_class(&mut self, class: &ClassDeclaration) {
        self.push();
        let mut seen_private = HashSet::new();
        for member in &class.members {
            let name = match member.data() {
                ClassMember::Method(method) => &method.name,
                ClassMember::Property(property) => &property.name,
                ClassMember::AutoAccessor(accessor) => &accessor.name,
                _ => continue,
            };
            if let PropertyName::Private(private) = name
                && let Some(text) = private_name(self.file, private)
                && seen_private.insert(text.clone())
            {
                self.bind_lexical(text, private.range());
            }
        }
        let constructor = class.members.iter().find_map(|member| match member.data() {
            ClassMember::Constructor(constructor) => Some(constructor),
            _ => None,
        });
        let parameters = constructor
            .map(|constructor| constructor.parameters.as_slice())
            .unwrap_or(&[]);
        self.fn_boundary += 1;
        self.function_depth += 1;
        self.push();
        self.function_roots.push(self.bound.len() - 1);
        self.preseed_parameters(parameters);
        if let Some(constructor) = constructor {
            self.preseed_vars(&constructor.body.data().statements);
            self.predeclare_immediate(&constructor.body.data().statements, false);
        }
        self.scan_parameter_initializers(parameters);
        if let Some(constructor) = constructor {
            for statement in &constructor.body.data().statements {
                self.scan_statement(statement);
            }
        }
        for member in &class.members {
            match member.data() {
                ClassMember::Property(property)
                    if !property.modifiers.is_static
                        && !property.modifiers.is_abstract
                        && !property.modifiers.is_declare =>
                {
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                }
                ClassMember::AutoAccessor(accessor)
                    if !accessor.modifiers.is_static
                        && !accessor.modifiers.is_abstract
                        && !accessor.modifiers.is_declare =>
                {
                    if let Some(initializer) = &accessor.initializer {
                        self.scan_expression(initializer);
                    }
                }
                _ => {}
            }
        }
        self.function_roots.pop();
        self.pop();
        self.function_depth -= 1;
        self.fn_boundary -= 1;
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(_) => {}
                ClassMember::Method(method) => {
                    if let PropertyName::Computed(expression) = &method.name {
                        self.scan_expression(expression);
                    }
                    self.scan_function_like(&method.function);
                }
                ClassMember::Property(property) if property.modifiers.is_static => {
                    self.scan_property_name(&property.name);
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                }
                ClassMember::Property(property)
                    if !property.modifiers.is_abstract && !property.modifiers.is_declare =>
                {
                    self.scan_property_name(&property.name);
                }
                ClassMember::AutoAccessor(accessor) if accessor.modifiers.is_static => {
                    self.scan_property_name(&accessor.name);
                    if let Some(initializer) = &accessor.initializer {
                        self.scan_expression(initializer);
                    }
                }
                ClassMember::AutoAccessor(accessor)
                    if !accessor.modifiers.is_abstract && !accessor.modifiers.is_declare =>
                {
                    self.scan_property_name(&accessor.name);
                }
                ClassMember::StaticBlock(block) => {
                    self.push();
                    self.predeclare_immediate(&block.data().statements, false);
                    for statement in &block.data().statements {
                        self.scan_statement(statement);
                    }
                    self.pop();
                }
                _ => {}
            }
        }
        self.pop();
    }
    fn scan_expression(&mut self, expression: &Expr) {
        if let Some(replacement) = self
            .jsx_plan
            .and_then(|plan| plan.expression_desugars.get(&expression.id()))
            .cloned()
        {
            self.scan_expression(&replacement);
            return;
        }
        match expression.data() {
            Expression::JsxElement(_)
            | Expression::JsxFragment(_)
            | Expression::JsxSelfClosingElement(_) => {}
            Expression::Identifier(identifier) => {
                if let Some(name) = self
                    .jsx_plan
                    .and_then(|plan| plan.generated_text.get(identifier.id()))
                    .map(str::to_owned)
                    .or_else(|| identifier_name(self.file, identifier))
                {
                    self.use_name(&name);
                }
            }
            Expression::This => {
                if self.fn_boundary == 0 {
                    self.uses_this = true;
                }
            }
            Expression::Super => {}
            Expression::Meta(MetaProperty::NewTarget) => {
                if self.fn_boundary == 0 {
                    self.uses_new_target = true;
                }
            }
            Expression::Meta(MetaProperty::ImportMeta) => {}
            Expression::Literal(_) => {}
            Expression::Template(template) => {
                for expression in &template.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::TaggedTemplate(tagged) => {
                self.scan_expression(&tagged.tag);
                for expression in &tagged.template.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(expression) => self.scan_expression(expression),
                        ArrayElement::Spread(spread) => self.scan_expression(&spread.argument),
                        _ => {}
                    }
                }
            }
            Expression::Object(object) => {
                for member in &object.members {
                    match member.data() {
                        ObjectMember::Property(property) => {
                            if let PropertyName::Computed(key) = &property.name {
                                self.scan_expression(key);
                            }
                            self.scan_expression(&property.value);
                        }
                        ObjectMember::Method(method) => {
                            if let PropertyName::Computed(key) = &method.name {
                                self.scan_expression(key);
                            }
                            self.scan_function_like(&method.function);
                        }
                        ObjectMember::Spread(spread) => self.scan_expression(&spread.argument),
                        ObjectMember::Missing(_) => {}
                    }
                }
            }
            Expression::Function(function) => self.scan_function_like(&function.function),
            Expression::Class(class) => {
                self.scan_class_heritage(&class.class);
                self.scan_class(&class.class);
            }
            Expression::Arrow(arrow) => self.scan_arrow(arrow),
            Expression::Call(call) => {
                self.scan_expression(&call.callee);
                for argument in &call.arguments {
                    match argument {
                        CallArgument::Expression(expression) => self.scan_expression(expression),
                        CallArgument::Spread(spread) => self.scan_expression(&spread.argument),
                        CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::New(new) => {
                self.scan_expression(&new.callee);
                for argument in &new.arguments {
                    match argument {
                        CallArgument::Expression(expression) => self.scan_expression(expression),
                        CallArgument::Spread(spread) => self.scan_expression(&spread.argument),
                        CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::Member(member) => {
                self.scan_expression(&member.object);
                if let MemberProperty::Computed(expression) = &member.property {
                    self.scan_expression(expression);
                }
                if let MemberProperty::Private(private) = &member.property
                    && let Some(name) = private_name(self.file, private)
                {
                    self.use_name(&name);
                }
            }
            Expression::Await(await_expression) => self.scan_expression(&await_expression.argument),
            Expression::Yield(yield_expression) => {
                if let Some(argument) = &yield_expression.argument {
                    self.scan_expression(argument);
                }
            }
            Expression::Unary(unary) => self.scan_expression(&unary.argument),
            Expression::Update(update) => self.scan_assignment_target(&update.argument),
            Expression::Binary(binary) => {
                self.scan_expression(&binary.left);
                self.scan_expression(&binary.right);
            }
            Expression::Logical(logical) => {
                self.scan_expression(&logical.left);
                self.scan_expression(&logical.right);
            }
            Expression::Conditional(conditional) => {
                self.scan_expression(&conditional.test);
                self.scan_expression(&conditional.consequent);
                self.scan_expression(&conditional.alternate);
            }
            Expression::Assignment(assignment) => {
                self.scan_expression(&assignment.right);
                self.scan_assignment_target(&assignment.left);
            }
            Expression::Sequence(sequence) => {
                for expression in &sequence.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::Parenthesized(inner)
            | Expression::NonNull(crate::syntax::NonNullExpression { expression: inner }) => {
                self.scan_expression(inner);
            }
            Expression::As(expression) => self.scan_expression(&expression.expression),
            Expression::Satisfies(expression) => self.scan_expression(&expression.expression),
            Expression::TypeAssertion(expression) => self.scan_expression(&expression.expression),
            Expression::Import(import) => {
                self.scan_expression(&import.source);
                if let Some(options) = &import.options {
                    self.scan_expression(options);
                }
            }
            Expression::Missing(_) => {}
        }
    }
    fn scan_assignment_target(&mut self, target: &AssignmentTargetNode) {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => {
                if let Some(name) = identifier_name(self.file, identifier) {
                    self.use_name(&name);
                }
            }
            AssignmentTarget::Member(member) => {
                self.scan_expression(&member.object);
                if let MemberProperty::Computed(expression) = &member.property {
                    self.scan_expression(expression);
                }
                if let MemberProperty::Private(private) = &member.property
                    && let Some(name) = private_name(self.file, private)
                {
                    self.use_name(&name);
                }
            }
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    if let PropertyName::Computed(key) = &property.name {
                        self.scan_expression(key);
                    }
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                    self.scan_assignment_target(&property.target);
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    if let AssignmentArrayElement::Target(inner) = element {
                        self.scan_assignment_target(inner);
                    }
                }
            }
            AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(operand) => {
                self.scan_expression(operand);
            }
        }
    }
}
/// The `for` head range used for the back-edge jump's diagnostic anchor.
fn head_range(for_statement: &ForStatement) -> TextRange {
    for_statement
        .test
        .as_ref()
        .map_or_else(zero_range, |test| test.range())
}
fn collect_immediate_declarations<'a>(
    file: &SourceFile,
    statements: &'a [Stmt],
) -> Vec<ImmediateDeclaration<'a>> {
    let mut declarations = Vec::new();
    for statement in statements {
        collect_immediate_declaration(file, statement, &mut declarations);
    }
    declarations
}
fn collect_immediate_declaration<'a>(
    file: &SourceFile,
    statement: &'a Stmt,
    declarations: &mut Vec<ImmediateDeclaration<'a>>,
) {
    match statement.data() {
        Statement::Variable(declaration)
            if matches!(
                declaration.kind,
                VariableKind::Let
                    | VariableKind::Const
                    | VariableKind::Using
                    | VariableKind::AwaitUsing
            ) =>
        {
            for declarator in &declaration.declarations {
                collect_pattern_declarations(file, &declarator.data().binding, declarations);
            }
        }
        Statement::Function(declaration) => {
            let function = &declaration.function;
            if function.body.is_some()
                && let Some(identifier) = &function.name
                && let Some(name) = identifier_name(file, identifier)
            {
                declarations.push(ImmediateDeclaration {
                    name,
                    site: binding_site(identifier.range()),
                    range: statement.range(),
                    kind: ImmediateDeclarationKind::Function(function),
                });
            }
        }
        Statement::Class(class) => {
            if let Some(identifier) = &class.name
                && let Some(name) = identifier_name(file, identifier)
            {
                declarations.push(ImmediateDeclaration {
                    name,
                    site: binding_site(identifier.range()),
                    range: identifier.range(),
                    kind: ImmediateDeclarationKind::Lexical,
                });
            }
        }
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
            declaration,
        ))) => collect_immediate_declaration(file, declaration, declarations),
        Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
            ExportDefaultValue::Function(function) => {
                if function.body.is_some()
                    && let Some(identifier) = &function.name
                    && let Some(name) = identifier_name(file, identifier)
                {
                    declarations.push(ImmediateDeclaration {
                        name,
                        site: binding_site(identifier.range()),
                        range: statement.range(),
                        kind: ImmediateDeclarationKind::Function(function),
                    });
                }
            }
            ExportDefaultValue::Class(class) => {
                if let Some(identifier) = &class.name
                    && let Some(name) = identifier_name(file, identifier)
                {
                    declarations.push(ImmediateDeclaration {
                        name,
                        site: binding_site(identifier.range()),
                        range: identifier.range(),
                        kind: ImmediateDeclarationKind::Lexical,
                    });
                }
            }
            _ => {}
        },
        _ => {}
    }
}
fn collect_pattern_declarations<'a>(
    file: &SourceFile,
    pattern: &'a Pattern,
    declarations: &mut Vec<ImmediateDeclaration<'a>>,
) {
    match pattern.data() {
        BindingPattern::Identifier(identifier) => {
            if let Some(name) = identifier_name(file, identifier) {
                declarations.push(ImmediateDeclaration {
                    name,
                    site: binding_site(identifier.range()),
                    range: identifier.range(),
                    kind: ImmediateDeclarationKind::Lexical,
                });
            }
        }
        BindingPattern::Object(object) => {
            for property in &object.properties {
                collect_pattern_declarations(file, &property.binding, declarations);
            }
        }
        BindingPattern::Array(array) => {
            for element in &array.elements {
                if let ArrayBindingElement::Binding(binding) = element {
                    collect_pattern_declarations(file, binding, declarations);
                }
            }
        }
        BindingPattern::Assignment(assignment) => {
            collect_pattern_declarations(file, &assignment.left, declarations);
        }
        BindingPattern::Rest(rest) => {
            collect_pattern_declarations(file, &rest.argument, declarations);
        }
        BindingPattern::Missing(_) => {}
    }
}
/// The runtime names a statement declares (for `export` linkage).
pub(crate) fn declared_names(file: &SourceFile, statement: &Stmt) -> Vec<String> {
    let mut names = Vec::new();
    match statement.data() {
        Statement::Variable(declaration) => {
            for declarator in &declaration.declarations {
                collect_pattern_names(file, &declarator.data().binding, &mut names);
            }
        }
        Statement::Function(declaration) => {
            if let Some(name) = &declaration.function.name
                && let Some(text) = identifier_name(file, name)
            {
                names.push(text);
            }
        }
        Statement::Class(class) => {
            if let Some(name) = &class.name
                && let Some(text) = identifier_name(file, name)
            {
                names.push(text);
            }
        }
        Statement::Enum(declaration) if !declaration.is_const => {
            if let Some(name) = identifier_name(file, &declaration.name) {
                names.push(name);
            }
        }
        Statement::ImportEquals(import) => {
            if let Some(name) = identifier_name(file, &import.local) {
                names.push(name);
            }
        }
        Statement::Namespace(declaration) => {
            if let Some(name) = declaration
                .name
                .as_identifier()
                .and_then(|n| identifier_name(file, n))
            {
                names.push(name);
            }
        }
        _ => {}
    }
    names
}
/// Collects every `var`-scoped binding name in a statement list, not descending
/// into nested function or class bodies (which have their own `var` scope).
pub(crate) fn collect_var_names(file: &SourceFile, statements: &[Stmt], names: &mut Vec<String>) {
    for statement in statements {
        collect_var_names_stmt(file, statement, names);
    }
}
fn collect_var_names_stmt(file: &SourceFile, statement: &Stmt, names: &mut Vec<String>) {
    match statement.data() {
        Statement::Variable(declaration) if matches!(declaration.kind, VariableKind::Var) => {
            for declarator in &declaration.declarations {
                collect_pattern_names(file, &declarator.data().binding, names);
            }
        }
        Statement::Block(block) => collect_var_names(file, &block.data().statements, names),
        Statement::If(statement) => {
            collect_var_names_stmt(file, &statement.consequent, names);
            if let Some(alternate) = &statement.alternate {
                collect_var_names_stmt(file, alternate, names);
            }
        }
        Statement::For(statement) => {
            if let Some(ForInitializer::Variable(declaration)) = &statement.initializer
                && matches!(declaration.kind, VariableKind::Var)
            {
                for declarator in &declaration.declarations {
                    collect_pattern_names(file, &declarator.data().binding, names);
                }
            }
            collect_var_names_stmt(file, &statement.body, names);
        }
        Statement::ForIn(statement) => {
            collect_for_binding_var(file, &statement.binding, names);
            collect_var_names_stmt(file, &statement.body, names);
        }
        Statement::ForOf(statement) => {
            collect_for_binding_var(file, &statement.binding, names);
            collect_var_names_stmt(file, &statement.body, names);
        }
        Statement::While(statement) => collect_var_names_stmt(file, &statement.body, names),
        Statement::DoWhile(statement) => collect_var_names_stmt(file, &statement.body, names),
        Statement::Switch(statement) => {
            for case in &statement.cases {
                for statement in &case.data().consequent {
                    collect_var_names_stmt(file, statement, names);
                }
            }
        }
        Statement::Try(statement) => {
            for statement in &statement.block.data().statements {
                collect_var_names_stmt(file, statement, names);
            }
            if let Some(handler) = &statement.handler {
                for statement in &handler.data().body.data().statements {
                    collect_var_names_stmt(file, statement, names);
                }
            }
            if let Some(finalizer) = &statement.finalizer {
                for statement in &finalizer.data().statements {
                    collect_var_names_stmt(file, statement, names);
                }
            }
        }
        Statement::Labeled(statement) => collect_var_names_stmt(file, &statement.body, names),
        Statement::With(statement) => collect_var_names_stmt(file, &statement.body, names),
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
            statement,
        ))) => collect_var_names_stmt(file, statement, names),
        Statement::Enum(declaration) if !declaration.is_const => {
            if let Some(name) = identifier_name(file, &declaration.name) {
                names.push(name);
            }
        }
        Statement::Namespace(declaration) => {
            if let Some(name) = declaration
                .name
                .as_identifier()
                .and_then(|n| identifier_name(file, n))
            {
                names.push(name);
            }
        }
        _ => {}
    }
}
fn collect_for_binding_var(file: &SourceFile, binding: &ForBinding, names: &mut Vec<String>) {
    if let ForBinding::Variable(declaration) = binding
        && matches!(declaration.kind, VariableKind::Var)
    {
        for declarator in &declaration.declarations {
            collect_pattern_names(file, &declarator.data().binding, names);
        }
    }
}
pub(crate) fn collect_pattern_names(file: &SourceFile, pattern: &Pattern, names: &mut Vec<String>) {
    match pattern.data() {
        BindingPattern::Identifier(identifier) => {
            if let Some(text) = identifier_name(file, identifier) {
                names.push(text);
            }
        }
        BindingPattern::Object(object) => {
            for property in &object.properties {
                collect_pattern_names(file, &property.binding, names);
            }
        }
        BindingPattern::Array(array) => {
            for element in &array.elements {
                if let ArrayBindingElement::Binding(inner) = element {
                    collect_pattern_names(file, inner, names);
                }
            }
        }
        BindingPattern::Rest(rest) => collect_pattern_names(file, &rest.argument, names),
        BindingPattern::Assignment(assignment) => {
            collect_pattern_names(file, &assignment.left, names);
        }
        BindingPattern::Missing(_) => {}
    }
}
/// The cooked identity of an identifier node, or `None` for a missing token.
fn identifier_name(file: &SourceFile, identifier: &IdentifierNode) -> Option<String> {
    let token = identifier.data().token();
    if token.is_missing() {
        return None;
    }
    file.identifier_text(token).map(Cow::into_owned)
}
/// The raw text of a private identifier (`#name`), or `None` for a missing
/// token.
fn private_name(file: &SourceFile, private: &PrivateIdentifierNode) -> Option<String> {
    let token = private.data().token();
    if token.is_missing() {
        return None;
    }
    file.token_text(token).map(str::to_owned)
}
/// Maps a source binary operator to its bytecode counterpart.
fn map_binary_operator(operator: BinaryOperator) -> BinaryOp {
    match operator {
        BinaryOperator::Add => BinaryOp::Add,
        BinaryOperator::Subtract => BinaryOp::Subtract,
        BinaryOperator::Multiply => BinaryOp::Multiply,
        BinaryOperator::Divide => BinaryOp::Divide,
        BinaryOperator::Remainder => BinaryOp::Remainder,
        BinaryOperator::Exponentiate => BinaryOp::Exponent,
        BinaryOperator::BitAnd => BinaryOp::BitAnd,
        BinaryOperator::BitOr => BinaryOp::BitOr,
        BinaryOperator::BitXor => BinaryOp::BitXor,
        BinaryOperator::LeftShift => BinaryOp::ShiftLeft,
        BinaryOperator::SignedRightShift => BinaryOp::ShiftRight,
        BinaryOperator::UnsignedRightShift => BinaryOp::UnsignedShiftRight,
        BinaryOperator::Equal => BinaryOp::Equal,
        BinaryOperator::NotEqual => BinaryOp::NotEqual,
        BinaryOperator::StrictEqual => BinaryOp::StrictEqual,
        BinaryOperator::StrictNotEqual => BinaryOp::StrictNotEqual,
        BinaryOperator::LessThan => BinaryOp::LessThan,
        BinaryOperator::LessThanOrEqual => BinaryOp::LessThanOrEqual,
        BinaryOperator::GreaterThan => BinaryOp::GreaterThan,
        BinaryOperator::GreaterThanOrEqual => BinaryOp::GreaterThanOrEqual,
        BinaryOperator::Instanceof => BinaryOp::InstanceOf,
        BinaryOperator::In => BinaryOp::In,
    }
}
/// A compound assignment's underlying operation.
enum CompoundOp {
    Arithmetic(BinaryOp),
    Logical(LogicalOperator),
}
fn compound_operator(operator: AssignmentOperator) -> Option<CompoundOp> {
    let op = match operator {
        AssignmentOperator::Assign => return None,
        AssignmentOperator::AddAssign => BinaryOp::Add,
        AssignmentOperator::SubtractAssign => BinaryOp::Subtract,
        AssignmentOperator::MultiplyAssign => BinaryOp::Multiply,
        AssignmentOperator::DivideAssign => BinaryOp::Divide,
        AssignmentOperator::RemainderAssign => BinaryOp::Remainder,
        AssignmentOperator::ExponentiateAssign => BinaryOp::Exponent,
        AssignmentOperator::LeftShiftAssign => BinaryOp::ShiftLeft,
        AssignmentOperator::SignedRightShiftAssign => BinaryOp::ShiftRight,
        AssignmentOperator::UnsignedRightShiftAssign => BinaryOp::UnsignedShiftRight,
        AssignmentOperator::BitAndAssign => BinaryOp::BitAnd,
        AssignmentOperator::BitOrAssign => BinaryOp::BitOr,
        AssignmentOperator::BitXorAssign => BinaryOp::BitXor,
        AssignmentOperator::LogicalAndAssign => {
            return Some(CompoundOp::Logical(LogicalOperator::And));
        }
        AssignmentOperator::LogicalOrAssign => {
            return Some(CompoundOp::Logical(LogicalOperator::Or));
        }
        AssignmentOperator::NullishAssign => {
            return Some(CompoundOp::Logical(LogicalOperator::Nullish));
        }
    };
    Some(CompoundOp::Arithmetic(op))
}
fn numeric_key_text(
    context: &FunctionContext<'_>,
    number: &NumericLiteralNode,
) -> Result<String, LowerError> {
    let range = number.range();
    let token = number.data().token();
    if token.is_missing() {
        return Err(context.missing(range, NodeKind::NumericLiteral));
    }
    let lexeme = context
        .file
        .token_text(token)
        .filter(|text| !text.is_empty())
        .ok_or_else(|| context.error(range, LowerErrorKind::InvalidNumericLiteral))?;
    let value = number_value(lexeme)
        .ok_or_else(|| context.error(range, LowerErrorKind::InvalidNumericLiteral))?;
    if value.fract() == 0.0 && value.is_finite() && (0.0..=9_007_199_254_740_991.0).contains(&value)
    {
        Ok(format!("{}", value as u64))
    } else {
        // Non-integer numeric keys stringify by their number value.
        Ok(format_number_key(value))
    }
}
fn format_number_key(value: f64) -> String {
    if value == 0.0 {
        "0".to_owned()
    } else {
        let text = format!("{value}");
        text
    }
}
/// Trims the delimiter characters from a template element's raw lexeme.
fn trim_template_delimiters(text: &str, kind: TokenKind) -> &str {
    let (head, tail): (usize, usize) = match kind {
        TokenKind::NoSubstitutionTemplate => (1, 1),
        TokenKind::TemplateHead => (1, 2),
        TokenKind::TemplateMiddle => (1, 2),
        TokenKind::TemplateTail => (1, 1),
        _ => (0, 0),
    };
    let bytes = text.len();
    if bytes < head + tail {
        return "";
    }
    &text[head..bytes - tail]
}
/// Splits a regex literal `/pattern/flags` into `(pattern, flags)`.
fn split_regex(lexeme: &str) -> Option<(String, String)> {
    let lexeme = lexeme.strip_prefix('/')?;
    let last_slash = lexeme.rfind('/')?;
    let pattern = &lexeme[..last_slash];
    let flags = &lexeme[last_slash + 1..];
    Some((pattern.to_owned(), flags.to_owned()))
}
fn number_constant(value: f64) -> Constant {
    if value.fract() == 0.0
        && value.is_finite()
        && (f64::from(i32::MIN)..=f64::from(i32::MAX)).contains(&value)
        && !(value == 0.0 && value.is_sign_negative())
    {
        Constant::Int32(value as i32)
    } else {
        Constant::Number(NumberBits::from_f64(value))
    }
}
#[cfg(test)]
mod tests {
    use super::{
        BigIntTextError, CaptureKey, ConstEnumOperation, ContainerKind, IteratorCloseMode,
        LowerError, LowerErrorKind, LowerOptions, UnsupportedConstruct, canonical_bigint_text,
        lower, lower_checked,
    };
    use crate::checker::{ProgramCheckInput, ResolvedModuleEdge, check, check_program};
    use crate::literal::cook_escapes;
    use crate::parser::parse;
    use crate::scanner::scan;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;
    fn repository_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("repository root is readable")
    }
    fn script_kind(path: &str) -> ScriptKind {
        if path.ends_with(".d.ts")
            || path.ends_with(".ts")
            || path.ends_with(".mts")
            || path.ends_with(".cts")
        {
            ScriptKind::TypeScript
        } else if path.ends_with(".tsx") {
            ScriptKind::TypeScriptReact
        } else if path.ends_with(".js") || path.ends_with(".mjs") || path.ends_with(".cjs") {
            ScriptKind::JavaScript
        } else if path.ends_with(".jsx") {
            ScriptKind::JavaScriptReact
        } else {
            panic!("declared corpus source has unsupported extension: {path}");
        }
    }
    fn declared_corpus_sources(root: &Path) -> Vec<String> {
        let manifest = fs::read_to_string(root.join("corpus/manifest.toml"))
            .expect("corpus manifest is readable");
        let mut sources = BTreeSet::new();
        for line in manifest.lines() {
            if let Some(value) = quoted_value(line, "entrypoint") {
                sources.insert(value);
            }
        }
        let specs = root.join("corpus/specs");
        for entry in fs::read_dir(&specs).expect("corpus specs directory is readable") {
            let path = entry.expect("spec directory entry").path();
            if path.extension().and_then(|extension| extension.to_str()) != Some("toml") {
                continue;
            }
            let text = fs::read_to_string(&path).expect("corpus spec is UTF-8");
            let start = text
                .find("source_files")
                .unwrap_or_else(|| panic!("{} has no source_files", path.display()));
            let array = &text[start..];
            let open = array
                .find('[')
                .expect("source_files has an opening bracket");
            let close = array[open + 1..]
                .find(']')
                .map(|index| open + 1 + index)
                .expect("source_files has a closing bracket");
            let contents = &array[open + 1..close];
            for item in contents.split(',') {
                let item = item.trim();
                if item.is_empty() {
                    continue;
                }
                let value = item
                    .strip_prefix('"')
                    .and_then(|item| item.strip_suffix('"'))
                    .unwrap_or_else(|| {
                        panic!(
                            "{} has malformed source_files item `{item}`",
                            path.display()
                        )
                    });
                sources.insert(value.to_owned());
            }
        }
        for local_case in [
            "corpus/cases/derived-construction.ts",
            "corpus/cases/event-loop.ts",
            "corpus/cases/explicit-resource.ts",
            "corpus/cases/for-await-iterator.ts",
            "corpus/cases/import-meta.ts",
            "corpus/cases/lexical-environment.ts",
            "corpus/cases/top-level-throw.ts",
        ] {
            assert!(
                sources.contains(local_case),
                "local corpus case {local_case} is a declared corpus member"
            );
        }
        assert_eq!(
            sources.len(),
            70,
            "the checked corpus contract is 70 sources: upstream entrypoints and \
             spec-declared project files plus the seven named local cases"
        );
        sources.into_iter().collect()
    }
    fn quoted_value(line: &str, key: &str) -> Option<String> {
        let line = line.trim();
        let value = line
            .strip_prefix(key)?
            .trim_start()
            .strip_prefix('=')?
            .trim();
        Some(value.strip_prefix('"')?.strip_suffix('"')?.to_owned())
    }
    #[test]
    fn cooking_preserves_lone_surrogate_units() {
        assert_eq!(cook_escapes("\\uD800").as_units(), [0xD800]);
        assert_eq!(cook_escapes("\\uD83D\\uDE03").as_units(), [0xD83D, 0xDE03]);
        assert_eq!(cook_escapes("\\u{1F603}").as_units(), [0xD83D, 0xDE03]);
    }
    #[test]
    fn all_declared_corpus_sources_lower_to_verified_modules() {
        let root = repository_root();
        let sources = declared_corpus_sources(&root);
        let mut failures = Vec::new();
        for (index, relative) in sources.iter().enumerate() {
            let path = root.join(relative);
            let text = fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} is unreadable: {error}", path.display()));
            let source =
                Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
            let scanned = scan(SourceId::new(index as u32), script_kind(relative), source);
            let parsed = parse(scanned);
            match lower(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                },
            ) {
                Ok(module) => {
                    assert!(
                        module.certificate(module.entry()).is_some(),
                        "{relative}: entry is verified"
                    );
                }
                Err(error) => failures.push(format!("{relative}: {error}")),
            }
        }
        assert!(
            failures.is_empty(),
            "{}/{} declared corpus sources failed lowering:\n{}",
            failures.len(),
            sources.len(),
            failures.join("\n")
        );
    }
    use bamts_bytecode::{
        BinaryOp, Constant, DecodeLimits, Function, Instruction, IteratorKind, Module, Pc,
        RESUME_RETURN, RESUME_THROW, Register, UnaryOp, Verified, decode_verified,
    };
    fn lower_js_result(src: &str) -> Result<Module<Verified>, LowerError> {
        let source = Arc::new(
            SourceText::new(src.to_owned()).expect("test source fits the per-file budget"),
        );
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        lower(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
        )
    }
    fn lower_js(src: &str) -> Module<Verified> {
        lower_js_result(src).expect("snippet lowers to a verified module")
    }
    #[test]
    fn class_decorators_lower_in_reverse_and_bind_the_final_class_once() {
        let module = lower_js(
            "function first() {} function second() { return class Replacement {} } @second @first class C {}",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::Call { callee, .. } if is_decorator_application_call(code, index) => {
                    Some((index, callee))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            calls.len(),
            2,
            "both class decorator applications occur at class definition time"
        );
        assert!(
            code[..calls[0].0]
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadConst { .. })),
            "decorator expressions are evaluated before application"
        );
        assert!(calls[0].0 < calls[1].0, "decorators apply in reverse order");
        let constants = module.constants();
        let store_globals: Vec<_> = code
            .iter()
            .filter(|instruction| match instruction {
                Instruction::StoreGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii("C")
                ),
                _ => false,
            })
            .collect();
        assert_eq!(
            store_globals.len(),
            1,
            "the class declaration binds the final decorated constructor once"
        );
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::CreateCell { .. }
            )),
            "the class keeps its TDZ cell"
        );
    }
    #[test]
    fn checker_diagnosed_super_misuse_lowers_to_inert_values() {
        // The checker rejects every one of these (BAMTS-C024..C027); lowering
        // must still produce a verified module for diagnosed sources instead
        // of failing.
        for src in [
            "function f() { super(); }",
            "super;",
            "let x = super;",
            "class A { constructor() { super(); } }",
            "class A extends Object { constructor() { super(); const g = () => super(); } }",
            "class A extends Object { m() { super(); } }",
        ] {
            lower_js(src);
        }
    }
    #[test]
    fn parameter_decorators_are_rejected() {
        let error = lower_js_result(
            "function marker() {} class C { constructor(@marker first, @marker second) {} }",
        )
        .expect_err("parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error = lower_js_result("function marker() {} function f(@marker x) { return x; }")
            .expect_err("function parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error =
            lower_js_result("function marker() {} class C { method(@marker x) { return x; } }")
                .expect_err("method parameter decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ParameterDecorator)
        );
        let error = lower_js_result("function marker() {} class C { @marker constructor() {} }")
            .expect_err("constructor decorators must fail lowering");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::ConstructorDecorator)
        );
    }
    #[test]
    fn decorated_class_expressions_return_the_replacement() {
        let module = lower_js(
            "function replace() { return class Replacement {} } const C = @replace class Named {} new C();",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let call_count = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(call_count, 1, "the expression class decorator applies once");
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::Construct { .. }
            )),
            "the decorated expression result is constructed"
        );
    }
    #[test]
    fn decorated_fields_apply_in_source_order_with_one_computed_key() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec static [key()] = 1; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .map(|(index, _)| index)
            .collect();
        let apply_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(key_calls.len(), 1, "computed key expression evaluates once");
        assert_eq!(
            apply_calls.len(),
            1,
            "field decorator application occurs once"
        );
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let installation = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, .. }
                    if *object == raw_ctor && index > apply_calls[0] =>
                {
                    Some(index)
                }
                _ => None,
            })
            .expect("decorated static field installs its captured key");
        assert!(
            key_calls[0] < apply_calls[0],
            "key evaluation precedes decorator application"
        );
        assert!(
            apply_calls[0] < installation,
            "decorator application precedes static field installation"
        );
    }
    #[test]
    fn decorated_instance_field_uses_the_same_captured_key_and_receives_no_replacement() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec\n[key()]; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .count();
        let apply_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(key_calls, 1, "computed-key expression evaluates once");
        assert_eq!(
            apply_calls, 1,
            "instance field decorator application occurs once at class definition time"
        );
        let entry_index = module.entry().get() as usize;
        let constructor = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, function)| {
                *index != entry_index
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .map(|(_, function)| function)
            .expect("instance field still initializes in the constructor");
        assert!(
            !constructor
                .code()
                .iter()
                .enumerate()
                .any(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        && is_decorator_application_call(constructor.code(), index)
                }),
            "decorator application remains class-definition time"
        );
    }
    #[test]
    fn decorated_auto_accessor_key_evaluates_once_before_installation() {
        let module = lower_js(
            "function key() { return 'x'; } function dec(target, key) { return target[key]; } class C { @dec accessor [key()] = 1; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(code, *index) == Some(0)
                    && call_loads_global(code, constants, *index, "key")
            })
            .count();
        let apply_calls = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .count();
        assert_eq!(key_calls, 1, "key expression evaluates once");
        assert_eq!(
            apply_calls, 1,
            "auto-accessor decorator application occurs once"
        );
    }
    #[test]
    fn field_decorator_initializer_flag_is_definite_on_every_merge_path() {
        let module = lower_js(
            "function dec(_value, _context) { return undefined; } class C { @dec x = 1; }",
        );
        assert!(
            module.functions()[module.entry().get() as usize]
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "field decorator application occurs in the entry function"
        );
    }
    #[test]
    fn add_initializer_helper_seeds_its_return_register_before_branching() {
        let module = lower_js("function dec() {} class C { @dec m() {} }");
        let helper = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 2
                    && function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. }))
            })
            .expect("member context emits an addInitializer helper");
        let Instruction::Return { value } = helper.code().last().expect("trailing return") else {
            panic!("addInitializer ends with Return");
        };
        let return_reg = *value;
        let seeded_before_branch = helper
            .code()
            .iter()
            .take_while(|instruction| {
                !matches!(
                    instruction,
                    Instruction::JumpIfFalse { .. }
                        | Instruction::JumpIfTrue { .. }
                        | Instruction::Jump { .. }
                )
            })
            .any(|instruction| {
                matches!(
                    instruction,
                    Instruction::LoadConst { dst, .. } | Instruction::Move { dst, .. }
                        if *dst == return_reg
                )
            });
        assert!(
            seeded_before_branch,
            "addInitializer return register must be seeded before the open/closed split"
        );
    }
    #[test]
    fn member_decorator_stages_drain_before_class_decorators_in_pinned_order() {
        let module = lower_js(
            "function static_method() {} \
             function instance_method() {} \
             function static_field() {} \
             function instance_field() {} \
             function class_decorator() {} \
             @class_decorator class C { \
                 @static_method static m() {} \
                 @static_field static x = 1; \
                 @instance_method m() {} \
                 @instance_field x = 1; \
             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let application_calls: Vec<_> = code
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && is_decorator_application_call(code, *index)
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(
            application_calls.len(),
            5,
            "four member decorators and one class decorator apply at class definition time"
        );
        let expected = [
            "static_method",
            "instance_method",
            "static_field",
            "instance_field",
            "class_decorator",
        ];
        for (call_index, &expected_name) in application_calls.iter().zip(expected.iter()) {
            assert!(
                call_loads_global(code, constants, *call_index, expected_name),
                "decorator application call at index {call_index} must load global \
                 `{expected_name}`"
            );
        }
    }
    #[test]
    fn mixed_source_order_member_decorator_and_key_staging() {
        let module = lower_js(
            "function a() { return 'a'; }             function b() { return 'b'; }             function c() { return 'c'; }             function dec(_value, _context) {}             class C {                 [a()] = 0;                 @dec
[b()] = 0;                 static [c()] = 0;             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let key_call = |name: &str| -> usize {
            code.iter()
                .enumerate()
                .find_map(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        .then_some(())
                        .filter(|_| call_arity(code, index) == Some(0))
                        .filter(|_| call_loads_global(code, constants, index, name))
                        .map(|_| index)
                })
                .unwrap_or_else(|| panic!("missing key call for {name}"))
        };
        let a = key_call("a");
        let b = key_call("b");
        let c = key_call("c");
        assert!(
            a < b && b < c,
            "computed keys evaluate in source order: a < b < c"
        );
        let apply = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    .then_some(index)
                    .filter(|&index| is_decorator_application_call(code, index))
            })
            .expect("decorated member applies once");
        assert!(
            c < apply,
            "all key evaluations precede decorator application"
        );
    }
    #[test]
    fn plain_computed_field_key_evaluated_once_at_class_definition() {
        let module = lower_js("function key() { return 'x'; } class C { [key()] = 1 } new C();");
        let entry_index = module.entry().get() as usize;
        let entry = module.functions()[entry_index].code();
        let constants = module.constants();
        let entry_key_calls = entry
            .iter()
            .enumerate()
            .filter(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. })
                    && call_arity(entry, *index) == Some(0)
                    && call_loads_global(entry, constants, *index, "key")
            })
            .count();
        assert_eq!(
            entry_key_calls, 1,
            "plain computed key evaluates once at class definition"
        );
        let constructor = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, function)| {
                *index != entry_index
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .map(|(_, function)| function)
            .expect("plain instance field initializes in the constructor");
        assert!(
            !constructor
                .code()
                .iter()
                .enumerate()
                .any(|(index, instruction)| {
                    matches!(instruction, Instruction::Call { .. })
                        && call_arity(constructor.code(), index) == Some(0)
                        && call_loads_global(constructor.code(), constants, index, "key")
                }),
            "constructor must reuse the staged key instead of re-evaluating it"
        );
        assert!(
            constructor
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::SetProperty { .. })),
            "constructor still assigns the plain field"
        );
    }
    #[test]
    fn constructor_captures_accessor_initializer_not_stored_key() {
        let module = lower_js("function outer() { let x = 1; return class { accessor y = x; }; }");
        let constructor = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() >= 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .expect("accessor constructor captures outer state and class elements");
        assert_eq!(
            constructor.capture_count(),
            2,
            "constructor captures initializer free var and class_elements"
        );
        let set_property = constructor
            .code()
            .iter()
            .position(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            .expect("accessor writes backing field");
        assert!(
            constructor.code()[..set_property]
                .iter()
                .any(|instruction| { matches!(instruction, Instruction::GetProperty { .. }) }),
            "captured initializer loads through a cell before the backing-field write"
        );
    }
    fn function_has_name(module: &Module<Verified>, function: &Function, expected: &str) -> bool {
        let Some(name) = function.name() else {
            return false;
        };
        matches!(
            &module.constants()[name.get() as usize],
            Constant::String(value) if value.eq_ascii(expected)
        )
    }
    fn global_load_call_index(code: &[Instruction], constants: &[Constant], name: &str) -> usize {
        let load_pc = code
            .iter()
            .position(|instruction| match instruction {
                Instruction::LoadGlobal { name: global, .. } => matches!(
                    &constants[global.get() as usize],
                    Constant::String(value) if value.eq_ascii(name)
                ),
                _ => false,
            })
            .unwrap_or_else(|| panic!("missing LoadGlobal for {name}"));
        let Instruction::LoadGlobal { dst, .. } = code[load_pc] else {
            unreachable!();
        };
        code.iter()
            .enumerate()
            .skip(load_pc + 1)
            .find_map(|(index, instruction)| match instruction {
                Instruction::Call { callee, .. } if *callee == dst => Some(index),
                _ => None,
            })
            .unwrap_or_else(|| panic!("missing direct call of {name}"))
    }
    fn is_empty_variadic_call(code: &[Instruction], call_index: usize) -> bool {
        let Some(Instruction::Call {
            callee, arguments, ..
        }) = code.get(call_index)
        else {
            return false;
        };
        let Some(Instruction::CreateArray { dst: arguments_reg }) =
            call_index.checked_sub(1).and_then(|index| code.get(index))
        else {
            return false;
        };
        if arguments_reg != arguments {
            return false;
        }
        let Some(Instruction::GetProperty {
            dst: callee_reg, ..
        }) = call_index.checked_sub(2).and_then(|index| code.get(index))
        else {
            return false;
        };
        callee_reg == callee
    }
    fn call_arity(code: &[Instruction], call_index: usize) -> Option<usize> {
        let Instruction::Call { arguments, .. } = code.get(call_index)? else {
            return None;
        };
        let mut arity = 0usize;
        for index in (0..call_index).rev() {
            match &code[index] {
                Instruction::ArrayPush { array, .. } if array == arguments => arity += 1,
                Instruction::CreateArray { dst } if dst == arguments => return Some(arity),
                Instruction::CreateArray { .. } | Instruction::Call { .. } => return None,
                _ => {}
            }
        }
        None
    }
    fn is_decorator_application_call(code: &[Instruction], call_index: usize) -> bool {
        call_arity(code, call_index) == Some(2)
    }
    fn call_loads_global(
        code: &[Instruction],
        constants: &[Constant],
        call_index: usize,
        name: &str,
    ) -> bool {
        let Some(Instruction::Call { callee, .. }) = code.get(call_index) else {
            return false;
        };
        code[..call_index]
            .iter()
            .rev()
            .any(|instruction| match instruction {
                Instruction::LoadGlobal { dst, name: global } if dst == callee => matches!(
                    &constants[global.get() as usize],
                    Constant::String(value) if value.eq_ascii(name)
                ),
                _ => false,
            })
    }
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct QueuedInitializerDrain {
        call_index: usize,
        queue: Register,
    }
    fn queued_initializer_drains(code: &[Instruction]) -> Vec<QueuedInitializerDrain> {
        code.iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                if !matches!(instruction, Instruction::Call { .. }) {
                    return None;
                }
                if !is_empty_variadic_call(code, index) {
                    return None;
                }
                let Instruction::GetProperty { object: queue, .. } = code[index - 2] else {
                    return None;
                };
                Some(QueuedInitializerDrain {
                    call_index: index,
                    queue,
                })
            })
            .collect()
    }
    fn class_extra_initializer_queue_register(code: &[Instruction]) -> Register {
        code.iter()
            .enumerate()
            .rev()
            .find_map(|(index, instruction)| {
                let Instruction::CreateArray { dst: queue } = instruction else {
                    return None;
                };
                if !matches!(code.get(index + 1), Some(Instruction::CreateCell { .. })) {
                    return None;
                }
                if index > 0 && matches!(code[index - 1], Instruction::CreateArray { .. }) {
                    return None;
                }
                Some(*queue)
            })
            .expect("class decoration allocates an extra-initializer queue")
    }
    fn drains_for_queue<'a>(
        drains: &'a [QueuedInitializerDrain],
        queue: Register,
    ) -> impl Iterator<Item = &'a QueuedInitializerDrain> + 'a {
        drains.iter().filter(move |drain| drain.queue == queue)
    }
    fn key_name(code: &[Instruction], constants: &[Constant], register: Register) -> String {
        let id = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no LoadConst defines key register {register:?}"));
        match &constants[id.get() as usize] {
            Constant::String(value) => value
                .to_utf8_strict()
                .expect("compiler-interned property key is well-formed UTF-16"),
            other => panic!("expected a string constant for the key, got {other:?}"),
        }
    }
    fn class_raw_ctor_and_prototype(
        code: &[Instruction],
        constants: &[Constant],
    ) -> (Register, Register) {
        let (raw_ctor, prototype, constructor_key) = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::DefineDataProperty { object, key, value }
                    if key_name(code, constants, *key) == "constructor" =>
                {
                    Some((*value, *object, *key))
                }
                _ => None,
            })
            .expect("class lowering emits tag48 for prototype.constructor");
        assert_eq!(
            key_name(code, constants, constructor_key),
            "constructor",
            "tag48 key register must evaluate to the string \"constructor\""
        );
        assert!(
            code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::DefineDataProperty { object, key, value }
                        if *object == raw_ctor
                            && *value == prototype
                            && key_name(code, constants, *key) == "prototype"
                )
            }),
            "the same raw ctor installs `.prototype` pointing at that object"
        );
        (raw_ctor, prototype)
    }
    fn assert_class_prototype_constructor_links_raw_ctor(module: &Module<Verified>) {
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let tag48 = code
            .iter()
            .find(|instruction| match instruction {
                Instruction::DefineDataProperty { key, .. } => {
                    key_name(code, constants, *key) == "constructor"
                }
                _ => false,
            })
            .expect("entry function contains tag48 prototype.constructor");
        let (prototype, constructor_key, raw_ctor) = match tag48 {
            Instruction::DefineDataProperty { object, key, value } => (*object, *key, *value),
            _ => unreachable!("filter matched DefineDataProperty"),
        };
        assert_eq!(
            key_name(code, constants, constructor_key),
            "constructor",
            "resolved tag48 key constant is \"constructor\""
        );
        assert!(
            !code.iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::SetProperty { object, key, .. }
                        if *object == prototype
                            && key_name(code, constants, *key) == "constructor"
                )
            }),
            "class prototype.constructor must not use ordinary SetProperty"
        );
        let (discovered_raw, discovered_proto) = class_raw_ctor_and_prototype(code, constants);
        assert_eq!(
            (discovered_raw, discovered_proto),
            (raw_ctor, prototype),
            "helper object/value flow matches the located tag48"
        );
        assert_eq!(
            discovered_raw, raw_ctor,
            "prototype.constructor value is the raw source constructor"
        );
    }
    #[test]
    fn named_class_prototype_constructor_refers_to_raw_ctor() {
        assert_class_prototype_constructor_links_raw_ctor(&lower_js("class C {}"));
    }
    #[test]
    fn anonymous_class_prototype_constructor_refers_to_raw_ctor() {
        assert_class_prototype_constructor_links_raw_ctor(&lower_js("const C = class {};"));
    }
    #[test]
    fn decorated_class_prototype_constructor_refers_to_raw_ctor_not_replacement() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        assert_class_prototype_constructor_links_raw_ctor(&module);
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let final_class = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::StoreGlobal { name, value } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value_name) if value_name.eq_ascii("C")
                )
                .then_some(*value),
                _ => None,
            })
            .expect("the decorated class declaration binds the replacement constructor");
        assert_ne!(
            raw_ctor, final_class,
            "class replacement must leave raw ctor and final class in distinct registers"
        );
    }
    #[test]
    fn named_class_constructor_carries_source_name_metadata() {
        let module = lower_js("class C {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "C")),
            "named class constructor metadata uses the source class name"
        );
        let anonymous = lower_js("const C = class {};");
        assert!(
            anonymous
                .functions()
                .iter()
                .all(|function| function.name().is_none()),
            "anonymous class constructors keep empty function metadata"
        );
        let expression = lower_js("const C = class Named {};");
        assert!(
            expression
                .functions()
                .iter()
                .any(|function| function_has_name(&expression, function, "Named")),
            "named class expressions thread the expression name into constructor metadata"
        );
    }
    #[test]
    fn decorated_named_class_keeps_raw_constructor_name_metadata() {
        let module =
            lower_js("function replace() { return class Replacement {} } @replace class Named {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "Named")),
            "class decorators still see the non-empty raw constructor name"
        );
        assert!(
            module.functions().iter().any(|function| function_has_name(
                &module,
                function,
                "Replacement"
            )),
            "replacement constructors keep their own source names"
        );
    }
    #[test]
    fn static_initializers_capture_final_class_as_lexical_this() {
        let module = lower_js("class C { static x = this; static { this; } }");
        let entry = &module.functions()[module.entry().get() as usize];
        assert!(
            !entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "static field and block this lower through final_class, not LoadThis"
        );
        assert!(
            entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::SetProperty { .. })),
            "static field still installs on the class"
        );
    }
    #[test]
    fn class_extra_initializers_run_after_static_inits_in_source_order() {
        let module = lower_js(
            "function runClassExtra() {} \
             function runStaticField() {} \
             function runStaticBlock() {} \
             function dec(_value, context) { context.addInitializer(runClassExtra); } \
             @dec class C { \
               static x = (runStaticField(), 0); \
               static { runStaticBlock(); } \
             }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let static_field_call = global_load_call_index(code, constants, "runStaticField");
        let static_block_call = global_load_call_index(code, constants, "runStaticBlock");
        let class_queue = class_extra_initializer_queue_register(code);
        let drains = queued_initializer_drains(code);
        let mut drains_by_queue: std::collections::BTreeMap<Register, Vec<usize>> =
            std::collections::BTreeMap::new();
        for drain in &drains {
            drains_by_queue
                .entry(drain.queue)
                .or_default()
                .push(drain.call_index);
        }
        for (queue, call_indices) in &drains_by_queue {
            assert_eq!(
                call_indices.len(),
                1,
                "initializer queue {queue:?} must drain exactly once, got {call_indices:?}"
            );
        }
        let class_drains: Vec<_> = drains_for_queue(&drains, class_queue).collect();
        assert_eq!(
            class_drains.len(),
            1,
            "class-level addInitializer runs exactly one queued callback"
        );
        let class_extra_call = class_drains[0].call_index;
        for member_drain in drains.iter().filter(|drain| drain.queue != class_queue) {
            assert!(
                member_drain.call_index < static_block_call,
                "member extra-initializer drains must precede static blocks"
            );
        }
        assert!(
            static_field_call < static_block_call,
            "static field initializers precede static blocks"
        );
        assert!(
            static_block_call < class_extra_call,
            "static blocks precede class-level extra initializers"
        );
        assert!(
            static_field_call < class_extra_call,
            "all static initializers precede class-level extra initializers"
        );
    }
    #[test]
    fn decorated_replacement_static_this_uses_final_class_capture() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        let entry = &module.functions()[module.entry().get() as usize];
        assert!(
            !entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "replaced-class static initializers still capture lexical this from final_class"
        );
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "C")),
            "raw decorated constructor metadata remains named"
        );
    }
    #[test]
    fn decorated_replacement_static_field_installs_on_raw_ctor_but_this_is_final_class() {
        let module = lower_js(
            "function replace() { return class R {}; } @replace class C { static x = this; }",
        );
        let code = module.functions()[module.entry().get() as usize].code();
        let constants = module.constants();
        let (raw_ctor, _) = class_raw_ctor_and_prototype(code, constants);
        let final_class = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::StoreGlobal { name, value } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value_name) if value_name.eq_ascii("C")
                )
                .then_some(*value),
                _ => None,
            })
            .expect("the decorated class declaration binds the replacement constructor");
        assert_ne!(
            raw_ctor, final_class,
            "class replacement must leave raw ctor and final class in distinct registers"
        );
        let (install_index, install_object) = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, key, .. }
                    if *object == raw_ctor && key_name(code, constants, *key) == "x" =>
                {
                    Some((index, *object))
                }
                _ => None,
            })
            .expect("static field x installs after decoration");
        assert_eq!(
            install_object, raw_ctor,
            "decorated replacement static fields own the raw constructor object"
        );
        assert!(
            code[..install_index].iter().any(|instruction| matches!(
                instruction,
                Instruction::Call { this_value, .. } if *this_value == final_class
            )),
            "static initializer-chain Call uses final_class as this before field install"
        );
    }
    #[test]
    fn instance_method_this_still_loads_activation_this() {
        let module = lower_js("class C { m() { return this; } }");
        assert!(
            module.functions().iter().any(|function| {
                function.name().is_none()
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::LoadThis { .. }))
            }),
            "instance this stays activation-loaded"
        );
    }
    #[test]
    fn export_default_named_class_keeps_raw_constructor_metadata() {
        let module = lower_js("export default class Named {}");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function_has_name(&module, function, "Named")),
            "export default class C still threads AST class.name into constructor metadata"
        );
    }
    #[test]
    fn computed_keys_and_decorator_expressions_keep_enclosing_this() {
        let computed = lower_js("class C { static [this] = 1; }");
        let computed_entry = &computed.functions()[computed.entry().get() as usize];
        assert!(
            computed_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "computed keys evaluate with enclosing this, not final_class"
        );
        let decorated = lower_js("function d(v) { return (x) => x; } @d(this) class C {}");
        let decorated_entry = &decorated.functions()[decorated.entry().get() as usize];
        assert!(
            decorated_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "decorator expressions evaluate with enclosing this, not final_class"
        );
        let static_this = lower_js("class C { static x = this; }");
        let static_entry = &static_this.functions()[static_this.entry().get() as usize];
        assert!(
            !static_entry
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadThis { .. })),
            "deferred static field this still captures final_class only"
        );
    }
    #[test]
    fn raise_type_error_is_a_bare_throw_without_constructor_lookup() {
        let module = lower_js("function dec() { return 42; } @dec class C {}");
        let constants = module.constants();
        let code = module.functions()[module.entry().get() as usize].code();
        let loads_type_error = |instructions: &[Instruction]| {
            instructions.iter().any(|instruction| match instruction {
                Instruction::LoadGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii("TypeError")
                ),
                _ => false,
            })
        };
        assert!(
            !loads_type_error(code),
            "decorator type errors must not resolve the TypeError global"
        );
        let function_type = code
            .iter()
            .position(|instruction| match instruction {
                Instruction::LoadConst { constant, .. } => matches!(
                    &constants[constant.get() as usize],
                    Constant::String(value) if value.eq_ascii("function")
                ),
                _ => false,
            })
            .expect("callable validation loads \"function\"");
        let error_path = &code[function_type..];
        let throw_pc = error_path
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("type error path calls the non-callable offender");
        let error_prefix = &error_path[..=throw_pc];
        assert!(
            !error_prefix
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Construct { .. })),
            "type error lowering must not construct a user-visible TypeError"
        );
        assert!(
            !loads_type_error(error_prefix),
            "type error lowering must not read the TypeError name"
        );
        assert!(
            !error_prefix
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Throw { .. })),
            "type error lowering uses a bare engine throw, not an explicit Throw of a constructed value"
        );
    }
    #[test]
    fn escaped_add_initializer_after_close_takes_type_error_path_not_append() {
        let module = lower_js(
            "let escaped; function dec(_value, context) { escaped = context.addInitializer; } @dec class C {}",
        );
        let constants = module.constants();
        let entry = module.functions()[module.entry().get() as usize].code();
        let helper = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 2
                    && function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. }))
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            })
            .expect("class context emits an addInitializer helper");
        let code = helper.code();
        let gate = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            .expect("open/closed gate");
        let Instruction::JumpIfFalse { target, .. } = code[gate] else {
            unreachable!();
        };
        let open_entry = target.get() as usize;
        let closed_arm = &code[gate + 1..open_entry];
        let open_arm = &code[open_entry..];
        assert!(
            closed_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Call { .. })),
            "closed arm calls a non-callable to throw an engine-origin TypeError"
        );
        assert!(
            !closed_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Construct { .. })),
            "closed arm must not construct a user-visible TypeError"
        );
        assert!(
            !closed_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::ArrayPush {
                    array,
                    ..
                } if array.get() == 0
            )),
            "closed arm must not append to the captured initializer queue (r0)"
        );
        assert!(
            !closed_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )),
            "closed state throws before callable validation"
        );
        assert!(
            open_arm.iter().any(|instruction| matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )),
            "open arm still validates that the callback is callable"
        );
        assert!(
            open_arm
                .iter()
                .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
            "open arm appends a callable callback"
        );
        let (cell, create_pc) = entry
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::CreateCell { dst } => {
                    let pushed = entry.iter().any(|candidate| {
                        matches!(
                            candidate,
                            Instruction::ArrayPush { value, .. } if value == dst
                        )
                    });
                    let closed = entry.iter().any(|candidate| match candidate {
                        Instruction::SetProperty { object, value, .. } if object == dst => {
                            entry.iter().any(|prior| {
                                matches!(
                                    prior,
                                    Instruction::LoadConst {
                                        dst: load_dst,
                                        constant,
                                    } if load_dst == value
                                        && matches!(
                                            &constants[constant.get() as usize],
                                            Constant::Boolean(true)
                                        )
                                )
                            })
                        }
                        _ => false,
                    });
                    (pushed && closed).then_some((*dst, index))
                }
                _ => None,
            })
            .expect("decoration state cell is captured and later closed");
        let push_pc = entry
            .iter()
            .position(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .expect("state cell is pushed into the helper captures array");
        let close_pc = entry
            .iter()
            .enumerate()
            .rev()
            .find_map(|(index, instruction)| match instruction {
                Instruction::SetProperty { object, value, .. } if *object == cell => entry
                    .iter()
                    .any(|prior| {
                        matches!(
                            prior,
                            Instruction::LoadConst { dst, constant }
                                if dst == value
                                    && matches!(
                                        &constants[constant.get() as usize],
                                        Constant::Boolean(true)
                                    )
                        )
                    })
                    .then_some(index),
                _ => None,
            })
            .expect("state cell is closed with true");
        let decorator_call = entry[create_pc..close_pc]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| create_pc + offset)
            .expect("class decorator applies while the queue is open");
        assert!(
            create_pc < push_pc && push_pc < decorator_call && decorator_call < close_pc,
            "shared state cell is captured before application and closed after it"
        );
    }

    #[test]
    fn class_decoration_state_cell_stores_false_before_decorator_call_and_true_after() {
        let module = lower_js(
            "let escaped; function dec(_value, context) { escaped = context.addInitializer; } @dec class C {}",
        );
        let constants = module.constants();
        let entry = module.functions()[module.entry().get() as usize].code();
        let store_positions = |cell: Register, expected: bool| {
            entry
                .iter()
                .enumerate()
                .filter_map(|(index, instruction)| match instruction {
                    Instruction::SetProperty { object, value, .. }
                        if *object == cell
                            && entry.iter().any(|candidate| {
                                matches!(
                                    candidate,
                                    Instruction::LoadConst { dst, constant }
                                        if *dst == *value
                                            && matches!(
                                                &constants[constant.get() as usize],
                                                Constant::Boolean(actual) if *actual == expected
                                            )
                                )
                            }) =>
                    {
                        Some(index)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let candidates: Vec<(Register, usize)> = entry
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::CreateCell { dst } => {
                    let captured = entry.iter().any(|candidate| {
                        matches!(candidate, Instruction::ArrayPush { value, .. } if value == dst)
                    });
                    (captured && !store_positions(*dst, true).is_empty()).then_some((*dst, index))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            candidates.len(),
            1,
            "the empty class has one captured, subsequently closed decoration state cell"
        );
        let (cell, create_pc) = candidates[0];
        let open_store = *store_positions(cell, false)
            .first()
            .expect("state cell is seeded open with false before any decorator runs");
        let close_store = *store_positions(cell, true)
            .last()
            .expect("state cell is closed with true");
        let capture_push = entry
            .iter()
            .position(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .expect("state cell is captured by the addInitializer helper");
        let decorator_call = entry[capture_push..close_store]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| capture_push + offset)
            .expect("class decorator is called while the state cell is open");
        assert!(
            create_pc < open_store && open_store < capture_push,
            "state cell is seeded after allocation and before helper capture"
        );
        assert!(
            open_store < decorator_call && decorator_call < close_store,
            "state cell is open for class decoration and closes afterwards"
        );
    }

    #[test]
    fn using_captures_disposer_before_binding_and_disposes_on_normal_exit() {
        let module = lower_js("{ using value = acquire(); consume(value); }");
        let code = module.functions()[0].code();
        let acquire = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("initializer evaluates once");
        let capture_offset = code[acquire..]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("capture follows evaluation");
        let captured = acquire + capture_offset;
        let (method, kind, src) = match code[captured] {
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint: bamts_bytecode::DisposeHint::Sync,
            } => (method, kind, src),
            _ => unreachable!(),
        };
        let body_call = code[captured + 1..]
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .map(|offset| captured + 1 + offset)
            .expect("body runs after capture");
        let disposal = code[body_call + 1..]
            .windows(2)
            .position(|window| {
                matches!(
                    &window[1],
                    Instruction::Call {
                        callee,
                        this_value,
                        ..
                    } if callee == &method && this_value == &src
                ) && matches!(&window[0], Instruction::CreateArray { .. })
            })
            .map(|offset| body_call + 1 + offset + 1)
            .expect("normal exit calls the captured method on the bound value");
        let skip = code[..disposal]
            .windows(2)
            .enumerate()
            .find_map(|(index, window)| match window {
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { condition, target },
                ] if left == &kind => Some((index + 1, *condition, target.get() as usize)),
                _ => None,
            })
            .expect("nullish kind equality feeds a JumpIfTrue skip");
        let (_jump_pc, _condition, target) = skip;
        assert!(
            target > disposal,
            "nullish kind jumps past the disposal call (polarity fixed)"
        );
        assert!(
            module.functions()[0]
                .handlers()
                .iter()
                .any(|handler| handler.start.get() <= (body_call as u32)
                    && handler.end.get() > body_call as u32),
            "body completion is captured for disposal"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposes_multiple_resources_in_lifo_order() {
        let module = lower_js("{ using outer = acquireOuter(); using inner = acquireInner(); }");
        let code = module.functions()[0].code();
        let captures = code
            .iter()
            .enumerate()
            .filter_map(|(pc, instruction)| match instruction {
                Instruction::DisposeCapture { method, src, .. } => Some((pc, *method, *src)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(captures.len(), 2, "each initializer captures one record");
        let outer_call = code
            .iter()
            .enumerate()
            .skip(captures[0].0 + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                    if callee == &captures[0].1 && this_value == &captures[0].2)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("outer disposal is emitted");
        let inner_call = code
            .iter()
            .enumerate()
            .skip(captures[1].0 + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                    if callee == &captures[1].1 && this_value == &captures[1].2)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("inner disposal is emitted");
        assert!(inner_call < outer_call, "records close innermost first");
        assert_round_trips(&module);
    }
    #[test]
    fn missing_sync_disposer_fails_during_capture_before_the_binding_is_used() {
        let module = lower_js("{ using missing = {}; trace(missing); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("missing disposer is validated eagerly by capture");
        let use_call = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .filter(|(_, instruction)| matches!(instruction, Instruction::Call { .. }))
            .map(|(pc, _)| pc)
            .next()
            .expect("the body would observe the binding if capture succeeded");
        assert!(
            capture < use_call,
            "capture runs before any body use, so its TypeError is declaration-time"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn await_using_in_async_function_captures_async_and_awaits_disposal() {
        let module =
            lower_js("async function f() { await using value = acquire(); consume(value); }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function is present");
        let code = function.code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Async,
                        ..
                    }
                )
            })
            .expect("await using captures with DisposeHint::Async");
        let (method, kind, src) = match code[capture] {
            Instruction::DisposeCapture {
                method,
                kind,
                src,
                hint: bamts_bytecode::DisposeHint::Async,
            } => (method, kind, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("async disposal still emits Call for non-nullish kinds");
        let await_pc = code
            .iter()
            .enumerate()
            .skip(disposal)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Await { .. } => Some(pc),
                _ => None,
            })
            .expect("async disposal awaits");
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= disposal && handler.end.get() as usize > await_pc
            })
            .expect("handler covers Call + Await");
        assert!(handler.start.get() as usize <= disposal);
        assert!(handler.end.get() as usize > await_pc);
        let _ = kind;
        assert_round_trips(&module);
    }

    #[test]
    fn await_using_in_sync_function_is_rejected() {
        let error = lower_js_result("function f() { await using value = acquire(); }")
            .expect_err("await using requires async capability");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::UsingDeclaration)
        );
    }

    #[test]
    fn await_using_at_module_top_level_captures_async() {
        let module = lower_js("await using value = acquire();");
        let code = module.functions()[0].code();
        assert!(
            code.iter().any(|instruction| matches!(
                instruction,
                Instruction::DisposeCapture {
                    hint: bamts_bytecode::DisposeHint::Async,
                    ..
                }
            )),
            "module top-level await using captures async"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_using_of_captures_per_iteration_and_disposes_before_next_step() {
        let module = lower_js("for (using value of xs) { consume(value); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Sync,
                        ..
                    }
                )
            })
            .expect("loop-head using captures per iteration");
        let next = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::IteratorNext { .. }))
            .expect("for-of steps the iterator");
        let jump_to_head = code
            .iter()
            .enumerate()
            .rev()
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Jump { target } if target.get() as usize <= next => Some(pc),
                _ => None,
            })
            .expect("loop jumps back to the head");
        assert!(
            capture < jump_to_head,
            "capture is inside the per-iteration body"
        );
        let disposal_call = code[capture..jump_to_head]
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }));
        assert!(
            disposal_call,
            "per-iteration disposal runs before the next iterator step"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_await_using_of_in_async_function_uses_async_capture() {
        let module =
            lower_js("async function f(xs) { for (await using value of xs) { consume(value); } }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function");
        assert!(
            function.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::DisposeCapture {
                    hint: bamts_bytecode::DisposeHint::Async,
                    ..
                }
            )),
            "loop-head await using captures with Async hint"
        );
        assert_round_trips(&module);
    }

    #[test]
    fn for_await_using_of_in_sync_function_is_rejected() {
        let error = lower_js_result("function f(xs) { for (await using value of xs) {} }")
            .expect_err("loop-head await using requires async capability");
        assert_eq!(
            error.kind,
            LowerErrorKind::Unsupported(UnsupportedConstruct::UsingDeclaration)
        );
    }

    #[test]
    fn async_disposal_awaits_undefined_on_nullish_and_sync_fallback_kinds() {
        let module = lower_js("async function f() { await using value = acquire(); }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_async)
            .expect("async function");
        let code = function.code();
        let capture = code
            .iter()
            .position(|instruction| {
                matches!(
                    instruction,
                    Instruction::DisposeCapture {
                        hint: bamts_bytecode::DisposeHint::Async,
                        ..
                    }
                )
            })
            .expect("async capture");
        let kind = match code[capture] {
            Instruction::DisposeCapture { kind, .. } => kind,
            _ => unreachable!(),
        };
        let kind_equals: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(pc, instruction)| match instruction {
                Instruction::Binary {
                    op: BinaryOp::StrictEqual,
                    left,
                    ..
                } if left == &kind => Some(pc),
                _ => None,
            })
            .collect();
        assert!(
            kind_equals.len() >= 2,
            "async disposal compares capture_kind for nullish skip-call and sync-fallback skip-copy"
        );
        let awaits_after_capture = code[capture..]
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Await { .. }))
            .count();
        assert_eq!(
            awaits_after_capture, 1,
            "formal pattern emits a single Await of the selected awaited register"
        );
        // Ensure kind==2 compare uses JumpIfTrue skip polarity (skip copy).
        let skip_copy = code.windows(2).any(|window| {
            matches!(
                window,
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { .. }
                ] if left == &kind
            )
        });
        assert!(skip_copy, "kind comparisons use JumpIfTrue skip polarity");
        assert_round_trips(&module);
    }

    #[test]
    fn using_close_disposal_sits_after_the_protected_body() {
        let module = lower_js("{ using value = acquire(); if (value) { trace(value); } }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .filter(|(_, instruction)| {
                matches!(instruction, Instruction::Call { callee, this_value, .. }
                if callee == &method && this_value == &src)
            })
            .map(|(pc, _)| pc)
            .next()
            .expect("disposal call is emitted once");
        assert!(
            module.functions()[0].handlers().iter().any(|handler| {
                handler.start.get() > capture as u32 && handler.end.get() as usize <= disposal
            }),
            "the protected body ends before disposal and its handler is disjoint"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposal_skips_nullish_kind_with_jump_if_true_polarity() {
        let module = lower_js("{ using value = acquire(); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let kind = match code[capture] {
            Instruction::DisposeCapture { kind, .. } => kind,
            _ => unreachable!(),
        };
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("non-nullish path still emits the disposer call");
        let (eq_pc, jump_pc, target) = code[..disposal]
            .windows(2)
            .enumerate()
            .find_map(|(index, window)| match window {
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        dst,
                        left,
                        ..
                    },
                    Instruction::JumpIfTrue { condition, target },
                ] if left == &kind && condition == dst => {
                    Some((index, index + 1, target.get() as usize))
                }
                _ => None,
            })
            .expect("capture_kind == 0 is tested with JumpIfTrue");
        assert!(eq_pc < jump_pc && jump_pc < disposal);
        assert!(
            target > disposal,
            "kind 0 must skip the disposer call, not enter it"
        );
        assert!(
            !matches!(code[jump_pc], Instruction::JumpIfFalse { .. }),
            "inverted JumpIfFalse polarity is the D1 bug"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn using_disposal_wraps_disposer_call_in_handler_and_emits_suppress_error() {
        let module = lower_js("{ using value = acquire(); consume(value); }");
        let code = module.functions()[0].code();
        let capture = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::DisposeCapture { .. }))
            .expect("resource is captured");
        let (method, src) = match code[capture] {
            Instruction::DisposeCapture { method, src, .. } => (method, src),
            _ => unreachable!(),
        };
        let disposal = code
            .iter()
            .enumerate()
            .skip(capture + 1)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Call {
                    callee, this_value, ..
                } if callee == &method && this_value == &src => Some(pc),
                _ => None,
            })
            .expect("disposal call is emitted");
        let dispose_handler = module.functions()[0]
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= disposal && handler.end.get() as usize > disposal
            })
            .expect("disposer Call is covered by an ExceptionHandler");
        assert!(
            dispose_handler.handler.get() as usize > disposal,
            "handler body is emitted after the disposer region"
        );
        let handler_pc = dispose_handler.handler.get() as usize;
        let catch_register = dispose_handler.catch_register;
        let suppress = code[handler_pc..]
            .iter()
            .enumerate()
            .find_map(|(offset, instruction)| match instruction {
                Instruction::SuppressError {
                    error, suppressed, ..
                } if error == &catch_register => Some((handler_pc + offset, *suppressed)),
                _ => None,
            })
            .expect("disposer failure path emits SuppressError");
        let (suppress_pc, suppressed) = suppress;
        assert_ne!(
            catch_register, suppressed,
            "SuppressError keeps the prior completion distinct from the disposer error"
        );
        let throw_guard = code[handler_pc..suppress_pc].windows(2).any(|window| {
            matches!(
                window,
                [
                    Instruction::Binary {
                        op: BinaryOp::StrictEqual,
                        ..
                    },
                    Instruction::JumpIfFalse { .. }
                ]
            )
        });
        assert!(
            throw_guard,
            "SuppressError is gated on the finally completion kind being THROW"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn debugger_statement_lowers_to_no_runtime_instruction() {
        let module = lower_js("debugger;");
        assert_eq!(module.functions()[0].code(), &[Instruction::Halt]);
    }
    #[test]
    fn invalid_labeled_jumps_fail_at_the_control_target_boundary() {
        for (source, operation) in [
            ("block: { break; }", "break target is not live"),
            (
                "block: { continue block; }",
                "continue target is not an iteration statement",
            ),
        ] {
            let error = lower_js_result(source).expect_err("invalid jump must not lower");
            assert_eq!(
                error.kind,
                LowerErrorKind::InvalidControlFlow { operation },
                "{source}"
            );
        }
    }
    #[test]
    fn lowering_preserves_lone_surrogate_escapes() {
        let module = lower_js("const lone = '\\uD800'; const face = '\\u{1F603}';");
        let strings: Vec<_> = module
            .constants()
            .iter()
            .filter_map(|constant| match constant {
                Constant::String(value) => Some(value.as_units()),
                _ => None,
            })
            .collect();
        assert!(strings.iter().any(|units| *units == [0xD800]));
        assert!(strings.iter().any(|units| *units == [0xD83D, 0xDE03]));
    }
    #[test]
    fn non_decimal_bigint_literals_lower_to_decimal_constants() {
        let module = lower_js(
            "const hex = 0x100000000000000000000000000000001n; \
             const octal = 0o20n; \
             const binary = 0b1_0000n;",
        );
        let bigints: Vec<_> = module
            .constants()
            .iter()
            .filter_map(|constant| match constant {
                Constant::BigInt(value) => Some(value.as_str()),
                _ => None,
            })
            .collect();
        assert!(bigints.contains(&"340282366920938463463374607431768211457"));
        assert!(bigints.contains(&"16"));
    }
    #[test]
    fn malformed_non_decimal_bigint_separator_fails_lowering() {
        let source = Arc::new(
            SourceText::new("const value = 0x1_n;".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        let error = lower(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
        )
        .expect_err("a trailing BigInt separator is invalid");
        assert_eq!(error.kind, LowerErrorKind::InvalidBigIntLiteral);
    }
    #[test]
    fn non_decimal_bigint_conversion_honors_output_limit() {
        assert_eq!(
            canonical_bigint_text("0xffn", 3, usize::MAX).as_deref(),
            Ok("255")
        );
        assert_eq!(
            canonical_bigint_text("0xffn", 2, usize::MAX),
            Err(BigIntTextError::Bytes)
        );
    }
    #[test]
    fn non_decimal_bigint_conversion_honors_work_limit() {
        assert_eq!(
            canonical_bigint_text("0xffffn", 5, 4).as_deref(),
            Ok("65535")
        );
        assert_eq!(
            canonical_bigint_text("0xffffn", 5, 3),
            Err(BigIntTextError::Work)
        );
    }
    #[test]
    fn non_decimal_bigint_conversion_matches_small_integer_values() {
        for value in 0_u32..4096 {
            let expected = value.to_string();
            for lexeme in [
                format!("0x{value:x}n"),
                format!("0o{value:o}n"),
                format!("0b{value:b}n"),
            ] {
                assert_eq!(
                    canonical_bigint_text(&lexeme, 16, usize::MAX).as_deref(),
                    Ok(expected.as_str()),
                    "{lexeme}"
                );
            }
        }
    }
    fn any_instruction(
        module: &Module<Verified>,
        predicate: impl Fn(&Instruction) -> bool,
    ) -> bool {
        module
            .functions()
            .iter()
            .flat_map(|function| function.code())
            .any(predicate)
    }
    #[test]
    fn checked_lowering_inlines_a_local_const_enum_member() {
        let source = Arc::new(
            SourceText::new("const enum K { X = 2, Y = X + 3 } K.Y;".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("checked const enum lowers");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
        )));
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 5.0
        )));
    }
    #[test]
    fn checked_lowering_inlines_const_enum_members_in_every_expression_context() {
        for (context, expression) in [
            ("bare member", "K.Y;"),
            ("binary operand", "K.Y + 1;"),
            ("call argument", "((value: number) => value)(K.Y);"),
            ("parenthesized member", "((K.Y));"),
        ] {
            let source = Arc::new(
                SourceText::new(format!("const enum K {{ X = 2, Y = X + 3 }} {expression}"))
                    .expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
            let checked = check(&parsed);
            let module = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect("checked const enum lowers in every expression context");
            assert!(
                !any_instruction(&module, |instruction| matches!(
                    instruction,
                    Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
                )),
                "{context} must not access `K` at runtime"
            );
            assert!(module.constants().iter().any(|constant| matches!(
                constant,
                Constant::Number(value) if value.to_f64() == 5.0
            )));
        }
        let source = Arc::new(
            SourceText::new("enum E { Literal = `literal`, Interpolated = `${1}` }".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("checked runtime enum lowers");
        let mappings = module
            .functions()
            .iter()
            .flat_map(|function| function.code())
            .filter(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            .count();
        assert_eq!(
            mappings, 2,
            "each string template member emits only a forward mapping"
        );
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::String(value) if value.as_units() == [108, 105, 116, 101, 114, 97, 108]
        )));
    }
    #[test]
    fn checked_lowering_inlines_const_enum_reads_but_rejects_member_callees() {
        let source = Arc::new(
            SourceText::new("const enum K { X = 2 } K.X; (K.X as number);".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("const enum reads lower");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::LoadGlobal { .. } | Instruction::GetProperty { .. }
        )));
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 2.0
        )));
        for (context, expression, operation) in [
            ("ordinary call", "K.X();", ConstEnumOperation::Read),
            ("parenthesized call", "(K.X)();", ConstEnumOperation::Read),
            (
                "asserted call",
                "(K.X as number)();",
                ConstEnumOperation::Read,
            ),
            (
                "optional call",
                "K.X?.();",
                ConstEnumOperation::OptionalAccess,
            ),
            (
                "parenthesized optional call",
                "(K.X as number)?.();",
                ConstEnumOperation::OptionalAccess,
            ),
            ("ordinary construct", "new K.X();", ConstEnumOperation::Read),
            (
                "parenthesized construct",
                "new (K.X)();",
                ConstEnumOperation::Read,
            ),
            (
                "asserted construct",
                "new (K.X as number)();",
                ConstEnumOperation::Read,
            ),
        ] {
            let source = Arc::new(
                SourceText::new(format!("const enum K {{ X = 2 }} {expression}"))
                    .expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
            let checked = check(&parsed);
            let error = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect_err("const enum member cannot be called or constructed");
            assert_eq!(
                error.kind,
                LowerErrorKind::ConstEnumOperation { operation },
                "{context}: {expression}"
            );
        }
    }
    #[test]
    fn checked_lowering_rejects_const_enum_member_write_and_delete() {
        for (source, operation) in [
            ("const enum K { X = 2 } K.X = 3;", ConstEnumOperation::Write),
            (
                "const enum K { X = 2 } delete K.X;",
                ConstEnumOperation::Delete,
            ),
            (
                "const enum K { X = 2 } K?.X;",
                ConstEnumOperation::OptionalAccess,
            ),
        ] {
            let source_text = Arc::new(
                SourceText::new(source.to_owned()).expect("test source fits the per-file budget"),
            );
            let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source_text));
            let checked = check(&parsed);
            let error = lower_checked(
                parsed.product(),
                LowerOptions {
                    javascript_compatibility: true,
                },
                checked.product().enum_facts(),
                checked.product().namespace_facts(),
            )
            .expect_err("const enum member mutation is rejected");
            assert_eq!(
                error.kind,
                LowerErrorKind::ConstEnumOperation { operation },
                "{source}"
            );
        }
    }
    fn lower_local_const_enum_mutation(source: &str) -> LowerError {
        let source = Arc::new(
            SourceText::new(source.to_owned()).expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect_err("const enum member mutation must fail during lowering")
    }
    fn lower_imported_const_enum_mutation(importer: &str, import_statement: usize) -> LowerError {
        let enum_file = parse(scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new("export const enum K { X = 2 }".to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let importer_file = parse(scan(
            SourceId::new(1),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(importer.to_owned()).expect("test source fits the per-file budget"),
            ),
        ));
        let files = [enum_file, importer_file];
        let import = files[1].product().statements()[import_statement].data();
        let crate::syntax::Statement::Import(import) = import else {
            panic!("declared import statement is an import");
        };
        let Some(crate::syntax::ImportBinding::Named(specifiers)) = import
            .clause
            .as_ref()
            .and_then(|clause| clause.binding.as_ref())
        else {
            panic!("const enum import is named");
        };
        let specifier = specifiers[0].id();
        let edges = [ResolvedModuleEdge {
            from: SourceId::new(1),
            specifier: files[1].product().statements()[import_statement].id(),
            to: SourceId::new(0),
        }];
        let checked = check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        );
        let facts = checked
            .product()
            .file(SourceId::new(1))
            .expect("program model contains importer");
        assert!(
            facts.enum_facts().is_elided_import_specifier(specifier),
            "invalid imported const-enum writes must not retain a runtime import"
        );
        lower_checked(
            files[1].product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            facts.enum_facts(),
            facts.namespace_facts(),
        )
        .expect_err("imported const enum member mutation must fail during lowering")
    }
    #[test]
    fn checked_lowering_rejects_local_const_enum_mutation_matrix() {
        for (operation, mutation, expected) in [
            ("assignment", "K.X = 3;", ConstEnumOperation::Write),
            (
                "compound assignment",
                "K.X += 3;",
                ConstEnumOperation::Write,
            ),
            ("prefix update", "++K.X;", ConstEnumOperation::Write),
            ("postfix update", "K.X++;", ConstEnumOperation::Write),
            (
                "nested assignment target",
                "({ value: K.X } = { value: 3 });",
                ConstEnumOperation::Write,
            ),
            ("delete", "delete K.X;", ConstEnumOperation::Delete),
        ] {
            for (site, source) in [
                ("top level", format!("const enum K {{ X = 2 }} {mutation}")),
                (
                    "nested function",
                    format!("const enum K {{ X = 2 }} function mutate() {{ {mutation} }}"),
                ),
                (
                    "pre-declaration",
                    format!("{mutation} const enum K {{ X = 2 }}"),
                ),
            ] {
                let error = lower_local_const_enum_mutation(&source);
                assert_eq!(
                    error.kind,
                    LowerErrorKind::ConstEnumOperation {
                        operation: expected
                    },
                    "{operation} at {site}: {source}"
                );
            }
        }
    }
    #[test]
    fn checked_lowering_rejects_imported_const_enum_mutation_matrix() {
        for (operation, mutation, expected) in [
            ("assignment", "K.X = 3;", ConstEnumOperation::Write),
            (
                "compound assignment",
                "K.X += 3;",
                ConstEnumOperation::Write,
            ),
            ("prefix update", "++K.X;", ConstEnumOperation::Write),
            ("postfix update", "K.X++;", ConstEnumOperation::Write),
            (
                "nested assignment target",
                "({ value: K.X } = { value: 3 });",
                ConstEnumOperation::Write,
            ),
            ("delete", "delete K.X;", ConstEnumOperation::Delete),
        ] {
            let import = "import { K } from './enum';";
            for (site, importer, import_statement) in [
                ("top level", format!("{import} {mutation}"), 0),
                (
                    "nested function",
                    format!("{import} function mutate() {{ {mutation} }}"),
                    0,
                ),
                ("pre-declaration", format!("{mutation} {import}"), 1),
            ] {
                let error = lower_imported_const_enum_mutation(&importer, import_statement);
                assert_eq!(
                    error.kind,
                    LowerErrorKind::ConstEnumOperation {
                        operation: expected
                    },
                    "{operation} at {site}: {importer}"
                );
            }
        }
    }
    #[test]
    fn checked_lowering_materializes_empty_exported_namespace_object() {
        let source = Arc::new(
            SourceText::new("export namespace N {}".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("empty exported namespace lowers");
        let code = module.functions()[module.entry().get() as usize].code();
        let create_object = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateObject { .. }))
            .expect("empty exported namespace materializes a runtime object");
        let export = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Export { .. }))
            .expect("empty exported namespace publishes a value export");
        assert!(
            create_object < export,
            "runtime container must exist before the value export is published"
        );
        let has_call = code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }));
        assert!(!has_call, "empty namespace does not evaluate an IIFE body");
        assert_round_trips(&module);
    }
    #[test]
    fn checked_lowering_retains_elided_const_enum_import_side_effect_without_binding() {
        let enum_source = "export let evaluated = 0; evaluated += 1; export const enum K { X = 1 }";
        let importer_source =
            "import { K, evaluated } from './enum_dep.ts'; const observed = K.X + evaluated;";
        let enum_file = parse(scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(enum_source.to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let importer_file = parse(scan(
            SourceId::new(1),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(importer_source.to_owned())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let files = [enum_file, importer_file];
        let import = files[1].product().statements()[0].data();
        let crate::syntax::Statement::Import(import) = import else {
            panic!("first importer statement is an import");
        };
        let Some(crate::syntax::ImportBinding::Named(specifiers)) = import
            .clause
            .as_ref()
            .and_then(|clause| clause.binding.as_ref())
        else {
            panic!("importer uses named bindings");
        };
        let elided = specifiers[0].id();
        let retained = specifiers[1].id();
        let edges = [ResolvedModuleEdge {
            from: SourceId::new(1),
            specifier: files[1].product().statements()[0].id(),
            to: SourceId::new(0),
        }];
        let checked = check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        );
        let facts = checked
            .product()
            .file(SourceId::new(1))
            .expect("program model contains importer");
        assert!(
            facts.enum_facts().is_elided_import_specifier(elided),
            "const-enum named binding is elided"
        );
        let retained_elided = facts.enum_facts().is_elided_import_specifier(retained);
        assert!(!retained_elided, "ordinary named binding is retained");
        let module = lower_checked(
            files[1].product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            facts.enum_facts(),
            facts.namespace_facts(),
        )
        .expect("elided const-enum import lowers");
        let code = module.functions()[module.entry().get() as usize].code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::Import { .. })),
            "direct checked-module lowering keeps Import for module evaluation"
        );
        let constants = module.constants();
        let reads_named = |export_name: &str| {
            code.iter().enumerate().any(|(index, instruction)| {
                let Instruction::GetProperty { key, .. } = instruction else {
                    return false;
                };
                code[..index].iter().rev().any(|prior| match prior {
                    Instruction::LoadConst { dst, constant } if dst == key => matches!(
                        &constants[constant.get() as usize],
                        Constant::String(value) if value.eq_ascii(export_name)
                    ),
                    _ => false,
                })
            })
        };
        let reads_k = reads_named("K");
        assert!(
            !reads_k,
            "elided const-enum specifier must not read a runtime export binding"
        );
        assert!(
            reads_named("evaluated"),
            "ordinary import bindings are still materialized"
        );
        let stores_global = |binding: &str| {
            code.iter().any(|instruction| match instruction {
                Instruction::StoreGlobal { name, .. } => matches!(
                    &constants[name.get() as usize],
                    Constant::String(value) if value.eq_ascii(binding)
                ),
                _ => false,
            })
        };
        let stores_k = stores_global("K");
        assert!(
            !stores_k,
            "elided const-enum specifier leaves no runtime local binding"
        );
        assert!(
            stores_global("evaluated"),
            "ordinary import bindings still install a runtime local"
        );
        assert!(module.constants().iter().any(|constant| matches!(
            constant,
            Constant::Number(value) if value.to_f64() == 1.0
        )));
        assert_round_trips(&module);
    }
    fn max_capture_count(module: &Module<Verified>) -> u32 {
        module
            .functions()
            .iter()
            .map(|function| function.capture_count())
            .max()
            .unwrap_or(0)
    }
    fn created_cell_used_as_capture(code: &[Instruction]) -> Option<Register> {
        code.iter().find_map(|instruction| {
            let Instruction::ArrayPush { array, value } = instruction else {
                return None;
            };
            if array == value {
                return None;
            }
            code.iter()
                .any(|candidate| {
                    matches!(
                        candidate,
                        Instruction::CreateArray { dst } | Instruction::CreateCell { dst }
                            if dst == value
                    )
                })
                .then_some(*value)
        })
    }
    fn cell_capture_pushes(code: &[Instruction], cell: Register) -> usize {
        code.iter()
            .filter(|instruction| {
                matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell)
            })
            .count()
    }
    fn cell_allocations(code: &[Instruction], cell: Register) -> usize {
        code.iter()
            .filter(|instruction| {
                matches!(
                    instruction,
                    Instruction::CreateArray { dst } | Instruction::CreateCell { dst }
                        if *dst == cell
                )
            })
            .count()
    }
    fn dormant_promotion_cell_blocks(code: &[Instruction]) -> usize {
        code.iter()
            .enumerate()
            .filter(|(entry, instruction)| {
                let Instruction::CreateArray { dst } = instruction else {
                    return false;
                };
                matches!(
                    code.get((*entry).saturating_sub(1)),
                    Some(Instruction::Jump { target }) if target.get() as usize == *entry + 2
                ) && matches!(
                    code.get(*entry + 1),
                    Some(Instruction::ArrayPush { array, value }) if array == dst && value == dst
                ) && !code.iter().any(|instruction| {
                    matches!(
                        instruction,
                        Instruction::Jump { target }
                            | Instruction::JumpIfTrue { target, .. }
                            | Instruction::JumpIfFalse { target, .. }
                            if target.get() as usize == *entry
                    )
                })
            })
            .count()
    }
    #[test]
    fn capture_keys_dedupe_live_containers_and_with_regions() {
        let name = String::from("value");
        let name_key = CaptureKey::Name(name.clone(), Vec::new());
        assert_eq!(name_key, CaptureKey::Name(name, Vec::new()));
        assert_eq!(
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            ),
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            )
        );
        assert_ne!(
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Enum,
                Register::new(3)
            ),
            CaptureKey::Container(
                crate::checker::SymbolId::new(0),
                ContainerKind::Namespace,
                Register::new(3)
            )
        );
        assert_ne!(
            CaptureKey::WithObject((1, 4), Register::new(5)),
            CaptureKey::WithObject((2, 6), Register::new(5))
        );
        let nested_function_captures = [
            CaptureKey::Name(String::from("value"), Vec::new()),
            CaptureKey::Container(
                crate::checker::SymbolId::new(1),
                ContainerKind::Namespace,
                Register::new(2),
            ),
            CaptureKey::WithObject((10, 20), Register::new(3)),
            CaptureKey::WithObject((11, 19), Register::new(4)),
        ];
        assert!(matches!(
            nested_function_captures.last(),
            Some(CaptureKey::WithObject((11, 19), object)) if *object == Register::new(4)
        ));
        let mut live_regions = nested_function_captures
            .iter()
            .filter_map(|capture| match capture {
                CaptureKey::WithObject(site, object) => Some((*site, *object)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            live_regions,
            [((10, 20), Register::new(3)), ((11, 19), Register::new(4))]
        );
        live_regions.pop();
        assert_eq!(live_regions, [((10, 20), Register::new(3))]);
        live_regions.clear();
        assert!(live_regions.is_empty());
    }
    #[test]
    fn outer_write_is_observed_by_a_captured_read() {
        let module = lower_js(
            "function outer() { let value = 0; const read = () => value; value = 1; return read; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                created_cell_used_as_capture(code).is_some()
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::SetProperty { .. }))
            })
            .expect("outer function owns the promoted binding");
        let cell = created_cell_used_as_capture(code).expect("cell is captured");
        assert!(code.iter().any(
            |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
        ));
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn inner_write_is_observed_by_the_outer_read() {
        let module = lower_js(
            "function outer() { let value = 0; const write = () => { value = 1; }; write(); return value; }",
        );
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == Register::new(0))
                )
        }));
        assert!(module.functions().iter().any(|function| {
            let code = function.code();
            created_cell_used_as_capture(code).is_some_and(|cell| {
                code.iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell)
                )
            })
        }));
    }
    #[test]
    fn assigned_local_cell_dominates_a_later_conditional_closure() {
        let module = lower_js(
            "function outer(flag) { let value = 0; value = 1; let read; if (flag) read = () => value; return value; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer function owns the captured cell");
        let cell = created_cell_used_as_capture(code).expect("cell is captured");
        let allocation = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
            )
            .expect("cell allocation is present");
        let conditional = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::JumpIfFalse { .. }))
            .expect("if statement branches");
        assert!(allocation < conditional);
        assert!(code[..conditional].iter().any(
            |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
        ));
    }
    #[test]
    fn assigned_parameter_uses_one_cell_before_later_method_capture() {
        let module = lower_js(
            "function mitt(all) { all = all || new Map(); return { read() { return all; } }; }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("mitt function owns the parameter cell");
        let cell = created_cell_used_as_capture(code).expect("parameter cell is captured");
        let allocation = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
            )
            .expect("parameter cell is allocated");
        let assignment = code
            .iter()
            .position(
                |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell),
            )
            .expect("parameter assignment stores through its cell");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("method closure is created");
        assert!(allocation < assignment && assignment < closure);
        assert_eq!(cell_allocations(code, cell), 1);
    }
    #[test]
    fn captured_parameter_cells_precede_default_initializer_closures() {
        for source in [
            "function f(a = () => a) { return a; }",
            "function f(make = () => later, later = 1) { return make; }",
            "function f(make = () => rest, ...rest) { return make; }",
            "function f({ value = () => value } = {}) { return value; }",
        ] {
            let module = lower_js(source);
            let owner = module
                .functions()
                .iter()
                .find(|function| created_cell_used_as_capture(function.code()).is_some())
                .expect("parameter owner materializes a captured default closure");
            let code = owner.code();
            let cell = created_cell_used_as_capture(code).expect("parameter cell is captured");
            let allocation = code
                .iter()
                .position(
                    |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                )
                .expect("parameter cell is allocated");
            let closure = code
                .iter()
                .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .expect("default initializer creates a closure");
            assert!(allocation < closure, "{source}");
            assert_eq!(cell_allocations(code, cell), 1, "{source}");
        }
    }
    #[test]
    fn declaration_owned_closures_capture_their_predeclared_cells() {
        for source in [
            "function outer() { const f = () => f; return f; }",
            "function outer() { function f() { return f; } return f; }",
            "function outer() { class C { self() { return C; } } return C; }",
            "function outer() { const { f = () => f } = {}; return f; }",
            "function outer() { const f = () => f; { const f = 1; } return f; }",
        ] {
            let module = lower_js(source);
            let owner = module
                .functions()
                .iter()
                .find(|function| created_cell_used_as_capture(function.code()).is_some())
                .expect("declaration owner materializes the captured cell");
            let code = owner.code();
            let cell = created_cell_used_as_capture(code).expect("cell is captured");
            let allocation = code
                .iter()
                .position(
                    |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                )
                .expect("captured cell is allocated");
            let closure = code
                .iter()
                .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .expect("declaration value creates a closure");
            assert!(allocation < closure, "{source}");
            assert_eq!(cell_allocations(code, cell), 1, "{source}");
            assert!(
                code[closure..].iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell)
                ),
                "the declaration stores its final value into the same cell: {source}"
            );
        }
    }
    #[test]
    fn safe_uncaptured_lexical_stays_in_a_register() {
        let module = lower_js("function outer() { const value = 1; return value; }");
        assert!(module.functions().iter().all(|function| {
            !function
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
        }));
    }
    #[test]
    fn captured_later_lexical_is_predeclared_once() {
        let module = lower_js(
            "function outer() { const read = () => later; const later = 1; return read; }",
        );
        let owner = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
            })
            .expect("owner predeclares the later lexical cell");
        assert_eq!(
            owner
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
                .count(),
            1
        );
        let cell = created_cell_used_as_capture(owner.code()).expect("closure captures the cell");
        assert_eq!(cell_allocations(owner.code(), cell), 1);
    }
    #[test]
    fn early_closure_read_uses_one_predeclared_cell_then_initializes_it() {
        let module = lower_js(
            "function outer() { const read = () => later; read(); let later = 1; return read(); }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer owns the captured later binding");
        let cell = created_cell_used_as_capture(code).expect("later binding is a cell");
        let create = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateCell { dst } if *dst == cell))
            .expect("cell is seeded at scope entry");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("reader closure is instantiated");
        let initialize = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell))
            .expect("declaration initializes the cell");
        assert!(create < closure && closure < initialize);
        assert_eq!(cell_allocations(code, cell), 1);
    }
    #[test]
    fn function_declaration_is_instantiated_once_before_executable_statements() {
        let module = lower_js(
            "function outer() { return declaredLater(); function declaredLater() { return 2; } }",
        );
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::Call { .. }))
            })
            .expect("outer function calls its declaration");
        let closure = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            .expect("function declaration is instantiated");
        let call = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Call { .. }))
            .expect("call is emitted");
        assert!(closure < call);
        assert_eq!(
            code.iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                .count(),
            1
        );
    }
    #[test]
    fn class_heritage_reads_its_own_uninitialized_cell() {
        let module = lower_js("function outer() { class C extends C {} return C; }");
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| {
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateCell { .. }))
            })
            .expect("class owner predeclares its binding");
        let cell = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::CreateCell { dst } => Some(*dst),
                _ => None,
            })
            .expect("class cell exists");
        let create = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::CreateCell { dst } if *dst == cell))
            .expect("class cell allocation");
        let heritage_read = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell))
            .expect("heritage reads through the class cell");
        let initialize = code
            .iter()
            .rposition(|instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == cell))
            .expect("class declaration initializes the same cell");
        assert!(create < heritage_read && heritage_read < initialize);
    }
    #[test]
    fn same_name_shadow_does_not_overbox_uncaptured_binding() {
        let module =
            lower_js("function outer() { let value = 1; { let value = 2; } return () => value; }");
        let code = module
            .functions()
            .iter()
            .map(|function| function.code())
            .find(|code| created_cell_used_as_capture(code).is_some())
            .expect("outer binding is captured");
        assert_eq!(
            code.iter()
                .filter(|instruction| matches!(
                    instruction,
                    Instruction::CreateArray { .. } | Instruction::CreateCell { .. }
                ))
                .count(),
            2,
            "only the captured binding cell and closure capture array allocate"
        );
        assert_eq!(dormant_promotion_cell_blocks(code), 0);
    }
    #[test]
    fn sibling_getter_and_setter_capture_the_same_cell() {
        let module = lower_js(
            "function outer() { let value = 0; const get = () => value; const set = (next) => { value = next; }; return [get, set]; }",
        );
        assert!(module.functions().iter().any(|function| {
            let code = function.code();
            created_cell_used_as_capture(code)
                .is_some_and(|cell| cell_capture_pushes(code, cell) == 2)
        }));
    }
    #[test]
    fn transitive_capture_passes_an_existing_cell_without_wrapping_it() {
        let module = lower_js("function outer() { let value = 1; return () => () => value; }");
        let middle = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            })
            .expect("middle closure materializes the inner closure");
        assert_eq!(
            middle
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateArray { .. }))
                .count(),
            1,
            "only the capture array is allocated; capture register zero is already a cell"
        );
        assert!(middle.code().iter().any(
            |instruction| matches!(instruction, Instruction::ArrayPush { value, .. } if *value == Register::new(0))
        ));
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && !function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn capture_of_capture_reads_and_reexports_the_same_cell() {
        let module = lower_js(
            "function outer() { let value = 1; return () => { value; return () => value; }; }",
        );
        let middle = module
            .functions()
            .iter()
            .find(|function| {
                function.capture_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            })
            .expect("middle closure reads and reexports the capture");
        assert!(middle.code().iter().any(
            |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
        ));
        assert_eq!(
            middle
                .code()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::CreateArray { .. }))
                .count(),
            1
        );
    }
    #[test]
    fn logical_assignment_reads_and_writes_cell_contents() {
        let module = lower_js(
            "function outer() { let optional = false; return (term) => { optional ||= term; }; }",
        );
        assert!(module.functions().iter().any(|function| {
            function.capture_count() == 1
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::GetProperty { object, .. } if *object == Register::new(0))
                )
                && function.code().iter().any(
                    |instruction| matches!(instruction, Instruction::SetProperty { object, .. } if *object == Register::new(0))
                )
        }));
    }
    #[test]
    fn classic_for_let_rebinds_but_for_var_reuses_its_cell() {
        let lexical = lower_js(
            "function outer() { const reads = []; for (let index = 0; index < 2; index++) reads.push(() => index); return reads; }",
        );
        let shared = lower_js(
            "function outer() { const reads = []; for (var index = 0; index < 2; index++) reads.push(() => index); return reads; }",
        );
        let lexical_allocations = lexical
            .functions()
            .iter()
            .find_map(|function| {
                let code = function.code();
                let cell = created_cell_used_as_capture(code)?;
                Some(cell_allocations(code, cell))
            })
            .expect("lexical loop captures its binding cell");
        let shared_allocations = shared
            .functions()
            .iter()
            .find_map(|function| {
                let code = function.code();
                let cell = created_cell_used_as_capture(code)?;
                Some(cell_allocations(code, cell))
            })
            .expect("var loop captures its binding cell");
        assert_eq!(lexical_allocations, 2, "let copies into a fresh cell");
        assert_eq!(shared_allocations, 1, "var retains one function cell");
        for module in [&lexical, &shared] {
            let code = module
                .functions()
                .iter()
                .map(|function| function.code())
                .find(|code| created_cell_used_as_capture(code).is_some())
                .expect("captured loop owns a cell");
            assert_eq!(
                dormant_promotion_cell_blocks(code),
                0,
                "captured loops contain no late-promotion scaffold"
            );
        }
    }
    #[test]
    fn uncaptured_ordinary_and_loop_locals_emit_no_cell_scaffolds() {
        let ordinary = lower_js("function outer(value) { let copy = value; return copy; }");
        let classic =
            lower_js("function outer(limit) { for (let index = 0; index < limit; index++) {} }");
        let iterator = lower_js("function outer(values) { for (let value of values) {} }");
        for (label, module) in [
            ("ordinary", &ordinary),
            ("classic", &classic),
            ("iterator", &iterator),
        ] {
            let entry = module.entry().get() as usize;
            let code = module
                .functions()
                .iter()
                .enumerate()
                .find(|(index, _)| *index != entry)
                .map(|(_, function)| function.code())
                .expect("snippet has one declared function");
            assert_eq!(dormant_promotion_cell_blocks(code), 0);
            assert!(
                !code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::CreateArray { .. })),
                "{label} local storage allocates no cell"
            );
            assert!(
                !code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
                "{label} local storage initializes no cell"
            );
        }
    }
    #[test]
    fn iterator_let_allocates_inside_the_loop_but_var_allocates_before_it() {
        fn allocation_and_step(module: &Module<Verified>) -> (usize, usize) {
            module
                .functions()
                .iter()
                .find_map(|function| {
                    let code = function.code();
                    let cell = created_cell_used_as_capture(code)?;
                    let allocation = code.iter().position(
                        |instruction| matches!(instruction, Instruction::CreateArray { dst } | Instruction::CreateCell { dst } if *dst == cell),
                    )?;
                    let step = code
                        .iter()
                        .position(|instruction| matches!(instruction, Instruction::IteratorNext { .. }))?;
                    Some((allocation, step))
                })
                .expect("iterator loop captures its declaration")
        }
        let lexical = lower_js(
            "function outer(values) { const reads = []; for (let value of values) reads.push(() => value); return reads; }",
        );
        let shared = lower_js(
            "function outer(values) { const reads = []; for (var value of values) reads.push(() => value); return reads; }",
        );
        let (lexical_allocation, lexical_step) = allocation_and_step(&lexical);
        let (shared_allocation, shared_step) = allocation_and_step(&shared);
        assert!(
            lexical_step < lexical_allocation,
            "let creates a new cell after each iterator step"
        );
        assert!(
            shared_allocation < shared_step,
            "var creates one cell before iterator stepping begins"
        );
    }
    #[test]
    fn computed_member_access_uses_a_register_key() {
        let module = lower_js("const o: any = {}; const k = \"a\"; const v = o[k];");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetProperty { .. }
        )));
    }
    #[test]
    fn spread_call_builds_an_arguments_array_with_extend() {
        let module = lower_js("declare const f: any; const xs = [1]; f(...xs);");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::ArrayExtend { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Call { .. }
        )));
    }
    #[test]
    fn nonempty_array_pushes_elements() {
        let module = lower_js("const a = [1, 2, 3];");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::ArrayPush { .. }
        )));
    }
    #[test]
    fn closure_capturing_a_local_emits_a_nonempty_capture() {
        let module = lower_js("function outer() { const x = 1; return () => x; }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateClosure { .. }
        )));
        assert!(max_capture_count(&module) >= 1, "the arrow captures `x`");
    }
    #[test]
    fn ordinary_function_declarations_materialize_own_prototypes() {
        let module = lower_js("function Base() {}");
        let code = module.functions()[0].code();
        let constants = module.constants();
        let key_name = |register: Register| -> String {
            let id = code
                .iter()
                .find_map(|instruction| match instruction {
                    Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no LoadConst defines key register {register:?}"));
            match &constants[id.get() as usize] {
                Constant::String(value) => value
                    .to_utf8_strict()
                    .expect("compiler-interned property key is well-formed UTF-16"),
                other => panic!("expected a string constant for the key, got {other:?}"),
            }
        };
        let (closure_index, closure) = code
            .iter()
            .enumerate()
            .find_map(|(index, instruction)| match instruction {
                Instruction::CreateClosure { dst, .. } => Some((index, *dst)),
                _ => None,
            })
            .expect("function declaration materializes a closure");
        let (prototype_index, prototype) = code[closure_index + 1..]
            .iter()
            .enumerate()
            .find_map(|(offset, instruction)| match instruction {
                Instruction::CreateObject { dst } => Some((closure_index + 1 + offset, *dst)),
                _ => None,
            })
            .expect("ordinary function gets an own prototype object");
        let constructor_key = code[prototype_index + 1..]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::SetProperty { object, key, value }
                    if *object == prototype && *value == closure =>
                {
                    Some(*key)
                }
                _ => None,
            })
            .expect("prototype.constructor is assigned the closure");
        assert_eq!(
            key_name(constructor_key),
            "constructor",
            "the reverse link is stored under the key \"constructor\""
        );
        let prototype_key = code[closure_index + 1..]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::SetProperty { object, key, value }
                    if *object == closure && *value == prototype =>
                {
                    Some(*key)
                }
                _ => None,
            })
            .expect("closure.prototype is assigned the prototype");
        assert_eq!(
            key_name(prototype_key),
            "prototype",
            "the forward link is stored under the key \"prototype\""
        );
    }
    #[test]
    fn lowering_marks_only_ecmascript_constructors_constructable() {
        let ordinary = lower_js("function Base() {}");
        assert_eq!(
            ordinary
                .functions()
                .iter()
                .filter(|function| function.flags().is_constructable)
                .count(),
            1,
            "the declaration is constructable and the module entry is not"
        );

        let mixed = lower_js("const arrow = () => 1; const object = { method() {} }; class C {}");
        assert_eq!(
            mixed
                .functions()
                .iter()
                .filter(|function| function.flags().is_constructable)
                .count(),
            1,
            "only the class constructor is constructable"
        );
    }
    #[test]
    fn template_literal_lowers_to_string_concatenation() {
        let module = lower_js("const a = 1; const s = `x${a}y`;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Binary {
                op: bamts_bytecode::BinaryOp::Add,
                ..
            }
        )));
    }
    #[test]
    fn for_of_lowers_to_the_iterator_protocol() {
        let module = lower_js("for (const v of [1, 2]) { globalThis; }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetIterator { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::IteratorNext { .. }
        )));
    }
    #[test]
    fn for_of_emits_an_iterator_close_cleanup() {
        let module = lower_js("for (const v of [1, 2]) { break; }");
        let code = module.functions()[0].code();
        assert!(any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::IteratorClose {
                mode: IteratorCloseMode::PreserveAbrupt,
                ..
            }
        )));
        let preserve_called = code
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::IteratorClose {
                    called,
                    mode: IteratorCloseMode::PreserveAbrupt,
                    ..
                } => Some(called),
                _ => None,
            })
            .expect("preserve close exists");
        assert!(
            !code.iter().any(|instruction| matches!(
                instruction,
                Instruction::RequireCloseResult { called, .. }
                    if called == preserve_called
            )),
            "preserve close never validates the return result"
        );
        assert!(
            code.windows(2).any(|window| {
                matches!(
                    (&window[0], &window[1]),
                    (
                        Instruction::IteratorClose {
                            result,
                            called,
                            mode: IteratorCloseMode::Propagate,
                            ..
                        },
                        Instruction::RequireCloseResult {
                            result: checked,
                            called: checked_called,
                        }
                    ) if result == checked && called == checked_called
                )
            }),
            "sync propagate close validates its raw result immediately"
        );
        assert!(!code.windows(2).any(|window| {
            matches!(
                (&window[0], &window[1]),
                (
                    Instruction::IteratorClose {
                        mode: IteratorCloseMode::PreserveAbrupt,
                        ..
                    },
                    Instruction::RequireCloseResult { .. }
                )
            )
        }));
        assert_round_trips(&module);
    }
    #[test]
    fn for_in_does_not_close_its_key_iterator() {
        let module = lower_js("for (const k in obj) { break; }");
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::IteratorClose { .. }
        )));
        assert_round_trips(&module);
    }
    #[test]
    fn for_await_awaits_the_close_result() {
        let module = lower_js("async function f() { for await (const x of xs) { break; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function.code().iter().any(|instruction| {
                    matches!(
                        instruction,
                        Instruction::IteratorClose {
                            mode: IteratorCloseMode::PreserveAbrupt,
                            ..
                        }
                    )
                })
            })
            .expect("async loop function has iterator cleanup");
        let code = function.code();
        let (preserve_called, preserve_await_pc) = code
            .windows(3)
            .enumerate()
            .find_map(|(pc, window)| match (&window[0], &window[1], &window[2]) {
                (
                    Instruction::IteratorClose {
                        result,
                        called,
                        mode: IteratorCloseMode::PreserveAbrupt,
                        ..
                    },
                    Instruction::Await { src, .. },
                    after,
                ) if result == src && !matches!(after, Instruction::RequireCloseResult { .. }) => {
                    Some((called, Pc::new(pc as u32 + 1)))
                }
                _ => None,
            })
            .expect("preserve close awaits without validating");
        assert!(
            !code.iter().any(|instruction| matches!(
                instruction,
                Instruction::RequireCloseResult { called, .. }
                    if called == preserve_called
            )),
            "preserve called flag is never consumed by close-result validation"
        );
        let propagate_close = code.windows(3).any(|window| {
            matches!(
                (&window[0], &window[1], &window[2]),
                (
                    Instruction::IteratorClose {
                        result,
                        called,
                        mode: IteratorCloseMode::Propagate,
                        ..
                    },
                    Instruction::Await { dst, src, .. },
                    Instruction::RequireCloseResult {
                        result: checked,
                        called: checked_called,
                    }
                ) if result == src && dst == checked && called == checked_called
            )
        });
        assert!(
            propagate_close,
            "async propagate validates the settled close result"
        );
        assert!(
            function.handlers().iter().any(|handler| {
                handler.start == preserve_await_pc
                    && handler.end.get() == preserve_await_pc.get() + 1
            }),
            "preserve rejection handler covers exactly one Await"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn for_of_cleanup_round_trips() {
        let module = lower_js(
            "function f(xs: any, ys: any) { outer: for (const x of xs) { for (const y of ys) { if (y) continue outer; if (x) break outer; return y; } } }",
        );
        assert_round_trips(&module);
    }
    #[test]
    fn object_destructuring_reads_named_properties() {
        let module = lower_js("declare const obj: any; const { a, b } = obj;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::GetProperty { .. }
        )));
    }
    #[test]
    fn regex_literal_lowers_to_create_regexp() {
        let module = lower_js("const r = /ab+c/gi;");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateRegExp { .. }
        )));
    }
    #[test]
    fn class_with_extends_builds_prototype_chain() {
        let module = lower_js("class B {} class C extends B { m() { return 1; } }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::SetPrototype { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreateClosure { .. }
        )));
    }
    fn instruction_indices(
        code: &[Instruction],
        predicate: impl Fn(&Instruction) -> bool,
    ) -> Vec<usize> {
        code.iter()
            .enumerate()
            .filter_map(|(index, instruction)| predicate(instruction).then_some(index))
            .collect()
    }
    fn super_construct_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::ConstructWithNewTarget { .. })
        })
    }
    fn first_super_construct_index(code: &[Instruction]) -> Option<usize> {
        super_construct_indices(code).first().copied()
    }
    fn first_create_cell_index(code: &[Instruction]) -> Option<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::CreateCell { .. })
        })
        .first()
        .copied()
    }
    fn calls_before_index(code: &[Instruction], bound: usize) -> Vec<usize> {
        plain_call_indices(code)
            .into_iter()
            .filter(|index| *index < bound)
            .collect()
    }
    fn first_call_after_index(code: &[Instruction], bound: usize) -> Option<usize> {
        plain_call_indices(code)
            .into_iter()
            .find(|index| *index > bound)
    }
    fn instance_field_init_after_super(
        code: &[Instruction],
        super_construct: usize,
        this_cell: Register,
    ) -> usize {
        instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { object, .. } if *object != this_cell
            )
        })
        .into_iter()
        .find(|index| *index > super_construct)
        .unwrap_or_else(|| panic!("derived field is initialized after super"))
    }
    fn plain_call_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::Call { .. })
        })
    }
    fn expect_one_index(label: &str, indices: Vec<usize>) -> usize {
        match indices.as_slice() {
            [index] => *index,
            [] => panic!("{label}: expected one match, found none"),
            _ => panic!("{label}: expected one match, found {indices:?}"),
        }
    }
    fn derived_constructor_function<'a>(
        module: &'a Module<Verified>,
        selector: impl Fn(&[Instruction]) -> bool,
        label: &'static str,
    ) -> &'a Function {
        module
            .functions()
            .iter()
            .find(|function| selector(function.code()))
            .unwrap_or_else(|| panic!("{label}"))
    }
    fn derived_constructor_with_super_count<'a>(
        module: &'a Module<Verified>,
        super_calls: usize,
        label: &'static str,
    ) -> &'a Function {
        derived_constructor_function(
            module,
            |code| {
                first_create_cell_index(code).is_some()
                    && super_construct_indices(code).len() == super_calls
                    && !code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::CreateClosure { .. }))
            },
            label,
        )
    }
    fn this_cell_register(code: &[Instruction]) -> Register {
        code.iter()
            .find_map(|instruction| match instruction {
                Instruction::CreateCell { dst } => Some(*dst),
                _ => None,
            })
            .expect("derived constructor creates its this cell")
    }
    fn assert_super_construct_operands(function: &Function, index: usize) {
        let code = function.code();
        let Instruction::ConstructWithNewTarget {
            callee,
            new_target,
            arguments,
            ..
        } = &code[index]
        else {
            panic!("instruction at {index} is not ConstructWithNewTarget");
        };
        assert!(
            callee.get() < function.capture_count(),
            "super construct callee is the parent-constructor capture"
        );
        assert!(
            code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::LoadNewTarget { dst } if *dst == *new_target
                )
            }),
            "super construct uses an explicit new.target operand"
        );
        assert!(
            code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::CreateArray { dst } if *dst == *arguments
                )
            }) || code[..index].iter().any(|instruction| {
                matches!(
                    instruction,
                    Instruction::ArrayExtend { array, .. } if *array == *arguments
                )
            }),
            "super construct receives a prepared arguments array operand"
        );
    }
    #[test]
    fn derived_constructor_places_fields_between_super_and_trailing_body() {
        let module = lower_js(
            "class Base {} class Derived extends Base { field = 1; constructor() { before(); super(); after(); } }",
        );
        let constructor = derived_constructor_function(
            &module,
            |code| super_construct_indices(code).len() == 1,
            "derived constructor constructs its parent with an explicit new.target",
        );
        let code = constructor.code();
        let super_construct = expect_one_index(
            "derived constructor constructs its parent with an explicit new.target",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let this_cell = this_cell_register(code);
        let before_call = expect_one_index(
            "before() remains a plain call",
            calls_before_index(code, super_construct),
        );
        let field = instance_field_init_after_super(code, super_construct, this_cell);
        let after_call = first_call_after_index(code, field)
            .expect("after() remains a plain call after field initialization");
        assert!(before_call < super_construct && super_construct < field && field < after_call);
    }
    #[test]
    fn implicit_derived_constructor_forwards_arguments_before_fields() {
        let module = lower_js("class Base {} class Derived extends Base { field = 1; }");
        let constructor = derived_constructor_function(
            &module,
            |code| {
                super_construct_indices(code).len() == 1
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::ArrayExtend { .. }))
            },
            "implicit derived constructor extends its arguments array",
        );
        let code = constructor.code();
        let super_construct = expect_one_index(
            "implicit derived constructor constructs its parent",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let this_cell = this_cell_register(code);
        let field = instance_field_init_after_super(code, super_construct, this_cell);
        assert!(super_construct < field);
    }
    #[test]
    fn derived_constructor_this_cell_matrix_lowers_without_shape_gating() {
        struct Case {
            source: &'static str,
            calls: usize,
            read_before_call: bool,
            read_after_call: bool,
        }
        for case in [
            Case {
                source: "class Base {} class Derived extends Base { constructor() { this.x; super(); } }",
                calls: 1,
                read_before_call: true,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() { this.x = 1; super(); } }",
                calls: 1,
                read_before_call: true,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor(flag) { if (flag) super(); } }",
                calls: 1,
                read_before_call: false,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() {} }",
                calls: 0,
                read_before_call: false,
                read_after_call: true,
            },
            Case {
                source: "class Base {} class Derived extends Base { constructor() { super(); this.x = 1; } }",
                calls: 1,
                read_before_call: false,
                read_after_call: true,
            },
        ] {
            let module = lower_js(case.source);
            let constructor = derived_constructor_with_super_count(
                &module,
                case.calls,
                "derived constructor matches its ConstructWithNewTarget count",
            );
            let code = constructor.code();
            let create_cell =
                first_create_cell_index(code).expect("derived constructor creates its this cell");
            let cell = this_cell_register(code);
            let super_calls = super_construct_indices(code);
            assert_eq!(super_calls.len(), case.calls, "{}", case.source);
            if case.calls == 1 {
                let super_construct = expect_one_index(
                    "derived constructor constructs its parent with ConstructWithNewTarget",
                    super_calls,
                );
                assert_super_construct_operands(constructor, super_construct);
            } else {
                assert!(
                    first_super_construct_index(code).is_none(),
                    "{}",
                    case.source
                );
            }
            let cell_reads_after_allocation: Vec<_> = instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { object, .. } if *object == cell)
            })
            .into_iter()
            .filter(|read| create_cell < *read)
            .collect();
            let this_reads_before_first_super = first_super_construct_index(code)
                .is_some_and(|call| cell_reads_after_allocation.iter().any(|read| *read < call));
            assert_eq!(
                this_reads_before_first_super, case.read_before_call,
                "{}",
                case.source
            );
            let last_super_anchor = first_super_construct_index(code)
                .or(super_construct_indices(code).last().copied())
                .unwrap_or(create_cell);
            assert_eq!(
                cell_reads_after_allocation
                    .iter()
                    .any(|read| *read > last_super_anchor),
                case.read_after_call,
                "{}",
                case.source
            );
        }
        let module = lower_js(
            "class Base {} class Derived extends Base { constructor(value, get = () => this) { super(); get().value = value; } }",
        );
        let constructor = derived_constructor_function(
            &module,
            |code| super_construct_indices(code).len() == 1,
            "default-parameter constructor constructs its parent with ConstructWithNewTarget",
        );
        let code = constructor.code();
        let cell = this_cell_register(code);
        assert_eq!(
            cell.get(),
            constructor.capture_count() + constructor.parameter_count(),
            "the this cell follows the initialized capture and parameter prefix"
        );
        let super_construct = expect_one_index(
            "default-parameter constructor constructs its parent",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_construct);
        let cell_creation = first_create_cell_index(code).expect("this cell creation is present");
        let cell_capture = expect_one_index(
            "default initializer arrow captures the this cell",
            instruction_indices(
                code,
                |instruction| matches!(instruction, Instruction::ArrayPush { value, .. } if *value == cell),
            ),
        );
        let closure_creation = expect_one_index(
            "default initializer creates its arrow",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::CreateClosure { .. })
            }),
        );
        assert!(cell_creation < cell_capture);
        assert!(cell_capture < closure_creation);
        assert!(closure_creation < super_construct);
    }
    #[test]
    fn derived_constructor_super_store_and_guard_are_adjacent() {
        let module =
            lower_js("class Base {} class Derived extends Base { constructor() { super(); } }");
        let constructor = derived_constructor_with_super_count(
            &module,
            1,
            "derived constructor constructs its parent with ConstructWithNewTarget",
        );
        let code = constructor.code();
        let constants = module.constants();
        let super_pc = expect_one_index(
            "derived constructor constructs its parent with ConstructWithNewTarget",
            super_construct_indices(code),
        );
        assert_super_construct_operands(constructor, super_pc);
        let Instruction::ConstructWithNewTarget {
            dst: construct_dst, ..
        } = &code[super_pc]
        else {
            panic!("instruction at {super_pc} is not ConstructWithNewTarget");
        };
        let construct_dst = *construct_dst;
        let cell_store_pc = expect_one_index(
            "super result is stored into the this cell",
            instruction_indices(code, |instruction| {
                matches!(
                    instruction,
                    Instruction::SetProperty { value, .. } if *value == construct_dst
                )
            })
            .into_iter()
            .filter(|index| *index > super_pc)
            .collect(),
        );
        let Instruction::SetProperty {
            object: this_cell, ..
        } = &code[cell_store_pc]
        else {
            panic!("instruction at {cell_store_pc} is not SetProperty");
        };
        let this_cell = *this_cell;
        let true_load_pc = expect_one_index(
            "derived super guard loads the boolean true constant",
            instruction_indices(code, |instruction| {
                matches!(
                    instruction,
                    Instruction::LoadConst { constant, .. }
                        if matches!(constants[constant.get() as usize], Constant::Boolean(true))
                )
            })
            .into_iter()
            .filter(|index| *index > cell_store_pc)
            .collect(),
        );
        let Instruction::LoadConst { dst: true_src, .. } = &code[true_load_pc] else {
            panic!("instruction at {true_load_pc} is not LoadConst");
        };
        let true_src = *true_src;
        let guard_move_pc = expect_one_index(
            "derived super guard moves the true constant into the guard register",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::Move { src, .. } if *src == true_src)
            })
            .into_iter()
            .filter(|index| *index > true_load_pc)
            .collect(),
        );
        assert!(
            super_pc < cell_store_pc
                && cell_store_pc < true_load_pc
                && true_load_pc < guard_move_pc,
            "super construct, this-cell store, true load, and guard move must be ordered"
        );
        for (offset, instruction) in code[super_pc + 1..guard_move_pc].iter().enumerate() {
            let pc = super_pc + 1 + offset;
            let violation = matches!(
                instruction,
                Instruction::Call { .. }
                    | Instruction::Construct { .. }
                    | Instruction::ConstructWithNewTarget { .. }
                    | Instruction::GetProperty { .. }
            ) || matches!(
                instruction,
                Instruction::SetProperty { object, .. } if *object != this_cell
            );
            assert!(
                !violation,
                "instruction at {pc} between super construct and guard move is not an allowed compiler-only op: {instruction:?}"
            );
        }
    }
    #[test]
    fn private_field_creates_a_private_name() {
        let module = lower_js("class C { #x = 1; read() { return this.#x; } }");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::CreatePrivateName { .. }
        )));
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::LoadThis { .. }
        )));
    }
    #[test]
    fn generator_sets_the_flag_and_suspends() {
        let module = lower_js("function* g() { yield 1; yield 2; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_generator)
        );
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Suspend { .. }
        )));
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "yield never emits the await opcode"
        );
    }
    #[test]
    fn generator_suspend_emits_inline_throw_and_return_dispatch() {
        let module = lower_js("function* g() { yield 1; }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("generator suspends");
        let Instruction::Suspend {
            dst, resume, mode, ..
        } = code[suspend_pc]
        else {
            unreachable!()
        };
        assert_ne!(
            dst, mode,
            "resume value and completion mode use distinct registers"
        );
        let resume_pc = resume.get() as usize;
        assert_eq!(
            resume_pc,
            suspend_pc + 1,
            "resume enters the inline dispatch"
        );

        let Instruction::LoadConst {
            dst: throw_marker,
            constant: throw_constant,
        } = code[resume_pc]
        else {
            panic!("throw mode marker is loaded first")
        };
        assert_eq!(
            module.constants()[throw_constant.get() as usize],
            Constant::Int32(RESUME_THROW)
        );
        let Instruction::Binary {
            dst: throw_matches,
            op: BinaryOp::StrictEqual,
            left: throw_left,
            right: throw_right,
        } = code[resume_pc + 1]
        else {
            panic!("throw mode is tested inline")
        };
        assert_eq!((throw_left, throw_right), (mode, throw_marker));
        let Instruction::JumpIfFalse {
            condition: throw_condition,
            target: after_throw,
        } = code[resume_pc + 2]
        else {
            panic!("throw guard skips the abrupt arm")
        };
        assert_eq!(throw_condition, throw_matches);
        assert_eq!(after_throw.get() as usize, resume_pc + 4);
        assert_eq!(code[resume_pc + 3], Instruction::Throw { value: dst });

        let Instruction::LoadConst {
            dst: return_marker,
            constant: return_constant,
        } = code[resume_pc + 4]
        else {
            panic!("return mode marker follows throw dispatch")
        };
        assert_eq!(
            module.constants()[return_constant.get() as usize],
            Constant::Int32(RESUME_RETURN)
        );
        let Instruction::Binary {
            dst: return_matches,
            op: BinaryOp::StrictEqual,
            left: return_left,
            right: return_right,
        } = code[resume_pc + 5]
        else {
            panic!("return mode is tested inline")
        };
        assert_eq!((return_left, return_right), (mode, return_marker));
        let Instruction::JumpIfFalse {
            condition: return_condition,
            target: after_return,
        } = code[resume_pc + 6]
        else {
            panic!("return guard skips the abrupt arm")
        };
        assert_eq!(return_condition, return_matches);
        assert_eq!(after_return.get() as usize, resume_pc + 8);
        assert_eq!(code[resume_pc + 7], Instruction::Return { value: dst });
        assert_round_trips(&module);
    }

    #[test]
    fn generator_throw_resume_dispatch_stays_inside_try_handler() {
        let module = lower_js("function* g() { try { yield 1; } catch (e) { yield e; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("try body suspends");
        let Instruction::Suspend { dst, resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let throw_pc = code
            .iter()
            .enumerate()
            .skip(resume.get() as usize)
            .find_map(|(pc, instruction)| match instruction {
                Instruction::Throw { value } if *value == dst => Some(pc),
                _ => None,
            })
            .expect("resume throw arm");
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .expect("try handler covers the suspension");
        assert!(
            handler.start.get() as usize <= resume.get() as usize
                && handler.end.get() as usize > throw_pc,
            "resume entry and Throw remain inside the protected range"
        );
    }

    #[test]
    fn generator_return_bypasses_catch_and_routes_to_finally() {
        let module = lower_js(
            "function* g() { try { yield 1; } catch (e) { sink(e); } finally { sink(2); } }",
        );
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("try body suspends");
        let Instruction::Suspend { resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let handler = function
            .handlers()
            .iter()
            .find(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .expect("try handler");
        let return_route = code[resume.get() as usize + 7..handler.end.get() as usize]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::Jump { target } => Some(*target),
                _ => None,
            })
            .expect("return routes out of the protected body");
        assert_ne!(
            return_route, handler.handler,
            "return completion must not enter the catch clause"
        );
        assert!(
            return_route.get() >= handler.end.get(),
            "return completion targets the finalizer after the protected range"
        );
    }

    #[test]
    fn nested_generator_return_routes_through_each_finally() {
        let module = lower_js(
            "function* g() { try { try { yield 1; } finally { sink(1); } } finally { sink(2); } }",
        );
        let function = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("generator function");
        let code = function.code();
        let suspend_pc = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::Suspend { .. }))
            .expect("nested try body suspends");
        let Instruction::Suspend { dst, resume, .. } = code[suspend_pc] else {
            unreachable!()
        };
        let mut enclosing: Vec<_> = function
            .handlers()
            .iter()
            .filter(|handler| {
                handler.start.get() as usize <= suspend_pc
                    && handler.end.get() as usize > suspend_pc
            })
            .collect();
        enclosing.sort_by_key(|handler| handler.end.get() - handler.start.get());
        let [inner, outer] = enclosing.as_slice() else {
            panic!("the suspension is protected by two nested handlers")
        };
        let return_body = resume.get() as usize + 7;
        assert!(
            code[return_body..inner.end.get() as usize].iter().any(
                |instruction| matches!(instruction, Instruction::Move { src, .. } if *src == dst)
            ),
            "return value is recorded in the innermost finally frame"
        );
        let inner_route = code[return_body..inner.end.get() as usize]
            .iter()
            .find_map(|instruction| match instruction {
                Instruction::Jump { target } => Some(*target),
                _ => None,
            })
            .expect("return routes to inner finalizer");
        assert!(
            inner_route.get() >= inner.end.get() && inner_route.get() < outer.end.get(),
            "inner finalizer runs while still inside the outer protected range"
        );
        assert!(
            code[inner_route.get() as usize..outer.end.get() as usize]
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Jump { target } if target.get() >= outer.end.get())),
            "inner finalizer dispatch preserves return and routes to the outer finalizer"
        );
    }

    #[test]
    fn async_await_uses_the_await_opcode() {
        let module = lower_js("async function f(p: any) { return await p; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_async)
        );
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::Await { .. }
        )));
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "await never emits the yield opcode"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn async_generator_distinguishes_await_from_yield() {
        let module = lower_js("async function* g(p: any) { const v = await p; yield v; }");
        assert!(
            module
                .functions()
                .iter()
                .any(|function| function.flags().is_async && function.flags().is_generator)
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "the await operand suspends with Await"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "the produced item yields with Suspend"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn for_await_splits_step_await_result() {
        let module = lower_js("async function f(xs: any) { for await (const v of xs) { v; } }");
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorStep { .. })),
            "the async iterator is stepped for its raw result"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "the raw iterator result is awaited"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorResult { .. })),
            "the settled iterator result yields done/value"
        );
        assert!(
            !any_instruction(&module, |i| matches!(i, Instruction::IteratorNext { .. })),
            "async loops never use the fused sync step"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn async_generator_yield_star_delegates_through_the_async_protocol() {
        let module = lower_js("async function* g(xs: any) { yield* xs; }");
        assert!(
            any_instruction(&module, |i| matches!(
                i,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the delegated iterator is acquired through Symbol.asyncIterator"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::IteratorStep { .. })),
            "each delegated step is acquired as a raw result"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Await { .. })),
            "raw delegated results are awaited before unpacking"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Suspend { .. })),
            "delegated values yield through the generator suspension"
        );
        assert!(
            any_instruction(&module, |i| matches!(i, Instruction::Call { .. })),
            "abrupt completions forward through delegated iterator methods"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn sync_generator_inside_async_function_keeps_sync_yield_star() {
        let module = lower_js(
            "async function f() { const g = function* (xs: any) { yield* xs; }; return g; }",
        );
        let generator = module
            .functions()
            .iter()
            .find(|function| function.flags().is_generator)
            .expect("nested generator lowers");
        assert!(
            generator.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::GetIterator {
                    kind: IteratorKind::Sync,
                    ..
                }
            )),
            "a sync generator's yield* stays on Symbol.iterator"
        );
        assert!(
            !generator.code().iter().any(|instruction| matches!(
                instruction,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the enclosing async function must not leak into the nested generator"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn yield_star_allows_a_newline_before_the_delegated_operand() {
        let module = lower_js("async function* g(f: any) { yield*\n f(); }");
        assert!(
            any_instruction(&module, |i| matches!(
                i,
                Instruction::GetIterator {
                    kind: IteratorKind::Async,
                    ..
                }
            )),
            "the newline form still lowers as async delegation"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn free_names_load_from_the_environment() {
        let module = lower_js("const keys = Object.keys({});");
        assert!(any_instruction(&module, |i| matches!(
            i,
            Instruction::LoadGlobal { .. }
        )));
    }
    #[test]
    fn try_finally_routes_completions_through_the_finalizer() {
        let module = lower_js(
            "function f(x: any) { while (x) { try { return 1; } finally { x = 0; } } return 2; }",
        );
        // A handler is registered and the finalizer runs before the return.
        assert!(
            module
                .functions()
                .iter()
                .any(|function| !function.handlers().is_empty())
        );
        assert_round_trips(&module);
    }
    #[test]
    fn optional_member_call_skips_arguments_and_preserves_receiver() {
        let key_is_method = |code: &[Instruction], constants: &[Constant], register: Register| {
            let constant = code
                .iter()
                .find_map(|instruction| match instruction {
                    Instruction::LoadConst { dst, constant } if *dst == register => Some(constant),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("no LoadConst defines property key {register:?}"));
            match &constants[constant.get() as usize] {
                Constant::String(value) => {
                    value.to_utf8_strict().is_ok_and(|value| value == "method")
                }
                _ => false,
            }
        };
        let assert_optional_call = |src: &str, expect_method_jump: bool| {
            let module = lower_js(src);
            let code = module.functions()[0].code();
            let constants = module.constants();
            let (member_index, callee, object) = code
                .iter()
                .enumerate()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::GetProperty { dst, object, key }
                        if key_is_method(code, constants, *key) =>
                    {
                        Some((index, *dst, *object))
                    }
                    _ => None,
                })
                .expect("optional member call loads its method");
            let (call_index, call_dst, this_value) = code
                .iter()
                .enumerate()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::Call {
                        dst,
                        callee: call_callee,
                        this_value,
                        ..
                    } if *call_callee == callee => Some((index, *dst, *this_value)),
                    _ => None,
                })
                .expect("optional member call invokes the loaded method");
            assert_eq!(
                this_value, object,
                "the call keeps the member object as this"
            );
            let result_move_index = code[call_index + 1..]
                .iter()
                .enumerate()
                .find_map(|(offset, instruction)| match instruction {
                    Instruction::Move { src, .. } if *src == call_dst => {
                        Some(call_index + 1 + offset)
                    }
                    _ => None,
                })
                .expect("the call result is moved into a shared result register");
            let merge = result_move_index + 1;
            let (object_jump_index, object_jump_target) = code[..member_index]
                .iter()
                .enumerate()
                .rev()
                .find_map(|(index, instruction)| match instruction {
                    Instruction::JumpIfTrue { condition, target }
                        if code[..index].iter().any(|prior| {
                            matches!(
                                prior,
                                Instruction::Binary { dst, op: BinaryOp::Equal, left, .. }
                                    if *dst == *condition && *left == object
                            )
                        }) =>
                    {
                        Some((index, *target))
                    }
                    _ => None,
                })
                .expect("optional object test branches before the member read");
            assert!(
                code[object_jump_index + 1..call_index]
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::Call { .. })),
                "the argument side effect is emitted before the member call"
            );
            assert_eq!(
                object_jump_target.get() as usize,
                merge,
                "the object-nullish branch jumps to the instruction after the result assignment"
            );
            if expect_method_jump {
                let method_jump_target = code[member_index + 1..call_index]
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(offset, instruction)| {
                        let index = member_index + 1 + offset;
                        match instruction {
                            Instruction::JumpIfTrue { condition, target }
                                if code[member_index + 1..index].iter().any(|prior| {
                                    matches!(
                                        prior,
                                        Instruction::Binary { dst, op: BinaryOp::Equal, left, .. }
                                            if *dst == *condition && *left == callee
                                    )
                                }) =>
                            {
                                Some(target)
                            }
                            _ => None,
                        }
                    })
                    .expect("optional method test branches before the call");
                assert_eq!(
                    method_jump_target.get() as usize,
                    merge,
                    "the method-nullish branch jumps to the same merge point"
                );
            }
        };
        assert_optional_call(
            "declare const obj: any; declare function side_effect(): number; obj?.method(side_effect());",
            false,
        );
        assert_optional_call(
            "declare const obj: any; declare function side_effect(): number; obj?.method?.(side_effect());",
            true,
        );
    }
    #[test]
    fn arrow_rest_loads_the_activations_own_arguments() {
        // `(...options) => options` must collect the arrow invocation's own
        let module = lower_js("const collect = (...options) => options; collect(1, 2);");
        let entry = module.entry().get() as usize;
        let arrow = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, _)| *index != entry)
            .map(|(_, function)| function)
            .expect("the arrow is the sole non-entry function");
        let code = arrow.code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the arrow body loads its own activation arguments for rest"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::GetIterator { .. })),
            "rest collection iterates the loaded arguments"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::ArrayPush { .. })),
            "rest collection pushes into the rest array"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn regular_function_rest_with_fixed_parameters_loads_arguments() {
        let module = lower_js("function f(a, ...rest) { return rest; }");
        let entry = module.entry().get() as usize;
        let function = module
            .functions()
            .iter()
            .enumerate()
            .find(|(index, _)| *index != entry)
            .map(|(_, function)| function)
            .expect("the regular function is the sole non-entry function");
        let code = function.code();
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the function loads its own arguments for rest"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::GetIterator { .. })),
            "rest collection iterates the loaded arguments"
        );
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::IteratorNext { .. })),
            "the fixed parameter is discarded by stepping the iterator"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn arrow_lexical_arguments_is_captured_not_loaded() {
        let module = lower_js("function outer() { const read = () => arguments; return read(); }");
        let arrow = module
            .functions()
            .iter()
            .find(|function| function.capture_count() >= 1)
            .expect("the arrow captures `arguments` from outer");
        assert!(
            !arrow
                .code()
                .iter()
                .any(|instruction| matches!(instruction, Instruction::LoadArguments { .. })),
            "the arrow reads `arguments` from its capture, not its own activation"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn dynamic_import_lowers_a_computed_specifier_once_before_options() {
        let module = lower_js("import('./left' + pick(), effects());");
        let code = module.functions()[0].code();
        let binary_positions: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                matches!(
                    instruction,
                    Instruction::Binary {
                        op: BinaryOp::Add,
                        ..
                    }
                )
                .then_some(index)
            })
            .collect();
        assert_eq!(
            binary_positions.len(),
            1,
            "the computed specifier expression is lowered once"
        );
        let call_positions: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                matches!(instruction, Instruction::Call { .. }).then_some(index)
            })
            .collect();
        assert_eq!(call_positions.len(), 2);
        let import_dynamic = code
            .iter()
            .position(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
            .expect("import(expr) emits ImportDynamic");
        assert!(binary_positions[0] > call_positions[0]);
        assert!(binary_positions[0] < call_positions[1]);
        assert!(call_positions[1] < import_dynamic);
        assert_round_trips(&module);
    }
    #[test]
    fn dynamic_import_lowers_a_literal_specifier_through_import_dynamic() {
        let module = lower_js("import('./dep.js');");
        assert!(any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::ImportDynamic { .. }
        )));
        assert!(!any_instruction(&module, |instruction| matches!(
            instruction,
            Instruction::Import { .. }
        )));
        assert_round_trips(&module);
    }
    fn assert_round_trips(module: &Module<Verified>) {
        let bytes = module.encode();
        decode_verified(&bytes, &DecodeLimits::default())
            .expect("a verified module re-decodes and re-verifies");
    }
    #[test]
    fn synthetic_functions_allocate_captures_before_parameters() {
        use super::{Binding, DeclarationScope, FunctionContext, ModuleBuilder};
        use crate::enum_plan::EnumFacts;
        use crate::namespace_plan::NamespaceFacts;
        let source =
            Arc::new(SourceText::new("".to_owned()).expect("test source fits the per-file budget"));
        let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
        let parsed = parse(scanned);
        let file = parsed.product();
        let enum_facts = EnumFacts::unchecked();
        let namespace_facts = NamespaceFacts::unchecked();
        let mut builder = ModuleBuilder {
            source: file.source_id(),
            constants: Vec::new(),
            functions: Vec::new(),
        };
        let mut context = FunctionContext::new_top_level(
            file,
            None,
            super::LoweringGoal::Module,
            &enum_facts,
            &namespace_facts,
            namespace_facts.symbols(),
        );
        let range = file.range();
        // Enclosing state the synthetic closure captures by value: one named
        // cell and the class-definition element table.
        let seed = context.alloc_register(range).expect("register");
        context.declare(
            "seed".to_owned(),
            Binding::Cell(seed),
            DeclarationScope::Function,
        );
        let table = context.alloc_register(range).expect("register");
        context
            .emit(range, Instruction::CreateArray { dst: table })
            .expect("emit");
        let captures = [
            CaptureKey::Name("seed".to_owned(), Vec::new()),
            CaptureKey::ClassElements(table),
        ];
        let closure = context
            .build_synthetic_function(
                &mut builder,
                range,
                None,
                &captures,
                2,
                |inner, _, parameters| {
                    assert_eq!(parameters, &[Register::new(2), Register::new(3)]);
                    assert_eq!(inner.class_elements, Some(Register::new(1)));
                    let sum = inner.alloc_register(range)?;
                    inner.emit(
                        range,
                        Instruction::Binary {
                            dst: sum,
                            op: BinaryOp::Add,
                            left: parameters[0],
                            right: parameters[1],
                        },
                    )?;
                    Ok(sum)
                },
            )
            .expect("synthetic function lowers");
        let functions: Vec<_> = builder
            .functions
            .iter()
            .map(|slot| slot.as_ref().expect("filled"))
            .collect();
        assert_eq!(functions.len(), 1);
        let generated = functions[0];
        assert_eq!(generated.capture_count(), 2);
        assert_eq!(generated.parameter_count(), 2);
        assert_eq!(
            generated.code().last(),
            Some(&Instruction::Return {
                value: Register::new(4)
            }),
            "every synthetic function has exactly one trailing return"
        );
        let enclosing = context.code;
        let tail = &enclosing[enclosing.len() - 4..];
        assert!(
            matches!(tail[0], Instruction::CreateArray { .. })
                && matches!(
                    tail[1],
                    Instruction::ArrayPush { value, .. } if value == seed
                )
                && matches!(
                    tail[2],
                    Instruction::ArrayPush { value, .. } if value == table
                )
                && matches!(
                    tail[3],
                    Instruction::CreateClosure { dst, .. } if dst == closure
                ),
            "captures materialize by value in capture order: {tail:?}"
        );
    }

    // ------------------------------------------------------------------
    // Sloppy `with` lowering contracts
    // ------------------------------------------------------------------
    fn entry_code(module: &Module<Verified>) -> &[Instruction] {
        module.functions()[module.entry().get() as usize].code()
    }
    fn with_has_binding_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::WithHasBinding { .. })
        })
    }
    fn to_object_indices(code: &[Instruction]) -> Vec<usize> {
        instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::ToObject { .. })
        })
    }
    #[test]
    fn with_statement_lowers_object_once_through_to_object() {
        let module = lower_js("with (o) { x; }");
        let code = entry_code(&module);
        let to_objects = to_object_indices(code);
        assert_eq!(
            to_objects.len(),
            1,
            "exactly one ToObject for the with object"
        );
        let membership = with_has_binding_indices(code);
        assert!(!membership.is_empty(), "free name consults with membership");
        assert!(
            to_objects[0] < membership[0],
            "ToObject precedes membership tests"
        );
        assert_round_trips(&module);
    }
    #[test]
    fn with_identifier_read_tests_membership_before_global_fallback() {
        let module = lower_js("with (o) { x; }");
        let code = entry_code(&module);
        let membership = expect_one_index("WithHasBinding", with_has_binding_indices(code));
        let get = expect_one_index(
            "GetProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            }),
        );
        let loads = instruction_indices(code, |instruction| {
            matches!(instruction, Instruction::LoadGlobal { .. })
        });
        let fallback = loads
            .iter()
            .copied()
            .find(|&index| index > get)
            .expect("unmatched path falls back to LoadGlobal after GetProperty");
        assert!(
            membership < get && get < fallback,
            "membership before GetProperty before fallback LoadGlobal: {membership} < {get} < {fallback}"
        );
    }
    #[test]
    fn with_body_lexical_declaration_shadows_the_with_object() {
        // Top-level `let` lowers through StoreGlobal without a local scope binding,
        // so exercise the lexical shadow inside a function body.
        let module = lower_js("function f(o) { with (o) { let x = 1; x; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::ToObject { .. }))
            })
            .expect("function containing with");
        assert!(
            with_has_binding_indices(function.code()).is_empty(),
            "body let beats with: no WithHasBinding for x"
        );
        assert_eq!(to_object_indices(function.code()).len(), 1);
    }
    #[test]
    fn with_shadows_an_outer_var() {
        let module = lower_js("function f(o) { var x = 1; with (o) { x; } }");
        let function = module
            .functions()
            .iter()
            .find(|function| {
                function
                    .code()
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::WithHasBinding { .. }))
            })
            .expect("function body emits WithHasBinding for outer var");
        assert_eq!(
            with_has_binding_indices(function.code()).len(),
            1,
            "outer var is shadowed by with"
        );
    }
    #[test]
    fn nested_with_regions_test_innermost_object_first() {
        let module = lower_js("with (a) { with (b) { x; } }");
        let code = entry_code(&module);
        let to_objects: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::ToObject { dst, .. } => Some((index, *dst)),
                _ => None,
            })
            .collect();
        assert_eq!(to_objects.len(), 2, "outer and inner ToObject");
        let inner_to_object_at = to_objects[1].0;
        let outer_object = to_objects[0].1;
        let inner_object = to_objects[1].1;
        // Object expr of the inner with may consult the outer region; the body
        // read of `x` starts after the inner ToObject and walks innermost-first.
        let membership: Vec<_> = code
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| match instruction {
                Instruction::WithHasBinding { object, .. } if index > inner_to_object_at => {
                    Some(*object)
                }
                _ => None,
            })
            .collect();
        assert_eq!(membership.len(), 2, "body read probes both regions");
        assert_eq!(
            membership[0], inner_object,
            "innermost WithHasBinding comes first"
        );
        assert_eq!(membership[1], outer_object, "outer WithHasBinding follows");
    }
    #[test]
    fn with_simple_assignment_resolves_put_value_after_rhs() {
        // Literal RHS: no pre-RHS target freeze; membership is only for PutValue.
        let module = lower_js("with (o) { x = 2; }");
        let code = entry_code(&module);
        let to_object = expect_one_index("ToObject", to_object_indices(code));
        let membership = with_has_binding_indices(code);
        assert_eq!(membership.len(), 1, "PutValue alone probes membership");
        assert!(
            to_object < membership[0],
            "object coercion precedes PutValue"
        );
        let write = instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { .. } | Instruction::StoreGlobal { .. }
            )
        })
        .into_iter()
        .find(|&index| index > membership[0])
        .expect("write follows PutValue membership");
        assert!(membership[0] < write);
    }
    #[test]
    fn with_compound_assignment_reresolves_put_value_after_rhs() {
        // GetValue before RHS, PutValue after — two membership walks around the
        // arithmetic (literal RHS avoids extra free-name probes).
        let module = lower_js("with (o) { x += 1; }");
        let code = entry_code(&module);
        let membership = with_has_binding_indices(code);
        assert_eq!(
            membership.len(),
            2,
            "compound assignment re-resolves PutValue after GetValue"
        );
        let binary = expect_one_index(
            "Binary",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::Binary { .. })
            }),
        );
        assert!(
            membership[0] < binary && binary < membership[1],
            "read membership < compute < write membership"
        );
    }
    #[test]
    fn with_update_reresolves_put_value_after_getvalue() {
        let module = lower_js("with (o) { x++; }");
        let code = entry_code(&module);
        let membership = with_has_binding_indices(code);
        assert_eq!(
            membership.len(),
            2,
            "update GetValue and PutValue each probe membership"
        );
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            })
            .len(),
            1
        );
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::SetProperty { .. })
            })
            .len(),
            1
        );
        assert!(membership[0] < membership[1]);
    }
    #[test]
    fn with_assignment_put_value_matches_node_after_rhs_delete() {
        // Instruction-order stand-in for Node's
        // `var outer=0; const o={x:1}; with(o){x=(delete o.x,2)}`
        // → globalThis.x=2. RHS delete completes before PutValue membership.
        let module = lower_js("with (o) { x = (delete o.x, 2); }");
        let code = entry_code(&module);
        let delete_at = expect_one_index(
            "DeleteProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::DeleteProperty { .. })
            }),
        );
        let put_membership = with_has_binding_indices(code)
            .into_iter()
            .find(|&index| index > delete_at)
            .expect("PutValue WithHasBinding follows the RHS delete");
        let write_after = instruction_indices(code, |instruction| {
            matches!(
                instruction,
                Instruction::SetProperty { .. } | Instruction::StoreGlobal { .. }
            )
        })
        .into_iter()
        .any(|index| index > put_membership);
        assert!(
            write_after,
            "PutValue emits a write after the re-resolved membership test"
        );
    }
    #[test]
    fn with_typeof_falls_back_to_type_of_global() {
        let module = lower_js("with (o) { typeof x; }");
        let code = entry_code(&module);
        assert_eq!(with_has_binding_indices(code).len(), 1);
        assert!(any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::TypeOfGlobal { .. })
        }));
        assert!(any_instruction(&module, |instruction| {
            matches!(
                instruction,
                Instruction::Unary {
                    op: UnaryOp::TypeOf,
                    ..
                }
            )
        }));
        assert!(
            !instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            })
            .is_empty()
        );
    }
    #[test]
    fn with_delete_targets_the_with_object() {
        let module = lower_js("with (o) { delete x; }");
        let code = entry_code(&module);
        assert_eq!(with_has_binding_indices(code).len(), 1);
        assert_eq!(
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::DeleteProperty { .. })
            })
            .len(),
            1
        );
    }
    #[test]
    fn with_method_call_receives_the_with_object_as_this() {
        let module = lower_js("with (o) { m(); }");
        let code = entry_code(&module);
        let get = expect_one_index(
            "GetProperty",
            instruction_indices(code, |instruction| {
                matches!(instruction, Instruction::GetProperty { .. })
            }),
        );
        let call = expect_one_index("Call", plain_call_indices(code));
        let Instruction::GetProperty { object: base, .. } = code[get] else {
            panic!("expected GetProperty");
        };
        let Instruction::Call { this_value, .. } = code[call] else {
            panic!("expected Call");
        };
        assert_eq!(
            this_value, base,
            "matched identifier call uses with object as this"
        );
    }
    #[test]
    fn closure_in_with_body_captures_the_region_and_dispatches_after_exit() {
        let module = lower_js("with (o) { g = function () { return x; }; }");
        assert!(any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::CreateClosure { .. })
        }));
        // Entry also freezes `g` for the assignment; the nested function is the
        // one that both probes membership and reads through GetProperty.
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                let code = function.code();
                code.iter()
                    .any(|instruction| matches!(instruction, Instruction::WithHasBinding { .. }))
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::GetProperty { .. }))
                    && code
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("nested function consults captured with region");
        assert_eq!(with_has_binding_indices(inner.code()).len(), 1);
    }
    #[test]
    fn closure_captured_outer_binding_still_consults_with_region() {
        let module =
            lower_js("function f(o) { var x = 1; with (o) { return function () { return x; }; } }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function.code().iter().any(|instruction| {
                        matches!(instruction, Instruction::WithHasBinding { .. })
                    })
            })
            .expect("closure over outer var inside with still emits WithHasBinding");
        assert!(
            inner
                .code()
                .iter()
                .any(|instruction| { matches!(instruction, Instruction::GetProperty { .. }) })
        );
    }
    #[test]
    fn closure_with_body_lexical_capture_shadows_object_property() {
        // Lexical `x` declared inside the with body must win over a same-named
        // property on the with object once captured into a nested closure.
        let module =
            lower_js("function f(o) { with (o) { let x = 1; return function () { return x; }; } }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("closure capturing with-body lexical");
        assert!(
            with_has_binding_indices(inner.code()).is_empty(),
            "captured with-body lexical must not consult the with object property"
        );
    }
    #[test]
    fn nested_closures_propagate_captured_name_with_sites() {
        // Middle frame restores `x` at scope 0 beside the captured with region.
        // Innermost must still inherit site provenance through that boundary —
        // `floor < scope_depth` alone is not enough for captured names.
        let module = lower_js(
            "function f(o) { var x = 1; with (o) { return function () { return function () { return x; }; }; } }",
        );
        let innermost = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 0
                    && function.code().iter().any(|instruction| {
                        matches!(instruction, Instruction::WithHasBinding { .. })
                    })
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::GetProperty { .. }))
            })
            .expect("two-level nested closure must still consult captured with region");
        assert!(
            !with_has_binding_indices(innermost.code()).is_empty(),
            "captured-name with sites must propagate across nested closures"
        );
    }
    #[test]
    fn closure_parameter_shadows_a_captured_with_region() {
        let module = lower_js("with (o) { g = function (x) { return x; }; }");
        let inner = module
            .functions()
            .iter()
            .find(|function| {
                function.parameter_count() == 1
                    && function
                        .code()
                        .iter()
                        .any(|instruction| matches!(instruction, Instruction::Return { .. }))
            })
            .expect("nested function with parameter");
        assert!(
            inner
                .code()
                .iter()
                .all(|instruction| !matches!(instruction, Instruction::WithHasBinding { .. })),
            "child parameter shadows captured with region"
        );
    }
    #[test]
    fn with_object_expression_cannot_see_its_own_region() {
        let module = lower_js("with (o) { with (x) {} }");
        let code = entry_code(&module);
        let membership = expect_one_index("WithHasBinding", with_has_binding_indices(code));
        let to_objects = to_object_indices(code);
        assert_eq!(to_objects.len(), 2);
        assert!(
            membership < to_objects[1],
            "membership for x precedes the inner ToObject"
        );
    }
    #[test]
    fn with_statement_round_trips() {
        let module = lower_js("with (o) { x = 1; x++; typeof x; delete x; m(); }");
        assert_round_trips(&module);
    }
    #[test]
    fn identifier_read_outside_with_emits_no_membership_test() {
        let module = lower_js("x;");
        assert!(!any_instruction(&module, |instruction| {
            matches!(instruction, Instruction::WithHasBinding { .. })
        }));
    }
    #[test]
    fn with_body_error_still_pops_region() {
        let error = lower_js_result("with (o) { return; }").expect_err("top-level return");
        assert!(matches!(error.kind, LowerErrorKind::ReturnOutsideFunction));
    }

    #[test]
    fn ambient_string_module_lowers_to_empty_module() {
        let module = lower_js("declare module \"pkg\" { export const x: number; }");
        let entry = &module.functions()[module.entry().get() as usize];
        let has_runtime = entry.code().iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::CreateObject { .. }
                    | Instruction::StoreGlobal { .. }
                    | Instruction::Call { .. }
            )
        });
        assert!(
            !has_runtime,
            "ambient string modules must erase to no runtime container work: {:?}",
            entry.code()
        );
    }

    #[test]
    fn identifier_namespace_still_lowers_iife_container() {
        let source = Arc::new(
            SourceText::new("namespace N { export const x = 1 }".to_owned())
                .expect("test source fits the per-file budget"),
        );
        let parsed = parse(scan(SourceId::new(0), ScriptKind::TypeScript, source));
        let checked = check(&parsed);
        let module = lower_checked(
            parsed.product(),
            LowerOptions {
                javascript_compatibility: true,
            },
            checked.product().enum_facts(),
            checked.product().namespace_facts(),
        )
        .expect("identifier namespace lowers with namespace facts");
        assert!(
            any_instruction(&module, |instruction| matches!(
                instruction,
                Instruction::CreateObject { .. }
            )),
            "identifier namespaces must keep runtime lowering"
        );
    }
}
