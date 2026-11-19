//! Compiler-owned frontend orchestration.
//!
//! [`compile_frontend`] drives the fixed scan -> parse -> check -> optional emit
//! pipeline over one source and returns a single recovered [`FrontendOutput`].
//! The pipeline never stops on user diagnostics: every stage always yields a
//! product, and their diagnostics are unioned into one canonically ordered,
//! duplicate-free vector without losing any distinct severity, range, or code.
//!
//! This module owns no filesystem, CLI, lowerer, runtime, or backend. It only
//! composes the existing scanner, parser, checker, and emitter surfaces.

use bamts_cancel::{CancellationToken, Cancelled};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::checker::diagnostic_messages::{Args, by_u32};
use crate::checker::{self, ProgramCheckInput, ResolvedModuleEdge, SemanticModel};
use crate::diagnostic::{Diagnostic, DiagnosticCode, Recovered};
use crate::emitter::transforms::ModuleExports;
use crate::emitter::{self, EmitFileNames, EmitOptions, EmitOutput};
use crate::lint::{LintProfile, LintTable};
use crate::parser;
use crate::program::{
    JsxRoutingDecision, ModuleEdge, ModuleTarget, ProgramOutputKind, ResolvedModule,
    ResolvedProgram,
};
use crate::scanner;
use crate::source::{ScriptKind, SourceId, SourceText};
use crate::syntax::{
    ExportDeclaration, ExportNamedDeclaration, NamespaceName, SourceFile, Statement, Stmt,
};
use crate::telemetry::{Phase, Telemetry};

/// An import nothing satisfies, in `tsc`'s own numbering.
const CANNOT_FIND_MODULE: DiagnosticCode = DiagnosticCode::new("TS2307");

struct EdgeNode {
    id: crate::syntax::NodeId,
    range: crate::source::TextRange,
    children: Vec<Self>,
}

struct SourceEdgeNodeIndex {
    exact: std::collections::HashMap<crate::source::TextRange, crate::syntax::NodeId>,
    roots: Vec<EdgeNode>,
}

impl SourceEdgeNodeIndex {
    fn new(source: &SourceFile) -> Self {
        let mut exact = std::collections::HashMap::new();
        let roots = Self::statements(source.statements(), &mut exact);
        Self { exact, roots }
    }

    fn statements(
        statements: &[crate::syntax::Stmt],
        exact: &mut std::collections::HashMap<crate::source::TextRange, crate::syntax::NodeId>,
    ) -> Vec<EdgeNode> {
        statements
            .iter()
            .map(|statement| Self::statement(statement, exact))
            .collect()
    }

    fn statement(
        statement: &crate::syntax::Stmt,
        exact: &mut std::collections::HashMap<crate::source::TextRange, crate::syntax::NodeId>,
    ) -> EdgeNode {
        use crate::syntax::{ExportDefaultValue, ExternalModuleReference, FunctionBody, Statement};

        let id = statement.id();
        match statement.data() {
            Statement::Import(import) => {
                exact.insert(import.source.range(), id);
            }
            Statement::ImportEquals(import) => {
                if let ExternalModuleReference::Require(source) = &import.reference {
                    exact.insert(source.range(), id);
                }
            }
            Statement::Export(ExportDeclaration::All(export)) => {
                exact.insert(export.source.range(), id);
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                source: Some(source),
                ..
            })) => {
                exact.insert(source.range(), id);
            }
            _ => {}
        }

        let children = match statement.data() {
            Statement::Function(function) => match &function.function.body {
                Some(FunctionBody::Block(block)) => {
                    Self::statements(&block.data().statements, exact)
                }
                _ => Vec::new(),
            },
            Statement::Namespace(namespace) => {
                Self::statements(&namespace.body.data().statements, exact)
            }
            Statement::Declare(inner)
            | Statement::Labeled(crate::syntax::LabeledStatement { body: inner, .. }) => {
                vec![Self::statement(inner, exact)]
            }
            Statement::Block(block) => Self::statements(&block.data().statements, exact),
            Statement::If(branch) => {
                let mut children = vec![Self::statement(&branch.consequent, exact)];
                if let Some(alternate) = &branch.alternate {
                    children.push(Self::statement(alternate, exact));
                }
                children
            }
            Statement::Switch(switch) => switch
                .cases
                .iter()
                .flat_map(|case| Self::statements(&case.data().consequent, exact))
                .collect(),
            Statement::For(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::ForIn(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::ForOf(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::While(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::DoWhile(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::Try(statement) => {
                let mut children = Self::statements(&statement.block.data().statements, exact);
                if let Some(handler) = &statement.handler {
                    children.extend(Self::statements(
                        &handler.data().body.data().statements,
                        exact,
                    ));
                }
                if let Some(finalizer) = &statement.finalizer {
                    children.extend(Self::statements(&finalizer.data().statements, exact));
                }
                children
            }
            Statement::With(statement) => vec![Self::statement(&statement.body, exact)],
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => vec![Self::statement(inner, exact)],
            Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
                ExportDefaultValue::Function(function) => match &function.body {
                    Some(FunctionBody::Block(block)) => {
                        Self::statements(&block.data().statements, exact)
                    }
                    _ => Vec::new(),
                },
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };

        debug_assert!(
            children
                .windows(2)
                .all(|pair| pair[0].range.end() <= pair[1].range.start()),
            "edge node children must be source-ordered and non-overlapping"
        );

        EdgeNode {
            id,
            range: statement.range(),
            children,
        }
    }

    fn node_for(&self, range: crate::source::TextRange) -> Option<crate::syntax::NodeId> {
        self.exact
            .get(&range)
            .copied()
            .or_else(|| Self::smallest_containing(&self.roots, range))
    }

    fn smallest_containing(
        nodes: &[EdgeNode],
        range: crate::source::TextRange,
    ) -> Option<crate::syntax::NodeId> {
        let index = nodes.partition_point(|node| node.range.start() <= range.start());
        let node = nodes.get(index.checked_sub(1)?)?;
        (node.range.end() >= range.end())
            .then(|| Self::smallest_containing(&node.children, range).unwrap_or(node.id))
    }
}

/// The frontend product a caller wants produced for one source.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FrontendMode {
    /// Scan, parse, and type-check only; no emit is produced.
    Check,
    /// Additionally emit runtime JavaScript with type-only syntax erased.
    JavaScript,
    /// Additionally emit a TypeScript declaration file.
    Declaration,
}

impl FrontendMode {
    /// Returns the emit options this mode requests, or `None` for check-only.
    #[must_use]
    pub fn emit_options(self) -> Option<EmitOptions> {
        match self {
            Self::Check => None,
            Self::JavaScript => Some(EmitOptions::default()),
            Self::Declaration => Some(EmitOptions {
                declaration: true,
                emit_declaration_only: true,
                ..EmitOptions::default()
            }),
        }
    }
}

fn dependencies_of(program: &ResolvedProgram, source_id: SourceId) -> &[ModuleEdge] {
    program
        .module(source_id)
        .map_or(&[], |module| module.dependencies())
}

/// The local module an edge's names come from; types may resolve apart.
fn edge_target(edge: &ModuleEdge) -> Option<SourceId> {
    edge.type_target()
        .unwrap_or_else(|| edge.target())
        .local_source_id()
}

fn local_dependency(
    program: &ResolvedProgram,
    source_id: SourceId,
    specifier: &str,
) -> Option<SourceId> {
    dependencies_of(program, source_id)
        .iter()
        .find(|edge| edge.specifier() == specifier)
        .and_then(edge_target)
}

fn program_emit_options(
    program: &ResolvedProgram,
    mode: FrontendMode,
    module_index: usize,
) -> Option<EmitOptions> {
    let mut options = mode.emit_options()?;

    // Shared mapping: target, always_strict, module. The program carries the
    // resolved strict-family and es5 flags through `check_options()`; mapping
    // them here through `apply_emit_fields` — the same method the project
    // (CLI) path uses — ensures the lane and the CLI cannot diverge on
    // downleveling or the strict-mode prologue.
    let check = program.check_options();
    let target = check.target();
    let always_strict = check.always_strict();
    let module = program.emit_module_kind(module_index);
    options.apply_emit_fields(
        target,
        always_strict,
        module,
        program.use_define_for_class_fields(),
        program.import_helpers(),
    );
    options.es_module_interop = program.es_module_interop().unwrap_or(true);
    options.node_module_mode = program.is_node_module_mode();
    options.experimental_decorators = program.experimental_decorators();
    options.emit_decorator_metadata = program.emit_decorator_metadata();
    options.no_emit_helpers = check.no_emit_helpers();
    options.remove_comments = check.remove_comments();
    options.verbatim_module_syntax = program.verbatim_module_syntax();
    options.source_map = program.source_map();
    options.inline_source_map = program.inline_source_map();
    options.inline_sources = program.inline_sources();

    // JSX routing is JavaScript-specific and already shared with the CLI path,
    // which applies the same overrides from `program.jsx()` after its base
    // `emit_options` call.
    if mode == FrontendMode::JavaScript {
        match program.jsx_routing_decision(ProgramOutputKind::JavaScript) {
            JsxRoutingDecision::Emit | JsxRoutingDecision::TransformAndEmit => {
                options.jsx = program.jsx();
                options.jsx_factory = program.jsx_factory().map(Arc::from);
                options.jsx_fragment_factory = program.jsx_fragment_factory().map(Arc::from);
                options.jsx_import_source = program.jsx_import_source().map(Arc::from);
            }
            JsxRoutingDecision::Lower | JsxRoutingDecision::RejectPreservedNative => {
                unreachable!("JavaScript output never selects a native JSX route");
            }
        }
    }
    Some(options)
}

/// One immutable frontend compilation request.
#[derive(Clone, Debug)]
pub struct FrontendRequest {
    /// The compilation-assigned identity of the source.
    pub source_id: SourceId,
    /// The syntax accepted for the source.
    pub script_kind: ScriptKind,
    /// The shared, immutable source text.
    pub source: Arc<SourceText>,
    /// The frontend product to produce.
    pub mode: FrontendMode,
    /// Skip the emit stage even when the mode would normally produce one.
    pub no_emit: bool,
    /// Suppress emit when any pre-emit diagnostic is an error.
    pub no_emit_on_error: bool,
}

/// The immutable product of a full frontend compilation.
///
/// The recovered [`SourceFile`] and [`SemanticModel`] are always present, the
/// [`EmitOutput`] is present exactly when the request asked for one, and
/// [`FrontendOutput::diagnostics`] is the single canonically ordered union of
/// every stage's diagnostics.
pub struct FrontendOutput {
    mode: FrontendMode,
    source_file: SourceFile,
    semantic_model: SemanticModel,
    emit: Option<EmitOutput>,
    diagnostics: Vec<Diagnostic>,
}

impl FrontendOutput {
    /// Returns the mode this output was produced for.
    #[must_use]
    pub const fn mode(&self) -> FrontendMode {
        self.mode
    }

    /// Returns the recovered parser product, always present even on syntax errors.
    #[must_use]
    pub const fn source_file(&self) -> &SourceFile {
        &self.source_file
    }

    /// Returns the recovered semantic model, always present even on type errors.
    #[must_use]
    pub const fn semantic_model(&self) -> &SemanticModel {
        &self.semantic_model
    }

    /// Returns the emit product, present exactly when the request asked to emit.
    #[must_use]
    pub const fn emit(&self) -> Option<&EmitOutput> {
        self.emit.as_ref()
    }

    /// Returns every stage's diagnostics in canonical order with no duplicates.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Returns whether any diagnostic is an error.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| !diagnostic.is_warning())
    }

    /// Consumes the output into its parts.
    #[must_use]
    pub fn into_parts(
        self,
    ) -> (
        SourceFile,
        SemanticModel,
        Option<EmitOutput>,
        Vec<Diagnostic>,
    ) {
        (
            self.source_file,
            self.semantic_model,
            self.emit,
            self.diagnostics,
        )
    }
}

/// Frontend products for every module of one canonical resolved program.
pub struct ProgramFrontendOutput {
    entrypoint: SourceId,
    modules: Vec<FrontendOutput>,
    index: HashMap<SourceId, usize>,
}
#[cfg(test)]
thread_local! {
    static MODULE_EXPORTS_COMPUTATIONS: std::cell::RefCell<HashMap<SourceId, usize>> =
        std::cell::RefCell::new(HashMap::new());
}

#[cfg(test)]
fn record_module_exports_computation(source_id: SourceId) {
    MODULE_EXPORTS_COMPUTATIONS.with(|counts| {
        *counts.borrow_mut().entry(source_id).or_default() += 1;
    });
}

impl ProgramFrontendOutput {
    #[must_use]
    pub const fn entrypoint_id(&self) -> SourceId {
        self.entrypoint
    }

    /// Products in the same dependency-first order as the resolved program.
    #[must_use]
    pub fn modules(&self) -> &[FrontendOutput] {
        &self.modules
    }

    /// Each module's export names with no runtime form. A name forwarded from
    /// another module, by a re-export or `export *`, takes that module's answer.
    #[must_use]
    pub fn erased_exports(&self, program: &ResolvedProgram) -> HashMap<SourceId, BTreeSet<String>> {
        let mut erased = HashMap::new();
        let mut exports = HashMap::new();
        let by_source = &self.index;
        for module in &self.modules {
            let source_id = module.source_file().source_id();
            self.resolve_erased_exports(
                program,
                source_id,
                &mut erased,
                &mut exports,
                &mut HashSet::new(),
                by_source,
            );
        }
        erased
    }

    fn module_index(modules: &[FrontendOutput]) -> HashMap<SourceId, usize> {
        let mut index = HashMap::with_capacity(modules.len());
        for (position, module) in modules.iter().enumerate() {
            index
                .entry(module.source_file().source_id())
                .or_insert(position);
        }
        index
    }

    fn cached_module_exports(
        &self,
        source_id: SourceId,
        cache: &mut HashMap<SourceId, ModuleExports>,
        by_source: &HashMap<SourceId, usize>,
    ) -> Option<ModuleExports> {
        if cache.contains_key(&source_id) {
            return cache.get(&source_id).cloned();
        }
        let module = by_source.get(&source_id).map(|&index| &self.modules[index])?;
        #[cfg(test)]
        record_module_exports_computation(source_id);
        cache.insert(
            source_id,
            emitter::transforms::module_exports(module.source_file(), module.semantic_model()),
        );
        cache.get(&source_id).cloned()
    }

    fn resolve_erased_exports(
        &self,
        program: &ResolvedProgram,
        source_id: SourceId,
        erased: &mut HashMap<SourceId, BTreeSet<String>>,
        exports_cache: &mut HashMap<SourceId, ModuleExports>,
        visiting: &mut HashSet<SourceId>,
        by_source: &HashMap<SourceId, usize>,
    ) {
        if erased.contains_key(&source_id) {
            return;
        }
        if !by_source.contains_key(&source_id) {
            return;
        }
        // A cycle decides nothing: a name stays until something proves it erased.
        if !visiting.insert(source_id) {
            return;
        }
        let Some(exports) = self.cached_module_exports(source_id, exports_cache, by_source) else {
            return;
        };
        let mut names = exports.types;
        let forwarded: BTreeSet<String> = exports
            .forwards
            .iter()
            .map(|(exported, ..)| exported.clone())
            .collect();
        for (exported, specifier, imported) in &exports.forwards {
            let target = local_dependency(program, source_id, specifier);
            if let Some(target) = target {
                self.resolve_erased_exports(program, target, erased, exports_cache, visiting, by_source);
            }
            if target
                .and_then(|target| erased.get(&target))
                .is_some_and(|target_names| target_names.contains(imported))
            {
                names.insert(exported.clone());
            } else {
                // An explicit export outranks a local type of the same name.
                names.remove(exported);
            }
        }
        let mut star_values = BTreeSet::new();
        for specifier in &exports.stars {
            if let Some(target) = local_dependency(program, source_id, specifier) {
                self.resolve_erased_exports(program, target, erased, exports_cache, visiting, by_source);
                if let Some(target_exports) = exports_cache.get(&target) {
                    star_values.extend(target_exports.values.iter().cloned());
                }
                // An explicit export of the same name shadows what a star brings.
                if let Some(starred) = erased.get(&target) {
                    names.extend(
                        starred
                            .iter()
                            .filter(|name| {
                                name.as_str() != "default" && !forwarded.contains(name.as_str())
                            })
                            .cloned(),
                    );
                }
            }
        }
        // A name stays if any star brings it as a value.
        names.retain(|name| !exports.values.contains(name) && !star_values.contains(name));
        erased.insert(source_id, names);
    }

    /// `(specifier, name)` for what the module's imports can name that has no
    /// runtime form. Emit cannot see other files, and an ES module naming one
    /// of these fails at load.
    #[must_use]
    pub fn erased_imports(
        &self,
        program: &ResolvedProgram,
        erased: &HashMap<SourceId, BTreeSet<String>>,
        source_id: SourceId,
    ) -> BTreeSet<(String, String)> {
        let mut pairs = BTreeSet::new();
        for edge in dependencies_of(program, source_id) {
            let names = edge_target(edge).and_then(|target| erased.get(&target));
            for name in names.into_iter().flatten() {
                pairs.insert((edge.specifier().to_owned(), name.clone()));
            }
        }
        pairs
    }

    #[must_use]
    pub fn module(&self, source_id: SourceId) -> Option<&FrontendOutput> {
        self.index.get(&source_id).map(|&position| &self.modules[position])
    }
}

/// Runs the frontend for every module while preserving the graph's canonical identities.
#[must_use]
pub fn compile_program_frontend(
    program: &ResolvedProgram,
    mode: FrontendMode,
) -> ProgramFrontendOutput {
    compile_program_frontend_with_cancel(
        program,
        mode,
        &LintTable::new(LintProfile::Default),
        &CancellationToken::new(),
    )
    .expect("fresh token is never cancelled")
}

/// Runs the frontend for every module with caller-resolved lint levels.
#[must_use]
pub fn compile_program_frontend_with_lints(
    program: &ResolvedProgram,
    mode: FrontendMode,
    levels: &LintTable,
) -> ProgramFrontendOutput {
    compile_program_frontend_with_cancel(program, mode, levels, &CancellationToken::new())
        .expect("fresh token is never cancelled")
}

/// Runs the frontend for every module with cooperative cancellation.
///
/// Cancellation is observed between frontend stages and at every source and
/// dependency iteration boundary. A completed result is otherwise identical to
/// compile_program_frontend_with_lints.
/// The names of every `declare module "name"` in the program, which satisfy
/// an import that no file does.
fn ambient_module_names(parsed: &[Recovered<SourceFile>]) -> Vec<String> {
    fn collect(file: &SourceFile, statement: &Stmt, names: &mut Vec<String>) {
        match statement.data() {
            Statement::Declare(inner) => collect(file, inner, names),
            Statement::Namespace(namespace) => {
                if let NamespaceName::StringLiteral(literal) = &namespace.name
                    && let Some(text) = file.token_text(literal.data().token())
                {
                    names.push(text.trim_matches(['\'', '"']).to_owned());
                }
            }
            _ => {}
        }
    }
    let mut names = Vec::new();
    for file in parsed {
        for statement in file.product().statements() {
            collect(file.product(), statement, &mut names);
        }
    }
    names
}

/// Whether an ambient module `pattern` covers `specifier`. One `*` matches
/// any text, as in `declare module "*.css"`.
fn ambient_module_matches(pattern: &str, specifier: &str) -> bool {
    match pattern.split_once('*') {
        Some((prefix, suffix)) => {
            specifier.len() >= prefix.len() + suffix.len()
                && specifier.starts_with(prefix)
                && specifier.ends_with(suffix)
        }
        None => pattern == specifier,
    }
}

/// TS2307 for each import of `module` that nothing satisfies.
fn unresolved_import_diagnostics(
    module: &ResolvedModule,
    ambient_modules: &[String],
) -> Vec<Diagnostic> {
    module
        .dependencies()
        .iter()
        .filter(|edge| {
            edge.is_unresolved()
                && !ambient_modules
                    .iter()
                    .any(|pattern| ambient_module_matches(pattern, edge.specifier()))
        })
        .map(|edge| {
            let message = by_u32(2307)
                .and_then(|entry| entry.format(Args::new([edge.specifier()])).ok())
                .unwrap_or_else(|| "Cannot find module.".to_owned());
            Diagnostic::error(
                CANNOT_FIND_MODULE,
                module.source_id(),
                edge.range(),
                message,
            )
        })
        .collect()
}

/// TS2343 for downlevel syntax whose `tslib` export is absent.
const MISSING_HELPER_IN_TSLIB: DiagnosticCode = DiagnosticCode::new("TS2343");
/// TS2354 for downlevel syntax when `tslib` cannot be resolved.
const MISSING_TSLIB_MODULE: DiagnosticCode = DiagnosticCode::new("TS2354");

/// tsc helper names the emitter catalog does not define. The walk attributes
/// these exactly where the reference baselines place them; the emitter half
/// stays untouched until downleveling learns these forms.
const ES_DECORATE: &str = "__esDecorate";
const RUN_INITIALIZERS: &str = "__runInitializers";
const SET_FUNCTION_NAME: &str = "__setFunctionName";
const PROP_KEY: &str = "__propKey";
const ASYNC_GENERATOR: &str = "__asyncGenerator";
const AWAIT_HELPER: &str = "__await";
const ASYNC_DELEGATOR: &str = "__asyncDelegator";
const ASYNC_VALUES: &str = "__asyncValues";
const MAKE_TEMPLATE_OBJECT: &str = "__makeTemplateObject";

/// Inputs deciding whether downlevel syntax needs an imported helper. The
/// target predicates reuse [`LanguageFeature`] exactly as lowering does, so
/// the check and the emit cannot disagree on when a helper is required.
struct TslibHelperContext {
    target: crate::emitter::ScriptTarget,
    es_module_interop: bool,
    experimental_decorators: bool,
    emit_decorator_metadata: bool,
    module_kind: Option<crate::emitter::ModuleKind>,
}

/// One file's view for the helper check.
struct TslibHelperFile<'a> {
    source_id: SourceId,
    source: &'a SourceFile,
    path: &'a std::path::Path,
    module_kind: Option<crate::emitter::ModuleKind>,
    is_module: bool,
    is_declaration_file: bool,
}

enum TslibTarget {
    File(SourceId),
    OnDisk(std::path::PathBuf),
    Ambient(SourceId),
}

/// Program-wide missing-helper diagnostics keyed by needing file. TS2354
/// reports once per file at its first needing site; TS2343 reports once per
/// helper for each distinct `tslib` copy, at that helper's first site.
fn tslib_helper_diagnostics_for_program(
    program: &ResolvedProgram,
    parsed: &[Recovered<SourceFile>],
) -> HashMap<SourceId, Vec<Diagnostic>> {
    if program.import_helpers() != Some(true) {
        return HashMap::new();
    }
    let context = TslibHelperContext {
        target: program.check_options().target(),
        module_kind: None,
        es_module_interop: program.es_module_interop().unwrap_or(true),
        experimental_decorators: program.experimental_decorators(),
        emit_decorator_metadata: program.emit_decorator_metadata(),
    };
    let mut by_id: HashMap<SourceId, (usize, &SourceFile)> = HashMap::new();
    for (index, file) in parsed.iter().enumerate() {
        by_id.insert(file.product().source_id(), (index, file.product()));
    }
    let mut files: Vec<TslibHelperFile<'_>> = Vec::new();
    for (index, module) in program.modules().iter().enumerate() {
        let Some((_, source)) = by_id.get(&module.source_id()) else {
            continue;
        };
        let file_name = module
            .path()
            .file_name()
            .map(|name| name.to_string_lossy())
            .unwrap_or_default();
        files.push(TslibHelperFile {
            source_id: module.source_id(),
            source,
            path: module.path(),
            module_kind: program.emit_module_kind(index),
            is_module: crate::checker::source_is_module(source),
            is_declaration_file: file_name.ends_with(".d.ts")
                || file_name.ends_with(".d.mts")
                || file_name.ends_with(".d.cts"),
        });
    }
    tslib_helper_diagnostics_for_files(&files, &context)
}

/// Core check over explicit file views, so unit tests exercise it without a
/// resolved program.
fn tslib_helper_diagnostics_for_files(
    files: &[TslibHelperFile<'_>],
    context: &TslibHelperContext,
) -> HashMap<SourceId, Vec<Diagnostic>> {
    let mut cache = TslibDiskCache::default();
    tslib_helper_diagnostics_for_files_cached(files, context, &mut cache)
}

fn tslib_helper_diagnostics_for_files_cached(
    files: &[TslibHelperFile<'_>],
    context: &TslibHelperContext,
    cache: &mut TslibDiskCache,
) -> HashMap<SourceId, Vec<Diagnostic>> {
    let mut diagnostics: HashMap<SourceId, Vec<Diagnostic>> = HashMap::new();
    let mut reported: HashSet<(String, String)> = HashSet::new();
    let mut by_source = HashMap::with_capacity(files.len());
    for (position, file) in files.iter().enumerate() {
        by_source.entry(file.source_id).or_insert(position);
    }
    for file in files {
        if !file.is_module || file.is_declaration_file {
            continue;
        }
        let context = TslibHelperContext {
            target: context.target,
            module_kind: file.module_kind,
            es_module_interop: context.es_module_interop,
            experimental_decorators: context.experimental_decorators,
            emit_decorator_metadata: context.emit_decorator_metadata,
        };
        let sites = tslib_helper_sites(file.source, &context);
        if sites.is_empty() {
            continue;
        }
        let Some(target) = resolve_tslib(files, file) else {
            let span = sites[0].1;
            let message = by_u32(2354)
                .and_then(|entry| entry.format(Args::new(["tslib"])).ok())
                .unwrap_or_else(|| {
                    "This syntax requires an imported helper but module 'tslib' cannot be found."
                        .to_owned()
                });
            diagnostics
                .entry(file.source_id)
                .or_default()
                .push(Diagnostic::error(
                    MISSING_TSLIB_MODULE,
                    file.source_id,
                    span,
                    message,
                ));
            continue;
        };
        let exports = match tslib_export_names(files, &target, cache, &by_source) {
            Some(exports) => exports,
            None => {
                let span = sites[0].1;
                let message = by_u32(2354)
                    .and_then(|entry| entry.format(Args::new(["tslib"])).ok())
                    .unwrap_or_else(|| {
                        "This syntax requires an imported helper but module 'tslib' cannot be found."
                            .to_owned()
                    });
                diagnostics
                    .entry(file.source_id)
                    .or_default()
                    .push(Diagnostic::error(
                        MISSING_TSLIB_MODULE,
                        file.source_id,
                        span,
                        message,
                    ));
                continue;
            }
        };
        let identity = tslib_identity(files, &target, &by_source);
        for (helper, span) in ordered_first_sites(&sites) {
            if exports.contains(helper) {
                continue;
            }
            if !reported.insert((helper.to_owned(), identity.clone())) {
                continue;
            }
            let message = by_u32(2343)
                .and_then(|entry| entry.format(Args::new(["tslib", helper])).ok())
                .unwrap_or_else(|| {
                    format!(
                        "This syntax requires an imported helper named '{helper}' which does not exist in 'tslib'. Consider upgrading your version of 'tslib'."
                    )
                });
            diagnostics
                .entry(file.source_id)
                .or_default()
                .push(Diagnostic::error(
                    MISSING_HELPER_IN_TSLIB,
                    file.source_id,
                    span,
                    message,
                ));
        }
    }
    diagnostics
}

/// First span per helper in walk order, helper names sorted alphabetically
/// within one span to match the reference order.
fn ordered_first_sites(
    sites: &[(&'static str, crate::source::TextRange)],
) -> Vec<(&'static str, crate::source::TextRange)> {
    let mut first: HashMap<&'static str, crate::source::TextRange> = HashMap::new();
    for &(helper, span) in sites {
        first.entry(helper).or_insert(span);
    }
    let mut ordered: Vec<(&'static str, crate::source::TextRange)> = first.into_iter().collect();
    ordered.sort_by(|left, right| {
        left.1
            .start()
            .cmp(&right.1.start())
            .then_with(|| left.0.cmp(right.0))
    });
    ordered
}

/// Syntax walk collecting the first site that needs each `tslib` helper.
/// Spans mirror the reference baselines exactly; see each `record` call.
struct TslibHelperWalk<'a> {
    context: &'a TslibHelperContext,
    source: &'a SourceFile,
    sites: Vec<(&'static str, crate::source::TextRange)>,
    ambient: bool,
    in_async_generator: bool,
    extends_keywords: Vec<crate::source::TextRange>,
}
/// First-spanning sites in source order for one file.
fn tslib_helper_sites(
    source: &SourceFile,
    context: &TslibHelperContext,
) -> Vec<(&'static str, crate::source::TextRange)> {
    let extends_keywords = source
        .tokens()
        .iter()
        .filter(|token| token.kind() == crate::syntax::TokenKind::KwExtends)
        .map(|token| token.range())
        .collect::<Vec<_>>();
    let mut walk = TslibHelperWalk {
        context,
        source,
        sites: Vec::new(),
        ambient: false,
        in_async_generator: false,
        extends_keywords,
    };
    walk.stmts(source.statements());
    walk.sites
}

impl TslibHelperWalk<'_> {
    fn record(&mut self, helper: &'static str, span: crate::source::TextRange) {
        if !self.ambient {
            self.sites.push((helper, span));
        }
    }

    fn stmts(&mut self, statements: &[crate::syntax::Stmt]) {
        for statement in statements {
            self.stmt(statement);
        }
    }

    fn stmt(&mut self, statement: &crate::syntax::Stmt) {
        use crate::syntax::Statement;
        match statement.data() {
            Statement::Import(import) => self.import_decl(import, statement.range()),
            Statement::ImportEquals(_) => {}
            Statement::Export(export) => self.export_decl(export, statement.range()),
            Statement::Variable(declaration) => {
                self.variable_declaration(declaration, statement.range())
            }
            Statement::Function(function) => self.function_declaration(&function.function),
            Statement::Class(class) => self.class_decl(class),
            Statement::Expression(statement) => self.expr(&statement.expression),
            Statement::If(branch) => {
                self.expr(&branch.test);
                self.stmt(&branch.consequent);
                if let Some(alternate) = &branch.alternate {
                    self.stmt(alternate);
                }
            }
            Statement::Block(block) => self.stmts(&block.data().statements),
            Statement::Switch(switch) => {
                self.expr(&switch.discriminant);
                for case in &switch.cases {
                    if let Some(test) = &case.data().test {
                        self.expr(test);
                    }
                    self.stmts(&case.data().consequent);
                }
            }
            Statement::For(statement) => {
                if let Some(initializer) = &statement.initializer {
                    self.for_initializer(initializer);
                }
                if let Some(test) = &statement.test {
                    self.expr(test);
                }
                if let Some(update) = &statement.update {
                    self.expr(update);
                }
                self.stmt(&statement.body);
            }
            Statement::ForIn(statement) => {
                self.for_binding(&statement.binding);
                self.expr(&statement.object);
                self.stmt(&statement.body);
            }
            Statement::ForOf(statement) => {
                self.for_binding(&statement.binding);
                self.expr(&statement.iterable);
                self.stmt(&statement.body);
            }
            Statement::While(statement) => {
                self.expr(&statement.test);
                self.stmt(&statement.body);
            }
            Statement::DoWhile(statement) => {
                self.stmt(&statement.body);
                self.expr(&statement.test);
            }
            Statement::Try(statement) => {
                self.stmts(&statement.block.data().statements);
                if let Some(handler) = &statement.handler {
                    if let Some(binding) = &handler.data().binding {
                        self.binding_pattern(binding);
                    }
                    self.stmts(&handler.data().body.data().statements);
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.stmts(&finalizer.data().statements);
                }
            }
            Statement::With(statement) => {
                self.expr(&statement.object);
                self.stmt(&statement.body);
            }
            Statement::Labeled(statement) => self.stmt(&statement.body),
            Statement::Return(statement) => {
                if let Some(argument) = &statement.argument {
                    self.expr(argument);
                }
            }
            Statement::Throw(statement) => self.expr(&statement.argument),
            Statement::Namespace(namespace) => self.stmts(&namespace.body.data().statements),
            Statement::Declare(inner) => {
                let ambient = std::mem::replace(&mut self.ambient, true);
                self.stmt(inner);
                self.ambient = ambient;
            }
            Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Debugger
            | Statement::Empty
            | Statement::Interface(_)
            | Statement::TypeAlias(_)
            | Statement::Enum(_)
            | Statement::Missing(_) => {}
        }
    }

    fn for_initializer(&mut self, initializer: &crate::syntax::ForInitializer) {
        match initializer {
            crate::syntax::ForInitializer::Variable(declaration) => {
                self.variable_declaration(declaration, declaration.range);
            }
            crate::syntax::ForInitializer::Expression(expression) => self.expr(expression),
        }
    }

    fn for_binding(&mut self, binding: &crate::syntax::ForBinding) {
        match binding {
            crate::syntax::ForBinding::Variable(declaration) => {
                if matches!(
                    declaration.kind,
                    crate::syntax::VariableKind::Using | crate::syntax::VariableKind::AwaitUsing
                ) {
                    self.need_using(declaration.range);
                }
                for declarator in &declaration.declarations {
                    self.binding_pattern(&declarator.data().binding);
                    if let Some(initializer) = &declarator.data().initializer {
                        self.expr(initializer);
                    }
                }
            }
            crate::syntax::ForBinding::Target(target) => {
                self.assignment_target(target);
            }
        }
    }

    fn variable_declaration(
        &mut self,
        declaration: &crate::syntax::VariableDeclaration,
        span: crate::source::TextRange,
    ) {
        use crate::syntax::VariableKind;
        if matches!(
            declaration.kind,
            VariableKind::Using | VariableKind::AwaitUsing
        ) {
            self.need_using(span);
        }
        for declarator in &declaration.declarations {
            let binding = &declarator.data().binding;
            self.binding_pattern(binding);
            if let Some(initializer) = &declarator.data().initializer {
                self.async_function_initializer(binding, initializer);
                self.expr(initializer);
            }
        }
    }

    fn need_using(&mut self, span: crate::source::TextRange) {
        use crate::emitter::transforms::LanguageFeature;
        if self.context.target.supports(LanguageFeature::Using) {
            return;
        }
        self.record(
            crate::emitter::helpers::HelperKind::AddDisposableResource.ident(),
            span,
        );
        self.record(
            crate::emitter::helpers::HelperKind::DisposeResources.ident(),
            span,
        );
    }
    fn expr(&mut self, expression: &crate::syntax::Expr) {
        use crate::syntax::Expression;
        match expression.data() {
            Expression::Identifier(_)
            | Expression::This
            | Expression::Super
            | Expression::Literal(_)
            | Expression::Meta(_)
            | Expression::Missing(_) => {}
            Expression::Template(template) => {
                for element in &template.expressions {
                    self.expr(element);
                }
            }
            Expression::TaggedTemplate(tagged) => {
                if !self
                    .context
                    .target
                    .supports(crate::emitter::transforms::LanguageFeature::Classes)
                {
                    self.record(
                        MAKE_TEMPLATE_OBJECT,
                        self.tagged_template_span(tagged, expression.range()),
                    );
                }
                self.expr(&tagged.tag);
                for element in &tagged.template.expressions {
                    self.expr(element);
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        crate::syntax::ArrayElement::Expression(inner) => self.expr(inner),
                        crate::syntax::ArrayElement::Spread(spread) => {
                            self.expr(&spread.argument);
                        }
                        crate::syntax::ArrayElement::Elision
                        | crate::syntax::ArrayElement::Missing(_) => {}
                    }
                }
            }
            Expression::Object(object) => {
                for member in &object.members {
                    self.object_member(member);
                }
            }
            Expression::Function(function) => {
                let span = function
                    .function
                    .name
                    .as_ref()
                    .map(|name| name.range())
                    .unwrap_or_else(|| expression.range());
                self.function_like(&function.function, Some(span));
            }
            Expression::Class(class) => self.class_decl(&class.class),
            Expression::Arrow(function) => {
                self.arrow_like(function, expression.range());
            }
            Expression::Call(call) => {
                self.expr(&call.callee);
                for argument in &call.arguments {
                    match argument {
                        crate::syntax::CallArgument::Expression(inner) => self.expr(inner),
                        crate::syntax::CallArgument::Spread(spread) => {
                            self.expr(&spread.argument);
                        }
                        crate::syntax::CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::Member(member) => self.member_read(member, expression.range()),
            Expression::New(call) => {
                self.expr(&call.callee);
                for argument in &call.arguments {
                    match argument {
                        crate::syntax::CallArgument::Expression(inner) => self.expr(inner),
                        crate::syntax::CallArgument::Spread(spread) => {
                            self.expr(&spread.argument);
                        }
                        crate::syntax::CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::Await(awaited) => self.expr(&awaited.argument),
            Expression::Yield(resumption) => {
                if resumption.delegate
                    && self.in_async_generator
                    && !self
                        .context
                        .target
                        .supports(crate::emitter::transforms::LanguageFeature::AsyncIteration)
                {
                    let span = self.yield_span(expression.range());
                    self.record(ASYNC_DELEGATOR, span);
                    self.record(ASYNC_VALUES, span);
                }
                if let Some(argument) = &resumption.argument {
                    self.expr(argument);
                }
            }
            Expression::Unary(unary) => self.expr(&unary.argument),
            Expression::Update(update) => {
                if let crate::syntax::AssignmentTarget::Member(member) = update.argument.data() {
                    if self.is_private_member(&member.property) && self.private_fields_active() {
                        let span = update.argument.range();
                        self.record(
                            crate::emitter::helpers::HelperKind::ClassPrivateFieldGet.ident(),
                            span,
                        );
                        self.record(
                            crate::emitter::helpers::HelperKind::ClassPrivateFieldSet.ident(),
                            span,
                        );
                        self.assignment_target_no_write(&update.argument);
                    } else {
                        self.assignment_target(&update.argument);
                    }
                } else {
                    self.assignment_target(&update.argument);
                }
            }
            Expression::Binary(binary) => {
                if binary.operator == crate::syntax::BinaryOperator::In {
                    self.private_name_in(&binary.left);
                }
                self.expr(&binary.left);
                self.expr(&binary.right);
            }
            Expression::Logical(logical) => {
                self.expr(&logical.left);
                self.expr(&logical.right);
            }
            Expression::Conditional(conditional) => {
                self.expr(&conditional.test);
                self.expr(&conditional.consequent);
                self.expr(&conditional.alternate);
            }
            Expression::Assignment(assignment) => {
                self.assignment_expression(assignment);
            }
            Expression::Sequence(sequence) => {
                for element in &sequence.expressions {
                    self.expr(element);
                }
            }
            Expression::Parenthesized(inner) => self.expr(inner),
            Expression::As(cast) => self.expr(&cast.expression),
            Expression::Satisfies(cast) => self.expr(&cast.expression),
            Expression::TypeAssertion(cast) => self.expr(&cast.expression),
            Expression::NonNull(inner) => self.expr(&inner.expression),
            Expression::Import(import) => {
                self.expr(&import.source);
                if let Some(options) = &import.options {
                    self.expr(options);
                }
            }
            Expression::JsxElement(element) => self.jsx_children(&element.children),
            Expression::JsxFragment(fragment) => self.jsx_children(&fragment.children),
            Expression::JsxSelfClosingElement(element) => {
                for attribute in &element.attributes {
                    self.jsx_attribute(attribute);
                }
            }
        }
    }

    fn jsx_children(&mut self, children: &[crate::syntax::JsxChild]) {
        for child in children {
            match child {
                crate::syntax::JsxChild::Element(element) => self.expr(element),
                crate::syntax::JsxChild::ExpressionContainer(container) => {
                    if let Some(expression) = &container.data().expression {
                        self.expr(expression);
                    }
                }
                crate::syntax::JsxChild::Spread(spread) => self.expr(&spread.data().expression),
                crate::syntax::JsxChild::Text(_) => {}
            }
        }
    }

    fn jsx_attribute(&mut self, attribute: &crate::syntax::JsxAttributeItem) {
        if let crate::syntax::JsxAttributeItem::Attribute(attribute) = attribute
            && let Some(crate::syntax::JsxAttributeInitializer::Expression(container)) =
                &attribute.data().initializer
            && let Some(expression) = &container.data().expression
        {
            self.expr(expression);
        }
    }

    fn function_declaration(&mut self, function: &crate::syntax::FunctionLike) {
        self.function_like(function, function.name.as_ref().map(|name| name.range()));
    }

    fn arrow_like(
        &mut self,
        function: &crate::syntax::ArrowFunction,
        arrow_range: crate::source::TextRange,
    ) {
        use crate::emitter::transforms::LanguageFeature;
        if function.is_async
            && !self
                .context
                .target
                .supports(LanguageFeature::AsyncFunctions)
        {
            self.record(
                crate::emitter::helpers::HelperKind::Awaiter.ident(),
                arrow_range,
            );
        }
        for parameter in &function.parameters {
            self.parameter(parameter);
        }
        let outer = std::mem::replace(&mut self.in_async_generator, false);
        match &function.body {
            crate::syntax::FunctionBody::Block(block) => self.stmts(&block.data().statements),
            crate::syntax::FunctionBody::Expression(expression) => self.expr(expression),
            crate::syntax::FunctionBody::Missing(_) => {}
        }
        self.in_async_generator = outer;
    }

    fn function_like(
        &mut self,
        function: &crate::syntax::FunctionLike,
        span: Option<crate::source::TextRange>,
    ) {
        use crate::emitter::transforms::LanguageFeature;
        let is_async_generator = function.is_async && function.is_generator;
        let span = span.or_else(|| function.name.as_ref().map(|name| name.range()));
        if function.is_async
            && !is_async_generator
            && !self
                .context
                .target
                .supports(LanguageFeature::AsyncFunctions)
            && let Some(span) = span
        {
            self.record(crate::emitter::helpers::HelperKind::Awaiter.ident(), span);
        }
        if is_async_generator
            && !self
                .context
                .target
                .supports(LanguageFeature::AsyncIteration)
            && let Some(span) = span
        {
            self.record(ASYNC_GENERATOR, span);
            self.record(AWAIT_HELPER, span);
        }
        if function.is_generator
            && !self.context.target.supports(LanguageFeature::Generators)
            && let Some(span) = span
        {
            self.record(crate::emitter::helpers::HelperKind::Generator.ident(), span);
        }
        for parameter in &function.parameters {
            self.parameter(parameter);
        }
        if function.body.is_some() {
            let outer = std::mem::replace(&mut self.in_async_generator, is_async_generator);
            match function.body.as_ref() {
                Some(crate::syntax::FunctionBody::Block(block)) => {
                    self.stmts(&block.data().statements);
                }
                Some(crate::syntax::FunctionBody::Expression(expression)) => {
                    self.expr(expression);
                }
                Some(crate::syntax::FunctionBody::Missing(_)) | None => {}
            }
            self.in_async_generator = outer;
        }
    }

    fn parameter(&mut self, parameter: &crate::syntax::ParameterNode) {
        let data = parameter.data();
        for decorator in &data.decorators {
            self.parameter_decorator(decorator);
        }
        self.binding_pattern(&data.binding);
        if let Some(initializer) = &data.initializer {
            self.expr(initializer);
        }
    }

    fn class_decl(&mut self, class: &crate::syntax::ClassDeclaration) {
        let anonymous = class.name.is_none();
        self.class_decorators(&class.decorators, anonymous);
        if let Some(heritage) = &class.extends {
            if !self
                .context
                .target
                .supports(crate::emitter::transforms::LanguageFeature::Classes)
            {
                self.record(
                    crate::emitter::helpers::HelperKind::Extends.ident(),
                    self.extends_span(heritage),
                );
            }
            self.expr(&heritage.expression);
        }
        for member in &class.members {
            self.member(member);
        }
    }

    fn member(&mut self, member: &crate::syntax::ClassMemberNode) {
        use crate::syntax::ClassMember;
        match member.data() {
            ClassMember::Constructor(constructor) => {
                for parameter in &constructor.parameters {
                    self.parameter(parameter);
                }
                self.stmts(&constructor.body.data().statements);
            }
            ClassMember::Method(method) => {
                let computed = matches!(method.name, crate::syntax::PropertyName::Computed(_));
                self.member_decorators(&method.function.decorators, true, computed);
                let name = match &method.name {
                    crate::syntax::PropertyName::Identifier(name) => Some(name.range()),
                    crate::syntax::PropertyName::String(literal) => Some(literal.range()),
                    crate::syntax::PropertyName::Number(literal) => Some(literal.range()),
                    crate::syntax::PropertyName::Private(name) => Some(name.range()),
                    crate::syntax::PropertyName::Computed(expression) => {
                        self.expr(expression);
                        None
                    }
                    crate::syntax::PropertyName::Missing(_) => None,
                };
                self.function_like(&method.function, name);
            }
            ClassMember::Property(property) => {
                let computed = matches!(property.name, crate::syntax::PropertyName::Computed(_));
                self.member_decorators(&property.decorators, false, computed);
                self.property_name(&property.name);
                if let Some(initializer) = &property.initializer {
                    self.expr(initializer);
                }
            }
            ClassMember::AutoAccessor(accessor) => {
                let computed = matches!(accessor.name, crate::syntax::PropertyName::Computed(_));
                self.member_decorators(&accessor.decorators, true, computed);
                self.property_name(&accessor.name);
                if let Some(initializer) = &accessor.initializer {
                    self.expr(initializer);
                }
            }
            ClassMember::StaticBlock(block) => self.stmts(&block.data().statements),
            ClassMember::IndexSignature(_) | ClassMember::Missing(_) | ClassMember::Semicolon => {}
        }
    }

    fn property_name(&mut self, name: &crate::syntax::PropertyName) {
        if let crate::syntax::PropertyName::Computed(expression) = name {
            self.expr(expression);
        }
    }

    fn object_member(&mut self, member: &crate::syntax::ObjectMemberNode) {
        use crate::syntax::ObjectMember;
        match member.data() {
            ObjectMember::Property(property) => {
                self.property_name(&property.name);
                self.expr(&property.value);
            }
            ObjectMember::Method(method) => {
                let name = match &method.name {
                    crate::syntax::PropertyName::Identifier(name) => Some(name.range()),
                    crate::syntax::PropertyName::String(literal) => Some(literal.range()),
                    crate::syntax::PropertyName::Number(literal) => Some(literal.range()),
                    crate::syntax::PropertyName::Private(name) => Some(name.range()),
                    crate::syntax::PropertyName::Computed(expression) => {
                        self.expr(expression);
                        None
                    }
                    crate::syntax::PropertyName::Missing(_) => None,
                };
                self.function_like(&method.function, name);
            }
            ObjectMember::Spread(spread) => {
                if !self
                    .context
                    .target
                    .supports(crate::emitter::transforms::LanguageFeature::Classes)
                {
                    self.record(
                        crate::emitter::helpers::HelperKind::Assign.ident(),
                        spread.argument.range(),
                    );
                }
                self.expr(&spread.argument);
            }
            ObjectMember::Missing(_) => {}
        }
    }

    fn binding_pattern(&mut self, pattern: &crate::syntax::Pattern) {
        use crate::syntax::BindingPattern;
        match pattern.data() {
            BindingPattern::Identifier(_) => {}
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.property_name(&property.name);
                    if let crate::syntax::BindingPattern::Rest(rest) = property.binding.data() {
                        self.object_rest(&rest.argument);
                    }
                    self.binding_pattern(&property.binding);
                    if let Some(initializer) = &property.initializer {
                        self.expr(initializer);
                    }
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                        self.binding_pattern(inner);
                    }
                }
            }
            BindingPattern::Rest(rest) => {
                self.binding_pattern(&rest.argument);
            }
            BindingPattern::Assignment(assignment) => {
                self.binding_pattern(&assignment.left);
                self.expr(&assignment.right);
            }
            BindingPattern::Missing(_) => {}
        }
    }

    fn object_rest(&mut self, argument: &crate::syntax::Pattern) {
        use crate::emitter::transforms::LanguageFeature;
        if !self
            .context
            .target
            .supports(LanguageFeature::ObjectRestSpread)
            && let crate::syntax::BindingPattern::Identifier(name) = argument.data()
        {
            self.record(
                crate::emitter::helpers::HelperKind::Rest.ident(),
                name.range(),
            );
        }
    }

    fn assignment_target(&mut self, target: &crate::syntax::AssignmentTargetNode) {
        use crate::syntax::AssignmentTarget;
        match target.data() {
            AssignmentTarget::Identifier(_) => {}
            AssignmentTarget::Member(member) => {
                self.private_write(&member.property, target.range());
                self.expr(&member.object);
                if let crate::syntax::MemberProperty::Computed(inner) = &member.property {
                    self.expr(inner);
                }
            }
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    self.property_name(&property.name);
                    if property.rest
                        && let AssignmentTarget::Identifier(name) = property.target.data()
                        && !self.context.target.supports(
                            crate::emitter::transforms::LanguageFeature::ObjectRestSpread,
                        )
                    {
                        self.record(
                            crate::emitter::helpers::HelperKind::Rest.ident(),
                            name.range(),
                        );
                    }
                    self.assignment_target(&property.target);
                    if let Some(initializer) = &property.initializer {
                        self.expr(initializer);
                    }
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    match element {
                        crate::syntax::AssignmentArrayElement::Target(inner)
                        | crate::syntax::AssignmentArrayElement::Rest(inner) => {
                            self.assignment_target(inner);
                        }
                        crate::syntax::AssignmentArrayElement::Elision
                        | crate::syntax::AssignmentArrayElement::Missing(_) => {}
                    }
                }
            }
            AssignmentTarget::Missing(_) | AssignmentTarget::Invalid(_) => {}
        }
    }

    fn assignment_expression(&mut self, assignment: &crate::syntax::AssignmentExpression) {
        if let crate::syntax::AssignmentTarget::Member(member) = assignment.left.data()
            && self.is_private_member(&member.property)
            && self.private_fields_active()
        {
            let span = assignment.left.range();
            if assignment.operator != crate::syntax::AssignmentOperator::Assign {
                self.record(
                    crate::emitter::helpers::HelperKind::ClassPrivateFieldGet.ident(),
                    span,
                );
            }
            self.record(
                crate::emitter::helpers::HelperKind::ClassPrivateFieldSet.ident(),
                span,
            );
        }
        if !matches!(
            assignment.left.data(),
            crate::syntax::AssignmentTarget::Member(_)
        ) {
            self.assignment_target(&assignment.left);
        } else {
            self.assignment_target_no_write(&assignment.left);
        }
        self.expr(&assignment.right);
    }

    fn assignment_target_no_write(&mut self, target: &crate::syntax::AssignmentTargetNode) {
        if let crate::syntax::AssignmentTarget::Member(member) = target.data() {
            self.expr(&member.object);
            if let crate::syntax::MemberProperty::Computed(inner) = &member.property {
                self.expr(inner);
            }
        }
    }

    fn private_fields_active(&self) -> bool {
        use crate::emitter::transforms::LanguageFeature;
        self.context.target.supports(LanguageFeature::Classes)
            && !self.context.target.supports(LanguageFeature::ClassFields)
    }
    fn is_private_member(&self, property: &crate::syntax::MemberProperty) -> bool {
        matches!(property, crate::syntax::MemberProperty::Private(_))
    }

    fn private_write(
        &mut self,
        property: &crate::syntax::MemberProperty,
        span: crate::source::TextRange,
    ) {
        if self.is_private_member(property) && self.private_fields_active() {
            self.record(
                crate::emitter::helpers::HelperKind::ClassPrivateFieldSet.ident(),
                span,
            );
        }
    }

    fn private_name_in(&mut self, operand: &crate::syntax::Expr) {
        if let crate::syntax::Expression::Identifier(name) = operand.data()
            && name.data().token().kind() == crate::syntax::TokenKind::PrivateIdentifier
            && self.private_fields_active()
        {
            self.record(
                crate::emitter::helpers::HelperKind::ClassPrivateFieldIn.ident(),
                name.range(),
            );
        }
    }

    fn class_decorators(&mut self, decorators: &[crate::syntax::DecoratorNode], anonymous: bool) {
        use crate::emitter::helpers::HelperKind;
        for decorator in decorators {
            let span = decorator.range();
            if self.context.experimental_decorators {
                self.record(HelperKind::Decorate.ident(), span);
                if self.context.emit_decorator_metadata {
                    self.record(HelperKind::Metadata.ident(), span);
                }
            } else {
                self.record(ES_DECORATE, span);
                self.record(RUN_INITIALIZERS, span);
                if anonymous {
                    self.record(SET_FUNCTION_NAME, span);
                }
            }
            self.expr(&decorator.data().expression);
        }
    }

    fn member_decorators(
        &mut self,
        decorators: &[crate::syntax::DecoratorNode],
        needs_function_name: bool,
        computed: bool,
    ) {
        use crate::emitter::helpers::HelperKind;
        for decorator in decorators {
            let span = decorator.range();
            if self.context.experimental_decorators {
                self.record(HelperKind::Decorate.ident(), span);
                if self.context.emit_decorator_metadata {
                    self.record(HelperKind::Metadata.ident(), span);
                }
            } else {
                self.record(ES_DECORATE, span);
                self.record(RUN_INITIALIZERS, span);
                if needs_function_name && !computed {
                    self.record(SET_FUNCTION_NAME, span);
                }
                if computed {
                    self.record(PROP_KEY, span);
                }
            }
            self.expr(&decorator.data().expression);
        }
    }

    fn parameter_decorator(&mut self, decorator: &crate::syntax::DecoratorNode) {
        use crate::emitter::helpers::HelperKind;
        let span = decorator.range();
        self.record(HelperKind::Decorate.ident(), span);
        self.record(HelperKind::Param.ident(), span);
        if self.context.emit_decorator_metadata {
            self.record(HelperKind::Metadata.ident(), span);
        }
        self.expr(&decorator.data().expression);
    }

    fn import_decl(
        &mut self,
        import: &crate::syntax::ImportDeclaration,
        span: crate::source::TextRange,
    ) {
        use crate::syntax::ImportBinding;
        if import.type_only || !self.interop_active() {
            return;
        }
        let Some(clause) = &import.clause else {
            return;
        };
        let named_has_default = matches!(&clause.binding, Some(ImportBinding::Named(specifiers)) if specifiers.iter().any(|specifier| {
            specifier.data().mode == crate::syntax::ImportSpecifierMode::Value
                && self.module_export_text(&specifier.data().imported) == "default"
        }));
        if clause.default.is_some()
            && !matches!(&clause.binding, Some(ImportBinding::Namespace(_)))
            && !named_has_default
        {
            self.record(
                crate::emitter::helpers::HelperKind::ImportDefault.ident(),
                span,
            );
        }
        match &clause.binding {
            Some(ImportBinding::Namespace(_)) => {
                self.record(
                    crate::emitter::helpers::HelperKind::ImportStar.ident(),
                    span,
                );
            }
            Some(ImportBinding::Named(specifiers)) => {
                for specifier in specifiers {
                    if specifier.data().mode == crate::syntax::ImportSpecifierMode::Value
                        && self.module_export_text(&specifier.data().imported) == "default"
                    {
                        self.record(
                            crate::emitter::helpers::HelperKind::ImportDefault.ident(),
                            specifier.range(),
                        );
                    }
                }
            }
            None => {}
        }
    }

    fn export_decl(
        &mut self,
        export: &crate::syntax::ExportDeclaration,
        span: crate::source::TextRange,
    ) {
        use crate::syntax::{ExportDeclaration, ExportDefaultValue, ExportNamedDeclaration};
        match export {
            ExportDeclaration::All(all) => {
                if all.type_only {
                    return;
                }
                if all.exported.is_some() {
                    if self.interop_active() {
                        self.record(
                            crate::emitter::helpers::HelperKind::ImportStar.ident(),
                            span,
                        );
                    }
                } else if self.downlevel_module() {
                    self.record(
                        crate::emitter::helpers::HelperKind::ExportStar.ident(),
                        span,
                    );
                }
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source,
                ..
            }) => {
                if *type_only || source.is_none() {
                    return;
                }
                if !self.interop_active() {
                    return;
                }
                for specifier in specifiers {
                    if self.module_export_text(&specifier.data().local) == "default" {
                        self.record(
                            crate::emitter::helpers::HelperKind::ImportDefault.ident(),
                            specifier.range(),
                        );
                    }
                }
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) => {
                self.stmt(inner)
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    let span = function
                        .name
                        .as_ref()
                        .map(|name| name.range())
                        .unwrap_or(span);
                    self.function_like(function, Some(span));
                }
                ExportDefaultValue::Class(class) => self.class_decl(class),
                ExportDefaultValue::Expression(expression) => self.expr(expression),
                ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => {}
            },
            ExportDeclaration::Assignment(expression) => self.expr(expression),
        }
    }

    fn interop_active(&self) -> bool {
        use crate::emitter::ModuleKind;
        self.context.es_module_interop
            && matches!(
                self.context.module_kind,
                Some(ModuleKind::CommonJs | ModuleKind::Amd | ModuleKind::Umd)
            )
    }

    fn downlevel_module(&self) -> bool {
        use crate::emitter::ModuleKind;
        matches!(
            self.context.module_kind,
            Some(ModuleKind::CommonJs | ModuleKind::Amd | ModuleKind::Umd | ModuleKind::System)
        )
    }

    fn extends_span(&self, heritage: &crate::syntax::ClassHeritage) -> crate::source::TextRange {
        let expression = heritage.expression.range();
        let index = self
            .extends_keywords
            .partition_point(|keyword| keyword.end() <= expression.start());
        let keyword = index.checked_sub(1).and_then(|at| self.extends_keywords.get(at)).copied();
        keyword.map_or(expression, |keyword| {
            crate::source::TextRange::new(keyword.start(), expression.end()).unwrap_or(expression)
        })
    }

    fn tagged_template_span(
        &self,
        tagged: &crate::syntax::TaggedTemplateExpression,
        fallback: crate::source::TextRange,
    ) -> crate::source::TextRange {
        let first = tagged
            .template
            .elements
            .first()
            .map(|element| element.range().start());
        let last = tagged
            .template
            .elements
            .last()
            .map(|element| element.range().end());
        match (first, last) {
            (Some(start), Some(end)) => {
                let start = crate::source::Utf16Pos::new(start.get().saturating_sub(1));
                let end = crate::source::Utf16Pos::new(end.get().saturating_add(1));
                crate::source::TextRange::new(start, end).unwrap_or(fallback)
            }
            _ => fallback,
        }
    }

    fn yield_span(&self, node: crate::source::TextRange) -> crate::source::TextRange {
        let end = crate::source::Utf16Pos::new(node.start().get().saturating_add(5));
        crate::source::TextRange::new(node.start(), end).unwrap_or(node)
    }

    fn async_function_initializer(
        &mut self,
        binding: &crate::syntax::Pattern,
        initializer: &crate::syntax::Expr,
    ) {
        use crate::emitter::transforms::LanguageFeature;
        if let crate::syntax::BindingPattern::Identifier(name) = binding.data()
            && let crate::syntax::Expression::Function(function) = initializer.data()
            && function.function.name.is_none()
            && function.function.is_async
            && !function.function.is_generator
            && !self.context.target.supports(LanguageFeature::AsyncFunctions)
        {
            self.record(
                crate::emitter::helpers::HelperKind::Awaiter.ident(),
                name.range(),
            );
        }
    }

    fn module_export_text(&self, name: &crate::syntax::ModuleExportName) -> String {
        match name {
            crate::syntax::ModuleExportName::Identifier(identifier) => self
                .source
                .token_text(identifier.data().token())
                .unwrap_or_default()
                .to_owned(),
            crate::syntax::ModuleExportName::String(literal) => self
                .source
                .token_text(literal.data().token())
                .map_or_else(String::new, |text| {
                    text.trim_matches(|character| character == '\'' || character == '"')
                        .to_owned()
                }),
            crate::syntax::ModuleExportName::Missing(_) => String::new(),
        }
    }
    fn member_read(
        &mut self,
        member: &crate::syntax::MemberExpression,
        span: crate::source::TextRange,
    ) {
        if self.is_private_member(&member.property) && self.private_fields_active() {
            self.record(
                crate::emitter::helpers::HelperKind::ClassPrivateFieldGet.ident(),
                span,
            );
        }
        self.expr(&member.object);
        if let crate::syntax::MemberProperty::Computed(inner) = &member.property {
            self.expr(inner);
        }
    }
}
fn resolve_tslib(files: &[TslibHelperFile<'_>], from: &TslibHelperFile<'_>) -> Option<TslibTarget> {
    let mut candidates: std::collections::HashMap<String, SourceId> =
        std::collections::HashMap::new();
    for file in files {
        candidates.insert(file.path.to_string_lossy().into_owned(), file.source_id);
    }
    let mut directory = from.path.parent();
    while let Some(dir) = directory {
        for name in [
            "tslib.d.ts",
            "tslib.ts",
            "tslib.d.mts",
            "tslib.mts",
            "tslib.d.cts",
            "tslib.cts",
            "tslib.tsx",
            "tslib.ts",
            "tslib.jsx",
            "tslib.js",
        ] {
            let probe = dir.join("node_modules").join("tslib").join(name);
            if let Some(id) = candidates.get(&probe.to_string_lossy().into_owned()) {
                return Some(TslibTarget::File(*id));
            }
            if probe.is_file() {
                return Some(TslibTarget::OnDisk(probe));
            }
        }
        for name in ["index.d.ts", "index.ts", "index.tsx", "index.js"] {
            let probe = dir.join("node_modules").join("tslib").join(name);
            if let Some(id) = candidates.get(&probe.to_string_lossy().into_owned()) {
                return Some(TslibTarget::File(*id));
            }
            if probe.is_file() {
                return Some(TslibTarget::OnDisk(probe));
            }
        }
        directory = dir.parent();
    }
    files.iter().find_map(|file| {
        ambient_tslib_present(file.source).then_some(TslibTarget::Ambient(file.source_id))
    })
}

/// Whether the file declares an ambient `tslib` module.
fn ambient_tslib_present(source: &SourceFile) -> bool {
    use crate::syntax::{NamespaceName, Statement};
    source.statements().iter().any(|statement| {
        let mut current = statement;
        loop {
            match current.data() {
                Statement::Declare(inner) => current = inner,
                Statement::Namespace(namespace) => {
                    return matches!(&namespace.name, NamespaceName::StringLiteral(literal) if source.token_text(literal.data().token()).is_some_and(|text| text.trim_matches(|character| character == '\'' || character == '"') == "tslib"));
                }
                Statement::Export(crate::syntax::ExportDeclaration::Named(crate::syntax::ExportNamedDeclaration::Declaration(inner))) => current = inner,
                _ => return false,
            }
        }
    })
}

/// Parsed on-disk `tslib` export names keyed by canonical path, shared by every
/// file of one [`compile_program_frontend`] call instead of re-reading and
/// re-parsing per needing module. `None` records an unreadable copy so the
/// failure reports TS2354 once per path.
#[derive(Default)]
struct TslibDiskCache {
    names: HashMap<std::path::PathBuf, Option<std::collections::BTreeSet<String>>>,
}

/// Value export names of the resolved `tslib`, for the TS2343 presence check.
/// Returns `None` when an on-disk copy cannot be used (non-regular, oversize,
/// or unparseable), so the caller reports TS2354 instead of TS2343.
fn tslib_export_names(
    files: &[TslibHelperFile<'_>],
    target: &TslibTarget,
    cache: &mut TslibDiskCache,
    by_source: &HashMap<SourceId, usize>,
) -> Option<std::collections::BTreeSet<String>> {
    match target {
        TslibTarget::File(id) => {
            let position = by_source.get(id)?;
            let source = files[*position].source;
            let mut names = std::collections::BTreeSet::new();
            collect_value_exports(source, source.statements(), &mut names);
            Some(names)
        }
        TslibTarget::OnDisk(path) => {
            let key = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
            if let Some(cached) = cache.names.get(&key) {
                return cached.clone();
            }
            let names = tslib_on_disk_source(path).map(|source| {
                let mut names = std::collections::BTreeSet::new();
                collect_value_exports(&source, source.statements(), &mut names);
                names
            });
            cache.names.insert(key, names.clone());
            names
        }
        TslibTarget::Ambient(id) => {
            let position = by_source.get(id)?;
            let source = files[*position].source;
            let mut names = std::collections::BTreeSet::new();
            collect_ambient_tslib_exports(source, &mut names);
            Some(names)
        }
    }
}

/// Cap for an on-disk `tslib` read: far above the real package, bounding a
/// hostile copy. Oversize reads report TS2354 instead of loading the file.
const TSLIB_ON_DISK_READ_CAP: u64 = 16 * 1024 * 1024;

/// Read and parse a `tslib` copy the loader never pulled into the program.
/// Import-free `tslib` packages still satisfy `importHelpers`, so exports are
/// collected from the file on disk. Only regular files up to the read cap are
/// used; anything else is `None` so the check reports TS2354.
fn tslib_on_disk_source(path: &std::path::Path) -> Option<SourceFile> {
    if !std::fs::metadata(path).ok()?.is_file() {
        return None;
    }
    let file = std::fs::File::open(path).ok()?;
    let mut text = String::new();
    use std::io::Read as _;
    file.take(TSLIB_ON_DISK_READ_CAP + 1).read_to_string(&mut text).ok()?;
    if text.len() as u64 > TSLIB_ON_DISK_READ_CAP {
        return None;
    }
    let source_id = SourceId::new(u32::MAX);
    let script_kind = match path.extension().and_then(|ext| ext.to_str()) {
        Some("ts" | "mts" | "cts") => ScriptKind::TypeScript,
        Some("tsx") => ScriptKind::TypeScriptReact,
        Some("js" | "mjs" | "cjs") => ScriptKind::JavaScript,
        Some("jsx") => ScriptKind::JavaScriptReact,
        _ => return None,
    };
    let text = SourceText::new(text).ok()?;
    let (source, _) = parser::parse(scanner::scan(source_id, script_kind, Arc::new(text))).into_parts();
    Some(source)
}

/// Identity key for cross-file TS2343 deduplication: same helper from the same
/// `tslib` copy reports once. On-disk copies canonicalize so two probes of one
/// file share an identity.
fn tslib_identity(
    files: &[TslibHelperFile<'_>],
    target: &TslibTarget,
    by_source: &HashMap<SourceId, usize>,
) -> String {
    match target {
        TslibTarget::File(id) => by_source.get(id).map_or_else(
            || "tslib".to_owned(),
            |position| files[*position].path.to_string_lossy().into_owned(),
        ),
        TslibTarget::OnDisk(path) => std::fs::canonicalize(path)
            .map(|canonical| canonical.to_string_lossy().into_owned())
            .unwrap_or_else(|_| path.to_string_lossy().into_owned()),
        TslibTarget::Ambient(id) => format!("ambient:{id:?}"),
    }
}

/// Value export names of top-level statements. `export {}` contributes none;
/// `export =` and `export *` are not followed.
fn collect_value_exports(
    source: &SourceFile,
    statements: &[crate::syntax::Stmt],
    names: &mut std::collections::BTreeSet<String>,
) {
    use crate::syntax::{ExportDeclaration, ExportNamedDeclaration, Statement};
    for statement in statements {
        match statement.data() {
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => {
                collect_exported_declaration(source, inner, names);
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only: false,
                specifiers,
                ..
            })) => {
                for specifier in specifiers {
                    let exported = export_name_text(source, &specifier.data().exported);
                    if !exported.is_empty() {
                        names.insert(exported);
                    }
                }
            }
            Statement::Declare(inner) => {
                collect_declared_exports(source, inner, names);
            }
            _ => {}
        }
    }
}

/// Value export names inside `declare module "tslib"`.
fn collect_ambient_tslib_exports(
    source: &SourceFile,
    names: &mut std::collections::BTreeSet<String>,
) {
    use crate::syntax::{NamespaceName, Statement};
    for statement in source.statements() {
        let mut current = statement;
        loop {
            match current.data() {
                Statement::Declare(inner) => current = inner,
                Statement::Export(crate::syntax::ExportDeclaration::Named(
                    crate::syntax::ExportNamedDeclaration::Declaration(inner),
                )) => current = inner,
                Statement::Namespace(namespace) => {
                    if matches!(&namespace.name, NamespaceName::StringLiteral(literal) if source.token_text(literal.data().token()).is_some_and(|text| text.trim_matches(|character| character == '\'' || character == '"') == "tslib"))
                    {
                        collect_value_exports(source, &namespace.body.data().statements, names);
                    }
                    break;
                }
                _ => break,
            }
        }
    }
}

/// Names a value declaration exports under `export`.
fn collect_exported_declaration(
    source: &SourceFile,
    inner: &crate::syntax::Stmt,
    names: &mut std::collections::BTreeSet<String>,
) {
    use crate::syntax::Statement;
    match inner.data() {
        Statement::Variable(declaration) => {
            for declarator in &declaration.declarations {
                collect_binding_names(&declarator.data().binding, names, source);
            }
        }
        Statement::Function(function) => {
            if let Some(name) = &function.function.name
                && let Some(text) = source.token_text(name.data().token())
            {
                names.insert(text.to_owned());
            }
        }
        Statement::Class(class) => {
            if let Some(name) = &class.name
                && let Some(text) = source.token_text(name.data().token())
            {
                names.insert(text.to_owned());
            }
        }
        Statement::Enum(declaration) => {
            if let Some(text) = source.token_text(declaration.name.data().token()) {
                names.insert(text.to_owned());
            }
        }
        Statement::Namespace(namespace) => {
            if let crate::syntax::NamespaceName::Identifier { name, .. } = &namespace.name
                && let Some(text) = source.token_text(name.data().token())
            {
                names.insert(text.to_owned());
            }
        }
        Statement::Declare(inner) => collect_declared_exports(source, inner, names),
        _ => {}
    }
}

/// `declare`-wrapped declarations still export when named.
fn collect_declared_exports(
    source: &SourceFile,
    inner: &crate::syntax::Stmt,
    names: &mut std::collections::BTreeSet<String>,
) {
    use crate::syntax::Statement;
    match inner.data() {
        Statement::Export(_) => collect_value_exports(source, std::slice::from_ref(inner), names),
        _ => collect_exported_declaration(source, inner, names),
    }
}

/// Identifier names bound by a pattern.
fn collect_binding_names(
    pattern: &crate::syntax::Pattern,
    names: &mut std::collections::BTreeSet<String>,
    source: &SourceFile,
) {
    use crate::syntax::BindingPattern;
    match pattern.data() {
        BindingPattern::Identifier(name) => {
            if let Some(text) = source.token_text(name.data().token()) {
                names.insert(text.to_owned());
            }
        }
        BindingPattern::Object(object) => {
            for property in &object.properties {
                collect_binding_names(&property.binding, names, source);
            }
        }
        BindingPattern::Array(array) => {
            for element in &array.elements {
                if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                    collect_binding_names(inner, names, source);
                }
            }
        }
        BindingPattern::Rest(rest) => collect_binding_names(&rest.argument, names, source),
        BindingPattern::Assignment(assignment) => {
            collect_binding_names(&assignment.left, names, source)
        }
        BindingPattern::Missing(_) => {}
    }
}

/// Exported name text for an export specifier side.
fn export_name_text(source: &SourceFile, name: &crate::syntax::ModuleExportName) -> String {
    match name {
        crate::syntax::ModuleExportName::Identifier(identifier) => source
            .token_text(identifier.data().token())
            .unwrap_or_default()
            .to_owned(),
        crate::syntax::ModuleExportName::String(literal) => source
            .token_text(literal.data().token())
            .map_or_else(String::new, |text| {
                text.trim_matches(|character| character == '\'' || character == '"')
                    .to_owned()
            }),
        crate::syntax::ModuleExportName::Missing(_) => String::new(),
    }
}

pub fn compile_program_frontend_with_cancel(
    program: &ResolvedProgram,
    mode: FrontendMode,
    levels: &LintTable,
    cancel: &CancellationToken,
) -> Result<ProgramFrontendOutput, Cancelled> {
    Telemetry::measure(Phase::Total, || {
        cancel.check()?;
        let mut parsed = Vec::with_capacity(program.modules().len());
        for module in program.modules() {
            cancel.check()?;
            let scanned = Telemetry::measure(Phase::Scan, || {
                scanner::scan_with_cancel(
                    module.source_id(),
                    module.script_kind(),
                    Arc::clone(module.source()),
                    cancel.clone(),
                )
            })
            .map_err(Cancelled::from)?;
            cancel.check()?;
            parsed.push(
                Telemetry::measure(Phase::Parse, || {
                    parser::parse_with_cancel(scanned, cancel.clone())
                })
                .map_err(Cancelled::from)?,
            );
            cancel.check()?;
        }

        let edges = resolved_checker_edges_with_cancel(program, &parsed, cancel)?;
        cancel.check()?;
        let ambient_modules = ambient_module_names(&parsed);
        let checked = Telemetry::measure(Phase::Check, || {
            checker::check_program_with_options_and_cancel(
                ProgramCheckInput {
                    files: &parsed,
                    edges: &edges,
                },
                levels,
                program.check_options(),
                cancel.clone(),
            )
        })
        .map_err(Cancelled::from)?;
        cancel.check()?;
        let program_diagnostics = checked.diagnostics();
        let tslib_diagnostics = tslib_helper_diagnostics_for_program(program, &parsed);
        let mut modules = Vec::with_capacity(parsed.len());
        for (index, parsed) in parsed.into_iter().enumerate() {
            cancel.check()?;
            let source_id = parsed.product().source_id();
            let semantic_model = checked
                .product()
                .file(source_id)
                .expect("whole-program checker returns every parsed module")
                .clone();
            let module = &program.modules()[index];
            let source_name = Arc::from(
                module
                    .path()
                    .to_string_lossy()
                    .into_owned()
                    .into_boxed_str(),
            );
            let mut js_path = module.path().to_path_buf();
            let keeps_jsx = matches!(
                program.jsx(),
                None | Some(crate::source::JsxEmit::Preserve | crate::source::JsxEmit::ReactNative)
            ) && matches!(
                module.script_kind(),
                ScriptKind::TypeScriptReact | ScriptKind::JavaScriptReact
            );
            js_path.set_extension(if keeps_jsx { "jsx" } else { "js" });
            let names = EmitFileNames {
                source_name,
                js_file_name: js_path.file_name().map(|name| {
                    Arc::from(name.to_string_lossy().into_owned().into_boxed_str())
                }),
                declaration_file_name: None,
                source_root: None,
                js_source_name: module.path().file_name().map(|name| {
                    Arc::from(name.to_string_lossy().into_owned().into_boxed_str())
                }),
                ..EmitFileNames::default()
            };
            let emit = if let Some(options) = program_emit_options(program, mode, index) {
                cancel.check()?;
                let output = Telemetry::measure(Phase::Emit, || {
                    emitter::emit_checked(parsed.product(), &semantic_model, &options, &names)
                });
                cancel.check()?;
                Some(output)
            } else {
                None
            };
            let (source_file, mut diagnostics) = parsed.into_parts();
            diagnostics.extend(
                program_diagnostics
                    .iter()
                    .filter(|diagnostic| diagnostic.source_id() == source_id)
                    .cloned(),
            );
            diagnostics.extend(unresolved_import_diagnostics(module, &ambient_modules));
            if let Some(extra) = tslib_diagnostics.get(&source_id) {
                diagnostics.extend(extra.iter().cloned());
            }
            if let Some(output) = &emit {
                diagnostics.extend(output.diagnostics.iter().cloned());
            }
            modules.push(FrontendOutput {
                mode,
                source_file,
                semantic_model,
                emit,
                diagnostics: canonicalize(diagnostics),
            });
            cancel.check()?;
        }
        cancel.check()?;
        let index = ProgramFrontendOutput::module_index(&modules);
        Ok(ProgramFrontendOutput {
            entrypoint: program.entrypoint_id(),
            modules,
            index,
        })
    })
}

fn resolved_checker_edges_with_cancel(
    program: &ResolvedProgram,
    files: &[Recovered<SourceFile>],
    cancel: &CancellationToken,
) -> Result<Vec<ResolvedModuleEdge>, Cancelled> {
    let mut by_source = HashMap::with_capacity(files.len());
    for (position, file) in files.iter().enumerate() {
        by_source
            .entry(file.product().source_id())
            .or_insert(position);
    }
    let mut edges = Vec::new();
    for module in program.modules() {
        cancel.check()?;
        let position = by_source
            .get(&module.source_id())
            .expect("resolved module has one parsed source");
        let source = files[*position].product();
        let nodes = SourceEdgeNodeIndex::new(source);
        for edge in module.dependencies() {
            cancel.check()?;
            let ModuleTarget::Local(to) = edge.type_target().unwrap_or_else(|| edge.target())
            else {
                continue;
            };
            let Some(specifier) = nodes.node_for(edge.range()) else {
                continue;
            };
            edges.push(ResolvedModuleEdge {
                from: module.source_id(),
                specifier,
                to: *to,
            });
        }
    }
    cancel.check()?;
    Ok(edges)
}

/// Runs the fixed frontend pipeline with settled default lint levels.
#[must_use]
pub fn compile_frontend(request: FrontendRequest) -> FrontendOutput {
    compile_frontend_with_lints(request, &LintTable::new(LintProfile::Default))
}

/// Runs the fixed scan -> parse -> check -> optional emit frontend pipeline
/// using the caller's resolved lint table.
///
/// Every stage runs regardless of the diagnostics its predecessor produced, so
/// the returned [`FrontendOutput`] always carries a recovered `SourceFile` and
/// `SemanticModel`. Emit is produced only when the request mode asks for one
/// and neither `no_emit` nor `no_emit_on_error` (when pre-emit errors exist)
/// suppresses it. All stage diagnostics are merged, canonically ordered, and
/// de-duplicated into one vector.
#[must_use]
pub fn compile_frontend_with_lints(request: FrontendRequest, levels: &LintTable) -> FrontendOutput {
    let FrontendRequest {
        source_id,
        script_kind,
        source,
        mode,
        no_emit,
        no_emit_on_error,
    } = request;

    let scanned = scanner::scan(source_id, script_kind, source);
    let parsed = parser::parse(scanned);
    let checked = checker::check_with_lints(&parsed, levels);

    let pre_emit_diagnostics: Vec<Diagnostic> = parsed
        .diagnostics()
        .iter()
        .chain(checked.diagnostics().iter())
        .cloned()
        .collect();
    let pre_emit_has_errors = pre_emit_diagnostics
        .iter()
        .any(|diagnostic| !diagnostic.is_warning());
    let should_emit = !no_emit && !(no_emit_on_error && pre_emit_has_errors);

    let names = EmitFileNames {
        source_name: Arc::from(format!("source{}.ts", source_id.get()).into_boxed_str()),
        js_file_name: None,
        source_root: None,
        ..EmitFileNames::default()
    };
    let emit = if should_emit {
        mode.emit_options().map(|options| {
            emitter::emit_checked(parsed.product(), checked.product(), &options, &names)
        })
    } else {
        None
    };

    let (source_file, _) = parsed.into_parts();
    let (semantic_model, _) = checked.into_parts();

    let mut diagnostics = pre_emit_diagnostics;
    if let Some(output) = &emit {
        diagnostics.extend(output.diagnostics.iter().cloned());
    }
    let diagnostics = canonicalize(diagnostics);

    FrontendOutput {
        mode,
        source_file,
        semantic_model,
        emit,
        diagnostics,
    }
}

/// Orders diagnostics by the canonical [`Diagnostic`] key and removes exact
/// duplicates.
///
/// The canonical order is a total order over `(source, range, code, severity,
/// message)`, so sorting groups every identical diagnostic and `dedup` collapses
/// only exact duplicates: two diagnostics differing in any of severity, range,
/// or code are never merged.
fn canonicalize(mut diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics.sort();
    diagnostics.dedup();
    diagnostics
}

#[cfg(test)]
mod tests {
    use super::{
        FrontendMode, FrontendOutput, FrontendRequest, ProgramFrontendOutput, canonicalize,
        compile_frontend, compile_program_frontend, compile_program_frontend_with_cancel,
        resolved_checker_edges_with_cancel,
    };
    use crate::diagnostic::{Diagnostic, DiagnosticCode, DiagnosticSeverity};
    use crate::lint::{LintProfile, LintTable};
    use crate::program::{ProgramLoader, ResolvedProgram};
    use crate::project::{ProjectConfig, ProjectRoot};
    use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
    use crate::telemetry::{Phase, TelemetryCollector};
    use bamts_cancel::{CancellationToken, Cancelled};
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn request(source: &str, mode: FrontendMode) -> FrontendRequest {
        request_with(source, mode, false, false)
    }

    fn request_with(
        source: &str,
        mode: FrontendMode,
        no_emit: bool,
        no_emit_on_error: bool,
    ) -> FrontendRequest {
        FrontendRequest {
            source_id: SourceId::new(0),
            script_kind: ScriptKind::TypeScript,
            source: Arc::new(
                SourceText::new(source).expect("test source fits the per-file budget"),
            ),
            mode,
            no_emit,
            no_emit_on_error,
        }
    }

    fn program_fixture_with_config(
        source: &str,
        config_source: &str,
    ) -> (PathBuf, ResolvedProgram) {
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-emit-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&root_path).expect("create pipeline fixture");
        std::fs::write(root_path.join("main.ts"), source).expect("write pipeline fixture");
        let root = ProjectRoot::new(std::fs::canonicalize(&root_path).expect("canonical fixture"))
            .expect("valid project root");
        let config = ProjectConfig::parse(&root, root_path.join("tsconfig.json"), config_source)
            .expect("valid project config");
        let program = ProgramLoader::new(&root, config.options())
            .expect("construct program loader")
            .load("main.ts")
            .expect("load fixture program");
        (root_path, program)
    }

    /// Writes `files` to a fresh project and returns its root and config.
    fn project(files: &[(&str, &str)]) -> (PathBuf, ProjectRoot, ProjectConfig) {
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-unresolved-{}-{}",
            std::process::id(),
            files.len()
        ));
        let _ = std::fs::remove_dir_all(&root_path);
        for (name, text) in files {
            let path = root_path.join(name);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("create fixture directory");
            std::fs::write(path, text).expect("write fixture file");
        }
        let root = ProjectRoot::new(std::fs::canonicalize(&root_path).expect("canonical fixture"))
            .expect("valid project root");
        let config = ProjectConfig::parse(
            &root,
            root_path.join("tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("valid project config");
        (root_path, root, config)
    }

    #[test]
    fn a_check_run_reports_every_unresolved_import() {
        let (root_path, root, config) = project(&[
            (
                "main.ts",
                "import a from 'missing';\n\
                 import b from './gone';\n\
                 import c from 'declared';\n\
                 import d from 'pattern.css';\n\
                 import e from 'typed';\n\
                 declare module 'declared' {}\n\
                 declare module '*.css' {}\n",
            ),
            (
                "node_modules/typed/package.json",
                r#"{"name":"typed","types":"./lib/index.d.ts"}"#,
            ),
            ("node_modules/typed/lib/index.d.ts", "export default 1;\n"),
        ]);
        let loader = ProgramLoader::new(&root, config.options()).expect("construct loader");
        assert!(
            loader.clone().load("main.ts").is_err(),
            "a run that executes must still refuse an unresolved import"
        );
        let program = loader
            .tolerating_unresolved_imports()
            .load("main.ts")
            .expect("a check run keeps going");
        assert_eq!(
            program.modules().len(),
            2,
            "`typed` resolves as `tsc` would"
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let entry = output
            .modules()
            .iter()
            .find(|module| module.source_file().source_id() == output.entrypoint_id())
            .expect("entrypoint module present");
        let reported: Vec<_> = entry
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str() == "TS2307")
            .map(|diagnostic| diagnostic.message().to_owned())
            .collect();
        assert_eq!(reported.len(), 2, "{reported:?}");
        assert!(reported[0].contains("'missing'"), "{reported:?}");
        assert!(reported[1].contains("'./gone'"), "{reported:?}");
        let _ = std::fs::remove_dir_all(root_path);
    }

    fn tslib_case(files: &[(&str, &str)], config: &str) -> (PathBuf, ResolvedProgram) {
        static NEXT_TSLIB_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-tslib-{}-{}",
            std::process::id(),
            NEXT_TSLIB_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&root_path);
        for (name, text) in files {
            let path = root_path.join(name);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("create fixture directory");
            std::fs::write(path, text).expect("write fixture file");
        }
        let root = ProjectRoot::new(std::fs::canonicalize(&root_path).expect("canonical fixture"))
            .expect("valid project root");
        let config = ProjectConfig::parse(&root, root_path.join("tsconfig.json"), config)
            .expect("valid project config");
        let program = ProgramLoader::new(&root, config.options())
            .expect("construct loader")
            .tolerating_unresolved_imports()
            .load("main.ts")
            .expect("load fixture program");
        (root_path, program)
    }

    fn entry_diagnostics(output: &ProgramFrontendOutput, code: &str) -> Vec<(usize, String)> {
        let entry = output
            .modules()
            .iter()
            .find(|module| module.source_file().source_id() == output.entrypoint_id())
            .expect("entrypoint module present");
        let source = entry.source_file().source_text();
        entry
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str() == code)
            .map(|diagnostic| {
                let (line, _) = source
                    .line_column(diagnostic.range().start())
                    .expect("diagnostic range is in bounds");
                (line, diagnostic.message().to_owned())
            })
            .collect()
    }


    fn entry_ranges(output: &ProgramFrontendOutput, code: &str) -> Vec<(usize, usize, usize, usize, String)> {
        let entry = output
            .modules()
            .iter()
            .find(|module| module.source_file().source_id() == output.entrypoint_id())
            .expect("entrypoint module present");
        let source = entry.source_file().source_text();
        entry
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str() == code)
            .map(|diagnostic| {
                let (start_line, start_column) = source
                    .line_column(diagnostic.range().start())
                    .expect("diagnostic range is in bounds");
                let (end_line, end_column) = source
                    .line_column(diagnostic.range().end())
                    .expect("diagnostic range is in bounds");
                (
                    start_line,
                    start_column,
                    end_line,
                    end_column,
                    diagnostic.message().to_owned(),
                )
            })
            .collect()
    }


    const TSLIB_HELPERS_CONFIG: &str =
        r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015"}}"#;

    #[test]
    fn missing_tslib_helper_reports_ts2343_at_async_name() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "export {};\nexport async function foo(): Promise<void> {}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert_eq!(reported.len(), 1, "{reported:?}");
        assert_eq!(reported[0].0, 1, "{reported:?}");
        assert!(reported[0].1.contains("__awaiter"), "{reported:?}");
        assert!(reported[0].1.contains("tslib"), "{reported:?}");
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn declared_tslib_helper_is_silent() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "export {};\nexport async function foo(): Promise<void> {}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export declare function __awaiter(thisArg: any, _arguments: any, P: Function, generator: Function): any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        assert!(entry_diagnostics(&output, "TS2354").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn missing_tslib_module_reports_ts2354() {
        let (root_path, program) = tslib_case(
            &[(
                "main.ts",
                "export {};\nexport async function foo(): Promise<void> {}\n",
            )],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2354");
        assert_eq!(reported.len(), 1, "{reported:?}");
        assert_eq!(reported[0].0, 1, "{reported:?}");
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn script_file_needs_no_tslib_check() {
        let (root_path, program) = tslib_case(
            &[("main.ts", "async function foo(): Promise<void> {}\n")],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        assert!(entry_diagnostics(&output, "TS2354").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn import_star_without_tslib_reports_ts2354_at_statement() {
        let (root_path, program) = tslib_case(
            &[(
                "main.ts",
                "import * as path from \"path\";\ndeclare module \"path\";\npath.resolve();\nexport {};\n",
            )],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015","esModuleInterop":true}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2354");
        assert_eq!(reported.len(), 1, "{reported:?}");
        assert_eq!(reported[0].0, 0, "{reported:?}");
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn oversize_or_non_regular_on_disk_tslib_is_unresolved() {
        static NEXT_DISK_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "bamts-pipeline-tslib-disk-{}-{}",
            std::process::id(),
            NEXT_DISK_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).expect("create disk fixture");
        let path = root.join("tslib.js");
        std::fs::write(&path, "export function __awaiter() {}\n").expect("write small tslib");
        assert!(
            super::tslib_on_disk_source(&path).is_some(),
            "a small regular tslib copy parses"
        );
        let big = "x".repeat(super::TSLIB_ON_DISK_READ_CAP as usize + 1);
        std::fs::write(&path, big).expect("write oversize tslib");
        assert!(
            super::tslib_on_disk_source(&path).is_none(),
            "an oversize tslib copy is unresolved (TS2354)"
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            let link = root.join("link.js");
            symlink("/dev/null", &link).expect("link a non-regular file");
            assert!(
                super::tslib_on_disk_source(&link).is_none(),
                "a non-regular tslib path is unresolved (TS2354)"
            );
        }
        let dir_js = root.join("dir.js");
        std::fs::create_dir_all(&dir_js).expect("create dir with js extension");
        assert!(
            super::tslib_on_disk_source(&dir_js).is_none(),
            "a non-regular tslib path is unresolved (TS2354)"
        );
        let _ = std::fs::remove_dir_all(root);
    }
    #[test]
    fn oversize_on_disk_tslib_reports_ts2354_not_ts2343() {
        let (root_path, program) = tslib_case(
            &[(
                "main.ts",
                "export {};\nexport async function foo(): Promise<void> {}\n",
            )],
            TSLIB_HELPERS_CONFIG,
        );
        let tslib = root_path.join("node_modules/tslib/tslib.d.ts");
        std::fs::create_dir_all(tslib.parent().expect("tslib has a parent"))
            .expect("create tslib dir");
        std::fs::write(
            &tslib,
            "x".repeat(super::TSLIB_ON_DISK_READ_CAP as usize + 1),
        )
        .expect("write oversize tslib");
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let missing = entry_diagnostics(&output, "TS2354");
        assert_eq!(missing.len(), 1, "{missing:?}");
        assert!(
            entry_diagnostics(&output, "TS2343").is_empty(),
            "an unreadable copy is unresolved, not a missing helper"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn extends_helper_missing_reports_ts2343_with_es5_gating() {
        let source = "export {};\nclass Base {}\nclass Child extends Base {}\n";
        let missing = [(
            "node_modules/tslib/tslib.d.ts",
            "export const notAHelper: any;\n",
        )];
        let mut files: Vec<(&str, &str)> = vec![("main.ts", source)];
        files.extend(missing);
        let (root_path, program) = tslib_case(
            &files,
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es5"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert!(
            reported.iter().any(|(_, message)| message.contains("__extends")),
            "missing __extends reports TS2343: {reported:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
        let (root_path, program) = tslib_case(
            &[("main.ts", source)],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        assert!(entry_diagnostics(&output, "TS2354").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn standard_decorator_helpers_missing_report_es_decorate() {
        let source = "export {};\nfunction dec(value: any, context: any): any {}\n@dec class C {}\n";
        let (root_path, program) = tslib_case(
            &[
                ("main.ts", source),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert!(
            reported.iter().any(|(_, message)| message.contains("__esDecorate")),
            "missing __esDecorate reports TS2343: {reported:?}"
        );
        assert!(
            reported.iter().any(|(_, message)| message.contains("__runInitializers")),
            "missing __runInitializers reports TS2343: {reported:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn async_generator_helpers_follow_target_gating() {
        let source = "export async function* g() {}\n";
        let (root_path, program) = tslib_case(
            &[
                ("main.ts", source),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert!(
            reported.iter().any(|(_, message)| message.contains("__asyncGenerator")),
            "missing __asyncGenerator reports TS2343: {reported:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
        let (root_path, program) = tslib_case(
            &[("main.ts", source)],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2018"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        assert!(entry_diagnostics(&output, "TS2354").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn template_object_helper_needs_es5() {
        let source = "export {};\nfunction tag(s: any): any {}\nconst v = tag`x`;\n";
        let (root_path, program) = tslib_case(
            &[
                ("main.ts", source),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es5"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert!(
            reported.iter().any(|(_, message)| message.contains("__makeTemplateObject")),
            "missing __makeTemplateObject reports TS2343: {reported:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
        let (root_path, program) = tslib_case(
            &[("main.ts", source)],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn missing_helper_reports_once_per_tslib_copy() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "import './other';\nexport async function foo(): Promise<void> {}\n",
                ),
                (
                    "other.ts",
                    "export async function bar(): Promise<void> {}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let mut count = 0;
        for module in output.modules() {
            count += module
                .diagnostics()
                .iter()
                .filter(|diagnostic| {
                    diagnostic.code().as_str() == "TS2343"
                        && diagnostic.message().contains("__awaiter")
                })
                .count();
        }
        assert_eq!(count, 1, "one TS2343 per helper per tslib copy");
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn helper_check_is_silent_without_import_helpers() {
        let (root_path, program) = tslib_case(
            &[(
                "main.ts",
                "export {};\nexport async function foo(): Promise<void> {}\n",
            )],
            r#"{"compilerOptions":{"module":"commonjs","target":"es2015"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(entry_diagnostics(&output, "TS2343").is_empty());
        assert!(entry_diagnostics(&output, "TS2354").is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn tslib_helper_table_reports_each_walk_helper() {
        const ES5: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es5"}}"#;
        const ES2015: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015"}}"#;
        const ES2018: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2018"}}"#;
        const ES2020: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2020"}}"#;
        const ES2022: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2022"}}"#;
        const EXP_ES2015: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015","experimentalDecorators":true,"emitDecoratorMetadata":true}}"#;
        const EXP_NO_METADATA_ES2015: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015","experimentalDecorators":true}}"#;
        const MODULE_ES2015: &str = r#"{"compilerOptions":{"importHelpers":true,"module":"es2015","target":"es2015"}}"#;
        struct Row {
            name: &'static str,
            source: &'static str,
            extra: &'static [(&'static str, &'static str)],
            config: &'static str,
            expected: &'static [(&'static str, usize, usize, usize, usize)],
        }
        let rows: &[Row] = &[
            Row {
                name: "awaiter",
                source: "export {};\nexport async function foo(): Promise<void> {}\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 1, 22, 1, 25)],
            },
            Row {
                name: "awaiter_gated_es2018",
                source: "export {};\nexport async function foo(): Promise<void> {}\n",
                extra: &[],
                config: ES2018,
                expected: &[],
            },
            Row {
                name: "generator",
                source: "export {};\nfunction* g() {}\n",
                extra: &[],
                config: ES5,
                expected: &[("__generator", 1, 10, 1, 11)],
            },
            Row {
                name: "generator_gated_es2015",
                source: "export {};\nfunction* g() {}\n",
                extra: &[],
                config: ES2015,
                expected: &[],
            },
            Row {
                name: "async_generator_pair",
                source: "export async function* g() {}\n",
                extra: &[],
                config: ES2015,
                expected: &[("__asyncGenerator", 0, 23, 0, 24), ("__await", 0, 23, 0, 24)],
            },
            Row {
                name: "async_delegator_quad",
                source: "export async function* g() {\n  yield* [1];\n}\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__asyncGenerator", 0, 23, 0, 24),
                    ("__await", 0, 23, 0, 24),
                    ("__asyncDelegator", 1, 2, 1, 7),
                    ("__asyncValues", 1, 2, 1, 7),
                ],
            },
            Row {
                name: "async_generator_gated_es2018",
                source: "export async function* g() {}\n",
                extra: &[],
                config: ES2018,
                expected: &[],
            },
            Row {
                name: "extends",
                source: "export {};\nclass A {}\nclass B extends A {}\n",
                extra: &[],
                config: ES5,
                expected: &[("__extends", 2, 8, 2, 17)],
            },
            Row {
                name: "extends_gated_es2015",
                source: "export {};\nclass A {}\nclass B extends A {}\n",
                extra: &[],
                config: ES2015,
                expected: &[],
            },
            Row {
                name: "assign",
                source: "export {};\nconst o = { a: 1 };\nconst y = { ...o };\n",
                extra: &[],
                config: ES5,
                expected: &[("__assign", 2, 15, 2, 16)],
            },
            Row {
                name: "assign_gated_es2015",
                source: "export {};\nconst o = { a: 1 };\nconst y = { ...o };\n",
                extra: &[],
                config: ES2015,
                expected: &[],
            },
            Row {
                name: "rest",
                source: "export {};\nconst y = { a: 1 };\nconst { ...x } = y;\n",
                extra: &[],
                config: ES2015,
                expected: &[("__rest", 2, 11, 2, 12)],
            },
            Row {
                name: "rest_gated_es2018",
                source: "export {};\nconst y = { a: 1 };\nconst { ...x } = y;\n",
                extra: &[],
                config: ES2018,
                expected: &[],
            },
            Row {
                name: "experimental_decorators",
                source: "export {};\ndeclare var dec: any;\n@dec\nclass C {\n  method(@dec x: number) {}\n}\n",
                extra: &[],
                config: EXP_ES2015,
                expected: &[
                    ("__decorate", 2, 0, 2, 4),
                    ("__metadata", 2, 0, 2, 4),
                    ("__param", 4, 9, 4, 13),
                ],
            },
            Row {
                name: "es_decorate_pair",
                source: "export {};\ndeclare var dec: any;\n@dec\nclass C {}\n",
                extra: &[],
                config: ES2015,
                expected: &[("__esDecorate", 2, 0, 2, 4), ("__runInitializers", 2, 0, 2, 4)],
            },
            Row {
                name: "member_method_decorator_set_function_name",
                source: "export {};\ndeclare var dec: any;\nclass C {\n  @dec\n  m() {}\n}\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__esDecorate", 3, 2, 3, 6),
                    ("__runInitializers", 3, 2, 3, 6),
                    ("__setFunctionName", 3, 2, 3, 6),
                ],
            },
            Row {
                name: "param_decorator_without_metadata",
                source: "export {};\ndeclare var dec: any;\nclass C {\n  method(@dec x: number) {}\n}\n",
                extra: &[],
                config: EXP_NO_METADATA_ES2015,
                expected: &[("__decorate", 3, 9, 3, 13), ("__param", 3, 9, 3, 13)],
            },
            Row {
                name: "prop_key",
                source: "export {};\ndeclare var dec: any;\ndeclare var x: any;\nclass C {\n  @dec static accessor [x]: any;\n}\n",
                extra: &[],
                config: ES2022,
                expected: &[
                    ("__esDecorate", 4, 2, 4, 6),
                    ("__propKey", 4, 2, 4, 6),
                    ("__runInitializers", 4, 2, 4, 6),
                ],
            },
            Row {
                name: "make_template_object",
                source: "export {};\nfunction tag(s: any): any { return s; }\nconst v = tag`x`;\n",
                extra: &[],
                config: ES5,
                expected: &[("__makeTemplateObject", 2, 12, 2, 17)],
            },
            Row {
                name: "make_template_object_gated_es2015",
                source: "export {};\nfunction tag(s: any): any { return s; }\nconst v = tag`x`;\n",
                extra: &[],
                config: ES2015,
                expected: &[],
            },
            Row {
                name: "import_star",
                source: "import * as ns from \"dep\";\ndeclare module \"dep\";\nexport {};\nns;\n",
                extra: &[],
                config: ES2015,
                expected: &[("__importStar", 0, 0, 0, 26)],
            },
            Row {
                name: "import_default_named",
                source: "import { default as foo } from \"dep\";\ndeclare module \"dep\";\nexport {};\nfoo;\n",
                extra: &[],
                config: ES2015,
                expected: &[("__importDefault", 0, 9, 0, 23)],
            },
            Row {
                name: "import_default_clause",
                source: "import foo from \"dep\";\ndeclare module \"dep\";\nexport {};\nfoo;\n",
                extra: &[],
                config: ES2015,
                expected: &[("__importDefault", 0, 0, 0, 22)],
            },
            Row {
                name: "combined_default_namespace_reports_only_import_star",
                source: "import greet, * as dependency from \"dep\";\ndeclare module \"dep\";\nexport {};\ngreet;\ndependency;\n",
                extra: &[],
                config: ES2015,
                expected: &[("__importStar", 0, 0, 0, 41)],
            },
            Row {
                name: "import_default_gated_es2015_module",
                source: "import foo from \"dep\";\ndeclare module \"dep\";\nexport {};\nfoo;\n",
                extra: &[],
                config: MODULE_ES2015,
                expected: &[],
            },
            Row {
                name: "import_star_gated_es2015_module",
                source: "import * as ns from \"dep\";\ndeclare module \"dep\";\nexport {};\nns;\n",
                extra: &[],
                config: MODULE_ES2015,
                expected: &[],
            },
            Row {
                name: "oracle_arrow_argument_reports_awaiter_at_arrow",
                source: "declare function foo(f: any): void;\nfoo(async () => {});\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 1, 4, 1, 18)],
            },
            Row {
                name: "oracle_arrow_initializer_reports_awaiter_at_arrow",
                source: "const f = async () => {};\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 10, 0, 24)],
            },
            Row {
                name: "oracle_function_initializer_reports_awaiter_at_binding",
                source: "const g = async function () {};\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 6, 0, 7)],
            },
            Row {
                name: "oracle_function_argument_reports_awaiter_at_function",
                source: "declare function foo(f: any): void;\nfoo(async function () {});\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 1, 4, 1, 24)],
            },
            Row {
                name: "oracle_async_method_reports_awaiter_at_name",
                source: "class C { async m() {} }\nexport { C };\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 16, 0, 17)],
            },
            Row {
                name: "oracle_async_object_method_reports_awaiter_at_name",
                source: "const o = { async m() {} };\nexport { o };\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 18, 0, 19)],
            },
            Row {
                name: "oracle_nested_arrow_reports_awaiter_at_arrow",
                source: "export async function* gen() { return async () => {}; }\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__asyncGenerator", 0, 23, 0, 26),
                    ("__await", 0, 23, 0, 26),
                    ("__awaiter", 0, 38, 0, 52),
                ],
            },
            Row {
                name: "oracle_default_with_named_reports_import_default_at_statement",
                source: "import d, { a } from \"./dep\";\nexport const x = [d, a];\n",
                extra: &[("dep.ts", "export default 1;\nexport const a = 2;\n")],
                config: ES2015,
                expected: &[("__importDefault", 0, 0, 0, 29)],
            },
            Row {
                name: "oracle_default_with_default_specifier_reports_import_default_at_specifier",
                source: "import d, { default as x } from \"./dep\";\nexport const y = [d, x];\n",
                extra: &[("dep.ts", "export default 1;\nexport const a = 2;\n")],
                config: ES2015,
                expected: &[("__importDefault", 0, 12, 0, 24)],
            },
            Row {
                name: "oracle_unused_default_reports_import_default",
                source: "import foo from \"./dep\";\nexport type T = typeof foo;\n",
                extra: &[("dep.ts", "export default 1;\nexport const a = 2;\n")],
                config: ES2015,
                expected: &[("__importDefault", 0, 0, 0, 24)],
            },
            Row {
                name: "oracle_unused_namespace_reports_import_star",
                source: "import * as ns from \"./dep\";\nexport type U = typeof ns;\n",
                extra: &[("dep.ts", "export default 1;\nexport const a = 2;\n")],
                config: ES2015,
                expected: &[("__importStar", 0, 0, 0, 28)],
            },
            Row {
                name: "oracle_fully_unused_default_reports_import_default",
                source: "import dropped from \"./dep\";\nexport const z = 1;\n",
                extra: &[("dep.ts", "export default 1;\nexport const a = 2;\n")],
                config: ES2015,
                expected: &[("__importDefault", 0, 0, 0, 28)],
            },
            Row {
                name: "oracle_export_default_async_fn_reports_at_statement",
                source: "export default async function () {}\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 0, 0, 35)],
            },
            Row {
                name: "oracle_export_default_async_gen_reports_at_statement",
                source: "export default async function* () {}\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__asyncGenerator", 0, 0, 0, 36),
                    ("__await", 0, 0, 0, 36),
                ],
            },
            Row {
                name: "oracle_paren_function_init_reports_at_function",
                source: "const p = (async function () {});\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 11, 0, 31)],
            },
            Row {
                name: "oracle_double_paren_function_init_reports_at_function",
                source: "const r = ((async function () {}));\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 12, 0, 32)],
            },
            Row {
                name: "oracle_named_export_default_async_fn_reports_at_name",
                source: "export default async function f() {}\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 30, 0, 31)],
            },
            Row {
                name: "oracle_export_default_async_arrow_reports_at_arrow",
                source: "export default async () => {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 15, 0, 29)],
            },
            Row {
                name: "oracle_paren_arrow_init_reports_at_arrow",
                source: "const q = (async () => {});\nexport {};\n",
                extra: &[],
                config: ES2015,
                expected: &[("__awaiter", 0, 11, 0, 25)],
            },
            Row {
                name: "export_star",
                source: "export * from \"./other\";\n",
                extra: &[("other.ts", "export const x = 1;\n")],
                config: ES2015,
                expected: &[("__exportStar", 0, 0, 0, 24)],
            },
            Row {
                name: "export_star_gated_es2015_module",
                source: "export * from \"./other\";\n",
                extra: &[("other.ts", "export const x = 1;\n")],
                config: MODULE_ES2015,
                expected: &[],
            },
            Row {
                name: "export_default_reexport",
                source: "export { default } from \"./other\";\n",
                extra: &[("other.ts", "export default 1;\n")],
                config: ES2015,
                expected: &[("__importDefault", 0, 9, 0, 16)],
            },
            Row {
                name: "using_pair",
                source: "export {};\nusing x = null;\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__addDisposableResource", 1, 0, 1, 15),
                    ("__disposeResources", 1, 0, 1, 15),
                ],
            },
            Row {
                name: "for_using_pair",
                source: "export {};\nfor (using x = null;;) { break; }\n",
                extra: &[],
                config: ES2015,
                expected: &[
                    ("__addDisposableResource", 1, 5, 1, 19),
                    ("__disposeResources", 1, 5, 1, 19),
                ],
            },
            Row {
                name: "private_fields",
                source: "export class Foo {\n  #field = true;\n  f() {\n    this.#field = this.#field;\n    #field in this;\n  }\n}\n",
                extra: &[],
                config: ES2020,
                expected: &[
                    ("__classPrivateFieldSet", 3, 4, 3, 15),
                    ("__classPrivateFieldGet", 3, 18, 3, 29),
                    ("__classPrivateFieldIn", 4, 4, 4, 10),
                ],
            },
            Row {
                name: "private_fields_gated_es2022",
                source: "export class Foo {\n  #field = true;\n  f() {\n    this.#field = this.#field;\n    #field in this;\n  }\n}\n",
                extra: &[],
                config: ES2022,
                expected: &[],
            },
            Row {
                name: "ambient_suppressed",
                source: "export {};\ndeclare class D extends C {}\n",
                extra: &[],
                config: ES5,
                expected: &[],
            },
            Row {
                name: "helpers_off",
                source: "export {};\nexport async function foo(): Promise<void> {}\n",
                extra: &[],
                config: r#"{"compilerOptions":{"module":"commonjs","target":"es2015"}}"#,
                expected: &[],
            },
        ];
        for row in rows {
            let mut files: Vec<(&str, &str)> = vec![
                ("main.ts", row.source),
                ("node_modules/tslib/tslib.d.ts", "export const notAHelper: any;\n"),
            ];
            files.extend_from_slice(row.extra);
            let (root_path, program) = tslib_case(&files, row.config);
            let output = compile_program_frontend(&program, FrontendMode::Check);
            let reported = entry_ranges(&output, "TS2343");
            assert!(
                entry_diagnostics(&output, "TS2354").is_empty(),
                "row {}: tslib is present so TS2354 must not fire: {:?}",
                row.name,
                entry_diagnostics(&output, "TS2354")
            );
            assert_eq!(
                reported.len(),
                row.expected.len(),
                "row {}: report count differs: {reported:?}",
                row.name
            );
            for (
                (helper, start_line, start_column, end_line, end_column),
                (actual_start_line, actual_start_column, actual_end_line, actual_end_column, message),
            ) in row.expected.iter().zip(reported.iter())
            {
                let expected_message = format!(
                    "This syntax requires an imported helper named '{helper}' which does not exist in 'tslib'. Consider upgrading your version of 'tslib'."
                );
                assert_eq!(
                    *message, expected_message,
                    "row {}: helper {helper} text differs",
                    row.name
                );
                assert_eq!(
                    (
                        *actual_start_line,
                        *actual_start_column,
                        *actual_end_line,
                        *actual_end_column
                    ),
                    (*start_line, *start_column, *end_line, *end_column),
                    "row {}: helper {helper} range differs: {reported:?}",
                    row.name
                );
            }
            let _ = std::fs::remove_dir_all(root_path);
        }
    }

    #[test]
    fn allow_synthetic_default_imports_reports_import_default() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "import foo from \"dep\";\ndeclare module \"dep\";\nexport {};\nfoo;\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es2015","allowSyntheticDefaultImports":true}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_ranges(&output, "TS2343");
        assert_eq!(reported.len(), 1, "{reported:?}");
        assert_eq!(
            (reported[0].0, reported[0].1, reported[0].2, reported[0].3),
            (0, 0, 0, 22),
            "{reported:?}"
        );
        assert!(
            reported[0].4.contains("'__importDefault'"),
            "allowSyntheticDefaultImports alone still needs __importDefault: {reported:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn iteration_constructs_need_no_tslib_helper_at_es2015() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "export {};\nfor (const x of [1, 2, 3]) { console.log(x); }\nexport const y = [...[1, 2]];\nexport const [a, b] = [1, 2];\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(
            entry_diagnostics(&output, "TS2343").is_empty(),
            "for-of, spread, and destructuring need no helper at the minimum target: {:?}",
            entry_diagnostics(&output, "TS2343")
        );
        assert!(
            entry_diagnostics(&output, "TS2354").is_empty(),
            "{:?}",
            entry_diagnostics(&output, "TS2354")
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn reexport_needs_only_export_star_from_tslib() {
        let (root_path, program) = tslib_case(
            &[
                ("main.ts", "export * from \"./other\";\n"),
                ("other.ts", "export const x = 1;\n"),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export declare function __exportStar(m: any, exports: any): any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert!(
            entry_diagnostics(&output, "TS2343").is_empty(),
            "__createBinding is never reported on its own: {:?}",
            entry_diagnostics(&output, "TS2343")
        );
        assert!(
            entry_diagnostics(&output, "TS2354").is_empty(),
            "{:?}",
            entry_diagnostics(&output, "TS2354")
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    fn decode_base64(payload: &str) -> Vec<u8> {
        fn sextet(unit: u8) -> u8 {
            match unit {
                b'A'..=b'Z' => unit - b'A',
                b'a'..=b'z' => unit - b'a' + 26,
                b'0'..=b'9' => unit - b'0' + 52,
                b'+' => 62,
                b'/' => 63,
                _ => panic!("inline map payload is base64"),
            }
        }
        let bytes = payload.as_bytes();
        assert!(bytes.len() % 4 == 0, "inline map payload pads to a quartet");
        let mut out = Vec::with_capacity(bytes.len() / 4 * 3);
        for quartet in bytes.chunks_exact(4) {
            let pad = quartet.iter().rev().take_while(|unit| **unit == b'=').count();
            let mut word: u32 = 0;
            for (position, unit) in quartet.iter().enumerate() {
                if *unit != b'=' {
                    word |= u32::from(sextet(*unit)) << (18 - 6 * position);
                }
            }
            out.push((word >> 16) as u8);
            if pad < 2 {
                out.push((word >> 8) as u8);
            }
            if pad < 1 {
                out.push(word as u8);
            }
        }
        out
    }

    #[test]
    fn shared_on_disk_tslib_reports_once_per_helper_across_files() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "import \"./other\";\nexport async function foo(): Promise<void> {}\n",
                ),
                (
                    "other.ts",
                    "export function* g() {}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es5"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let mut reports: Vec<(String, String)> = Vec::new();
        for module in output.modules() {
            let file = program
                .module(module.source_file().source_id())
                .map(|resolved| resolved.path().to_string_lossy().into_owned())
                .unwrap_or_default();

            for diagnostic in module.diagnostics() {
                if diagnostic.code().as_str() == "TS2343" {
                    reports.push((file.clone(), diagnostic.message().to_owned()));
                }
            }
        }
        reports.sort();
        assert_eq!(reports.len(), 2, "{reports:?}");
        assert!(
            reports[0].0.ends_with("main.ts") && reports[0].1.contains("'__awaiter'"),
            "main.ts reports only __awaiter: {reports:?}"
        );
        assert!(
            reports[1].0.ends_with("other.ts") && reports[1].1.contains("'__generator'"),
            "other.ts reports only __generator: {reports:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn inline_source_map_embeds_decodable_map_with_expected_sources() {
        let source = "export const value: number = 1;";
        let config = r#"{"compilerOptions":{"inlineSourceMap":true}}"#;
        let (root_path, program) = program_fixture_with_config(source, config);
        assert!(program.inline_source_map());
        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);
        let prefix = "//# sourceMappingURL=data:application/json;base64,";
        let payload = js
            .lines()
            .find_map(|line| line.strip_prefix(prefix))
            .expect("inline map comment closes the emit");
        let decoded: Vec<u8> = decode_base64(payload);
        let map = String::from_utf8(decoded).expect("inline map is UTF-8 JSON");
        assert!(
            map.contains("\"version\":3"),
            "inline payload is a source map: {map:?}"
        );
        assert!(
            map.contains("main.ts"),
            "inline map names the compiled source: {map:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn inline_sources_embeds_compiled_source_text() {
        let source = "export const value: number = 1;";
        let config = r#"{"compilerOptions":{"inlineSourceMap":true,"inlineSources":true}}"#;
        let (root_path, program) = program_fixture_with_config(source, config);
        assert!(program.inline_sources());
        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);
        let prefix = "//# sourceMappingURL=data:application/json;base64,";
        let payload = js
            .lines()
            .find_map(|line| line.strip_prefix(prefix))
            .expect("inline map comment closes the emit");
        let decoded: Vec<u8> = decode_base64(payload);
        let map = String::from_utf8(decoded).expect("inline map is UTF-8 JSON");
        assert!(
            map.contains(source),
            "inline map carries the compiled source text: {map:?}"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn shared_import_module_exports_computed_once() {
        let (root_path, program) = tslib_case(
            &[
                ("main.ts", "import \"./other\";\nimport \"./shared\";\nexport {};\n"),
                ("other.ts", "import \"./shared\";\nexport const a = 1;\n"),
                ("shared.ts", "export type T = number;\nexport const v = 1;\n"),
            ],
            r#"{"compilerOptions":{"module":"commonjs"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        reset_module_exports_computations();
        let erased = output.erased_exports(&program);
        let counts = module_exports_computations();
        assert_eq!(counts.len(), output.modules().len(), "{counts:?}");
        for module in output.modules() {
            let id = module.source_file().source_id();
            assert_eq!(
                counts.get(&id),
                Some(&1),
                "shared module exports computed once: {counts:?}"
            );
        }
        let shared = output
            .modules()
            .iter()
            .find(|module| {
                program
                    .module(module.source_file().source_id())
                    .is_some_and(|resolved| {
                        resolved.path().file_name().is_some_and(|name| {
                            name.to_string_lossy() == "shared.ts"
                        })
                    })
            })
            .expect("shared module present");
        assert_eq!(
            erased.get(&shared.source_file().source_id()),
            Some(&std::collections::BTreeSet::from(["T".to_owned()])),
            "shared type export is erased"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn tslib_helper_duplicate_use_reports_once_per_helper() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "export {};\nexport async function foo(): Promise<void> {}\nexport async function bar(): Promise<void> {}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        assert_eq!(reported.len(), 1, "{reported:?}");
        assert_eq!(reported[0].0, 1, "{reported:?}");
        assert!(reported[0].1.contains("'__awaiter'"), "{reported:?}");
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn tslib_helper_distinct_copies_report_per_copy() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "import \"./pkg1/index\";\nimport \"./pkg2/index\";\nexport {};\n",
                ),
                (
                    "pkg1/index.ts",
                    "export async function foo(): Promise<void> {}\n",
                ),
                (
                    "pkg1/node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
                (
                    "pkg2/index.ts",
                    "export async function foo(): Promise<void> {}\n",
                ),
                (
                    "pkg2/node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            TSLIB_HELPERS_CONFIG,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let mut count = 0;
        let mut owners: Vec<SourceId> = Vec::new();
        for module in output.modules() {
            for diagnostic in module.diagnostics() {
                if diagnostic.code().as_str() == "TS2343"
                    && diagnostic.message().contains("'__awaiter'")
                {
                    count += 1;
                    owners.push(module.source_file().source_id());
                    let source = module.source_file().source_text();
                    let (line, _) = source
                        .line_column(diagnostic.range().start())
                        .expect("diagnostic range is in bounds");
                    assert_eq!(line, 0, "{diagnostic:?}");
                }
            }
        }
        assert_eq!(count, 2, "one TS2343 per distinct tslib copy");
        assert_ne!(owners[0], owners[1], "copies report in different files");
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn tslib_helper_same_span_orders_alphabetically() {
        let (root_path, program) = tslib_case(
            &[
                (
                    "main.ts",
                    "export async function* g() {\n  yield* [1];\n}\n",
                ),
                (
                    "node_modules/tslib/tslib.d.ts",
                    "export const notAHelper: any;\n",
                ),
            ],
            r#"{"compilerOptions":{"importHelpers":true,"module":"commonjs","target":"es5"}}"#,
        );
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let reported = entry_diagnostics(&output, "TS2343");
        let order = ["__asyncGenerator", "__await", "__generator", "__asyncDelegator", "__asyncValues"];
        assert_eq!(reported.len(), order.len(), "{reported:?}");
        for (index, helper) in order.iter().enumerate() {
            assert!(
                reported[index].1.contains(&format!("'{helper}'")),
                "position {index} must be {helper}: {reported:?}"
            );
        }
        assert_eq!(reported[0].0, 0, "{reported:?}");
        assert_eq!(reported[1].0, 0, "{reported:?}");
        assert_eq!(reported[2].0, 0, "{reported:?}");
        assert_eq!(reported[3].0, 1, "{reported:?}");
        assert_eq!(reported[4].0, 1, "{reported:?}");
        let _ = std::fs::remove_dir_all(root_path);
    }

    fn entrypoint_javascript(output: &ProgramFrontendOutput) -> String {
        let module = output
            .modules()
            .iter()
            .find(|m| m.source_file().source_id() == output.entrypoint_id())
            .expect("entrypoint module present");
        let emit = module.emit().expect("javascript mode emits");
        let js = emit.javascript.as_ref().expect("javascript slot present");
        js.code.clone()
    }
    fn program_fixture(source: &str) -> (PathBuf, ResolvedProgram) {
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-cancel-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&root_path).expect("create pipeline fixture");
        std::fs::write(root_path.join("main.ts"), source).expect("write pipeline fixture");
        let root = ProjectRoot::new(std::fs::canonicalize(&root_path).expect("canonical fixture"))
            .expect("valid project root");
        let config = ProjectConfig::parse(&root, root_path.join("tsconfig.json"), "{}")
            .expect("valid project config");
        let program = ProgramLoader::new(&root, config.options())
            .expect("construct program loader")
            .load("main.ts")
            .expect("load fixture program");
        (root_path, program)
    }

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered range")
    }

    fn has_code(diagnostics: &[Diagnostic], code: &str) -> bool {
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code().as_str() == code)
    }

    fn is_sorted_unique(diagnostics: &[Diagnostic]) -> bool {
        diagnostics.windows(2).all(|pair| pair[0] < pair[1])
    }

    #[test]
    fn merges_syntax_type_and_warning_diagnostics_into_one_ordered_vector() {
        // Warning (unchecked catch property access), a type error (string not
        // assignable to number), and a trailing syntax error (missing initializer)
        // all coexist in one source.
        let source =
            "try {} catch (e) { e.message }\nconst n: number = \"oops\";\nconst bad: number =";
        let output = compile_frontend(request(source, FrontendMode::Check));
        let diagnostics = output.diagnostics();

        // The three stages each contributed at least one diagnostic.
        assert!(has_code(diagnostics, "BAMTS-W005"), "warning stage missing");
        assert!(has_code(diagnostics, "BAMTS-C004"), "type stage missing");
        assert!(
            diagnostics.iter().any(
                |diagnostic| diagnostic.severity() == DiagnosticSeverity::Error
                    && diagnostic.code().as_str() != "BAMTS-C004"
            ),
            "syntax stage missing",
        );

        // Both severities survive the merge.
        assert!(diagnostics.iter().any(Diagnostic::is_warning));
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| !diagnostic.is_warning())
        );

        // The single vector is canonically ordered and free of exact duplicates.
        assert!(is_sorted_unique(diagnostics), "diagnostics not canonical");
    }

    #[test]
    fn emits_despite_earlier_errors() {
        // A type error must not suppress the emit product.
        let source = "const n: number = \"oops\";";
        let output = compile_frontend(request(source, FrontendMode::JavaScript));

        assert!(output.has_errors(), "expected a type error");
        let emit = output.emit().expect("javascript mode must emit");
        let javascript = emit.javascript.as_ref().expect("javascript slot present");
        assert!(
            javascript.code.contains("oops"),
            "emit should still print the recovered program",
        );
    }

    #[test]
    fn check_mode_produces_no_emit_while_js_and_declaration_do() {
        let source = "let value: number = 1;";

        let check = compile_frontend(request(source, FrontendMode::Check));
        assert!(check.emit().is_none(), "check mode must not emit");

        let js = compile_frontend(request(source, FrontendMode::JavaScript));
        let js_emit = js
            .emit()
            .expect("javascript mode emits")
            .javascript
            .as_ref()
            .expect("javascript slot present");

        let declaration = compile_frontend(request(source, FrontendMode::Declaration));
        let declaration_emit = declaration
            .emit()
            .expect("declaration mode emits")
            .declaration
            .as_ref()
            .expect("declaration slot present");

        // JavaScript erases the type annotation; the declaration surface keeps it.
        assert!(!js_emit.code.contains("number"), "js must erase the type");
        assert!(
            declaration_emit.code.contains("number"),
            "declaration must retain the type",
        );
        assert_ne!(js_emit.code, declaration_emit.code);
    }

    #[test]
    fn no_emit_skips_emit_stage_entirely() {
        let source = "let value: number = 1;";
        let output = compile_frontend(request_with(source, FrontendMode::JavaScript, true, false));

        assert!(output.emit().is_none(), "no_emit must suppress emit");
    }

    #[test]
    fn no_emit_on_error_suppresses_emit_when_errors_present() {
        let source = "const n: number = \"oops\";";
        let output = compile_frontend(request_with(source, FrontendMode::JavaScript, false, true));

        assert!(output.has_errors(), "expected a type error");
        assert!(
            output.emit().is_none(),
            "no_emit_on_error must suppress emit"
        );
    }

    #[test]
    fn canonicalize_collapses_exact_duplicates_and_preserves_distinct_ones() {
        let source_id = SourceId::new(0);
        let code = DiagnosticCode::new("BAMTS-C001");
        let base = Diagnostic::error(code, source_id, range(0, 1), "duplicate");
        let duplicate = base.clone();
        // Distinct in severity only.
        let as_warning = Diagnostic::warning(code, source_id, range(0, 1), "duplicate");
        // Distinct in range only.
        let elsewhere = Diagnostic::error(code, source_id, range(2, 3), "duplicate");
        // Distinct in code only.
        let other_code = Diagnostic::error(
            DiagnosticCode::new("BAMTS-C002"),
            source_id,
            range(0, 1),
            "duplicate",
        );

        let merged = canonicalize(vec![
            base.clone(),
            duplicate,
            as_warning.clone(),
            elsewhere.clone(),
            other_code.clone(),
            base.clone(),
        ]);

        // The two exact copies collapse to one; every distinct diagnostic remains.
        assert_eq!(merged.len(), 4);
        assert_eq!(merged.iter().filter(|d| **d == base).count(), 1);
        assert!(merged.contains(&as_warning));
        assert!(merged.contains(&elsewhere));
        assert!(merged.contains(&other_code));
        assert!(is_sorted_unique(&merged));
    }

    #[test]
    fn frontend_output_never_contains_duplicate_diagnostics() {
        let source =
            "try {} catch (e) { e.message }\nconst n: number = \"oops\";\nconst bad: number =";
        let output = compile_frontend(request(source, FrontendMode::JavaScript));
        assert!(is_sorted_unique(output.diagnostics()));
    }

    #[test]
    fn resolved_edges_keep_static_and_find_import_equals_and_nested_dynamic_imports() {
        use std::{
            fs,
            sync::atomic::{AtomicU64, Ordering},
        };

        use crate::{
            parser,
            program::ProgramLoader,
            project::{ProjectConfig, ProjectRoot},
            scanner,
            syntax::{Expression, FunctionBody, Statement},
        };

        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root_path).unwrap();
        let write = |name: &str, source: &str| fs::write(root_path.join(name), source).unwrap();
        write(
            "main.ts",
            "import value from \"./static\"; import equal = require(\"./equal\"); async function nested() { return import(\"./dynamic\"); }",
        );
        write("static.ts", "export default 1;");
        write("equal.ts", "export = 1;");
        write("dynamic.ts", "export default 1;");

        let root = ProjectRoot::new(fs::canonicalize(&root_path).unwrap()).unwrap();
        let config = ProjectConfig::parse(&root, root_path.join("tsconfig.json"), "{}").unwrap();
        let program = ProgramLoader::new(&root, config.options())
            .unwrap()
            .load("main.ts")
            .unwrap();
        let files = program
            .modules()
            .iter()
            .map(|module| {
                parser::parse(scanner::scan(
                    module.source_id(),
                    module.script_kind(),
                    Arc::clone(module.source()),
                ))
            })
            .collect::<Vec<_>>();
        let edges = resolved_checker_edges_with_cancel(&program, &files, &CancellationToken::new())
            .unwrap();
        let source = files
            .iter()
            .find(|file| file.product().source_id() == program.entrypoint_id())
            .unwrap()
            .product();
        let statements = source.statements();
        let Statement::Function(function) = statements[2].data() else {
            panic!("expected nested function declaration");
        };
        let Some(FunctionBody::Block(body)) = &function.function.body else {
            panic!("expected function block");
        };
        let Statement::Return(return_statement) = body.data().statements[0].data() else {
            panic!("expected return statement");
        };
        let dynamic_import = return_statement.argument.as_ref().unwrap();
        assert!(matches!(dynamic_import.data(), Expression::Import(_)));

        assert_eq!(edges.len(), 3);
        assert!(
            edges
                .iter()
                .any(|edge| edge.specifier == statements[0].id())
        );
        assert!(
            edges
                .iter()
                .any(|edge| edge.specifier == statements[1].id())
        );
        assert!(
            edges
                .iter()
                .any(|edge| edge.specifier == body.data().statements[0].id())
        );

        fs::remove_dir_all(root_path).unwrap();
    }
    #[test]
    fn pre_cancelled_program_frontend_stops_deterministically() {
        let (root_path, program) = program_fixture("export const value: number = 1;");
        let cancel = CancellationToken::new();
        cancel.cancel();

        let result = compile_program_frontend_with_cancel(
            &program,
            FrontendMode::Check,
            &LintTable::new(LintProfile::Default),
            &cancel,
        );

        assert!(matches!(result, Err(Cancelled)));
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn resolved_checker_edges_prefer_declaration_overlay_targets() {
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let root_path = std::env::temp_dir().join(format!(
            "bamts-pipeline-overlay-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        let package_path = root_path.join("node_modules/overlay");
        std::fs::create_dir_all(&package_path).unwrap();
        std::fs::write(
            root_path.join("main.ts"),
            "import { value } from 'overlay'; value;",
        )
        .unwrap();
        std::fs::write(
            package_path.join("package.json"),
            r#"{"name":"overlay","main":"./index.js","types":"./index.d.ts"}"#,
        )
        .unwrap();
        std::fs::write(package_path.join("index.js"), "exports.value = 1;").unwrap();
        std::fs::write(
            package_path.join("index.d.ts"),
            "export declare const value: string;",
        )
        .unwrap();

        let root = ProjectRoot::new(std::fs::canonicalize(&root_path).unwrap()).unwrap();
        let config = ProjectConfig::parse(&root, root_path.join("tsconfig.json"), "{}").unwrap();
        let program = ProgramLoader::new(&root, config.options())
            .unwrap()
            .load("main.ts")
            .unwrap();
        let files = program
            .modules()
            .iter()
            .map(|module| {
                crate::parser::parse(crate::scanner::scan(
                    module.source_id(),
                    module.script_kind(),
                    Arc::clone(module.source()),
                ))
            })
            .collect::<Vec<_>>();
        let dependency = &program.entrypoint().dependencies()[0];
        let runtime_target = dependency.target().local_source_id().unwrap();
        let declaration_target = dependency
            .type_target()
            .and_then(crate::program::ModuleTarget::local_source_id)
            .unwrap();
        let edges = resolved_checker_edges_with_cancel(&program, &files, &CancellationToken::new())
            .unwrap();

        assert_ne!(declaration_target, runtime_target);
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].to, declaration_target);
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn cancellable_program_frontend_records_every_pipeline_phase() {
        let (root_path, program) = program_fixture("export const value: number = 1;");
        let collector = TelemetryCollector::start();

        compile_program_frontend_with_cancel(
            &program,
            FrontendMode::JavaScript,
            &LintTable::new(LintProfile::Default),
            &CancellationToken::new(),
        )
        .unwrap();

        let totals = collector.snapshot();
        for phase in [
            Phase::Total,
            Phase::Scan,
            Phase::Parse,
            Phase::Check,
            Phase::Emit,
        ] {
            assert!(
                totals.get(phase) > std::time::Duration::ZERO,
                "{phase:?} telemetry was not recorded",
            );
        }
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn cancelled_source_iteration_stops_edge_collection() {
        let (root_path, program) = program_fixture("export const value: number = 1;");
        let files = program
            .modules()
            .iter()
            .map(|module| {
                crate::parser::parse(crate::scanner::scan(
                    module.source_id(),
                    module.script_kind(),
                    Arc::clone(module.source()),
                ))
            })
            .collect::<Vec<_>>();
        let cancel = CancellationToken::new();
        cancel.cancel();

        assert!(matches!(
            resolved_checker_edges_with_cancel(&program, &files, &cancel),
            Err(Cancelled)
        ));
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn legacy_program_frontend_delegates_without_output_changes() {
        let (root_path, program) = program_fixture("export const value: number = 1;");
        let legacy = compile_program_frontend(&program, FrontendMode::Check);
        let canonical = compile_program_frontend_with_cancel(
            &program,
            FrontendMode::Check,
            &LintTable::new(LintProfile::Default),
            &CancellationToken::new(),
        )
        .unwrap();

        assert_eq!(legacy.entrypoint_id(), canonical.entrypoint_id());
        assert_eq!(legacy.modules().len(), canonical.modules().len());
        for (legacy, canonical) in legacy.modules().iter().zip(canonical.modules()) {
            assert_eq!(legacy.mode(), canonical.mode());
            assert_eq!(
                legacy.source_file().source_id(),
                canonical.source_file().source_id()
            );
            assert_eq!(legacy.diagnostics(), canonical.diagnostics());
            assert_eq!(legacy.emit().is_some(), canonical.emit().is_some());
        }
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn es5_always_strict_emits_var_lowering_and_prologue_through_pipeline() {
        // A script (no imports/exports) compiled with target: es5 and
        // alwaysStrict: true must emit `var` (not `let`) and a "use strict"
        // prologue. Before the fix, program_emit_options used
        // EmitOptions::default() (target EsNext, always_strict false) so the
        // lane never downleveled and never wrote the prologue.
        let source = "let value = 1;";
        let config = r#"{"compilerOptions":{"target":"es5","alwaysStrict":true}}"#;
        let (root_path, program) = program_fixture_with_config(source, config);

        assert!(program.check_options().es5(), "fixture should carry es5");
        assert!(
            program.check_options().always_strict(),
            "fixture should carry always_strict"
        );

        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);

        assert!(
            js.starts_with("\"use strict\";\n"),
            "expected strict prologue, got: {js:?}"
        );
        assert!(
            js.contains("var "),
            "expected var lowering for es5, got: {js:?}"
        );
        assert!(
            !js.contains("let "),
            "let should not appear in es5 output, got: {js:?}"
        );
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn es2015_module_emits_no_strict_prologue_through_pipeline() {
        // An external module (has import/export) compiled with module: es2015
        // must NOT receive a "use strict" prologue, even when alwaysStrict is
        // true. The strict_prelude rule suppresses the prologue for ES module
        // output; this test proves the module option reaches emit through the
        // pipeline path.
        let source = "export const value = 1;";
        let config = r#"{"compilerOptions":{"module":"es2015","alwaysStrict":true}}"#;
        let (root_path, program) = program_fixture_with_config(source, config);

        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);

        assert!(
            !js.starts_with("\"use strict\";\n"),
            "ES module output should not have strict prologue, got: {js:?}"
        );
        std::fs::remove_dir_all(root_path).unwrap();
    }
    #[test]
    fn source_map_program_closes_emit_with_external_map_url() {
        let source = "export const value: number = 1;";
        let config = r#"{"compilerOptions":{"sourceMap":true}}"#;
        let (root_path, program) = program_fixture_with_config(source, config);
        assert!(program.source_map());
        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);
        assert!(
            js.ends_with("//# sourceMappingURL=main.js.map"),
            "external map url closes the emit: {js:?}"
        );
        std::fs::remove_dir_all(root_path).unwrap();
    }

    #[test]
    fn program_without_source_map_emits_no_map_url() {
        let (root_path, program) = program_fixture("export const value: number = 1;");
        let output = compile_program_frontend(&program, FrontendMode::JavaScript);
        let js = entrypoint_javascript(&output);
        assert!(
            !js.contains("sourceMappingURL"),
            "no map url without sourceMap: {js:?}"
        );
        std::fs::remove_dir_all(root_path).unwrap();
    }
    const BARREL_TYPE_COUNT: usize = 150;
    const BARREL_STAR_COUNT: usize = 8;

    fn barrel_case() -> (PathBuf, ResolvedProgram) {
        let mut target = String::new();
        for i in 0..BARREL_TYPE_COUNT {
            target.push_str(&format!("export type T{i} = number;\n"));
        }
        for i in 0..BARREL_TYPE_COUNT {
            target.push_str(&format!("export const V{i} = {i};\n"));
        }
        let mut barrel = String::new();
        for _ in 0..BARREL_STAR_COUNT {
            barrel.push_str("export * from \"./target\";\n");
        }
        barrel.push_str("export { T0 as T0a, V0 as V0a } from \"./target\";\n");
        barrel.push_str("export { T1, V1 } from \"./target\";\n");
        barrel.push_str("export type Local = string;\n");
        barrel.push_str("export const localValue = 1;\n");
        tslib_case(
            &[
                ("main.ts", "import \"./barrel\";\nexport {};\n"),
                ("target.ts", target.as_str()),
                ("barrel.ts", barrel.as_str()),
            ],
            r#"{"compilerOptions":{"module":"commonjs"}}"#,
        )
    }

    fn erased_by_name(
        output: &ProgramFrontendOutput,
        program: &ResolvedProgram,
    ) -> std::collections::HashMap<String, std::collections::BTreeSet<String>> {
        let erased = output.erased_exports(program);
        output
            .modules()
            .iter()
            .map(|module| {
                let id = module.source_file().source_id();
                let name = program
                    .module(id)
                    .map(|resolved| {
                        resolved
                            .path()
                            .file_name()
                            .unwrap()
                            .to_string_lossy()
                            .into_owned()
                    })
                    .expect("frontend module resolves");
                (name, erased.get(&id).cloned().unwrap_or_default())
            })
            .collect()
    }

    fn module_exports_computations() -> std::collections::HashMap<SourceId, usize> {
        super::MODULE_EXPORTS_COMPUTATIONS.with(|counts| counts.borrow().clone())
    }

    fn reset_module_exports_computations() {
        super::MODULE_EXPORTS_COMPUTATIONS.with(|counts| counts.borrow_mut().clear());
    }

    #[test]
    fn barrel_erased_exports_match_recorded_baseline() {
        let (root_path, program) = barrel_case();
        let output = compile_program_frontend(&program, FrontendMode::Check);
        let by_name = erased_by_name(&output, &program);
        assert_eq!(by_name.len(), 3, "{by_name:?}");
        let mut expected_target = std::collections::BTreeSet::new();
        for i in 0..BARREL_TYPE_COUNT {
            expected_target.insert(format!("T{i}"));
        }
        assert_eq!(by_name["target.ts"], expected_target);
        let mut expected_barrel = expected_target.clone();
        expected_barrel.insert("Local".to_owned());
        expected_barrel.insert("T0a".to_owned());
        assert_eq!(by_name["barrel.ts"], expected_barrel);
        assert!(by_name["main.ts"].is_empty());
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn barrel_module_exports_computed_once_per_module() {
        let (root_path, program) = barrel_case();
        let output = compile_program_frontend(&program, FrontendMode::Check);
        reset_module_exports_computations();
        let _ = output.erased_exports(&program);
        let counts = module_exports_computations();
        assert_eq!(counts.len(), output.modules().len(), "{counts:?}");
        for module in output.modules() {
            let id = module.source_file().source_id();
            assert_eq!(
                counts.get(&id),
                Some(&1),
                "exports of {id:?} computed {counts:?}"
            );
        }
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn module_lookup_matches_linear_scan_for_every_module() {
        let (root_path, program) = barrel_case();
        let output = compile_program_frontend(&program, FrontendMode::Check);
        for position in 0..output.modules().len() {
            let id = output.modules()[position].source_file().source_id();
            let linear = output
                .modules()
                .iter()
                .find(|module| module.source_file().source_id() == id)
                .expect("module resolves linearly");
            let indexed = output.module(id).expect("module resolves by index");
            assert!(
                std::ptr::eq(linear, indexed),
                "off-by-one index position returns the wrong module for {id:?}"
            );
        }
        assert!(
            output.module(SourceId::new(u32::MAX)).is_none(),
            "absent source id must resolve to no module"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }

    #[test]
    fn module_index_keeps_first_position_for_duplicate_source_ids() {
        let build = |source: &str| {
            compile_frontend(FrontendRequest {
                source_id: SourceId::new(7),
                script_kind: ScriptKind::TypeScript,
                source: Arc::new(
                    SourceText::new(source).expect("test source fits the per-file budget"),
                ),
                mode: FrontendMode::Check,
                no_emit: false,
                no_emit_on_error: false,
            })
        };
        let modules = vec![
            build("export const first: number = 1;"),
            build("export const second: number = 2;"),
        ];
        let index = ProgramFrontendOutput::module_index(&modules);
        let output = ProgramFrontendOutput {
            entrypoint: SourceId::new(7),
            modules,
            index,
        };
        let found = output
            .module(SourceId::new(7))
            .expect("duplicate source id resolves");
        assert!(
            std::ptr::eq(found, &output.modules[0]),
            "insert instead of or_insert keeps the last duplicate instead of the first"
        );
    }

    fn linear_erased_exports(
        output: &ProgramFrontendOutput,
        program: &ResolvedProgram,
    ) -> std::collections::HashMap<SourceId, std::collections::BTreeSet<String>> {
        fn linear_module(
            output: &ProgramFrontendOutput,
            source_id: SourceId,
        ) -> Option<&FrontendOutput> {
            output
                .modules()
                .iter()
                .find(|module| module.source_file().source_id() == source_id)
        }
        fn resolve(
            output: &ProgramFrontendOutput,
            program: &ResolvedProgram,
            source_id: SourceId,
            erased: &mut std::collections::HashMap<SourceId, std::collections::BTreeSet<String>>,
            visiting: &mut std::collections::HashSet<SourceId>,
        ) {
            if erased.contains_key(&source_id) {
                return;
            }
            let Some(module) = linear_module(output, source_id) else {
                return;
            };
            if !visiting.insert(source_id) {
                return;
            }
            let exports = crate::emitter::transforms::module_exports(
                module.source_file(),
                module.semantic_model(),
            );
            let mut names = exports.types;
            let forwarded: std::collections::BTreeSet<String> = exports
                .forwards
                .iter()
                .map(|(exported, ..)| exported.clone())
                .collect();
            for (exported, specifier, imported) in &exports.forwards {
                let target = super::local_dependency(program, source_id, specifier);
                if let Some(target) = target {
                    resolve(output, program, target, erased, visiting);
                }
                if target
                    .and_then(|target| erased.get(&target))
                    .is_some_and(|target_names| target_names.contains(imported))
                {
                    names.insert(exported.clone());
                } else {
                    names.remove(exported);
                }
            }
            let mut star_values = std::collections::BTreeSet::new();
            for specifier in &exports.stars {
                if let Some(target) = super::local_dependency(program, source_id, specifier) {
                    resolve(output, program, target, erased, visiting);
                    if let Some(target_module) = linear_module(output, target) {
                        star_values.extend(
                            crate::emitter::transforms::module_exports(
                                target_module.source_file(),
                                target_module.semantic_model(),
                            )
                            .values,
                        );
                    }
                    if let Some(starred) = erased.get(&target) {
                        names.extend(
                            starred
                                .iter()
                                .filter(|name| {
                                    name.as_str() != "default"
                                        && !forwarded.contains(name.as_str())
                                })
                                .cloned(),
                        );
                    }
                }
            }
            names.retain(|name| !exports.values.contains(name) && !star_values.contains(name));
            erased.insert(source_id, names);
        }
        let mut erased = std::collections::HashMap::new();
        for module in output.modules() {
            resolve(
                output,
                program,
                module.source_file().source_id(),
                &mut erased,
                &mut std::collections::HashSet::new(),
            );
        }
        erased
    }

    #[test]
    fn erased_exports_matches_linear_scan_oracle() {
        let (root_path, program) = barrel_case();
        let output = compile_program_frontend(&program, FrontendMode::Check);
        assert_eq!(
            output.erased_exports(&program),
            linear_erased_exports(&output, &program),
            "index position drift resolves a module to the wrong exports"
        );
        let _ = std::fs::remove_dir_all(root_path);
    }
}
