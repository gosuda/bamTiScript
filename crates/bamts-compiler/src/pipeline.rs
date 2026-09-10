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
use std::sync::Arc;

use crate::checker::{self, ProgramCheckInput, ResolvedModuleEdge, SemanticModel};
use crate::diagnostic::{Diagnostic, Recovered};
use crate::emitter::{self, EmitFileNames, EmitOptions, EmitOutput, ModuleKind};
use crate::lint::{LintProfile, LintTable};
use crate::parser;
use crate::program::{JsxRoutingDecision, ModuleTarget, ProgramOutputKind, ResolvedProgram};
use crate::scanner;
use crate::source::{ScriptKind, SourceId, SourceText};
use crate::syntax::{ExportDeclaration, ExportNamedDeclaration, SourceFile};
use crate::telemetry::{Phase, Telemetry};

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

fn program_emit_options(program: &ResolvedProgram, mode: FrontendMode) -> Option<EmitOptions> {
    let mut options = mode.emit_options()?;

    // Shared mapping: target, always_strict, module. The program carries the
    // resolved strict-family and es5 flags through `check_options()`; mapping
    // them here through `apply_emit_fields` — the same method the project
    // (CLI) path uses — ensures the lane and the CLI cannot diverge on
    // downleveling or the strict-mode prologue.
    let check = program.check_options();
    let target = check.target();
    let always_strict = check.always_strict();
    let module = program.is_commonjs().then_some(ModuleKind::CommonJs);
    options.apply_emit_fields(
        target,
        always_strict,
        module,
        program.use_define_for_class_fields(),
        program.import_helpers(),
    );
    options.no_emit_helpers = check.no_emit_helpers();

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

    #[must_use]
    pub fn module(&self, source_id: SourceId) -> Option<&FrontendOutput> {
        self.modules
            .iter()
            .find(|output| output.source_file().source_id() == source_id)
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
                js_file_name: Some(Arc::from(
                    js_path.to_string_lossy().into_owned().into_boxed_str(),
                )),
                declaration_file_name: None,
                source_root: None,
                ..EmitFileNames::default()
            };
            let emit = if let Some(options) = program_emit_options(program, mode) {
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
        Ok(ProgramFrontendOutput {
            entrypoint: program.entrypoint_id(),
            modules,
        })
    })
}

fn resolved_checker_edges_with_cancel(
    program: &ResolvedProgram,
    files: &[Recovered<SourceFile>],
    cancel: &CancellationToken,
) -> Result<Vec<ResolvedModuleEdge>, Cancelled> {
    let mut edges = Vec::new();
    for module in program.modules() {
        cancel.check()?;
        let source = files
            .iter()
            .find(|file| file.product().source_id() == module.source_id())
            .expect("resolved module has one parsed source")
            .product();
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
        FrontendMode, FrontendRequest, ProgramFrontendOutput, canonicalize, compile_frontend,
        compile_program_frontend, compile_program_frontend_with_cancel,
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
}
