//! Target-directed downlevel transforms over the existing emit AST.
//!
//! Feature detection walks the immutable [`SourceFile`]. When the requested
//! [`ScriptTarget`] does not natively include a feature, the tree is rewritten
//! in place — synthetic identifiers are interned into an extended [`SourceText`]
//! so the core printer can resolve them. Helper demand is recorded by the
//! rewrite itself and emitted through that same printer.
//!
//! # Guarantees
//! * **Deterministic.** Temps are allocated with a monotonic counter and helper
//!   names are interned in a fixed catalog order.
//! * **Byte-stable.** Identical input and derived [`TransformOptions`] produce
//!   identical JavaScript and diagnostic vectors.
//! * **Negative paths.** Private fields, `using`, `for await`, classes below
//!   ES2015, and generators below ES2015 produce typed diagnostics instead of
//!   silently emitting later syntax.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::checker::SemanticModel;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::jsx_desugar::{
    JsxEmitOptions, JsxRuntimeBinding, JsxRuntimeImportStyle, JsxSourceDesugarPlan,
    desugar_source_jsx,
};
use crate::source::{
    JsxEmit, NodeIdSource, SourceId, SourcePositionError, SourceText, TextRange, Utf16Pos,
};
use crate::syntax::*;

use super::helpers::{self, HelperKind, HelperOptions};
use super::{
    EmitFileNames, EmitOutput, ModuleKind, Newline, PrintOptions, PrintSource, Surface,
    print_with_jsx_plan,
};

/// Stable diagnostic identifiers produced by target transforms.
pub mod codes {
    use crate::diagnostic::DiagnosticCode;

    /// `class` syntax below ES2015 cannot be downleveled by this layer.
    pub const CLASS_REQUIRES_ES2015: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1101");
    /// Generator syntax below ES2015 cannot be downleveled by this layer.
    pub const GENERATOR_REQUIRES_ES2015: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1102");
    /// Private fields below ES2022 require helpers this layer does not apply.
    pub const PRIVATE_FIELD_REQUIRES_ES2022: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1103");
    /// `using` / `await using` is not downleveled.
    pub const USING_UNSUPPORTED: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1104");
    /// `for await` below ES2018 is not downleveled.
    pub const ASYNC_ITERATION_REQUIRES_ES2018: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1105");
    /// A static field on an unnamed class expression cannot be lowered.
    pub const STATIC_FIELD_REQUIRES_CLASS_NAME: DiagnosticCode =
        DiagnosticCode::new("TS-EMIT-1106");
    /// Destructuring assignment (not a declaration) below ES2015 is not lowered.
    pub const DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015: DiagnosticCode =
        DiagnosticCode::new("TS-EMIT-1107");
    /// Target rewriting exceeded the compiler's bounded per-file text budget.
    pub const SOURCE_TOO_LARGE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1108");
    /// Auto-accessors below ES2022 require a dedicated transform.
    pub const AUTO_ACCESSOR_REQUIRES_ES2022: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1109");
}

/// ECMAScript language target. Later variants include every earlier feature.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ScriptTarget {
    Es3,
    Es5,
    Es2015,
    Es2016,
    Es2017,
    Es2018,
    Es2019,
    Es2020,
    Es2021,
    Es2022,
    Es2023,
    Es2024,
    Es2025,
    #[default]
    EsNext,
}

/// A language feature with a first-supporting [`ScriptTarget`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LanguageFeature {
    ArrowFunctions,
    Classes,
    Generators,
    Destructuring,
    AsyncFunctions,
    Exponentiation,
    ObjectRestSpread,
    AsyncIteration,
    OptionalChaining,
    NullishCoalescing,
    LogicalAssignment,
    ClassFields,
    Using,
    ForOf,
}

impl LanguageFeature {
    /// Returns the earliest target that natively includes this feature.
    #[must_use]
    pub const fn since(self) -> ScriptTarget {
        match self {
            Self::ArrowFunctions | Self::Classes | Self::Generators | Self::Destructuring => {
                ScriptTarget::Es2015
            }
            Self::AsyncFunctions => ScriptTarget::Es2017,
            Self::Exponentiation => ScriptTarget::Es2016,
            Self::ObjectRestSpread | Self::AsyncIteration => ScriptTarget::Es2018,
            Self::OptionalChaining | Self::NullishCoalescing => ScriptTarget::Es2020,
            Self::LogicalAssignment => ScriptTarget::Es2021,
            Self::ClassFields => ScriptTarget::Es2022,
            Self::Using => ScriptTarget::EsNext,
            Self::ForOf => ScriptTarget::Es2015,
        }
    }
}

impl ScriptTarget {
    /// Returns whether this target natively includes `feature`.
    #[must_use]
    pub const fn supports(self, feature: LanguageFeature) -> bool {
        (self as u8) >= (feature.since() as u8)
    }
}

/// Stage-internal transform view derived from the canonical emit options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransformOptions {
    /// Language target that drives downlevel decisions.
    pub target: ScriptTarget,
    /// Whether the emitted file begins with a `"use strict"` prologue.
    pub always_strict: bool,
    /// When true, class fields that survive downlevel use `define` semantics.
    /// Defaults to true for targets that natively include class fields.
    pub use_define_for_class_fields: bool,
    /// Helper import policy applied after rewrite.
    pub helpers: HelperOptions,
    /// Module kind used to decide strict prologue and JSX import style.
    pub module_kind: Option<ModuleKind>,
    /// Printer newline.
    pub newline: Newline,
    /// Printer indent width.
    pub indent_width: u8,
    /// JSX mode and factories used to build one source-level desugar plan.
    pub jsx: Option<JsxEmit>,
    pub jsx_factory: Option<Arc<str>>,
    pub jsx_fragment_factory: Option<Arc<str>>,
    pub jsx_import_source: Option<Arc<str>>,
    pub(crate) jsx_import_style: JsxRuntimeImportStyle,
    /// Whether to produce an external JavaScript source map.
    pub source_map: bool,
    /// Whether to produce and inline a JavaScript source map.
    pub inline_source_map: bool,
    /// Whether JavaScript source maps include the original source text.
    pub inline_sources: bool,
}

/// Features found in a file, helpers they require, and diagnostics they produce.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransformPlan {
    /// Features present in the source, in catalog order.
    pub features: Vec<LanguageFeature>,
    /// Features that the target does not natively include.
    pub required: Vec<LanguageFeature>,
    /// Helpers the rewrite will call, in catalog order.
    pub helpers: Vec<HelperKind>,
    /// Diagnostics produced by analysis, in canonical order.
    pub diagnostics: Vec<Diagnostic>,
}

/// Analyzes `file` without rewriting it.
#[must_use]
pub fn analyze(file: &SourceFile, options: &TransformOptions) -> TransformPlan {
    let mut features = BTreeSet::new();
    let mut diagnostics = Vec::new();
    scan_statements(
        file,
        file.statements(),
        options,
        &mut features,
        &mut diagnostics,
        false,
    );
    let required: Vec<LanguageFeature> = features
        .iter()
        .copied()
        .filter(|feature| !options.target.supports(*feature))
        .collect();
    let mut helpers = BTreeSet::new();
    if required.contains(&LanguageFeature::AsyncFunctions) {
        helpers.insert(HelperKind::Awaiter);
    }
    // __generator only when the target lacks native generators: at es2015+
    // the awaiter body is a native function* and tsc emits no __generator.
    if required.contains(&LanguageFeature::Generators) {
        helpers.insert(HelperKind::Generator);
    }
    if required.contains(&LanguageFeature::ObjectRestSpread)
        || required.contains(&LanguageFeature::Destructuring)
    {
        helpers.insert(HelperKind::Rest);
    }
    diagnostics.sort();
    TransformPlan {
        features: features.into_iter().collect(),
        required,
        helpers: helpers.into_iter().collect(),
        diagnostics,
    }
}

/// Rewrites `file` for `options.target` and prints it through the core printer.
#[must_use]
pub fn emit_transformed(
    file: &SourceFile,
    model: &SemanticModel,
    options: &TransformOptions,
    names: &EmitFileNames,
) -> EmitOutput {
    let plan = analyze(file, options);
    let mut ids = NodeIdSource::after(file.id());
    let jsx_plan = executable_jsx_plan(file, options, names, &mut ids);
    let mut jsx_diagnostics = Vec::new();
    if let Err(diagnostic) = &jsx_plan {
        jsx_diagnostics.push((**diagnostic).clone());
    }
    let mut jsx_plan = jsx_plan.ok().flatten();
    let runtime_prelude = jsx_plan
        .as_mut()
        .map(|plan| bind_and_render_jsx_runtime(file, plan))
        .unwrap_or_default();

    let mut rewriter = Rewriter::new(file, options, Some(model), &mut ids);
    if jsx_plan
        .as_ref()
        .is_some_and(|plan| plan.demand.needs_assign)
    {
        rewriter.used_helpers.insert(HelperKind::Assign);
    }
    let statements = rewriter.rewrite_root_statements(file.statements(), file.range());
    let used_helpers: Vec<_> = rewriter.used_helpers.iter().copied().collect();
    let (source, eof, range) = match rewriter.finish_source() {
        Ok(parts) => parts,
        Err(_error) => {
            let mut diagnostics = plan.diagnostics;
            diagnostics.extend(jsx_diagnostics);
            diagnostics.extend(rewriter.diagnostics);
            diagnostics.push(Diagnostic::error(
                codes::SOURCE_TOO_LARGE,
                file.source_id(),
                file.range(),
                "transformed source text exceeds the per-file budget",
            ));
            diagnostics.sort();
            diagnostics.dedup();
            return EmitOutput {
                diagnostics,
                ..EmitOutput::default()
            };
        }
    };
    let rewritten = SourceFile::new(
        file.id(),
        file.source_id(),
        file.script_kind(),
        range,
        source,
        file.tokens().to_vec(),
        statements,
        eof,
        file.diagnostics().to_vec(),
    );
    let helper_emit = helpers::emit_helpers(&used_helpers, &options.helpers, Some(&rewritten));
    // Under `moduleDetection: auto` a file whose JSX draws the automatic
    // runtime import is a module (commentsOnJSXExpressionsArePreserved),
    // so the synthesized import counts like a source-level one.
    let is_module = !runtime_prelude.is_empty() || crate::checker::source_is_module(file);
    let cjs_marker = rewriter.cjs_marker_prelude(!runtime_prelude.is_empty());
    let cjs_requires = rewriter.cjs_require_prelude();
    let prelude = join_preludes(
        &strict_prelude(file, options, is_module),
        &join_preludes(
            &helper_emit.prelude,
            &join_preludes(&cjs_marker, &join_preludes(&runtime_prelude, &cjs_requires)),
        ),
    );
    let mut output = print_with_jsx_plan(
        PrintSource {
            file: &rewritten,
            original_content: file.source_text().as_str(),
            synthesized: Some(&rewriter.synthesized_ids),
            synthesized_floor: rewriter.synthesized_floor,
        },
        model,
        PrintOptions {
            newline: options.newline,
            indent_width: options.indent_width,
            source_map: options.source_map,
            inline_source_map: options.inline_source_map,
            inline_sources: options.inline_sources,
        },
        names,
        Surface::JavaScript,
        Some(prelude),
        jsx_plan.as_ref(),
    );
    output.diagnostics.extend(plan.diagnostics);
    output.diagnostics.extend(jsx_diagnostics);
    output.diagnostics.extend(rewriter.diagnostics);
    output.diagnostics.extend(helper_emit.diagnostics);
    output.diagnostics.sort();
    output.diagnostics.dedup();
    output
}

fn executable_jsx_plan(
    file: &SourceFile,
    options: &TransformOptions,
    names: &EmitFileNames,
    ids: &mut NodeIdSource,
) -> Result<Option<JsxSourceDesugarPlan>, Box<Diagnostic>> {
    let Some(emit @ (JsxEmit::React | JsxEmit::ReactJsx | JsxEmit::ReactJsxDev)) = options.jsx
    else {
        return Ok(None);
    };
    let emit_options = JsxEmitOptions {
        emit,
        factory: options.jsx_factory.clone(),
        fragment_factory: options.jsx_fragment_factory.clone(),
        import_source: options.jsx_import_source.clone(),
        import_style: options.jsx_import_style,
        file_name: Some(Arc::clone(&names.source_name)),
    };
    desugar_source_jsx(file, file.source_text(), &emit_options, ids)
        .map(Some)
        .map_err(|_| {
            Box::new(Diagnostic::error(
                super::codes::JSX_DESUGAR_FAILED,
                file.source_id(),
                file.range(),
                "JSX source desugaring failed",
            ))
        })
}

fn bind_and_render_jsx_runtime(file: &SourceFile, plan: &mut JsxSourceDesugarPlan) -> String {
    let Some(module) = plan.demand.module_specifier.clone() else {
        return String::new();
    };
    let demanded = plan
        .demand
        .bindings
        .values()
        .copied()
        .collect::<BTreeSet<_>>();
    if demanded.is_empty() {
        return String::new();
    }
    let mut occupied = file
        .tokens()
        .iter()
        .filter(|token| token.kind() == TokenKind::Identifier)
        .filter_map(|token| {
            let start = file
                .source_text()
                .utf16_to_byte(token.range().start())
                .ok()?;
            let end = file.source_text().utf16_to_byte(token.range().end()).ok()?;
            file.source_text()
                .as_str()
                .get(start..end)
                .map(str::to_owned)
        })
        .collect::<BTreeSet<_>>();
    let mut locals = BTreeMap::new();
    for binding in demanded {
        let preferred = match binding {
            JsxRuntimeBinding::Jsx => "_jsx",
            JsxRuntimeBinding::Jsxs => "_jsxs",
            JsxRuntimeBinding::JsxDev => "_jsxDEV",
            JsxRuntimeBinding::Fragment => "_Fragment",
        };
        let local = collision_free_name(preferred, &mut occupied);
        locals.insert(binding, Arc::<str>::from(local));
    }
    plan.rebind_runtime_names(&locals);

    let module = quote_module_specifier(&module);
    match plan.demand.import_style {
        JsxRuntimeImportStyle::EsModule => {
            let bindings = locals
                .iter()
                .map(|(binding, local)| format!("{} as {}", binding.export_name(), local))
                .collect::<Vec<_>>()
                .join(", ");
            format!("import {{ {bindings} }} from {module};\n")
        }
        JsxRuntimeImportStyle::CommonJs => {
            let namespace = collision_free_name("_jsxRuntime", &mut occupied);
            let mut prelude = format!("var {namespace} = require({module});\n");
            for (binding, local) in locals {
                prelude.push_str(&format!(
                    "var {local} = {namespace}.{};\n",
                    binding.export_name()
                ));
            }
            prelude
        }
    }
}

fn collision_free_name(preferred: &str, occupied: &mut BTreeSet<String>) -> String {
    if occupied.insert(preferred.to_owned()) {
        return preferred.to_owned();
    }
    let mut suffix = 1_u32;
    loop {
        let candidate = format!("{preferred}_{suffix}");
        if occupied.insert(candidate.clone()) {
            return candidate;
        }
        suffix += 1;
    }
}

fn quote_module_specifier(module: &str) -> String {
    format!("\"{}\"", module.replace('\\', "\\\\").replace('"', "\\\""))
}

/// Builds the `"use strict";` prologue for one file.
///
/// Measured over 10781 single-file TypeScript 7.0.2 baselines carrying a real
/// `.js` section: a top-level external module takes the prologue exactly when
/// it is transpiled to CommonJS, and a script takes it exactly when
/// `alwaysStrict` is on. Agreement is 10694 of 10781.
///
/// Two edges that measurement settled against the obvious guess. An external
/// module emitted as ES modules takes no prologue even under `alwaysStrict`,
/// because the module format is already strict; emitting one there diverges on
/// 673 baselines. And AMD, UMD, and System take no head prologue either,
/// unlike CommonJS, which costs 238 baselines if they are lumped together.
/// No baseline sets `alwaysStrict` off on a CommonJS module, so that cell
/// follows the module rule rather than the option.
///
/// A source-level directive at the head suppresses the synthetic one.
#[must_use]
fn strict_prelude(file: &SourceFile, options: &TransformOptions, is_module: bool) -> String {
    // An unset `module` resolves the way upstream resolves it, from the target:
    // CommonJS below ES2015 and ES modules at or above it. That default decides
    // 673 baselines on its own, so it cannot be folded into either branch.
    let module_kind = options.module_kind.unwrap_or({
        if options.target < ScriptTarget::Es2015 {
            ModuleKind::CommonJs
        } else {
            ModuleKind::Es2015
        }
    });
    let strict = if is_module {
        module_kind == ModuleKind::CommonJs
    } else {
        options.always_strict
    };
    if !strict {
        return String::new();
    }
    let starts_with_strict = file.statements().first().is_some_and(|statement| {
        let Statement::Expression(statement) = statement.data() else {
            return false;
        };
        let Expression::Literal(Literal::String(literal)) = statement.expression.data() else {
            return false;
        };
        file.token_text(literal.data().token())
            .is_some_and(|text| text.trim_matches(['\'', '"']) == "use strict")
    });
    if starts_with_strict {
        String::new()
    } else {
        String::from("\"use strict\";\n")
    }
}

fn join_preludes(runtime: &str, helpers: &str) -> String {
    match (runtime.is_empty(), helpers.is_empty()) {
        (true, _) => helpers.to_owned(),
        (_, true) => runtime.to_owned(),
        (false, false) => format!("{runtime}{helpers}"),
    }
}

struct NameBank {
    text: String,
    utf16: usize,
    names: std::collections::BTreeMap<String, TextRange>,
}

impl NameBank {
    fn new(source: &SourceText) -> Self {
        Self {
            text: source.as_str().to_owned(),
            utf16: source.len_utf16().get(),
            names: std::collections::BTreeMap::new(),
        }
    }

    fn intern(&mut self, lexeme: &str) -> TextRange {
        if let Some(range) = self.names.get(lexeme) {
            return *range;
        }
        if !self.text.is_empty() && !self.text.ends_with('\n') {
            self.text.push('\n');
            self.utf16 += 1;
        }
        let start = self.utf16;
        self.text.push_str(lexeme);
        self.utf16 += lexeme.encode_utf16().count();
        let range = TextRange::new(Utf16Pos::new(start), Utf16Pos::new(self.utf16))
            .expect("interned range is ordered");
        self.text.push('\n');
        self.utf16 += 1;
        self.names.insert(lexeme.to_owned(), range);
        range
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FieldMode {
    Native,
    Assign,
    Define,
}

impl FieldMode {
    const fn for_options(options: &TransformOptions) -> Self {
        if options.target.supports(LanguageFeature::ClassFields)
            && options.use_define_for_class_fields
        {
            Self::Native
        } else if options.use_define_for_class_fields {
            Self::Define
        } else {
            Self::Assign
        }
    }
}

#[derive(Clone)]
struct FieldInit {
    name: PropertyName,
    init: Expr,
    range: TextRange,
}

#[derive(Clone)]
enum StaticStep {
    Field(Box<FieldInit>),
    Block(BlockNode),
}

struct ClassLowering {
    class: ClassDeclaration,
    prelude: Vec<Stmt>,
    postlude: Vec<Stmt>,
}

#[derive(Clone, Copy)]
enum ExportWrapper {
    None,
    Named,
    Default,
}

struct Rewriter<'a> {
    options: &'a TransformOptions,
    model: Option<&'a SemanticModel>,
    source_id: SourceId,
    source: SourceText,
    source_text: String,
    bank: NameBank,
    ids: &'a mut NodeIdSource,
    synthesized_floor: u32,
    next_temp: u32,
    diagnostics: Vec<Diagnostic>,
    replace_await: bool,
    used_helpers: BTreeSet<HelperKind>,
    key_prelude: Vec<Stmt>,
    expression_temp_scopes: Vec<Vec<IdentifierNode>>,
    parameter_initializer_depths: Vec<usize>,
    cjs: Option<CjsPlan>,
    synthesized_ids: BTreeSet<NodeId>,
}

/// Per-file CommonJS lowering plan built before the rewrite walk.
#[derive(Default)]
struct CjsPlan {
    /// The file has module syntax, so it receives the `__esModule` marker.
    is_module: bool,
    /// Exported names needing `exports.<name> = void 0;` in the prelude.
    void_0: Vec<String>,
    /// `require` prelude lines in import-statement order.
    requires: Vec<String>,
    /// Import binding replacement by resolved module-scope symbol.
    imports: BTreeMap<crate::checker::SymbolId, CjsImportRef>,
    /// Require-local names whose member calls become `(0, m.p)()`.
    require_roots: BTreeSet<String>,
}

#[derive(Clone)]
struct CjsImportRef {
    /// The `require` binding local (`_10_lib_1`).
    root: String,
    /// Property read off the module object; `None` keeps the root bare.
    property: Option<String>,
}

/// Allocates tsc-shaped require locals (`<slug>_N`, sanitized with a leading
/// underscore only when the slug cannot start an identifier) that avoid
/// source identifiers.
struct RequireNames {
    occupied: BTreeSet<String>,
    counters: BTreeMap<String, u32>,
}

impl RequireNames {
    fn new(occupied: BTreeSet<String>) -> Self {
        Self {
            occupied,
            counters: BTreeMap::new(),
        }
    }

    fn allocate(&mut self, module: &str) -> String {
        let base = module.rsplit('/').next().unwrap_or(module);
        let counter = self.counters.entry(base.to_owned()).or_insert(0);
        // tsc binds require locals as `<slug>_<n>` when the path's last
        // segment can start an identifier (`enum_1`) and sanitizes with a
        // leading underscore only when it cannot (`_10_lib_1`).
        let starts_identifier = base
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '$');
        loop {
            *counter += 1;
            let candidate = if starts_identifier {
                format!("{base}_{}", *counter)
            } else {
                format!("_{base}_{}", *counter)
            };
            if self.occupied.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

impl<'a> Rewriter<'a> {
    fn new(
        file: &'a SourceFile,
        options: &'a TransformOptions,
        model: Option<&'a SemanticModel>,
        ids: &'a mut NodeIdSource,
    ) -> Self {
        let cjs = if options.module_kind == Some(ModuleKind::CommonJs) {
            model.and_then(|model| Self::build_cjs_plan(file, options, model))
        } else {
            None
        };
        let synthesized_floor = ids.position();
        Self {
            options,
            model,
            source_id: file.source_id(),
            source: file.source_text().clone(),
            source_text: file.source_text().as_str().to_owned(),
            bank: NameBank::new(file.source_text()),
            ids,
            synthesized_floor,
            next_temp: 0,
            diagnostics: Vec::new(),
            replace_await: false,
            used_helpers: BTreeSet::new(),
            key_prelude: Vec::new(),
            expression_temp_scopes: Vec::new(),
            parameter_initializer_depths: Vec::new(),
            cjs,
            synthesized_ids: BTreeSet::new(),
        }
    }
    /// Scans top-level module syntax into a CommonJS lowering plan.
    fn build_cjs_plan(
        file: &SourceFile,
        options: &TransformOptions,
        model: &SemanticModel,
    ) -> Option<CjsPlan> {
        let occupied: BTreeSet<String> = file
            .tokens()
            .iter()
            .filter(|token| token.kind() == TokenKind::Identifier)
            .filter_map(|token| {
                let start = file
                    .source_text()
                    .utf16_to_byte(token.range().start())
                    .ok()?;
                let end = file.source_text().utf16_to_byte(token.range().end()).ok()?;
                file.source_text()
                    .as_str()
                    .get(start..end)
                    .map(str::to_owned)
            })
            .collect();
        let mut names = RequireNames::new(occupied);
        let mut plan = CjsPlan::default();
        let module_scope = model.module_scope();
        let symbol_of = |name: &str| model.scope(module_scope).value(name);
        for statement in file.statements() {
            match statement.data() {
                Statement::Import(import) => {
                    if import.type_only {
                        continue;
                    }
                    plan.is_module = true;
                    let Some(clause) = &import.clause else {
                        continue;
                    };
                    let raw = raw_token_text(file, import.source.data().token());
                    let module = raw.trim_matches(['"', '\'']);
                    let local = names.allocate(module);
                    // Upstream re-quotes module specifiers with double
                    // quotes in every require form.
                    let quoted = quote_module_specifier(module);
                    let line = format!(
                        "{} {local} = require({quoted});",
                        if options.target <= ScriptTarget::Es5 {
                            "var"
                        } else {
                            "const"
                        }
                    );
                    plan.requires.push(line);
                    plan.require_roots.insert(local.clone());
                    if let Some(default) = &clause.default {
                        let text = identifier_text(file, default);
                        if let Some(symbol) = symbol_of(&text) {
                            plan.imports.insert(
                                symbol,
                                CjsImportRef {
                                    root: local.clone(),
                                    property: Some(String::from("default")),
                                },
                            );
                        }
                    }
                    match &clause.binding {
                        Some(ImportBinding::Namespace(name)) => {
                            let text = identifier_text(file, name);
                            if let Some(symbol) = symbol_of(&text) {
                                plan.imports.insert(
                                    symbol,
                                    CjsImportRef {
                                        root: local.clone(),
                                        property: None,
                                    },
                                );
                            }
                        }
                        Some(ImportBinding::Named(specifiers)) => {
                            for specifier in specifiers {
                                let specifier = specifier.data();
                                if !matches!(specifier.mode, ImportSpecifierMode::Value) {
                                    continue;
                                }
                                let imported = match &specifier.imported {
                                    ModuleExportName::Identifier(ident) => {
                                        Some(identifier_text(file, ident))
                                    }
                                    _ => None,
                                };
                                let Some(property) = imported else {
                                    continue;
                                };
                                let text = identifier_text(file, &specifier.local);
                                if let Some(symbol) = symbol_of(&text) {
                                    plan.imports.insert(
                                        symbol,
                                        CjsImportRef {
                                            root: local.clone(),
                                            property: Some(property),
                                        },
                                    );
                                }
                            }
                        }
                        None => {}
                    }
                }
                Statement::ImportEquals(import) => {
                    plan.is_module |= !import.is_type_only
                        && matches!(import.reference, ExternalModuleReference::Require(_));
                }
                Statement::Export(export) => {
                    plan.is_module = true;
                    if let ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) =
                        export
                    {
                        match inner.data() {
                            Statement::Class(class) => {
                                if let Some(name) = &class.name {
                                    plan.void_0.push(identifier_text(file, name));
                                }
                            }
                            Statement::Function(_)
                            | Statement::Interface(_)
                            | Statement::TypeAlias(_) => {}
                            _ => {
                                for name in declared_binding_names(file, inner) {
                                    plan.void_0.push(name);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        // Script files keep the plan too: the marker stays off until a
        // require prelude (for example the JSX runtime) forces module form.
        plan.void_0.sort();
        plan.void_0.dedup();
        Some(plan)
    }

    /// `exports.<exported> = <local>;`
    fn cjs_export_assignment(&mut self, exported: &str, local: &str, range: TextRange) -> Stmt {
        let left = self.cjs_export_target(exported, range);
        let right = self.ident_expr(local);
        let assignment = self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(right),
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assignment),
            }),
        )
    }

    /// `exports.default = <value>;`
    fn cjs_export_default_assignment(&mut self, range: TextRange, value: Expr) -> Stmt {
        let left = self.cjs_export_target("default", range);
        let assignment = self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assignment),
            }),
        )
    }

    fn cjs_export_target(&mut self, exported: &str, range: TextRange) -> AssignmentTargetNode {
        let exports_ident = self.ident("exports");
        let object = self.syn_node(range, Expression::Identifier(exports_ident));
        let property = MemberProperty::Named(self.ident(exported));
        self.syn_node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        )
    }

    /// `require("./m");` for a side-effect import, with the specifier
    /// re-quoted the way upstream prints module text.
    fn cjs_require_statement(&mut self, source: &StringLiteralNode) -> Stmt {
        let range = source.range();
        let raw = self.token_text(source.data().token()).to_owned();
        let module = raw.trim_matches(['"', '\'']);
        let require = self.ident("require");
        let callee = self.syn_node(range, Expression::Identifier(require));
        let literal = self.string_literal(module);
        let module = self.syn_node(range, Expression::Literal(Literal::String(literal)));
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(module))],
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    /// Replaces `export <declaration>` with assignments around the
    /// declaration. Functions hoist, so the export assignment precedes them;
    /// classes and variables receive the `void 0` preamble instead.
    fn cjs_export_declaration(&mut self, range: TextRange, inner: &Stmt) -> Vec<Stmt> {
        match inner.data() {
            Statement::Function(function) => {
                let Some(name) = function
                    .function
                    .name
                    .as_ref()
                    .map(|ident| self.token_text(ident.data().token()).to_owned())
                else {
                    return self.rewrite_statement(inner);
                };
                let mut out = vec![self.cjs_export_assignment(&name, &name, range)];
                out.extend(self.rewrite_statement(inner));
                out
            }
            Statement::Class(class) => {
                let Some(name) = class
                    .name
                    .as_ref()
                    .map(|ident| self.token_text(ident.data().token()).to_owned())
                else {
                    return self.rewrite_statement(inner);
                };
                let mut out = self.rewrite_statement(inner);
                out.push(self.cjs_export_assignment(&name, &name, range));
                out
            }
            _ => {
                let names = self.cjs_declared_names(inner);
                let mut out = self.rewrite_statement(inner);
                for name in &names {
                    out.push(self.cjs_export_assignment(name, name, range));
                }
                out
            }
        }
    }

    /// `export default class C {}` / anonymous `default_1` renaming.
    fn cjs_default_class(&mut self, range: TextRange, class: &ClassDeclaration) -> Vec<Stmt> {
        let (class, name) = match &class.name {
            Some(ident) => (
                class.clone(),
                self.token_text(ident.data().token()).to_owned(),
            ),
            None => {
                let ident = self.ident("default_1");
                let mut renamed = class.clone();
                renamed.name = Some(ident);
                (renamed, String::from("default_1"))
            }
        };
        let statement = self.syn_node(range, Statement::Class(class));
        let mut out = self.rewrite_statement(&statement);
        let default_value = self.ident_expr(&name);
        out.push(self.cjs_export_default_assignment(range, default_value));
        out
    }

    /// `export { a, b as c };` becomes one assignment per specifier.
    fn cjs_export_specifiers(&mut self, specifiers: &[ExportSpecifierNode]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for specifier in specifiers {
            let specifier = specifier.data();
            if matches!(specifier.mode, ExportSpecifierMode::TypeOnly) {
                continue;
            }
            let local_range = match &specifier.local {
                ModuleExportName::Identifier(local) => local.range(),
                _ => continue,
            };
            let (local, exported) = match (&specifier.local, &specifier.exported) {
                (ModuleExportName::Identifier(local), ModuleExportName::Identifier(exported)) => (
                    self.token_text(local.data().token()).to_owned(),
                    self.token_text(exported.data().token()).to_owned(),
                ),
                _ => continue,
            };
            out.push(self.cjs_export_assignment(&exported, &local, local_range));
        }
        out
    }

    /// Declared value names of a statement, via the rewrite text.
    fn cjs_declared_names(&self, statement: &Stmt) -> Vec<String> {
        match statement.data() {
            Statement::Variable(declaration) => declaration
                .declarations
                .iter()
                .filter_map(|declarator| match declarator.data().binding.data() {
                    BindingPattern::Identifier(ident) => {
                        Some(self.token_text(ident.data().token()).to_owned())
                    }
                    _ => None,
                })
                .collect(),
            Statement::Enum(declaration) => {
                vec![self.token_text(declaration.name.data().token()).to_owned()]
            }
            _ => Vec::new(),
        }
    }

    fn rewrite_export_named_declaration(&mut self, statement: &Stmt, inner: &Stmt) -> Vec<Stmt> {
        if self.cjs.is_some() {
            return self.cjs_export_declaration(statement.range(), inner);
        }
        match inner.data() {
            Statement::Class(class) => self.rewrite_named_export_class(statement, inner, class),
            _ => self
                .rewrite_statement(inner)
                .into_iter()
                .map(|inner| {
                    self.node(
                        statement.range(),
                        Statement::Export(ExportDeclaration::Named(
                            ExportNamedDeclaration::Declaration(Box::new(inner)),
                        )),
                    )
                })
                .collect(),
        }
    }
    /// `export default function f() {}` / anonymous `default_1` renaming.
    fn cjs_default_function(&mut self, range: TextRange, function: &FunctionLike) -> Vec<Stmt> {
        let (function, name) = match &function.name {
            Some(ident) => (
                function.clone(),
                self.token_text(ident.data().token()).to_owned(),
            ),
            None => {
                let ident = self.ident("default_1");
                let mut renamed = function.clone();
                renamed.name = Some(ident);
                (renamed, String::from("default_1"))
            }
        };
        let function = self.rewrite_function_like(&function, range);
        let statement = self.node(range, Statement::Function(FunctionDeclaration { function }));
        let mut out = vec![statement];
        let default_value = self.ident_expr(&name);
        out.push(self.cjs_export_default_assignment(range, default_value));
        out
    }

    /// Rewrites a resolved import reference to its CommonJS member form.
    fn cjs_identifier_replacement(&mut self, expression: &Expr) -> Option<Expr> {
        let (root, property) = {
            let plan = self.cjs.as_ref()?;
            let symbol = self.model?.reference(expression.id())?;
            let reference = plan.imports.get(&symbol)?;
            (reference.root.clone(), reference.property.clone())
        };
        let range = expression.range();
        let root_ident = self.ident(&root);
        let object = self.node(range, Expression::Identifier(root_ident));
        let Some(property) = property else {
            return Some(object);
        };
        let property = self.ident(&property);
        Some(self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object),
                property: MemberProperty::Named(property),
                optional: false,
            }),
        ))
    }

    /// Whether a call's original callee identifier maps to an imported
    /// binding, so the rewritten member call becomes `(0, m.p)(...)`.
    fn cjs_call_needs_safe_wrap(&self, original_callee: &Expr) -> bool {
        let Some(plan) = &self.cjs else {
            return false;
        };
        let Expression::Identifier(ident) = original_callee.data() else {
            return false;
        };
        let Some(symbol) = self.model.and_then(|model| model.reference(ident.id())) else {
            return false;
        };
        plan.imports
            .get(&symbol)
            .is_some_and(|reference| reference.property.is_some())
    }

    fn cjs_wrap_callee(&mut self, callee: Expr) -> Expr {
        let range = callee.range();
        let zero = self.number_expr("0");
        self.node(
            range,
            Expression::Sequence(SequenceExpression {
                expressions: vec![zero, callee],
            }),
        )
    }

    /// The `__esModule` marker plus the `void 0` export preamble.
    fn cjs_marker_prelude(&self, force_module: bool) -> String {
        let Some(plan) = &self.cjs else {
            return String::new();
        };
        if !(plan.is_module || force_module) {
            return String::new();
        }
        let mut prelude =
            String::from("Object.defineProperty(exports, \"__esModule\", { value: true });\n");
        let mut names = plan.void_0.clone();
        names.sort();
        names.dedup();
        if !names.is_empty() {
            prelude.push_str("exports.");
            for (index, name) in names.iter().enumerate() {
                if index > 0 {
                    prelude.push_str(" = exports.");
                }
                prelude.push_str(name);
            }
            prelude.push_str(" = void 0;\n");
        }
        prelude
    }

    fn cjs_require_prelude(&self) -> String {
        let Some(plan) = &self.cjs else {
            return String::new();
        };
        let mut prelude = String::new();
        for line in &plan.requires {
            prelude.push_str(line);
            prelude.push('\n');
        }
        prelude
    }

    /// Raw source text of a token, with escapes kept verbatim.
    fn token_text(&self, token: &Token) -> &str {
        let range = token.range();
        let start = range.start().get();
        let end = range.end().get();
        let start_byte = utf16_to_byte(&self.source_text, start);
        let end_byte = utf16_to_byte(&self.source_text, end);
        match (start_byte, end_byte) {
            (Some(start), Some(end)) => self.source_text.get(start..end).unwrap_or(""),
            _ => "",
        }
    }

    fn ident(&mut self, name: &str) -> IdentifierNode {
        let range = self.bank.intern(name);
        let token = Token::new(TokenKind::Identifier, range);
        Node::new(self.alloc_id(), range, Identifier::new(token))
    }

    fn alloc_id(&mut self) -> NodeId {
        self.ids.fresh()
    }

    fn ident_expr(&mut self, name: &str) -> Expr {
        let ident = self.ident(name);
        let range = ident.range();
        Node::new(self.alloc_id(), range, Expression::Identifier(ident))
    }

    fn helper_ident(&mut self, kind: HelperKind) -> Expr {
        self.used_helpers.insert(kind);
        self.ident_expr(kind.ident())
    }

    /// The authored spelling of an identifier, from the original text.
    fn identifier_name(&self, ident: &IdentifierNode) -> Option<String> {
        let token = ident.data().token();
        let start = self.source.utf16_to_byte(token.range().start()).ok()?;
        let end = self.source.utf16_to_byte(token.range().end()).ok()?;
        self.source.as_str().get(start..end).map(str::to_owned)
    }

    fn number_expr(&mut self, lexeme: &str) -> Expr {
        let range = self.bank.intern(lexeme);
        let token = Token::new(TokenKind::NumericLiteral, range);
        let literal = Node::new(self.alloc_id(), range, NumericLiteral::new(token));
        Node::new(
            self.alloc_id(),
            range,
            Expression::Literal(Literal::Number(literal)),
        )
    }
    fn boolean_expr(&mut self, value: bool) -> Expr {
        let (lexeme, kind) = if value {
            ("true", TokenKind::KwTrue)
        } else {
            ("false", TokenKind::KwFalse)
        };
        let range = self.bank.intern(lexeme);
        let token = Token::new(kind, range);
        let literal = Node::new(self.alloc_id(), range, BooleanLiteral::new(token));
        Node::new(
            self.alloc_id(),
            range,
            Expression::Literal(Literal::Boolean(literal)),
        )
    }

    fn null_expr(&mut self) -> Expr {
        let range = self.bank.intern("null");
        let token = Token::new(TokenKind::KwNull, range);
        let literal = Node::new(self.alloc_id(), range, NullLiteral::new(token));
        Node::new(
            self.alloc_id(),
            range,
            Expression::Literal(Literal::Null(literal)),
        )
    }

    fn string_literal(&mut self, unquoted: &str) -> StringLiteralNode {
        let lexeme = format!("\"{unquoted}\"");
        let range = self.bank.intern(&lexeme);
        let token = Token::new(TokenKind::StringLiteral, range);
        Node::new(self.alloc_id(), range, StringLiteral::new(token))
    }

    fn temp_ident(&mut self) -> IdentifierNode {
        let name = format!("_t{}", self.next_temp);
        self.next_temp += 1;
        self.ident(&name)
    }

    fn expression_temp(&mut self) -> IdentifierNode {
        let temp = self.temp_ident();
        if let Some(scope) = self.expression_temp_scopes.last_mut() {
            scope.push(temp.clone());
        }
        temp
    }

    fn temp_declaration(&mut self, temps: Vec<IdentifierNode>, range: TextRange) -> Option<Stmt> {
        if temps.is_empty() {
            return None;
        }
        let declarations = temps
            .into_iter()
            .map(|temp| self.make_declarator(temp, None, range))
            .collect();
        let declaration = VariableDeclaration {
            range,
            kind: VariableKind::Var,
            declarations,
        };
        Some(self.syn_node(range, Statement::Variable(declaration)))
    }

    fn rewrite_root_statements(&mut self, statements: &[Stmt], range: TextRange) -> Vec<Stmt> {
        self.expression_temp_scopes.push(Vec::new());
        let mut rewritten = self.rewrite_statements(statements);
        let temps = self.expression_temp_scopes.pop().unwrap_or_default();
        if let Some(declaration) = self.temp_declaration(temps, range) {
            rewritten.insert(0, declaration);
        }
        rewritten
    }

    fn node<T>(&mut self, range: TextRange, data: T) -> Node<T> {
        Node::new(self.alloc_id(), range, data)
    }
    /// Like [`node`](Self::node) but records the minted id as synthesized.
    fn syn_node<T>(&mut self, range: TextRange, data: T) -> Node<T> {
        let id = self.alloc_id();
        self.synthesized_ids.insert(id);
        Node::new(id, range, data)
    }

    /// Whether any of `ids` is recorded as synthesized.
    fn any_marked(&self, ids: impl IntoIterator<Item = NodeId>) -> bool {
        ids.into_iter().any(|id| self.synthesized_ids.contains(&id))
    }

    /// Mints a wrapper marked when `child_marked` is true, otherwise unmarked.
    fn wrap_marked<T>(&mut self, range: TextRange, data: T, child_marked: bool) -> Node<T> {
        if child_marked {
            self.syn_node(range, data)
        } else {
            self.node(range, data)
        }
    }

    fn diag(&mut self, code: DiagnosticCode, range: TextRange, message: &'static str) {
        self.diagnostics
            .push(Diagnostic::error(code, self.source_id, range, message));
    }

    fn finish_source(&self) -> Result<(Arc<SourceText>, Token, TextRange), SourcePositionError> {
        let source = Arc::new(SourceText::new(self.bank.text.clone())?);
        let len = source.len_utf16();
        let range =
            TextRange::new(Utf16Pos::ZERO, len).expect("source length is an ordered full range");
        let eof = Token::new(
            TokenKind::EndOfFile,
            TextRange::new(len, len).expect("equal source endpoints are ordered"),
        );
        Ok((source, eof, range))
    }

    fn needs(feature: LanguageFeature, options: &TransformOptions) -> bool {
        !options.target.supports(feature)
    }

    fn rewrite_statements(&mut self, statements: &[Stmt]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for statement in statements {
            out.extend(self.rewrite_statement(statement));
        }
        out
    }

    fn rewrite_statement(&mut self, statement: &Stmt) -> Vec<Stmt> {
        match statement.data() {
            Statement::Class(class) => self.rewrite_class_statement(statement, class),
            Statement::Function(function) => {
                let function = self.rewrite_function_like(&function.function, statement.range());
                vec![self.node(
                    statement.range(),
                    Statement::Function(FunctionDeclaration { function }),
                )]
            }
            Statement::Variable(declaration) => {
                self.rewrite_variable_statement(statement, declaration)
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => self.rewrite_export_named_declaration(statement, inner),
            Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
                ExportDefaultValue::Class(class) => {
                    if self.cjs.is_some() {
                        return self.cjs_default_class(statement.range(), class);
                    }
                    self.rewrite_default_export_class(statement, class)
                }
                ExportDefaultValue::Function(function) => {
                    if self.cjs.is_some() {
                        return self.cjs_default_function(statement.range(), function);
                    }
                    vec![statement.clone()]
                }
                ExportDefaultValue::Expression(value) => {
                    if self.cjs.is_some() {
                        let value = self.rewrite_expr(value);
                        return vec![self.cjs_export_default_assignment(statement.range(), value)];
                    }
                    let value = self.rewrite_expr(value);
                    vec![self.node(
                        statement.range(),
                        Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                            value: ExportDefaultValue::Expression(Box::new(value)),
                        })),
                    )]
                }
                ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => {
                    vec![statement.clone()]
                }
            },
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source,
                ..
            })) => {
                if self.cjs.is_some() && source.is_none() && !*type_only {
                    return self.cjs_export_specifiers(specifiers);
                }
                vec![statement.clone()]
            }
            Statement::Import(import) => {
                if self.cjs.is_none() {
                    return vec![statement.clone()];
                }
                if import.type_only {
                    // Type-only imports carry no runtime form.
                    return Vec::new();
                }
                match &import.clause {
                    // A side-effect import stays at its position as a bare
                    // require; clause imports move into the prelude.
                    None => vec![self.cjs_require_statement(&import.source)],
                    Some(_) => Vec::new(),
                }
            }
            Statement::Block(block) => {
                let statements = self.rewrite_statements(&block.data().statements);
                let block = self.node(block.range(), Block { statements });
                vec![self.node(statement.range(), Statement::Block(block))]
            }
            Statement::Return(ret) => {
                let argument = ret
                    .argument
                    .as_ref()
                    .map(|expression| Box::new(self.rewrite_expr(expression)));
                vec![self.node(
                    statement.range(),
                    Statement::Return(ReturnStatement { argument }),
                )]
            }
            Statement::Expression(expr) => {
                let mut candidate = &*expr.expression;
                while let Expression::Parenthesized(value) = candidate.data() {
                    candidate = value;
                }
                if Self::needs(LanguageFeature::Destructuring, self.options)
                    && let Expression::Assignment(assignment) = candidate.data()
                    && matches!(
                        assignment.left.data(),
                        AssignmentTarget::Object(_) | AssignmentTarget::Array(_)
                    )
                {
                    return self.lower_assignment_destructuring(statement.range(), assignment);
                }
                let expression = Box::new(self.rewrite_expr(&expr.expression));
                vec![self.node(
                    statement.range(),
                    Statement::Expression(ExpressionStatement { expression }),
                )]
            }
            Statement::If(value) => {
                let test = self.rewrite_expr(&value.test);
                let consequent = self.rewrite_single_statement(&value.consequent);
                let alternate = value
                    .alternate
                    .as_deref()
                    .map(|statement| Box::new(self.rewrite_single_statement(statement)));
                vec![self.node(
                    statement.range(),
                    Statement::If(IfStatement {
                        test: Box::new(test),
                        consequent: Box::new(consequent),
                        alternate,
                    }),
                )]
            }
            Statement::While(value) => {
                let test = self.rewrite_expr(&value.test);
                let body = self.rewrite_single_statement(&value.body);
                vec![self.node(
                    statement.range(),
                    Statement::While(WhileStatement {
                        test: Box::new(test),
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::DoWhile(value) => {
                let body = self.rewrite_single_statement(&value.body);
                let test = self.rewrite_expr(&value.test);
                vec![self.node(
                    statement.range(),
                    Statement::DoWhile(DoWhileStatement {
                        body: Box::new(body),
                        test: Box::new(test),
                    }),
                )]
            }
            Statement::With(value) => {
                let object = self.rewrite_expr(&value.object);
                let body = self.rewrite_single_statement(&value.body);
                vec![self.node(
                    statement.range(),
                    Statement::With(WithStatement {
                        object: Box::new(object),
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::Labeled(value) => {
                let body = self.rewrite_single_statement(&value.body);
                vec![self.node(
                    statement.range(),
                    Statement::Labeled(LabeledStatement {
                        label: value.label.clone(),
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::Throw(value) => {
                let argument = self.rewrite_expr(&value.argument);
                vec![self.node(
                    statement.range(),
                    Statement::Throw(ThrowStatement {
                        argument: Box::new(argument),
                    }),
                )]
            }
            Statement::ForOf(for_of) => {
                if for_of.mode == ForOfMode::Async
                    && Self::needs(LanguageFeature::AsyncIteration, self.options)
                {
                    self.diag(
                        codes::ASYNC_ITERATION_REQUIRES_ES2018,
                        statement.range(),
                        "for-await-of requires ScriptTarget::Es2018 or later",
                    );
                }
                // tsc's default ES5 for-of: index the iterable
                // (`for (var _i = 0, src = it; _i < src.length; _i++)`).
                // The binding moves into the body as a declaration, so
                // destructuring bindings and defaults compose through
                // the ordinary destructuring lowering.
                if for_of.mode == ForOfMode::Sync
                    && Self::needs(LanguageFeature::ForOf, self.options)
                {
                    return self.lower_sync_for_of(statement, for_of);
                }
                let iterable = self.rewrite_expr(&for_of.iterable);
                let body = self.rewrite_single_statement(&for_of.body);
                vec![self.node(
                    statement.range(),
                    Statement::ForOf(ForOfStatement {
                        mode: for_of.mode,
                        binding: for_of.binding.clone(),
                        iterable: Box::new(iterable),
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::ForIn(for_in) => {
                // The for-in construct is native ES5; only the head's
                // const/let binding needs var conversion there.
                let binding = match &for_in.binding {
                    ForBinding::Variable(declaration) => {
                        let mut declaration = declaration.clone();
                        if self.options.target <= ScriptTarget::Es5 {
                            declaration.kind = VariableKind::Var;
                        }
                        ForBinding::Variable(declaration)
                    }
                    target @ ForBinding::Target(_) => target.clone(),
                };
                let object = self.rewrite_expr(&for_in.object);
                let body = self.rewrite_single_statement(&for_in.body);
                vec![self.node(
                    statement.range(),
                    Statement::ForIn(ForInStatement {
                        binding,
                        object: Box::new(object),
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::For(value) => {
                let initializer = value
                    .initializer
                    .as_ref()
                    .map(|initializer| match initializer {
                        ForInitializer::Expression(expression) => {
                            ForInitializer::Expression(Box::new(self.rewrite_expr(expression)))
                        }
                        ForInitializer::Variable(declaration) => {
                            ForInitializer::Variable(declaration.clone())
                        }
                    });
                let test = value
                    .test
                    .as_deref()
                    .map(|expression| Box::new(self.rewrite_expr(expression)));
                let update = value
                    .update
                    .as_deref()
                    .map(|expression| Box::new(self.rewrite_expr(expression)));
                let body = self.rewrite_single_statement(&value.body);
                vec![self.node(
                    statement.range(),
                    Statement::For(ForStatement {
                        initializer,
                        test,
                        update,
                        body: Box::new(body),
                    }),
                )]
            }
            Statement::Try(value) => {
                let block = self.rewrite_block(&value.block);
                let handler = value.handler.as_ref().map(|handler| {
                    let body = self.rewrite_block(&handler.data().body);
                    self.node(
                        handler.range(),
                        CatchClause {
                            binding: handler.data().binding.clone(),
                            body,
                        },
                    )
                });
                let finalizer = value
                    .finalizer
                    .as_ref()
                    .map(|block| self.rewrite_block(block));
                vec![self.node(
                    statement.range(),
                    Statement::Try(TryStatement {
                        block,
                        handler,
                        finalizer,
                    }),
                )]
            }
            Statement::Switch(value) => {
                let discriminant = self.rewrite_expr(&value.discriminant);
                let cases = value
                    .cases
                    .iter()
                    .map(|case| {
                        let test = case
                            .data()
                            .test
                            .as_deref()
                            .map(|value| Box::new(self.rewrite_expr(value)));
                        let consequent = self.rewrite_statements(&case.data().consequent);
                        self.node(case.range(), SwitchCase { test, consequent })
                    })
                    .collect();
                vec![self.node(
                    statement.range(),
                    Statement::Switch(SwitchStatement {
                        discriminant: Box::new(discriminant),
                        cases,
                    }),
                )]
            }
            Statement::Declare(inner) => {
                let erased = match inner.data() {
                    Statement::Enum(_) | Statement::Namespace(_) => true,
                    Statement::Variable(declaration) => declaration.kind == VariableKind::Var,
                    _ => false,
                };
                if erased {
                    Vec::new()
                } else {
                    vec![statement.clone()]
                }
            }
            Statement::ImportEquals(_)
            | Statement::Export(_)
            | Statement::Interface(_)
            | Statement::TypeAlias(_)
            | Statement::Enum(_)
            | Statement::Namespace(_)
            | Statement::Empty
            | Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Debugger
            | Statement::Missing(_) => vec![statement.clone()],
        }
    }

    fn rewrite_single_statement(&mut self, statement: &Stmt) -> Stmt {
        let statements = self.rewrite_statement(statement);
        if statements.len() == 1 {
            return statements
                .into_iter()
                .next()
                .expect("one rewritten statement");
        }
        let block = self.node(statement.range(), Block { statements });
        self.node(statement.range(), Statement::Block(block))
    }

    fn rewrite_block(&mut self, block: &BlockNode) -> BlockNode {
        let statements = self.rewrite_statements(&block.data().statements);
        self.node(block.range(), Block { statements })
    }

    /// tsc's default ES5 for-of lowering: `for (var _i = 0, src = IT;
    /// _i < src.length; _i++) { BINDING = src[_i]; BODY }`. The binding
    /// statement enters the body as a rewritten declaration so pattern
    /// bindings and defaults compose with the destructuring lowering.
    fn lower_sync_for_of(&mut self, statement: &Stmt, for_of: &ForOfStatement) -> Vec<Stmt> {
        let range = statement.range();
        let counter = self.temp_ident();
        let source = self.temp_ident();
        let iterable = self.rewrite_expr(&for_of.iterable);
        let zero = self.number_expr("0");
        let counter_decl = self.make_declarator(counter.clone(), Some(zero), range);
        let counter_expr = self.node(counter.range(), Expression::Identifier(counter.clone()));
        let length = self.member_ident(&source, "length", range);
        let test = self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::LessThan,
                left: Box::new(counter_expr.clone()),
                right: Box::new(length),
            }),
        );
        let counter_target = Box::new(self.node(
            counter.range(),
            AssignmentTarget::Identifier(counter.clone()),
        ));
        let update = self.node(
            counter.range(),
            Expression::Update(UpdateExpression {
                operator: UpdateOperator::Increment,
                argument: counter_target,
                prefix: false,
            }),
        );
        // The body's binding declaration: source[counter].
        let element = self.member_computed(&source, &counter_expr, range);
        let binding_statement = match &for_of.binding {
            ForBinding::Variable(declaration) => {
                let mut declaration = declaration.clone();
                declaration.kind = VariableKind::Var;
                if declaration.declarations.len() == 1 {
                    let declarator = &declaration.declarations[0];
                    let lowered = self.node(
                        declarator.range(),
                        VariableDeclarator {
                            initializer: Some(Box::new(element)),
                            ..declarator.data().clone()
                        },
                    );
                    declaration.declarations = vec![lowered];
                    self.node(range, Statement::Variable(declaration))
                } else {
                    let body = self.rewrite_single_statement(&for_of.body);
                    return vec![self.node(
                        range,
                        Statement::ForOf(ForOfStatement {
                            mode: for_of.mode,
                            binding: ForBinding::Variable(declaration),
                            iterable: Box::new(iterable),
                            body: Box::new(body),
                        }),
                    )];
                }
            }
            // `target = source[counter];` - destructuring targets lower
            // through the statement rewriter like any assignment.
            ForBinding::Target(target) => {
                let left = match target.data() {
                    AssignmentTarget::Member(member) => {
                        self.rewrite_member_target(member, target.range())
                    }
                    _ => target.clone(),
                };
                let assignment = self.node(
                    range,
                    Expression::Assignment(AssignmentExpression {
                        operator: AssignmentOperator::Assign,
                        left,
                        right: Box::new(element),
                    }),
                );
                self.node(
                    range,
                    Statement::Expression(ExpressionStatement {
                        expression: Box::new(assignment),
                    }),
                )
            }
        };
        let source_decl = self.make_declarator(source.clone(), Some(iterable), range);
        let initializer = ForInitializer::Variable(VariableDeclaration {
            range,
            kind: VariableKind::Var,
            declarations: vec![counter_decl, source_decl],
        });
        // The binding declaration must itself lower (pattern bindings,
        // defaults) - route it through the statement rewriter.
        let lowered_binding = self.rewrite_statements(&[binding_statement]);
        // A non-block body is a single statement, not a missing one:
        // block_statements returns None for it, so the match form must
        // push it rather than drop it.
        let inner = self.rewrite_single_statement(&for_of.body);
        let mut statements = lowered_binding;
        match inner.data() {
            Statement::Block(block) => statements.extend(block.data().statements.iter().cloned()),
            _ => statements.push(inner.clone()),
        }
        let body_node = self.node(range, Block { statements });
        let body_stmt = self.node(range, Statement::Block(body_node));
        vec![self.node(
            range,
            Statement::For(ForStatement {
                initializer: Some(initializer),
                test: Some(Box::new(test)),
                update: Some(Box::new(update)),
                body: Box::new(body_stmt),
            }),
        )]
    }

    fn rewrite_variable_statement(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        if matches!(
            declaration.kind,
            VariableKind::Using | VariableKind::AwaitUsing
        ) && Self::needs(LanguageFeature::Using, self.options)
        {
            self.diag(
                codes::USING_UNSUPPORTED,
                statement.range(),
                "using declarations are not downleveled",
            );
        }
        if !Self::needs(LanguageFeature::Destructuring, self.options) {
            let outer_key_prelude = std::mem::take(&mut self.key_prelude);
            let mut statements = Vec::new();
            let mut declarations = Vec::with_capacity(declaration.declarations.len());
            for declarator in &declaration.declarations {
                let rewritten = self.rewrite_declarator_initializer(declarator);
                let prelude = std::mem::take(&mut self.key_prelude);
                if !prelude.is_empty() {
                    if !declarations.is_empty() {
                        statements.push(self.node(
                            statement.range(),
                            Statement::Variable(VariableDeclaration {
                                range: declaration.range,
                                kind: declaration.kind,
                                declarations: std::mem::take(&mut declarations),
                            }),
                        ));
                    }
                    statements.extend(prelude);
                }
                declarations.push(rewritten);
            }
            self.key_prelude = outer_key_prelude;
            statements.push(self.node(
                statement.range(),
                Statement::Variable(VariableDeclaration {
                    range: declaration.range,
                    kind: declaration.kind,
                    declarations,
                }),
            ));
            return statements;
        }
        // A suspending binding (yield in a default or computed key) cannot
        // live in a ternary: the machine must split the default selection
        // into branch statements it owns, preserving conditional
        // evaluation. Clean bindings lower to tsc's ternary declarators.
        let suspending = declaration.declarations.iter().any(|declarator| {
            count_binding_yields(&declarator.data().binding) > 0
                || binding_contains_await(&declarator.data().binding)
        });
        if suspending {
            return self.lower_suspending_declaration(declaration);
        }
        let mut declarations = Vec::new();
        self.key_prelude.clear();
        for declarator in &declaration.declarations {
            declarations.extend(self.lower_declarator(declaration.kind, declarator));
        }
        let key_prelude = std::mem::take(&mut self.key_prelude);
        let mut statements = key_prelude;
        statements.push(self.node(
            statement.range(),
            Statement::Variable(VariableDeclaration {
                range: declaration.range,
                kind: if self.options.target <= ScriptTarget::Es5 {
                    VariableKind::Var
                } else {
                    declaration.kind
                },
                declarations,
            }),
        ));
        statements
    }

    /// tsc's ES5 default shape: `name = read === void 0 ? DEFAULT : read`.
    /// The default runs only when the read is undefined; the rewrite pass
    /// owns await conversion inside it.
    fn default_ternary(&mut self, read: &IdentifierNode, default: &Expr, range: TextRange) -> Expr {
        let test_left = self.node(range, Expression::Identifier(read.clone()));
        let void_zero = self.void_zero(range);
        let test = self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictEqual,
                left: Box::new(test_left),
                right: Box::new(void_zero),
            }),
        );
        let consequent = self.rewrite_expr(default);
        let alternate = self.node(range, Expression::Identifier(read.clone()));
        self.node(
            range,
            Expression::Conditional(ConditionalExpression {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: Box::new(alternate),
            }),
        )
    }

    fn lower_declarator(
        &mut self,
        kind: VariableKind,
        declarator: &VariableDeclaratorNode,
    ) -> Vec<VariableDeclaratorNode> {
        let _ = kind;
        let data = declarator.data();
        match data.binding.data() {
            BindingPattern::Identifier(_) => {
                vec![self.rewrite_declarator_initializer(declarator)]
            }
            BindingPattern::Object(object) => {
                self.lower_object_binding(declarator, object, data.initializer.as_deref())
            }
            BindingPattern::Array(array) => {
                self.lower_array_binding(declarator, array, data.initializer.as_deref())
            }
            BindingPattern::Assignment(_)
            | BindingPattern::Rest(_)
            | BindingPattern::Missing(_) => {
                vec![self.rewrite_declarator_initializer(declarator)]
            }
        }
    }

    fn rhs_ident(
        &mut self,
        initializer: Option<&Expr>,
        range: TextRange,
    ) -> (IdentifierNode, bool) {
        if let Some(expression) = initializer
            && let Expression::Identifier(ident) = expression.data()
        {
            return (ident.clone(), false);
        }
        let temp = self.temp_ident();
        let _ = range;
        (temp, true)
    }

    fn rewrite_declarator_initializer(
        &mut self,
        declarator: &VariableDeclaratorNode,
    ) -> VariableDeclaratorNode {
        let initializer = declarator.data().initializer.as_deref().map(|value| {
            let rewritten = if let (BindingPattern::Identifier(binding), Expression::Class(class)) =
                (declarator.data().binding.data(), value.data())
            {
                let (source, _, _) = self.finish_source().expect("synthetic source");
                let range = binding.data().token().range();
                let start = source.utf16_to_byte(range.start()).expect("binding start");
                let end = source.utf16_to_byte(range.end()).expect("binding end");
                let name = source.as_str()[start..end].to_owned();
                self.lower_class_expression(value, class, Some(&name), true)
            } else {
                self.rewrite_expr(value)
            };
            Box::new(rewritten)
        });
        self.node(
            declarator.range(),
            VariableDeclarator {
                initializer,
                ..declarator.data().clone()
            },
        )
    }
    /// Lowers a declaration whose binding carries suspensions (yield in
    /// a default or computed key). Every bound name hoists first; reads
    /// become temp var statements; a default becomes an if/else whose
    /// arms assign the value temp, so the machine splits exactly at the
    /// default's suspension and the default evaluates only when the
    /// read is undefined — tsc's conditional-evaluation semantics in
    /// this machine's statement protocol.
    fn lower_suspending_declaration(&mut self, declaration: &VariableDeclaration) -> Vec<Stmt> {
        let range = declaration.range;
        let mut out = Vec::new();
        let mut names = Vec::new();
        for declarator in &declaration.declarations {
            collect_binding_names(&declarator.data().binding, &mut names);
        }
        if !names.is_empty() {
            let declarations = names
                .into_iter()
                .map(|name| self.make_declarator(name, None, range))
                .collect();
            let hoist = self.node(
                range,
                Statement::Variable(VariableDeclaration {
                    range,
                    kind: VariableKind::Var,
                    declarations,
                }),
            );
            out.push(hoist);
        }
        for declarator in &declaration.declarations {
            let initializer = declarator.data().initializer.as_deref();
            if let BindingPattern::Identifier(ident) = declarator.data().binding.data() {
                // A plain identifier declarator alongside a suspending
                // binding still needs its assignment; the rewrite pass
                // owns the initializer's awaits.
                if let Some(init) = initializer {
                    let value = self.rewrite_expr(init);
                    out.push(self.assign_statement(ident, value, range));
                }
                continue;
            }
            let (rhs, needs_temp) = self.rhs_ident(initializer, range);
            if needs_temp {
                let init = initializer
                    .map(|value| self.rewrite_expr(value))
                    .unwrap_or_else(|| self.ident_expr("undefined"));
                let declarations = vec![self.make_declarator(rhs.clone(), Some(init), range)];
                let temp = self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range,
                        kind: VariableKind::Var,
                        declarations,
                    }),
                );
                out.push(temp);
            }
            self.emit_binding_statements(&rhs, &declarator.data().binding, range, &mut out);
        }
        out
    }

    /// The statement form of one binding pattern: temp reads, default
    /// if/else selections, and final assignments. Only runs for
    /// suspending bindings; the clean form lives in the declarator
    /// lowering.
    fn emit_binding_statements(
        &mut self,
        rhs: &IdentifierNode,
        pattern: &Pattern,
        range: TextRange,
        out: &mut Vec<Stmt>,
    ) {
        match pattern.data() {
            BindingPattern::Identifier(_) | BindingPattern::Missing(_) => {}
            BindingPattern::Rest(_) => {}
            BindingPattern::Object(object) => {
                let mut rest_keys: Vec<RestExcludeKey> = Vec::new();
                for property in &object.properties {
                    // The member expression this property reads.
                    let member = match &property.name {
                        PropertyName::Computed(key) => {
                            let temp = self.temp_ident();
                            // The key temp needs its `var` even when the
                            // key suspends: the assignment form would
                            // otherwise target an undeclared name.
                            let temp_decl = vec![self.make_declarator(temp.clone(), None, range)];
                            out.push(self.node(
                                range,
                                Statement::Variable(VariableDeclaration {
                                    range,
                                    kind: VariableKind::Var,
                                    declarations: temp_decl,
                                }),
                            ));
                            if contains_yield(key) {
                                let assign =
                                    self.assign_statement(&temp, key.as_ref().clone(), range);
                                out.push(assign);
                            } else {
                                let value = self.rewrite_expr(key);
                                out.push(self.make_temp_declaration(temp.clone(), value, range));
                            }
                            rest_keys.push(RestExcludeKey::Computed(temp.clone()));
                            let reference =
                                self.node(temp.range(), Expression::Identifier(temp.clone()));
                            self.member_computed(rhs, &reference, range)
                        }
                        _ => match property_key_text(self, property) {
                            Some(key) => {
                                rest_keys.push(RestExcludeKey::Static(key.clone()));
                                self.member_ident(rhs, &key, range)
                            }
                            None => continue,
                        },
                    };
                    self.emit_property_statements(property, member, range, rhs, out);
                }
                // The rest property binds after the named reads.
                for property in &object.properties {
                    if let BindingPattern::Rest(rest) = property.binding.data()
                        && let BindingPattern::Identifier(ident) = rest.argument.data()
                    {
                        let excluded = self.rest_exclude_array(&rest_keys, range);
                        let call = self.rest_call(rhs, excluded, range);
                        out.push(self.assign_statement(ident, call, range));
                    }
                }
            }
            BindingPattern::Array(array) => {
                let mut index = 0usize;
                for element in &array.elements {
                    match element {
                        ArrayBindingElement::Elision | ArrayBindingElement::Missing(_) => {
                            index += 1;
                        }
                        ArrayBindingElement::Binding(binding) => {
                            if let BindingPattern::Rest(rest) = binding.data()
                                && let BindingPattern::Identifier(ident) = rest.argument.data()
                            {
                                // Rest consumes the remainder without
                                // advancing the element index.
                                let slice = self.slice_call(rhs, index, range);
                                out.push(self.assign_statement(ident, slice, range));
                                continue;
                            }
                            self.emit_element_statements(rhs, binding, index, range, out);
                            index += 1;
                        }
                    }
                }
            }
            BindingPattern::Assignment(assignment) => {
                let member = self.member_index(rhs, 0, range);
                self.emit_defaulted_binding(
                    &assignment.left,
                    &assignment.right,
                    member,
                    range,
                    out,
                );
            }
        }
    }

    /// One object property's statement form: read temp, default if/else,
    /// then the target bind or nested recursion.
    fn emit_property_statements(
        &mut self,
        property: &ObjectBindingProperty,
        member: Expr,
        range: TextRange,
        _rhs: &IdentifierNode,
        out: &mut Vec<Stmt>,
    ) {
        match property.binding.data() {
            BindingPattern::Identifier(ident) => {
                let read = self.temp_ident();
                let declarations = vec![self.make_declarator(read.clone(), Some(member), range)];
                out.push(self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range,
                        kind: VariableKind::Var,
                        declarations,
                    }),
                ));
                let value = match &property.initializer {
                    Some(default) => {
                        let value = self.temp_ident();
                        let declarations = vec![self.make_declarator(value.clone(), None, range)];
                        out.push(self.node(
                            range,
                            Statement::Variable(VariableDeclaration {
                                range,
                                kind: VariableKind::Var,
                                declarations,
                            }),
                        ));
                        let selection = self.default_selection(&read, default, &value, range);
                        out.push(selection);
                        value
                    }
                    None => read,
                };
                let value_expr = self.node(range, Expression::Identifier(value.clone()));
                out.push(self.assign_statement(ident, value_expr, range));
            }
            _ => {
                let value = self.emit_read_with_default(
                    &property.binding,
                    &property.initializer,
                    member,
                    range,
                    out,
                );
                self.emit_binding_statements(&value, &property.binding, range, out);
            }
        }
    }

    fn emit_element_statements(
        &mut self,
        rhs: &IdentifierNode,
        binding: &Pattern,
        index: usize,
        range: TextRange,
        out: &mut Vec<Stmt>,
    ) {
        let member = self.member_index(rhs, index, range);
        match binding.data() {
            BindingPattern::Identifier(_) => {
                let value = self.emit_read_with_default(binding, &None, member, range, out);
                if let BindingPattern::Identifier(ident) = binding.data() {
                    let value_expr = self.node(range, Expression::Identifier(value.clone()));
                    out.push(self.assign_statement(ident, value_expr, range));
                }
            }
            BindingPattern::Assignment(assignment) => {
                self.emit_defaulted_binding(
                    &assignment.left,
                    &assignment.right,
                    member,
                    range,
                    out,
                );
            }
            _ => {
                let value = self.emit_read_with_default(binding, &None, member, range, out);
                self.emit_binding_statements(&value, binding, range, out);
            }
        }
    }

    /// The read temp for a member, plus the if/else default selection
    /// when a default exists. Returns the identifier holding the value.
    fn emit_read_with_default(
        &mut self,
        _binding: &Pattern,
        initializer: &Option<Box<Expr>>,
        member: Expr,
        range: TextRange,
        out: &mut Vec<Stmt>,
    ) -> IdentifierNode {
        let read = self.temp_ident();
        let declarations = vec![self.make_declarator(read.clone(), Some(member), range)];
        out.push(self.node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                kind: VariableKind::Var,
                declarations,
            }),
        ));
        match initializer {
            Some(default) => {
                let value = self.temp_ident();
                // The value temp needs its `var`: it is assigned only
                // inside the selection's branches, so nothing else
                // declares it and strict mode would throw on the
                // implicit global.
                let declarations = vec![self.make_declarator(value.clone(), None, range)];
                out.push(self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range,
                        kind: VariableKind::Var,
                        declarations,
                    }),
                ));
                let selection = self.default_selection(&read, default, &value, range);
                out.push(selection);
                value
            }
            None => read,
        }
    }

    /// `if (read === void 0) { value = DEFAULT; } else { value = read; }`
    fn default_selection(
        &mut self,
        read: &IdentifierNode,
        default: &Expr,
        value: &IdentifierNode,
        range: TextRange,
    ) -> Stmt {
        let test_left = self.node(range, Expression::Identifier(read.clone()));
        let void_zero = self.void_zero(range);
        let test = self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictEqual,
                left: Box::new(test_left),
                right: Box::new(void_zero),
            }),
        );
        let rewritten = self.rewrite_expr(default);
        let then_assign = self.assign_statement(value, rewritten, range);
        let then_block = self.node(
            range,
            Block {
                statements: vec![then_assign],
            },
        );
        let read_expr = self.node(range, Expression::Identifier(read.clone()));
        let else_assign = self.assign_statement(value, read_expr, range);
        let else_block = self.node(
            range,
            Block {
                statements: vec![else_assign],
            },
        );
        let then_stmt = self.node(range, Statement::Block(then_block));
        let else_stmt = self.node(range, Statement::Block(else_block));
        self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(test),
                consequent: Box::new(then_stmt),
                alternate: Some(Box::new(else_stmt)),
            }),
        )
    }

    /// Binds a target pattern to a member read with a default: the
    /// identifier case assigns the if/else value temp; nested patterns
    /// recurse off the defaulted read.
    fn emit_defaulted_binding(
        &mut self,
        left: &Pattern,
        right: &Expr,
        member: Expr,
        range: TextRange,
        out: &mut Vec<Stmt>,
    ) {
        match left.data() {
            BindingPattern::Identifier(ident) => {
                let read = self.temp_ident();
                let declarations = vec![self.make_declarator(read.clone(), Some(member), range)];
                out.push(self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range,
                        kind: VariableKind::Var,
                        declarations,
                    }),
                ));
                let value = self.temp_ident();
                let declarations = vec![self.make_declarator(value.clone(), None, range)];
                out.push(self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range,
                        kind: VariableKind::Var,
                        declarations,
                    }),
                ));
                let selection = self.default_selection(&read, right, &value, range);
                out.push(selection);
                let value_expr = self.node(range, Expression::Identifier(value.clone()));
                out.push(self.assign_statement(ident, value_expr, range));
            }
            _ => {
                let boxed = Some(Box::new(right.clone()));
                let value = self.emit_read_with_default(left, &boxed, member, range, out);
                self.emit_binding_statements(&value, left, range, out);
            }
        }
    }

    fn lower_object_binding(
        &mut self,
        declarator: &VariableDeclaratorNode,
        object: &ObjectBindingPattern,
        initializer: Option<&Expr>,
    ) -> Vec<VariableDeclaratorNode> {
        let range = declarator.range();
        let (rhs, needs_temp) = self.rhs_ident(initializer, range);
        let mut out = Vec::new();
        if needs_temp {
            let init = initializer
                .map(|value| self.rewrite_expr(value))
                .unwrap_or_else(|| self.ident_expr("undefined"));
            out.push(self.make_declarator(rhs.clone(), Some(init), range));
        }
        self.lower_object_pattern(&rhs, object, range, &mut out);
        out
    }

    /// Lowers one object pattern against a source identifier, appending
    /// declarators. Identifier bindings with defaults emit tsc's shape
    /// (`var _t = o.a, a = _t === void 0 ? 1 : _t`); nested patterns
    /// read off the defaulted temp (`{x: {y} = {}}` reads `y` off the
    /// ternary result, so the default feeds the nested reads).
    fn lower_object_pattern(
        &mut self,
        rhs: &IdentifierNode,
        object: &ObjectBindingPattern,
        range: TextRange,
        out: &mut Vec<VariableDeclaratorNode>,
    ) -> Vec<RestExcludeKey> {
        let mut rest_keys = Vec::new();
        // Properties evaluate in source order: a computed key runs after
        // the reads and defaults of the properties before it, so its temp
        // is a declarator in sequence rather than a hoisted prelude.
        for property in &object.properties {
            if let PropertyName::Computed(key) = &property.name {
                let temp = self.temp_ident();
                let value = self.rewrite_expr(key);
                out.push(self.make_declarator(temp.clone(), Some(value), range));
                rest_keys.push(RestExcludeKey::Computed(temp.clone()));
                let reference = self.node(temp.range(), Expression::Identifier(temp.clone()));
                let member = self.member_computed(rhs, &reference, range);
                self.lower_property_binding(property, member, range, out);
                continue;
            }
            if let BindingPattern::Rest(rest) = property.binding.data() {
                if let BindingPattern::Identifier(ident) = rest.argument.data() {
                    let excluded = self.rest_exclude_array(&rest_keys, range);
                    let call = self.rest_call(rhs, excluded, range);
                    out.push(self.make_declarator(ident.clone(), Some(call), range));
                }
                continue;
            }
            let Some(key) = property_key_text(self, property) else {
                continue;
            };
            rest_keys.push(RestExcludeKey::Static(key.clone()));
            let member = self.member_ident(rhs, &key, range);
            self.lower_property_binding(property, member, range, out);
        }
        rest_keys
    }

    /// Binds one property's value expression: an identifier target with a
    /// default emits the read-then-ternary pair; a nested pattern reads
    /// through a temp (defaulted when a default exists); a bare
    /// identifier clones the read.
    fn lower_property_binding(
        &mut self,
        property: &ObjectBindingProperty,
        member: Expr,
        range: TextRange,
        out: &mut Vec<VariableDeclaratorNode>,
    ) {
        match property.binding.data() {
            BindingPattern::Identifier(ident) => match &property.initializer {
                Some(default) => {
                    let read = self.temp_ident();
                    out.push(self.make_declarator(read.clone(), Some(member), range));
                    let ternary = self.default_ternary(&read, default, range);
                    out.push(self.make_declarator(ident.clone(), Some(ternary), range));
                }
                None => out.push(self.make_declarator(ident.clone(), Some(member), range)),
            },
            BindingPattern::Object(nested) => {
                let value = self.default_or_read(&property.initializer, member, range, out);
                self.lower_object_pattern(&value, nested, range, out);
            }
            BindingPattern::Array(nested) => {
                let value = self.default_or_read(&property.initializer, member, range, out);
                self.lower_array_pattern(&value, nested, range, out);
            }
            // Rest and invalid shapes never carry defaults; the caller's
            // rest pass and parser refusals own them.
            _ => {}
        }
    }

    /// A nested pattern's source: the read temp, or the defaulted temp
    /// when a default exists (tsc reads nested bindings off the
    /// ternary's value).
    fn default_or_read(
        &mut self,
        initializer: &Option<Box<Expr>>,
        member: Expr,
        range: TextRange,
        out: &mut Vec<VariableDeclaratorNode>,
    ) -> IdentifierNode {
        let read = self.temp_ident();
        out.push(self.make_declarator(read.clone(), Some(member), range));
        match initializer {
            Some(default) => {
                let value = self.temp_ident();
                let ternary = self.default_ternary(&read, default, range);
                out.push(self.make_declarator(value.clone(), Some(ternary), range));
                value
            }
            None => read,
        }
    }

    fn lower_array_binding(
        &mut self,
        declarator: &VariableDeclaratorNode,
        array: &ArrayBindingPattern,
        initializer: Option<&Expr>,
    ) -> Vec<VariableDeclaratorNode> {
        let range = declarator.range();
        let (rhs, needs_temp) = self.rhs_ident(initializer, range);
        let mut out = Vec::new();
        if needs_temp {
            let init = initializer
                .map(|value| self.rewrite_expr(value))
                .unwrap_or_else(|| self.ident_expr("undefined"));
            out.push(self.make_declarator(rhs.clone(), Some(init), range));
        }
        self.lower_array_pattern(&rhs, array, range, &mut out);
        out
    }

    /// Lowers one array pattern against a source identifier. Elements
    /// with defaults (`[a = 1]`) emit the read-then-ternary pair;
    /// `[a = 1]` under an assignment-wrapped nested pattern
    /// (`[[d = 2] = []]`) defaults the element read before the nested
    /// pattern consumes it. Holes advance the index without emitting.
    fn lower_array_pattern(
        &mut self,
        rhs: &IdentifierNode,
        array: &ArrayBindingPattern,
        range: TextRange,
        out: &mut Vec<VariableDeclaratorNode>,
    ) {
        let mut index = 0usize;
        for element in &array.elements {
            match element {
                ArrayBindingElement::Elision | ArrayBindingElement::Missing(_) => index += 1,
                ArrayBindingElement::Binding(binding) => match binding.data() {
                    BindingPattern::Identifier(ident) => {
                        let member = self.member_index(rhs, index, range);
                        out.push(self.make_declarator(ident.clone(), Some(member), range));
                        index += 1;
                    }
                    BindingPattern::Rest(rest) => {
                        if let BindingPattern::Identifier(ident) = rest.argument.data() {
                            let slice = self.slice_call(rhs, index, range);
                            out.push(self.make_declarator(ident.clone(), Some(slice), range));
                        }
                    }
                    BindingPattern::Object(nested) => {
                        let member = self.member_index(rhs, index, range);
                        let value = self.default_or_read(&None, member, range, out);
                        self.lower_object_pattern(&value, nested, range, out);
                        index += 1;
                    }
                    BindingPattern::Array(nested) => {
                        let member = self.member_index(rhs, index, range);
                        let value = self.default_or_read(&None, member, range, out);
                        self.lower_array_pattern(&value, nested, range, out);
                        index += 1;
                    }
                    // `[a = 1]`: the default applies to the element read.
                    BindingPattern::Assignment(assignment) => {
                        let member = self.member_index(rhs, index, range);
                        match assignment.left.data() {
                            BindingPattern::Identifier(ident) => {
                                let read = self.temp_ident();
                                out.push(self.make_declarator(read.clone(), Some(member), range));
                                let ternary = self.default_ternary(&read, &assignment.right, range);
                                out.push(self.make_declarator(ident.clone(), Some(ternary), range));
                            }
                            BindingPattern::Object(nested) => {
                                let value = self.default_or_read(
                                    &Some(assignment.right.clone()),
                                    member,
                                    range,
                                    out,
                                );
                                self.lower_object_pattern(&value, nested, range, out);
                            }
                            BindingPattern::Array(nested) => {
                                let value = self.default_or_read(
                                    &Some(assignment.right.clone()),
                                    member,
                                    range,
                                    out,
                                );
                                self.lower_array_pattern(&value, nested, range, out);
                            }
                            _ => {}
                        }
                        index += 1;
                    }
                    BindingPattern::Missing(_) => index += 1,
                },
            }
        }
    }

    fn make_declarator(
        &mut self,
        ident: IdentifierNode,
        initializer: Option<Expr>,
        range: TextRange,
    ) -> VariableDeclaratorNode {
        let binding = self.node(ident.range(), BindingPattern::Identifier(ident));
        self.node(
            range,
            VariableDeclarator {
                binding,
                definite: false,
                type_annotation: None,
                initializer: initializer.map(Box::new),
            },
        )
    }

    /// `object[<computed expression>]`.
    fn member_computed(&mut self, object: &IdentifierNode, key: &Expr, range: TextRange) -> Expr {
        let object_expr = self.node(object.range(), Expression::Identifier(object.clone()));
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object_expr),
                property: MemberProperty::Computed(Box::new(key.clone())),
                optional: false,
            }),
        )
    }

    fn member_ident(&mut self, object: &IdentifierNode, key: &str, range: TextRange) -> Expr {
        let object_expr = self.node(object.range(), Expression::Identifier(object.clone()));
        let property = self.ident(key);
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object_expr),
                property: MemberProperty::Named(property),
                optional: false,
            }),
        )
    }

    fn member_index(&mut self, object: &IdentifierNode, index: usize, range: TextRange) -> Expr {
        let object_expr = self.node(object.range(), Expression::Identifier(object.clone()));
        let index_expr = self.number_expr(&index.to_string());
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object_expr),
                property: MemberProperty::Computed(Box::new(index_expr)),
                optional: false,
            }),
        )
    }

    /// `object.property` / `object[key]` over an arbitrary value expression.
    fn member_expr(&mut self, object: &Expr, property: MemberProperty, range: TextRange) -> Expr {
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object.clone()),
                property,
                optional: false,
            }),
        )
    }

    /// Lowers one destructuring assignment at targets below ES2015 into a
    /// statement per assignment target. The right-hand side evaluates once,
    /// nested pattern values are captured in temps, and computed keys that
    /// are not bare identifiers evaluate once into a preceding temp.
    fn lower_assignment_destructuring(
        &mut self,
        range: TextRange,
        assignment: &AssignmentExpression,
    ) -> Vec<Stmt> {
        let mut statements = Vec::new();
        let value = if matches!(assignment.right.data(), Expression::Identifier(_)) {
            (*assignment.right).clone()
        } else {
            let temp = self.temp_ident();
            let right = self.rewrite_expr(&assignment.right);
            statements.push(self.make_temp_declaration(temp.clone(), right, range));
            self.node(temp.range(), Expression::Identifier(temp))
        };
        self.lower_assignment_target(&assignment.left, &value, &mut statements, range);
        statements
    }

    fn lower_assignment_target(
        &mut self,
        target: &AssignmentTargetNode,
        value: &Expr,
        statements: &mut Vec<Stmt>,
        range: TextRange,
    ) {
        match target.data() {
            AssignmentTarget::Identifier(_) | AssignmentTarget::Member(_) => {
                let assignment = Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: target.clone(),
                    right: Box::new(value.clone()),
                });
                let expression = self.node(target.range(), assignment);
                statements.push(self.node(
                    target.range(),
                    Statement::Expression(ExpressionStatement {
                        expression: Box::new(expression),
                    }),
                ));
            }
            AssignmentTarget::Object(pattern) => {
                for property in &pattern.properties {
                    self.lower_assignment_property(property, value, statements, range);
                }
            }
            AssignmentTarget::Array(pattern) => {
                for (index, element) in pattern.elements.iter().enumerate() {
                    let AssignmentArrayElement::Target(inner) = element else {
                        continue;
                    };
                    let index_expr = self.number_expr(&index.to_string());
                    let member = self.member_expr(
                        value,
                        MemberProperty::Computed(Box::new(index_expr)),
                        range,
                    );
                    self.assign_or_recurse(inner, member, statements, range);
                }
            }
            AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(_) => {}
        }
    }

    /// Reads `member` once when `target` nests a pattern, otherwise assigns
    /// it directly.
    fn assign_or_recurse(
        &mut self,
        target: &AssignmentTargetNode,
        member: Expr,
        statements: &mut Vec<Stmt>,
        range: TextRange,
    ) {
        if matches!(
            target.data(),
            AssignmentTarget::Object(_) | AssignmentTarget::Array(_)
        ) {
            let temp = self.temp_ident();
            statements.push(self.make_temp_declaration(temp.clone(), member, range));
            let value = self.node(temp.range(), Expression::Identifier(temp));
            self.lower_assignment_target(target, &value, statements, range);
        } else {
            self.lower_assignment_target(target, &member, statements, range);
        }
    }

    fn lower_assignment_property(
        &mut self,
        property: &AssignmentObjectProperty,
        value: &Expr,
        statements: &mut Vec<Stmt>,
        range: TextRange,
    ) {
        let Some(member) = self.assignment_property_member(property, value, statements) else {
            // A folded spread element has no name or target; report it the
            // way the diagnostic for nested forms would.
            self.diag(
                codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015,
                property_name_range(&property.name),
                "destructuring assignment requires ScriptTarget::Es2015 or later",
            );
            return;
        };
        if let Some(default) = &property.initializer {
            let read = self.temp_ident();
            statements.push(self.make_temp_declaration(read.clone(), member, range));
            let reference = self.node(read.range(), Expression::Identifier(read.clone()));
            let void_zero = self.void_zero(range);
            let test = self.node(
                range,
                Expression::Binary(BinaryExpression {
                    operator: BinaryOperator::StrictEqual,
                    left: Box::new(reference),
                    right: Box::new(void_zero),
                }),
            );
            let left = self.node(read.range(), AssignmentTarget::Identifier(read.clone()));
            let default_value = self.rewrite_expr(default);
            let assignment = Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(default_value),
            });
            let expression = self.node(range, assignment);
            let consequent = self.node(
                range,
                Statement::Expression(ExpressionStatement {
                    expression: Box::new(expression),
                }),
            );
            statements.push(self.node(
                range,
                Statement::If(IfStatement {
                    test: Box::new(test),
                    consequent: Box::new(consequent),
                    alternate: None,
                }),
            ));
            let read_value = self.node(read.range(), Expression::Identifier(read));
            self.assign_or_recurse(&property.target, read_value, statements, range);
        } else {
            self.assign_or_recurse(&property.target, member, statements, range);
        }
    }

    /// The `value[key]` read for one assignment-pattern property. String and
    /// number literal names keep their bracket form; a bare identifier
    /// computed key is pure and inlines, and any other computed key
    /// evaluates once into a preceding temp.
    fn assignment_property_member(
        &mut self,
        property: &AssignmentObjectProperty,
        value: &Expr,
        statements: &mut Vec<Stmt>,
    ) -> Option<Expr> {
        let range = property_name_range(&property.name);
        match &property.name {
            PropertyName::Identifier(ident) => {
                let key = self.token_text(ident.data().token()).to_owned();
                let property = self.ident(&key);
                Some(self.member_expr(value, MemberProperty::Named(property), range))
            }
            PropertyName::String(literal) => {
                let key = self.node(
                    literal.range(),
                    Expression::Literal(Literal::String(literal.clone())),
                );
                Some(self.member_expr(value, MemberProperty::Computed(Box::new(key)), range))
            }
            PropertyName::Number(literal) => {
                let key = self.node(
                    literal.range(),
                    Expression::Literal(Literal::Number(literal.clone())),
                );
                Some(self.member_expr(value, MemberProperty::Computed(Box::new(key)), range))
            }
            PropertyName::Computed(key) => {
                let key = self.rewrite_expr(key);
                let key = if matches!(key.data(), Expression::Identifier(_)) {
                    key
                } else {
                    let temp = self.temp_ident();
                    statements.push(self.make_temp_declaration(temp.clone(), key.clone(), range));
                    self.node(temp.range(), Expression::Identifier(temp))
                };
                Some(self.member_expr(value, MemberProperty::Computed(Box::new(key)), range))
            }
            PropertyName::Private(_) | PropertyName::Missing(_) => None,
        }
    }

    fn slice_call(&mut self, object: &IdentifierNode, start: usize, range: TextRange) -> Expr {
        let member = self.member_ident(object, "slice", range);
        let start_expr = self.number_expr(&start.to_string());
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(member),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(start_expr))],
            }),
        )
    }

    /// The `__rest` exclusion array. Static keys contribute plain
    /// strings; computed keys contribute tsc's runtime coercion
    /// (`typeof t === "symbol" ? t : t + ""`), because the excluded
    /// property name is only known at runtime.
    fn rest_exclude_array(&mut self, keys: &[RestExcludeKey], range: TextRange) -> Expr {
        let mut elements = Vec::new();
        for key in keys {
            let expr = match key {
                RestExcludeKey::Static(name) => {
                    let literal = self.string_literal(name);
                    self.node(
                        literal.range(),
                        Expression::Literal(Literal::String(literal)),
                    )
                }
                RestExcludeKey::Computed(temp) => {
                    let temp_expr = self.node(temp.range(), Expression::Identifier(temp.clone()));
                    let symbol = self.string_literal("symbol");
                    let symbol_expr =
                        self.node(symbol.range(), Expression::Literal(Literal::String(symbol)));
                    let typeof_argument =
                        self.node(temp.range(), Expression::Identifier(temp.clone()));
                    let typeof_expr = self.node(
                        temp.range(),
                        Expression::Unary(UnaryExpression {
                            operator: UnaryOperator::Typeof,
                            argument: Box::new(typeof_argument),
                        }),
                    );
                    let test = self.node(
                        temp.range(),
                        Expression::Binary(BinaryExpression {
                            operator: BinaryOperator::StrictEqual,
                            left: Box::new(typeof_expr),
                            right: Box::new(symbol_expr),
                        }),
                    );
                    let empty = self.string_literal("");
                    let empty_expr =
                        self.node(empty.range(), Expression::Literal(Literal::String(empty)));
                    let concat_left = self.node(temp.range(), Expression::Identifier(temp.clone()));
                    let concat = self.node(
                        temp.range(),
                        Expression::Binary(BinaryExpression {
                            operator: BinaryOperator::Add,
                            left: Box::new(concat_left),
                            right: Box::new(empty_expr),
                        }),
                    );
                    self.node(
                        temp.range(),
                        Expression::Conditional(ConditionalExpression {
                            test: Box::new(test),
                            consequent: Box::new(temp_expr),
                            alternate: Box::new(concat),
                        }),
                    )
                }
            };
            elements.push(ArrayElement::Expression(Box::new(expr)));
        }
        self.node(range, Expression::Array(ArrayLiteral { elements }))
    }

    fn rest_call(&mut self, object: &IdentifierNode, excluded: Expr, range: TextRange) -> Expr {
        let callee = self.helper_ident(HelperKind::Rest);
        let object_expr = self.node(object.range(), Expression::Identifier(object.clone()));
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(object_expr)),
                    CallArgument::Expression(Box::new(excluded)),
                ],
            }),
        )
    }

    fn rewrite_class_statement(&mut self, statement: &Stmt, class: &ClassDeclaration) -> Vec<Stmt> {
        self.rewrite_class_dispatch(statement, statement.range(), class, ExportWrapper::None)
    }

    fn rewrite_named_export_class(
        &mut self,
        statement: &Stmt,
        inner: &Stmt,
        class: &ClassDeclaration,
    ) -> Vec<Stmt> {
        self.rewrite_class_dispatch(statement, inner.range(), class, ExportWrapper::Named)
    }

    fn rewrite_default_export_class(
        &mut self,
        statement: &Stmt,
        class: &ClassDeclaration,
    ) -> Vec<Stmt> {
        self.rewrite_class_dispatch(statement, statement.range(), class, ExportWrapper::Default)
    }

    fn rewrite_class_dispatch(
        &mut self,
        statement: &Stmt,
        class_range: TextRange,
        class: &ClassDeclaration,
        wrapper: ExportWrapper,
    ) -> Vec<Stmt> {
        if Self::needs(LanguageFeature::Classes, self.options) {
            self.diag(
                codes::CLASS_REQUIRES_ES2015,
                statement.range(),
                "class syntax requires ScriptTarget::Es2015 or later",
            );
            return vec![statement.clone()];
        }
        let mut class = class.clone();
        let restored_name = if matches!(wrapper, ExportWrapper::Default) && class.name.is_none() {
            let name = self.temp_ident();
            class.name = Some(name.clone());
            Some(name)
        } else {
            None
        };
        let mut lowered = self.lower_class(&class, class_range, None);
        let class_statement = self.node(class_range, Statement::Class(lowered.class));
        let wrapped = match wrapper {
            ExportWrapper::None => class_statement,
            ExportWrapper::Named => self.node(
                statement.range(),
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(Box::new(class_statement)),
                )),
            ),
            ExportWrapper::Default => {
                let Statement::Class(class) = class_statement.data() else {
                    unreachable!("class dispatch must produce class");
                };
                self.node(
                    statement.range(),
                    Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                        value: ExportDefaultValue::Class(class.clone()),
                    })),
                )
            }
        };
        lowered.prelude.push(wrapped);
        if let Some(name) = restored_name {
            lowered
                .prelude
                .push(self.restore_default_class_name(&name, statement.range()));
        }
        lowered.prelude.extend(lowered.postlude);
        lowered.prelude
    }

    fn lower_class(
        &mut self,
        class: &ClassDeclaration,
        range: TextRange,
        static_target: Option<&IdentifierNode>,
    ) -> ClassLowering {
        let mode = FieldMode::for_options(self.options);
        let mut class = class.clone();
        let mut prelude = Vec::new();
        let mut instance = Vec::new();
        let mut static_steps = Vec::new();
        let mut members = Vec::new();
        let mut constructor = None;
        let has_computed = class.members.iter().any(|member| {
            let name = match member.data() {
                ClassMember::Property(property) => Some(&property.name),
                ClassMember::Method(method) => Some(&method.name),
                ClassMember::AutoAccessor(accessor) => Some(&accessor.name),
                ClassMember::Constructor(_)
                | ClassMember::StaticBlock(_)
                | ClassMember::IndexSignature(_)
                | ClassMember::Missing(_) => None,
            };
            name.is_some_and(|name| matches!(name, PropertyName::Computed(_)))
        });
        if !matches!(mode, FieldMode::Native)
            && has_computed
            && let Some(heritage) = class.extends.as_mut()
        {
            let temp = self.temp_ident();
            let value = self.rewrite_expr(&heritage.expression);
            prelude.push(self.make_temp_declaration(
                temp.clone(),
                value,
                heritage.expression.range(),
            ));
            *heritage.expression = self.node(temp.range(), Expression::Identifier(temp));
        } else if let Some(heritage) = class.extends.as_mut() {
            *heritage.expression = self.rewrite_expr(&heritage.expression);
        }
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(ctor) => {
                    let mut ctor = ctor.clone();
                    let statements = self.rewrite_statements(&ctor.body.data().statements);
                    ctor.body = self.node(ctor.body.range(), Block { statements });
                    constructor = Some(self.node(member.range(), ClassMember::Constructor(ctor)));
                }
                ClassMember::Property(property)
                    if property.modifiers.is_declare || property.modifiers.is_abstract => {}
                ClassMember::Property(property) if matches!(mode, FieldMode::Native) => {
                    let mut property = property.clone();
                    property.name = self.rewrite_property_name(&property.name);
                    property.initializer = property
                        .initializer
                        .as_deref()
                        .map(|value| Box::new(self.rewrite_expr(value)));
                    members.push(self.node(member.range(), ClassMember::Property(property)));
                }
                ClassMember::Property(property) => {
                    if matches!(property.name, PropertyName::Private(_)) {
                        self.diag(
                            codes::PRIVATE_FIELD_REQUIRES_ES2022,
                            member.range(),
                            "private class fields require ScriptTarget::Es2022 or later",
                        );
                        members.push(member.clone());
                        continue;
                    }
                    let name =
                        self.lower_class_member_name(&property.name, &mut prelude, member.range());
                    // Assignment semantics define nothing for a declaration
                    // without an initializer: tsc emits no assignment and no
                    // constructor for it (baseline
                    // computedPropertyNames36_ES5(target=es2015).js keeps
                    // `class Foo {\n}`). Define mode still materializes the
                    // `void 0` default through defineProperty below, so only
                    // Assign drops the entry. Computed-key side effects already
                    // live in `prelude`, independent of this push.
                    if property.initializer.is_none() && matches!(mode, FieldMode::Assign) {
                        continue;
                    }
                    let init = property
                        .initializer
                        .as_deref()
                        .map(|value| self.rewrite_expr(value))
                        .unwrap_or_else(|| self.void_zero(member.range()));
                    let field = FieldInit {
                        name,
                        init,
                        range: member.range(),
                    };
                    if property.modifiers.is_static {
                        static_steps.push(StaticStep::Field(Box::new(field)));
                    } else {
                        instance.push(field);
                    }
                }
                ClassMember::Method(method) => {
                    let mut method = method.clone();
                    method.name = if matches!(mode, FieldMode::Native) {
                        self.rewrite_property_name(&method.name)
                    } else {
                        self.lower_class_member_name(&method.name, &mut prelude, member.range())
                    };
                    method.function = self.rewrite_function_like(&method.function, member.range());
                    members.push(self.node(member.range(), ClassMember::Method(method)));
                }
                ClassMember::AutoAccessor(accessor) if matches!(mode, FieldMode::Native) => {
                    let mut accessor = accessor.clone();
                    accessor.name = self.rewrite_property_name(&accessor.name);
                    accessor.initializer = accessor
                        .initializer
                        .as_deref()
                        .map(|value| Box::new(self.rewrite_expr(value)));
                    members.push(self.node(member.range(), ClassMember::AutoAccessor(accessor)));
                }
                ClassMember::AutoAccessor(_) => {
                    self.diag(
                        codes::AUTO_ACCESSOR_REQUIRES_ES2022,
                        member.range(),
                        "auto-accessors require ScriptTarget::Es2022 or later",
                    );
                    members.push(member.clone());
                }
                ClassMember::StaticBlock(block) if matches!(mode, FieldMode::Native) => {
                    let statements = self.rewrite_statements(&block.data().statements);
                    let rewritten = self.node(block.range(), Block { statements });
                    members.push(self.node(member.range(), ClassMember::StaticBlock(rewritten)));
                }
                ClassMember::StaticBlock(block) => {
                    let statements = self.rewrite_statements(&block.data().statements);
                    static_steps.push(StaticStep::Block(
                        self.node(block.range(), Block { statements }),
                    ));
                }
                ClassMember::IndexSignature(_) | ClassMember::Missing(_) => {
                    members.push(member.clone());
                }
            }
        }
        debug_assert!(
            !has_computed || class.extends.is_none() || !prelude.is_empty(),
            "heritage must be captured before computed keys"
        );
        if matches!(mode, FieldMode::Native) {
            if let Some(ctor) = constructor {
                members.insert(0, ctor);
            }
        } else if let Some(ctor) =
            self.lower_constructor(constructor, &instance, class.extends.is_some(), range, mode)
        {
            members.insert(0, ctor);
        }
        class.members = members;
        let mut postlude = Vec::new();
        if !matches!(mode, FieldMode::Native)
            && let Some(name) = static_target.or(class.name.as_ref())
        {
            for step in static_steps {
                postlude.push(match step {
                    StaticStep::Field(mut field) => {
                        field.init = self.substitute_static_expr(&field.init, name);
                        self.field_statement(Some(name), &field, mode)
                    }
                    StaticStep::Block(block) => {
                        let block = self.substitute_static_block(&block, name);
                        self.static_block_statement(block, range)
                    }
                });
            }
        }
        ClassLowering {
            class,
            prelude,
            postlude,
        }
    }

    fn lower_class_member_name(
        &mut self,
        name: &PropertyName,
        prelude: &mut Vec<Stmt>,
        range: TextRange,
    ) -> PropertyName {
        let PropertyName::Computed(expression) = name else {
            return name.clone();
        };
        let temp = self.temp_ident();
        let value = self.rewrite_expr(expression);
        prelude.push(self.make_temp_declaration(temp.clone(), value, range));
        PropertyName::Computed(Box::new(
            self.node(temp.range(), Expression::Identifier(temp)),
        ))
    }

    fn rewrite_property_name(&mut self, name: &PropertyName) -> PropertyName {
        match name {
            PropertyName::Computed(value) => {
                PropertyName::Computed(Box::new(self.rewrite_expr(value)))
            }
            other => other.clone(),
        }
    }

    fn make_temp_declaration(
        &mut self,
        temp: IdentifierNode,
        value: Expr,
        range: TextRange,
    ) -> Stmt {
        let declaration = self.make_declarator(temp, Some(value), range);
        self.syn_node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                // Temps can land inside machine bodies that clone
                // verbatim; `let` there is a SyntaxError at ES5, but
                // ES2015+ targets keep the tighter binding.
                kind: if self.options.target >= ScriptTarget::Es2015 {
                    VariableKind::Let
                } else {
                    VariableKind::Var
                },
                declarations: vec![declaration],
            }),
        )
    }

    fn lower_constructor(
        &mut self,
        constructor: Option<ClassMemberNode>,
        fields: &[FieldInit],
        derived: bool,
        range: TextRange,
        mode: FieldMode,
    ) -> Option<ClassMemberNode> {
        if fields.is_empty() && constructor.is_none() {
            return None;
        }
        let inits: Vec<Stmt> = fields
            .iter()
            .map(|field| self.field_statement(None, field, mode))
            .collect();
        match constructor {
            Some(existing) => {
                let ClassMember::Constructor(ctor) = existing.data() else {
                    unreachable!("constructor slot must contain constructor");
                };
                let original_len = ctor.body.data().statements.len();
                let inits_empty = inits.is_empty();
                let statements = if derived {
                    self.splice_after_super(&ctor.body.data().statements, &inits)
                } else {
                    let mut statements = inits;
                    statements.extend(ctor.body.data().statements.clone());
                    statements
                };
                // A body carrying no field inits and no spliced statements
                // is authored content: keep the wrapper untainted (original
                // id space) so the empty-body layout gate can read its
                // authored lines (ParameterList6 keeps `constructor(C) {\n}`).
                // Any synthesized content keeps the tainted mint.
                let body = if inits_empty && statements.len() == original_len {
                    self.node(ctor.body.range(), Block { statements })
                } else {
                    self.syn_node(ctor.body.range(), Block { statements })
                };
                Some(self.syn_node(
                    existing.range(),
                    ClassMember::Constructor(ConstructorDeclaration {
                        body,
                        ..ctor.clone()
                    }),
                ))
            }
            None => {
                let mut statements = Vec::new();
                if derived {
                    statements.push(self.super_forward_call(range));
                }
                statements.extend(inits);
                let body = self.syn_node(range, Block { statements });
                Some(self.syn_node(
                    range,
                    ClassMember::Constructor(ConstructorDeclaration {
                        decorators: Vec::new(),
                        modifiers: DeclarationModifiers::default(),
                        parameters: Vec::new(),
                        body,
                    }),
                ))
            }
        }
    }

    fn splice_after_super(&mut self, statements: &[Stmt], inits: &[Stmt]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for statement in statements {
            match statement.data() {
                Statement::Expression(expr) if is_super_call_expression(&expr.expression) => {
                    out.push(statement.clone());
                    out.extend(inits.iter().cloned());
                }
                Statement::Block(block) => {
                    let statements = self.splice_after_super(&block.data().statements, inits);
                    let child_marked = self.any_marked(statements.iter().map(|s| s.id()));
                    let block = self.wrap_marked(block.range(), Block { statements }, child_marked);
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Block(block),
                        child_marked,
                    ));
                }
                Statement::If(if_stmt) => {
                    let consequent = self.splice_super_statement(&if_stmt.consequent, inits);
                    let alternate = if_stmt
                        .alternate
                        .as_deref()
                        .map(|value| Box::new(self.splice_super_statement(value, inits)));
                    let child_marked = self.any_marked(
                        [consequent.id()]
                            .into_iter()
                            .chain(alternate.iter().map(|a| a.id())),
                    );
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::If(IfStatement {
                            test: if_stmt.test.clone(),
                            consequent: Box::new(consequent),
                            alternate,
                        }),
                        child_marked,
                    ));
                }
                Statement::Try(try_stmt) => {
                    let statements =
                        self.splice_after_super(&try_stmt.block.data().statements, inits);
                    let block_marked = self.any_marked(statements.iter().map(|s| s.id()));
                    let block = self.wrap_marked(
                        try_stmt.block.range(),
                        Block { statements },
                        block_marked,
                    );
                    let handler = try_stmt.handler.as_ref().map(|handler| {
                        let statements =
                            self.splice_after_super(&handler.data().body.data().statements, inits);
                        let body_marked = self.any_marked(statements.iter().map(|s| s.id()));
                        let body = self.wrap_marked(
                            handler.data().body.range(),
                            Block { statements },
                            body_marked,
                        );
                        let handler_marked = body_marked;
                        self.wrap_marked(
                            handler.range(),
                            CatchClause {
                                binding: handler.data().binding.clone(),
                                body,
                            },
                            handler_marked,
                        )
                    });
                    let finalizer = try_stmt.finalizer.as_ref().map(|block| {
                        let statements = self.splice_after_super(&block.data().statements, inits);
                        let marked = self.any_marked(statements.iter().map(|s| s.id()));
                        self.wrap_marked(block.range(), Block { statements }, marked)
                    });
                    let child_marked = block_marked
                        || handler
                            .as_ref()
                            .is_some_and(|h| self.synthesized_ids.contains(&h.id()))
                        || finalizer
                            .as_ref()
                            .is_some_and(|f| self.synthesized_ids.contains(&f.id()));
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Try(TryStatement {
                            block,
                            handler,
                            finalizer,
                        }),
                        child_marked,
                    ));
                }
                Statement::For(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::For(ForStatement {
                            body: Box::new(body),
                            ..value.clone()
                        }),
                        child_marked,
                    ));
                }
                Statement::ForIn(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::ForIn(ForInStatement {
                            body: Box::new(body),
                            ..value.clone()
                        }),
                        child_marked,
                    ));
                }
                Statement::ForOf(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::ForOf(ForOfStatement {
                            body: Box::new(body),
                            ..value.clone()
                        }),
                        child_marked,
                    ));
                }
                Statement::While(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::While(WhileStatement {
                            body: Box::new(body),
                            ..value.clone()
                        }),
                        child_marked,
                    ));
                }
                Statement::DoWhile(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::DoWhile(DoWhileStatement {
                            body: Box::new(body),
                            ..value.clone()
                        }),
                        child_marked,
                    ));
                }
                Statement::Labeled(value) => {
                    let body = self.splice_super_statement(&value.body, inits);
                    let child_marked = self.synthesized_ids.contains(&body.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Labeled(LabeledStatement {
                            label: value.label.clone(),
                            body: Box::new(body),
                        }),
                        child_marked,
                    ));
                }
                Statement::Switch(value) => {
                    let cases = value
                        .cases
                        .iter()
                        .map(|case| {
                            let consequent =
                                self.splice_after_super(&case.data().consequent, inits);
                            let child_marked = self.any_marked(consequent.iter().map(|s| s.id()));
                            self.wrap_marked(
                                case.range(),
                                SwitchCase {
                                    test: case.data().test.clone(),
                                    consequent,
                                },
                                child_marked,
                            )
                        })
                        .collect::<Vec<_>>();
                    let child_marked = self.any_marked(cases.iter().map(|c| c.id()));
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Switch(SwitchStatement {
                            discriminant: value.discriminant.clone(),
                            cases,
                        }),
                        child_marked,
                    ));
                }
                Statement::Expression(value) => {
                    let expression = self.wrap_super_calls(&value.expression, inits);
                    let child_marked = self.synthesized_ids.contains(&expression.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Expression(ExpressionStatement {
                            expression: Box::new(expression),
                        }),
                        child_marked,
                    ));
                }
                Statement::Return(value) => {
                    let argument = value
                        .argument
                        .as_deref()
                        .map(|value| Box::new(self.wrap_super_calls(value, inits)));
                    let child_marked = argument
                        .as_ref()
                        .is_some_and(|a| self.synthesized_ids.contains(&a.id()));
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Return(ReturnStatement { argument }),
                        child_marked,
                    ));
                }
                Statement::Throw(value) => {
                    let argument = self.wrap_super_calls(&value.argument, inits);
                    let child_marked = self.synthesized_ids.contains(&argument.id());
                    out.push(self.wrap_marked(
                        statement.range(),
                        Statement::Throw(ThrowStatement {
                            argument: Box::new(argument),
                        }),
                        child_marked,
                    ));
                }
                _ => out.push(statement.clone()),
            }
        }
        out
    }

    fn wrap_super_calls(&mut self, expression: &Expr, inits: &[Stmt]) -> Expr {
        if is_super_call_expression(expression) {
            let mut expressions = vec![expression.clone()];
            expressions.extend(inits.iter().filter_map(|statement| {
                let Statement::Expression(value) = statement.data() else {
                    return None;
                };
                Some(value.expression.as_ref().clone())
            }));
            expressions.push(self.syn_node(expression.range(), Expression::This));
            return self.syn_node(
                expression.range(),
                Expression::Sequence(SequenceExpression { expressions }),
            );
        }
        match expression.data() {
            Expression::Call(call) => {
                let callee = self.wrap_super_calls(&call.callee, inits);
                let arguments = call
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        CallArgument::Expression(value) => {
                            CallArgument::Expression(Box::new(self.wrap_super_calls(value, inits)))
                        }
                        CallArgument::Spread(spread) => CallArgument::Spread(SpreadElement {
                            argument: Box::new(self.wrap_super_calls(&spread.argument, inits)),
                        }),
                        CallArgument::Missing(missing) => CallArgument::Missing(missing.clone()),
                    })
                    .collect();
                self.node(
                    expression.range(),
                    Expression::Call(CallExpression {
                        callee: Box::new(callee),
                        optional: call.optional,
                        type_arguments: call.type_arguments.clone(),
                        arguments,
                    }),
                )
            }
            Expression::Conditional(value) => {
                let test = self.wrap_super_calls(&value.test, inits);
                let consequent = self.wrap_super_calls(&value.consequent, inits);
                let alternate = self.wrap_super_calls(&value.alternate, inits);
                self.node(
                    expression.range(),
                    Expression::Conditional(ConditionalExpression {
                        test: Box::new(test),
                        consequent: Box::new(consequent),
                        alternate: Box::new(alternate),
                    }),
                )
            }
            Expression::Binary(value) => {
                let left = self.wrap_super_calls(&value.left, inits);
                let right = self.wrap_super_calls(&value.right, inits);
                self.node(
                    expression.range(),
                    Expression::Binary(BinaryExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Logical(value) => {
                let left = self.wrap_super_calls(&value.left, inits);
                let right = self.wrap_super_calls(&value.right, inits);
                self.node(
                    expression.range(),
                    Expression::Logical(LogicalExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Sequence(value) => {
                let expressions = value
                    .expressions
                    .iter()
                    .map(|value| self.wrap_super_calls(value, inits))
                    .collect();
                self.node(
                    expression.range(),
                    Expression::Sequence(SequenceExpression { expressions }),
                )
            }
            Expression::Parenthesized(value) => {
                let value = self.wrap_super_calls(value, inits);
                self.node(
                    expression.range(),
                    Expression::Parenthesized(Box::new(value)),
                )
            }
            Expression::Assignment(value) => {
                let right = self.wrap_super_calls(&value.right, inits);
                self.node(
                    expression.range(),
                    Expression::Assignment(AssignmentExpression {
                        right: Box::new(right),
                        ..value.clone()
                    }),
                )
            }
            Expression::Arrow(arrow) => {
                let body = match &arrow.body {
                    FunctionBody::Expression(value) => {
                        FunctionBody::Expression(Box::new(self.wrap_super_calls(value, inits)))
                    }
                    FunctionBody::Block(block) => {
                        let statements = self.splice_after_super(&block.data().statements, inits);
                        FunctionBody::Block(self.node(block.range(), Block { statements }))
                    }
                    FunctionBody::Missing(missing) => FunctionBody::Missing(missing.clone()),
                };
                self.node(
                    expression.range(),
                    Expression::Arrow(ArrowFunction {
                        body,
                        ..arrow.clone()
                    }),
                )
            }
            Expression::Function(_) | Expression::Class(_) => expression.clone(),
            _ => expression.clone(),
        }
    }
    fn splice_super_statement(&mut self, statement: &Stmt, inits: &[Stmt]) -> Stmt {
        let statements = self.splice_after_super(std::slice::from_ref(statement), inits);
        if statements.len() == 1 {
            return statements.into_iter().next().expect("one statement");
        }
        let child_marked = self.any_marked(statements.iter().map(|s| s.id()));
        let block = self.wrap_marked(statement.range(), Block { statements }, child_marked);
        self.wrap_marked(statement.range(), Statement::Block(block), child_marked)
    }

    fn field_statement(
        &mut self,
        class_name: Option<&IdentifierNode>,
        field: &FieldInit,
        mode: FieldMode,
    ) -> Stmt {
        if matches!(mode, FieldMode::Define) {
            return self.define_field_statement(class_name, field);
        }
        let object = match class_name {
            Some(name) => self.syn_node(name.range(), Expression::Identifier(name.clone())),
            None => self.syn_node(field.range, Expression::This),
        };
        let property = self.member_property(&field.name, field.range);
        let target = self.syn_node(
            field.range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        );
        let assignment = self.syn_node(
            field.range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: target,
                right: Box::new(field.init.clone()),
            }),
        );
        self.syn_node(
            field.range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assignment),
            }),
        )
    }

    fn define_field_statement(
        &mut self,
        class_name: Option<&IdentifierNode>,
        field: &FieldInit,
    ) -> Stmt {
        let object = self.ident("Object");
        let callee = self.member_ident(&object, "defineProperty", field.range);
        let receiver = match class_name {
            Some(name) => self.syn_node(name.range(), Expression::Identifier(name.clone())),
            None => self.syn_node(field.range, Expression::This),
        };
        let key = self.property_key_expression(&field.name, field.range);
        let enumerable = self.boolean_expr(true);
        let configurable = self.boolean_expr(true);
        let writable = self.boolean_expr(true);
        let descriptor = self.object_literal(
            vec![
                ("enumerable", enumerable),
                ("configurable", configurable),
                ("writable", writable),
                ("value", field.init.clone()),
            ],
            field.range,
        );
        let call = self.syn_node(
            field.range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(receiver)),
                    CallArgument::Expression(Box::new(key)),
                    CallArgument::Expression(Box::new(descriptor)),
                ],
            }),
        );
        self.syn_node(
            field.range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    fn member_property(&mut self, name: &PropertyName, range: TextRange) -> MemberProperty {
        match name {
            PropertyName::Identifier(name) => MemberProperty::Named(name.clone()),
            PropertyName::Private(name) => MemberProperty::Private(name.clone()),
            PropertyName::Computed(value) => MemberProperty::Computed(value.clone()),
            PropertyName::String(value) => MemberProperty::Computed(Box::new(self.node(
                value.range(),
                Expression::Literal(Literal::String(value.clone())),
            ))),
            PropertyName::Number(value) => MemberProperty::Computed(Box::new(self.node(
                value.range(),
                Expression::Literal(Literal::Number(value.clone())),
            ))),
            PropertyName::Missing(_) => MemberProperty::Computed(Box::new(self.void_zero(range))),
        }
    }

    fn property_key_expression(&mut self, name: &PropertyName, range: TextRange) -> Expr {
        match name {
            PropertyName::Identifier(name) => {
                let (source, _, _) = self.finish_source().expect("synthetic source");
                let range = name.data().token().range();
                let start = source
                    .utf16_to_byte(range.start())
                    .expect("identifier start is a source boundary");
                let end = source
                    .utf16_to_byte(range.end())
                    .expect("identifier end is a source boundary");
                let text = source.as_str()[start..end].to_owned();
                let literal = self.string_literal(&text);
                self.node(
                    literal.range(),
                    Expression::Literal(Literal::String(literal)),
                )
            }
            PropertyName::Private(_) => self.void_zero(range),
            PropertyName::Computed(value) => value.as_ref().clone(),
            PropertyName::String(value) => self.node(
                value.range(),
                Expression::Literal(Literal::String(value.clone())),
            ),
            PropertyName::Number(value) => self.node(
                value.range(),
                Expression::Literal(Literal::Number(value.clone())),
            ),
            PropertyName::Missing(_) => self.void_zero(range),
        }
    }

    /// Builds a wholly synthesized object literal. Every mint records in the
    /// taint set: the printer's single-line object gate keys on it, and an
    /// untainted descriptor collapsed `Object.defineProperty(this, "foo",
    /// { ... })` onto one line where tsc expands (override18 regression).
    fn object_literal(&mut self, entries: Vec<(&str, Expr)>, range: TextRange) -> Expr {
        let mut members = Vec::new();
        for (name, value) in entries {
            let property = ObjectProperty {
                name: PropertyName::Identifier(self.ident(name)),
                value: Box::new(value),
                modifier: PropertyModifier::None,
                shorthand: false,
            };
            members.push(self.syn_node(range, ObjectMember::Property(property)));
        }
        self.syn_node(range, Expression::Object(ObjectLiteral { members }))
    }

    fn substitute_static_block(
        &mut self,
        block: &BlockNode,
        class_name: &IdentifierNode,
    ) -> BlockNode {
        let statements = block
            .data()
            .statements
            .iter()
            .map(|statement| self.substitute_static_statement(statement, class_name))
            .collect();
        self.node(block.range(), Block { statements })
    }

    fn substitute_static_statement(
        &mut self,
        statement: &Stmt,
        class_name: &IdentifierNode,
    ) -> Stmt {
        match statement.data() {
            Statement::Expression(value) => {
                let expression = self.substitute_static_expr(&value.expression, class_name);
                self.node(
                    statement.range(),
                    Statement::Expression(ExpressionStatement {
                        expression: Box::new(expression),
                    }),
                )
            }
            Statement::Return(value) => {
                let argument = value.argument.as_deref().map(|expression| {
                    Box::new(self.substitute_static_expr(expression, class_name))
                });
                self.node(
                    statement.range(),
                    Statement::Return(ReturnStatement { argument }),
                )
            }
            Statement::Throw(value) => {
                let argument = self.substitute_static_expr(&value.argument, class_name);
                self.node(
                    statement.range(),
                    Statement::Throw(ThrowStatement {
                        argument: Box::new(argument),
                    }),
                )
            }
            Statement::Variable(value) => {
                let declarations = value
                    .declarations
                    .iter()
                    .map(|declaration| {
                        let initializer =
                            declaration.data().initializer.as_deref().map(|value| {
                                Box::new(self.substitute_static_expr(value, class_name))
                            });
                        self.node(
                            declaration.range(),
                            VariableDeclarator {
                                initializer,
                                ..declaration.data().clone()
                            },
                        )
                    })
                    .collect();
                self.node(
                    statement.range(),
                    Statement::Variable(VariableDeclaration {
                        declarations,
                        ..value.clone()
                    }),
                )
            }
            Statement::Block(block) => {
                let block = self.substitute_static_block(block, class_name);
                self.node(statement.range(), Statement::Block(block))
            }
            Statement::If(value) => {
                let test = self.substitute_static_expr(&value.test, class_name);
                let consequent = self.substitute_static_statement(&value.consequent, class_name);
                let alternate = value
                    .alternate
                    .as_deref()
                    .map(|value| Box::new(self.substitute_static_statement(value, class_name)));
                self.node(
                    statement.range(),
                    Statement::If(IfStatement {
                        test: Box::new(test),
                        consequent: Box::new(consequent),
                        alternate,
                    }),
                )
            }
            Statement::While(value) => {
                let test = self.substitute_static_expr(&value.test, class_name);
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::While(WhileStatement {
                        test: Box::new(test),
                        body: Box::new(body),
                    }),
                )
            }
            Statement::DoWhile(value) => {
                let body = self.substitute_static_statement(&value.body, class_name);
                let test = self.substitute_static_expr(&value.test, class_name);
                self.node(
                    statement.range(),
                    Statement::DoWhile(DoWhileStatement {
                        body: Box::new(body),
                        test: Box::new(test),
                    }),
                )
            }
            Statement::For(value) => {
                let initializer = value
                    .initializer
                    .as_ref()
                    .map(|initializer| match initializer {
                        ForInitializer::Expression(value) => ForInitializer::Expression(Box::new(
                            self.substitute_static_expr(value, class_name),
                        )),
                        ForInitializer::Variable(value) => ForInitializer::Variable(value.clone()),
                    });
                let test = value
                    .test
                    .as_deref()
                    .map(|value| Box::new(self.substitute_static_expr(value, class_name)));
                let update = value
                    .update
                    .as_deref()
                    .map(|value| Box::new(self.substitute_static_expr(value, class_name)));
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::For(ForStatement {
                        initializer,
                        test,
                        update,
                        body: Box::new(body),
                    }),
                )
            }
            Statement::ForIn(value) => {
                let object = self.substitute_static_expr(&value.object, class_name);
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::ForIn(ForInStatement {
                        object: Box::new(object),
                        body: Box::new(body),
                        ..value.clone()
                    }),
                )
            }
            Statement::ForOf(value) => {
                let iterable = self.substitute_static_expr(&value.iterable, class_name);
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::ForOf(ForOfStatement {
                        iterable: Box::new(iterable),
                        body: Box::new(body),
                        ..value.clone()
                    }),
                )
            }
            Statement::Labeled(value) => {
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::Labeled(LabeledStatement {
                        label: value.label.clone(),
                        body: Box::new(body),
                    }),
                )
            }
            Statement::Switch(value) => {
                let discriminant = self.substitute_static_expr(&value.discriminant, class_name);
                let cases = value
                    .cases
                    .iter()
                    .map(|case| {
                        let test =
                            case.data().test.as_deref().map(|value| {
                                Box::new(self.substitute_static_expr(value, class_name))
                            });
                        let consequent = case
                            .data()
                            .consequent
                            .iter()
                            .map(|value| self.substitute_static_statement(value, class_name))
                            .collect();
                        self.node(case.range(), SwitchCase { test, consequent })
                    })
                    .collect();
                self.node(
                    statement.range(),
                    Statement::Switch(SwitchStatement {
                        discriminant: Box::new(discriminant),
                        cases,
                    }),
                )
            }
            Statement::Try(value) => {
                let block = self.substitute_static_block(&value.block, class_name);
                let handler = value.handler.as_ref().map(|handler| {
                    let body = self.substitute_static_block(&handler.data().body, class_name);
                    self.node(
                        handler.range(),
                        CatchClause {
                            binding: handler.data().binding.clone(),
                            body,
                        },
                    )
                });
                let finalizer = value
                    .finalizer
                    .as_ref()
                    .map(|block| self.substitute_static_block(block, class_name));
                self.node(
                    statement.range(),
                    Statement::Try(TryStatement {
                        block,
                        handler,
                        finalizer,
                    }),
                )
            }
            Statement::With(value) => {
                let object = self.substitute_static_expr(&value.object, class_name);
                let body = self.substitute_static_statement(&value.body, class_name);
                self.node(
                    statement.range(),
                    Statement::With(WithStatement {
                        object: Box::new(object),
                        body: Box::new(body),
                    }),
                )
            }
            Statement::Function(_) | Statement::Class(_) => statement.clone(),
            Statement::Import(_)
            | Statement::ImportEquals(_)
            | Statement::Export(_)
            | Statement::Interface(_)
            | Statement::TypeAlias(_)
            | Statement::Enum(_)
            | Statement::Namespace(_)
            | Statement::Declare(_)
            | Statement::Empty
            | Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Debugger
            | Statement::Missing(_) => statement.clone(),
        }
    }

    fn substitute_static_expr(&mut self, expression: &Expr, class_name: &IdentifierNode) -> Expr {
        match expression.data() {
            Expression::This => self.node(
                class_name.range(),
                Expression::Identifier(class_name.clone()),
            ),
            Expression::Member(member) if matches!(member.object.data(), Expression::Super) => {
                self.static_super_get(&member.property, class_name, expression.range())
            }
            Expression::Call(call)
                if matches!(
                    call.callee.data(),
                    Expression::Member(MemberExpression { object, .. })
                        if matches!(object.data(), Expression::Super)
                ) =>
            {
                let Expression::Member(member) = call.callee.data() else {
                    unreachable!("guarded super member");
                };
                let get = self.static_super_get(&member.property, class_name, expression.range());
                let call_name = self.ident("call");
                let callee = self.node(
                    expression.range(),
                    Expression::Member(MemberExpression {
                        object: Box::new(get),
                        property: MemberProperty::Named(call_name),
                        optional: false,
                    }),
                );
                let receiver = self.node(
                    class_name.range(),
                    Expression::Identifier(class_name.clone()),
                );
                let mut arguments = vec![CallArgument::Expression(Box::new(receiver))];
                arguments.extend(call.arguments.iter().map(|argument| match argument {
                    CallArgument::Expression(value) => CallArgument::Expression(Box::new(
                        self.substitute_static_expr(value, class_name),
                    )),
                    CallArgument::Spread(spread) => CallArgument::Spread(SpreadElement {
                        argument: Box::new(
                            self.substitute_static_expr(&spread.argument, class_name),
                        ),
                    }),
                    CallArgument::Missing(missing) => CallArgument::Missing(missing.clone()),
                }));
                self.node(
                    expression.range(),
                    Expression::Call(CallExpression {
                        callee: Box::new(callee),
                        optional: false,
                        type_arguments: None,
                        arguments,
                    }),
                )
            }
            Expression::Call(call) => {
                let callee = self.substitute_static_expr(&call.callee, class_name);
                let arguments = call
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        CallArgument::Expression(value) => CallArgument::Expression(Box::new(
                            self.substitute_static_expr(value, class_name),
                        )),
                        CallArgument::Spread(spread) => CallArgument::Spread(SpreadElement {
                            argument: Box::new(
                                self.substitute_static_expr(&spread.argument, class_name),
                            ),
                        }),
                        CallArgument::Missing(missing) => CallArgument::Missing(missing.clone()),
                    })
                    .collect();
                self.node(
                    expression.range(),
                    Expression::Call(CallExpression {
                        callee: Box::new(callee),
                        optional: call.optional,
                        type_arguments: call.type_arguments.clone(),
                        arguments,
                    }),
                )
            }
            Expression::Member(member) => {
                let object = self.substitute_static_expr(&member.object, class_name);
                let property = match &member.property {
                    MemberProperty::Computed(value) => MemberProperty::Computed(Box::new(
                        self.substitute_static_expr(value, class_name),
                    )),
                    other => other.clone(),
                };
                self.node(
                    expression.range(),
                    Expression::Member(MemberExpression {
                        object: Box::new(object),
                        property,
                        optional: member.optional,
                    }),
                )
            }
            Expression::Binary(value) => {
                let left = self.substitute_static_expr(&value.left, class_name);
                let right = self.substitute_static_expr(&value.right, class_name);
                self.node(
                    expression.range(),
                    Expression::Binary(BinaryExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Logical(value) => {
                let left = self.substitute_static_expr(&value.left, class_name);
                let right = self.substitute_static_expr(&value.right, class_name);
                self.node(
                    expression.range(),
                    Expression::Logical(LogicalExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Conditional(value) => {
                let test = self.substitute_static_expr(&value.test, class_name);
                let consequent = self.substitute_static_expr(&value.consequent, class_name);
                let alternate = self.substitute_static_expr(&value.alternate, class_name);
                self.node(
                    expression.range(),
                    Expression::Conditional(ConditionalExpression {
                        test: Box::new(test),
                        consequent: Box::new(consequent),
                        alternate: Box::new(alternate),
                    }),
                )
            }
            Expression::Assignment(value)
                if matches!(
                    value.left.data(),
                    AssignmentTarget::Member(AssignmentMemberTarget { object, .. })
                        if matches!(object.data(), Expression::Super)
                ) =>
            {
                let AssignmentTarget::Member(member) = value.left.data() else {
                    unreachable!("guarded static super assignment");
                };
                self.static_super_set(
                    &member.property,
                    value.operator,
                    &value.right,
                    class_name,
                    expression.range(),
                )
            }
            Expression::Assignment(value) => {
                let left = match value.left.data() {
                    AssignmentTarget::Member(member) => {
                        let object = self.substitute_static_expr(&member.object, class_name);
                        let property = match &member.property {
                            MemberProperty::Computed(value) => MemberProperty::Computed(Box::new(
                                self.substitute_static_expr(value, class_name),
                            )),
                            other => other.clone(),
                        };
                        self.node(
                            value.left.range(),
                            AssignmentTarget::Member(AssignmentMemberTarget {
                                object: Box::new(object),
                                property,
                            }),
                        )
                    }
                    _ => value.left.clone(),
                };
                let right = self.substitute_static_expr(&value.right, class_name);
                self.node(
                    expression.range(),
                    Expression::Assignment(AssignmentExpression {
                        operator: value.operator,
                        left,
                        right: Box::new(right),
                    }),
                )
            }
            _ => expression.clone(),
        }
    }

    fn static_super_set(
        &mut self,
        property: &MemberProperty,
        operator: AssignmentOperator,
        right: &Expr,
        class_name: &IdentifierNode,
        range: TextRange,
    ) -> Expr {
        let key_temp = self.temp_ident();
        let value_temp = self.temp_ident();
        let key = self.static_super_key(property, class_name, range);
        let key_statement = self.make_temp_declaration(key_temp.clone(), key, range);
        let key_reference = self.node(key_temp.range(), Expression::Identifier(key_temp.clone()));
        let temp_property = MemberProperty::Computed(Box::new(key_reference));
        let right = self.substitute_static_expr(right, class_name);
        let value = if operator == AssignmentOperator::Assign {
            right
        } else {
            let old = self.static_super_get(&temp_property, class_name, range);
            let binary_operator = match operator {
                AssignmentOperator::AddAssign => BinaryOperator::Add,
                AssignmentOperator::SubtractAssign => BinaryOperator::Subtract,
                AssignmentOperator::MultiplyAssign => BinaryOperator::Multiply,
                AssignmentOperator::DivideAssign => BinaryOperator::Divide,
                AssignmentOperator::RemainderAssign => BinaryOperator::Remainder,
                AssignmentOperator::ExponentiateAssign => BinaryOperator::Exponentiate,
                AssignmentOperator::LeftShiftAssign => BinaryOperator::LeftShift,
                AssignmentOperator::SignedRightShiftAssign => BinaryOperator::SignedRightShift,
                AssignmentOperator::UnsignedRightShiftAssign => BinaryOperator::UnsignedRightShift,
                AssignmentOperator::BitAndAssign => BinaryOperator::BitAnd,
                AssignmentOperator::BitXorAssign => BinaryOperator::BitXor,
                AssignmentOperator::BitOrAssign => BinaryOperator::BitOr,
                AssignmentOperator::LogicalAndAssign
                | AssignmentOperator::LogicalOrAssign
                | AssignmentOperator::NullishAssign
                | AssignmentOperator::Assign => {
                    return self.static_super_set(
                        property,
                        AssignmentOperator::Assign,
                        &right,
                        class_name,
                        range,
                    );
                }
            };
            self.node(
                range,
                Expression::Binary(BinaryExpression {
                    operator: binary_operator,
                    left: Box::new(old),
                    right: Box::new(right),
                }),
            )
        };
        let value_statement = self.make_temp_declaration(value_temp.clone(), value, range);
        let value_reference = self.node(
            value_temp.range(),
            Expression::Identifier(value_temp.clone()),
        );
        let set = self.static_super_reflect_set(
            temp_property,
            value_reference.clone(),
            class_name,
            range,
        );
        let set_statement = self.node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(set),
            }),
        );
        let return_statement = self.node(
            range,
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(value_reference)),
            }),
        );
        let body = self.node(
            range,
            Block {
                statements: vec![
                    key_statement,
                    value_statement,
                    set_statement,
                    return_statement,
                ],
            },
        );
        let arrow = self.node(
            range,
            Expression::Arrow(ArrowFunction {
                is_async: false,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: None,
                body: FunctionBody::Block(body),
            }),
        );
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(arrow),
                optional: false,
                type_arguments: None,
                arguments: Vec::new(),
            }),
        )
    }

    fn static_super_key(
        &mut self,
        property: &MemberProperty,
        class_name: &IdentifierNode,
        range: TextRange,
    ) -> Expr {
        match property {
            MemberProperty::Named(name) => {
                let (source, _, _) = self.finish_source().expect("synthetic source");
                let token_range = name.data().token().range();
                let start = source
                    .utf16_to_byte(token_range.start())
                    .expect("name start");
                let end = source.utf16_to_byte(token_range.end()).expect("name end");
                let text = source.as_str()[start..end].to_owned();
                let literal = self.string_literal(&text);
                self.node(
                    literal.range(),
                    Expression::Literal(Literal::String(literal)),
                )
            }
            MemberProperty::Private(_) => self.void_zero(range),
            MemberProperty::Computed(value) => self.substitute_static_expr(value, class_name),
        }
    }

    fn static_super_reflect_set(
        &mut self,
        property: MemberProperty,
        value: Expr,
        class_name: &IdentifierNode,
        range: TextRange,
    ) -> Expr {
        let object = self.ident("Object");
        let get_proto = self.member_ident(&object, "getPrototypeOf", range);
        let class = self.node(
            class_name.range(),
            Expression::Identifier(class_name.clone()),
        );
        let proto = self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(get_proto),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(class.clone()))],
            }),
        );
        let key = match property {
            MemberProperty::Named(_name) => {
                let literal = self.string_literal("name");
                self.node(
                    literal.range(),
                    Expression::Literal(Literal::String(literal)),
                )
            }
            MemberProperty::Private(_) => self.void_zero(range),
            MemberProperty::Computed(value) => value.as_ref().clone(),
        };
        let reflect = self.ident("Reflect");
        let set = self.member_ident(&reflect, "set", range);
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(set),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(proto)),
                    CallArgument::Expression(Box::new(key)),
                    CallArgument::Expression(Box::new(value)),
                    CallArgument::Expression(Box::new(class)),
                ],
            }),
        )
    }
    fn static_super_get(
        &mut self,
        property: &MemberProperty,
        class_name: &IdentifierNode,
        range: TextRange,
    ) -> Expr {
        let object = self.ident("Object");
        let get_proto = self.member_ident(&object, "getPrototypeOf", range);
        let class = self.node(
            class_name.range(),
            Expression::Identifier(class_name.clone()),
        );
        let proto = self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(get_proto),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(class.clone()))],
            }),
        );
        let key = match property {
            MemberProperty::Named(name) => {
                let (source, _, _) = self.finish_source().expect("synthetic source");
                let token_range = name.data().token().range();
                let start = source
                    .utf16_to_byte(token_range.start())
                    .expect("name start");
                let end = source.utf16_to_byte(token_range.end()).expect("name end");
                let text = source.as_str()[start..end].to_owned();
                let literal = self.string_literal(&text);
                self.node(
                    literal.range(),
                    Expression::Literal(Literal::String(literal)),
                )
            }
            MemberProperty::Private(_) => self.void_zero(range),
            MemberProperty::Computed(value) => self.substitute_static_expr(value, class_name),
        };
        let reflect = self.ident("Reflect");
        let get = self.member_ident(&reflect, "get", range);
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(get),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(proto)),
                    CallArgument::Expression(Box::new(key)),
                    CallArgument::Expression(Box::new(class)),
                ],
            }),
        )
    }
    fn static_block_statement(&mut self, block: BlockNode, range: TextRange) -> Stmt {
        let arrow = self.syn_node(
            range,
            Expression::Arrow(ArrowFunction {
                is_async: false,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: None,
                body: FunctionBody::Block(block),
            }),
        );
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(arrow),
                optional: false,
                type_arguments: None,
                arguments: Vec::new(),
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    fn restore_default_class_name(
        &mut self,
        class_name: &IdentifierNode,
        range: TextRange,
    ) -> Stmt {
        self.restore_class_name(class_name, "default", range)
    }

    fn restore_class_name(
        &mut self,
        class_name: &IdentifierNode,
        value: &str,
        range: TextRange,
    ) -> Stmt {
        let object = self.ident("Object");
        let callee = self.member_ident(&object, "defineProperty", range);
        let receiver = self.syn_node(
            class_name.range(),
            Expression::Identifier(class_name.clone()),
        );
        let key_literal = self.string_literal("name");
        let key = self.syn_node(
            key_literal.range(),
            Expression::Literal(Literal::String(key_literal)),
        );
        let value_literal = self.string_literal(value);
        let value = self.syn_node(
            value_literal.range(),
            Expression::Literal(Literal::String(value_literal)),
        );
        let configurable = self.boolean_expr(true);
        let descriptor = self.object_literal(
            vec![("value", value), ("configurable", configurable)],
            range,
        );
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(receiver)),
                    CallArgument::Expression(Box::new(key)),
                    CallArgument::Expression(Box::new(descriptor)),
                ],
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    fn super_forward_call(&mut self, range: TextRange) -> Stmt {
        let arguments = self.ident_expr("arguments");
        let callee = self.syn_node(range, Expression::Super);
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Spread(SpreadElement {
                    argument: Box::new(arguments),
                })],
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    fn rewrite_function_like(&mut self, function: &FunctionLike, range: TextRange) -> FunctionLike {
        let parameters = self.rewrite_parameters(&function.parameters);
        if function.is_async && Self::needs(LanguageFeature::AsyncFunctions, self.options) {
            let mut rewritten = function.clone();
            rewritten.parameters = parameters;
            return self.lower_async_function(&rewritten, range);
        }
        let body = function.body.as_ref().map(|body| self.rewrite_body(body));
        let mut rewritten = FunctionLike {
            parameters,
            body,
            ..function.clone()
        };
        if rewritten.is_generator && Self::needs(LanguageFeature::Generators, self.options) {
            let lowered = self.lower_generator_function(&rewritten);
            if lowered.is_generator {
                self.diag(
                    codes::GENERATOR_REQUIRES_ES2015,
                    range,
                    "generators require ScriptTarget::Es2015 or later",
                );
            } else {
                rewritten = lowered;
            }
        }
        rewritten
    }

    fn rewrite_parameters(&mut self, parameters: &[ParameterNode]) -> Vec<ParameterNode> {
        parameters
            .iter()
            .map(|parameter| {
                let initializer = parameter.data().initializer.as_deref().map(|initializer| {
                    let depth = self.expression_temp_scopes.len();
                    self.parameter_initializer_depths.push(depth);
                    let rewritten = self.rewrite_expr(initializer);
                    let popped = self.parameter_initializer_depths.pop();
                    debug_assert_eq!(popped, Some(depth));
                    Box::new(rewritten)
                });
                self.node(
                    parameter.range(),
                    Parameter {
                        initializer,
                        ..parameter.data().clone()
                    },
                )
            })
            .collect()
    }

    fn rewrite_body(&mut self, body: &FunctionBody) -> FunctionBody {
        match body {
            FunctionBody::Block(block) => {
                self.expression_temp_scopes.push(Vec::new());
                let mut statements = self.rewrite_statements(&block.data().statements);
                let temps = self.expression_temp_scopes.pop().unwrap_or_default();
                let has_temps = !temps.is_empty();
                if let Some(declaration) = self.temp_declaration(temps, block.range()) {
                    statements.insert(0, declaration);
                }
                let block_node = if has_temps {
                    self.syn_node(block.range(), Block { statements })
                } else {
                    let child_marked = self.any_marked(statements.iter().map(|s| s.id()));
                    self.wrap_marked(block.range(), Block { statements }, child_marked)
                };
                FunctionBody::Block(block_node)
            }
            FunctionBody::Expression(expression) => {
                FunctionBody::Expression(Box::new(self.rewrite_expr(expression)))
            }
            FunctionBody::Missing(missing) => FunctionBody::Missing(missing.clone()),
        }
    }

    fn lower_async_function(&mut self, function: &FunctionLike, range: TextRange) -> FunctionLike {
        let previous = self.replace_await;
        self.replace_await = true;
        let inner_body = function
            .body
            .as_ref()
            .map(|body| self.rewrite_body(body))
            .unwrap_or_else(|| {
                FunctionBody::Block(self.syn_node(
                    range,
                    Block {
                        statements: Vec::new(),
                    },
                ))
            });
        self.replace_await = previous;
        let inner = FunctionLike {
            decorators: Vec::new(),
            name: None,
            is_async: false,
            is_generator: true,
            type_parameters: None,
            parameters: Vec::new(),
            return_type: None,
            body: Some(inner_body),
        };
        let inner = if Self::needs(LanguageFeature::Generators, self.options) {
            let lowered = self.lower_generator_function(&inner);
            if lowered.is_generator {
                // The machine declined; the inner stays a native generator
                // inside __awaiter, which the target cannot run. Signal it
                // instead of emitting ES2015+ syntax silently.
                self.diag(
                    codes::GENERATOR_REQUIRES_ES2015,
                    range,
                    "generators require ScriptTarget::Es2015 or later",
                );
            }
            lowered
        } else {
            inner
        };
        let inner_expr = self.syn_node(
            range,
            Expression::Function(FunctionExpression { function: inner }),
        );
        let awaiter = self.helper_ident(HelperKind::Awaiter);
        let this_arg = self.syn_node(range, Expression::This);
        let void_zero = self.void_zero(range);
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(awaiter),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(this_arg)),
                    CallArgument::Expression(Box::new(void_zero.clone())),
                    CallArgument::Expression(Box::new(void_zero)),
                    CallArgument::Expression(Box::new(inner_expr)),
                ],
            }),
        );
        let return_stmt = self.syn_node(
            range,
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(call)),
            }),
        );
        FunctionLike {
            is_async: false,
            is_generator: false,
            body: Some(FunctionBody::Block(self.syn_node(
                range,
                Block {
                    statements: vec![return_stmt],
                },
            ))),
            ..function.clone()
        }
    }

    fn void_zero(&mut self, range: TextRange) -> Expr {
        let zero = self.number_expr("0");
        self.node(
            range,
            Expression::Unary(UnaryExpression {
                operator: UnaryOperator::Void,
                argument: Box::new(zero),
            }),
        )
    }

    /// Lowers a generator body to a `__generator(this, function (_a) {...})`
    /// state machine for targets without native generators. Slice:
    /// statement-list bodies whose yields sit at statement level, or bodies
    /// with no yields at all; richer shapes keep the native generator (and
    /// the user path keeps its requires-es2015 diagnostic).
    fn lower_generator_function(&mut self, function: &FunctionLike) -> FunctionLike {
        let Some(FunctionBody::Block(block)) = function.body.as_ref() else {
            return function.clone();
        };
        let Some((hoisted, state_name, temps, machine)) = self.generator_machine(block) else {
            return function.clone();
        };
        let range = block.range();
        let state = self.ident(&state_name);
        let binding = self.node(state.range(), BindingPattern::Identifier(state));
        let parameter = self.node(
            binding.range(),
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers {
                    accessibility: None,
                    is_readonly: false,
                    is_override: false,
                },
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let machine_function = FunctionLike {
            decorators: Vec::new(),
            name: None,
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters: vec![parameter],
            return_type: None,
            body: Some(FunctionBody::Block(self.syn_node(
                range,
                Block {
                    statements: machine,
                },
            ))),
        };
        let machine_expr = self.syn_node(
            range,
            Expression::Function(FunctionExpression {
                function: machine_function,
            }),
        );
        let generator = self.helper_ident(HelperKind::Generator);
        let this_arg = self.syn_node(range, Expression::This);
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(generator),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(this_arg)),
                    CallArgument::Expression(Box::new(machine_expr)),
                ],
            }),
        );
        let return_stmt = self.syn_node(
            range,
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(call)),
            }),
        );
        let mut declarations = hoisted;
        declarations.extend(temps.iter().cloned());
        let mut statements = Vec::new();
        if let Some(declaration) = self.temp_declaration(declarations, range) {
            statements.push(declaration);
        }
        statements.push(return_stmt);
        FunctionLike {
            is_generator: false,
            body: Some(FunctionBody::Block(
                self.syn_node(range, Block { statements }),
            )),
            ..function.clone()
        }
    }

    fn generator_machine(&mut self, block: &BlockNode) -> Option<MachineParts> {
        // User var names join the skip set so machine temps and the state
        // parameter never collide with them. A probe pass with a throwaway
        // state name discovers the temp count; a second pass builds the
        // real tree with tsc's allocation: temps `_a`.. first, then the
        // state parameter after them.
        let mut skip = std::collections::HashSet::new();
        for statement in &block.data().statements {
            if let Statement::Variable(declaration) = statement.data() {
                for declarator in &declaration.declarations {
                    if let BindingPattern::Identifier(name) = declarator.data().binding.data()
                        && let Some(text) = self.identifier_name(name)
                    {
                        skip.insert(text);
                    }
                }
            }
        }
        let mut probe = MachineCtx::new("_m0s", skip.clone());
        self.machine_statements(block, &mut probe)?;
        let state = machine_state_name(&skip, &probe.temp_names);
        let mut ctx = MachineCtx::new(&state, skip);
        self.machine_statements(block, &mut ctx)?;
        debug_assert_eq!(ctx.temp_names.len(), probe.temp_names.len());
        let range = block.range();
        let hoisted = ctx.hoisted.clone();
        let temps = ctx.temps.clone();
        if ctx.segments.len() == 1 {
            return Some((hoisted, state, temps, ctx.segments.pop()?));
        }
        let state_expr = self.ident_expr(&state);
        let label_name = self.ident("label");
        let label = self.member_expr(&state_expr, MemberProperty::Named(label_name), range);
        let mut cases = Vec::new();
        for (index, segment) in ctx.segments.into_iter().enumerate() {
            let test = self.number_expr(&index.to_string());
            cases.push(self.node(
                range,
                SwitchCase {
                    test: Some(Box::new(test)),
                    consequent: segment,
                },
            ));
        }
        let switch = self.syn_node(
            range,
            Statement::Switch(SwitchStatement {
                discriminant: Box::new(label),
                cases,
            }),
        );
        Some((hoisted, state, temps, vec![switch]))
    }

    /// Rewrites the block's statements into machine segments. Evaluation
    /// order is preserved by materializing already-computed sibling values
    /// into temps before a suspending sibling splits the segment.
    fn machine_statements(&mut self, block: &BlockNode, ctx: &mut MachineCtx) -> Option<()> {
        if statements_contain_await(&block.data().statements) {
            // A leaked await means a conversion hole upstream; refusing
            // keeps the failure mode a wrong-but-valid generator instead
            // of `await` inside a plain function.
            return None;
        }
        let range = block.range();
        for statement in &block.data().statements {
            if ctx.terminated {
                return None;
            }
            match statement.data() {
                Statement::Variable(declaration) if declaration.kind == VariableKind::Var => {
                    for declarator in &declaration.declarations {
                        let BindingPattern::Identifier(name) = declarator.data().binding.data()
                        else {
                            return None;
                        };
                        let name = name.clone();
                        ctx.hoisted.push(name.clone());
                        if let Some(initializer) = &declarator.data().initializer {
                            let value = if contains_yield(initializer) {
                                self.eval(initializer, ctx)?
                            } else {
                                initializer.as_ref().clone()
                            };
                            let assign = self.assign_statement(&name, value, range);
                            ctx.push(assign);
                        }
                    }
                }
                Statement::Expression(expression) => {
                    // A comma sequence in statement position flattens: each
                    // element discards its value, so they become standalone
                    // statements in order.
                    if let Expression::Sequence(sequence) = expression.expression.data() {
                        for element in &sequence.expressions {
                            self.machine_emit_expression(element, ctx)?;
                        }
                    } else {
                        self.machine_emit_expression(&expression.expression, ctx)?;
                    }
                }
                Statement::If(if_statement) => {
                    self.machine_emit_if(statement, if_statement, ctx)?;
                }
                Statement::While(while_statement) => {
                    self.machine_emit_while(statement, while_statement, ctx)?;
                }
                Statement::DoWhile(do_statement) => {
                    self.machine_emit_do(statement, do_statement, ctx)?;
                }
                Statement::For(for_statement) => {
                    self.machine_emit_for(statement, for_statement, ctx)?;
                }
                Statement::Switch(switch_statement) => {
                    self.machine_emit_switch(statement, switch_statement, ctx)?;
                }
                Statement::Labeled(labeled) => {
                    let name = self.identifier_name(&labeled.label)?;
                    ctx.loop_labels.push(name);
                    let result = self.machine_emit_labeled(statement, &labeled.body, ctx);
                    ctx.loop_labels.pop();
                    result?;
                }

                Statement::Return(returned) => {
                    let terminator = match &returned.argument {
                        Some(value) if contains_yield(value) => {
                            let evaluated = self.eval(value, ctx)?;
                            let sentinel = self.number_expr("2 /*return*/");
                            let array = self.array_literal(vec![sentinel, evaluated], range);
                            self.machine_return(array, range)
                        }
                        Some(value) => {
                            let sentinel = self.number_expr("2 /*return*/");
                            let array =
                                self.array_literal(vec![sentinel, value.as_ref().clone()], range);
                            self.machine_return(array, range)
                        }
                        None => {
                            let sentinel = self.return_sentinel(range);
                            self.machine_return(sentinel, range)
                        }
                    };
                    ctx.push(terminator);
                    ctx.terminated = true;
                }
                _ => return None,
            }
        }
        if !ctx.terminated {
            let sentinel = self.return_sentinel(range);
            let ret = self.machine_return(sentinel, range);
            ctx.push(ret);
        }
        Some(())
    }

    /// Emits one expression as a statement, splitting any suspension.
    fn machine_emit_expression(&mut self, expression: &Expr, ctx: &mut MachineCtx) -> Option<()> {
        let range = expression.range();
        if !contains_yield(expression) {
            ctx.push(self.node(
                range,
                Statement::Expression(ExpressionStatement {
                    expression: Box::new(expression.clone()),
                }),
            ));
            return Some(());
        }
        let value = self.eval(expression, ctx)?;
        ctx.push(self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(value),
            }),
        ));
        Some(())
    }

    /// Lowers an if-statement into the machine. A test-only suspension
    /// reassembles inline with no labels; a suspending branch builds the
    /// labeled shape: a negated-test break to the else label, the
    /// consequent (splitting naturally), a break to the end label, the
    /// alternate under the else label, an explicit end-label assignment
    /// marking the join fallthrough, and the end label itself. Labels
    /// number positionally: consequent resumes, else, alternate resumes,
    /// end.
    fn machine_emit_if(
        &mut self,
        statement: &Stmt,
        if_statement: &IfStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let cons_block = block_statements(&if_statement.consequent)?;
        // A missing alternate is the empty else: fallthrough. Refusing
        // the whole generator over `if (c) { ... }` with no else clause
        // rejects one of the most common statement shapes.
        let alt_block: &[Stmt] = match if_statement.alternate.as_deref() {
            Some(alternate) => block_statements(alternate)?,
            None => &[],
        };
        if !branch_is_simple(cons_block) || !branch_is_simple(alt_block) {
            return None;
        }
        let cons_resumes = count_branch_yields(cons_block);
        let alt_resumes = count_branch_yields(alt_block);

        if cons_resumes == 0
            && alt_resumes == 0
            && !statements_contain_return(cons_block)
            && !statements_contain_return(alt_block)
        {
            // Inline reassembly: only the test can suspend.
            if !contains_yield(&if_statement.test) {
                ctx.push(statement.clone());
                return Some(());
            }
            let test = self.eval(&if_statement.test, ctx)?;
            let rebuilt = self.node(
                range,
                Statement::If(IfStatement {
                    test: Box::new(test),
                    consequent: if_statement.consequent.clone(),
                    alternate: if_statement.alternate.clone(),
                }),
            );
            ctx.push(rebuilt);
            return Some(());
        }
        if contains_yield(&if_statement.test) || ctx.terminated {
            return None;
        }
        let base = ctx.segments.len() as u32;
        let negated = self.node(
            if_statement.test.range(),
            Expression::Unary(UnaryExpression {
                operator: UnaryOperator::Not,
                argument: Box::new(if_statement.test.as_ref().clone()),
            }),
        );
        let else_label = base + cons_resumes;
        let end_label = else_label + 1 + alt_resumes;

        let jump = self.break_to(else_label, range);
        let guard = self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(negated),
                consequent: Box::new(jump),
                alternate: None,
            }),
        );
        ctx.push(guard);

        self.machine_emit_branch(cons_block, ctx)?;
        let cons_break = self.break_to(end_label, range);
        ctx.push(cons_break);
        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, else_label);
        self.machine_emit_branch(alt_block, ctx)?;
        let state = ctx.state.clone();
        let mark = self.label_assignment(end_label, &state, range);
        ctx.push(mark);

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, end_label);
        Some(())
    }
    fn machine_emit_labeled(
        &mut self,
        statement: &Stmt,
        body: &Stmt,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        match body.data() {
            Statement::While(while_statement) => {
                let body_block = block_statements(&while_statement.body)?;
                if count_yields(&while_statement.test) == 0
                    && count_branch_yields(body_block) == 0
                    && !statements_contain_return(body_block)
                {
                    // Clean loops stay inline, label attached.
                    ctx.push(statement.clone());
                    return Some(());
                }
                self.machine_emit_while(body, while_statement, ctx)
            }
            Statement::DoWhile(do_statement) => {
                let body_block = block_statements(&do_statement.body)?;
                if count_yields(&do_statement.test) == 0
                    && count_branch_yields(body_block) == 0
                    && !statements_contain_return(body_block)
                {
                    ctx.push(statement.clone());
                    return Some(());
                }
                self.machine_emit_do(body, do_statement, ctx)
            }
            Statement::For(for_statement) => {
                let body_block = block_statements(&for_statement.body)?;
                if for_clauses_are_clean(for_statement)
                    && count_branch_yields(body_block) == 0
                    && !statements_contain_return(body_block)
                {
                    let rebuilt =
                        self.inline_for_with_hoist(statement.range(), for_statement, ctx)?;
                    let label = match statement.data() {
                        Statement::Labeled(labeled) => labeled.label.clone(),
                        _ => return None,
                    };
                    let labeled = self.node(
                        statement.range(),
                        Statement::Labeled(LabeledStatement {
                            label,
                            body: Box::new(rebuilt),
                        }),
                    );
                    ctx.push(labeled);
                    return Some(());
                }
                self.machine_emit_for(body, for_statement, ctx)
            }
            Statement::Labeled(labeled) => {
                let name = self.identifier_name(&labeled.label)?;
                ctx.loop_labels.push(name);
                let result = self.machine_emit_labeled(body, &labeled.body, ctx);
                ctx.loop_labels.pop();
                result
            }
            _ => None,
        }
    }

    /// Lowers a while-loop into the machine. Clean loops stay inline;
    /// suspending ones build the labeled shape: the loop head holds the
    /// guard (after a suspending test resumes), `if (!test) return
    /// [3 /*break*/, exit];`, the body translates continue to a head jump
    /// and break to an exit jump, the body's completion loops back to the
    /// head, and the exit label continues the machine.
    fn machine_emit_while(
        &mut self,
        statement: &Stmt,
        while_statement: &WhileStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let body_block = block_statements(&while_statement.body)?;
        let test_resumes = count_yields(&while_statement.test);
        let body_resumes = count_branch_yields(body_block);
        if test_resumes == 0 && body_resumes == 0 && !statements_contain_return(body_block) {
            ctx.push(statement.clone());
            return Some(());
        }
        if ctx.terminated {
            return None;
        }
        let head = ctx.segments.len() as u32 - 1;
        let exit_label = head + test_resumes + body_resumes + 1;

        let test = self.eval(&while_statement.test, ctx)?;
        let negated = self.node(
            while_statement.test.range(),
            Expression::Unary(UnaryExpression {
                operator: UnaryOperator::Not,
                argument: Box::new(test),
            }),
        );
        let jump = self.break_to(exit_label, range);
        let guard = self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(negated),
                consequent: Box::new(jump),
                alternate: None,
            }),
        );
        ctx.push(guard);

        self.machine_emit_loop_body(body_block, head, exit_label, ctx)?;
        let body_terminated = ctx
            .segments
            .last()
            .and_then(|segment| segment.last())
            .is_some_and(|statement| matches!(statement.data(), Statement::Return(_)));
        if !body_terminated {
            let loop_back = self.break_to(head, range);
            ctx.push(loop_back);
        }

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, exit_label);
        Some(())
    }

    /// Lowers a do-while loop into the machine. Clean loops stay inline.
    /// The body starts at the head; its completion marks the test label
    /// (a suspending test resumes into the guard), the guard is POSITIVE
    /// (`if (test) return [3 /*break*/, head];`) because the loop-back is
    /// the taken branch, and continue jumps to the test label rather than
    /// the head — JS do-while semantics.
    fn machine_emit_do(
        &mut self,
        statement: &Stmt,
        do_statement: &DoWhileStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let body_block = block_statements(&do_statement.body)?;
        let test_resumes = count_yields(&do_statement.test);
        let body_resumes = count_branch_yields(body_block);
        if test_resumes == 0 && body_resumes == 0 && !statements_contain_return(body_block) {
            ctx.push(statement.clone());
            return Some(());
        }
        if ctx.terminated {
            return None;
        }
        let head = ctx.segments.len() as u32 - 1;
        let test_label = head + body_resumes + 1;
        let exit_label = test_label + test_resumes + 1;

        self.machine_emit_loop_body(body_block, test_label, exit_label, ctx)?;
        let body_terminated = ctx
            .segments
            .last()
            .and_then(|segment| segment.last())
            .is_some_and(|statement| matches!(statement.data(), Statement::Return(_)));
        if !body_terminated {
            let state = ctx.state.clone();
            let mark = self.label_assignment(test_label, &state, range);
            ctx.push(mark);
        }

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, test_label);
        let test = self.eval(&do_statement.test, ctx)?;

        // Positive guard: the loop-back is the taken branch. Re-mint the
        // test so a clean authored condition still hugs the head line.
        let guard_test = self.node(do_statement.test.range(), test.data().clone());
        let jump = self.break_to(head, range);
        let guard = self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(guard_test),
                consequent: Box::new(jump),
                alternate: None,
            }),
        );
        ctx.push(guard);
        let state = ctx.state.clone();
        let mark = self.label_assignment(exit_label, &state, range);
        ctx.push(mark);

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, exit_label);
        Some(())
    }

    /// A clean for-loop whose head declares `var`s keeps tsc's shape: the
    /// declarations hoist to the machine's var section and the head keeps
    /// only an assignment initializer (`for (c = x; ...)`), or nothing.
    fn inline_for_with_hoist(
        &mut self,
        range: TextRange,
        for_statement: &ForStatement,
        ctx: &mut MachineCtx,
    ) -> Option<Stmt> {
        let initializer = match &for_statement.initializer {
            Some(ForInitializer::Variable(declaration)) => {
                if declaration.declarations.len() != 1 {
                    return None;
                }
                let declarator = &declaration.declarations[0];
                let BindingPattern::Identifier(name) = declarator.data().binding.data() else {
                    return None;
                };
                let name = name.clone();
                ctx.hoisted.push(name.clone());
                match &declarator.data().initializer {
                    Some(initializer) => {
                        let assign = self.assign_statement(
                            &name,
                            initializer.as_ref().clone(),
                            initializer.range(),
                        );
                        let expression = match assign.data() {
                            Statement::Expression(expression) => expression.expression.clone(),
                            _ => return None,
                        };
                        Some(ForInitializer::Expression(expression))
                    }
                    None => None,
                }
            }
            other => other.clone(),
        };
        Some(self.node(
            range,
            Statement::For(ForStatement {
                initializer,
                test: for_statement.test.clone(),
                update: for_statement.update.clone(),
                body: for_statement.body.clone(),
            }),
        ))
    }

    /// Lowers a for-loop into the machine. The initializer runs at the
    /// head, the test label follows it (a suspending test resumes into the
    /// guard), the negated guard exits to the exit label, the body runs
    /// with continue targeting the update label (JS for semantics), the
    /// update label holds the increment and loops back to the test label,
    /// and the exit label continues the machine. Clean loops stay inline.
    fn machine_emit_for(
        &mut self,
        statement: &Stmt,
        for_statement: &ForStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let body_block = block_statements(&for_statement.body)?;
        if for_clauses_are_clean(for_statement)
            && count_branch_yields(body_block) == 0
            && !statements_contain_return(body_block)
        {
            let rebuilt = self.inline_for_with_hoist(range, for_statement, ctx)?;
            ctx.push(rebuilt);
            return Some(());
        }
        let Some(test) = for_statement.test.as_deref() else {
            // No test clause: the machine shape is not specced here.
            return None;
        };
        if ctx.terminated {
            return None;
        }
        let init_resumes = match &for_statement.initializer {
            Some(ForInitializer::Expression(expression)) => count_yields(expression),
            Some(ForInitializer::Variable(declaration)) => declaration
                .declarations
                .iter()
                .map(|declarator| {
                    declarator
                        .data()
                        .initializer
                        .as_deref()
                        .map_or(0, count_yields)
                })
                .sum(),
            None => 0,
        };
        let test_resumes = count_yields(test);
        let update_resumes = for_statement.update.as_deref().map_or(0, count_yields);
        let body_resumes = count_branch_yields(body_block);
        let head = ctx.segments.len() as u32 - 1;
        let test_label = head + init_resumes + 1;
        let guard_label = test_label + test_resumes;
        let update_label = guard_label + body_resumes + 1;
        let exit_label = update_label + update_resumes + 1;

        match &for_statement.initializer {
            Some(ForInitializer::Variable(declaration)) => {
                // The declaration is plain data here; re-wrap it in a
                // statement for the shared branch emitter.
                let wrapper = self.node(
                    range,
                    Statement::Variable(VariableDeclaration {
                        range: declaration.range,
                        kind: declaration.kind,
                        declarations: declaration.declarations.clone(),
                    }),
                );
                self.machine_emit_branch(std::slice::from_ref(&wrapper), ctx)?;
            }
            Some(ForInitializer::Expression(expression)) => {
                self.machine_emit_expression(expression, ctx)?;
            }
            None => {}
        }
        let state = ctx.state.clone();
        let mark = self.label_assignment(test_label, &state, range);
        ctx.push(mark);

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, test_label);
        let evaluated = self.eval(test, ctx)?;
        let negated = self.node(
            test.range(),
            Expression::Unary(UnaryExpression {
                operator: UnaryOperator::Not,
                argument: Box::new(evaluated),
            }),
        );
        let jump = self.break_to(exit_label, range);
        let guard = self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(negated),
                consequent: Box::new(jump),
                alternate: None,
            }),
        );
        ctx.push(guard);

        self.machine_emit_loop_body(body_block, update_label, exit_label, ctx)?;
        let body_terminated = ctx
            .segments
            .last()
            .and_then(|segment| segment.last())
            .is_some_and(|statement| matches!(statement.data(), Statement::Return(_)));
        if !body_terminated {
            let state = ctx.state.clone();
            let mark = self.label_assignment(update_label, &state, range);
            ctx.push(mark);
        }

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, update_label);
        if let Some(update) = for_statement.update.as_deref() {
            self.machine_emit_expression(update, ctx)?;
        }
        let back = self.break_to(test_label, range);
        ctx.push(back);

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, exit_label);
        Some(())
    }

    /// Lowers a switch-statement into the machine. A clean switch stays
    /// inline; a suspending discriminant with clean members reassembles
    /// inline around the resumed value. Otherwise the machine form: the
    /// discriminant is held in a temp, body labels run in source case
    /// order after the dispatch phases, clean tests join the head's
    /// dispatch switch, each suspending test closes it and yields and its
    /// resume opens the next holding the sent comparison plus later clean
    /// tests, and the chain falls through to the default body's label or
    /// the end. Bodies run at their labels; break jumps to the end and a
    /// break-less body marks the next body's label.
    fn machine_emit_switch(
        &mut self,
        statement: &Stmt,
        switch_statement: &SwitchStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let case_test_suspends =
            |case: &SwitchCaseNode| case.data().test.as_deref().is_some_and(contains_yield);
        let case_body_resumes =
            |case: &SwitchCaseNode| count_branch_yields(&case.data().consequent);
        let disc_suspends = contains_yield(&switch_statement.discriminant);
        let any_test = switch_statement.cases.iter().any(case_test_suspends);
        let any_body = switch_statement
            .cases
            .iter()
            .any(|case| case_body_resumes(case) > 0);
        let any_return = switch_statement
            .cases
            .iter()
            .any(|case| statements_contain_return(&case.data().consequent));
        if !disc_suspends && !any_test && !any_body && !any_return {
            ctx.push(statement.clone());
            return Some(());
        }
        if disc_suspends && !any_test && !any_body && !any_return {
            // Only the discriminant suspends: reassemble inline around
            // the resumed value, cases cloned.
            let discriminant = self.eval(&switch_statement.discriminant, ctx)?;
            let rebuilt = self.node(
                range,
                Statement::Switch(SwitchStatement {
                    discriminant: Box::new(discriminant),
                    cases: switch_statement.cases.clone(),
                }),
            );
            ctx.push(rebuilt);
            return Some(());
        }
        if disc_suspends {
            // A suspending discriminant alongside suspending members is
            // beyond this slice.
            return None;
        }
        for case in &switch_statement.cases {
            if !case.data().consequent.iter().all(|statement| {
                matches!(
                    statement.data(),
                    Statement::Expression(_)
                        | Statement::Variable(_)
                        | Statement::Break(_)
                        | Statement::Empty
                )
            }) {
                return None;
            }
        }
        if ctx.terminated {
            return None;
        }

        let head = ctx.segments.len() as u32 - 1;
        // One resume segment per yield node, not per suspending case: a
        // case test like `(yield a) + (yield b)` splits twice, and a
        // case-count under-count skews every dispatch target past it.
        let suspending_tests = switch_statement
            .cases
            .iter()
            .map(|case| case.data().test.as_deref().map_or(0, count_yields))
            .sum::<u32>();
        // Each suspending test's yield lands in the current segment and
        // its resume opens one new segment, so the dispatch phases span
        // head..head+suspending_tests and bodies start after.
        let mut cursor = head + 1 + suspending_tests;
        let mut body_labels = Vec::new();
        for case in &switch_statement.cases {
            body_labels.push(cursor);
            // A body occupies its own label plus one per resume phase
            // inside it; the next body starts after all of them.
            let resumes = case_body_resumes(case);
            cursor += resumes + 1;
        }
        let end_label = cursor;
        let default_label = switch_statement
            .cases
            .iter()
            .position(|case| case.data().test.is_none())
            .map(|index| body_labels[index]);

        // The discriminant is always held in a temp in machine form.
        let bank_range = self.bank.intern("switch");
        let disc_temp = self.materialize(
            switch_statement.discriminant.as_ref().clone(),
            ctx,
            bank_range,
        )?;

        // Dispatch chain.
        let mut clean_entries: Vec<(Expr, u32)> = Vec::new();
        let mut sent_entry: Option<(Expr, u32)> = None;
        for (index, case) in switch_statement.cases.iter().enumerate() {
            let target = body_labels[index];
            match case.data().test.as_deref() {
                Some(test) if contains_yield(test) => {
                    let dispatch = self.push_dispatch_switch(
                        &disc_temp,
                        &clean_entries,
                        sent_entry.take(),
                        range,
                    )?;
                    if let Some(dispatch) = dispatch {
                        ctx.push(dispatch);
                    }
                    clean_entries.clear();
                    // eval splits the suspension (`return [4, arg];`),
                    // opens the resume segment, and returns the resumed
                    // value — the sent comparison's test in the next phase.
                    let resumed = self.eval(test, ctx)?;
                    sent_entry = Some((resumed, target));
                }
                Some(test) => clean_entries.push((test.clone(), target)),
                None => {}
            }
        }
        let dispatch = self.push_dispatch_switch(&disc_temp, &clean_entries, sent_entry, range)?;
        if let Some(dispatch) = dispatch {
            ctx.push(dispatch);
        }
        let fallthrough_target = default_label.unwrap_or(end_label);
        let fallthrough = self.break_to(fallthrough_target, range);
        ctx.push(fallthrough);

        // Bodies at their labels, in source order.
        for (index, case) in switch_statement.cases.iter().enumerate() {
            let label = body_labels[index];
            ctx.segments.push(Vec::new());
            debug_assert_eq!(ctx.segments.len() as u32 - 1, label);
            self.machine_emit_switch_body(
                &case.data().consequent,
                end_label,
                index,
                &body_labels,
                case.range(),
                ctx,
            )?;
        }

        ctx.segments.push(Vec::new());
        debug_assert_eq!(ctx.segments.len() as u32 - 1, end_label);
        Some(())
    }

    /// The dispatch mini-switch: one inline jump case per clean entry, the
    /// sent comparison first when a suspending test just resumed. Tests
    /// carry bank-interned ranges so the printer's inline rule fires.
    fn push_dispatch_switch(
        &mut self,
        disc_temp: &Expr,
        clean_entries: &[(Expr, u32)],
        sent_entry: Option<(Expr, u32)>,
        range: TextRange,
    ) -> Option<Option<Stmt>> {
        if clean_entries.is_empty() && sent_entry.is_none() {
            return Some(None);
        }
        let mut cases = Vec::new();
        if let Some((sent, target)) = sent_entry {
            // Re-mint with a bank range so the printer's inline rule
            // fires for the comparison case.
            let bank = self.bank.intern("sent");
            let minted = self.node(bank, sent.data().clone());
            let jump = self.break_to(target, range);
            let case = self.node(
                range,
                SwitchCase {
                    test: Some(Box::new(minted)),
                    consequent: vec![jump],
                },
            );
            cases.push(case);
        }
        for (test, target) in clean_entries {
            let bank = self.bank.intern("case");
            let minted = self.node(bank, test.data().clone());
            let jump = self.break_to(*target, range);
            let case = self.node(
                range,
                SwitchCase {
                    test: Some(Box::new(minted)),
                    consequent: vec![jump],
                },
            );
            cases.push(case);
        }
        let switch = self.syn_node(
            range,
            Statement::Switch(SwitchStatement {
                discriminant: Box::new(disc_temp.clone()),
                cases,
            }),
        );
        Some(Some(switch))
    }

    /// One case body: statements flow through the branch emitter, break
    /// jumps to the end, and a body ending without a break marks the next
    /// body's label (switch fallthrough).
    fn machine_emit_switch_body(
        &mut self,
        statements: &[Stmt],
        end_label: u32,
        index: usize,
        body_labels: &[u32],
        case_range: TextRange,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let mut fell_through = true;
        for statement in statements {
            match statement.data() {
                Statement::Break(_) => {
                    let bank_range = self.bank.intern("break");
                    let out = self.break_to(end_label, bank_range);
                    ctx.push(out);
                    fell_through = false;
                }
                Statement::Empty => {}
                Statement::Expression(_) | Statement::Variable(_) => {
                    self.machine_emit_branch(std::slice::from_ref(statement), ctx)?;
                }
                _ => return None,
            }
        }
        if fell_through {
            let next = body_labels.get(index + 1).copied().unwrap_or(end_label);
            let state = ctx.state.clone();
            let mark = self.label_assignment(next, &state, case_range);
            ctx.push(mark);
        }
        Some(())
    }

    /// Emits loop-body statements, translating continue/break jumps and
    /// single-jump if-guards; other statements flow through the shared
    /// branch emitter. Translated jumps carry bank ranges so authored
    /// same-line detection cannot claim them.
    fn machine_emit_loop_body(
        &mut self,
        statements: &[Stmt],
        head: u32,
        exit: u32,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        for statement in statements {
            match statement.data() {
                Statement::Continue(jump) => {
                    self.jump_label_matches(&jump.label, ctx)?;
                    let bank_range = self.bank.intern("continue");
                    let back = self.break_to(head, bank_range);
                    ctx.push(back);
                }
                Statement::Break(jump) => {
                    self.jump_label_matches(&jump.label, ctx)?;
                    let bank_range = self.bank.intern("break");
                    let out = self.break_to(exit, bank_range);
                    ctx.push(out);
                }
                Statement::If(if_statement) if if_statement.alternate.is_none() => {
                    self.machine_emit_jump_guard(if_statement, head, exit, ctx)?;
                }
                Statement::Expression(_) | Statement::Variable(_) => {
                    self.machine_emit_branch(std::slice::from_ref(statement), ctx)?;
                }
                _ => return None,
            }
        }
        Some(())
    }

    /// `if (cond) continue|break;` — rewrites the jump into a labeled
    /// break with the body on its own line.
    fn machine_emit_jump_guard(
        &mut self,
        if_statement: &IfStatement,
        head: u32,
        exit: u32,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        if contains_yield(&if_statement.test) {
            return None;
        }
        let branch: &[Stmt] = match if_statement.consequent.data() {
            Statement::Block(block) => &block.data().statements,
            _ => std::slice::from_ref(&if_statement.consequent),
        };
        if branch.len() != 1
            || !matches!(
                branch[0].data(),
                Statement::Continue(_) | Statement::Break(_)
            )
        {
            return None;
        }
        let bank_range = self.bank.intern("jump");
        let jump = match branch[0].data() {
            Statement::Continue(j) => {
                self.jump_label_matches(&j.label, ctx)?;
                self.break_to(head, bank_range)
            }
            Statement::Break(j) => {
                self.jump_label_matches(&j.label, ctx)?;
                self.break_to(exit, bank_range)
            }
            _ => return None,
        };
        let rebuilt = self.node(
            if_statement.consequent.range(),
            Statement::If(IfStatement {
                test: Box::new(if_statement.test.as_ref().clone()),
                consequent: Box::new(jump),
                alternate: None,
            }),
        );
        ctx.push(rebuilt);
        Some(())
    }

    /// A labeled jump must target an enclosing loop of this machine.
    fn jump_label_matches(&self, label: &Option<IdentifierNode>, ctx: &MachineCtx) -> Option<()> {
        match label {
            None => Some(()),
            Some(label) => {
                let name = self.identifier_name(label)?;
                if ctx.loop_labels.iter().any(|candidate| candidate == &name) {
                    Some(())
                } else {
                    None
                }
            }
        }
    }
    fn machine_emit_branch(&mut self, statements: &[Stmt], ctx: &mut MachineCtx) -> Option<()> {
        for statement in statements {
            match statement.data() {
                Statement::Expression(expression) => {
                    self.machine_emit_expression(&expression.expression, ctx)?;
                }
                Statement::Variable(declaration) if declaration.kind == VariableKind::Var => {
                    for declarator in &declaration.declarations {
                        let BindingPattern::Identifier(name) = declarator.data().binding.data()
                        else {
                            return None;
                        };
                        let name = name.clone();
                        ctx.hoisted.push(name.clone());
                        if let Some(initializer) = &declarator.data().initializer {
                            let value = if contains_yield(initializer) {
                                self.eval(initializer, ctx)?
                            } else {
                                initializer.as_ref().clone()
                            };
                            let assign = self.assign_statement(&name, value, statement.range());
                            ctx.push(assign);
                        }
                    }
                }
                _ => return None,
            }
        }
        Some(())
    }

    /// `return [3 /*break*/, label];`
    fn break_to(&mut self, label: u32, range: TextRange) -> Stmt {
        let sentinel = self.number_expr("3 /*break*/");
        let target = self.number_expr(&label.to_string());
        let array = self.array_literal(vec![sentinel, target], range);
        self.machine_return(array, range)
    }

    /// `<state>.label = <label>;`
    fn label_assignment(&mut self, label: u32, state: &str, range: TextRange) -> Stmt {
        let state_ident = self.ident(state);
        let label_name = self.ident("label");
        let object = self.node(state_ident.range(), Expression::Identifier(state_ident));
        let left = self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property: MemberProperty::Named(label_name),
            }),
        );
        let value = self.number_expr(&label.to_string());
        let assign = self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assign),
            }),
        )
    }

    /// Evaluates an expression for the machine: subexpressions evaluated
    /// before a suspension keep their values in temps, and the resume side
    /// reassembles the form with `<state>.sent()` at the suspension point.
    fn eval(&mut self, expr: &Expr, ctx: &mut MachineCtx) -> Option<Expr> {
        if !contains_yield(expr) {
            return Some(expr.clone());
        }
        let range = expr.range();
        match expr.data() {
            Expression::Yield(yielded) => {
                if yielded.delegate {
                    return None;
                }
                // A bare `yield;` is the same protocol with void 0; refusing
                // the whole generator over the missing argument drops a
                // trivial, common shape.
                let void_argument = self.void_zero(expr.range());
                let argument = yielded
                    .argument
                    .as_ref()
                    .map_or(void_argument, |argument| argument.as_ref().clone());
                let evaluated = self.eval(&argument, ctx)?;
                let sentinel = self.number_expr("4 /*yield*/");
                let array = self.array_literal(vec![sentinel, evaluated], range);
                let terminator = self.machine_return(array, range);
                ctx.push(terminator);
                ctx.segments.push(Vec::new());
                Some(self.state_sent_call(&ctx.state, range))
            }
            Expression::Binary(binary) => {
                let left = self.eval_sibling(&binary.left, contains_yield(&binary.right), ctx)?;
                let left = self.paren_if_sent(left, range);
                let right = self.eval(&binary.right, ctx)?;
                let right = self.paren_if_sent(right, range);
                Some(self.node(
                    range,
                    Expression::Binary(BinaryExpression {
                        operator: binary.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                ))
            }
            Expression::Logical(_) | Expression::Conditional(_) => None,
            Expression::Assignment(assignment) => {
                match assignment.left.data() {
                    AssignmentTarget::Member(member) => {
                        let base_suspends = contains_yield(&member.object)
                            || matches!(&member.property, MemberProperty::Computed(key) if contains_yield(key));
                        if base_suspends {
                            return None;
                        }
                    }
                    // Pattern and invalid targets are beyond this slice.
                    AssignmentTarget::Object(_)
                    | AssignmentTarget::Array(_)
                    | AssignmentTarget::Missing(_)
                    | AssignmentTarget::Invalid(_) => return None,
                    AssignmentTarget::Identifier(_) => {}
                }
                let right = self.eval(&assignment.right, ctx)?;
                Some(self.node(
                    range,
                    Expression::Assignment(AssignmentExpression {
                        operator: assignment.operator,
                        left: assignment.left.clone(),
                        right: Box::new(right),
                    }),
                ))
            }
            Expression::Unary(unary) => {
                let argument = self.eval(&unary.argument, ctx)?;
                Some(self.node(
                    range,
                    Expression::Unary(UnaryExpression {
                        operator: unary.operator,
                        argument: Box::new(argument),
                    }),
                ))
            }
            Expression::Parenthesized(inner) => {
                let value = self.eval(inner, ctx)?;
                Some(self.node(range, Expression::Parenthesized(Box::new(value))))
            }
            Expression::As(cast) => {
                let value = self.eval(&cast.expression, ctx)?;
                Some(self.node(
                    range,
                    Expression::As(AsExpression {
                        expression: Box::new(value),
                        type_node: cast.type_node.clone(),
                    }),
                ))
            }
            Expression::NonNull(non_null) => {
                let value = self.eval(&non_null.expression, ctx)?;
                Some(self.node(
                    range,
                    Expression::NonNull(NonNullExpression {
                        expression: Box::new(value),
                    }),
                ))
            }
            Expression::Sequence(sequence) => {
                let mut parts = Vec::new();
                for (index, element) in sequence.expressions.iter().enumerate() {
                    let later = sequence.expressions[index + 1..].iter().any(contains_yield);
                    parts.push(self.eval_sibling(element, later, ctx)?);
                }
                self.sequence_expression(parts, range)
            }
            Expression::Template(template) => {
                let mut expressions = Vec::new();
                for (index, expression) in template.expressions.iter().enumerate() {
                    let later = template.expressions[index + 1..].iter().any(contains_yield);
                    expressions.push(self.eval_sibling(expression, later, ctx)?);
                }
                Some(self.node(
                    range,
                    Expression::Template(TemplateLiteral {
                        elements: template.elements.clone(),
                        expressions,
                    }),
                ))
            }
            Expression::Array(array) => self.eval_array(array, ctx, range),
            Expression::Object(object) => self.eval_object(object, ctx, range),
            Expression::Member(member) => {
                let key_suspends = matches!(&member.property, MemberProperty::Computed(key) if contains_yield(key));
                let object_expr = if contains_yield(&member.object) {
                    let value = self.eval(&member.object, ctx)?;
                    self.paren_if_sent(value, range)
                } else if key_suspends {
                    let value = member.object.as_ref().clone();
                    self.materialize(value, ctx, range)?
                } else {
                    member.object.as_ref().clone()
                };
                let property = match &member.property {
                    MemberProperty::Computed(key) if contains_yield(key) => {
                        MemberProperty::Computed(Box::new(self.eval(key, ctx)?))
                    }
                    other => other.clone(),
                };
                Some(self.node(
                    range,
                    Expression::Member(MemberExpression {
                        object: Box::new(object_expr),
                        property,
                        optional: member.optional,
                    }),
                ))
            }
            Expression::Call(call) => {
                let first_susp = call.arguments.iter().position(call_argument_suspends);
                let has_spread = call
                    .arguments
                    .iter()
                    .any(|argument| matches!(argument, CallArgument::Spread(_)));
                let Some(first_susp) = first_susp else {
                    // No suspending argument: a suspending callee reassembles
                    // inline; arguments pass through unchanged.
                    let callee = if contains_yield(&call.callee) {
                        let value = self.eval(&call.callee, ctx)?;
                        self.paren_if_sent(value, range)
                    } else {
                        call.callee.as_ref().clone()
                    };
                    let arguments = call.arguments.clone();
                    return Some(self.node(
                        range,
                        Expression::Call(CallExpression {
                            callee: Box::new(callee),
                            optional: call.optional,
                            type_arguments: call.type_arguments.clone(),
                            arguments,
                        }),
                    ));
                };
                if has_spread || contains_yield(&call.callee) {
                    return None;
                }
                // tsc's protocol for suspending arguments: the callee is
                // held in a temp — for a member callee the object is held
                // too, through a parenthesized temp assignment, and becomes
                // the apply receiver. Arguments before the suspension are
                // held in one temp array; resumption concats the rest.
                let (apply_callee, receiver) = match call.callee.data() {
                    Expression::Identifier(_) => {
                        let temp = self.materialize(call.callee.as_ref().clone(), ctx, range)?;
                        let void_zero = self.void_zero(range);
                        (temp, void_zero)
                    }
                    Expression::Member(member)
                        if !contains_yield(&member.object)
                            && !matches!(&member.property, MemberProperty::Computed(_)) =>
                    {
                        let (ident, assign) =
                            self.alloc_temp(member.object.as_ref().clone(), ctx, range)?;
                        let parenthesized =
                            self.node(range, Expression::Parenthesized(Box::new(assign)));
                        let member_expr = self.node(
                            range,
                            Expression::Member(MemberExpression {
                                object: Box::new(parenthesized),
                                property: member.property.clone(),
                                optional: member.optional,
                            }),
                        );
                        let temp = self.materialize(member_expr, ctx, range)?;
                        let reference = self.node(ident.range(), Expression::Identifier(ident));
                        (temp, reference)
                    }
                    _ => return None,
                };
                let prior_form = if first_susp > 0 {
                    let prior = call.arguments[..first_susp]
                        .iter()
                        .map(|argument| match argument {
                            CallArgument::Expression(value) => Some(value.as_ref().clone()),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let prior_array = self.array_literal(prior, range);
                    Some(self.materialize(prior_array, ctx, range)?)
                } else {
                    None
                };
                let mut rest = Vec::new();
                for (index, argument) in call.arguments.iter().skip(first_susp).enumerate() {
                    let offset = first_susp + index;
                    let later = call.arguments[offset + 1..]
                        .iter()
                        .any(call_argument_suspends);
                    match argument {
                        CallArgument::Expression(value) => {
                            let evaluated = self.eval_sibling(value, later, ctx)?;
                            rest.push(evaluated);
                        }
                        _ => return None,
                    }
                }
                let args_form = if let Some(temp) = prior_form {
                    let rest_array = self.array_literal(rest, range);
                    let concat = self.member_access(temp, "concat", range);
                    self.node(
                        range,
                        Expression::Call(CallExpression {
                            callee: Box::new(concat),
                            optional: false,
                            type_arguments: None,
                            arguments: vec![CallArgument::Expression(Box::new(rest_array))],
                        }),
                    )
                } else {
                    self.array_literal(rest, range)
                };
                let apply = self.member_access(apply_callee, "apply", range);
                Some(self.node(
                    range,
                    Expression::Call(CallExpression {
                        callee: Box::new(apply),
                        optional: false,
                        type_arguments: None,
                        arguments: vec![
                            CallArgument::Expression(Box::new(receiver)),
                            CallArgument::Expression(Box::new(args_form)),
                        ],
                    }),
                ))
            }
            Expression::New(new) => {
                if new.arguments.iter().any(call_argument_suspends) {
                    // The bind protocol for suspending `new` arguments is
                    // beyond this slice.
                    return None;
                }
                let callee = if contains_yield(&new.callee) {
                    let value = self.eval(&new.callee, ctx)?;
                    self.paren_if_sent(value, range)
                } else {
                    new.callee.as_ref().clone()
                };
                Some(self.node(
                    range,
                    Expression::New(NewExpression {
                        callee: Box::new(callee),
                        type_arguments: new.type_arguments.clone(),
                        arguments: new.arguments.clone(),
                    }),
                ))
            }
            Expression::Import(import) => {
                // Source operands run before the options suspend; a clean
                // source with side effects must materialize into a temp
                // ahead of the split, or its effects slip into the resume
                // segment and run after the suspension.
                let options_suspends = import.options.as_deref().is_some_and(contains_yield);
                let source = match self.eval(&import.source, ctx)? {
                    value if options_suspends => self.materialize(value, ctx, range)?,
                    value => value,
                };
                let options = match &import.options {
                    Some(options) if contains_yield(options) => {
                        Some(Box::new(self.eval(options, ctx)?))
                    }
                    other => other.clone(),
                };
                Some(self.node(
                    range,
                    Expression::Import(ImportExpression {
                        source: Box::new(source),
                        options,
                    }),
                ))
            }
            _ => None,
        }
    }

    /// Evaluates one sibling, materializing its value into a temp when a
    /// later sibling suspends across it.
    fn eval_sibling(
        &mut self,
        expr: &Expr,
        later_suspends: bool,
        ctx: &mut MachineCtx,
    ) -> Option<Expr> {
        let value = self.eval(expr, ctx)?;
        if later_suspends {
            self.materialize(value, ctx, expr.range())
        } else {
            Some(value)
        }
    }

    /// Array literals split at the first suspending element: suspension at
    /// index 0 reassembles inline, a later suspension holds the evaluated
    /// prefix in a temp and resumes through `.concat`.
    fn eval_array(
        &mut self,
        array: &ArrayLiteral,
        ctx: &mut MachineCtx,
        range: TextRange,
    ) -> Option<Expr> {
        let first = array.elements.iter().position(
            |element| matches!(element, ArrayElement::Expression(value) if contains_yield(value)),
        );
        let first = first?;
        let mut elements = Vec::new();
        for (index, element) in array.elements.iter().enumerate() {
            match element {
                ArrayElement::Expression(value) => {
                    let later = array.elements[index + 1..]
                        .iter()
                        .any(|element| matches!(element, ArrayElement::Expression(value) if contains_yield(value)));
                    let evaluated = self.eval_sibling(value, later, ctx)?;
                    elements.push(ArrayElement::Expression(Box::new(evaluated)));
                }
                ArrayElement::Spread(_) if contains_yield_array(array) => return None,
                other => elements.push(other.clone()),
            }
        }
        if first == 0 {
            return Some(self.node(range, Expression::Array(ArrayLiteral { elements })));
        }
        let prefix = array.elements[..first].to_vec();
        let prefix_literal = self.node(range, Expression::Array(ArrayLiteral { elements: prefix }));
        let temp = self.materialize(prefix_literal, ctx, range)?;
        let rest = elements
            .into_iter()
            .skip(first)
            .map(|element| match element {
                ArrayElement::Expression(value) => Some(*value),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let rest_array = self.array_literal(rest, range);
        let concat = self.member_access(temp, "concat", range);
        Some(self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(concat),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(rest_array))],
            }),
        ))
    }

    /// Object literals hold the evaluated prefix in a temp and resume by
    /// assigning properties in order, ending with the temp.
    fn eval_object(
        &mut self,
        object: &ObjectLiteral,
        ctx: &mut MachineCtx,
        range: TextRange,
    ) -> Option<Expr> {
        if !object.members.iter().all(|member| {
            matches!(member.data(), ObjectMember::Property(property) if !matches!(&property.name, PropertyName::Computed(_)))
        }) {
            return None;
        }
        let first = object
            .members
            .iter()
            .position(|member| {
                matches!(member.data(), ObjectMember::Property(property) if contains_yield(&property.value))
            })?;
        let prefix = object.members[..first].to_vec();
        let prefix_literal =
            self.node(range, Expression::Object(ObjectLiteral { members: prefix }));
        let temp = self.materialize(prefix_literal, ctx, range)?;
        let mut parts = Vec::new();
        for member in &object.members[first..] {
            let ObjectMember::Property(property) = member.data() else {
                return None;
            };
            let value = &property.value;
            let evaluated = self.eval(value, ctx)?;
            parts.push(self.temp_property_assign(&temp, property, evaluated, range)?);
        }
        parts.push(temp);
        self.sequence_expression(parts, range)
    }

    /// `<state>.sent()`
    fn state_sent_call(&mut self, state: &str, range: TextRange) -> Expr {
        let state_expr = self.ident_expr(state);
        let sent_name = self.ident("sent");
        let sent = self.member_expr(&state_expr, MemberProperty::Named(sent_name), range);
        self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(sent),
                optional: false,
                type_arguments: None,
                arguments: Vec::new(),
            }),
        )
    }

    /// Wraps a `<state>.sent()` call in parentheses at the positions tsc
    /// parenthesizes them: operands and member/new bases.
    fn paren_if_sent(&mut self, expr: Expr, range: TextRange) -> Expr {
        let sent_range = self.bank.intern("sent");
        let is_sent = matches!(
            expr.data(),
            Expression::Call(call)
                if matches!(
                    call.callee.data(),
                    Expression::Member(member)
                        if matches!(&member.property, MemberProperty::Named(name)
                            if name.data().token().range() == sent_range)
                )
        );
        if is_sent {
            self.node(range, Expression::Parenthesized(Box::new(expr)))
        } else {
            expr
        }
    }

    fn member_access(&mut self, object: Expr, property: &str, range: TextRange) -> Expr {
        let name = self.ident(property);
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object),
                property: MemberProperty::Named(name),
                optional: false,
            }),
        )
    }

    fn sequence_expression(&mut self, parts: Vec<Expr>, range: TextRange) -> Option<Expr> {
        if parts.len() < 2 {
            return None;
        }
        Some(self.node(
            range,
            Expression::Sequence(SequenceExpression { expressions: parts }),
        ))
    }

    /// `<temp>.<name> = <value>`
    fn temp_property_assign(
        &mut self,
        temp: &Expr,
        property: &ObjectProperty,
        value: Expr,
        range: TextRange,
    ) -> Option<Expr> {
        let name = match &property.name {
            PropertyName::Identifier(name) => name.clone(),
            PropertyName::String(_) => {
                return None;
            }
            _ => return None,
        };
        let left = self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(temp.clone()),
                property: MemberProperty::Named(name),
            }),
        );
        Some(self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        ))
    }

    /// Holds an already-computed value in a fresh temp assignment so it
    /// survives the suspension, and returns the temp reference.
    fn materialize(&mut self, value: Expr, ctx: &mut MachineCtx, range: TextRange) -> Option<Expr> {
        let (name, assign) = self.alloc_temp(value, ctx, range)?;
        let statement = self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assign),
            }),
        );
        ctx.push(statement);
        Some(self.node(name.range(), Expression::Identifier(name)))
    }

    /// Allocates a temp and builds `<temp> = <value>` as an expression,
    /// without emitting it: member-callee saving inlines the assignment in
    /// parentheses instead of as a statement.
    fn alloc_temp(
        &mut self,
        value: Expr,
        ctx: &mut MachineCtx,
        range: TextRange,
    ) -> Option<(IdentifierNode, Expr)> {
        let name_text = ctx.next_temp_name()?;
        ctx.temp_names.push(name_text.clone());
        let name = self.ident(&name_text);
        ctx.temps.push(name.clone());
        let left = self.node(name.range(), AssignmentTarget::Identifier(name.clone()));
        let assign = self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        );
        Some((name, assign))
    }

    /// `name = value;`
    fn assign_statement(&mut self, target: &IdentifierNode, value: Expr, range: TextRange) -> Stmt {
        let left = self.node(target.range(), AssignmentTarget::Identifier(target.clone()));
        let assignment = self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(assignment),
            }),
        )
    }

    /// `return <argument>;`
    fn machine_return(&mut self, argument: Expr, range: TextRange) -> Stmt {
        self.syn_node(
            range,
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(argument)),
            }),
        )
    }

    /// `[2 /*return*/]`
    fn return_sentinel(&mut self, range: TextRange) -> Expr {
        let sentinel = self.number_expr("2 /*return*/");
        self.array_literal(vec![sentinel], range)
    }

    fn array_literal(&mut self, elements: Vec<Expr>, range: TextRange) -> Expr {
        let elements = elements
            .into_iter()
            .map(|element| ArrayElement::Expression(Box::new(element)))
            .collect();
        self.node(range, Expression::Array(ArrayLiteral { elements }))
    }

    fn lower_class_expression(
        &mut self,
        expression: &Expr,
        class_expression: &ClassExpression,
        inferred_name: Option<&str>,
        hoist_suspending: bool,
    ) -> Expr {
        if matches!(FieldMode::for_options(self.options), FieldMode::Native) {
            let lowered = self.lower_class(&class_expression.class, expression.range(), None);
            let child_marked = self.any_marked(lowered.class.members.iter().map(|m| m.id()));
            return self.wrap_marked(
                expression.range(),
                Expression::Class(ClassExpression {
                    class: lowered.class,
                }),
                child_marked,
            );
        }
        let temp = self.temp_ident();
        let mut lowered =
            self.lower_class(&class_expression.class, expression.range(), Some(&temp));
        // Nothing needed the temp — no field statements, computed keys,
        // heritage temps, or static steps — so tsc keeps the class
        // expression inline (classExpressionTest2 emits `var m = class C {`
        // with type parameters stripped, never a temp IIFE).
        if lowered.prelude.is_empty() && lowered.postlude.is_empty() {
            let child_marked = self.any_marked(lowered.class.members.iter().map(|m| m.id()));
            return self.wrap_marked(
                expression.range(),
                Expression::Class(ClassExpression {
                    class: lowered.class,
                }),
                child_marked,
            );
        }
        // A suspending computed key cannot live inside the IIFE: the
        // arrow is a plain function, so a yield there is a SyntaxError
        // (tsc 6.0.2 emits exactly that broken shape). Where the caller
        // drains key_prelude into an enclosing statement list, the
        // suspending key temps hoist out and the machine splits them;
        // expression contexts cannot hoist, so they keep the IIFE and
        // signal the requires-es2015 refusal instead of breaking
        // silently. Static-field postludes reference the constructed
        // temp and can never hoist; they refuse the same way.
        // Whole-prelude move only: partitioning the prelude would
        // reorder mixed suspending and clean keys, and computed keys
        // evaluate in member order. Entries never reference the class
        // temp (its declaration is pushed below), so the move is
        // order-safe. An await counts too: in expression position the
        // rewrite pass leaves it raw, and the machine entry gate then
        // refuses the whole generator loudly.
        let suspends = |statement: &Stmt| {
            count_branch_yields(std::slice::from_ref(statement)) > 0
                || statements_contain_await(std::slice::from_ref(statement))
        };
        let refused = lowered.prelude.iter().any(&suspends) && !hoist_suspending;
        if !refused && hoist_suspending && lowered.prelude.iter().any(&suspends) {
            self.key_prelude
                .extend(std::mem::take(&mut lowered.prelude));
        }
        let postlude_refused = lowered.postlude.iter().any(suspends);
        if refused || postlude_refused {
            self.diag(
                codes::GENERATOR_REQUIRES_ES2015,
                expression.range(),
                "generators require ScriptTarget::Es2015 or later",
            );
            // Returning the unlowered class keeps the failure loud and
            // honest: the machine's class walker (heritage, computed
            // names, field initializers) sees the suspension, refuses
            // the conversion, and the generator stays native under the
            // diagnostic. Lowering anyway would bury a raw yield or
            // await inside a synthesized plain arrow the machine
            // cannot see through - the postlude (static-field
            // initializers) included, not just the key prelude.
            return expression.clone();
        }
        let class = self.syn_node(
            expression.range(),
            Expression::Class(ClassExpression {
                class: lowered.class,
            }),
        );
        let declaration = self.make_declarator(temp.clone(), Some(class), expression.range());
        lowered.prelude.push(self.syn_node(
            expression.range(),
            Statement::Variable(VariableDeclaration {
                range: expression.range(),
                kind: if self.options.target >= ScriptTarget::Es2015 {
                    VariableKind::Let
                } else {
                    VariableKind::Var
                },
                declarations: vec![declaration],
            }),
        ));
        if class_expression.class.name.is_none() {
            lowered.prelude.push(self.restore_class_name(
                &temp,
                inferred_name.unwrap_or(""),
                expression.range(),
            ));
        }
        lowered.prelude.extend(lowered.postlude);
        let result = self.syn_node(temp.range(), Expression::Identifier(temp));
        lowered.prelude.push(self.syn_node(
            expression.range(),
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(result)),
            }),
        ));
        let body = self.syn_node(
            expression.range(),
            Block {
                statements: lowered.prelude,
            },
        );
        let arrow = self.syn_node(
            expression.range(),
            Expression::Arrow(ArrowFunction {
                is_async: false,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: None,
                body: FunctionBody::Block(body),
            }),
        );
        self.syn_node(
            expression.range(),
            Expression::Call(CallExpression {
                callee: Box::new(arrow),
                optional: false,
                type_arguments: None,
                arguments: Vec::new(),
            }),
        )
    }

    fn rewrite_call_arguments(&mut self, arguments: &[CallArgument]) -> Vec<CallArgument> {
        arguments
            .iter()
            .map(|argument| match argument {
                CallArgument::Expression(value) => {
                    CallArgument::Expression(Box::new(self.rewrite_expr(value)))
                }
                CallArgument::Spread(spread) => CallArgument::Spread(SpreadElement {
                    argument: Box::new(self.rewrite_expr(&spread.argument)),
                }),
                CallArgument::Missing(missing) => CallArgument::Missing(missing.clone()),
            })
            .collect()
    }
    fn rewrite_expr(&mut self, expression: &Expr) -> Expr {
        if self.replace_await
            && let Expression::Await(awaited) = expression.data()
        {
            let argument = self.rewrite_expr(&awaited.argument);
            return self.node(
                expression.range(),
                Expression::Yield(YieldExpression {
                    delegate: false,
                    argument: Some(Box::new(argument)),
                }),
            );
        }
        match expression.data() {
            Expression::Class(class) => {
                let previous = self.replace_await;
                self.replace_await = false;
                let lowered = self.lower_class_expression(expression, class, None, false);
                self.replace_await = previous;
                lowered
            }
            Expression::Function(function) => {
                // A nested function-like owns its awaits: rewriting them
                // into yields here would emit `yield` inside a non-async
                // function, so the flag clears for the nested body and
                // restores after.
                let previous = self.replace_await;
                self.replace_await = false;
                let function = self.rewrite_function_like(&function.function, expression.range());
                self.replace_await = previous;
                self.node(
                    expression.range(),
                    Expression::Function(FunctionExpression { function }),
                )
            }
            Expression::Arrow(arrow) => {
                let previous = self.replace_await;
                self.replace_await = false;
                let rewritten = self.rewrite_arrow(expression, arrow);
                self.replace_await = previous;
                rewritten
            }
            Expression::Await(awaited) => {
                let argument = self.rewrite_expr(&awaited.argument);
                self.node(
                    expression.range(),
                    Expression::Await(AwaitExpression {
                        argument: Box::new(argument),
                    }),
                )
            }
            Expression::Call(_)
                if Self::needs(LanguageFeature::OptionalChaining, self.options)
                    && spine_has_optional(expression) =>
            {
                self.lower_optional_chain(expression)
            }
            Expression::Call(call) => {
                let needs_safe_wrap = self.cjs_call_needs_safe_wrap(&call.callee);
                let callee = self.rewrite_expr(&call.callee);
                let callee = if needs_safe_wrap {
                    self.cjs_wrap_callee(callee)
                } else {
                    callee
                };
                let arguments = self.rewrite_call_arguments(&call.arguments);
                self.node(
                    expression.range(),
                    Expression::Call(CallExpression {
                        callee: Box::new(callee),
                        optional: call.optional,
                        type_arguments: None,
                        arguments,
                    }),
                )
            }
            Expression::New(new_expr) => {
                let callee = self.rewrite_expr(&new_expr.callee);
                let arguments = self.rewrite_call_arguments(&new_expr.arguments);
                self.node(
                    expression.range(),
                    Expression::New(NewExpression {
                        callee: Box::new(callee),
                        type_arguments: None,
                        arguments,
                    }),
                )
            }
            Expression::Member(_)
                if Self::needs(LanguageFeature::OptionalChaining, self.options)
                    && spine_has_optional(expression) =>
            {
                self.lower_optional_chain(expression)
            }
            Expression::Member(member) => {
                let object = self.rewrite_expr(&member.object);
                let property = match &member.property {
                    MemberProperty::Computed(value) => {
                        MemberProperty::Computed(Box::new(self.rewrite_expr(value)))
                    }
                    other => other.clone(),
                };
                self.node(
                    expression.range(),
                    Expression::Member(MemberExpression {
                        object: Box::new(object),
                        property,
                        optional: member.optional,
                    }),
                )
            }
            Expression::Parenthesized(value) => {
                let value = self.rewrite_expr(value);
                self.node(
                    expression.range(),
                    Expression::Parenthesized(Box::new(value)),
                )
            }
            Expression::Sequence(value) => {
                let expressions = value
                    .expressions
                    .iter()
                    .map(|value| self.rewrite_expr(value))
                    .collect();
                self.node(
                    expression.range(),
                    Expression::Sequence(SequenceExpression { expressions }),
                )
            }
            Expression::Conditional(value) => {
                let test = self.rewrite_expr(&value.test);
                let consequent = self.rewrite_expr(&value.consequent);
                let alternate = self.rewrite_expr(&value.alternate);
                self.node(
                    expression.range(),
                    Expression::Conditional(ConditionalExpression {
                        test: Box::new(test),
                        consequent: Box::new(consequent),
                        alternate: Box::new(alternate),
                    }),
                )
            }
            Expression::Binary(value) => {
                let left = self.rewrite_expr(&value.left);
                let right = self.rewrite_expr(&value.right);
                if value.operator == BinaryOperator::Exponentiate
                    && Self::needs(LanguageFeature::Exponentiation, self.options)
                {
                    return self.math_pow(left, right, expression.range());
                }
                self.node(
                    expression.range(),
                    Expression::Binary(BinaryExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Logical(value) => {
                let left = self.rewrite_expr(&value.left);
                let right = self.rewrite_expr(&value.right);
                if value.operator == LogicalOperator::Nullish
                    && Self::needs(LanguageFeature::NullishCoalescing, self.options)
                {
                    return self.lower_nullish_coalescing(left, right, expression.range());
                }
                self.node(
                    expression.range(),
                    Expression::Logical(LogicalExpression {
                        operator: value.operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                )
            }
            Expression::Unary(value) => {
                let argument = self.rewrite_expr(&value.argument);
                self.node(
                    expression.range(),
                    Expression::Unary(UnaryExpression {
                        operator: value.operator,
                        argument: Box::new(argument),
                    }),
                )
            }
            Expression::As(value) => {
                let inner = self.rewrite_expr(&value.expression);
                self.node(
                    expression.range(),
                    Expression::As(AsExpression {
                        expression: Box::new(inner),
                        type_node: value.type_node.clone(),
                    }),
                )
            }
            Expression::Satisfies(value) => {
                let inner = self.rewrite_expr(&value.expression);
                self.node(
                    expression.range(),
                    Expression::Satisfies(SatisfiesExpression {
                        expression: Box::new(inner),
                        type_node: value.type_node.clone(),
                    }),
                )
            }
            Expression::TypeAssertion(value) => {
                let inner = self.rewrite_expr(&value.expression);
                self.node(
                    expression.range(),
                    Expression::TypeAssertion(TypeAssertionExpression {
                        expression: Box::new(inner),
                        type_node: value.type_node.clone(),
                    }),
                )
            }
            Expression::NonNull(value) => {
                let inner = self.rewrite_expr(&value.expression);
                self.node(
                    expression.range(),
                    Expression::NonNull(NonNullExpression {
                        expression: Box::new(inner),
                    }),
                )
            }
            Expression::Import(value) => {
                let source = self.rewrite_expr(&value.source);
                let options = value
                    .options
                    .as_deref()
                    .map(|value| Box::new(self.rewrite_expr(value)));
                self.node(
                    expression.range(),
                    Expression::Import(ImportExpression {
                        source: Box::new(source),
                        options,
                    }),
                )
            }
            Expression::Assignment(assignment)
                if Self::needs(LanguageFeature::Destructuring, self.options)
                    && matches!(
                        assignment.left.data(),
                        AssignmentTarget::Object(_) | AssignmentTarget::Array(_)
                    ) =>
            {
                self.diag(
                    codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015,
                    expression.range(),
                    "destructuring assignment requires ScriptTarget::Es2015 or later",
                );
                expression.clone()
            }
            Expression::Assignment(assignment) => {
                if assignment.operator == AssignmentOperator::ExponentiateAssign
                    && Self::needs(LanguageFeature::Exponentiation, self.options)
                {
                    return self.lower_compound_exponentiation(expression, assignment);
                }
                if Self::needs(LanguageFeature::LogicalAssignment, self.options)
                    && matches!(
                        assignment.operator,
                        AssignmentOperator::LogicalAndAssign
                            | AssignmentOperator::LogicalOrAssign
                            | AssignmentOperator::NullishAssign
                    )
                {
                    return self.lower_logical_assignment(expression, assignment);
                }
                let right = self.rewrite_expr(&assignment.right);
                let left = if self.replace_await
                    && let AssignmentTarget::Member(member) = assignment.left.data()
                    && target_contains_await(&member.object, &member.property)
                {
                    // Convert awaits inside the target too, so a
                    // suspending target becomes a visible machine refusal
                    // instead of a live `await` in ES5 output.
                    self.rewrite_member_target(member, assignment.left.range())
                } else {
                    assignment.left.clone()
                };
                self.node(
                    expression.range(),
                    Expression::Assignment(AssignmentExpression {
                        left,
                        right: Box::new(right),
                        ..assignment.clone()
                    }),
                )
            }
            Expression::Identifier(_) => {
                if let Some(replacement) = self.cjs_identifier_replacement(expression) {
                    replacement
                } else {
                    expression.clone()
                }
            }
            _ => expression.clone(),
        }
    }

    fn rewrite_member_target(
        &mut self,
        member: &AssignmentMemberTarget,
        range: TextRange,
    ) -> AssignmentTargetNode {
        let object = self.rewrite_expr(&member.object);
        let property = match &member.property {
            MemberProperty::Computed(key) => {
                MemberProperty::Computed(Box::new(self.rewrite_expr(key)))
            }
            other => other.clone(),
        };
        self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        )
    }

    /// `Math.pow(base, exponent)` — the ES2016 exponentiation downlevel form.
    fn math_pow(&mut self, base: Expr, exponent: Expr, range: TextRange) -> Expr {
        let math = self.ident("Math");
        let callee = self.member_ident(&math, "pow", range);
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(base)),
                    CallArgument::Expression(Box::new(exponent)),
                ],
            }),
        )
    }

    /// Lowers `a ?? b` below ES2020 to
    /// `a !== null && a !== void 0 ? a : b`.
    ///
    /// Baseline `nullishCoalescingOperator1.js` (default ES5 target) shows the
    /// canonical identifier form `a1 !== null && a1 !== void 0 ? a1 : 'whatever'`.
    /// Baseline `nullishCoalescingOperator2.js` (target=es2015) keeps the same
    /// lowered form at ES2015.  Counterexample side: at ES2020+ the native `??`
    /// is preserved (see the sampler's es2020-target cases emitting `??`
    /// verbatim).  A non-identifier left operand is captured once through an
    /// expression temp — tsc emits `var _a; (_a = f()) !== null && _a !==
    /// void 0 ? _a : rhs` — so the operand evaluates exactly once.
    ///
    /// `left` and `right` arrive already rewritten by the caller; this method
    /// must not rewrite either again.
    fn lower_nullish_coalescing(&mut self, left: Expr, right: Expr, range: TextRange) -> Expr {
        let (read, consequent) = if matches!(left.data(), Expression::Identifier(_)) {
            (left.clone(), left)
        } else {
            let temp = self.expression_temp();
            let reference = self.node(temp.range(), Expression::Identifier(temp.clone()));
            let target = self.node(temp.range(), AssignmentTarget::Identifier(temp));
            let capture = self.node(
                range,
                Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: target,
                    right: Box::new(left),
                }),
            );
            (
                self.node(range, Expression::Parenthesized(Box::new(capture))),
                reference,
            )
        };
        let null_check = self.strict_not_equal_null(&read, range);
        let void_check = self.strict_not_equal_void(&consequent, range);
        let test = self.node(
            range,
            Expression::Logical(LogicalExpression {
                operator: LogicalOperator::And,
                left: Box::new(null_check),
                right: Box::new(void_check),
            }),
        );
        self.node(
            range,
            Expression::Conditional(ConditionalExpression {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: Box::new(right),
            }),
        )
    }
    /// `left !== null` — one piece of the nullish coalescing lowering.
    fn strict_not_equal_null(&mut self, left: &Expr, range: TextRange) -> Expr {
        let null_lit = self.null_expr();
        self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictNotEqual,
                left: Box::new(left.clone()),
                right: Box::new(null_lit),
            }),
        )
    }
    /// `left !== void 0` — the other piece of the nullish coalescing lowering.
    fn strict_not_equal_void(&mut self, left: &Expr, range: TextRange) -> Expr {
        let void_zero = self.void_zero(range);
        self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictNotEqual,
                left: Box::new(left.clone()),
                right: Box::new(void_zero),
            }),
        )
    }

    /// `left === null` — the is-nullish check for optional-chain lowering.
    fn strict_equal_null(&mut self, left: &Expr, range: TextRange) -> Expr {
        let null_lit = self.null_expr();
        self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictEqual,
                left: Box::new(left.clone()),
                right: Box::new(null_lit),
            }),
        )
    }

    /// `left === void 0` — the is-undefined check for optional-chain lowering.
    fn strict_equal_void(&mut self, left: &Expr, range: TextRange) -> Expr {
        let void_zero = self.void_zero(range);
        self.node(
            range,
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::StrictEqual,
                left: Box::new(left.clone()),
                right: Box::new(void_zero),
            }),
        )
    }

    /// Lowers `a ||= b`, `a &&= b`, and `a ??= b` below ES2021.
    ///
    /// Identifier targets: `a || (a = b)`, `a && (a = b)`, and
    /// `a !== null && a !== void 0 ? a : (a = b)`.
    ///
    /// Baseline `equalityWithtNullishCoalescingAssignment(strict=false).js`
    /// shows `??=` lowered to `a !== null && a !== void 0 ? a : (a = true)`.
    /// Member targets base-capture through an expression temp so the object
    /// (and computed key) evaluate once, matching tsc's
    /// `(_a = obj).prop || (_a.prop = rhs)` shape.
    fn lower_logical_assignment(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
    ) -> Expr {
        let range = expression.range();
        let right = self.rewrite_expr(&assignment.right);
        match assignment.left.data() {
            AssignmentTarget::Identifier(identifier) => {
                let read = self.node(
                    identifier.range(),
                    Expression::Identifier(identifier.clone()),
                );
                let plain_read = self.node(
                    identifier.range(),
                    Expression::Identifier(identifier.clone()),
                );
                let inner_assign = self.node(
                    range,
                    Expression::Assignment(AssignmentExpression {
                        operator: AssignmentOperator::Assign,
                        left: assignment.left.clone(),
                        right: Box::new(right),
                    }),
                );
                self.compose_logical_assignment(
                    assignment.operator,
                    read,
                    plain_read,
                    inner_assign,
                    range,
                )
            }
            AssignmentTarget::Member(member) => {
                // JS evaluates `read` first in `read || assign`, so the
                // capture assignments belong to the READ side; the inner
                // assignment writes through plain temp references.
                let ((captured_target, captured_read), (reference_target, reference_read)) =
                    self.capture_member_parts(member);
                let _ = captured_target;
                let inner_assign = self.node(
                    range,
                    Expression::Assignment(AssignmentExpression {
                        operator: AssignmentOperator::Assign,
                        left: reference_target,
                        right: Box::new(right),
                    }),
                );
                self.compose_logical_assignment(
                    assignment.operator,
                    captured_read,
                    reference_read,
                    inner_assign,
                    range,
                )
            }
            AssignmentTarget::Object(_)
            | AssignmentTarget::Array(_)
            | AssignmentTarget::Missing(_)
            | AssignmentTarget::Invalid(_) => expression.clone(),
        }
    }

    /// Wraps single-evaluation reads and the plain assignment into the
    /// target's logical-assignment lowering form.  `first_read` sits in the
    /// position JS evaluates first (the logical test, and for `??=` the
    /// conditional test); `plain_read` is used where the operand is read
    /// again after the capture has run (the `??=` consequent).
    fn compose_logical_assignment(
        &mut self,
        operator: AssignmentOperator,
        first_read: Expr,
        plain_read: Expr,
        assign: Expr,
        range: TextRange,
    ) -> Expr {
        match operator {
            AssignmentOperator::LogicalOrAssign => self.node(
                range,
                Expression::Logical(LogicalExpression {
                    operator: LogicalOperator::Or,
                    left: Box::new(first_read),
                    right: Box::new(assign),
                }),
            ),
            AssignmentOperator::LogicalAndAssign => self.node(
                range,
                Expression::Logical(LogicalExpression {
                    operator: LogicalOperator::And,
                    left: Box::new(first_read),
                    right: Box::new(assign),
                }),
            ),
            AssignmentOperator::NullishAssign => {
                let null_check = self.strict_not_equal_null(&first_read, range);
                let void_check = self.strict_not_equal_void(&plain_read, range);
                let test = self.node(
                    range,
                    Expression::Logical(LogicalExpression {
                        operator: LogicalOperator::And,
                        left: Box::new(null_check),
                        right: Box::new(void_check),
                    }),
                );
                // The alternate is an assignment inside a conditional: wrap it
                // so the printer keeps tsc's `(a = b)` parens (`a ??= b` →
                // `a !== null && a !== void 0 ? a : (a = b)`).
                let alternate = self.node(range, Expression::Parenthesized(Box::new(assign)));
                self.node(
                    range,
                    Expression::Conditional(ConditionalExpression {
                        test: Box::new(test),
                        consequent: Box::new(plain_read),
                        alternate: Box::new(alternate),
                    }),
                )
            }
            _ => first_read,
        }
    }

    /// Captures a member assignment target for single evaluation: the base
    /// object (and every computed key) is stored into an expression temp.
    /// Returns `((captured_target, captured_read), (reference_target,
    /// reference_read))`.  The `captured` pair embeds the temp assignments —
    /// use it on the position JS evaluates FIRST (an assignment's left side,
    /// or a logical chain's left operand).  The `reference` pair reads the
    /// temps plainly — use it on later positions.  tsc's member-target
    /// logical-assignment form is `(_a = obj).prop || (_a.prop = rhs)`:
    /// `captured_read` is the left of `||`, `reference_target` is the left of
    /// the inner `=`.  Compound exponentiation mirrors this: `(_a =
    /// obj).v = Math.pow(_a.v, rhs)`.
    fn capture_member_parts(
        &mut self,
        member: &AssignmentMemberTarget,
    ) -> ((AssignmentTargetNode, Expr), (AssignmentTargetNode, Expr)) {
        let range = member.object.range();
        let object = self.rewrite_expr(&member.object);
        let (capture_object, reference_object) = if matches!(object.data(), Expression::Super) {
            (object.clone(), object)
        } else {
            let base = self.expression_temp();
            let base_reference = self.node(base.range(), Expression::Identifier(base.clone()));
            let base_target = self.node(base.range(), AssignmentTarget::Identifier(base));
            let base_assignment = self.node(
                object.range(),
                Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: base_target,
                    right: Box::new(object),
                }),
            );
            (base_assignment, base_reference)
        };
        let (capture_property, reference_property) = match &member.property {
            MemberProperty::Computed(key) => {
                let coerced_key = self.coerce_property_key(key);
                let key_range = coerced_key.range();
                let key_temp = self.expression_temp();
                let key_reference =
                    self.node(key_temp.range(), Expression::Identifier(key_temp.clone()));
                let key_target =
                    self.node(key_temp.range(), AssignmentTarget::Identifier(key_temp));
                let key_assignment = self.node(
                    key_range,
                    Expression::Assignment(AssignmentExpression {
                        operator: AssignmentOperator::Assign,
                        left: key_target,
                        right: Box::new(coerced_key),
                    }),
                );
                (
                    MemberProperty::Computed(Box::new(key_assignment)),
                    MemberProperty::Computed(Box::new(key_reference)),
                )
            }
            other => (other.clone(), other.clone()),
        };
        let captured_read = self.member_expr(&capture_object, capture_property.clone(), range);
        let captured_target = self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(capture_object),
                property: capture_property,
            }),
        );
        let reference_read = self.member_expr(&reference_object, reference_property.clone(), range);
        let reference_target = self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(reference_object),
                property: reference_property,
            }),
        );
        (
            (captured_target, captured_read),
            (reference_target, reference_read),
        )
    }

    /// Lowers an optional chain below ES2020.
    ///
    /// Rule: `a?.b` becomes `a === null || a === void 0 ? void 0 : a.b`.
    /// Proven by baseline `optionalChainingInArrow(target=es5).js`:
    /// `names === null || names === void 0 ? void 0 : names.filter(...)`.
    /// The check covers the chain BEFORE the first optional link; every
    /// later link — the optional one included — moves into the consequent,
    /// so `a?.b.c` short-circuits the whole chain.  The checked prefix is
    /// captured through an expression temp whenever it is not a bare
    /// identifier read, matching tsc's single-evaluation guarantee.
    fn lower_optional_chain(&mut self, expression: &Expr) -> Expr {
        let range = expression.range();
        let (root, segments) = collect_chain(expression);
        let Some(opt_idx) = segments.iter().position(ChainSegment::optional) else {
            return expression.clone();
        };
        let checked = &segments[..opt_idx];
        let continuation = &segments[opt_idx..];

        let rewritten_root = self.rewrite_expr(&root);
        let needs_capture = !matches!(root.data(), Expression::Identifier(_) | Expression::Super)
            || !checked.is_empty();
        let (checked_first_root, checked_plain_root) = if needs_capture {
            let temp = self.expression_temp();
            let reference = self.node(temp.range(), Expression::Identifier(temp.clone()));
            let target = self.node(temp.range(), AssignmentTarget::Identifier(temp));
            let capture = self.node(
                rewritten_root.range(),
                Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: target,
                    right: Box::new(rewritten_root),
                }),
            );
            (
                self.node(range, Expression::Parenthesized(Box::new(capture))),
                reference,
            )
        } else {
            (rewritten_root.clone(), rewritten_root)
        };

        // The capture assignment rides on the first read; the void check
        // and the chain read the plain reference.
        let checked_first = self.fold_chain(checked_first_root, checked, range);
        let checked_plain = self.fold_chain(checked_plain_root.clone(), checked, range);
        let null_check = self.strict_equal_null(&checked_first, range);
        let void_check = self.strict_equal_void(&checked_plain, range);
        let test = self.node(
            range,
            Expression::Logical(LogicalExpression {
                operator: LogicalOperator::Or,
                left: Box::new(null_check),
                right: Box::new(void_check),
            }),
        );
        let consequent = self.void_zero(range);
        let alternate = self.fold_chain(checked_plain_root, continuation, range);
        self.node(
            range,
            Expression::Conditional(ConditionalExpression {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: Box::new(alternate),
            }),
        )
    }
    /// Folds chain segments onto `base`, lowering each optional link's
    /// `?.` into a plain access (the surrounding ternary owns the check).
    fn fold_chain(&mut self, base: Expr, segments: &[ChainSegment], _range: TextRange) -> Expr {
        let mut current = base;
        for segment in segments {
            current = match segment {
                ChainSegment::Member {
                    property,
                    range: segment_range,
                    ..
                } => {
                    let property = match property {
                        MemberProperty::Computed(key) => {
                            MemberProperty::Computed(Box::new(self.rewrite_expr(key)))
                        }
                        other => other.clone(),
                    };
                    self.member_expr(&current, property, *segment_range)
                }
                ChainSegment::Call {
                    arguments,
                    range: segment_range,
                    ..
                } => {
                    let arguments = self.rewrite_call_arguments(arguments);
                    self.node(
                        *segment_range,
                        Expression::Call(CallExpression {
                            callee: Box::new(current),
                            optional: false,
                            type_arguments: None,
                            arguments,
                        }),
                    )
                }
            };
        }
        current
    }

    fn coerce_property_key(&mut self, key: &Expr) -> Expr {
        let key = self.rewrite_expr(key);
        let range = key.range();
        let prop_key = self.helper_ident(HelperKind::PropKey);
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(prop_key),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(key))],
            }),
        )
    }

    /// Lowers `lhs **= rhs` below ES2016 to `lhs = Math.pow(lhs, rhs)`.
    /// Identifier targets read the binding directly. Member targets capture
    /// the base and every computed key so getters and right-hand expressions
    /// cannot redirect the assignment by mutating either value.
    fn lower_compound_exponentiation(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
    ) -> Expr {
        let right = self.rewrite_expr(&assignment.right);
        match assignment.left.data() {
            AssignmentTarget::Identifier(identifier) => {
                let read = self.node(
                    identifier.range(),
                    Expression::Identifier(identifier.clone()),
                );
                let lowered = Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: assignment.left.clone(),
                    right: Box::new(self.math_pow(read, right, expression.range())),
                });
                self.node(expression.range(), lowered)
            }
            AssignmentTarget::Member(member) => {
                if self
                    .parameter_initializer_depths
                    .last()
                    .is_some_and(|depth| *depth == self.expression_temp_scopes.len())
                    && let MemberProperty::Computed(key) = &member.property
                    && !matches!(member.object.data(), Expression::Super)
                {
                    return self.lower_parameter_computed_exponentiation(
                        expression, assignment, member, key, right,
                    );
                }
                // JS evaluates an assignment's left side before its right,
                // so the capture assignments belong to the assignment target.
                let ((captured_target, _), (_, reference_read)) = self.capture_member_parts(member);
                let read = reference_read;
                let lowered = Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: captured_target,
                    right: Box::new(self.math_pow(read, right, expression.range())),
                });
                self.node(expression.range(), lowered)
            }
            AssignmentTarget::Object(_)
            | AssignmentTarget::Array(_)
            | AssignmentTarget::Missing(_)
            | AssignmentTarget::Invalid(_) => expression.clone(),
        }
    }

    fn lower_parameter_computed_exponentiation(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
        member: &AssignmentMemberTarget,
        key: &Expr,
        right: Expr,
    ) -> Expr {
        let (target, read) = self.parameter_computed_reference(expression, assignment, member, key);
        let powered = self.math_pow(read, right, expression.range());
        self.node(
            expression.range(),
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: target,
                right: Box::new(powered),
            }),
        )
    }

    fn parameter_computed_reference(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
        member: &AssignmentMemberTarget,
        key: &Expr,
    ) -> (AssignmentTargetNode, Expr) {
        let object = self.rewrite_expr(&member.object);
        let key = self.coerce_property_key(key);
        let frame = self.expression_temp();
        let frame_reference = self.node(frame.range(), Expression::Identifier(frame.clone()));
        let frame_target = self.node(frame.range(), AssignmentTarget::Identifier(frame));
        let frame_value = self.node(
            expression.range(),
            Expression::Array(ArrayLiteral {
                elements: vec![
                    ArrayElement::Expression(Box::new(object)),
                    ArrayElement::Expression(Box::new(key)),
                ],
            }),
        );
        // Assign only after key coercion returns. A recursive default initializer can then
        // overwrite the shared temp without corrupting this invocation's reference.
        let frame_assignment = self.node(
            expression.range(),
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: frame_target,
                right: Box::new(frame_value),
            }),
        );
        let target = {
            let object = self.reference_frame_slot(&frame_assignment, "0", expression.range());
            let property = MemberProperty::Computed(Box::new(self.reference_frame_slot(
                &frame_reference,
                "1",
                expression.range(),
            )));
            self.node(
                assignment.left.range(),
                AssignmentTarget::Member(AssignmentMemberTarget {
                    object: Box::new(object),
                    property,
                }),
            )
        };
        let read = {
            let object = self.reference_frame_slot(&frame_reference, "0", expression.range());
            let property = MemberProperty::Computed(Box::new(self.reference_frame_slot(
                &frame_reference,
                "1",
                expression.range(),
            )));
            self.member_expr(&object, property, expression.range())
        };
        (target, read)
    }

    fn reference_frame_slot(&mut self, frame: &Expr, index: &str, range: TextRange) -> Expr {
        let index = self.number_expr(index);
        self.member_expr(frame, MemberProperty::Computed(Box::new(index)), range)
    }
    /// Whether an arrow body references `this` or `arguments`, whose
    /// lexical capture needs hoisting when the arrow becomes a function
    /// expression. Unrecognized shapes report capture so the conversion
    /// refuses them.
    fn arrow_body_captures(&self, body: &FunctionBody) -> bool {
        match body {
            FunctionBody::Expression(expr) => self.expr_captures(expr),
            FunctionBody::Block(block) => block
                .data()
                .statements
                .iter()
                .any(|s| self.stmt_captures(s)),
            FunctionBody::Missing(_) => true,
        }
    }

    fn stmt_captures(&self, statement: &Stmt) -> bool {
        match statement.data() {
            Statement::Expression(statement) => self.expr_captures(&statement.expression),
            Statement::Return(returned) => returned
                .argument
                .as_deref()
                .is_some_and(|value| self.expr_captures(value)),
            Statement::Variable(declaration) => declaration.declarations.iter().any(|declarator| {
                declarator
                    .data()
                    .initializer
                    .as_deref()
                    .is_some_and(|value| self.expr_captures(value))
            }),
            Statement::Block(block) => block
                .data()
                .statements
                .iter()
                .any(|s| self.stmt_captures(s)),
            Statement::If(if_statement) => {
                self.expr_captures(&if_statement.test)
                    || self.stmt_captures(&if_statement.consequent)
                    || if_statement
                        .alternate
                        .as_deref()
                        .is_some_and(|alternate| self.stmt_captures(alternate))
            }
            _ => true,
        }
    }

    fn expr_captures(&self, expression: &Expr) -> bool {
        match expression.data() {
            Expression::This => true,
            Expression::Identifier(identifier) => {
                self.identifier_name(identifier).as_deref() == Some("arguments")
            }
            Expression::Function(_) | Expression::Class(_) | Expression::Arrow(_) => false,
            Expression::Call(call) => {
                self.expr_captures(&call.callee)
                    || call.arguments.iter().any(|argument| match argument {
                        CallArgument::Expression(value) => self.expr_captures(value),
                        _ => false,
                    })
            }
            Expression::Member(member) => {
                self.expr_captures(&member.object)
                    || matches!(&member.property, MemberProperty::Computed(key) if self.expr_captures(key))
            }
            Expression::Object(object) => object.members.iter().any(|member| match member.data() {
                ObjectMember::Property(property) => {
                    self.expr_captures(&property.value)
                        || matches!(&property.name, PropertyName::Computed(key) if self.expr_captures(key))
                }
                _ => true,
            }),
            Expression::Array(array) => array.elements.iter().any(|element| match element {
                ArrayElement::Expression(value) => self.expr_captures(value),
                _ => true,
            }),
            Expression::Unary(unary) => self.expr_captures(&unary.argument),
            Expression::Yield(yielded) => yielded
                .argument
                .as_deref()
                .is_some_and(|value| self.expr_captures(value)),
            Expression::Await(awaited) => self.expr_captures(&awaited.argument),
            Expression::Assignment(assignment) => self.expr_captures(&assignment.right),
            _ => true,
        }
    }

    fn rewrite_arrow(&mut self, expression: &Expr, arrow: &ArrowFunction) -> Expr {
        let parameters = self.rewrite_parameters(&arrow.parameters);
        if arrow.is_async && Self::needs(LanguageFeature::AsyncFunctions, self.options) {
            let previous = self.replace_await;
            self.replace_await = true;
            let body = match &arrow.body {
                FunctionBody::Expression(expr) => {
                    self.expression_temp_scopes.push(Vec::new());
                    let rewritten = self.rewrite_expr(expr);
                    let temps = self.expression_temp_scopes.pop().unwrap_or_default();
                    let mut statements = Vec::new();
                    if let Some(declaration) = self.temp_declaration(temps, expression.range()) {
                        statements.push(declaration);
                    }
                    statements.push(self.syn_node(
                        expression.range(),
                        Statement::Return(ReturnStatement {
                            argument: Some(Box::new(rewritten)),
                        }),
                    ));
                    let block = self.syn_node(expression.range(), Block { statements });
                    FunctionBody::Block(block)
                }
                other => self.rewrite_body(other),
            };
            self.replace_await = previous;
            let inner = FunctionLike {
                decorators: Vec::new(),
                name: None,
                is_async: false,
                is_generator: true,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: None,
                body: Some(body),
            };
            let inner = if Self::needs(LanguageFeature::Generators, self.options) {
                let lowered = self.lower_generator_function(&inner);
                if lowered.is_generator {
                    // Same contract as the named-function path: the machine
                    // declined and the inner stays a native generator inside
                    // __awaiter, which the target cannot run — signal it.
                    self.diag(
                        codes::GENERATOR_REQUIRES_ES2015,
                        expression.range(),
                        "generators require ScriptTarget::Es2015 or later",
                    );
                }
                lowered
            } else {
                inner
            };
            let inner_expr = self.syn_node(
                expression.range(),
                Expression::Function(FunctionExpression { function: inner }),
            );
            // ES5 has no arrows: the lowered arrow becomes a function
            // expression returning the awaiter, whose receiver is `void 0`
            // because arrows never bind `this`. Bodies that capture
            // `this`/`arguments` need the hoisted-capture machinery and
            // keep the arrow instead.
            let plain_parameters = arrow.parameters.iter().all(|parameter| {
                matches!(
                    parameter.data().binding.data(),
                    BindingPattern::Identifier(_)
                ) && parameter.data().initializer.is_none()
            });
            let lower_to_function = Self::needs(LanguageFeature::ArrowFunctions, self.options)
                && plain_parameters
                && !self.arrow_body_captures(&arrow.body);
            let this_arg = if lower_to_function {
                self.void_zero(expression.range())
            } else {
                self.syn_node(expression.range(), Expression::This)
            };
            let awaiter = self.helper_ident(HelperKind::Awaiter);
            let void_zero = self.void_zero(expression.range());
            let call = self.syn_node(
                expression.range(),
                Expression::Call(CallExpression {
                    callee: Box::new(awaiter),
                    optional: false,
                    type_arguments: None,
                    arguments: vec![
                        CallArgument::Expression(Box::new(this_arg)),
                        CallArgument::Expression(Box::new(void_zero.clone())),
                        CallArgument::Expression(Box::new(void_zero)),
                        CallArgument::Expression(Box::new(inner_expr)),
                    ],
                }),
            );
            if lower_to_function {
                // The expression body keeps tsc's converted-arrow layout:
                // `function (params) { return awaiter; }` prints inline.
                let function = FunctionLike {
                    decorators: Vec::new(),
                    name: None,
                    is_async: false,
                    is_generator: false,
                    type_parameters: None,
                    parameters,
                    return_type: None,
                    body: Some(FunctionBody::Expression(Box::new(call))),
                };
                return self.syn_node(
                    expression.range(),
                    Expression::Function(FunctionExpression { function }),
                );
            }
            return self.syn_node(
                expression.range(),
                Expression::Arrow(ArrowFunction {
                    is_async: false,
                    type_parameters: None,
                    parameters,
                    return_type: None,
                    body: FunctionBody::Expression(Box::new(call)),
                }),
            );
        }
        let body = match &arrow.body {
            FunctionBody::Expression(expr) => {
                self.expression_temp_scopes.push(Vec::new());
                let rewritten = self.rewrite_expr(expr);
                let temps = self.expression_temp_scopes.pop().unwrap_or_default();
                match self.temp_declaration(temps, expression.range()) {
                    None => FunctionBody::Expression(Box::new(rewritten)),
                    Some(declaration) => {
                        let returned = self.syn_node(
                            expression.range(),
                            Statement::Return(ReturnStatement {
                                argument: Some(Box::new(rewritten)),
                            }),
                        );

                        FunctionBody::Block(self.syn_node(
                            expression.range(),
                            Block {
                                statements: vec![declaration, returned],
                            },
                        ))
                    }
                }
            }
            other => self.rewrite_body(other),
        };
        let body_marked = match &body {
            FunctionBody::Block(block) => self.synthesized_ids.contains(&block.id()),
            FunctionBody::Expression(expr) => self.synthesized_ids.contains(&expr.id()),
            FunctionBody::Missing(_) => false,
        };
        self.wrap_marked(
            expression.range(),
            Expression::Arrow(ArrowFunction {
                parameters,
                body,
                ..arrow.clone()
            }),
            body_marked,
        )
    }
}

fn is_super_call_expression(expression: &Expr) -> bool {
    let Expression::Call(call) = expression.data() else {
        return false;
    };
    matches!(call.callee.data(), Expression::Super)
}

/// One member/call link of an optional-chain spine, ordered root-outward.
enum ChainSegment {
    Member {
        property: MemberProperty,
        optional: bool,
        range: TextRange,
    },
    Call {
        arguments: Vec<CallArgument>,
        optional: bool,
        range: TextRange,
    },
}

/// The statements of a block branch, or None for non-block shapes this
/// slice does not lower.
fn block_statements(statement: &Stmt) -> Option<&[Stmt]> {
    match statement.data() {
        Statement::Block(block) => Some(&block.data().statements),
        _ => None,
    }
}

/// Whether a for-loop's clauses carry no suspensions (the body may).
fn for_clauses_are_clean(for_statement: &ForStatement) -> bool {
    let init_clean = match &for_statement.initializer {
        Some(ForInitializer::Expression(expression)) => !contains_yield(expression),
        Some(ForInitializer::Variable(declaration)) => {
            declaration.declarations.iter().all(|declarator| {
                declarator
                    .data()
                    .initializer
                    .as_deref()
                    .is_none_or(|init| !contains_yield(init))
                    && count_binding_yields(&declarator.data().binding) == 0
            })
        }
        None => true,
    };
    let test_clean = for_statement
        .test
        .as_deref()
        .is_none_or(|test| !contains_yield(test));
    let update_clean = for_statement
        .update
        .as_deref()
        .is_none_or(|update| !contains_yield(update));
    init_clean && test_clean && update_clean
}

/// One `__rest` exclusion entry: a static property name or the temp
/// holding an evaluated computed key (excluded at runtime via tsc's
/// symbol-aware coercion).
enum RestExcludeKey {
    Static(String),
    Computed(IdentifierNode),
}

/// Suspensions inside a binding pattern: default initializers and
/// computed key expressions. Destructuring lowering erases nothing once
/// these count — a clean pattern lowers to ternary declarators, a
/// suspending one to machine-owned branch statements.
fn count_binding_yields(pattern: &Pattern) -> u32 {
    match pattern.data() {
        BindingPattern::Identifier(_) | BindingPattern::Missing(_) => 0,
        BindingPattern::Object(object) => object
            .properties
            .iter()
            .map(|property| {
                let key = match &property.name {
                    PropertyName::Computed(key) => count_yields(key),
                    _ => 0,
                };
                let default = property.initializer.as_deref().map_or(0, count_yields);
                key + default + count_binding_yields(&property.binding)
            })
            .sum(),
        BindingPattern::Array(array) => array
            .elements
            .iter()
            .map(|element| match element {
                ArrayBindingElement::Elision | ArrayBindingElement::Missing(_) => 0,
                ArrayBindingElement::Binding(binding) => count_binding_yields(binding),
            })
            .sum(),
        BindingPattern::Rest(rest) => count_binding_yields(&rest.argument),
        BindingPattern::Assignment(assignment) => {
            count_yields(&assignment.right) + count_binding_yields(&assignment.left)
        }
    }
}

/// Every identifier a pattern binds, in source order.
fn collect_binding_names(pattern: &Pattern, names: &mut Vec<IdentifierNode>) {
    match pattern.data() {
        BindingPattern::Identifier(ident) => names.push(ident.clone()),
        BindingPattern::Missing(_) => {}
        BindingPattern::Object(object) => {
            for property in &object.properties {
                collect_binding_names(&property.binding, names);
            }
        }
        BindingPattern::Array(array) => {
            for element in &array.elements {
                if let ArrayBindingElement::Binding(binding) = element {
                    collect_binding_names(binding, names);
                }
            }
        }
        BindingPattern::Rest(rest) => collect_binding_names(&rest.argument, names),
        BindingPattern::Assignment(assignment) => {
            collect_binding_names(&assignment.left, names);
        }
    }
}

/// The await view of the same binding-pattern walk.
fn binding_contains_await(pattern: &Pattern) -> bool {
    match pattern.data() {
        BindingPattern::Identifier(_) | BindingPattern::Missing(_) => false,
        BindingPattern::Object(object) => object.properties.iter().any(|property| {
            matches!(&property.name, PropertyName::Computed(key) if contains_await(key))
                || property.initializer.as_deref().is_some_and(contains_await)
                || binding_contains_await(&property.binding)
        }),
        BindingPattern::Array(array) => array.elements.iter().any(|element| match element {
            ArrayBindingElement::Elision | ArrayBindingElement::Missing(_) => false,
            ArrayBindingElement::Binding(binding) => binding_contains_await(binding),
        }),
        BindingPattern::Rest(rest) => binding_contains_await(&rest.argument),
        BindingPattern::Assignment(assignment) => {
            contains_await(&assignment.right) || binding_contains_await(&assignment.left)
        }
    }
}

/// Whether every branch statement is a shape the labeled if slice emits.
fn branch_is_simple(statements: &[Stmt]) -> bool {
    statements.iter().all(|statement| {
        matches!(
            statement.data(),
            Statement::Expression(_) | Statement::Variable(_)
        )
    })
}

/// The number of yield splits a branch's statements produce. Zero gates
/// the inline verbatim clone, so a statement shape the loop-body emitter
/// cannot lower must report non-zero (it refuses, keeping the native
/// form) — never zero.
fn count_branch_yields(statements: &[Stmt]) -> u32 {
    statements
        .iter()
        .map(|statement| match statement.data() {
            Statement::Expression(expression) => count_yields(&expression.expression),
            Statement::Variable(declaration) => declaration
                .declarations
                .iter()
                .map(|declarator| {
                    declarator
                        .data()
                        .initializer
                        .as_deref()
                        .map_or(0, count_yields)
                        + count_binding_yields(&declarator.data().binding)
                })
                .sum(),
            Statement::Continue(_) | Statement::Break(_) | Statement::Empty => 0,
            Statement::Return(ret) => ret.argument.as_deref().map_or(0, count_yields),
            Statement::Throw(throw) => count_yields(&throw.argument),
            Statement::Block(block) => count_branch_yields(&block.data().statements),
            // Clean nested control flow clones correctly inside a machine
            // body, so it counts precisely; suspending nested shapes route
            // to the body emitter, which refuses what it cannot lower.
            Statement::If(if_statement) => {
                count_yields(&if_statement.test)
                    + count_branch_yields(branch_statements(&if_statement.consequent))
                    + if_statement
                        .alternate
                        .as_ref()
                        .map_or(0, |alt| count_branch_yields(branch_statements(alt)))
            }
            Statement::While(while_statement) => {
                count_yields(&while_statement.test)
                    + count_branch_yields(branch_statements(&while_statement.body))
            }
            Statement::DoWhile(do_statement) => {
                count_yields(&do_statement.test)
                    + count_branch_yields(branch_statements(&do_statement.body))
            }
            Statement::Labeled(labeled) => count_branch_yields(branch_statements(&labeled.body)),
            _ => 1,
        })
        .sum()
}

/// The statements of a branch or loop body: a block flattens, any other
/// statement is a single-statement branch. Counters and the return guard
/// must see through non-block bodies, or a nested `while (x) return z;`
/// hides its return and the clone gate drops the value.
fn branch_statements(statement: &Stmt) -> &[Stmt] {
    match statement.data() {
        Statement::Block(block) => &block.data().statements,
        _ => std::slice::from_ref(statement),
    }
}

/// Whether any statement in this region returns — at any nesting depth,
/// but never inside a nested function-like (those own their returns).
/// A cloned raw return exits the machine's inner function directly and
/// the runtime silently drops the value, so clone gates must refuse.
fn statements_contain_return(statements: &[Stmt]) -> bool {
    statements.iter().any(|statement| match statement.data() {
        Statement::Return(_) => true,
        Statement::Block(block) => statements_contain_return(&block.data().statements),
        Statement::If(if_statement) => {
            statements_contain_return(branch_statements(&if_statement.consequent))
                || if_statement
                    .alternate
                    .as_ref()
                    .is_some_and(|alt| statements_contain_return(branch_statements(alt)))
        }
        Statement::While(while_statement) => {
            statements_contain_return(branch_statements(&while_statement.body))
        }
        Statement::DoWhile(do_statement) => {
            statements_contain_return(branch_statements(&do_statement.body))
        }
        Statement::Labeled(labeled) => statements_contain_return(branch_statements(&labeled.body)),
        Statement::Switch(switch_statement) => switch_statement
            .cases
            .iter()
            .any(|case| statements_contain_return(&case.data().consequent)),
        _ => false,
    })
}

impl ChainSegment {
    const fn optional(&self) -> bool {
        match self {
            Self::Member { optional, .. } | Self::Call { optional, .. } => *optional,
        }
    }
}

/// The enclosing-context code of a class: decorators, the heritage
/// expression, computed member names, and field initializers. Method,
/// constructor, and static-block bodies are function boundaries and own
/// their suspensions, so they stay opaque to the enclosing walkers.
fn count_class_context_yields(class: &ClassDeclaration) -> u32 {
    let decorators: u32 = class
        .decorators
        .iter()
        .map(|decorator| count_yields(&decorator.data().expression))
        .sum();
    let heritage = class
        .extends
        .as_ref()
        .map(|heritage| count_yields(&heritage.expression))
        .unwrap_or(0);
    let members: u32 = class
        .members
        .iter()
        .map(|member| match member.data() {
            ClassMember::Method(method) => match &method.name {
                PropertyName::Computed(key) => count_yields(key),
                _ => 0,
            },
            ClassMember::Property(property) => match &property.name {
                PropertyName::Computed(key) => count_yields(key),
                _ => property.initializer.as_deref().map_or(0, count_yields),
            },
            ClassMember::AutoAccessor(accessor) => match &accessor.name {
                PropertyName::Computed(key) => count_yields(key),
                _ => accessor.initializer.as_deref().map_or(0, count_yields),
            },
            _ => 0,
        })
        .sum();
    decorators + heritage + members
}

/// The await view of the same class-context walk.
fn class_context_contains_await(class: &ClassDeclaration) -> bool {
    if class
        .decorators
        .iter()
        .any(|decorator| contains_await(&decorator.data().expression))
        || class
            .extends
            .as_ref()
            .is_some_and(|heritage| contains_await(&heritage.expression))
    {
        return true;
    }
    class.members.iter().any(|member| match member.data() {
        ClassMember::Method(method) => {
            matches!(&method.name, PropertyName::Computed(key) if contains_await(key))
        }
        ClassMember::Property(property) => {
            matches!(&property.name, PropertyName::Computed(key) if contains_await(key))
                || property.initializer.as_deref().is_some_and(contains_await)
        }
        ClassMember::AutoAccessor(accessor) => {
            matches!(&accessor.name, PropertyName::Computed(key) if contains_await(key))
                || accessor.initializer.as_deref().is_some_and(contains_await)
        }
        _ => false,
    })
}

/// The yield view of the same class-context walk.
fn class_context_contains_yield(class: &ClassDeclaration) -> bool {
    if class
        .decorators
        .iter()
        .any(|decorator| contains_yield(&decorator.data().expression))
        || class
            .extends
            .as_ref()
            .is_some_and(|heritage| contains_yield(&heritage.expression))
    {
        return true;
    }
    class.members.iter().any(|member| match member.data() {
        ClassMember::Method(method) => {
            matches!(&method.name, PropertyName::Computed(key) if contains_yield(key))
        }
        ClassMember::Property(property) => {
            matches!(&property.name, PropertyName::Computed(key) if contains_yield(key))
                || property.initializer.as_deref().is_some_and(contains_yield)
        }
        ClassMember::AutoAccessor(accessor) => {
            matches!(&accessor.name, PropertyName::Computed(key) if contains_yield(key))
                || accessor.initializer.as_deref().is_some_and(contains_yield)
        }
        _ => false,
    })
}

/// Counts the yield nodes of this function's body (nested function-likes
/// own their own yields).
fn count_yields(expression: &Expr) -> u32 {
    match expression.data() {
        Expression::Yield(yielded) => 1 + yielded.argument.as_deref().map_or(0, count_yields),
        Expression::Identifier(_) | Expression::This | Expression::Super => 0,
        Expression::Literal(_) | Expression::Meta(_) | Expression::Missing(_) => 0,
        Expression::Function(_) | Expression::Arrow(_) => 0,
        // Heritage, computed names, and field initializers run in the
        // enclosing context; bodies stay owned.
        Expression::Class(class) => count_class_context_yields(&class.class),
        Expression::Template(template) => template.expressions.iter().map(count_yields).sum(),
        Expression::Array(array) => array
            .elements
            .iter()
            .map(|element| match element {
                ArrayElement::Expression(value) => count_yields(value),
                ArrayElement::Spread(spread) => count_yields(&spread.argument),
                _ => 0,
            })
            .sum(),
        Expression::Object(object) => object
            .members
            .iter()
            .map(|member| match member.data() {
                ObjectMember::Property(property) => {
                    count_yields(&property.value)
                        + match &property.name {
                            PropertyName::Computed(key) => count_yields(key),
                            _ => 0,
                        }
                }
                // A spread element carries an expression; method-like
                // members (methods/getters/setters) own their own
                // suspensions, just like nested function-likes, so the
                // wildcard below is safe for them.
                ObjectMember::Spread(spread) => count_yields(&spread.argument),
                // A method's computed name executes in the enclosing
                // function; its body owns its own suspensions.
                ObjectMember::Method(method) => match &method.name {
                    PropertyName::Computed(key) => count_yields(key),
                    _ => 0,
                },
                _ => 0,
            })
            .sum(),
        Expression::Call(call) => {
            count_yields(&call.callee)
                + call
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        CallArgument::Expression(value) => count_yields(value),
                        CallArgument::Spread(spread) => count_yields(&spread.argument),
                        _ => 0,
                    })
                    .sum::<u32>()
        }
        Expression::Member(member) => {
            count_yields(&member.object)
                + match &member.property {
                    MemberProperty::Computed(key) => count_yields(key),
                    _ => 0,
                }
        }
        Expression::New(new) => {
            count_yields(&new.callee)
                + new
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        CallArgument::Expression(value) => count_yields(value),
                        CallArgument::Spread(spread) => count_yields(&spread.argument),
                        _ => 0,
                    })
                    .sum::<u32>()
        }
        Expression::Await(awaited) => count_yields(&awaited.argument),
        Expression::Unary(unary) => count_yields(&unary.argument),
        Expression::Update(update) => match update.argument.data() {
            AssignmentTarget::Member(member) => {
                count_yields(&member.object)
                    + match &member.property {
                        MemberProperty::Computed(key) => count_yields(key),
                        _ => 0,
                    }
            }
            // Pattern and invalid targets can carry yields in computed
            // keys and defaults; a sentinel count routes them to eval,
            // which refuses, rather than the inline verbatim clone.
            AssignmentTarget::Identifier(_) => 0,
            _ => 1,
        },
        Expression::Binary(binary) => count_yields(&binary.left) + count_yields(&binary.right),
        Expression::Logical(logical) => count_yields(&logical.left) + count_yields(&logical.right),
        Expression::Conditional(conditional) => {
            count_yields(&conditional.test)
                + count_yields(&conditional.consequent)
                + count_yields(&conditional.alternate)
        }
        Expression::Assignment(assignment) => {
            count_yields(&assignment.right)
                + match assignment.left.data() {
                    AssignmentTarget::Member(member) => {
                        count_yields(&member.object)
                            + match &member.property {
                                MemberProperty::Computed(key) => count_yields(key),
                                _ => 0,
                            }
                    }
                    // Pattern and invalid targets can carry yields; a
                    // sentinel count routes them to eval, which refuses,
                    // rather than the inline verbatim clone.
                    AssignmentTarget::Identifier(_) => 0,
                    _ => 1,
                }
        }
        Expression::Sequence(sequence) => sequence.expressions.iter().map(count_yields).sum(),
        Expression::Parenthesized(inner) => count_yields(inner),
        Expression::As(cast) => count_yields(&cast.expression),
        Expression::NonNull(non_null) => count_yields(&non_null.expression),
        Expression::Import(import) => {
            count_yields(&import.source) + import.options.as_deref().map_or(0, count_yields)
        }
        // Unknown shapes report non-zero: zero means provably clean and
        // gates the inline verbatim clone; unknown routes to eval, whose
        // refusal keeps the native form.
        _ => 1,
    }
}

/// Splits a member/call spine into `(root, segments)` ordered root-outward.
/// Returns `None` only when the walk cannot proceed; callers guard with
/// [`spine_has_optional`] first.
fn collect_chain(expression: &Expr) -> (Expr, Vec<ChainSegment>) {
    let mut segments = Vec::new();
    let mut current = expression;
    loop {
        match current.data() {
            Expression::Member(member) => {
                segments.push(ChainSegment::Member {
                    property: member.property.clone(),
                    optional: member.optional,
                    range: current.range(),
                });
                current = &member.object;
            }
            Expression::Call(call) => {
                segments.push(ChainSegment::Call {
                    arguments: call.arguments.clone(),
                    optional: call.optional,
                    range: current.range(),
                });
                current = &call.callee;
            }
            _ => break,
        }
    }
    segments.reverse();
    (current.clone(), segments)
}

/// Whether any link of the member/call spine is optional (`?.`).
fn spine_has_optional(expression: &Expr) -> bool {
    let mut current = expression;
    loop {
        match current.data() {
            Expression::Member(member) => {
                if member.optional {
                    return true;
                }
                current = &member.object;
            }
            Expression::Call(call) => {
                if call.optional {
                    return true;
                }
                current = &call.callee;
            }
            _ => return false,
        }
    }
}

/// Converts a UTF-16 offset into a byte offset for plain-source text.
fn utf16_to_byte(text: &str, offset: usize) -> Option<usize> {
    if offset == 0 {
        return Some(0);
    }
    let mut units = 0usize;
    for (index, character) in text.char_indices() {
        if units == offset {
            return Some(index);
        }
        units += character.len_utf16();
    }
    if units == offset {
        return Some(text.len());
    }
    None
}

/// Raw token text taken straight from the source file.
fn raw_token_text(file: &SourceFile, token: &Token) -> String {
    let start = file
        .source_text()
        .utf16_to_byte(token.range().start())
        .unwrap_or(0);
    let end = file
        .source_text()
        .utf16_to_byte(token.range().end())
        .unwrap_or(0);
    file.source_text()
        .as_str()
        .get(start..end)
        .unwrap_or("")
        .to_owned()
}

/// The machine built from one generator body: hoisted user names, the
/// state parameter name, temp names, and the machine statements.
type MachineParts = (Vec<IdentifierNode>, String, Vec<IdentifierNode>, Vec<Stmt>);

/// Builder state for one `__generator` machine pass.
struct MachineCtx {
    hoisted: Vec<IdentifierNode>,
    temps: Vec<IdentifierNode>,
    temp_names: Vec<String>,
    segments: Vec<Vec<Stmt>>,
    terminated: bool,
    state: String,
    skip: std::collections::HashSet<String>,
    loop_labels: Vec<String>,
}

impl MachineCtx {
    fn new(state: &str, skip: std::collections::HashSet<String>) -> Self {
        Self {
            hoisted: Vec::new(),
            temps: Vec::new(),
            temp_names: Vec::new(),
            segments: vec![Vec::new()],
            terminated: false,
            skip,
            loop_labels: Vec::new(),
            state: state.to_string(),
        }
    }

    fn push(&mut self, statement: Stmt) {
        self.segments
            .last_mut()
            .expect("open segment")
            .push(statement);
    }

    /// The next free `_a`-style temp name, skipping user var names, the
    /// state parameter, and temps already allocated.
    fn next_temp_name(&self) -> Option<String> {
        let taken: std::collections::HashSet<String> = self
            .skip
            .iter()
            .chain(self.temp_names.iter())
            .chain([&self.state])
            .cloned()
            .collect();
        let mut index = 0u32;
        loop {
            let name = machine_name(index)?;
            if !taken.contains(&name) {
                return Some(name);
            }
            index += 1;
        }
    }
}

/// The `_a`, `_b`, … sequence used by the machine's temps and state.
fn machine_name(index: u32) -> Option<String> {
    let letters = b"abcdefghijklmnopqrstuvwxyz";
    let index = index as usize;
    if index >= letters.len() {
        return None;
    }
    Some(format!("_{}", letters[index] as char))
}

/// The state parameter takes the first free name after the temps.
fn machine_state_name(skip: &std::collections::HashSet<String>, temps: &[String]) -> String {
    let taken: std::collections::HashSet<&String> = skip.iter().chain(temps.iter()).collect();
    let mut index = 0u32;
    loop {
        // Past the alphabet machine_name returns None forever; a fixed
        // "_state" fallback would then loop endlessly when _state is also
        // taken, so the suffix keeps every candidate fresh and the loop
        // terminates.
        let name =
            machine_name(index).unwrap_or_else(|| format!("_state{}", index.saturating_sub(26)));
        if !taken.contains(&name) {
            return name;
        }
        index += 1;
    }
}

fn call_argument_suspends(argument: &CallArgument) -> bool {
    match argument {
        CallArgument::Expression(value) => contains_yield(value),
        CallArgument::Spread(spread) => contains_yield(&spread.argument),
        _ => false,
    }
}

/// Whether an assignment target subtree still holds an await, so the
/// left-side conversion only rebuilds targets it must touch.
fn target_contains_await(object: &Expr, property: &MemberProperty) -> bool {
    let key = match property {
        MemberProperty::Computed(key) => contains_await(key),
        _ => false,
    };
    contains_await(object) || key
}

/// Whether an expression still holds an await of THIS function (nested
/// function-likes own their own awaits).
fn contains_await(expression: &Expr) -> bool {
    match expression.data() {
        Expression::Await(_) => true,
        Expression::Identifier(_) | Expression::This | Expression::Super => false,
        Expression::Literal(_) | Expression::Meta(_) | Expression::Missing(_) => false,
        Expression::Function(_) | Expression::Arrow(_) => false,
        // Heritage, computed names, and field initializers run in the
        // enclosing context; bodies stay owned.
        Expression::Class(class) => class_context_contains_await(&class.class),
        Expression::Yield(yielded) => yielded.argument.as_deref().is_some_and(contains_await),
        Expression::Template(template) => template.expressions.iter().any(contains_await),
        Expression::Array(array) => array.elements.iter().any(|element| match element {
            ArrayElement::Expression(value) => contains_await(value),
            ArrayElement::Spread(spread) => contains_await(&spread.argument),
            _ => false,
        }),
        Expression::Object(object) => object.members.iter().any(|member| match member.data() {
            ObjectMember::Property(property) => {
                contains_await(&property.value)
                    || matches!(&property.name, PropertyName::Computed(key) if contains_await(key))
            }
            ObjectMember::Spread(spread) => contains_await(&spread.argument),
            // A method's computed name executes in the enclosing function;
            // its body owns its own suspensions.
            ObjectMember::Method(method) => {
                matches!(&method.name, PropertyName::Computed(key) if contains_await(key))
            }
            _ => false,
        }),
        Expression::Call(call) => {
            contains_await(&call.callee)
                || call.arguments.iter().any(|argument| match argument {
                    CallArgument::Expression(value) => contains_await(value),
                    CallArgument::Spread(spread) => contains_await(&spread.argument),
                    _ => false,
                })
        }
        Expression::Member(member) => target_contains_await(&member.object, &member.property),
        Expression::New(new) => {
            contains_await(&new.callee)
                || new.arguments.iter().any(|argument| match argument {
                    CallArgument::Expression(value) => contains_await(value),
                    CallArgument::Spread(spread) => contains_await(&spread.argument),
                    _ => false,
                })
        }
        Expression::Unary(unary) => contains_await(&unary.argument),
        Expression::Import(import) => {
            contains_await(&import.source) || import.options.as_deref().is_some_and(contains_await)
        }
        Expression::Update(update) => match update.argument.data() {
            AssignmentTarget::Member(member) => {
                target_contains_await(&member.object, &member.property)
            }
            // Pattern and invalid targets can carry expressions in
            // computed keys and defaults; report containment so the
            // machine refuses rather than clones.
            AssignmentTarget::Identifier(_) => false,
            _ => true,
        },
        Expression::Binary(binary) => contains_await(&binary.left) || contains_await(&binary.right),
        Expression::Logical(logical) => {
            contains_await(&logical.left) || contains_await(&logical.right)
        }
        Expression::Conditional(conditional) => {
            contains_await(&conditional.test)
                || contains_await(&conditional.consequent)
                || contains_await(&conditional.alternate)
        }
        Expression::Assignment(assignment) => {
            contains_await(&assignment.right)
                || match assignment.left.data() {
                    AssignmentTarget::Member(member) => {
                        target_contains_await(&member.object, &member.property)
                    }
                    // Pattern and invalid targets can carry expressions in
                    // computed keys and defaults; report containment so the
                    // machine refuses rather than clones.
                    AssignmentTarget::Identifier(_) => false,
                    _ => true,
                }
        }
        Expression::Sequence(sequence) => sequence.expressions.iter().any(contains_await),
        Expression::Parenthesized(inner) => contains_await(inner),
        Expression::As(cast) => contains_await(&cast.expression),
        Expression::NonNull(non_null) => contains_await(&non_null.expression),
        _ => true,
    }
}

/// Whether any statement still holds an await. Walks exactly the
/// statement shapes the machine accepts; other shapes report true, which
/// is consistent because the machine refuses them regardless.
fn statements_contain_await(statements: &[Stmt]) -> bool {
    statements.iter().any(|statement| match statement.data() {
        Statement::Expression(expression) => contains_await(&expression.expression),
        Statement::Variable(declaration) => declaration.declarations.iter().any(|declarator| {
            declarator
                .data()
                .initializer
                .as_deref()
                .is_some_and(contains_await)
                || binding_contains_await(&declarator.data().binding)
        }),
        Statement::Return(returned) => returned.argument.as_deref().is_some_and(contains_await),
        Statement::Block(block) => statements_contain_await(&block.data().statements),
        Statement::If(if_statement) => {
            contains_await(&if_statement.test)
                || branch_awaits(&if_statement.consequent)
                || if_statement.alternate.as_deref().is_some_and(branch_awaits)
        }
        Statement::While(while_statement) => {
            contains_await(&while_statement.test) || branch_awaits(&while_statement.body)
        }
        Statement::DoWhile(do_statement) => {
            contains_await(&do_statement.test) || branch_awaits(&do_statement.body)
        }
        Statement::For(for_statement) => {
            let init = match &for_statement.initializer {
                Some(ForInitializer::Expression(expression)) => contains_await(expression),
                Some(ForInitializer::Variable(declaration)) => {
                    declaration.declarations.iter().any(|declarator| {
                        declarator
                            .data()
                            .initializer
                            .as_deref()
                            .is_some_and(contains_await)
                            || binding_contains_await(&declarator.data().binding)
                    })
                }
                None => false,
            };
            let test = for_statement.test.as_deref().is_some_and(contains_await);
            let update = for_statement.update.as_deref().is_some_and(contains_await);
            init || test || update || branch_awaits(&for_statement.body)
        }
        Statement::Switch(switch_statement) => {
            contains_await(&switch_statement.discriminant)
                || switch_statement.cases.iter().any(|case| {
                    case.data().test.as_deref().is_some_and(contains_await)
                        || statements_contain_await(&case.data().consequent)
                })
        }
        Statement::Labeled(labeled) => branch_awaits(&labeled.body),
        // Jumps and empties hold no expressions.
        Statement::Break(_) | Statement::Continue(_) | Statement::Empty => false,
        // The machine helper wraps the body in try/catch, so a cloned raw
        // throw is protocol-safe; only its argument's awaits matter.
        Statement::Throw(throw_statement) => contains_await(&throw_statement.argument),
        _ => true,
    })
}

/// A branch's awaits: blocks walk their statements; other shapes report
/// true, matching the machine's refusal of them.
fn branch_awaits(statement: &Stmt) -> bool {
    match statement.data() {
        Statement::Break(_) | Statement::Continue(_) | Statement::Empty => false,
        // Delegate to the full statement walker so labeled and bare
        // control-flow bodies share one coverage set.
        _ => statements_contain_await(std::slice::from_ref(statement)),
    }
}

fn contains_yield_array(array: &ArrayLiteral) -> bool {
    array.elements.iter().any(|element| match element {
        ArrayElement::Expression(value) => contains_yield(value),
        ArrayElement::Spread(spread) => contains_yield(&spread.argument),
        _ => false,
    })
}

fn contains_yield(expression: &Expr) -> bool {
    match expression.data() {
        Expression::Yield(_) => true,
        Expression::Identifier(_) | Expression::This | Expression::Super => false,
        Expression::Literal(_) | Expression::Meta(_) | Expression::Missing(_) => false,
        // A yield inside a nested function belongs to that function.
        Expression::Function(_) | Expression::Arrow(_) => false,
        // Heritage, computed names, and field initializers run in the
        // enclosing context; bodies stay owned.
        Expression::Class(class) => class_context_contains_yield(&class.class),
        Expression::Template(template) => template.expressions.iter().any(contains_yield),
        Expression::TaggedTemplate(_) => true,
        Expression::Array(array) => contains_yield_array(array),
        Expression::Object(object) => object.members.iter().any(|member| match member.data() {
            ObjectMember::Property(property) => {
                contains_yield(&property.value)
                    || matches!(&property.name, PropertyName::Computed(key) if contains_yield(key))
            }
            ObjectMember::Spread(spread) => contains_yield(&spread.argument),
            // A method's computed name executes in the enclosing function;
            // its body owns its own suspensions.
            ObjectMember::Method(method) => {
                matches!(&method.name, PropertyName::Computed(key) if contains_yield(key))
            }
            _ => false,
        }),
        Expression::Call(call) => {
            contains_yield(&call.callee)
                || call.arguments.iter().any(|argument| match argument {
                    CallArgument::Expression(nested) => contains_yield(nested),
                    CallArgument::Spread(spread) => contains_yield(&spread.argument),
                    _ => false,
                })
        }
        Expression::Member(member) => {
            contains_yield(&member.object)
                || matches!(&member.property, MemberProperty::Computed(key) if contains_yield(key))
        }
        Expression::New(new) => {
            contains_yield(&new.callee)
                || new.arguments.iter().any(|argument| match argument {
                    CallArgument::Expression(nested) => contains_yield(nested),
                    CallArgument::Spread(spread) => contains_yield(&spread.argument),
                    _ => false,
                })
        }
        Expression::Await(awaited) => contains_yield(&awaited.argument),
        Expression::Unary(unary) => contains_yield(&unary.argument),
        Expression::Update(update) => match update.argument.data() {
            AssignmentTarget::Member(member) => {
                contains_yield(&member.object)
                    || matches!(&member.property, MemberProperty::Computed(key) if contains_yield(key))
            }
            // Pattern and invalid targets can carry expressions in
            // computed keys and defaults; report containment so the
            // machine refuses rather than clones.
            AssignmentTarget::Identifier(_) => false,
            _ => true,
        },
        Expression::Binary(binary) => contains_yield(&binary.left) || contains_yield(&binary.right),
        Expression::Logical(logical) => {
            contains_yield(&logical.left) || contains_yield(&logical.right)
        }
        Expression::Conditional(conditional) => {
            contains_yield(&conditional.test)
                || contains_yield(&conditional.consequent)
                || contains_yield(&conditional.alternate)
        }
        Expression::Assignment(assignment) => {
            contains_yield(&assignment.right)
                || match assignment.left.data() {
                    AssignmentTarget::Member(member) => {
                        contains_yield(&member.object)
                            || matches!(&member.property, MemberProperty::Computed(key) if contains_yield(key))
                    }
                    // Pattern and invalid targets can carry expressions in
                    // computed keys and defaults; report containment so the
                    // machine refuses rather than clones.
                    AssignmentTarget::Object(_)
                    | AssignmentTarget::Array(_)
                    | AssignmentTarget::Missing(_)
                    | AssignmentTarget::Invalid(_) => true,
                    AssignmentTarget::Identifier(_) => false,
                }
        }
        Expression::Sequence(sequence) => sequence.expressions.iter().any(contains_yield),
        Expression::Parenthesized(nested) => contains_yield(nested),
        Expression::As(cast) => contains_yield(&cast.expression),
        Expression::Satisfies(_) | Expression::TypeAssertion(_) => true,
        Expression::NonNull(non_null) => contains_yield(&non_null.expression),
        Expression::Import(import) => {
            contains_yield(&import.source) || import.options.as_deref().is_some_and(contains_yield)
        }
        Expression::JsxElement(_)
        | Expression::JsxFragment(_)
        | Expression::JsxSelfClosingElement(_) => true,
    }
}

fn identifier_text(file: &SourceFile, ident: &IdentifierNode) -> String {
    raw_token_text(file, ident.data().token())
}

/// Declared value names of a statement, for export assignment generation.
fn declared_binding_names(file: &SourceFile, statement: &Stmt) -> Vec<String> {
    match statement.data() {
        Statement::Variable(declaration) => declaration
            .declarations
            .iter()
            .filter_map(|declarator| match declarator.data().binding.data() {
                BindingPattern::Identifier(ident) => Some(identifier_text(file, ident)),
                _ => None,
            })
            .collect(),
        Statement::Enum(declaration) => vec![raw_token_text(file, declaration.name.data().token())],
        _ => Vec::new(),
    }
}

fn property_key_text(rewriter: &mut Rewriter, property: &ObjectBindingProperty) -> Option<String> {
    match &property.name {
        PropertyName::Identifier(ident) => {
            Some(rewriter.token_text(ident.data().token()).to_owned())
        }
        PropertyName::String(literal) => {
            let raw = rewriter.token_text(literal.data().token());
            Some(raw.trim_matches(['"', '\'']).to_owned())
        }
        _ => None,
    }
}

/// Source range of a property name, taken from its inner node.
fn property_name_range(name: &PropertyName) -> TextRange {
    match name {
        PropertyName::Identifier(ident) => ident.range(),
        PropertyName::String(literal) => literal.range(),
        PropertyName::Number(number) => number.range(),
        PropertyName::Computed(expression) => expression.range(),
        PropertyName::Private(private) => private.range(),
        PropertyName::Missing(_) => {
            TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("zero-width range is ordered")
        }
    }
}

fn scan_statements(
    file: &SourceFile,
    statements: &[Stmt],
    options: &TransformOptions,
    features: &mut BTreeSet<LanguageFeature>,
    diagnostics: &mut Vec<Diagnostic>,
    in_async: bool,
) {
    let _ = in_async;
    for statement in statements {
        match statement.data() {
            Statement::Class(class) => {
                features.insert(LanguageFeature::Classes);
                scan_class(file, class, options, features, diagnostics);
            }
            Statement::Function(function) => {
                scan_function(
                    file,
                    &function.function,
                    statement.range(),
                    options,
                    features,
                    diagnostics,
                );
            }
            Statement::Variable(declaration) => {
                if matches!(
                    declaration.kind,
                    VariableKind::Using | VariableKind::AwaitUsing
                ) {
                    features.insert(LanguageFeature::Using);
                }
                for declarator in &declaration.declarations {
                    scan_pattern(declarator.data().binding.data(), features);
                    if let Some(initializer) = declarator.data().initializer.as_deref() {
                        scan_expression(initializer, features);
                    }
                }
            }
            Statement::Expression(expr) => scan_expression(&expr.expression, features),
            Statement::If(value) => {
                scan_expression(&value.test, features);
                scan_nested_statements(std::slice::from_ref(value.consequent.as_ref()), features);
                if let Some(alternate) = value.alternate.as_deref() {
                    scan_nested_statements(std::slice::from_ref(alternate), features);
                }
            }
            Statement::While(value) => {
                scan_expression(&value.test, features);
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::DoWhile(value) => {
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
                scan_expression(&value.test, features);
            }
            Statement::With(value) => {
                scan_expression(&value.object, features);
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::Labeled(value) => {
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::Return(ret) => {
                if let Some(argument) = ret.argument.as_deref() {
                    scan_expression(argument, features);
                }
            }
            Statement::Throw(value) => scan_expression(&value.argument, features),
            Statement::For(value) => {
                if let Some(ForInitializer::Expression(initializer)) = &value.initializer {
                    scan_expression(initializer, features);
                }
                if let Some(test) = value.test.as_deref() {
                    scan_expression(test, features);
                }
                if let Some(update) = value.update.as_deref() {
                    scan_expression(update, features);
                }
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::ForIn(for_in) => {
                scan_expression(&for_in.object, features);
                scan_nested_statements(std::slice::from_ref(for_in.body.as_ref()), features);
            }
            Statement::ForOf(for_of) => {
                if for_of.mode == ForOfMode::Async {
                    features.insert(LanguageFeature::AsyncIteration);
                }
                scan_expression(&for_of.iterable, features);
                scan_nested_statements(std::slice::from_ref(for_of.body.as_ref()), features);
            }
            Statement::Switch(value) => {
                scan_expression(&value.discriminant, features);
                for case in &value.cases {
                    if let Some(test) = case.data().test.as_deref() {
                        scan_expression(test, features);
                    }
                    scan_nested_statements(&case.data().consequent, features);
                }
            }
            Statement::Try(value) => {
                scan_nested_statements(&value.block.data().statements, features);
                if let Some(handler) = &value.handler {
                    scan_nested_statements(&handler.data().body.data().statements, features);
                }
                if let Some(finalizer) = &value.finalizer {
                    scan_nested_statements(&finalizer.data().statements, features);
                }
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => scan_statements(
                file,
                std::slice::from_ref(inner),
                options,
                features,
                diagnostics,
                in_async,
            ),
            Statement::Export(ExportDeclaration::Default(default)) => {
                if let ExportDefaultValue::Class(class) = &default.value {
                    features.insert(LanguageFeature::Classes);
                    scan_class(file, class, options, features, diagnostics);
                } else if let ExportDefaultValue::Expression(value) = &default.value {
                    scan_expression(value, features);
                }
            }
            Statement::Block(block) => {
                scan_statements(
                    file,
                    &block.data().statements,
                    options,
                    features,
                    diagnostics,
                    in_async,
                );
            }
            _ => {}
        }
    }
}

fn scan_class(
    file: &SourceFile,
    class: &ClassDeclaration,
    options: &TransformOptions,
    features: &mut BTreeSet<LanguageFeature>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Some(heritage) = &class.extends {
        scan_expression(&heritage.expression, features);
    }
    for member in &class.members {
        match member.data() {
            ClassMember::Property(property) => {
                if !property.modifiers.is_declare && !property.modifiers.is_abstract {
                    features.insert(LanguageFeature::ClassFields);
                }
                scan_computed_name(&property.name, features);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expression(initializer, features);
                }
                if matches!(property.name, PropertyName::Private(_))
                    && !options.target.supports(LanguageFeature::ClassFields)
                {
                    diagnostics.push(Diagnostic::error(
                        codes::PRIVATE_FIELD_REQUIRES_ES2022,
                        file.source_id(),
                        member.range(),
                        "private class fields require ScriptTarget::Es2022 or later",
                    ));
                }
            }
            ClassMember::Method(method) => {
                scan_function(
                    file,
                    &method.function,
                    member.range(),
                    options,
                    features,
                    diagnostics,
                );
            }
            ClassMember::AutoAccessor(accessor) => {
                features.insert(LanguageFeature::ClassFields);
                scan_computed_name(&accessor.name, features);
                if let Some(initializer) = accessor.initializer.as_deref() {
                    scan_expression(initializer, features);
                }
                if !options.target.supports(LanguageFeature::ClassFields) {
                    diagnostics.push(Diagnostic::error(
                        codes::AUTO_ACCESSOR_REQUIRES_ES2022,
                        file.source_id(),
                        member.range(),
                        "auto-accessors require ScriptTarget::Es2022 or later",
                    ));
                }
            }
            ClassMember::StaticBlock(block) => {
                features.insert(LanguageFeature::ClassFields);
                scan_statements(
                    file,
                    &block.data().statements,
                    options,
                    features,
                    diagnostics,
                    false,
                );
            }
            _ => {}
        }
    }
}

fn scan_function(
    file: &SourceFile,
    function: &FunctionLike,
    _range: TextRange,
    options: &TransformOptions,
    features: &mut BTreeSet<LanguageFeature>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if function.is_async {
        features.insert(LanguageFeature::AsyncFunctions);
    }
    if function.is_generator {
        features.insert(LanguageFeature::Generators);
    }
    for parameter in &function.parameters {
        scan_pattern(parameter.data().binding.data(), features);
        if let Some(initializer) = parameter.data().initializer.as_deref() {
            scan_expression(initializer, features);
        }
    }
    match function.body.as_ref() {
        Some(FunctionBody::Block(body)) => scan_statements(
            file,
            &body.data().statements,
            options,
            features,
            diagnostics,
            function.is_async,
        ),
        Some(FunctionBody::Expression(expression)) => scan_expression(expression, features),
        Some(FunctionBody::Missing(_)) | None => {}
    }
}

fn scan_pattern(pattern: &BindingPattern, features: &mut BTreeSet<LanguageFeature>) {
    match pattern {
        BindingPattern::Object(_) | BindingPattern::Array(_) => {
            features.insert(LanguageFeature::Destructuring);
        }
        BindingPattern::Rest(_) => {
            features.insert(LanguageFeature::ObjectRestSpread);
            features.insert(LanguageFeature::Destructuring);
        }
        _ => {}
    }
}

/// Recursively scans one expression for exponentiation syntax. The deep walk
/// intentionally reports only [`LanguageFeature::Exponentiation`]: every other
/// feature keeps the statement-level analysis surface this module has always
/// exposed, and only exponentiation is lowered in every expression position
/// the rewriter visits.
fn scan_expression(expression: &Expr, features: &mut BTreeSet<LanguageFeature>) {
    match expression.data() {
        Expression::Binary(value) => {
            scan_expression(&value.left, features);
            if value.operator == BinaryOperator::Exponentiate {
                features.insert(LanguageFeature::Exponentiation);
            }
            scan_expression(&value.right, features);
        }
        Expression::Assignment(value) => {
            scan_target(value.left.data(), features);
            if value.operator == AssignmentOperator::ExponentiateAssign {
                features.insert(LanguageFeature::Exponentiation);
            }
            if matches!(
                value.operator,
                AssignmentOperator::LogicalAndAssign
                    | AssignmentOperator::LogicalOrAssign
                    | AssignmentOperator::NullishAssign
            ) {
                features.insert(LanguageFeature::LogicalAssignment);
            }
            scan_expression(&value.right, features);
        }
        Expression::Template(value) => {
            for expression in &value.expressions {
                scan_expression(expression, features);
            }
        }
        Expression::TaggedTemplate(value) => {
            scan_expression(&value.tag, features);
            for expression in &value.template.expressions {
                scan_expression(expression, features);
            }
        }
        Expression::Array(value) => {
            for element in &value.elements {
                if let ArrayElement::Expression(expression) = element {
                    scan_expression(expression, features);
                }
            }
        }
        Expression::Object(value) => {
            for member in &value.members {
                match member.data() {
                    ObjectMember::Property(property) => {
                        scan_computed_name(&property.name, features);
                        scan_expression(&property.value, features);
                    }
                    ObjectMember::Method(method) => {
                        scan_computed_name(&method.name, features);
                        scan_parameter_defaults(&method.function.parameters, features);
                        scan_nested_body(method.function.body.as_ref(), features);
                    }
                    ObjectMember::Spread(spread) => scan_expression(&spread.argument, features),
                    ObjectMember::Missing(_) => {}
                }
            }
        }
        Expression::Function(value) => {
            scan_parameter_defaults(&value.function.parameters, features);
            scan_nested_body(value.function.body.as_ref(), features);
        }
        Expression::Class(value) => scan_class_expressions(&value.class, features),
        Expression::Arrow(value) => {
            scan_parameter_defaults(&value.parameters, features);
            scan_nested_body(Some(&value.body), features);
        }
        Expression::Call(value) => {
            if value.optional {
                features.insert(LanguageFeature::OptionalChaining);
            }
            scan_expression(&value.callee, features);
            for argument in &value.arguments {
                match argument {
                    CallArgument::Expression(expression) => scan_expression(expression, features),
                    CallArgument::Spread(spread) => scan_expression(&spread.argument, features),
                    CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Member(value) => {
            if value.optional {
                features.insert(LanguageFeature::OptionalChaining);
            }
            scan_expression(&value.object, features);
            if let MemberProperty::Computed(key) = &value.property {
                scan_expression(key, features);
            }
        }
        Expression::New(value) => {
            scan_expression(&value.callee, features);
            for argument in &value.arguments {
                match argument {
                    CallArgument::Expression(expression) => scan_expression(expression, features),
                    CallArgument::Spread(spread) => scan_expression(&spread.argument, features),
                    CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Await(value) => scan_expression(&value.argument, features),
        Expression::Yield(value) => {
            if let Some(argument) = value.argument.as_deref() {
                scan_expression(argument, features);
            }
        }
        Expression::Unary(value) => scan_expression(&value.argument, features),
        Expression::Update(value) => scan_target(value.argument.data(), features),
        Expression::Logical(value) => {
            if value.operator == LogicalOperator::Nullish {
                features.insert(LanguageFeature::NullishCoalescing);
            }
            scan_expression(&value.left, features);
            scan_expression(&value.right, features);
        }
        Expression::Conditional(value) => {
            scan_expression(&value.test, features);
            scan_expression(&value.consequent, features);
            scan_expression(&value.alternate, features);
        }
        Expression::Sequence(value) => {
            for expression in &value.expressions {
                scan_expression(expression, features);
            }
        }
        Expression::Parenthesized(value) => scan_expression(value, features),
        Expression::As(value) => scan_expression(&value.expression, features),
        Expression::Satisfies(value) => scan_expression(&value.expression, features),
        Expression::TypeAssertion(value) => scan_expression(&value.expression, features),
        Expression::NonNull(value) => scan_expression(&value.expression, features),
        Expression::Import(value) => {
            scan_expression(&value.source, features);
            if let Some(options) = value.options.as_deref() {
                scan_expression(options, features);
            }
        }
        // JSX trees print through the JSX desugar plan, which owns their
        // expression containers, so the transform walk never visits them.
        _ => {}
    }
}

/// Recursively scans an assignment target for exponentiation syntax.
fn scan_target(target: &AssignmentTarget, features: &mut BTreeSet<LanguageFeature>) {
    match target {
        AssignmentTarget::Member(member) => {
            scan_expression(&member.object, features);
            if let MemberProperty::Computed(key) = &member.property {
                scan_expression(key, features);
            }
        }
        AssignmentTarget::Object(pattern) => {
            for property in &pattern.properties {
                scan_computed_name(&property.name, features);
                scan_target(property.target.data(), features);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expression(initializer, features);
                }
            }
        }
        AssignmentTarget::Array(pattern) => {
            for element in &pattern.elements {
                if let AssignmentArrayElement::Target(inner) = element {
                    scan_target(inner.data(), features);
                }
            }
        }
        AssignmentTarget::Identifier(_) | AssignmentTarget::Missing(_) => {}
        AssignmentTarget::Invalid(operand) => {
            scan_expression(operand, features);
        }
    }
}

/// Scans a property name for exponentiation inside a computed key.
fn scan_computed_name(name: &PropertyName, features: &mut BTreeSet<LanguageFeature>) {
    if let PropertyName::Computed(key) = name {
        scan_expression(key, features);
    }
}

/// Scans parameter default values for exponentiation syntax.
fn scan_parameter_defaults(parameters: &[ParameterNode], features: &mut BTreeSet<LanguageFeature>) {
    for parameter in parameters {
        if let Some(initializer) = parameter.data().initializer.as_deref() {
            scan_expression(initializer, features);
        }
    }
}

/// Scans a nested function body for exponentiation syntax.
fn scan_nested_body(body: Option<&FunctionBody>, features: &mut BTreeSet<LanguageFeature>) {
    match body {
        Some(FunctionBody::Block(block)) => {
            scan_nested_statements(&block.data().statements, features);
        }
        Some(FunctionBody::Expression(expression)) => scan_expression(expression, features),
        Some(FunctionBody::Missing(_)) | None => {}
    }
}

/// Exponentiation-only statement walk for bodies the rewriter descends into
/// from expression position (nested functions, arrows, object methods).
fn scan_nested_statements(statements: &[Stmt], features: &mut BTreeSet<LanguageFeature>) {
    for statement in statements {
        match statement.data() {
            Statement::Variable(declaration) => {
                for declarator in &declaration.declarations {
                    if let Some(initializer) = declarator.data().initializer.as_deref() {
                        scan_expression(initializer, features);
                    }
                }
            }
            Statement::Expression(expr) => scan_expression(&expr.expression, features),
            Statement::Return(ret) => {
                if let Some(argument) = ret.argument.as_deref() {
                    scan_expression(argument, features);
                }
            }
            Statement::Throw(value) => scan_expression(&value.argument, features),
            Statement::If(value) => {
                scan_expression(&value.test, features);
                scan_nested_statements(std::slice::from_ref(value.consequent.as_ref()), features);
                if let Some(alternate) = value.alternate.as_deref() {
                    scan_nested_statements(std::slice::from_ref(alternate), features);
                }
            }
            Statement::While(value) => {
                scan_expression(&value.test, features);
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::DoWhile(value) => {
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
                scan_expression(&value.test, features);
            }
            Statement::With(value) => {
                scan_expression(&value.object, features);
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::Labeled(value) => {
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::For(value) => {
                if let Some(ForInitializer::Expression(initializer)) = &value.initializer {
                    scan_expression(initializer, features);
                }
                if let Some(test) = value.test.as_deref() {
                    scan_expression(test, features);
                }
                if let Some(update) = value.update.as_deref() {
                    scan_expression(update, features);
                }
                scan_nested_statements(std::slice::from_ref(value.body.as_ref()), features);
            }
            Statement::ForIn(for_in) => {
                scan_expression(&for_in.object, features);
                scan_nested_statements(std::slice::from_ref(for_in.body.as_ref()), features);
            }
            Statement::ForOf(for_of) => {
                scan_expression(&for_of.iterable, features);
                scan_nested_statements(std::slice::from_ref(for_of.body.as_ref()), features);
            }
            Statement::Switch(value) => {
                scan_expression(&value.discriminant, features);
                for case in &value.cases {
                    if let Some(test) = case.data().test.as_deref() {
                        scan_expression(test, features);
                    }
                    scan_nested_statements(&case.data().consequent, features);
                }
            }
            Statement::Try(value) => {
                scan_nested_statements(&value.block.data().statements, features);
                if let Some(handler) = &value.handler {
                    scan_nested_statements(&handler.data().body.data().statements, features);
                }
                if let Some(finalizer) = &value.finalizer {
                    scan_nested_statements(&finalizer.data().statements, features);
                }
            }
            Statement::Function(function) => {
                scan_parameter_defaults(&function.function.parameters, features);
                scan_nested_body(function.function.body.as_ref(), features);
            }
            Statement::Class(class) => scan_class_expressions(class, features),
            Statement::Block(block) => {
                scan_nested_statements(&block.data().statements, features);
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => scan_nested_statements(std::slice::from_ref(inner), features),
            Statement::Export(ExportDeclaration::Default(default)) => {
                if let ExportDefaultValue::Expression(value) = &default.value {
                    scan_expression(value, features);
                }
            }
            _ => {}
        }
    }
}

/// Exponentiation-only walk over the expression positions of one class.
fn scan_class_expressions(class: &ClassDeclaration, features: &mut BTreeSet<LanguageFeature>) {
    if let Some(heritage) = &class.extends {
        scan_expression(&heritage.expression, features);
    }
    for member in &class.members {
        match member.data() {
            ClassMember::Property(property) => {
                scan_computed_name(&property.name, features);
                if let Some(initializer) = property.initializer.as_deref() {
                    scan_expression(initializer, features);
                }
            }
            ClassMember::Method(method) => {
                scan_computed_name(&method.name, features);
                scan_parameter_defaults(&method.function.parameters, features);
                scan_nested_body(method.function.body.as_ref(), features);
            }
            ClassMember::AutoAccessor(accessor) => {
                scan_computed_name(&accessor.name, features);
                if let Some(initializer) = accessor.initializer.as_deref() {
                    scan_expression(initializer, features);
                }
            }
            ClassMember::StaticBlock(block) => {
                scan_nested_statements(&block.data().statements, features);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{LanguageFeature, ScriptTarget, analyze, codes, emit_transformed};
    use crate::checker;
    use crate::diagnostic::Recovered;
    use crate::emitter::{EmitFileNames, EmitOptions, EmitOutput, ModuleKind};
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use std::sync::Arc;

    fn parse(source: &str) -> crate::syntax::SourceFile {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("test source fits the per-file source budget")),
        ))
        .into_product()
    }

    fn names() -> EmitFileNames {
        EmitFileNames {
            source_name: Arc::from("input.ts"),
            js_file_name: Some(Arc::from("output.js")),
            declaration_file_name: Some(Arc::from("output.d.ts")),
            source_root: None,
            ..EmitFileNames::default()
        }
    }

    fn options_for(target: ScriptTarget) -> EmitOptions {
        EmitOptions {
            target,
            ..EmitOptions::default()
        }
    }

    fn emit_at(source: &str, target: ScriptTarget) -> EmitOutput {
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(target);
        emit_transformed(
            &file,
            checked.product(),
            &options.transform_view(),
            &names(),
        )
    }

    fn emit_with_options(source: &str, options: EmitOptions) -> EmitOutput {
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        emit_transformed(
            &file,
            checked.product(),
            &options.transform_view(),
            &names(),
        )
    }

    fn javascript(output: &EmitOutput) -> &str {
        &output.javascript.as_ref().expect("JavaScript output").code
    }

    #[test]
    fn dense_million_node_file_keeps_authored_preservation_unaliased() {
        // The rewriter's id source is seeded past the parser high-water
        // (and any JSX-desugar consumption), so minted ids are disjoint
        // from authored ids BY CONSTRUCTION — the structural fix for the
        // old constant floor. This pins the observable consequences on a
        // dense million-node file: emit completes, no statements drop,
        // authored single-line preservation holds, and field lowering
        // still mints its descriptors.
        let mut statements = 330_000usize;
        let tail = "function probe() { return 1; }\nclass K { }";
        // Grow the prefix until the parser high-water crosses 1_000_100:
        // node yield per statement amortizes, so calibrate on the real
        // construction rather than a small sample.
        let high_water = loop {
            let probe = format!("{}{tail}", "a;".repeat(statements));
            let water = parse(&probe).id().get();
            if water >= 1_000_400 || statements > 600_000 {
                break water;
            }
            statements += 2_000;
        };
        let mut source = String::with_capacity(2_000_000);
        source.push_str(&"a;".repeat(statements));
        source.push_str("function probe() { return 1; }\n");
        source.push_str("class K { ");
        for i in 0..60 {
            source.push_str(&format!("f{i} = 1; "));
        }
        source.push_str("}\n");
        assert!(
            (1_000_350..=1_004_500).contains(&high_water),
            "calibration drifted: high water {high_water}"
        );
        let output = emit_with_options(
            &source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("function probe() { return 1; }"),
            "authored single-line body lost preservation"
        );
        assert!(
            code.contains("enumerable: true"),
            "descriptor lowering missing"
        );
    }

    #[test]
    fn esnext_keeps_async_and_class_fields() {
        let source = "class C { x = 1; }\nasync function f() { return await 1; }\n";
        let output = emit_at(source, ScriptTarget::EsNext);
        let code = javascript(&output);
        assert!(code.contains("x = 1"), "{code}");
        assert!(code.contains("async function"), "{code}");
        assert!(!code.contains("__awaiter"), "{code}");
    }

    #[test]
    fn es2015_downlevels_class_fields_into_the_constructor() {
        let output = emit_at("class C { x = 1; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("constructor"), "{code}");
        assert!(code.contains("this.x = 1"), "{code}");
        assert!(
            !code.lines().any(|line| line.trim() == "x = 1;"),
            "field initializer should move: {code}"
        );
    }
    #[test]
    fn require_locals_follow_the_tsc_slug_shape() {
        // tsc binds `enum_1` for an identifier-starting slug and
        // `_10_lib_1` when a leading digit forces sanitization.
        let mut names = super::RequireNames::new(std::collections::BTreeSet::new());
        assert_eq!(names.allocate("./enum"), "enum_1");
        assert_eq!(names.allocate("./10_lib"), "_10_lib_1");
        assert_eq!(names.allocate("./enum"), "enum_2");
    }

    #[test]
    fn class_expression_without_lowering_stays_inline() {
        // Authority: classExpressionTest2 — a generic class expression with
        // no lowered members emits inline with type parameters stripped
        // (`var m = class C {`), never a temp-IIFE wrap.
        let output = emit_at(
            "function M() {\n    var m = class C<X> { f() { return 1; } };\n    return new m();\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("var m = class C {"), "{code}");
        assert!(!code.contains("(() =>"), "{code}");
    }

    #[test]
    fn derived_class_fields_follow_super_and_literal_names_are_preserved() {
        let output = emit_at(
            r#"class C extends B { "x" = 1; 2 = 3; constructor() { super(); after(); } }
"#,
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let super_at = code
            .find("super()")
            .expect("derived constructor calls super");
        let string_at = code.find(r#"this["x"] = 1"#).expect("string field name");
        let number_at = code.find("this[2] = 3").expect("numeric field name");
        let after_at = code.find("after()").expect("original constructor body");
        assert!(
            super_at < string_at && string_at < number_at && number_at < after_at,
            "{code}"
        );
    }

    #[test]
    fn synthesized_derived_constructor_forwards_arguments_before_fields() {
        let output = emit_at("class C extends B { x = 1; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(code.contains("super(...arguments)"), "{code}");
        assert!(
            code.find("super(...arguments)").unwrap() < code.find("this.x = 1").unwrap(),
            "{code}"
        );
    }
    #[test]
    fn uninitialized_fields_emit_nothing_under_assignment_semantics() {
        // Baseline computedPropertyNames36_ES5(target=es2015).js keeps
        // `class Foo {\n}` for `class Foo { x }`: assignment semantics
        // define nothing for a declaration without an initializer.
        let output = emit_at("class C { x; static y; }\n", ScriptTarget::Es2015);
        let code = javascript(&output);
        assert!(!code.contains("constructor"), "{code}");
        assert!(!code.contains("void 0"), "{code}");
        assert!(code.contains("class C {"), "{code}");
    }

    #[test]
    fn uninitialized_fields_define_void_0_under_define_semantics() {
        let output = emit_with_options(
            "class C { x; static y; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("Object.defineProperty(this, \"x\""), "{code}");
        assert!(code.contains("Object.defineProperty(C, \"y\""), "{code}");
        assert!(code.contains("void 0"), "{code}");
        assert!(!code.contains("this.x ="), "{code}");
    }

    #[test]
    fn computed_field_names_are_evaluated_once_at_class_definition() {
        let output = emit_at(
            "class C { [key()] = 1; } new C(); new C();\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert!(code.contains("let _t0 = key()"), "{code}");
        assert!(code.contains("this[_t0] = 1"), "{code}");
    }
    #[test]
    fn computed_keys_preserve_heritage_and_member_evaluation_order() {
        let output = emit_at(
            "class C extends heritage() { [field()] = 1; [method()]() {} [later()] = 2; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let heritage = code.find("heritage()").expect("heritage evaluation");
        let field = code.find("field()").expect("first computed field");
        let method = code.find("method()").expect("computed method");
        let later = code.find("later()").expect("later computed field");
        let class = code.find("class C extends _t0").expect("rewritten class");
        assert!(
            heritage < field && field < method && method < later && later < class,
            "{code}"
        );
        assert!(code.contains("this[_t1] = 1"), "{code}");
        assert!(code.contains("[_t2]()"), "{code}");
        assert!(code.contains("this[_t3] = 2"), "{code}");
    }
    #[test]
    fn static_computed_field_runs_key_and_value_and_assigns_the_property() {
        let output = emit_at(
            "class C { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
        let key = code.find("let _t0 = key()").expect("key setup");
        let class = code.find("class C").expect("class declaration");
        let assignment = code
            .find("C[_t0] = value()")
            .expect("post-class static property assignment");
        assert!(key < class && class < assignment, "{code}");
    }
    #[test]
    fn named_export_wraps_only_the_lowered_class() {
        let output = emit_at(
            "export class C { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _t0 = key()").expect("ordinary key prelude");
        let class = code
            .find("export class C")
            .expect("exported rewritten class");
        let postlude = code
            .find("C[_t0] = value()")
            .expect("ordinary static postlude");
        assert!(prelude < class && class < postlude, "{code}");
        assert!(!code.contains("export let _t0"), "{code}");
        assert!(!code.contains("export C[_t0]"), "{code}");
    }

    #[test]
    fn named_default_export_keeps_class_and_generated_statements_separate() {
        let output = emit_at(
            "export default class C { field = 1; static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _t0 = key()").expect("ordinary key prelude");
        let class = code
            .find("export default class C")
            .expect("named default class");
        let postlude = code
            .find("C[_t0] = value()")
            .expect("ordinary static postlude");
        assert!(prelude < class && class < postlude, "{code}");
        assert!(code.contains("this.field = 1"), "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
        assert!(!code.contains("export default let"), "{code}");
    }

    #[test]
    fn anonymous_default_export_lowers_instance_fields_in_place() {
        let output = emit_at(
            "export default class { field = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("export default class"), "{code}");
        assert!(code.contains("constructor"), "{code}");
        assert!(code.contains("this.field = 1"), "{code}");
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code() == codes::STATIC_FIELD_REQUIRES_CLASS_NAME }),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn anonymous_default_static_field_uses_one_synthetic_class_target() {
        let output = emit_at(
            "export default class { static [key()] = value(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let prelude = code.find("let _t1 = key()").expect("ordinary key prelude");
        let class = code
            .find("export default class _t0")
            .expect("synthetically named default class");
        let postlude = code
            .find("_t0[_t1] = value()")
            .expect("static assignment uses synthetic class name");
        assert!(prelude < class && class < postlude, "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("value()").count(), 1, "{code}");
    }
    #[test]
    fn anonymous_default_static_class_restores_imported_name_to_default() {
        let output = emit_at(
            "export default class { static x = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let class = code
            .find("export default class _t0")
            .expect("synthetically named default class");
        let restore = code
            .find(r#"Object.defineProperty(_t0, "name""#)
            .expect("default name restoration");
        let static_assignment = code
            .find("_t0.x = 1")
            .expect("post-class static assignment");
        assert!(class < restore && restore < static_assignment, "{code}");
        assert!(code.contains(r#"value: "default""#), "{code}");
        assert!(code.contains("configurable: true"), "{code}");
    }

    #[test]
    fn es2015_downlevels_async_to_awaiter() {
        // Authority: es5-importHelpersAsyncFunctions(target=es2015).js emits
        // the awaiter alone — native generators need no __generator.
        let output = emit_at(
            "async function f(x) { return await x; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("__awaiter"), "{code}");
        assert!(code.contains("function*"), "{code}");
        assert!(code.contains("yield"), "{code}");
        assert!(!code.contains("async "), "{code}");
        assert!(
            code.contains("var __awaiter = (this && this.__awaiter) || function"),
            "{code}"
        );
        assert!(!code.contains("__generator"), "{code}");
    }

    #[test]
    fn helper_emission_uses_rewriter_demand_not_analysis_prediction() {
        // Authority: es5-importHelpersAsyncFunctions(target=es2015).js.
        let source = "function outer() { return async () => await 1; }\n";
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(ScriptTarget::Es2015);
        let transform_options = options.transform_view();
        let plan = analyze(&file, &transform_options);
        assert!(
            plan.helpers.is_empty(),
            "fixture must remain outside the shallow analysis walk"
        );

        let output = emit_transformed(&file, checked.product(), &transform_options, &names());
        let code = javascript(&output);
        assert!(
            code.contains("var __awaiter = (this && this.__awaiter) || function"),
            "{code}"
        );
        assert!(
            !code.contains("__generator"),
            "native-generator targets emit no __generator: {code}"
        );
    }

    #[test]
    fn es5_downlevels_object_destructuring() {
        let output = emit_at("const { a, b } = o;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("a = "), "{code}");
        assert!(code.contains("b = "), "{code}");
        assert!(!code.contains("{ a, b }"), "{code}");
    }

    #[test]
    fn private_fields_below_es2022_are_errors() {
        let output = emit_at("class C { #x = 1; }\n", ScriptTarget::Es2015);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::PRIVATE_FIELD_REQUIRES_ES2022),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn classes_below_es2015_are_errors() {
        let output = emit_at("class C {}\n", ScriptTarget::Es5);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::CLASS_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn using_declarations_are_errors_before_esnext() {
        let output = emit_at("using x = y;\n", ScriptTarget::Es2022);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == codes::USING_UNSUPPORTED),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn static_fields_and_blocks_remain_interleaved() {
        let output = emit_at(
            "class C { static a = one(); static { step(); } static b = two(); }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let first = code.find("C.a = one()").expect("first static field");
        let block = code.find("step()").expect("static block");
        let second = code.find("C.b = two()").expect("second static field");
        assert!(first < block && block < second, "{code}");
        assert!(!code.contains("static {"), "{code}");
    }

    #[test]
    fn define_mode_uses_complete_data_descriptors() {
        let output = emit_with_options(
            "class C { x = 1; static y = 2; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("Object.defineProperty(this, \"x\""), "{code}");
        assert!(code.contains("Object.defineProperty(C, \"y\""), "{code}");
        let enumerable = code
            .find("enumerable: true")
            .expect("enumerable descriptor");
        let configurable = code
            .find("configurable: true")
            .expect("configurable descriptor");
        let writable = code.find("writable: true").expect("writable descriptor");
        let value = code.find("value: 1").expect("descriptor value");
        assert!(
            enumerable < configurable && configurable < writable && writable < value,
            "{code}"
        );
    }

    #[test]
    fn synthesized_descriptor_object_expands_in_javascript() {
        // Authority: override18(target=es2015).js — the defineProperty
        // descriptor is wholly synthesized and prints multi-line even when
        // the authored source is compact. An untainted mint collapsed it
        // onto one line (sweep-2d76b09 regression).
        let output = emit_with_options(
            "class A { foo?: string; }\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                use_define_for_class_fields: Some(true),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.contains("Object.defineProperty(this, \"foo\", {\n            enumerable: true,"),
            "{code}"
        );
        assert!(!code.contains("{ enumerable: true, configurable"), "{code}");
    }

    #[test]
    fn declare_and_abstract_fields_have_no_runtime_initializers() {
        let output = emit_at(
            "abstract class C { declare x: number; abstract y: string; z = 1; }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(!code.contains("this.x"), "{code}");
        assert!(!code.contains("this.y"), "{code}");
        assert!(code.contains("this.z = 1"), "{code}");
    }

    #[test]
    fn nested_super_sites_receive_fields_after_each_completion() {
        let output = emit_at(
            "class C extends B { x = 1; constructor(flag) { if (flag) super(1); else { super(2); } } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("this.x = 1").count(), 2, "{code}");
        let first_super = code.find("super(1)").expect("first super");
        let first_init = code.find("this.x = 1").expect("first init");
        assert!(first_super < first_init, "{code}");
    }

    #[test]
    fn class_expressions_lower_inside_call_arguments() {
        let output = emit_at(
            "consume(class { static x = 1; y = 2; });\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("consume((() =>"), "{code}");
        assert!(code.contains("this.y = 2"), "{code}");
        assert!(code.contains(".x = 1"), "{code}");
        assert!(!code.contains("static x"), "{code}");
    }

    #[test]
    fn native_declaration_emits_suspending_class_key_prelude_in_order() {
        let output = emit_at(
            "function* g() { const left = before(), C = class { [yield key()]() {} }, right = after(); }\n",
            ScriptTarget::Es2015,
        );
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let code = javascript(&output);
        let positions = ["before()", "key()", "C =", "after()"].map(|needle| {
            assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
            code.find(needle).expect("emitted expression")
        });
        assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
    }

    #[test]
    fn static_this_and_super_are_rebound_to_the_constructor() {
        let output = emit_at(
            "class B { static p() {} } class C extends B { static x = this; static { super.p(); } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("C.x = C"), "{code}");
        assert!(
            code.contains("Reflect.get(Object.getPrototypeOf(C), \"p\", C).call(C)"),
            "{code}"
        );
    }

    #[test]
    fn static_block_only_source_is_detected_as_class_fields() {
        let file = parse("class C { static { run(); } }\n");
        let options = options_for(ScriptTarget::Es2015).transform_view();
        let plan = analyze(&file, &options);
        assert!(plan.features.contains(&LanguageFeature::ClassFields));
        assert!(plan.required.contains(&LanguageFeature::ClassFields));
    }
    #[test]
    fn nested_static_blocks_rewrite_this_through_control_flow() {
        let output = emit_at(
            "class C { static { if (flag) { for (; once(); ) { this.x = this; break; } } try { throw this; } catch (e) { this.y = e; } finally { this.z = this; } } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("C.x = C"), "{code}");
        assert!(code.contains("throw C"), "{code}");
        assert!(code.contains("C.y = e"), "{code}");
        assert!(code.contains("C.z = C"), "{code}");
    }

    #[test]
    fn static_super_writes_use_reflect_with_single_evaluation() {
        let output = emit_at(
            "class B { static get x() { return 1; } static set x(v) {} } class C extends B { static { super.x = rhs(); super[key()] += more(); } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(!code.contains("super.x ="), "{code}");
        assert!(!code.contains("super[key()]"), "{code}");
        assert_eq!(code.matches("key()").count(), 1, "{code}");
        assert_eq!(code.matches("rhs()").count(), 1, "{code}");
        assert_eq!(code.matches("more()").count(), 1, "{code}");
        assert!(code.matches("Reflect.set(").count() >= 2, "{code}");
        assert!(code.contains("Reflect.get("), "{code}");
    }

    #[test]
    fn node_executes_nested_static_super_writes() {
        let source = r#"
const log = [];
function key() { log.push("key"); return "x"; }
function rhs() { log.push("rhs"); return 3; }
class B {
  static get x() { log.push("get"); return this._x ?? 1; }
  static set x(value) { log.push("set"); this._x = value; }
}
class C extends B {
  static {
    if (true) {
      super.x = 2;
      try { super[key()] += rhs(); this.self = this; }
      finally { this.done = true; }
    }
  }
}
console.log(JSON.stringify([C._x, log, C.self === C, C.done]));
"#;
        let output = emit_at(source, ScriptTarget::Es2015);
        let code = javascript(&output);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-static-super-{nonce}.mjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).expect("Node stdout"),
            "[5,[\"set\",\"key\",\"get\",\"rhs\",\"set\"],true,true]\n"
        );
    }

    #[test]
    fn analysis_is_deterministic_and_lists_required_features() {
        let file = parse("async function f() { const { a } = x; }\n");
        let options = options_for(ScriptTarget::Es5).transform_view();
        let left = analyze(&file, &options);
        let right = analyze(&file, &options);
        assert_eq!(left, right);
        assert!(left.required.contains(&LanguageFeature::AsyncFunctions));
        assert!(left.required.contains(&LanguageFeature::Destructuring));
    }

    #[test]
    fn strict_prologue_follows_always_strict_and_module_kind() {
        // A top-level external module takes the prologue exactly when it is
        // transpiled to CommonJS; under ES module output it takes none even
        // with alwaysStrict on (673 baselines). Scripts follow alwaysStrict
        // alone, as conformance pairs like arrowFunctionContexts(alwaysstrict=...)
        // show.
        let module = emit_with_options(
            "export const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert!(
            javascript(&module).starts_with("\"use strict\";\n"),
            "a CommonJS external module implies strict: {}",
            javascript(&module)
        );
        let es_module = emit_with_options(
            "export const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::Es2015),
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&es_module).starts_with("\"use strict\";\n"),
            "an ES external module takes no prologue even under alwaysStrict: {}",
            javascript(&es_module)
        );
        let commonjs_script = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&commonjs_script).starts_with("\"use strict\";\n"),
            "a script under CommonJS still follows alwaysStrict: {}",
            javascript(&commonjs_script)
        );
        let script = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                ..EmitOptions::default()
            },
        );
        assert!(
            !javascript(&script).starts_with("\"use strict\";\n"),
            "a plain script has no prologue: {}",
            javascript(&script)
        );
        let always = emit_with_options(
            "const value = 1;\n",
            EmitOptions {
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            javascript(&always).starts_with("\"use strict\";\n"),
            "alwaysStrict emits the prologue: {}",
            javascript(&always)
        );
        let deduped = emit_with_options(
            "\"use strict\";\nconst value = 1;\n",
            EmitOptions {
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&deduped);
        assert_eq!(
            code.matches("\"use strict\";").count(),
            1,
            "a source directive suppresses the synthetic one: {code}"
        );
    }

    #[test]
    fn ambient_enum_and_module_produce_no_runtime_statements() {
        // Upstream ambientEnumElementInitializer5 (43527a9c) emits only the
        // strict prologue; ambientModules (df2119af) keeps only the trailing
        // member assignment.
        let ambient_enum = emit_at("declare enum E { e = -0xA }\n", ScriptTarget::Es2015);
        assert_eq!(
            javascript(&ambient_enum),
            "",
            "{:?}",
            javascript(&ambient_enum)
        );

        let ambient_module = emit_at(
            "declare namespace Foo.Bar { export var foo; };\nFoo.Bar.foo = 5;\n",
            ScriptTarget::Es2015,
        );
        // The ambient declaration vanishes; the runtime assignment survives,
        // matching upstream ambientModules (df2119af) after the prologue.
        assert!(
            !javascript(&ambient_module).starts_with("declare")
                && !javascript(&ambient_module).contains("export var foo"),
            "the ambient block is erased: {}",
            javascript(&ambient_module)
        );

        let runtime = emit_at("const enum K { A }\nlet kept = 1;\n", ScriptTarget::Es2015);
        assert!(
            javascript(&runtime).contains("kept"),
            "non-ambient code survives: {}",
            javascript(&runtime)
        );
    }

    #[test]
    fn generic_call_type_arguments_are_erased() {
        // Upstream genericCallWithNonGenericArgs1 (e71ae63c): f<any>(null)
        // emits f(null);
        let output = emit_at(
            "function f<T>(x: any) { }\nf<any>(null);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("f(null);"), "{code}");
        assert!(!code.contains("<any>"), "{code}");
    }

    #[test]
    fn commonjs_named_import_and_function_export_match_upstream_shape() {
        // Upstream commonjsSafeImport(target=es2015).js
        // (282283386bc4040f0eba585ac33e142c5c30cfbb67f969b1706c655dc7bee408).
        let export = emit_with_options(
            "export function Foo() {}\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let export_code = javascript(&export);
        assert!(
            export_code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.Foo = Foo;\nfunction Foo()"
            ),
            "{export_code}"
        );

        let import = emit_with_options(
            "import { Foo } from './10_lib';\nFoo();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let import_code = javascript(&import);
        assert!(
            import_code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst _10_lib_1 = require(\"./10_lib\");\n"
            ),
            "{import_code}"
        );
        assert!(
            import_code.contains("(0, _10_lib_1.Foo)();"),
            "{import_code}"
        );
        assert!(!import_code.contains("import "), "{import_code}");
    }

    #[test]
    fn es5_lowers_nested_computed_destructuring_assignment() {
        // Upstream computedPropertiesInDestructuring1.js
        // (50845e031ebf8203c61d4bfb72d37eea703fea245df4e215c7b5772583a8a898).
        let output = emit_at(
            "let foo = 'bar', bar4; [{ [foo]: bar4 }] = [{ bar: 'bar' }];\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code()
                    == codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
        assert!(code.contains("bar4 ="), "{code}");
        assert!(code.contains("[foo]"), "{code}");
        assert!(!code.contains("[{ [foo]: bar4 }] ="), "{code}");
    }

    #[test]
    fn commonjs_class_and_variable_exports_receive_void_0_preamble() {
        // Upstream importHelpersWithImportStarAs a.js (a2836e68) emits
        // `exports.A = void 0;` + class + `exports.A = A;`; the variable form
        // follows es6ImportDefaultBindingWithExport client.js (adfd4388).
        let output = emit_with_options(
            "export class A {}\nexport const x = 1;\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.A = exports.x = void 0;\n"
            ),
            "{code}"
        );
        let marker = code
            .find("exports.A = exports.x = void 0;")
            .expect("preamble");
        let class_at = code.find("class A").expect("class kept");
        let class_export = code.find("exports.A = A;").expect("class export");
        let variable = code.find("const x = 1;").expect("variable kept");
        let variable_export = code.find("exports.x = x;").expect("variable export");
        assert!(
            marker < class_at
                && class_at < class_export
                && class_export < variable
                && variable < variable_export,
            "{code}"
        );
    }

    #[test]
    fn commonjs_local_specifier_exports_assign_each_name() {
        // Same `exports.NAME = LOCAL;` identifier-assignment form as the
        // identifier default export in es6ImportDefaultBindingWithExport
        // server.js (adfd4388): `exports.default = a;`.
        let output = emit_with_options(
            "const a = 1, b = 2;\nexport { a, b as c };\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("exports.a = a;"), "{code}");
        assert!(code.contains("exports.c = b;"), "{code}");
        assert!(!code.contains("export {"), "{code}");
    }

    #[test]
    fn commonjs_side_effect_imports_stay_as_require() {
        let output = emit_with_options(
            "import './polyfill';\nrun();\n",
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(code.contains("require(\"./polyfill\");"), "{code}");
        assert!(!code.contains("import "), "{code}");
    }

    #[test]
    fn node_executes_lowered_computed_destructuring_assignment() {
        // computedPropertiesInDestructuring1 (50845e03) pins the preserved
        // ES6 forms; this snapshot carries no ES5 blob, so the ES5 lowering
        // contract is pinned behaviorally: values, and one evaluation per
        // key/default in source order.
        let source = r#"
const log = [];
let foo = "bar";
let bar = 0, bar3 = 0, bar4 = 0;
function key() { log.push("key"); return foo; }
function rhs() { log.push("rhs"); return { bar: "set" }; }
({ [key()]: bar } = rhs());
[{ [key()]: bar4 }] = [{ bar: "nested" }];
console.log(JSON.stringify([bar, bar4, log]));
"#;
        let output = emit_at(source, ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            !output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code()
                    == codes::DESTRUCTURING_ASSIGNMENT_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
        // 3 = function definition `function key()` + 2 call sites (one per destructuring)
        assert_eq!(code.matches("key()").count(), 3, "{code}");
        // 2 = function definition `function rhs()` + 1 call site
        assert_eq!(code.matches("rhs()").count(), 2, "{code}");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-cpd-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout)
                .expect("Node stdout")
                .trim(),
            // Per spec, RHS evaluates before computed keys in destructuring assignment:
            // rhs() → key() → key()
            r#"["set","nested",["rhs","key","key"]]"#
        );
    }

    #[test]
    fn computed_destructuring_keys_evaluate_once_into_a_temp() {
        // Upstream computedPropertiesInDestructuring1 (50845e03) lowers
        // `let {[foo2()]: bar3} = ...` to a temp declaration plus a
        // bracket read, with the key evaluated exactly once.
        let output = emit_at(
            "const key = \"k\";\nconst { [key]: value } = { k: 1 };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        // ES5 temps are `var` (a `let` inside cloned machine bodies is a
        // SyntaxError at ES5); ES2015+ keeps the tighter `let` binding.
        assert!(code.contains("var _t"), "ES5 temp kind: {code}");
        assert!(!code.contains("let _t"), "ES5 temp kind: {code}");
        let key_read_at = code.find(" = key").expect("key temp declared");
        let temp_name: String = code[..key_read_at]
            .chars()
            .rev()
            .take_while(|character| character.is_ascii_alphanumeric() || *character == '_')
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        assert!(temp_name.starts_with("_t"), "key temp name: {code}");
        assert_eq!(
            code.matches(" = key").count(),
            1,
            "key evaluates once into a temp: {code}"
        );
        assert!(
            code.contains(&format!("[{temp_name}]")),
            "binding reads through the temp: {code}"
        );
    }

    #[test]
    fn derived_constructor_keeps_prologue_before_super() {
        // Upstream constructorWithSuperAndPrologue.es5 (1e40213a): the
        // "ngInject" directive stays in the body ahead of the super call and
        // the super call becomes `return _super.call(this) || this;`.
        let output = emit_at(
            "class B extends A {\n    constructor() {\n        \"ngInject\";\n        console.log(\"B\");\n        super();\n    }\n}\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        let directive = code.find("ngInject").expect("directive survives");
        let super_call = code.find("super(").expect("super call survives");
        assert!(directive < super_call, "{code}");
    }
    #[test]
    fn transformed_output_is_byte_stable() {
        let source = "class C { x = 1; static y = 2; }\n";
        let file = parse(source);
        let checked = checker::check(&Recovered::clean(parse(source)));
        let options = options_for(ScriptTarget::Es2015).transform_view();
        let names = names();
        assert_eq!(
            emit_transformed(&file, checked.product(), &options, &names),
            emit_transformed(&file, checked.product(), &options, &names)
        );
    }

    #[test]
    fn es5_downlevels_exponentiation_to_math_pow() {
        // Upstream exponentiationOperatorWithAnyAndNumber: every `**`
        // becomes `Math.pow(left, right)` below ES2016, and the nested
        // right-associative form nests the calls.
        let output = emit_at(
            "var a: any;\nvar b: number;\nvar r1 = a ** b;\nvar r2 = b ** 2;\nvar r3 = a ** b ** 2;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow(a, b)"), "{code}");
        assert!(code.contains("Math.pow(b, 2)"), "{code}");
        assert!(code.contains("Math.pow(a, Math.pow(b, 2))"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_downlevels_compound_exponentiation_identifiers() {
        // Upstream compoundExponentiationAssignmentLHSIsReference: identifier
        // targets become `x = Math.pow(x, value)` without temps.
        let output = emit_at(
            "var x = 2;\nvar value = 3;\nx **= value;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("x = Math.pow(x, value)"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_compound_exponentiation_property_lhs_evaluates_base_once() {
        let output = emit_at(
            "var obj = { v: 2 };\nfunction pick() { return obj; }\npick().v **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_t0 = pick()).v = Math.pow(_t0.v, 3)"),
            "{code}"
        );
        assert_eq!(code.matches("_t0 = pick()").count(), 1, "{code}");
        // Declaration plus the pick return; the lowering never re-evaluates it.
        assert_eq!(code.matches("obj").count(), 2, "{code}");
    }

    #[test]
    fn es5_compound_exponentiation_captures_computed_keys() {
        let output = emit_at(
            "var obj = { a: 2 };\nobj[\"a\"] **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_t0 = obj)[_t1 = __propKey(\"a\")] = Math.pow(_t0[_t1], 3)"),
            "{code}"
        );
    }

    #[test]
    fn es5_declares_compound_exponentiation_temps_in_the_enclosing_function() {
        let output = emit_at(
            "var obj = { v: 2 };\nfunction f() { obj.v **= 3; }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("var _t0;"), "{code}");
        assert!(
            code.contains("(_t0 = obj).v = Math.pow(_t0.v, 3)"),
            "{code}"
        );
    }

    /// ES5 for-of lowers to the index form and still loops: the
    /// binding lands inside the body, the index bound is the iterable
    /// length, and one pass collects every element.
    #[test]
    fn node_executes_lowered_for_of_collects_every_element() {
        let output = emit_at(
            "var out = [];\nfor (const k of [1, 2, 3]) { out.push(k); }\nfor (const k in { a: 1 }) { out.push(k); }\nconsole.log(out.join(\",\"));\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("of "), "for-of must lower at es5:\n{code}");
        assert!(
            code.contains("var k in"),
            "for-in keeps native form:\n{code}"
        );
        assert!(
            !code.contains("const k"),
            "head bindings convert to var:\n{code}"
        );
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-forof-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert!(
            String::from_utf8_lossy(&result.stdout).contains("1,2,3,a"),
            "the loop must collect every element and key:\n{code}"
        );
    }

    #[test]
    fn es5_for_of_assignment_target_keeps_rewritten_iterable() {
        let output = emit_at(
            "async function f() { let x; for (x of await values) {} }\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("await values"), "{code}");
        assert!(!code.contains(" of "), "{code}");
        assert!(code.contains("/*yield*/, values]"), "{code}");
        assert!(code.contains("x = _t1[_t0]"), "{code}");
    }

    #[test]
    fn computed_destructuring_keys_evaluate_after_earlier_properties() {
        let output = emit_at(
            "var { a = first(), [second()]: b, c = third() } = source();\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let position = |needle: &str| {
            code.find(needle)
                .unwrap_or_else(|| panic!("{needle}: {code}"))
        };
        assert!(position("source()") < position("first()"), "{code}");
        assert!(position("first()") < position("second()"), "{code}");
        assert!(position("second()") < position("third()"), "{code}");
    }

    #[test]
    fn node_executes_lowered_compound_exponentiation_with_single_evaluations() {
        let output = emit_at(
            "var calls = 0;\nvar target = { v: 2 };\nfunction base() { calls += 1; return target; }\nfunction key() { calls += 10; return \"v\"; }\nbase()[key()] **= 3;\nconsole.log(calls + \":\" + target.v);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(!code.contains("**"), "{code}");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("bamts-exponentiation-{nonce}.cjs"));
        std::fs::write(&path, code).expect("write lowered JavaScript");
        let result = std::process::Command::new("node")
            .arg(&path)
            .output()
            .expect("execute Node");
        let _ = std::fs::remove_file(&path);
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        // The base runs once, the key runs once, and `2 ** 3` is `8`.
        assert!(
            String::from_utf8_lossy(&result.stdout).contains("11:8"),
            "{code}"
        );
    }

    #[test]
    fn es2016_preserves_exponentiation_operators() {
        let source = "var r = a ** 2;\na **= 2;\n";
        let es2016_output = emit_at(source, ScriptTarget::Es2016);
        let es2016 = javascript(&es2016_output);
        assert!(es2016.contains("**"), "{es2016}");
        assert!(es2016.contains("**="), "{es2016}");
        assert!(!es2016.contains("Math.pow"), "{es2016}");
        let es2015_output = emit_at(source, ScriptTarget::Es2015);
        let es2015 = javascript(&es2015_output);
        assert!(es2015.contains("Math.pow(a, 2)"), "{es2015}");
        assert!(!es2015.contains("**"), "{es2015}");
    }

    #[test]
    fn es5_lowers_exponentiation_nested_in_expressions() {
        let output = emit_at(
            "var r = flag ? call(a ** 2) : obj[b ** 3];\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow(a, 2)"), "{code}");
        assert!(code.contains("Math.pow(b, 3)"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn analysis_detects_exponentiation_nested_in_expressions() {
        let file = parse("var r = flag ? call(a ** 2) : b **= 3;\n");
        let options = options_for(ScriptTarget::Es5).transform_view();
        let plan = analyze(&file, &options);
        assert!(
            plan.features.contains(&LanguageFeature::Exponentiation),
            "{plan:?}"
        );
        assert!(
            plan.required.contains(&LanguageFeature::Exponentiation),
            "{plan:?}"
        );
        let plain = analyze(&parse("var r = a * b;\n"), &options);
        assert!(!plain.features.contains(&LanguageFeature::Exponentiation));
    }

    #[test]
    fn es5_rewrites_exponentiation_inside_synchronous_arrows() {
        let output = emit_at(
            "var expression = () => 2 ** 3;\n\
             var block = () => { var x = 2; x **= 3; return x; };\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("Math.pow").count(), 2, "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_rewrites_exponentiation_inside_parameter_initializers() {
        let output = emit_at(
            "function f(x = 2 ** 3) { return x; }\n\
             var g = (x = 3 ** 2) => x;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert_eq!(code.matches("Math.pow").count(), 2, "{code}");
        assert!(!code.contains("**"), "{code}");
    }

    #[test]
    fn es5_captures_computed_identifier_keys_before_getters() {
        let output = emit_at(
            "var key = \"a\";\n\
             var obj = { get a() { key = \"b\"; return 2; } };\n\
             obj[key] **= 3;\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        assert!(
            code.contains("(_t0 = obj)[_t1 = __propKey(key)] = Math.pow(_t0[_t1], 3)"),
            "{code}"
        );
    }

    #[test]
    fn es5_compound_exponentiation_coerces_computed_key_once() {
        let output = emit_at(
            "var coercions = 0;\n\
             var property = Symbol(\"x\");\n\
             var key = {};\n\
             key[Symbol.toPrimitive] = function (hint) {\n\
                 coercions += 1;\n\
                 if (hint !== \"string\") throw new Error(\"wrong hint\");\n\
                 return property;\n\
             };\n\
             var obj = {};\n\
             obj[property] = 2;\n\
             obj[key] **= 3;\n\
             console.log(coercions + \":\" + obj[property]);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "1:8\n", "{code}");
    }

    #[test]
    fn es5_property_key_conversion_reads_ordinary_method_once() {
        let output = emit_at(
            "var reads = 0;\n\
             var calls = 0;\n\
             var key = {};\n\
             Object.defineProperty(key, \"toString\", {\n\
                 get: function () {\n\
                     reads += 1;\n\
                     return function () { calls += 1; return \"x\"; };\n\
                 }\n\
             });\n\
             var obj = { x: 2 };\n\
             obj[key] **= 2;\n\
             console.log(reads + \":\" + calls + \":\" + obj.x);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "1:1:4\n", "{code}");
    }

    #[test]
    fn es5_property_key_conversion_without_symbol_uses_ordinary_methods() {
        let output = emit_at(
            "var Symbol = void 0;\n\
             var key = {};\n\
             var obj = { \"[object Object]\": 2 };\n\
             obj[key] **= 3;\n\
             console.log(obj[\"[object Object]\"]);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn imported_helpers_keep_exact_property_key_conversion_inline() {
        let mut options = options_for(ScriptTarget::Es5);
        options.import_helpers = true;
        options.module = Some(ModuleKind::CommonJs);
        let output = emit_with_options(
            "var property = Symbol(\"x\");\n\
             var key = {};\n\
             key[Symbol.toPrimitive] = function () { return property; };\n\
             var obj = {};\n\
             obj[property] = 2;\n\
             obj[key] **= 3;\n\
             console.log(obj[property]);\n",
            options,
        );
        let code = javascript(&output);
        assert!(code.contains("function __propKey"), "{code}");
        assert!(!code.contains("require(\"tslib\").__propKey"), "{code}");
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn es2015_static_super_exponentiation_uses_math_pow() {
        let output = emit_at(
            "class Base { static x = 2; }\n\
             class Derived extends Base { static m() { super.x **= 3; } }\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow"), "{code}");
        assert!(!code.contains("**"), "{code}");
    }
    #[test]
    fn es2015_static_block_super_exponentiation_uses_math_pow() {
        let output = emit_at(
            "class Base { static x = 2; }\n\
             class Derived extends Base { static { super.x **= 3; } }\n\
             console.log(Derived.x);\n",
            ScriptTarget::Es2015,
        );
        let code = javascript(&output);
        assert!(code.contains("Math.pow"), "{code}");
        assert!(!code.contains("**"), "{code}");
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout), "8\n", "{code}");
    }

    #[test]
    fn es5_parameter_compound_exponentiation_is_reentrant() {
        let output = emit_at(
            "var depth = 0;\n\
             var outer = { x: 2 };\n\
             var inner = { x: 5 };\n\
             function update(target, key, value = target[key] **= 2) { return value; }\n\
             var reentrant = {};\n\
             reentrant[Symbol.toPrimitive] = function () {\n\
                 if (depth++ === 0) update(inner, \"x\");\n\
                 return \"x\";\n\
             };\n\
             console.log(update(outer, reentrant) + \":\" + outer.x + \":\" + inner.x);\n",
            ScriptTarget::Es5,
        );
        let code = javascript(&output);
        let result = std::process::Command::new("node")
            .arg("-e")
            .arg(code)
            .output()
            .expect("execute Node");
        assert!(
            result.status.success(),
            "{}\n{code}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&result.stdout),
            "4:4:25\n",
            "{code}"
        );
    }

    #[test]
    fn import_equals_qualified_alias_is_not_a_module_and_gets_use_strict() {
        let source = "import I = A.B.C;\n";
        let file = parse(source);
        assert!(
            !crate::checker::source_is_module(&file),
            "import I = A.B.C (qualified alias) must not make the file a module"
        );
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            code.starts_with("\"use strict\";\n"),
            "a script with alwaysStrict must start with use strict: {code}"
        );
    }

    #[test]
    fn import_equals_require_is_a_module_and_takes_no_prologue_under_es2015() {
        let source = "import I = require(\"m\");\n";
        let file = parse(source);
        assert!(
            crate::checker::source_is_module(&file),
            "import I = require(\"m\") must make the file a module"
        );
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::Es2015),
                always_strict: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            !code.starts_with("\"use strict\";\n"),
            "an ES2015 module takes no strict prologue even under alwaysStrict: {code}"
        );
    }

    #[test]
    fn cjs_plan_for_qualified_alias_emits_no_require_or_esmodule_marker() {
        let source = "import I = A.B.C;\n";
        let output = emit_with_options(
            source,
            EmitOptions {
                target: ScriptTarget::Es2015,
                module: Some(crate::emitter::ModuleKind::CommonJs),
                ..EmitOptions::default()
            },
        );
        let code = javascript(&output);
        assert!(
            !code.contains("__esModule"),
            "a qualified alias must not trigger the __esModule marker: {code}"
        );
        assert!(
            !code.contains("require("),
            "a qualified alias must not emit a require call: {code}"
        );
    }

    #[test]
    fn es5_lowers_nullish_coalescing_identifier_to_the_conditional_form() {
        // Rule: `a ?? b` lowers below ES2020 to `a !== null && a !== void 0 ? a : b`.
        // Proven by baseline `nullishCoalescingOperator1.js` (default ES5
        // target): `const aa1 = a1 !== null && a1 !== void 0 ? a1 : 'whatever';`.
        // Counterexample-side check: `optionalChainingInArrow(target=es2015).js`
        // keeps the lowered form at ES2015, so the gate is ES2020, not ES2015.
        // This test fails without the production change: the pre-change
        // rewriter passed `??` through verbatim.
        let output = emit_at("const out = a1 ?? 'whatever';\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("a1 !== null && a1 !== void 0 ? a1 : 'whatever'"),
            "{code}"
        );
        assert!(!code.contains("??"), "{code}");
    }

    #[test]
    fn es2020_keeps_nullish_coalescing_native() {
        // Same rule's at-and-above-threshold side: `LanguageFeature::
        // NullishCoalescing::since()` is `ScriptTarget::Es2020`, so at ES2020
        // the native `??` survives unchanged (tsc gates emitNullishCoalescing
        // on `languageVersion >= ES2020`).
        let output = emit_at("const out = a1 ?? 'whatever';\n", ScriptTarget::Es2020);
        let code = javascript(&output);
        assert!(code.contains("a1 ?? 'whatever'"), "{code}");
        assert!(!code.contains("a1 !== null"), "{code}");
    }

    #[test]
    fn es5_nullish_coalescing_captures_non_identifier_operands_once() {
        // A non-identifier left operand must evaluate exactly once, captured
        // through an expression temp — tsc emits
        // `var _t; (_t = f()) !== null && _t !== void 0 ? _t : rhs`.
        let output = emit_at("const out = f() ?? 'x';\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert_eq!(code.matches("f()").count(), 1, "f() must run once: {code}");
        assert!(code.contains("!== null &&"), "{code}");
        assert!(!code.contains("??"), "{code}");
    }

    #[test]
    fn es5_lowers_nullish_assignment_to_the_conditional_assignment_form() {
        // Rule: `a ??= b` lowers below ES2021 to
        // `a !== null && a !== void 0 ? a : (a = b)`.
        // Proven by baseline
        // `equalityWithtNullishCoalescingAssignment(strict=false).js`:
        // `a !== null && a !== void 0 ? a : (a = true);`.
        let output = emit_at("let a = false;\na ??= true;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(
            code.contains("a !== null && a !== void 0 ? a : (a = true)"),
            "{code}"
        );
        assert!(!code.contains("??="), "{code}");
    }

    #[test]
    fn es5_lowers_or_and_and_assignment_to_expanded_logical_form() {
        // Rule: `a ||= b` → `a || (a = b)` and `a &&= b` → `a && (a = b)`
        // below ES2021 (tsc's emitLogicalAssignment expansion).
        let output = emit_at("let a = 0;\na ||= 1;\na &&= 2;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("a || (a = 1)"), "{code}");
        assert!(code.contains("a && (a = 2)"), "{code}");
        assert!(!code.contains("||="), "{code}");
        assert!(!code.contains("&&="), "{code}");
    }

    #[test]
    fn es2021_keeps_logical_assignment_native() {
        // `LanguageFeature::LogicalAssignment::since()` is Es2021: at ES2021
        // the operators survive verbatim.
        let output = emit_at("let a = 0;\na ||= 1;\n", ScriptTarget::Es2021);
        let code = javascript(&output);
        assert!(code.contains("a ||= 1"), "{code}");
    }

    #[test]
    fn es5_member_target_logical_assignment_captures_the_base_once() {
        // Member targets base-capture through an expression temp so the
        // object evaluates once: tsc's form is
        // `(_t = obj).p || ((_t.p) = rhs)` with the capture in the READ
        // position (JS evaluates a logical chain's left operand first).
        let output = emit_at("let o = { p: 0 };\no.p ||= 1;\n", ScriptTarget::Es5);
        let code = javascript(&output);
        assert!(code.contains("(_t0 = o).p || (_t0.p = 1)"), "{code}");
        assert!(!code.contains("||="), "{code}");
    }

    #[test]
    fn es2020_keeps_optional_chaining_native_but_es5_lowers_it() {
        // Rule: `a?.b` lowers below ES2020 to
        // `a === null || a === void 0 ? void 0 : a.b`.
        // Proven by baseline `optionalChainingInArrow(target=es5).js`:
        // `names === null || names === void 0 ? void 0 : names.filter(...)`;
        // the `target=esnext` variant of the same case
        // (`optionalChainingInParameterBindingPattern(target=esnext).js`)
        // exists on the at-threshold side.
        let lowered = emit_at("const v = names?.filter(f);\n", ScriptTarget::Es5);
        let lowered_code = javascript(&lowered);
        assert!(
            lowered_code.contains("names === null || names === void 0 ? void 0 :"),
            "{lowered_code}"
        );
        assert!(
            !lowered_code.contains("?.") || lowered_code.contains("\"use strict\""),
            "{lowered_code}"
        );
        let native = emit_at("const v = names?.filter(f);\n", ScriptTarget::Es2020);
        assert!(
            javascript(&native).contains("names?.filter(f)"),
            "{native:?}"
        );
    }
}
