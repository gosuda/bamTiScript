//! Deterministic AST-to-JavaScript and declaration emit.
//!
//! [`emit_checked`] is the production boundary: it consumes an existing
//! [`SemanticModel`], applies the selected transform and declaration stages, and
//! returns JavaScript and declaration products in separate canonical slots.
//! The low-level printer is private to the emitter module and never checks a
//! source file.
//!
//! # Guarantees
//! * **Deterministic.** The same tree, model, options, and file names produce
//!   byte-identical output and ordered diagnostics.
//! * **Type erasure.** JavaScript output removes type-only syntax while
//!   declaration output preserves the public type surface.
//! * **Correct precedence.** Parentheses are derived from AST precedence and
//!   associativity; explicit parenthesized nodes round-trip their parens,
//!   matching the upstream printer.
//! * **Mapped printing.** Generated and original columns use zero-based UTF-16
//!   code units, including text written by structural helper preludes.

pub mod declarations;
pub mod helpers;
pub mod sourcemap;
pub mod transforms;
pub mod transpile;

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    sync::Arc,
};

use crate::checker::{SemanticModel, Type, TypeId, render_type_declaration};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::enum_plan::{EnumFacts, EnumMemberPlan, EnumScalar};
use crate::jsx_desugar::JsxSourceDesugarPlan;
use crate::source::{JsxEmit, SourceId, SourceText, TextRange, Utf16Pos};
use crate::syntax::*;

use declarations::DeclarationOptions;
use helpers::{HelperOptions, HelperStyle};
use sourcemap::{LineColumn, SourceMap, SourceMapBuilder};
pub use transforms::ScriptTarget;
use transforms::{LanguageFeature, TransformOptions};

/// Stable diagnostic identifiers produced by the emitter.
pub mod codes {
    use crate::diagnostic::DiagnosticCode;

    /// A recovered expression node has no printable form.
    pub const MISSING_EXPRESSION: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1001");
    /// A recovered statement node has no printable form.
    pub const MISSING_STATEMENT: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1002");
    /// A recovered type node has no printable form.
    pub const MISSING_TYPE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1003");
    /// A recovered binding pattern has no printable form.
    pub const MISSING_BINDING: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1004");
    /// A recovered assignment target has no printable form.
    pub const MISSING_TARGET: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1005");
    /// A recovered property name has no printable form.
    pub const MISSING_PROPERTY_NAME: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1006");
    /// A recovered module or entity name has no printable form.
    pub const MISSING_NAME: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1007");
    /// A recovered class or type member has no printable form.
    pub const MISSING_MEMBER: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1008");
    /// A recovered element (array/argument) node has no printable form.
    pub const MISSING_ELEMENT: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1009");
    /// A token range is not a valid slice of the source text.
    pub const UNRESOLVED_TOKEN: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1010");
    /// `namespace` runtime lowering needs semantic analysis unavailable here.
    pub const NAMESPACE_UNLOWERED: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1011");
    /// A runtime enum declaration has no matching checked enum plan.
    pub const ENUM_FACTS_UNAVAILABLE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1013");
    /// JSX desugaring failed before JavaScript printing.
    pub const JSX_DESUGAR_FAILED: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1014");
    /// A compiler directive has a value outside its closed option domain.
    pub const INVALID_OPTION_VALUE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1501");
    /// A compiler directive is not owned by single-file emit.
    pub const UNRECOGNIZED_OPTION: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1502");
}

/// JavaScript module form used to select imported-helper syntax.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ModuleKind {
    CommonJs,
    Amd,
    Umd,
    System,
    Es2015,
    EsNext,
}

/// The structural line terminator the emitter inserts between lines.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Newline {
    /// Unix line feed (`\n`).
    Lf,
    /// Windows carriage return + line feed (`\r\n`).
    CrLf,
}

impl Newline {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Lf => "\n",
            Self::CrLf => "\r\n",
        }
    }
}

/// Canonical immutable options for JavaScript and declaration emit.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EmitOptions {
    pub target: ScriptTarget,
    pub module: Option<ModuleKind>,
    /// Whether every source file receives a strict-mode prologue.
    pub always_strict: bool,
    pub import_helpers: bool,
    /// Assume downleveling helpers exist globally; emit no helper prelude
    /// (`noEmitHelpers`, tsc's noEmitHelpers).
    pub no_emit_helpers: bool,
    pub use_define_for_class_fields: Option<bool>,
    pub declaration: bool,
    pub emit_declaration_only: bool,
    pub isolated_declarations: bool,
    pub strip_private: bool,
    pub source_map: bool,
    pub inline_source_map: bool,
    pub inline_sources: bool,
    pub declaration_map: bool,
    /// JSX output mode. `None` behaves like [`JsxEmit::Preserve`].
    pub jsx: Option<JsxEmit>,
    /// `jsxFactory` callee for classic JSX lowering. Preserve printing
    /// ignores it; the JSX lowering stage is its consumer.
    pub jsx_factory: Option<Arc<str>>,
    /// `jsxFragmentFactory` callee for classic JSX lowering.
    pub jsx_fragment_factory: Option<Arc<str>>,
    /// `jsxImportSource` module specifier for automatic-runtime JSX lowering.
    pub jsx_import_source: Option<Arc<str>>,
    pub newline: Newline,
    pub indent_width: u8,
}

impl Default for EmitOptions {
    fn default() -> Self {
        Self {
            target: ScriptTarget::EsNext,
            module: None,
            always_strict: false,
            import_helpers: false,
            no_emit_helpers: false,
            use_define_for_class_fields: None,
            declaration: false,
            emit_declaration_only: false,
            isolated_declarations: false,
            strip_private: false,
            source_map: false,
            inline_source_map: false,
            inline_sources: false,
            declaration_map: false,
            jsx: None,
            jsx_factory: None,
            jsx_fragment_factory: None,
            jsx_import_source: None,
            newline: Newline::Lf,
            indent_width: 4,
        }
    }
}

impl EmitOptions {
    /// Returns a copy using `newline` for structural line breaks.
    #[must_use]
    pub const fn with_newline(mut self, newline: Newline) -> Self {
        self.newline = newline;
        self
    }

    /// Returns a copy using `indent_width` spaces per indentation level.
    #[must_use]
    pub const fn with_indent_width(mut self, indent_width: u8) -> Self {
        self.indent_width = indent_width;
        self
    }

    /// Builds canonical emit options from normalized compiler directives.
    #[must_use]
    pub fn from_directives(
        directives: &BTreeMap<String, String>,
        source_id: SourceId,
    ) -> (Self, Vec<Diagnostic>) {
        let mut options = Self::default();
        let mut diagnostics = directives
            .iter()
            .filter_map(|(name, value)| options.apply_directive(name, value, source_id))
            .collect::<Vec<_>>();
        diagnostics.sort();
        diagnostics.dedup();
        (options, diagnostics)
    }

    /// Applies the emit-relevant fields that the project (CLI) and program
    /// (lane) paths must agree on: `target`, `always_strict`, `module`, and
    /// the `useDefineForClassFields` pin. This is the single mapping point so
    /// the two paths cannot diverge on downleveling or the strict-mode
    /// prologue. The pin is `Option` so an unset key keeps the
    /// target-derived default instead of forcing false.
    pub fn apply_emit_fields(
        &mut self,
        target: ScriptTarget,
        always_strict: bool,
        module: Option<ModuleKind>,
        use_define_for_class_fields: Option<bool>,
        import_helpers: Option<bool>,
    ) {
        self.target = target;
        self.always_strict = always_strict;
        if let Some(module) = module {
            self.module = Some(module);
        }
        if let Some(use_define) = use_define_for_class_fields {
            self.use_define_for_class_fields = Some(use_define);
        }
        if let Some(import_helpers) = import_helpers {
            self.import_helpers = import_helpers;
        }
    }

    /// Applies one compiler directive, returning a typed diagnostic on failure.
    pub fn apply_directive(
        &mut self,
        name: &str,
        value: &str,
        source_id: SourceId,
    ) -> Option<Diagnostic> {
        let name = name.to_ascii_lowercase();
        let value = value.trim();
        let invalid = || invalid_option_value(source_id);
        match name.as_str() {
            "target" => {
                let Some(target) = parse_target(value) else {
                    return Some(invalid());
                };
                self.target = target;
            }
            "alwaysstrict" => {
                let Some(always_strict) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.always_strict = always_strict;
            }
            "noemithelpers" => {
                let Some(no_emit_helpers) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.no_emit_helpers = no_emit_helpers;
            }
            "module" => {
                let Some(module) = parse_module(value) else {
                    return Some(invalid());
                };
                self.module = Some(module);
            }
            "importhelpers" => {
                let Some(import_helpers) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.import_helpers = import_helpers;
            }
            "usedefineforclassfields" => {
                let Some(use_define) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.use_define_for_class_fields = Some(use_define);
            }
            "declaration" => {
                let Some(declaration) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.declaration = declaration;
            }
            "emitdeclarationonly" => {
                let Some(emit_declaration_only) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.emit_declaration_only = emit_declaration_only;
            }
            "isolateddeclarations" => {
                let Some(isolated_declarations) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.isolated_declarations = isolated_declarations;
            }
            "stripinternal" => {
                let Some(strip_private) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.strip_private = strip_private;
            }
            "sourcemap" => {
                let Some(source_map) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.source_map = source_map;
            }
            "inlinesourcemap" => {
                let Some(inline_source_map) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.inline_source_map = inline_source_map;
            }
            "inlinesources" => {
                let Some(inline_sources) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.inline_sources = inline_sources;
            }
            "declarationmap" => {
                let Some(declaration_map) = parse_bool(value) else {
                    return Some(invalid());
                };
                self.declaration_map = declaration_map;
            }
            "jsx" => {
                let Some(jsx) = parse_jsx(value) else {
                    return Some(invalid());
                };
                self.jsx = Some(jsx);
            }
            "jsxfactory" => self.jsx_factory = Some(Arc::from(value)),
            "jsxfragmentfactory" => self.jsx_fragment_factory = Some(Arc::from(value)),
            "jsximportsource" => self.jsx_import_source = Some(Arc::from(value)),
            "newline" => {
                let Some(newline) = parse_newline(value) else {
                    return Some(invalid());
                };
                self.newline = newline;
            }
            "indentwidth" => {
                let Ok(indent_width) = value.parse() else {
                    return Some(invalid());
                };
                self.indent_width = indent_width;
            }
            _ => return Some(unrecognized_option(source_id)),
        }
        None
    }

    fn normalized(&self) -> Self {
        let mut normalized = self.clone();
        if !normalized.declaration && !normalized.emit_declaration_only {
            normalized.declaration_map = false;
        }
        if normalized.inline_source_map {
            normalized.source_map = false;
        }
        normalized
    }

    pub(crate) fn transform_view(&self) -> TransformOptions {
        let style = if !self.import_helpers {
            HelperStyle::Inline
        } else if self.module == Some(ModuleKind::CommonJs) {
            HelperStyle::CommonJs
        } else {
            HelperStyle::EsModule
        };
        TransformOptions {
            target: self.target,
            always_strict: self.always_strict,
            use_define_for_class_fields: self
                .use_define_for_class_fields
                .unwrap_or_else(|| self.target.supports(LanguageFeature::ClassFields)),
            helpers: HelperOptions {
                import_helpers: self.import_helpers,
                no_emit_helpers: self.no_emit_helpers,
                style,
                module_specifier: String::from("tslib"),
            },
            module_kind: self.module,
            newline: self.newline,
            indent_width: self.indent_width,
            jsx: self.jsx,
            jsx_factory: self.jsx_factory.clone(),
            jsx_fragment_factory: self.jsx_fragment_factory.clone(),
            jsx_import_source: self.jsx_import_source.clone(),
            jsx_import_style: if self.module == Some(ModuleKind::CommonJs) {
                crate::jsx_desugar::JsxRuntimeImportStyle::CommonJs
            } else {
                crate::jsx_desugar::JsxRuntimeImportStyle::EsModule
            },
            source_map: self.source_map,
            inline_source_map: self.inline_source_map,
            inline_sources: self.inline_sources,
        }
    }

    pub(crate) const fn declaration_view(&self) -> DeclarationOptions {
        DeclarationOptions {
            newline: self.newline,
            indent_width: self.indent_width,
            isolated_declarations: self.isolated_declarations,
            strip_private: self.strip_private,
            declaration_map: self.declaration_map,
        }
    }
}

/// File names recorded in emitted products and source maps.
///
/// Source-map names are explicit per surface: the emitter never re-derives
/// paths from project layout, so the boundary carries the exact
/// `sourceMappingURL` and map `sources` entry for each generated product.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmitFileNames {
    pub source_name: Arc<str>,
    pub js_file_name: Option<Arc<str>>,
    pub declaration_file_name: Option<Arc<str>>,
    pub source_root: Option<Arc<str>>,
    pub js_source_name: Option<Arc<str>>,
    pub js_source_map_url: Option<Arc<str>>,
    pub declaration_source_name: Option<Arc<str>>,
    pub declaration_source_map_url: Option<Arc<str>>,
}

impl Default for EmitFileNames {
    fn default() -> Self {
        Self {
            source_name: Arc::from("<anonymous>"),
            js_file_name: None,
            declaration_file_name: None,
            source_root: None,
            js_source_name: None,
            js_source_map_url: None,
            declaration_source_name: None,
            declaration_source_map_url: None,
        }
    }
}

impl EmitFileNames {
    /// Returns the map `sources` entry and `sourceMappingURL` for `surface`.
    #[must_use]
    pub(crate) fn map_naming(&self, surface: Surface) -> (Option<&str>, Option<&str>) {
        match surface {
            Surface::JavaScript => (
                self.js_source_name.as_deref(),
                self.js_source_map_url.as_deref(),
            ),
            Surface::Declaration => (
                self.declaration_source_name.as_deref(),
                self.declaration_source_map_url.as_deref(),
            ),
        }
    }
}

/// One emitted file and its optional real printer source map.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedFile {
    pub code: String,
    pub source_map: Option<SourceMap>,
}

/// Canonical recovered products from checked emit.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EmitOutput {
    pub javascript: Option<EmittedFile>,
    pub declaration: Option<EmittedFile>,
    pub diagnostics: Vec<Diagnostic>,
}

impl EmitOutput {
    /// Returns whether any diagnostic is an error.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| !diagnostic.is_warning())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PrintOptions {
    pub(crate) newline: Newline,
    pub(crate) indent_width: u8,
    pub(crate) source_map: bool,
    pub(crate) inline_source_map: bool,
    pub(crate) inline_sources: bool,
}

pub(crate) struct PrintSource<'a> {
    pub(crate) file: &'a SourceFile,
    pub(crate) original_content: &'a str,
    pub(crate) synthesized: Option<&'a BTreeSet<NodeId>>,
    /// First id the rewriter may mint for this file (its seed past the
    /// parser tree and any JSX-desugar consumption). Ids below it are
    /// parser-assigned and must carry ranges within the authored text.
    pub(crate) synthesized_floor: u32,
}

/// Print context for a braced block. Carries two tsc behaviors that split on
/// different axes: which braces get source-map segments, and whether an
/// authored single-line body may stay single-line.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum BlockLayout {
    /// Function, arrow, and method bodies: braces unmapped, layout preserved.
    FunctionBody,
    /// Static initialization blocks: braces map like statement blocks, layout
    /// still preserved (classThisReference keeps `static { this; }` on its
    /// authored line).
    StaticInitBody,
    /// Statement-position blocks (standalone, try/catch/finally, control
    /// bodies): braces mapped, always expanded (parser768531 expands an
    /// authored single-line standalone block).
    Statement,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Surface {
    JavaScript,
    Declaration,
}

/// Emits `file` using an existing semantic model without checking it again.
#[must_use]
pub fn emit_checked(
    file: &SourceFile,
    model: &SemanticModel,
    options: &EmitOptions,
    names: &EmitFileNames,
) -> EmitOutput {
    let source_map_conflict = options.source_map && options.inline_source_map;
    let inline_sources_without_source_map =
        options.inline_sources && !options.source_map && !options.inline_source_map;
    let options = options.normalized();
    let mut output = if options.emit_declaration_only {
        EmitOutput::default()
    } else {
        transforms::emit_transformed(file, model, &options.transform_view(), names)
    };
    if options.declaration || options.emit_declaration_only {
        let declaration =
            declarations::emit_declarations(file, model, options.declaration_view(), names);
        output.declaration = declaration.declaration;
        output.diagnostics.extend(declaration.diagnostics);
    }
    if source_map_conflict {
        output.diagnostics.push(option_diagnostic(
            codes::INVALID_OPTION_VALUE,
            file.source_id(),
            "sourceMap and inlineSourceMap cannot be specified together",
        ));
    }
    if inline_sources_without_source_map {
        output.diagnostics.push(option_diagnostic(
            codes::INVALID_OPTION_VALUE,
            file.source_id(),
            "inlineSources can only be used when sourceMap or inlineSourceMap is provided",
        ));
    }
    output.diagnostics.sort();
    output.diagnostics.dedup();
    output
}

#[must_use]
pub(crate) fn print(
    file: &SourceFile,
    model: &SemanticModel,
    options: PrintOptions,
    names: &EmitFileNames,
    surface: Surface,
    prelude: Option<String>,
) -> EmitOutput {
    print_with_jsx_plan(
        PrintSource {
            file,
            original_content: file.source_text().as_str(),
            synthesized: None,
            // No rewriter ran: every id is parser-assigned, so the mint
            // gate's range check applies universally.
            synthesized_floor: u32::MAX,
        },
        model,
        options,
        names,
        surface,
        prelude,
        None,
    )
}

#[must_use]
pub(crate) fn print_with_jsx_plan(
    source: PrintSource<'_>,
    model: &SemanticModel,
    options: PrintOptions,
    names: &EmitFileNames,
    surface: Surface,
    prelude: Option<String>,
    jsx_plan: Option<&JsxSourceDesugarPlan>,
) -> EmitOutput {
    let PrintSource {
        file,
        original_content,
        synthesized,
        synthesized_floor,
    } = source;
    let mut source_map = (options.source_map || options.inline_source_map).then(|| {
        let mut builder = SourceMapBuilder::new()
            .with_sources_content(options.inline_sources && surface == Surface::JavaScript);
        let file_name = match surface {
            Surface::JavaScript => names.js_file_name.as_deref(),
            Surface::Declaration => names.declaration_file_name.as_deref(),
        };
        if let Some(file_name) = file_name {
            builder = builder.with_file(file_name);
        }
        if let Some(source_root) = names.source_root.as_deref() {
            builder = builder.with_source_root(source_root);
        }
        builder
    });
    if let Some(builder) = &mut source_map {
        let (source_name, _) = names.map_naming(surface);
        builder.intern_source_with_content(
            source_name.unwrap_or_else(|| names.source_name.as_ref()),
            original_content,
        );
    }

    let (map_source, _) = names.map_naming(surface);
    let mapped_source_name: &str = map_source.unwrap_or_else(|| names.source_name.as_ref());
    let mut emitter = Emitter {
        line_comments: file
            .tokens()
            .iter()
            .filter(|token| token.kind() == TokenKind::LineComment)
            .map(|token| token.range())
            .collect(),
        tokens: file.tokens(),
        source: file.source_text(),
        source_name: mapped_source_name,
        source_id: file.source_id(),
        model,
        enum_facts: model.enum_facts(),
        options,
        map: source_map.take(),
        generated_line: 0,
        generated_column: 0,
        out: String::new(),
        indent: 0,
        pending_indent: false,
        anchor: file.range(),
        last_mapped_end: None,
        jsx_plan,
        diagnostics: Vec::new(),
        decl_ambient: false,
        current_scope: model.module_scope(),
        decl_drop_member_export: false,
        decl_source_is_js: matches!(
            file.script_kind(),
            crate::source::ScriptKind::JavaScript | crate::source::ScriptKind::JavaScriptReact
        ),
        authored_len: Utf16Pos::new(utf16_len(original_content)),
        synthesized,
        synthesized_floor,
    };
    if let Some(prelude) = prelude.filter(|prelude| !prelude.is_empty()) {
        let has_trailing_newline = prelude.ends_with('\n');
        emitter.raw(&prelude);
        if !has_trailing_newline {
            emitter.newline();
        }
    }
    match surface {
        Surface::JavaScript => emitter.emit_module_js(file.statements()),
        Surface::Declaration => emitter.emit_module_decl(file.statements()),
    }
    let mut code = emitter.out;
    emitter.diagnostics.sort();

    let source_map = emitter.map.take().map(SourceMapBuilder::finish);
    if let Some(source_map) = &source_map {
        if !code.is_empty() && !code.ends_with(options.newline.as_str()) {
            code.push_str(options.newline.as_str());
        }
        let (_, map_url) = names.map_naming(surface);
        if options.inline_source_map {
            code.push_str(&source_map.inline_comment());
        } else if let Some(url) = map_url {
            code.push_str(&SourceMap::url_comment(url));
        } else if let Some(file) = source_map.file() {
            code.push_str(&SourceMap::url_comment(&format!("{file}.map")));
        }
    }
    let emitted = EmittedFile { code, source_map };
    match surface {
        Surface::JavaScript => EmitOutput {
            javascript: Some(emitted),
            declaration: None,
            diagnostics: emitter.diagnostics,
        },
        Surface::Declaration => EmitOutput {
            javascript: None,
            declaration: Some(emitted),
            diagnostics: emitter.diagnostics,
        },
    }
}

pub(crate) fn parse_target(value: &str) -> Option<ScriptTarget> {
    match value.trim().to_ascii_lowercase().as_str() {
        "es3" => Some(ScriptTarget::Es3),
        "es5" => Some(ScriptTarget::Es5),
        "es6" | "es2015" => Some(ScriptTarget::Es2015),
        "es2016" => Some(ScriptTarget::Es2016),
        "es2017" => Some(ScriptTarget::Es2017),
        "es2018" => Some(ScriptTarget::Es2018),
        "es2019" => Some(ScriptTarget::Es2019),
        "es2020" => Some(ScriptTarget::Es2020),
        "es2021" => Some(ScriptTarget::Es2021),
        "es2022" => Some(ScriptTarget::Es2022),
        "es2023" => Some(ScriptTarget::Es2023),
        "es2024" => Some(ScriptTarget::Es2024),
        "es2025" => Some(ScriptTarget::Es2025),
        "esnext" | "latest" => Some(ScriptTarget::EsNext),
        _ => None,
    }
}

pub(crate) fn parse_module(value: &str) -> Option<ModuleKind> {
    match value.trim().to_ascii_lowercase().as_str() {
        "commonjs" => Some(ModuleKind::CommonJs),
        "amd" => Some(ModuleKind::Amd),
        "umd" => Some(ModuleKind::Umd),
        "system" => Some(ModuleKind::System),
        "es6" | "es2015" => Some(ModuleKind::Es2015),
        "esnext" => Some(ModuleKind::EsNext),
        _ => None,
    }
}

fn parse_jsx(value: &str) -> Option<JsxEmit> {
    value.trim().to_ascii_lowercase().parse().ok()
}

fn parse_newline(value: &str) -> Option<Newline> {
    match value.trim().to_ascii_lowercase().as_str() {
        "lf" => Some(Newline::Lf),
        "crlf" => Some(Newline::CrLf),
        _ => None,
    }
}

fn parse_bool(value: &str) -> Option<bool> {
    match value.trim().to_ascii_lowercase().as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn option_diagnostic(
    code: DiagnosticCode,
    source_id: SourceId,
    message: &'static str,
) -> Diagnostic {
    Diagnostic::error(
        code,
        source_id,
        TextRange::new(Utf16Pos::new(0), Utf16Pos::new(0)).expect("zero range is ordered"),
        message,
    )
}

fn invalid_option_value(source_id: SourceId) -> Diagnostic {
    option_diagnostic(
        codes::INVALID_OPTION_VALUE,
        source_id,
        "emit option has an invalid value",
    )
}

fn unrecognized_option(source_id: SourceId) -> Diagnostic {
    option_diagnostic(
        codes::UNRECOGNIZED_OPTION,
        source_id,
        "emit option is not recognized",
    )
}

// Operator precedence levels: larger binds tighter.
const P_SEQUENCE: u8 = 1;
const P_ASSIGN: u8 = 2;
const P_CONDITIONAL: u8 = 3;
const P_NULLISH: u8 = 4;
const P_LOGICAL_OR: u8 = 4;
const P_LOGICAL_AND: u8 = 5;
const P_BIT_OR: u8 = 6;
const P_BIT_XOR: u8 = 7;
const P_BIT_AND: u8 = 8;
const P_EQUALITY: u8 = 9;
const P_RELATIONAL: u8 = 10;
const P_SHIFT: u8 = 11;
const P_ADDITIVE: u8 = 12;
const P_MULTIPLICATIVE: u8 = 13;
const P_EXPONENT: u8 = 14;
const P_UNARY: u8 = 15;
const P_POSTFIX: u8 = 16;
const P_CALL_MEMBER: u8 = 17;
const P_PRIMARY: u8 = 18;

struct Emitter<'a> {
    source: &'a SourceText,
    /// Authored single-line comment ranges, sorted by start. Backs trailing
    /// comment preservation (`var y; // note`) in statement lists; the token
    /// stream carries them with original coordinates, which stay valid in
    /// the rewritten text because synthesis appends past authored content.
    line_comments: Vec<TextRange>,
    /// The full authored token stream, sorted by start. Backs authored-form
    /// lookups (arrow parameter parens) that the AST does not retain.
    tokens: &'a [Token],
    source_id: SourceId,
    model: &'a SemanticModel,
    enum_facts: &'a EnumFacts,
    options: PrintOptions,
    map: Option<SourceMapBuilder>,
    source_name: &'a str,
    generated_line: usize,
    generated_column: usize,
    /// The source range of the most recent `raw_mapped` write, used to
    /// compute the EOL mapping's source position at line boundaries.
    last_mapped_end: Option<TextRange>,
    out: String,
    jsx_plan: Option<&'a JsxSourceDesugarPlan>,
    indent: usize,
    pending_indent: bool,
    anchor: TextRange,
    diagnostics: Vec<Diagnostic>,
    decl_ambient: bool,
    /// Innermost namespace body scope currently being emitted, for resolving
    /// unqualified declaration names (inferred return types). Starts at the
    /// module scope; `emit_namespace_decl` narrows it to the namespace's
    /// local scope while emitting the body.
    current_scope: crate::checker::ScopeId,
    /// True inside an identifier-named namespace body, where tsc drops the
    /// `export` modifier from member declarations (the namespace itself is
    /// the only public surface). String-named `module "..."` bodies keep it.
    decl_drop_member_export: bool,
    /// True when the declaration is generated from a JavaScript source
    /// (`allowJs`). tsc does not add `declare` to exported declarations of a
    /// JS file, while it does for a TypeScript source.
    decl_source_is_js: bool,
    /// UTF-16 length of `PrintSource::original_content` — the authored text
    /// only, never the extended source range. Used by `preserves_single_line`
    /// to reject ranges that spill into synthesized appendix text.
    authored_len: Utf16Pos,
    /// Synthesized node ids recorded by the rewriter, or `None` when printing
    /// without a transform (declarations, untransformed JS).
    synthesized: Option<&'a BTreeSet<NodeId>>,
    /// First rewriter-minted id for this file; ids below it are
    /// parser-assigned and must carry ranges within the authored text.
    synthesized_floor: u32,
}

impl Emitter<'_> {
    /// The authored single-line comment between `after` and `limit` on
    /// `after`'s source line, if one exists (tsc preserves these with
    /// `removeComments` off, attached to the last statement on the line).
    /// The bound stops a comment from duplicating onto every statement that
    /// shares its line; `partition_point` keeps the scan logarithmic.
    fn trailing_line_comment(&self, after: Utf16Pos, limit: Utf16Pos) -> Option<TextRange> {
        let line = self.source.line_column(after).ok()?.0;
        let start = self
            .line_comments
            .partition_point(|range| range.start() < after);
        self.line_comments[start..]
            .iter()
            .take_while(|range| range.start() < limit)
            .find(|range| {
                self.source
                    .line_column(range.start())
                    .is_ok_and(|(other, _)| other == line)
            })
            .copied()
    }

    /// The authored source text covered by `range`, when it lies wholly in
    /// the source text.
    fn source_slice(&self, range: TextRange) -> Option<&str> {
        let start = self.source.utf16_to_byte(range.start()).ok()?;
        let end = self.source.utf16_to_byte(range.end()).ok()?;
        self.source.as_str().get(start..end)
    }

    /// Prints a statement list with tsc's default comment preservation: each
    /// statement that emits is followed by its same-line trailing comment
    /// before the newline. Single-line-preserved bodies do not route here —
    /// tsc expands a body whose statement carries a trailing comment, a
    /// rule queued separately.
    fn emit_statement_list(&mut self, statements: &[Stmt]) {
        for (index, statement) in statements.iter().enumerate() {
            if self.emit_statement(statement) {
                let limit = statements
                    .get(index + 1)
                    .map_or_else(|| Utf16Pos::new(usize::MAX), |next| next.range().start());
                if let Some(comment) = self.trailing_line_comment(statement.range().end(), limit) {
                    self.raw(" ");
                    if let Some(text) = self.source_slice(comment) {
                        let text = text.to_owned();
                        self.raw(&text);
                    }
                }
                self.newline();
            }
        }
    }
}

impl Emitter<'_> {
    /// Whether an arrow's single plain identifier parameter was authored
    /// without parentheses (`props =>`). The AST drops the distinction, so
    /// the token stream answers: a bare parameter has no `(` ending exactly
    /// where the binding starts.
    fn arrow_params_authored_bare(&self, arrow: &ArrowFunction) -> bool {
        if arrow.parameters.len() != 1 {
            return false;
        }
        let parameter = arrow.parameters[0].data();
        if parameter.initializer.is_some()
            || parameter.type_annotation.is_some()
            || parameter.optional
            || !parameter.decorators.is_empty()
        {
            return false;
        }
        if !matches!(parameter.binding.data(), BindingPattern::Identifier(_)) {
            return false;
        }
        let start = parameter.binding.range().start();
        let index = self
            .tokens
            .partition_point(|token| token.range().start() < start);
        let Some(before) = index.checked_sub(1).and_then(|i| self.tokens.get(i)) else {
            return true;
        };
        !(before.kind() == TokenKind::LParen && before.range().end() == start)
    }
}

impl<'a> Emitter<'a> {
    // ---- low level output -------------------------------------------------

    fn raw(&mut self, text: &str) {
        if text.is_empty() {
            return;
        }
        self.flush_indent();
        self.write_text(text);
    }

    /// Writes `text` and records a source-map mapping from the current
    /// generated position to the source position of `range.start()`.
    ///
    /// Unlike the old `mark` + `raw` deferred pattern, this records the
    /// mapping immediately after flushing indentation but before writing
    /// the text, so the generated column is exactly where `text` begins.
    /// `range` should be the source range of the token or node being
    /// written; `range.end()` is tracked for the next EOL mapping.
    fn raw_mapped(&mut self, text: &str, range: TextRange) {
        if text.is_empty() {
            return;
        }
        self.flush_indent();
        self.record_mapping(range);
        self.last_mapped_end = Some(range);
        self.write_text(text);
    }

    /// Like `raw_mapped` but records the mapping at a specific source position
    /// rather than a range start. Used for synthetic punctuation whose source
    /// position is derived (e.g. the space before `=` in `var x = 1`).
    fn raw_mapped_pos(&mut self, text: &str, pos: Utf16Pos) {
        if text.is_empty() {
            return;
        }
        let range = TextRange::new(pos, pos)
            .unwrap_or(TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).unwrap());
        self.raw_mapped(text, range);
    }

    /// Writes `text` and maps it to a source token of `width` UTF-16 units
    /// starting at `pos`, advancing `last_mapped_end` past the token so the
    /// following end-of-line mapping lands just after it, as in tsc segments.
    fn raw_mapped_token(&mut self, text: &str, pos: Utf16Pos, width: usize) {
        if text.is_empty() {
            return;
        }
        let end = Utf16Pos::new(pos.get().saturating_add(width));
        match TextRange::new(pos, end) {
            Ok(range) => self.raw_mapped(text, range),
            Err(_) => self.raw_mapped_pos(text, pos),
        }
    }

    /// UTF-16 position of the first `ch` occurring in the source within `range`.
    fn source_pos_of(&self, range: TextRange, ch: char) -> Option<Utf16Pos> {
        let start_byte = self.source.utf16_to_byte(range.start()).ok()?;
        let end_byte = self.source.utf16_to_byte(range.end()).ok()?;
        let text = self.source.as_str().get(start_byte..end_byte)?;
        let index = text.find(ch)?;
        Some(Utf16Pos::new(
            range.start().get() + utf16_len(&text[..index]),
        ))
    }

    /// UTF-16 position of the last `ch` occurring in the source within `range`.
    fn source_pos_of_last(&self, range: TextRange, ch: char) -> Option<Utf16Pos> {
        let start_byte = self.source.utf16_to_byte(range.start()).ok()?;
        let end_byte = self.source.utf16_to_byte(range.end()).ok()?;
        let text = self.source.as_str().get(start_byte..end_byte)?;
        let index = text.rfind(ch)?;
        Some(Utf16Pos::new(
            range.start().get() + utf16_len(&text[..index]),
        ))
    }
    /// Whether `id` is a synthesized node produced by the rewriter.
    fn is_synthesized(&self, id: NodeId) -> bool {
        self.synthesized.is_some_and(|set| set.contains(&id))
    }

    /// Whether a node with `id` and `range` preserves single-line emit:
    /// not synthesized, range non-empty, range within authored text, and
    /// the source text does not span multiple lines.
    fn preserves_single_line(&self, id: NodeId, range: TextRange) -> bool {
        if self.is_synthesized(id) {
            return false;
        }
        if range.start() == range.end() {
            return false;
        }
        // Mint gate: a parser-assigned id (below the rewriter floor) must
        // have a range within the authored content. NameBank::intern appends
        // to the extended text, so a range past `authored_len` on a
        // non-synthesized id indicates a lowering bug.
        debug_assert!(
            id.get() >= self.synthesized_floor || range.end() <= self.authored_len,
            "parser id {id:?} has range past authored_len"
        );
        if range.end() > self.authored_len {
            return false;
        }
        !self.source.spans_multiple_lines(range)
    }

    /// Whether a node is authored (not synthesized, range within the
    /// authored text). The empty-body layout gate keys on this before
    /// consulting authored line structure.
    fn node_spans_authored_lines<T>(&self, node: &Node<T>) -> bool {
        if self.is_synthesized(node.id()) {
            return false;
        }
        node.range().end() <= self.authored_len
    }

    /// Thin wrapper: checks a single AST node by its id and range.
    fn node_preserves_single_line<T>(&self, node: &Node<T>) -> bool {
        self.preserves_single_line(node.id(), node.range())
    }

    /// Maps `text` to the source position of `ch` inside `range`, falling back
    /// to `range.start()` when the character cannot be located.
    fn raw_mapped_char(&mut self, text: &str, range: TextRange, ch: char, width: usize) {
        let pos = self.source_pos_of(range, ch).unwrap_or(range.start());
        self.raw_mapped_token(text, pos, width);
    }

    /// Maps `text` to the last `ch` inside `range` (closing punctuation sits at
    /// the tail of the owning node), falling back to the last unit of `range`.
    fn raw_mapped_char_end(&mut self, text: &str, range: TextRange, ch: char) {
        let pos = self
            .source_pos_of_last(range, ch)
            .unwrap_or_else(|| Utf16Pos::new(range.end().get().saturating_sub(1)));
        self.raw_mapped_token(text, pos, 1);
    }

    /// Writes `text` without a glyph segment, then sets `last_mapped_end` to
    /// the source position just past the last `ch` in `range`. The next
    /// `newline()` emits an EOL segment at that position — matching tsc's
    /// convention for class-body close braces, which get an EOL segment but no
    /// glyph segment.
    fn raw_mapped_eol(&mut self, text: &str, range: TextRange, ch: char) {
        self.raw(text);
        let pos = self
            .source_pos_of_last(range, ch)
            .unwrap_or_else(|| Utf16Pos::new(range.end().get().saturating_sub(1)));
        if let Ok(end) = TextRange::new(pos, Utf16Pos::new(pos.get() + 1)) {
            self.last_mapped_end = Some(end);
        }
    }

    /// Maps the `, ` separator to the comma between two list elements.
    fn raw_mapped_list_separator(&mut self, previous_end: Utf16Pos, next: TextRange) {
        if let Some(window) = TextRange::new(previous_end, next.start())
            .ok()
            .filter(|range| !range.is_empty())
            && let Some(pos) = self.source_pos_of(window, ',')
        {
            self.raw_mapped_token(", ", pos, 1);
            return;
        }
        self.raw_mapped_pos(", ", next.start());
    }

    /// Emits the `, ` separator preceding a list element, anchoring the comma
    /// to its own source position found between `cursor` and `limit`. Returns
    /// the position just past the comma, or `cursor` when it cannot be located.
    fn mapped_list_separator_from(&mut self, cursor: Utf16Pos, limit: Utf16Pos) -> Utf16Pos {
        if let Some(window) = TextRange::new(cursor, limit)
            .ok()
            .filter(|range| !range.is_empty())
            && let Some(pos) = self.source_pos_of(window, ',')
        {
            self.raw_mapped_token(", ", pos, 1);
            return Utf16Pos::new(pos.get().saturating_add(1));
        }
        self.raw_mapped_pos(", ", cursor);
        cursor
    }

    /// Start position of `keyword` when it is the word immediately preceding
    /// `pos` in the source, ignoring intervening whitespace.
    fn keyword_start_before(&self, pos: Utf16Pos, keyword: &str) -> Option<Utf16Pos> {
        let end_byte = self.source.utf16_to_byte(pos).ok()?;
        let text = self.source.as_str().get(..end_byte)?;
        let trimmed = text.trim_end();
        let start = trimmed.len().checked_sub(keyword.len())?;
        if !trimmed[start..].starts_with(keyword) {
            return None;
        }
        let boundary_ok = trimmed[..start].chars().next_back().is_none_or(|previous| {
            !(previous.is_alphanumeric() || previous == '_' || previous == '$')
        });
        if !boundary_ok {
            return None;
        }
        self.source.byte_to_utf16(start).ok()
    }

    /// End position of the last parameter, for use as a scan window start.
    fn params_source_end(&self, parameters: &[ParameterNode]) -> Utf16Pos {
        parameters.last().map_or(Utf16Pos::ZERO, |parameter| {
            let parameter = parameter.data();
            parameter.initializer.as_ref().map_or_else(
                || parameter.binding.range().end(),
                |initializer| initializer.range().end(),
            )
        })
    }

    /// Records an end-of-line mapping: the current generated column
    /// (after the last token on this line, before the newline) maps to
    /// the source position just past the last mapped token's end.
    fn end_of_line(&mut self) {
        let Some(builder) = self.map.as_mut() else {
            return;
        };
        let Some(range) = self.last_mapped_end else {
            return;
        };
        let Ok((line, column)) = self.source.line_column(range.end()) else {
            return;
        };
        builder.add_mapping(
            self.source_name,
            LineColumn::new(self.generated_line, self.generated_column),
            LineColumn::new(line, column),
            None,
        );
    }

    fn newline(&mut self) {
        if self.map.is_some() {
            self.end_of_line();
        }
        self.out.push_str(self.options.newline.as_str());
        if self.map.is_some() {
            self.generated_line += 1;
            self.generated_column = 0;
        }
        self.pending_indent = true;
    }

    /// Flushes pending indentation, updating `generated_column`.
    fn flush_indent(&mut self) {
        if self.pending_indent {
            let spaces = self.indent * self.options.indent_width as usize;
            for _ in 0..spaces {
                self.out.push(' ');
            }
            if self.map.is_some() {
                self.generated_column += spaces;
            }
            self.pending_indent = false;
        }
    }

    /// Writes text to `out`, tracking `generated_line` / `generated_column`.
    fn write_text(&mut self, text: &str) {
        if self.map.is_some() {
            for ch in text.chars() {
                if ch == '\n' {
                    self.generated_line += 1;
                    self.generated_column = 0;
                } else {
                    self.generated_column += ch.len_utf16();
                }
            }
        }
        self.out.push_str(text);
    }

    /// Returns the current indentation level in spaces.
    fn current_indent_spaces(&self) -> usize {
        self.indent * self.options.indent_width as usize
    }
    /// Records the current generated position against the original position
    /// of `range.start()`.
    fn record_mapping(&mut self, range: TextRange) {
        let Some(builder) = self.map.as_mut() else {
            return;
        };
        let Ok((line, column)) = self.source.line_column(range.start()) else {
            return;
        };
        builder.add_mapping(
            self.source_name,
            LineColumn::new(self.generated_line, self.generated_column),
            LineColumn::new(line, column),
            None,
        );
    }

    fn diag(&mut self, code: DiagnosticCode, message: &'static str, range: TextRange) {
        self.diagnostics
            .push(Diagnostic::error(code, self.source_id, range, message));
    }

    fn diag_here(&mut self, code: DiagnosticCode, message: &'static str) {
        let range = self.anchor;
        self.diag(code, message, range);
    }

    /// Zero-copy lexeme for a token, or `None` for an invalid slice.
    fn text(&self, token: &Token) -> Option<&'a str> {
        if token.is_missing() {
            return Some("");
        }
        let source: &'a SourceText = self.source;
        let range = token.range();
        let start = source.utf16_to_byte(range.start()).ok()?;
        let end = source.utf16_to_byte(range.end()).ok()?;
        source.as_str().get(start..end)
    }

    fn emit_token(&mut self, token: &Token) {
        let range = token.range();
        match self.text(token) {
            Some(text) => self.raw_mapped(text, range),
            None => {
                self.diag(
                    codes::UNRESOLVED_TOKEN,
                    "token text is not a valid slice of the source",
                    range,
                );
            }
        }
    }

    fn emit_ident(&mut self, ident: &IdentifierNode) {
        let range = ident.range();
        if let Some(text) = self.generated_text(ident.id()).map(str::to_owned) {
            self.raw_mapped(&text, range);
        } else {
            self.emit_token(ident.data().token());
        }
    }

    fn emit_string(&mut self, literal: &StringLiteralNode) {
        if let Some(text) = self.generated_text(literal.id()) {
            let mut quoted = String::with_capacity(text.len() + 2);
            quoted.push('"');
            for character in text.chars() {
                match character {
                    '"' => quoted.push_str("\\\""),
                    '\\' => quoted.push_str("\\\\"),
                    '\n' => quoted.push_str("\\n"),
                    '\r' => quoted.push_str("\\r"),
                    '\t' => quoted.push_str("\\t"),
                    '\u{2028}' => quoted.push_str("\\u2028"),
                    '\u{2029}' => quoted.push_str("\\u2029"),
                    character if character.is_control() => {
                        use std::fmt::Write;
                        write!(quoted, "\\u{:04x}", character as u32)
                            .expect("writing to a String cannot fail");
                    }
                    character => quoted.push(character),
                }
            }
            quoted.push('"');
            self.raw_mapped(&quoted, literal.range());
        } else {
            self.emit_token(literal.data().token());
        }
    }

    fn generated_text(&self, id: NodeId) -> Option<&str> {
        self.jsx_plan.and_then(|plan| plan.generated_text.get(id))
    }

    // ---- module drivers ---------------------------------------------------

    fn emit_module_js(&mut self, statements: &[Stmt]) {
        self.emit_statement_list(statements);
    }

    fn emit_module_decl(&mut self, statements: &[Stmt]) {
        self.decl_ambient = true;
        for statement in statements {
            if self.emit_declaration(statement) {
                self.newline();
            }
        }
    }

    // =======================================================================
    // JavaScript statements
    // =======================================================================

    fn emit_statement(&mut self, statement: &Stmt) -> bool {
        let previous = self.anchor;
        self.anchor = statement.range();
        let stmt_range = self.anchor;
        let emitted = match statement.data() {
            Statement::Import(import) => self.emit_import(import, false),
            Statement::ImportEquals(import) => {
                if import.is_type_only {
                    false
                } else {
                    self.emit_import_equals_js(import);
                    true
                }
            }
            Statement::Export(export) => self.emit_export_js(export),
            Statement::Variable(declaration) => {
                self.emit_variable_head(declaration);
                let semi_start = Utf16Pos::new(stmt_range.end().get().saturating_sub(1));
                let semi_end = stmt_range.end();
                let semi_range = TextRange::new(semi_start, semi_end).unwrap_or(stmt_range);
                self.raw_mapped(";", semi_range);
                true
            }
            Statement::Function(function) => {
                if function.function.body.is_none() {
                    false
                } else {
                    self.emit_function_declaration_js(&function.function, stmt_range);
                    true
                }
            }
            Statement::Class(class) => {
                self.emit_class_js(class);
                true
            }
            Statement::Interface(_) | Statement::TypeAlias(_) | Statement::Declare(_) => false,
            Statement::Enum(declaration) => self.emit_enum_js(statement.id(), declaration),
            Statement::Namespace(_) => {
                self.diag_here(
                    codes::NAMESPACE_UNLOWERED,
                    "namespace runtime lowering requires semantic analysis",
                );
                false
            }
            Statement::Block(block) => {
                self.emit_block(block);
                true
            }
            Statement::Empty => false,
            Statement::Expression(statement) => {
                self.emit_expression_statement(statement);
                true
            }
            Statement::If(_) => {
                self.emit_if(statement);
                true
            }
            Statement::Switch(switch) => {
                self.emit_switch(switch);
                true
            }
            Statement::For(statement) => {
                self.emit_for(statement);
                true
            }
            Statement::ForIn(statement) => {
                self.emit_for_in(statement);
                true
            }
            Statement::ForOf(statement) => {
                self.emit_for_of(statement);
                true
            }
            Statement::While(statement) => {
                self.raw_mapped_char("while (", self.anchor, 'w', 5);
                self.emit_expression(&statement.test);
                self.raw_mapped_pos(")", statement.test.range().end());
                self.emit_control_body(&statement.body);
                true
            }
            Statement::DoWhile(statement) => {
                self.raw_mapped_char("do", self.anchor, 'd', 2);
                self.emit_control_body(&statement.body);
                let while_pos = self
                    .keyword_start_before(statement.test.range().start(), "while")
                    .unwrap_or(self.anchor.end());
                self.raw_mapped_token(" while (", while_pos, 5);
                self.emit_expression(&statement.test);
                self.raw_mapped_pos(");", statement.test.range().end());
                true
            }
            Statement::Try(statement) => {
                self.emit_try(statement);
                true
            }
            Statement::With(statement) => {
                self.raw("with (");
                self.emit_expression(&statement.object);
                self.raw(")");
                self.emit_control_body(&statement.body);
                true
            }
            Statement::Labeled(statement) => {
                self.emit_ident(&statement.label);
                self.raw(": ");
                self.emit_statement(&statement.body);
                true
            }
            Statement::Break(jump) => {
                self.raw_mapped_char("break", self.anchor, 'b', 5);
                if let Some(label) = &jump.label {
                    self.raw(" ");
                    self.emit_ident(label);
                }
                self.raw_mapped_pos(
                    ";",
                    Utf16Pos::new(self.anchor.end().get().saturating_sub(1)),
                );
                true
            }
            Statement::Continue(jump) => {
                self.raw_mapped_char("continue", self.anchor, 'c', 8);
                if let Some(label) = &jump.label {
                    self.raw(" ");
                    self.emit_ident(label);
                }
                self.raw_mapped_pos(
                    ";",
                    Utf16Pos::new(self.anchor.end().get().saturating_sub(1)),
                );
                true
            }
            Statement::Return(statement) => {
                self.raw_mapped_char("return", self.anchor, 'r', 6);
                if let Some(argument) = &statement.argument {
                    self.raw(" ");
                    self.emit_expression(argument);
                }
                self.raw_mapped_pos(
                    ";",
                    Utf16Pos::new(self.anchor.end().get().saturating_sub(1)),
                );
                true
            }
            Statement::Throw(statement) => {
                self.raw_mapped_char("throw ", self.anchor, 't', 5);
                self.emit_expression(&statement.argument);
                self.raw_mapped_pos(
                    ";",
                    Utf16Pos::new(self.anchor.end().get().saturating_sub(1)),
                );
                true
            }
            Statement::Debugger => {
                self.raw_mapped_char("debugger", self.anchor, 'd', 8);
                self.raw_mapped_pos(
                    ";",
                    Utf16Pos::new(self.anchor.end().get().saturating_sub(1)),
                );
                true
            }
            Statement::Missing(_) => {
                self.diag_here(
                    codes::MISSING_STATEMENT,
                    "cannot emit a missing statement node",
                );
                self.raw(";");
                true
            }
        };
        self.anchor = previous;
        emitted
    }

    fn emit_expression_statement(&mut self, statement: &ExpressionStatement) {
        let expression = &statement.expression;
        // Manual wrapping is only needed when emission would otherwise start
        // with a bare `{`, `function`, or `class`: a printed `(` anywhere on
        // the left edge already protects the statement position.
        let wrap =
            !self.starts_parenthesized(expression) && self.leads_with_bad_token(expression, false);
        if wrap {
            self.raw("(");
            self.emit_expression_prec(expression, 0);
            self.raw(")");
        } else {
            self.emit_expression_prec(expression, 0);
        }
        let semi_start = Utf16Pos::new(self.anchor.end().get().saturating_sub(1));
        let semi_end = self.anchor.end();
        let semi_range = TextRange::new(semi_start, semi_end).unwrap_or(self.anchor);
        self.raw_mapped(";", semi_range);
    }

    fn emit_if(&mut self, statement: &Stmt) {
        let Statement::If(if_statement) = statement.data() else {
            return;
        };
        self.raw_mapped("if (", self.anchor);
        self.emit_expression(&if_statement.test);
        self.raw_mapped_pos(")", if_statement.test.range().end());
        let hug = if_statement.test.id().get() >= self.synthesized_floor;
        self.emit_control_body_hug(&if_statement.consequent, hug);
        let machine_if = statement.id().get() >= self.synthesized_floor;
        if let Some(alternate) = &if_statement.alternate {
            let alt_range = alternate.range();
            if machine_if {
                // tsc's machine output breaks before `else`.
                self.newline();
                if matches!(alternate.data(), Statement::If(_)) {
                    let prev = self.anchor;
                    self.anchor = alt_range;
                    self.emit_if(alternate);
                    self.anchor = prev;
                } else {
                    self.raw("else");
                    self.emit_control_body(alternate);
                }
            } else if matches!(alternate.data(), Statement::If(_)) {
                self.raw_mapped_pos(" else ", if_statement.consequent.range().end());
                let prev = self.anchor;
                self.anchor = alt_range;
                self.emit_if(alternate);
                self.anchor = prev;
            } else {
                self.raw_mapped_pos(" else", if_statement.consequent.range().end());
                self.emit_control_body(alternate);
            }
        }
    }

    fn emit_control_body(&mut self, statement: &Stmt) {
        self.emit_control_body_hug(statement, true)
    }

    /// Emits a brace-less control body. `hug` carries tsc's layout rule:
    /// a fully synthesized guard (`if (!x) return [3 /*break*/, 2];`)
    /// keeps the body on the head's line, while a translated body — an
    /// authored test with a synthesized jump — breaks to its own line.
    fn emit_control_body_hug(&mut self, statement: &Stmt, hug: bool) {
        match statement.data() {
            Statement::Block(block) => {
                self.raw(" ");
                self.emit_block_with_braces(block, self.anchor, BlockLayout::Statement)
            }
            Statement::Empty => self.raw(" {}"),
            _ if self.body_authored_same_line(statement) => {
                // tsc keeps a brace-less control body authored on the
                // head's line bare (`if (cond) return mod;`, APISample_*).
                self.raw(" ");
                if self.emit_statement(statement) {
                    self.newline();
                }
            }
            _ if statement.id().get() >= self.synthesized_floor && hug => {
                // Machine control flow keeps the bare form tsc emits for
                // synthesized bodies (`if (!x) return [3 /*break*/, 2];`).
                self.raw(" ");
                self.emit_statement(statement);
            }
            _ if statement.id().get() >= self.synthesized_floor => {
                // A translated jump — authored test, synthesized body —
                // breaks to its own line.
                self.newline();
                self.indent += 1;
                self.emit_statement(statement);
                self.indent -= 1;
            }
            _ => {
                self.raw(" ");
                self.raw_mapped("{", self.anchor);
                self.newline();
                self.indent += 1;
                if self.emit_statement(statement) {
                    self.newline();
                }
                self.indent -= 1;
                self.raw_mapped_pos("}", self.anchor.end());
            }
        }
    }

    /// Whether a brace-less control body starts on the same source line as
    /// the `)` that precedes it — the authored-bare shape tsc preserves.
    fn body_authored_same_line(&self, statement: &Stmt) -> bool {
        let start = statement.range().start();
        let index = self
            .tokens
            .partition_point(|token| token.range().start() < start);
        // Walk back past trivia (whitespace and comments are tokens); the
        // first structural token decides.
        let mut cursor = index;
        let before = loop {
            let Some(candidate) = cursor.checked_sub(1).and_then(|i| self.tokens.get(i)) else {
                return false;
            };
            if !matches!(
                candidate.kind(),
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            ) {
                break candidate;
            }
            cursor -= 1;
        };
        before.kind() == TokenKind::RParen
            && matches!(
                (
                    self.source.line_column(before.range().end()),
                    self.source.line_column(start)
                ),
                (Ok((line_a, _)), Ok((line_b, _))) if line_a == line_b
            )
    }

    fn emit_block(&mut self, block: &BlockNode) {
        let range = block.range();
        self.emit_block_with_braces(block, range, BlockLayout::Statement);
    }

    fn emit_block_with_braces(&mut self, block: &BlockNode, range: TextRange, layout: BlockLayout) {
        let map_open_brace = layout != BlockLayout::FunctionBody;
        let may_preserve = layout != BlockLayout::Statement;
        if block.data().statements.is_empty() {
            if map_open_brace {
                self.raw_mapped_char("{", range, '{', 1);
            } else {
                self.raw("{");
            }
            // Authority, re-derived per context (2026-09-04 census: 285
            // newline-authored to two-line, 1200 same-line to `{ }`, no
            // try-family two-line evidence): same-line-authored empty
            // bodies print `{ }` — the space is synthesized and unmapped —
            // while a function-family body authored across lines keeps its
            // newline (ParameterList6: `constructor(C) {\n}`). Synthesized
            // or out-of-text ranges keep `{ }`.
            if may_preserve
                && self.node_spans_authored_lines(block)
                && self.source.spans_multiple_lines(range)
            {
                self.newline();
            } else {
                self.raw(" ");
            }
            self.raw_mapped_char_end("}", range, '}');
            return;
        }
        // Preservation: a non-empty declaration-family body (function,
        // arrow, static initialization block; ctor checks separately)
        // authored on one line stays on one line (`{ stmt; stmt; }`).
        // Statement-position blocks (standalone, try arms, control bodies)
        // always expand: parser768531's baseline expands an authored
        // single-line `{ a: 3; }`. Synthesized, past-authored-text, or
        // multi-line-authored bodies take the expanded path below.
        if may_preserve && self.node_preserves_single_line(block) {
            if map_open_brace {
                self.raw_mapped_char("{", range, '{', 1);
            } else {
                self.raw("{");
            }
            self.raw(" ");
            for statement in &block.data().statements {
                let _ = self.emit_statement(statement);
                self.raw(" ");
            }
            self.raw_mapped_char_end("}", range, '}');
            return;
        }
        if map_open_brace {
            self.raw_mapped_char("{", range, '{', 1);
        } else {
            self.raw("{");
        }
        self.newline();
        self.indent += 1;
        self.emit_statement_list(&block.data().statements);
        self.indent -= 1;
        self.raw_mapped_char_end("}", range, '}');
    }
    fn emit_switch(&mut self, switch: &SwitchStatement) {
        let range = self.anchor;
        self.raw_mapped("switch (", range);
        self.emit_expression(&switch.discriminant);
        self.raw_mapped_pos(") ", switch.discriminant.range().end());
        if switch.cases.is_empty() {
            self.raw_mapped_char("{", range, '{', 1);
            self.raw_mapped_char_end("}", range, '}');
            return;
        }
        self.raw_mapped_char("{", range, '{', 1);
        self.newline();
        self.indent += 1;
        for case_node in &switch.cases {
            let case = case_node.data();
            let case_range = case_node.range();
            match &case.test {
                Some(test) => {
                    self.raw_mapped("case ", case_range);
                    self.emit_expression(test);
                    self.raw_mapped_pos(":", test.range().end());
                }
                None => self.raw_mapped("default:", case_range),
            }
            // Synthesized machines (the __generator state machine) print a
            // single-statement case inline the way tsc emits them. The
            // discriminator is the case test: authored tests live inside the
            // authored text, machine tests are interned past its end.
            let inline = case.consequent.len() == 1
                && case
                    .test
                    .as_ref()
                    .is_some_and(|test| test.range().end() > self.authored_len);
            if inline {
                self.raw(" ");
                self.emit_statement(&case.consequent[0]);
                self.newline();
                continue;
            }
            self.newline();
            if !case.consequent.is_empty() {
                self.indent += 1;
                self.emit_statement_list(&case.consequent);
                self.indent -= 1;
            }
        }
        self.indent -= 1;
        self.raw_mapped_char_end("}", range, '}');
    }

    fn emit_for(&mut self, statement: &ForStatement) {
        self.raw_mapped("for (", self.anchor);
        match &statement.initializer {
            Some(ForInitializer::Variable(declaration)) => self.emit_variable_head(declaration),
            Some(ForInitializer::Expression(expression)) => {
                self.emit_expression_prec(expression, 0);
            }
            None => {}
        }
        self.raw(";");
        if let Some(test) = &statement.test {
            self.raw(" ");
            self.emit_expression(test);
        }
        self.raw(";");
        if let Some(update) = &statement.update {
            self.raw(" ");
            self.emit_expression(update);
        }
        self.raw_mapped_pos(")", self.anchor.end());
        self.emit_control_body(&statement.body);
    }

    fn emit_for_in(&mut self, statement: &ForInStatement) {
        let range = self.anchor;
        self.raw_mapped_char("for (", range, 'f', 3);
        self.emit_for_binding(&statement.binding);
        let in_pos = self
            .keyword_start_before(statement.object.range().start(), "in")
            .unwrap_or(range.end());
        self.raw_mapped_token(" in ", Utf16Pos::new(in_pos.get().saturating_sub(1)), 2);
        self.emit_expression_prec(&statement.object, P_ASSIGN);
        self.raw_mapped_pos(")", statement.object.range().end());
        self.emit_control_body(&statement.body);
    }

    fn emit_for_of(&mut self, statement: &ForOfStatement) {
        let range = self.anchor;
        if matches!(statement.mode, ForOfMode::Async) {
            self.raw_mapped_char("for await (", range, 'f', 3);
        } else {
            self.raw_mapped_char("for (", range, 'f', 3);
        }
        self.emit_for_binding(&statement.binding);
        let of_pos = self
            .keyword_start_before(statement.iterable.range().start(), "of")
            .unwrap_or(range.end());
        self.raw_mapped_token(" of ", Utf16Pos::new(of_pos.get().saturating_sub(1)), 2);
        self.emit_expression_prec(&statement.iterable, P_ASSIGN);
        self.raw_mapped_pos(")", statement.iterable.range().end());
        self.emit_control_body(&statement.body);
    }

    fn emit_for_binding(&mut self, binding: &ForBinding) {
        match binding {
            ForBinding::Variable(declaration) => self.emit_variable_head(declaration),
            ForBinding::Target(target) => self.emit_assignment_target(target),
        }
    }

    fn emit_try(&mut self, statement: &TryStatement) {
        self.raw_mapped("try ", self.anchor);
        self.emit_block(&statement.block);
        if let Some(handler) = &statement.handler {
            let handler_range = handler.range();
            let handler = handler.data();
            self.raw_mapped(" catch", handler_range);
            if let Some(binding) = &handler.binding {
                self.raw(" (");
                self.emit_pattern(binding);
                self.raw_mapped_pos(")", binding.range().end());
            }
            self.raw(" ");
            self.emit_block(&handler.body);
        }
        if let Some(finalizer) = &statement.finalizer {
            self.raw_mapped(" finally ", finalizer.range());
            self.emit_block(finalizer);
        }
    }

    fn emit_variable_head(&mut self, declaration: &VariableDeclaration) {
        self.raw_mapped(variable_kind_str(declaration.kind), declaration.range);
        self.raw(" ");
        for (index, declarator_node) in declaration.declarations.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            let declarator = declarator_node.data();
            self.emit_pattern(&declarator.binding);
            if let Some(initializer) = &declarator.initializer {
                self.raw_mapped_pos(" = ", declarator.binding.range().end());
                self.emit_expression_prec(initializer, P_ASSIGN);
            }
        }
    }

    // ---- imports / exports (JavaScript) -----------------------------------

    fn emit_import(&mut self, import: &ImportDeclaration, keep_types: bool) -> bool {
        if import.type_only && !keep_types {
            return false;
        }

        // A clause that resolves to no value bindings is fully type-only and is
        // erased in JavaScript (a bare side-effect import keeps its clause-less
        // form below).
        if !keep_types && let Some(clause) = &import.clause {
            let has_value = clause.default.is_some()
                || matches!(&clause.binding, Some(ImportBinding::Namespace(_)))
                || matches!(
                    &clause.binding,
                    Some(ImportBinding::Named(specifiers))
                        if specifiers
                            .iter()
                            .any(|s| matches!(s.data().mode, ImportSpecifierMode::Value))
                );
            if !has_value {
                return false;
            }
        }

        self.raw("import ");
        if keep_types && import.type_only {
            self.raw("type ");
        }
        if let Some(clause) = &import.clause {
            let mut wrote = false;
            if let Some(default) = &clause.default {
                self.emit_ident(default);
                wrote = true;
            }
            if let Some(binding) = &clause.binding {
                match binding {
                    ImportBinding::Namespace(name) => {
                        if wrote {
                            self.raw(", ");
                        }
                        self.raw("* as ");
                        self.emit_ident(name);
                    }
                    ImportBinding::Named(specifiers) => {
                        if wrote {
                            self.raw(", ");
                        }
                        self.emit_named_imports(specifiers, keep_types);
                    }
                }
            }
            self.raw(" from ");
        }
        self.emit_string(&import.source);
        if let Some(attributes) = &import.attributes {
            self.emit_import_attributes(attributes);
        }
        self.raw(";");
        true
    }

    fn emit_named_imports(&mut self, specifiers: &[ImportSpecifierNode], keep_types: bool) {
        let visible: Vec<&ImportSpecifierNode> = specifiers
            .iter()
            .filter(|s| keep_types || matches!(s.data().mode, ImportSpecifierMode::Value))
            .collect();
        if visible.is_empty() {
            self.raw("{}");
            return;
        }
        self.raw("{ ");
        for (index, specifier) in visible.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            let specifier = specifier.data();
            if keep_types && matches!(specifier.mode, ImportSpecifierMode::TypeOnly) {
                self.raw("type ");
            }
            if self.module_name_matches_ident(&specifier.imported, &specifier.local) {
                self.emit_ident(&specifier.local);
            } else {
                self.emit_module_export_name(&specifier.imported);
                self.raw(" as ");
                self.emit_ident(&specifier.local);
            }
        }
        self.raw(" }");
    }

    fn emit_import_attributes(&mut self, attributes: &ImportAttributes) {
        if attributes.entries.is_empty() {
            return;
        }
        self.raw(" with { ");
        for (index, entry) in attributes.entries.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            self.emit_module_export_name(&entry.name);
            self.raw(": ");
            self.emit_string(&entry.value);
        }
        self.raw(" }");
    }

    fn emit_import_equals_js(&mut self, import: &ImportEqualsDeclaration) {
        self.raw("const ");
        self.emit_ident(&import.local);
        self.raw(" = ");
        match &import.reference {
            ExternalModuleReference::Require(source) => {
                self.raw("require(");
                self.emit_string(source);
                self.raw(")");
            }
            ExternalModuleReference::Qualified(name) => self.emit_entity_name(name),
            ExternalModuleReference::Missing(_) => {
                self.diag_here(
                    codes::MISSING_NAME,
                    "cannot emit a missing module reference",
                );
            }
        }
        self.raw(";");
    }

    fn emit_export_js(&mut self, export: &ExportDeclaration) -> bool {
        match export {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) => {
                if !self.js_statement_emits(inner) {
                    // Trigger any recovery diagnostics without a dangling `export`.
                    self.emit_statement(inner);
                    return false;
                }
                if let Statement::Class(class) = inner.data() {
                    self.emit_decorators_block(&class.decorators);
                    self.raw("export ");
                    self.emit_class_core_js(class);
                    return true;
                }
                self.raw("export ");
                self.emit_statement(inner)
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source,
                attributes,
            }) => {
                if *type_only {
                    return false;
                }
                let visible: Vec<&ExportSpecifierNode> = specifiers
                    .iter()
                    .filter(|s| matches!(s.data().mode, ExportSpecifierMode::Value))
                    .collect();
                if visible.is_empty() {
                    return false;
                }
                self.raw("export { ");
                for (index, specifier) in visible.iter().enumerate() {
                    if index > 0 {
                        self.raw(", ");
                    }
                    self.emit_export_specifier(specifier.data(), false);
                }
                self.raw(" }");
                if let Some(source) = source {
                    self.raw(" from ");
                    self.emit_string(source);
                    if let Some(attributes) = attributes {
                        self.emit_import_attributes(attributes);
                    }
                }
                self.raw(";");
                true
            }
            ExportDeclaration::All(all) => {
                if all.type_only {
                    return false;
                }
                self.raw("export * ");
                if let Some(name) = &all.exported {
                    self.raw("as ");
                    self.emit_module_export_name(name);
                    self.raw(" ");
                }
                self.raw("from ");
                self.emit_string(&all.source);
                if let Some(attributes) = &all.attributes {
                    self.emit_import_attributes(attributes);
                }
                self.raw(";");
                true
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    self.raw("export default ");
                    let function_range = self
                        .keyword_start_before(self.anchor.end(), "function")
                        .map_or(self.anchor, |start| {
                            TextRange::new(start, self.anchor.end()).unwrap_or(self.anchor)
                        });
                    self.emit_function_declaration_js(function, function_range);
                    true
                }
                ExportDefaultValue::Class(class) => {
                    self.emit_decorators_block(&class.decorators);
                    self.raw("export default ");
                    self.emit_class_core_js(class);
                    true
                }
                ExportDefaultValue::Interface(_) => false,
                ExportDefaultValue::Expression(expression) => {
                    self.raw("export default ");
                    self.emit_expression_prec(expression, P_ASSIGN);
                    self.raw(";");
                    true
                }
                ExportDefaultValue::Missing(_) => {
                    self.diag_here(
                        codes::MISSING_EXPRESSION,
                        "cannot emit a missing default export",
                    );
                    false
                }
            },
            ExportDeclaration::Assignment(expression) => {
                self.raw("export default ");
                self.emit_expression_prec(expression, P_ASSIGN);
                self.raw(";");
                true
            }
        }
    }

    fn emit_export_specifier(&mut self, specifier: &ExportSpecifier, keep_type: bool) {
        if keep_type && matches!(specifier.mode, ExportSpecifierMode::TypeOnly) {
            self.raw("type ");
        }
        if self.module_names_match(&specifier.local, &specifier.exported) {
            self.emit_module_export_name(&specifier.local);
        } else {
            self.emit_module_export_name(&specifier.local);
            self.raw(" as ");
            self.emit_module_export_name(&specifier.exported);
        }
    }

    fn js_statement_emits(&self, statement: &Stmt) -> bool {
        match statement.data() {
            Statement::Interface(_)
            | Statement::TypeAlias(_)
            | Statement::Declare(_)
            | Statement::Namespace(_)
            | Statement::Empty => false,
            Statement::Function(function) => function.function.body.is_some(),
            Statement::Import(import) => !import.type_only,
            Statement::Enum(declaration) => !declaration.is_const,
            _ => true,
        }
    }

    // =======================================================================
    // enum lowering (JavaScript)
    // =======================================================================

    fn emit_enum_js(&mut self, declaration_id: NodeId, declaration: &EnumDeclaration) -> bool {
        let Some(name) = self
            .text(declaration.name.data().token())
            .map(str::to_owned)
        else {
            self.diag(
                codes::UNRESOLVED_TOKEN,
                "token text is not a valid slice of the source",
                declaration.name.range(),
            );
            return false;
        };
        if name.is_empty() || declaration.is_const {
            return false;
        }
        let Some(plan) = self.enum_facts.declaration(declaration_id) else {
            self.diag_here(
                codes::ENUM_FACTS_UNAVAILABLE,
                "runtime enum lowering requires checked enum facts",
            );
            return false;
        };
        if plan.members().len() != declaration.members.len() {
            self.diag_here(
                codes::ENUM_FACTS_UNAVAILABLE,
                "runtime enum lowering requires a complete checked enum plan",
            );
            return false;
        }

        self.raw("var ");
        self.raw(&name);
        self.raw(";");
        self.newline();
        self.raw("(function (");
        self.raw(&name);
        self.raw(") {");
        self.newline();
        self.indent += 1;
        for (member, plan_member) in declaration.members.iter().zip(plan.members()) {
            if self.emit_enum_member(&name, member.data(), plan_member) {
                self.newline();
            }
        }
        self.indent -= 1;
        self.raw("})(");
        self.raw(&name);
        self.raw(" || (");
        self.raw(&name);
        self.raw(" = {}));");
        true
    }

    fn emit_enum_member(
        &mut self,
        object: &str,
        member: &EnumMember,
        plan_member: &EnumMemberPlan,
    ) -> bool {
        let (Some(key), Some(value)) = (plan_member.name(), plan_member.value()) else {
            return false;
        };
        let initializer = member.initializer.as_deref();
        if value.constant().is_none() && initializer.is_none() {
            return false;
        }

        self.raw(object);
        self.raw("[");
        if plan_member.reverse() {
            self.raw(object);
            self.raw("[");
        }
        self.emit_enum_string(key);
        self.raw("] = ");
        if let Some(constant) = value.constant() {
            self.emit_enum_scalar(constant);
        } else if let Some(initializer) = initializer {
            self.emit_expression_prec(initializer, P_ASSIGN);
        }
        if plan_member.reverse() {
            self.raw("] = ");
            self.emit_enum_string(key);
        }
        self.raw(";");
        true
    }

    fn emit_enum_scalar(&mut self, scalar: &EnumScalar) {
        match scalar {
            EnumScalar::Number(value) => {
                let value = value.to_f64();
                if value.is_nan() {
                    self.raw("NaN");
                } else if value == f64::INFINITY {
                    self.raw("Infinity");
                } else if value == f64::NEG_INFINITY {
                    self.raw("-Infinity");
                } else {
                    write!(self.out, "{value}").expect("writing to a String cannot fail");
                }
            }
            EnumScalar::String(value) => self.emit_enum_string(value),
        }
    }

    fn emit_enum_string(&mut self, value: &bamts_bytecode::EcmaString) {
        self.raw("\"");
        for &unit in value.as_units() {
            match unit {
                0x08 => self.raw("\\b"),
                0x09 => self.raw("\\t"),
                0x0A => self.raw("\\n"),
                0x0C => self.raw("\\f"),
                0x0D => self.raw("\\r"),
                0x22 => self.raw("\\\""),
                0x5C => self.raw("\\\\"),
                0x20..=0x7E => self
                    .out
                    .push(char::from_u32(u32::from(unit)).expect("ASCII unit")),
                _ => write!(self.out, "\\u{unit:04X}").expect("writing to a String cannot fail"),
            }
        }
        self.raw("\"");
    }

    // =======================================================================
    // functions / classes (JavaScript)
    // =======================================================================

    fn emit_function_declaration_js(&mut self, function: &FunctionLike, range: TextRange) {
        if function.is_async {
            self.raw_mapped_char("async ", range, 'a', 5);
        }
        let keyword_pos = function
            .name
            .as_ref()
            .and_then(|name| self.keyword_start_before(name.range().start(), "function"))
            .unwrap_or(range.start());
        self.raw_mapped_token("function", keyword_pos, 8);
        if function.is_generator {
            self.raw_mapped_char("*", range, '*', 1);
        }
        if let Some(name) = &function.name {
            self.raw(" ");
            self.emit_ident(name);
        }
        self.emit_params_js(&function.parameters, range);
        self.raw(" ");
        self.emit_function_body_js(function.body.as_ref());
    }

    fn emit_function_expression_js(&mut self, function: &FunctionLike, range: TextRange) {
        if function.is_async {
            self.raw_mapped_char("async ", range, 'a', 5);
        }
        let keyword_pos = function
            .name
            .as_ref()
            .and_then(|name| self.keyword_start_before(name.range().start(), "function"))
            .unwrap_or(range.start());
        self.raw_mapped_token("function", keyword_pos, 8);
        if function.is_generator {
            self.raw_mapped_char("*", range, '*', 1);
        }
        if let Some(name) = &function.name {
            self.raw(" ");
            self.emit_ident(name);
        } else {
            // Anonymous expressions carry a synthesized space before the
            // parameter list (`function (val)`, `function* ()`, even async):
            // authority FunctionExpression1_es6, asyncAwaitIsolatedModules,
            // and 2dArrays all print it; named forms bind the space to the
            // name instead.
            self.raw(" ");
        }
        self.emit_params_js(&function.parameters, range);
        self.raw(" ");
        self.emit_function_body_js(function.body.as_ref());
    }

    fn emit_arrow_js(&mut self, arrow: &ArrowFunction, range: TextRange) {
        if arrow.is_async {
            self.raw_mapped_char("async ", range, 'a', 5);
        }
        if self.arrow_params_authored_bare(arrow) {
            // tsc preserves the authored bare form for a single plain
            // identifier parameter (`props => {`); parenthesized forms keep
            // their parens (arrowFunctionContexts).
            if let Some(parameter) = arrow.parameters.first() {
                self.emit_pattern(&parameter.data().binding);
            }
        } else {
            self.emit_params_js(&arrow.parameters, range);
        }
        let arrow_pos = self
            .source_pos_of(
                TextRange::new(self.params_source_end(&arrow.parameters), range.end())
                    .unwrap_or(range),
                '=',
            )
            .unwrap_or(range.end());
        self.raw_mapped_token(" => ", arrow_pos, 2);
        match &arrow.body {
            FunctionBody::Block(block) => {
                self.emit_block_with_braces(block, block.range(), BlockLayout::FunctionBody);
            }
            FunctionBody::Expression(expression) => {
                if !self.starts_parenthesized(expression)
                    && self.leads_with_bad_token(expression, true)
                {
                    self.raw("(");
                    self.emit_expression_prec(expression, 0);
                    self.raw(")");
                } else {
                    self.emit_expression_prec(expression, P_ASSIGN);
                }
            }
            FunctionBody::Missing(_) => {
                self.diag_here(
                    codes::MISSING_STATEMENT,
                    "cannot emit a missing function body",
                );
                self.raw("{}");
            }
        }
    }

    fn emit_function_body_js(&mut self, body: Option<&FunctionBody>) {
        match body {
            Some(FunctionBody::Block(block)) => {
                self.emit_block_with_braces(block, block.range(), BlockLayout::FunctionBody);
            }
            Some(FunctionBody::Expression(expression)) => {
                self.raw("{ return ");
                self.emit_expression_prec(expression, 0);
                self.raw("; }");
            }
            Some(FunctionBody::Missing(_)) | None => {
                self.diag_here(
                    codes::MISSING_STATEMENT,
                    "cannot emit a missing function body",
                );
                self.raw("{}");
            }
        }
    }

    fn emit_params_js(&mut self, parameters: &[ParameterNode], window: TextRange) {
        // tsc leaves an empty parameter list unmapped: only the callee name
        // carries a segment (e.g. `constructor() {`), while each token of a
        // non-empty list (`(`, params, separators, `)`) is mapped individually.
        let has_params = parameters
            .iter()
            .any(|parameter| !self.is_this_parameter(parameter.data()));
        if !has_params {
            self.raw("()");
            return;
        }
        let open = self.source_pos_of(window, '(').unwrap_or(window.start());
        self.raw_mapped_token("(", open, 1);
        let mut cursor = Utf16Pos::new(open.get().saturating_add(1));
        let mut first = true;
        let mut last_end = cursor;
        for parameter in parameters {
            let parameter = parameter.data();
            if self.is_this_parameter(parameter) {
                continue;
            }
            if !first {
                let limit = parameter.binding.range().start();
                self.mapped_list_separator_from(cursor, limit);
            }
            first = false;
            self.emit_decorators_inline(&parameter.decorators);
            self.emit_pattern(&parameter.binding);
            if let Some(initializer) = &parameter.initializer {
                self.raw_mapped_pos(" = ", parameter.binding.range().end());
                self.emit_expression_prec(initializer, P_ASSIGN);
            }
            last_end = parameter.initializer.as_ref().map_or_else(
                || parameter.binding.range().end(),
                |initializer| initializer.range().end(),
            );
            cursor = last_end;
        }
        let close = self
            .source_pos_of(
                TextRange::new(last_end, window.end()).unwrap_or(window),
                ')',
            )
            .unwrap_or(last_end);
        self.raw_mapped_token(")", close, 1);
    }

    fn is_this_parameter(&self, parameter: &Parameter) -> bool {
        if let BindingPattern::Identifier(ident) = parameter.binding.data() {
            matches!(self.text(ident.data().token()), Some("this"))
        } else {
            false
        }
    }

    fn emit_decorator(&mut self, decorator: &DecoratorNode) {
        self.raw("@");
        self.emit_expression_prec(&decorator.data().expression, P_ASSIGN);
    }

    fn emit_decorators_inline(&mut self, decorators: &[DecoratorNode]) {
        for decorator in decorators {
            self.emit_decorator(decorator);
            self.raw(" ");
        }
    }

    fn emit_decorators_block(&mut self, decorators: &[DecoratorNode]) {
        for decorator in decorators {
            self.emit_decorator(decorator);
            self.newline();
        }
    }

    fn emit_class_js(&mut self, class: &ClassDeclaration) {
        self.emit_decorators_block(&class.decorators);
        self.emit_class_core_js(class);
    }

    fn emit_class_core_js(&mut self, class: &ClassDeclaration) {
        let range = self.anchor;
        let keyword_pos = class
            .name
            .as_ref()
            .and_then(|name| self.keyword_start_before(name.range().start(), "class"))
            .unwrap_or(range.start());
        self.raw_mapped_token("class", keyword_pos, 5);
        if let Some(name) = &class.name {
            self.raw(" ");
            self.emit_ident(name);
        }
        if let Some(heritage) = &class.extends {
            let extends_pos = self
                .keyword_start_before(heritage.expression.range().start(), "extends")
                .unwrap_or(range.end());
            self.raw_mapped_token(" extends ", extends_pos, 7);
            self.emit_expression_prec(&heritage.expression, P_CALL_MEMBER);
        }
        self.raw(" ");
        self.emit_class_body_js(&class.members, range);
    }

    fn emit_class_body_js(&mut self, members: &[ClassMemberNode], range: TextRange) {
        self.raw("{");
        let has = members
            .iter()
            .any(|member| self.class_member_emits_js(member.data()));
        if has {
            self.newline();
            self.indent += 1;
        }
        for member in members {
            if self.emit_class_member_js(member.data()) {
                self.newline();
            }
        }
        if has {
            self.indent -= 1;
        } else {
            self.newline();
        }
        self.raw_mapped_eol("}", range, '}');
    }

    fn class_member_emits_js(&self, member: &ClassMember) -> bool {
        match member {
            ClassMember::Constructor(_) | ClassMember::StaticBlock(_) => true,
            ClassMember::Method(method) => {
                method.function.body.is_some() && !method.modifiers.is_abstract
            }
            ClassMember::Property(property) => {
                !property.modifiers.is_abstract && !property.modifiers.is_declare
            }
            ClassMember::AutoAccessor(accessor) => {
                !accessor.modifiers.is_abstract && !accessor.modifiers.is_declare
            }
            ClassMember::IndexSignature(_) | ClassMember::Missing(_) => false,
        }
    }

    fn emit_class_member_js(&mut self, member: &ClassMember) -> bool {
        match member {
            ClassMember::Constructor(constructor) => {
                self.emit_decorators_block(&constructor.decorators);
                self.emit_constructor_js(constructor);
                true
            }
            ClassMember::Method(method) => {
                if method.function.body.is_none() || method.modifiers.is_abstract {
                    return false;
                }
                self.emit_decorators_block(&method.function.decorators);
                self.emit_method_js(method);
                true
            }
            ClassMember::Property(property) => {
                if property.modifiers.is_abstract || property.modifiers.is_declare {
                    return false;
                }
                self.emit_decorators_block(&property.decorators);
                if property.modifiers.is_static {
                    self.raw("static ");
                }
                self.emit_property_name(&property.name);
                if let Some(initializer) = &property.initializer {
                    self.raw(" = ");
                    self.emit_expression_prec(initializer, P_ASSIGN);
                }
                self.raw(";");
                true
            }
            ClassMember::AutoAccessor(accessor) => {
                if accessor.modifiers.is_abstract || accessor.modifiers.is_declare {
                    return false;
                }
                self.emit_decorators_block(&accessor.decorators);
                if accessor.modifiers.is_static {
                    self.raw("static ");
                }
                self.raw("accessor ");
                self.emit_property_name(&accessor.name);
                if let Some(initializer) = &accessor.initializer {
                    self.raw(" = ");
                    self.emit_expression_prec(initializer, P_ASSIGN);
                }
                self.raw(";");
                true
            }
            ClassMember::StaticBlock(block) => {
                self.raw("static ");
                self.emit_block_with_braces(block, block.range(), BlockLayout::StaticInitBody);
                true
            }
            ClassMember::IndexSignature(_) => false,
            ClassMember::Missing(_) => {
                self.diag_here(codes::MISSING_MEMBER, "cannot emit a missing class member");
                false
            }
        }
    }

    fn emit_method_js(&mut self, method: &MethodDeclaration) {
        let range = self.anchor;
        if method.modifiers.is_static {
            self.raw_mapped_char("static ", range, 's', 6);
        }
        match method.modifier {
            PropertyModifier::Get => self.raw_mapped_char("get ", range, 'g', 3),
            PropertyModifier::Set => self.raw_mapped_char("set ", range, 's', 3),
            PropertyModifier::None => {
                if method.function.is_async {
                    self.raw_mapped_char("async ", range, 'a', 5);
                }
                if method.function.is_generator {
                    self.raw_mapped_char("*", range, '*', 1);
                }
            }
        }
        self.emit_property_name(&method.name);
        self.emit_params_js(&method.function.parameters, self.anchor);
        self.raw(" ");
        self.emit_function_body_js(method.function.body.as_ref());
    }

    fn emit_constructor_js(&mut self, constructor: &ConstructorDeclaration) {
        let range = self.anchor;
        let keyword_pos = self.source_pos_of(range, 'c').unwrap_or(range.start());
        self.raw_mapped_token("constructor", keyword_pos, 11);
        self.emit_params_js(&constructor.parameters, self.anchor);
        self.raw(" ");

        let injections: Vec<&ParameterNode> = constructor
            .parameters
            .iter()
            .filter(|parameter| is_parameter_property(parameter.data()))
            .collect();
        let body = constructor.body.data();
        // An injection-free constructor body is an ordinary function-family
        // body: empty, preserved-single-line, and expanded layouts all come
        // from the one shared block rule (the next census correction lands
        // there alone). Injections keep the expanded path below.
        if injections.is_empty() {
            self.emit_block_with_braces(
                &constructor.body,
                constructor.body.range(),
                BlockLayout::FunctionBody,
            );
            return;
        }
        self.raw("{");
        self.newline();
        self.indent += 1;
        for parameter in injections {
            if let BindingPattern::Identifier(name) = parameter.data().binding.data() {
                self.raw("this.");
                self.emit_ident(name);
                self.raw(" = ");
                self.emit_ident(name);
                self.raw(";");
                self.newline();
            } else {
                self.diag(
                    codes::MISSING_TARGET,
                    "parameter property must bind a plain identifier",
                    parameter.range(),
                );
            }
        }
        self.emit_statement_list(&body.statements);
        self.indent -= 1;
        self.raw_mapped_char_end("}", range, '}');
    }

    // =======================================================================
    // expressions (precedence-aware)
    // =======================================================================

    fn emit_expression(&mut self, expression: &Expr) {
        self.emit_expression_prec(expression, 0);
    }

    fn emit_expression_prec(&mut self, expression: &Expr, min_prec: u8) {
        let previous = self.anchor;
        self.anchor = expression.range();
        let prec = self.expression_prec(expression);
        let parenthesize = prec < min_prec;
        if parenthesize {
            self.raw("(");
        }
        self.emit_expression_inner(expression);
        if parenthesize {
            self.raw(")");
        }
        self.anchor = previous;
    }

    fn expression_prec(&self, expression: &Expr) -> u8 {
        if let Some(value) = self.enum_facts.const_use(expression.id()) {
            return match value.number() {
                Some(number) if number.to_f64().is_sign_negative() => P_UNARY,
                _ => P_PRIMARY,
            };
        }
        match expression.data() {
            Expression::Sequence(_) => P_SEQUENCE,
            Expression::Assignment(_) | Expression::Arrow(_) | Expression::Yield(_) => P_ASSIGN,
            Expression::Conditional(_) => P_CONDITIONAL,
            Expression::Logical(logical) => match logical.operator {
                LogicalOperator::And => P_LOGICAL_AND,
                LogicalOperator::Or => P_LOGICAL_OR,
                LogicalOperator::Nullish => P_NULLISH,
            },
            Expression::Binary(binary) => binary_prec(binary.operator),
            Expression::Unary(_) | Expression::Await(_) => P_UNARY,
            Expression::Update(update) => {
                if update.prefix {
                    P_UNARY
                } else {
                    P_POSTFIX
                }
            }
            Expression::Call(_)
            | Expression::New(_)
            | Expression::Member(_)
            | Expression::TaggedTemplate(_)
            | Expression::Import(_) => P_CALL_MEMBER,
            // A parenthesized node always prints its own parens (matching
            // tsc, which round-trips both source parens and the parens its
            // transforms synthesize), so it is opaque to outer precedence.
            Expression::Parenthesized(_) => P_PRIMARY,
            Expression::As(as_expr) => self.expression_prec(&as_expr.expression),
            Expression::Satisfies(satisfies) => self.expression_prec(&satisfies.expression),
            Expression::TypeAssertion(assertion) => self.expression_prec(&assertion.expression),
            Expression::NonNull(non_null) => self.expression_prec(&non_null.expression),
            _ => P_PRIMARY,
        }
    }

    fn emit_expression_inner(&mut self, expression: &Expr) {
        if let Some(replacement) = self
            .jsx_plan
            .and_then(|plan| plan.expression_desugars.get(&expression.id()))
            .cloned()
        {
            self.emit_expression_inner(&replacement);
            return;
        }
        if let Some(value) = self.enum_facts.const_use(expression.id()) {
            self.emit_enum_scalar(value);
            return;
        }
        match expression.data() {
            Expression::Identifier(ident) => self.emit_ident_expression(ident),
            Expression::This => self.raw("this"),
            Expression::Super => self.raw("super"),
            Expression::Literal(literal) => self.emit_literal(literal),
            Expression::Template(template) => self.emit_template(template),
            Expression::TaggedTemplate(tagged) => {
                self.emit_expression_prec(&tagged.tag, P_CALL_MEMBER);
                self.emit_template(&tagged.template);
            }
            Expression::Array(array) => self.emit_array(array),
            Expression::Object(object) => {
                self.emit_object(object, expression.id(), expression.range())
            }
            Expression::Function(function) => {
                self.emit_function_expression_js(&function.function, self.anchor)
            }
            Expression::Class(class) => self.emit_class_js(&class.class),
            Expression::Arrow(arrow) => self.emit_arrow_js(arrow, self.anchor),
            Expression::Call(call) => self.emit_call(call),
            Expression::Member(member) => self.emit_member(member),
            Expression::New(new) => self.emit_new(new),
            Expression::Await(await_expr) => {
                self.raw("await ");
                self.emit_expression_prec(&await_expr.argument, P_UNARY);
            }
            Expression::Yield(yield_expr) => self.emit_yield(yield_expr),
            Expression::Unary(unary) => self.emit_unary(unary),
            Expression::Update(update) => self.emit_update(update),
            Expression::Binary(binary) => self.emit_binary(binary),
            Expression::Logical(logical) => self.emit_logical(logical),
            Expression::Conditional(conditional) => self.emit_conditional(conditional),
            Expression::Assignment(assignment) => self.emit_assignment(assignment),
            Expression::Sequence(sequence) => self.emit_sequence(sequence),
            Expression::Parenthesized(inner) => {
                self.raw("(");
                self.emit_expression_prec(inner, 0);
                self.raw(")");
            }
            Expression::As(as_expr) => self.emit_expression_prec(&as_expr.expression, 0),
            Expression::Satisfies(satisfies) => {
                self.emit_expression_prec(&satisfies.expression, 0);
            }
            Expression::TypeAssertion(assertion) => {
                self.emit_expression_prec(&assertion.expression, 0);
            }
            Expression::NonNull(non_null) => self.emit_expression_prec(&non_null.expression, 0),
            Expression::Import(import) => {
                self.raw("import(");
                self.emit_expression_prec(&import.source, P_ASSIGN);
                if let Some(options) = &import.options {
                    self.raw(", ");
                    self.emit_expression_prec(options, P_ASSIGN);
                }
                self.raw(")");
            }
            Expression::Meta(meta) => match meta {
                MetaProperty::NewTarget => self.raw("new.target"),
                MetaProperty::ImportMeta => self.raw("import.meta"),
            },
            Expression::JsxElement(element) => self.emit_jsx_element(element),
            Expression::JsxSelfClosingElement(element) => {
                self.emit_jsx_self_closing_element(element);
            }
            Expression::JsxFragment(fragment) => self.emit_jsx_fragment(fragment),
            Expression::Missing(_) => {
                self.diag_here(
                    codes::MISSING_EXPRESSION,
                    "cannot emit a missing expression node",
                );
                self.raw("void 0");
            }
        }
    }

    fn emit_jsx_element(&mut self, element: &JsxElement) {
        self.emit_jsx_opening_element(element.opening.data());
        self.emit_jsx_children(&element.children);
        self.emit_jsx_closing_element(element.closing.data());
    }

    fn emit_jsx_self_closing_element(&mut self, element: &JsxSelfClosingElement) {
        self.raw("<");
        self.emit_jsx_element_name(&element.name);
        self.emit_jsx_attributes(&element.attributes);
        self.raw(" />");
    }

    fn emit_jsx_opening_element(&mut self, element: &JsxOpeningElement) {
        self.raw("<");
        self.emit_jsx_element_name(&element.name);
        self.emit_jsx_attributes(&element.attributes);
        self.raw(">");
    }

    fn emit_jsx_closing_element(&mut self, element: &JsxClosingElement) {
        self.raw("</");
        self.emit_jsx_element_name(&element.name);
        self.raw(">");
    }

    fn emit_jsx_fragment(&mut self, fragment: &JsxFragment) {
        self.raw("<>");
        self.emit_jsx_children(&fragment.children);
        self.raw("</>");
    }

    fn emit_jsx_element_name(&mut self, name: &JsxElementName) {
        match name {
            JsxElementName::Identifier(identifier) => self.emit_ident(identifier),
            JsxElementName::Member(member) => {
                self.emit_jsx_element_name(&member.object);
                self.raw(".");
                self.emit_ident(&member.property);
            }
            JsxElementName::Namespace(name) => {
                self.emit_ident(&name.namespace);
                self.raw(":");
                self.emit_ident(&name.name);
            }
        }
    }

    fn emit_jsx_attributes(&mut self, attributes: &[JsxAttributeItem]) {
        for entry in attributes {
            self.raw(" ");
            match entry {
                JsxAttributeItem::Attribute(attribute) => {
                    self.emit_jsx_attribute(attribute.data());
                }
                JsxAttributeItem::Spread(spread) => {
                    self.raw("{...");
                    self.emit_expression_prec(&spread.data().expression, P_ASSIGN);
                    self.raw("}");
                }
            }
        }
    }

    fn emit_jsx_attribute(&mut self, attribute: &JsxAttribute) {
        match &attribute.name {
            JsxAttributeName::Identifier(name) => self.emit_ident(name),
            JsxAttributeName::Namespace(name) => {
                self.emit_ident(&name.namespace);
                self.raw(":");
                self.emit_ident(&name.name);
            }
        }
        let Some(initializer) = &attribute.initializer else {
            return;
        };
        self.raw("=");
        match initializer {
            JsxAttributeInitializer::String(string) => self.emit_string(string),
            JsxAttributeInitializer::Expression(expression) => {
                self.emit_jsx_expression(expression.data(), expression.range());
            }
        }
    }

    fn emit_jsx_children(&mut self, children: &[JsxChild]) {
        for child in children {
            match child {
                JsxChild::Text(text) => self.emit_token(text.data().token()),
                JsxChild::ExpressionContainer(expression) => {
                    self.emit_jsx_expression(expression.data(), expression.range());
                }
                JsxChild::Spread(spread) => {
                    self.raw("{...");
                    self.emit_expression_prec(&spread.data().expression, P_ASSIGN);
                    self.raw("}");
                }
                JsxChild::Element(element) => self.emit_expression_prec(element, P_PRIMARY),
            }
        }
    }

    fn emit_jsx_expression(&mut self, expression: &JsxExpressionContainer, range: TextRange) {
        self.raw("{");
        if let Some(inner) = &expression.expression {
            if self.jsx_container_has_spread(range, inner.range()) {
                self.raw("...");
            }
            self.emit_expression_prec(inner, 0);
        }
        self.raw("}");
    }

    fn jsx_container_has_spread(&self, container: TextRange, expression: TextRange) -> bool {
        let Ok(start) = self.source.utf16_to_byte(container.start()) else {
            return false;
        };
        let Ok(end) = self.source.utf16_to_byte(expression.start()) else {
            return false;
        };
        self.source
            .as_str()
            .get(start..end)
            .is_some_and(|prefix| prefix.contains("..."))
    }

    fn emit_ident_expression(&mut self, ident: &IdentifierNode) {
        let range = ident.range();
        if let Some(text) = self.generated_text(ident.id()).map(str::to_owned) {
            self.raw_mapped(&text, range);
            return;
        }
        let Some(text) = self.text(ident.data().token()) else {
            self.diag(
                codes::UNRESOLVED_TOKEN,
                "token text is not a valid slice of the source",
                range,
            );
            return;
        };
        if let Some(member) = self.enum_facts.member_use(ident.id()) {
            let enum_name = self.model.symbol(member.enum_symbol()).name().to_owned();
            self.raw_mapped(&enum_name, range);
            self.raw("[");
            self.emit_enum_string(member.name());
            self.raw("]");
            return;
        }
        self.raw_mapped(text, range);
    }

    fn emit_literal(&mut self, literal: &Literal) {
        if let Literal::String(node) = literal
            && self.generated_text(node.id()).is_some()
        {
            self.emit_string(node);
            return;
        }
        let generated = match literal {
            Literal::String(node) => self.generated_text(node.id()),
            Literal::Number(node) => self.generated_text(node.id()),
            Literal::BigInt(node) => self.generated_text(node.id()),
            Literal::Boolean(node) => self.generated_text(node.id()),
            Literal::Null(node) => self.generated_text(node.id()),
            Literal::Regex(node) => self.generated_text(node.id()),
        }
        .map(str::to_owned);
        if let Some(text) = generated {
            let range = literal_range(literal);
            self.raw_mapped(&text, range);
            return;
        }
        match literal {
            Literal::String(node) => self.emit_token(node.data().token()),
            Literal::Number(node) => self.emit_token(node.data().token()),
            Literal::BigInt(node) => self.emit_token(node.data().token()),
            Literal::Boolean(node) => self.emit_token(node.data().token()),
            Literal::Null(node) => match self.text(node.data().token()) {
                Some(text) if !text.is_empty() => self.raw_mapped(text, node.range()),
                _ => self.raw("null"),
            },
            Literal::Regex(node) => self.emit_token(node.data().token()),
        }
    }

    fn emit_template(&mut self, template: &TemplateLiteral) {
        if template.elements.is_empty() {
            return;
        }
        self.emit_token(template.elements[0].data().token());
        for (index, expression) in template.expressions.iter().enumerate() {
            self.emit_expression_prec(expression, 0);
            if let Some(element) = template.elements.get(index + 1) {
                self.emit_token(element.data().token());
            }
        }
    }

    fn emit_array(&mut self, array: &ArrayLiteral) {
        let range = self.anchor;
        self.raw_mapped_char("[", range, '[', 1);
        let elements = &array.elements;
        let mut cursor = Utf16Pos::new(range.start().get().saturating_add(1));
        for (index, element) in elements.iter().enumerate() {
            let element_range = array_element_range(element);
            if index > 0 {
                let limit = element_range.map_or(range.end(), |r| r.start());
                cursor = self.mapped_list_separator_from(cursor, limit);
            }
            match element {
                ArrayElement::Expression(expression) => {
                    self.emit_expression_prec(expression, P_ASSIGN);
                }
                ArrayElement::Spread(spread) => {
                    self.raw_mapped_char("...", spread.argument.range(), '.', 3);
                    self.emit_expression_prec(&spread.argument, P_ASSIGN);
                }
                ArrayElement::Elision => {}
                ArrayElement::Missing(_) => {
                    self.diag_here(
                        codes::MISSING_ELEMENT,
                        "cannot emit a missing array element",
                    );
                }
            }
            if let Some(element_range) = element_range {
                cursor = element_range.end();
            }
        }
        if matches!(elements.last(), Some(ArrayElement::Elision)) {
            self.raw_mapped_char_end(",", range, ',');
        }
        self.raw_mapped_char_end("]", range, ']');
    }

    fn emit_object(&mut self, object: &ObjectLiteral, id: NodeId, range: TextRange) {
        if object.members.is_empty() {
            self.raw("{}");
            return;
        }
        // Preservation: members authored on one line join with `, `.
        // Synthesized or multi-line-authored objects take the expanded path.
        if self.preserves_single_line(id, range) {
            self.raw("{ ");
            let count = object.members.len();
            for (index, member) in object.members.iter().enumerate() {
                self.emit_object_member(member.data());
                if index + 1 < count {
                    self.raw(",");
                }
                self.raw(" ");
            }
            self.raw("}");
            return;
        }
        self.raw("{");
        self.newline();
        self.indent += 1;
        let count = object.members.len();
        for (index, member) in object.members.iter().enumerate() {
            self.emit_object_member(member.data());
            if index + 1 < count {
                self.raw(",");
            }
            self.newline();
        }
        self.indent -= 1;
        self.raw("}");
    }

    fn emit_object_member(&mut self, member: &ObjectMember) {
        match member {
            ObjectMember::Property(property) => {
                if property.shorthand && matches!(property.name, PropertyName::Identifier(_)) {
                    self.emit_property_name(&property.name);
                } else {
                    self.emit_property_name(&property.name);
                    self.raw(": ");
                    self.emit_expression_prec(&property.value, P_ASSIGN);
                }
            }
            ObjectMember::Method(method) => self.emit_object_method(method),
            ObjectMember::Spread(spread) => {
                self.raw("...");
                self.emit_expression_prec(&spread.argument, P_ASSIGN);
            }
            ObjectMember::Missing(_) => {
                self.diag_here(codes::MISSING_MEMBER, "cannot emit a missing object member");
            }
        }
    }

    fn emit_object_method(&mut self, method: &ObjectMethod) {
        match method.modifier {
            PropertyModifier::Get => self.raw("get "),
            PropertyModifier::Set => self.raw("set "),
            PropertyModifier::None => {
                if method.function.is_async {
                    self.raw("async ");
                }
                if method.function.is_generator {
                    self.raw("*");
                }
            }
        }
        self.emit_property_name(&method.name);
        self.emit_params_js(&method.function.parameters, self.anchor);
        self.raw(" ");
        self.emit_function_body_js(method.function.body.as_ref());
    }

    fn emit_property_name(&mut self, name: &PropertyName) {
        match name {
            PropertyName::Identifier(ident) => self.emit_ident(ident),
            PropertyName::Private(private) => self.emit_token(private.data().token()),
            PropertyName::String(string) => self.emit_string(string),
            PropertyName::Number(number) => self.emit_token(number.data().token()),
            PropertyName::Computed(expression) => {
                self.raw("[");
                self.emit_expression_prec(expression, P_ASSIGN);
                self.raw("]");
            }
            PropertyName::Missing(_) => {
                self.diag_here(
                    codes::MISSING_PROPERTY_NAME,
                    "cannot emit a missing property name",
                );
            }
        }
    }

    fn emit_call(&mut self, call: &CallExpression) {
        let range = self.anchor;
        self.emit_expression_prec(&call.callee, P_CALL_MEMBER);
        let open_pos = self
            .source_pos_of(
                TextRange::new(call.callee.range().end(), range.end()).unwrap_or(range),
                '(',
            )
            .unwrap_or(range.end());
        if call.optional {
            self.raw_mapped_token("?.(", open_pos, 2);
        } else {
            self.raw_mapped_token("(", open_pos, 1);
        }
        self.emit_arguments(&call.arguments);
        let close_pos = self.source_pos_of_last(range, ')').unwrap_or(range.end());
        self.raw_mapped_token(")", close_pos, 1);
    }

    fn emit_new(&mut self, new: &NewExpression) {
        let range = self.anchor;
        let new_pos = self.source_pos_of(range, 'n').unwrap_or(range.start());
        self.raw_mapped_token("new ", new_pos, 3);
        let callee = self.unwrap_expression(&new.callee);
        let wrap = matches!(callee.data(), Expression::Call(_)) || self.chain_has_optional(callee);
        if wrap {
            self.raw("(");
            self.emit_expression_prec(callee, 0);
            self.raw(")");
        } else {
            self.emit_expression_prec(callee, P_CALL_MEMBER);
        }
        let open_pos = self
            .source_pos_of(
                TextRange::new(callee.range().end(), range.end()).unwrap_or(range),
                '(',
            )
            .unwrap_or(callee.range().end());
        self.raw_mapped_token("(", open_pos, 1);
        self.emit_arguments(&new.arguments);
        let close_pos = self.source_pos_of_last(range, ')').unwrap_or(range.end());
        self.raw_mapped_token(")", close_pos, 1);
    }

    fn emit_arguments(&mut self, arguments: &[CallArgument]) {
        let mut previous_end: Option<Utf16Pos> = None;
        for (index, argument) in arguments.iter().enumerate() {
            let argument_range = call_argument_range(argument);
            if index > 0 {
                match (previous_end, argument_range) {
                    (Some(end), Some(next)) => {
                        self.mapped_list_separator_from(end, next.start());
                    }
                    (Some(end), None) => self.raw_mapped_pos(", ", end),
                    (None, _) => {}
                }
            }
            match argument {
                CallArgument::Expression(expression) => {
                    self.emit_expression_prec(expression, P_ASSIGN);
                }
                CallArgument::Spread(spread) => {
                    self.raw_mapped_char("...", spread.argument.range(), '.', 3);
                    self.emit_expression_prec(&spread.argument, P_ASSIGN);
                }
                CallArgument::Missing(_) => {
                    self.diag_here(
                        codes::MISSING_ELEMENT,
                        "cannot emit a missing call argument",
                    );
                }
            }
            previous_end = argument_range.map(|range| range.end());
        }
    }

    fn emit_member(&mut self, member: &MemberExpression) {
        let range = self.anchor;
        let dotted = !matches!(member.property, MemberProperty::Computed(_));
        let numeric_object = dotted
            && matches!(
                self.unwrap_expression(&member.object).data(),
                Expression::Literal(Literal::Number(_))
            );
        if numeric_object && !self.starts_parenthesized(&member.object) {
            self.raw("(");
            self.emit_expression_prec(&member.object, 0);
            self.raw(")");
        } else {
            self.emit_expression_prec(&member.object, P_CALL_MEMBER);
        }
        match &member.property {
            MemberProperty::Named(name) => {
                let dot_pos = self
                    .source_pos_of(
                        TextRange::new(member.object.range().end(), name.range().start())
                            .unwrap_or(self.anchor),
                        '.',
                    )
                    .unwrap_or(name.range().start());
                self.raw_mapped_token(if member.optional { "?." } else { "." }, dot_pos, 1);
                self.emit_ident(name);
            }
            MemberProperty::Private(private) => {
                let dot_pos = self
                    .source_pos_of(
                        TextRange::new(member.object.range().end(), range.end()).unwrap_or(range),
                        '.',
                    )
                    .unwrap_or(range.end());
                self.raw_mapped_token(if member.optional { "?." } else { "." }, dot_pos, 1);
                self.emit_token(private.data().token());
            }
            MemberProperty::Computed(expression) => {
                let bracket_pos = self
                    .source_pos_of(
                        TextRange::new(member.object.range().end(), expression.range().start())
                            .unwrap_or(range),
                        '[',
                    )
                    .unwrap_or(expression.range().start());
                self.raw_mapped_token(if member.optional { "?.[" } else { "[" }, bracket_pos, 1);
                self.emit_expression_prec(expression, 0);
                let close_pos = self.source_pos_of_last(range, ']').unwrap_or(range.end());
                self.raw_mapped_token("]", close_pos, 1);
            }
        }
    }

    fn emit_yield(&mut self, expression: &YieldExpression) {
        let range = self.anchor;
        let yield_pos = self.source_pos_of(range, 'y').unwrap_or(range.start());
        self.raw_mapped_token("yield", yield_pos, 5);
        if expression.delegate {
            let star_pos = self
                .source_pos_of(
                    TextRange::new(Utf16Pos::new(yield_pos.get() + 5), range.end())
                        .unwrap_or(range),
                    '*',
                )
                .unwrap_or(range.end());
            self.raw_mapped_token("*", star_pos, 1);
        }
        if let Some(argument) = &expression.argument {
            self.raw(" ");
            self.emit_expression_prec(argument, P_ASSIGN);
        }
    }

    fn emit_unary(&mut self, unary: &UnaryExpression) {
        let range = self.anchor;
        let (text, anchor_char, width): (&str, char, usize) = match unary.operator {
            UnaryOperator::Typeof => ("typeof ", 't', 6),
            UnaryOperator::Void => ("void ", 'v', 4),
            UnaryOperator::Delete => ("delete ", 'd', 6),
            UnaryOperator::Plus => ("+", '+', 1),
            UnaryOperator::Minus => ("-", '-', 1),
            UnaryOperator::Not => ("!", '!', 1),
            UnaryOperator::BitNot => ("~", '~', 1),
        };
        let keyword = text.strip_suffix(' ').unwrap_or(text);
        let op_pos = self
            .source_pos_of(range, anchor_char)
            .unwrap_or(range.start());
        self.raw_mapped_token(keyword, op_pos, width);
        if text != keyword {
            self.raw(" ");
        }
        if matches!(unary.operator, UnaryOperator::Plus | UnaryOperator::Minus)
            && self.needs_unary_space(&unary.argument)
        {
            self.raw(" ");
        }
        self.emit_expression_prec(&unary.argument, P_UNARY);
    }

    fn needs_unary_space(&self, argument: &Expr) -> bool {
        match self.unwrap_expression(argument).data() {
            Expression::Unary(inner) => {
                matches!(inner.operator, UnaryOperator::Plus | UnaryOperator::Minus)
            }
            Expression::Update(inner) => inner.prefix,
            _ => false,
        }
    }

    fn emit_update(&mut self, update: &UpdateExpression) {
        let range = self.anchor;
        let operator = match update.operator {
            UpdateOperator::Increment => "++",
            UpdateOperator::Decrement => "--",
        };
        let anchor_char = operator.chars().next().unwrap_or('+');
        if update.prefix {
            let op_pos = self
                .source_pos_of(range, anchor_char)
                .unwrap_or(range.start());
            self.raw_mapped_token(operator, op_pos, 2);
            self.emit_assignment_target(&update.argument);
        } else {
            self.emit_assignment_target(&update.argument);
            let op_pos = self
                .source_pos_of_last(range, anchor_char)
                .unwrap_or(range.end());
            self.raw_mapped_token(operator, op_pos, 2);
        }
    }

    fn emit_binary(&mut self, binary: &BinaryExpression) {
        let prec = binary_prec(binary.operator);
        if matches!(binary.operator, BinaryOperator::Exponentiate) {
            let left = self.unwrap_expression(&binary.left);
            if matches!(left.data(), Expression::Unary(_) | Expression::Await(_))
                || matches!(left.data(), Expression::Update(update) if update.prefix)
            {
                self.raw("(");
                self.emit_expression_prec(left, 0);
                self.raw(")");
            } else {
                self.emit_expression_prec(&binary.left, P_EXPONENT + 1);
            }
            self.raw_mapped_pos(" ** ", binary.left.range().end());
            self.emit_expression_prec(&binary.right, P_EXPONENT);
        } else {
            let operator_text = binary_str(binary.operator);
            self.emit_expression_prec(&binary.left, prec);
            let op_pos = self
                .source_pos_of(
                    TextRange::new(binary.left.range().end(), binary.right.range().start())
                        .unwrap_or(self.anchor),
                    operator_text.chars().next().unwrap_or('+'),
                )
                .unwrap_or(binary.left.range().end())
                .get()
                .saturating_sub(1);
            let op_pos = Utf16Pos::new(op_pos);
            self.raw_mapped_token(
                &format!(" {operator_text} "),
                op_pos,
                operator_text.chars().count(),
            );
            self.emit_expression_prec(&binary.right, prec + 1);
        }
    }

    fn emit_logical(&mut self, logical: &LogicalExpression) {
        let prec = match logical.operator {
            LogicalOperator::And => P_LOGICAL_AND,
            LogicalOperator::Or => P_LOGICAL_OR,
            LogicalOperator::Nullish => P_NULLISH,
        };
        let operator_text = logical_str(logical.operator);
        self.emit_logical_operand(&logical.left, logical.operator, prec, true);
        let op_pos = self
            .source_pos_of(
                TextRange::new(logical.left.range().end(), logical.right.range().start())
                    .unwrap_or(self.anchor),
                operator_text.chars().next().unwrap_or('&'),
            )
            .unwrap_or(logical.left.range().end())
            .get()
            .saturating_sub(1);
        let op_pos = Utf16Pos::new(op_pos);
        self.raw_mapped_token(
            &format!(" {operator_text} "),
            op_pos,
            operator_text.chars().count(),
        );
        self.emit_logical_operand(&logical.right, logical.operator, prec, false);
    }

    fn emit_logical_operand(
        &mut self,
        operand: &Expr,
        parent: LogicalOperator,
        prec: u8,
        is_left: bool,
    ) {
        if self.coalesce_mix(parent, operand) && !self.starts_parenthesized(operand) {
            self.raw("(");
            self.emit_expression_prec(operand, 0);
            self.raw(")");
            return;
        }
        let min_prec = if is_left { prec } else { prec + 1 };
        self.emit_expression_prec(operand, min_prec);
    }

    fn coalesce_mix(&self, parent: LogicalOperator, operand: &Expr) -> bool {
        if let Expression::Logical(child) = self.unwrap_expression(operand).data() {
            let parent_nullish = matches!(parent, LogicalOperator::Nullish);
            let child_nullish = matches!(child.operator, LogicalOperator::Nullish);
            parent_nullish != child_nullish
        } else {
            false
        }
    }

    fn emit_conditional(&mut self, conditional: &ConditionalExpression) {
        self.emit_expression_prec(&conditional.test, P_CONDITIONAL + 1);
        let question_pos = self
            .source_pos_of(
                TextRange::new(
                    conditional.test.range().end(),
                    conditional.consequent.range().start(),
                )
                .unwrap_or(self.anchor),
                '?',
            )
            .unwrap_or(conditional.test.range().end());
        self.raw_mapped_token(" ? ", question_pos, 1);
        self.emit_expression_prec(&conditional.consequent, P_ASSIGN);
        let colon_pos = self
            .source_pos_of(
                TextRange::new(
                    conditional.consequent.range().end(),
                    conditional.alternate.range().start(),
                )
                .unwrap_or(self.anchor),
                ':',
            )
            .unwrap_or(conditional.consequent.range().end());
        self.raw_mapped_token(" : ", colon_pos, 1);
        self.emit_expression_prec(&conditional.alternate, P_ASSIGN);
    }

    fn emit_assignment(&mut self, assignment: &AssignmentExpression) {
        let operator_text = assignment_str(assignment.operator);
        self.emit_assignment_target(&assignment.left);
        let op_pos = self
            .source_pos_of(
                TextRange::new(
                    assignment.left.range().end(),
                    assignment.right.range().start(),
                )
                .unwrap_or(self.anchor),
                operator_text.chars().next().unwrap_or('='),
            )
            .unwrap_or(assignment.left.range().end())
            .get()
            .saturating_sub(1);
        let op_pos = Utf16Pos::new(op_pos);
        self.raw_mapped_token(
            &format!(" {operator_text} "),
            op_pos,
            operator_text.chars().count(),
        );
        self.emit_expression_prec(&assignment.right, P_ASSIGN);
    }

    fn emit_sequence(&mut self, sequence: &SequenceExpression) {
        let mut previous_end: Option<Utf16Pos> = None;
        for expression in sequence.expressions.iter() {
            if let Some(end) = previous_end {
                self.mapped_list_separator_from(end, expression.range().start());
            }
            self.emit_expression_prec(expression, P_ASSIGN);
            previous_end = Some(expression.range().end());
        }
    }

    // ---- assignment targets / patterns ------------------------------------

    fn emit_assignment_target(&mut self, target: &AssignmentTargetNode) {
        match target.data() {
            AssignmentTarget::Identifier(ident) => self.emit_ident(ident),
            AssignmentTarget::Member(member) => {
                let dotted = !matches!(member.property, MemberProperty::Computed(_));
                let numeric_object = dotted
                    && matches!(
                        self.unwrap_expression(&member.object).data(),
                        Expression::Literal(Literal::Number(_))
                    );
                if numeric_object && !self.starts_parenthesized(&member.object) {
                    self.raw("(");
                    self.emit_expression_prec(&member.object, 0);
                    self.raw(")");
                } else {
                    self.emit_expression_prec(&member.object, P_CALL_MEMBER);
                }
                match &member.property {
                    MemberProperty::Named(name) => {
                        self.raw(".");
                        self.emit_ident(name);
                    }
                    MemberProperty::Private(private) => {
                        self.raw(".");
                        self.emit_token(private.data().token());
                    }
                    MemberProperty::Computed(expression) => {
                        self.raw("[");
                        self.emit_expression_prec(expression, 0);
                        self.raw("]");
                    }
                }
            }
            AssignmentTarget::Object(pattern) => {
                self.raw("{");
                for (index, property) in pattern.properties.iter().enumerate() {
                    if index > 0 {
                        self.raw(", ");
                    } else {
                        self.raw(" ");
                    }
                    self.emit_assignment_object_property(property);
                }
                if pattern.properties.is_empty() {
                    self.raw("}");
                } else {
                    self.raw(" }");
                }
            }
            AssignmentTarget::Array(pattern) => {
                self.raw("[");
                for (index, element) in pattern.elements.iter().enumerate() {
                    if index > 0 {
                        self.raw(", ");
                    }
                    match element {
                        AssignmentArrayElement::Target(target) => {
                            self.emit_assignment_target(target)
                        }
                        AssignmentArrayElement::Elision => {}
                        AssignmentArrayElement::Missing(_) => {
                            self.diag_here(codes::MISSING_TARGET, "cannot emit a missing target");
                        }
                    }
                }
                if matches!(
                    pattern.elements.last(),
                    Some(AssignmentArrayElement::Elision)
                ) {
                    self.raw(",");
                }
                self.raw("]");
            }
            AssignmentTarget::Missing(_) => {
                self.diag_here(
                    codes::MISSING_TARGET,
                    "cannot emit a missing assignment target",
                );
            }
            AssignmentTarget::Invalid(operand) => {
                self.emit_expression_prec(operand, 0);
            }
        }
    }

    fn emit_assignment_object_property(&mut self, property: &AssignmentObjectProperty) {
        let shorthand = property.initializer.is_none()
            && self.target_matches_name(&property.name, &property.target);
        if shorthand {
            self.emit_property_name(&property.name);
        } else {
            self.emit_property_name(&property.name);
            self.raw(": ");
            self.emit_assignment_target(&property.target);
        }
        if let Some(initializer) = &property.initializer {
            self.raw(" = ");
            self.emit_expression_prec(initializer, P_ASSIGN);
        }
    }

    fn emit_pattern(&mut self, pattern: &Pattern) {
        let pattern_range = pattern.range();
        match pattern.data() {
            BindingPattern::Identifier(ident) => self.emit_ident(ident),
            BindingPattern::Object(object) => {
                if object.properties.is_empty() {
                    self.raw_mapped_char_end("{}", pattern_range, '{');
                    return;
                }
                self.raw_mapped_char("{ ", pattern_range, '{', 1);
                let mut previous_end: Option<Utf16Pos> = None;
                for property in object.properties.iter() {
                    let property_range = object_binding_property_range(property);
                    match (previous_end, property_range) {
                        (Some(end), Some(next)) => self.raw_mapped_list_separator(end, next),
                        (Some(end), None) => self.raw_mapped_pos(", ", end),
                        (None, _) => {}
                    }
                    self.emit_object_binding_property(property);
                    previous_end = property_range.map(|range| range.end());
                }
                self.raw_mapped_char_end(" }", pattern_range, '}');
            }
            BindingPattern::Array(array) => {
                self.raw_mapped_char("[", pattern_range, '[', 1);
                let mut cursor = Utf16Pos::new(pattern_range.start().get().saturating_add(1));
                for (index, element) in array.elements.iter().enumerate() {
                    let element_range = array_binding_element_range(element);
                    if index > 0 {
                        let limit = element_range.map_or(pattern_range.end(), |r| r.start());
                        cursor = self.mapped_list_separator_from(cursor, limit);
                    }
                    match element {
                        ArrayBindingElement::Binding(binding) => self.emit_pattern(binding),
                        ArrayBindingElement::Elision => {}
                        ArrayBindingElement::Missing(_) => {
                            self.diag_here(codes::MISSING_BINDING, "cannot emit a missing binding");
                        }
                    }
                    if let Some(element_range) = element_range {
                        cursor = element_range.end();
                    }
                }
                if matches!(array.elements.last(), Some(ArrayBindingElement::Elision)) {
                    self.raw_mapped_char_end(",", pattern_range, ',');
                }
                self.raw_mapped_char_end("]", pattern_range, ']');
            }
            BindingPattern::Rest(rest) => {
                let rest_argument = rest.argument.range();
                self.raw_mapped_char("...", rest_argument, '.', 3);
                self.emit_pattern(&rest.argument);
            }
            BindingPattern::Assignment(assignment) => {
                self.emit_pattern(&assignment.left);
                self.raw_mapped_pos(" = ", assignment.left.range().end());
                self.emit_expression_prec(&assignment.right, P_ASSIGN);
            }
            BindingPattern::Missing(_) => {
                self.diag_here(
                    codes::MISSING_BINDING,
                    "cannot emit a missing binding pattern",
                );
            }
        }
    }

    fn emit_object_binding_property(&mut self, property: &ObjectBindingProperty) {
        if let BindingPattern::Rest(rest) = property.binding.data() {
            self.raw("...");
            self.emit_pattern(&rest.argument);
            return;
        }
        let shorthand = self.binding_matches_name(&property.name, &property.binding);
        if shorthand {
            self.emit_property_name(&property.name);
        } else {
            self.emit_property_name(&property.name);
            self.raw(": ");
            self.emit_pattern(&property.binding);
        }
        if let Some(initializer) = &property.initializer {
            self.raw(" = ");
            self.emit_expression_prec(initializer, P_ASSIGN);
        }
    }

    // ---- shorthand / name matching helpers --------------------------------

    fn module_name_matches_ident(&self, name: &ModuleExportName, ident: &IdentifierNode) -> bool {
        match name {
            ModuleExportName::Identifier(imported) => self.same_ident_text(imported, ident),
            _ => false,
        }
    }

    fn module_names_match(&self, left: &ModuleExportName, right: &ModuleExportName) -> bool {
        match (left, right) {
            (ModuleExportName::Identifier(a), ModuleExportName::Identifier(b)) => {
                self.same_ident_text(a, b)
            }
            _ => false,
        }
    }

    fn target_matches_name(&self, name: &PropertyName, target: &AssignmentTargetNode) -> bool {
        if let (PropertyName::Identifier(a), AssignmentTarget::Identifier(b)) =
            (name, target.data())
        {
            self.same_ident_text(a, b)
        } else {
            false
        }
    }

    fn binding_matches_name(&self, name: &PropertyName, binding: &Pattern) -> bool {
        if let (PropertyName::Identifier(a), BindingPattern::Identifier(b)) = (name, binding.data())
        {
            self.same_ident_text(a, b)
        } else {
            false
        }
    }

    fn same_ident_text(&self, left: &IdentifierNode, right: &IdentifierNode) -> bool {
        match (
            self.text(left.data().token()),
            self.text(right.data().token()),
        ) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    }

    fn emit_module_export_name(&mut self, name: &ModuleExportName) {
        match name {
            ModuleExportName::Identifier(ident) => self.emit_ident(ident),
            ModuleExportName::String(string) => self.emit_string(string),
            ModuleExportName::Missing(_) => {
                self.diag_here(
                    codes::MISSING_NAME,
                    "cannot emit a missing module export name",
                );
            }
        }
    }

    fn emit_entity_name(&mut self, name: &EntityName) {
        match name {
            EntityName::Identifier(ident) => self.emit_ident(ident),
            EntityName::Qualified { left, right } => {
                self.emit_entity_name(left);
                self.raw(".");
                self.emit_ident(right);
            }
            EntityName::Missing(_) => {
                self.diag_here(codes::MISSING_NAME, "cannot emit a missing entity name");
            }
        }
    }

    // ---- expression classification ----------------------------------------

    fn unwrap_expression<'e>(&self, expression: &'e Expr) -> &'e Expr {
        match expression.data() {
            Expression::Parenthesized(inner) => self.unwrap_expression(inner),
            Expression::As(as_expr) => self.unwrap_expression(&as_expr.expression),
            Expression::Satisfies(satisfies) => self.unwrap_expression(&satisfies.expression),
            Expression::TypeAssertion(assertion) => self.unwrap_expression(&assertion.expression),
            Expression::NonNull(non_null) => self.unwrap_expression(&non_null.expression),
            _ => expression,
        }
    }

    fn chain_has_optional(&self, expression: &Expr) -> bool {
        match expression.data() {
            Expression::Member(member) => {
                member.optional || self.chain_has_optional(&member.object)
            }
            Expression::Call(call) => call.optional || self.chain_has_optional(&call.callee),
            Expression::NonNull(non_null) => self.chain_has_optional(&non_null.expression),
            Expression::Parenthesized(inner) => self.chain_has_optional(inner),
            Expression::As(as_expr) => self.chain_has_optional(&as_expr.expression),
            Expression::Satisfies(satisfies) => self.chain_has_optional(&satisfies.expression),
            Expression::TypeAssertion(assertion) => self.chain_has_optional(&assertion.expression),
            _ => false,
        }
    }

    /// Whether an expression, at a statement or arrow-body position, would begin
    /// with a token requiring wrapping parentheses (`{`, `function`, `class`).
    fn leads_with_bad_token(&self, expression: &Expr, objects_only: bool) -> bool {
        match expression.data() {
            Expression::Object(_) => true,
            Expression::Function(_) | Expression::Class(_) => !objects_only,
            Expression::Binary(binary) => self.leads_with_bad_token(&binary.left, objects_only),
            Expression::Logical(logical) => self.leads_with_bad_token(&logical.left, objects_only),
            Expression::Conditional(conditional) => {
                self.leads_with_bad_token(&conditional.test, objects_only)
            }
            Expression::Assignment(assignment) => self.target_leads_with_object(&assignment.left),
            Expression::Sequence(sequence) => sequence
                .expressions
                .first()
                .is_some_and(|first| self.leads_with_bad_token(first, objects_only)),
            Expression::Call(call) => self.leads_with_bad_token(&call.callee, objects_only),
            Expression::Member(member) => self.leads_with_bad_token(&member.object, objects_only),
            Expression::TaggedTemplate(tagged) => {
                self.leads_with_bad_token(&tagged.tag, objects_only)
            }
            Expression::Update(update) => {
                !update.prefix && self.target_leads_with_object(&update.argument)
            }
            Expression::NonNull(non_null) => {
                self.leads_with_bad_token(&non_null.expression, objects_only)
            }
            Expression::As(as_expr) => self.leads_with_bad_token(&as_expr.expression, objects_only),
            Expression::Satisfies(satisfies) => {
                self.leads_with_bad_token(&satisfies.expression, objects_only)
            }
            Expression::TypeAssertion(assertion) => {
                self.leads_with_bad_token(&assertion.expression, objects_only)
            }
            Expression::Parenthesized(inner) => self.leads_with_bad_token(inner, objects_only),
            _ => false,
        }
    }

    fn target_leads_with_object(&self, target: &AssignmentTargetNode) -> bool {
        match target.data() {
            AssignmentTarget::Object(_) => true,
            AssignmentTarget::Member(member) => self.leads_with_bad_token(&member.object, false),
            _ => false,
        }
    }
    /// Whether emission of this expression starts with a printed `(`.
    /// Walks only the left edge through nodes whose emission forwards to
    /// it, stopping at parenthesized nodes (which print their own parens)
    /// instead of seeing through them like [`Self::leads_with_bad_token`]
    /// does. Naming the upstream query: this is the `GetLeftmostExpression`
    /// stop-at-parens half of the statement-position decision.
    fn starts_parenthesized(&self, expression: &Expr) -> bool {
        match expression.data() {
            Expression::Parenthesized(_) => true,
            Expression::As(as_expr) => self.starts_parenthesized(&as_expr.expression),
            Expression::Satisfies(satisfies) => self.starts_parenthesized(&satisfies.expression),
            Expression::TypeAssertion(assertion) => {
                self.starts_parenthesized(&assertion.expression)
            }
            Expression::NonNull(non_null) => self.starts_parenthesized(&non_null.expression),
            Expression::Binary(binary) => self.starts_parenthesized(&binary.left),
            Expression::Logical(logical) => self.starts_parenthesized(&logical.left),
            Expression::Conditional(conditional) => self.starts_parenthesized(&conditional.test),
            Expression::Sequence(sequence) => sequence
                .expressions
                .first()
                .is_some_and(|first| self.starts_parenthesized(first)),
            Expression::Call(call) => self.starts_parenthesized(&call.callee),
            Expression::Member(member) => self.starts_parenthesized(&member.object),
            Expression::TaggedTemplate(tagged) => self.starts_parenthesized(&tagged.tag),
            Expression::Update(update) if !update.prefix => {
                self.target_starts_parenthesized(&update.argument)
            }
            Expression::Assignment(assignment) => {
                self.target_starts_parenthesized(&assignment.left)
            }
            _ => false,
        }
    }

    fn target_starts_parenthesized(&self, target: &AssignmentTargetNode) -> bool {
        match target.data() {
            AssignmentTarget::Member(member) => self.starts_parenthesized(&member.object),
            _ => false,
        }
    }

    // =======================================================================
    // Declaration (.d.ts) emit
    // =======================================================================

    fn emit_declaration(&mut self, statement: &Stmt) -> bool {
        let previous = self.anchor;
        self.anchor = statement.range();
        // Emit leading JSDoc comments for declarations that retain them.
        let needs_jsdoc = matches!(
            statement.data(),
            Statement::Variable(_)
                | Statement::Function(_)
                | Statement::Class(_)
                | Statement::Interface(_)
                | Statement::TypeAlias(_)
                | Statement::Enum(_)
                | Statement::Namespace(_)
                | Statement::Export(_)
        );
        if needs_jsdoc {
            self.emit_jsdoc_for_range(self.anchor);
        }
        let emitted = match statement.data() {
            Statement::Import(import) => self.emit_import(import, true),
            Statement::ImportEquals(import) => {
                self.emit_import_equals_decl(import);
                true
            }
            Statement::Export(export) => self.emit_export_decl(export),
            Statement::Variable(declaration) => {
                self.emit_variable_decl(declaration);
                true
            }
            Statement::Function(function) => {
                self.emit_declare_prefix();
                self.emit_function_signature_decl(&function.function);
                true
            }
            Statement::Class(class) => {
                self.emit_decorators_block(&class.decorators);
                self.emit_declare_prefix();
                self.emit_class_core_decl(class);
                true
            }
            Statement::Interface(interface) => {
                self.emit_interface_decl(interface);
                true
            }
            Statement::TypeAlias(alias) => {
                self.emit_type_alias_decl(alias);
                true
            }
            Statement::Enum(declaration) => {
                self.emit_enum_decl(declaration);
                true
            }
            Statement::Namespace(namespace) => {
                self.emit_namespace_decl(statement.id(), namespace);
                true
            }
            Statement::Declare(inner) => self.emit_declaration(inner),
            Statement::Missing(_) => {
                self.diag_here(
                    codes::MISSING_STATEMENT,
                    "cannot emit a missing statement node",
                );
                false
            }
            _ => false,
        };
        self.anchor = previous;
        emitted
    }

    fn decl_statement_emits(&self, statement: &Stmt) -> bool {
        matches!(
            statement.data(),
            Statement::Import(_)
                | Statement::ImportEquals(_)
                | Statement::Variable(_)
                | Statement::Function(_)
                | Statement::Class(_)
                | Statement::Interface(_)
                | Statement::TypeAlias(_)
                | Statement::Enum(_)
                | Statement::Namespace(_)
                | Statement::Declare(_)
        )
    }

    fn emit_declare_prefix(&mut self) {
        if self.decl_ambient {
            self.raw("declare ");
        }
    }

    fn emit_import_equals_decl(&mut self, import: &ImportEqualsDeclaration) {
        self.emit_declare_prefix();
        self.raw("import ");
        if import.is_type_only {
            self.raw("type ");
        }
        self.emit_ident(&import.local);
        self.raw(" = ");
        match &import.reference {
            ExternalModuleReference::Require(source) => {
                self.raw("require(");
                self.emit_string(source);
                self.raw(")");
            }
            ExternalModuleReference::Qualified(name) => self.emit_entity_name(name),
            ExternalModuleReference::Missing(_) => {
                self.diag_here(
                    codes::MISSING_NAME,
                    "cannot emit a missing module reference",
                );
            }
        }
        self.raw(";");
    }

    fn emit_export_decl(&mut self, export: &ExportDeclaration) -> bool {
        match export {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner)) => {
                if !self.decl_statement_emits(inner) {
                    return false;
                }
                // tsc prefixes exported declarations of a TypeScript source with
                // `declare`, but not those of a JavaScript source. Inside a
                // namespace body `decl_ambient` is already false, so no prefix
                // is emitted there either. An explicit `export declare X` in
                // the source keeps its prefix through `Statement::Declare`;
                // `export import X = ...` never takes the ambient prefix.
                let saved_ambient = self.decl_ambient;
                let is_import_equals = matches!(inner.data(), Statement::ImportEquals(_));
                self.decl_ambient = (saved_ambient && !self.decl_source_is_js && !is_import_equals)
                    || matches!(inner.data(), Statement::Declare(_));
                // Identifier-named namespaces and `global` bodies drop the
                // `export` keyword from member declarations; the container is
                // the public surface.
                let export_keyword = if self.decl_drop_member_export && !is_import_equals {
                    ""
                } else {
                    "export "
                };
                if let Statement::Class(class) = inner.data() {
                    self.emit_decorators_block(&class.decorators);
                    self.raw(export_keyword);
                    self.emit_declare_prefix();
                    self.emit_class_core_decl(class);
                    self.decl_ambient = saved_ambient;
                    return true;
                }
                self.raw(export_keyword);
                let emitted = self.emit_declaration(inner);
                self.decl_ambient = saved_ambient;
                emitted
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source,
                attributes,
            }) => {
                self.raw("export ");
                if *type_only {
                    self.raw("type ");
                }
                if specifiers.is_empty() {
                    self.raw("{}");
                } else {
                    self.raw("{ ");
                    for (index, specifier) in specifiers.iter().enumerate() {
                        if index > 0 {
                            self.raw(", ");
                        }
                        self.emit_export_specifier(specifier.data(), !*type_only);
                    }
                    self.raw(" }");
                }
                if let Some(source) = source {
                    self.raw(" from ");
                    self.emit_string(source);
                    if let Some(attributes) = attributes {
                        self.emit_import_attributes(attributes);
                    }
                }
                self.raw(";");
                true
            }
            ExportDeclaration::All(all) => {
                self.raw("export ");
                if all.type_only {
                    self.raw("type ");
                }
                self.raw("* ");
                if let Some(name) = &all.exported {
                    self.raw("as ");
                    self.emit_module_export_name(name);
                    self.raw(" ");
                }
                self.raw("from ");
                self.emit_string(&all.source);
                if let Some(attributes) = &all.attributes {
                    self.emit_import_attributes(attributes);
                }
                self.raw(";");
                true
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    self.raw("export default ");
                    self.emit_function_signature_decl(function);
                    true
                }
                ExportDefaultValue::Class(class) => {
                    self.raw("export default ");
                    self.emit_class_core_decl(class);
                    true
                }
                ExportDefaultValue::Interface(interface) => {
                    self.raw("export default ");
                    self.emit_interface_decl(interface);
                    true
                }
                ExportDefaultValue::Expression(expression) => {
                    self.raw("export default ");
                    self.emit_expression_prec(expression, P_ASSIGN);
                    self.raw(";");
                    true
                }
                ExportDefaultValue::Missing(_) => {
                    self.diag_here(
                        codes::MISSING_EXPRESSION,
                        "cannot emit a missing default export",
                    );
                    false
                }
            },
            ExportDeclaration::Assignment(expression) => {
                self.raw("export = ");
                self.emit_expression_prec(expression, P_ASSIGN);
                self.raw(";");
                true
            }
        }
    }

    /// Extracts all consecutive `/** ... */` JSDoc comments immediately
    /// preceding `range`, in source order. Multiple adjacent JSDoc blocks
    /// separated only by whitespace are all retained (e.g. `@import defer`
    /// followed by `@type`).
    fn extract_jsdoc(&self, range: TextRange) -> Option<String> {
        let source = self.source;
        let byte_start = source.utf16_to_byte(range.start()).ok()?;
        let text = source.as_str();

        // Walk backwards from the declaration, collecting consecutive JSDoc
        // blocks separated only by whitespace.
        let mut comments: Vec<&str> = Vec::new();
        let mut cursor = byte_start;
        loop {
            let before = text.get(..cursor)?;
            // Skip trailing whitespace between the comment end and cursor.
            let trimmed_end = before.trim_end();
            if trimmed_end.len() == before.len() {
                // No whitespace before cursor — no comment here.
                break;
            }
            let after_trim = text.get(trimmed_end.len()..cursor)?;
            if !after_trim.chars().all(|ch| ch.is_whitespace()) {
                break;
            }
            // Find the last `/**` before the trimmed position.
            let Some(comment_start) = trimmed_end.rfind("/**") else {
                break;
            };
            let after_open = text.get(comment_start..)?;
            if after_open.starts_with("/**/") {
                break;
            }
            let Some(close_offset) = after_open.find("*/") else {
                break;
            };
            let comment_end = comment_start + close_offset + 2;
            // Verify only whitespace between comment end and cursor.
            let between = text.get(comment_end..cursor)?;
            if !between.chars().all(|ch| ch.is_whitespace()) {
                break;
            }
            comments.push(text.get(comment_start..comment_end)?);
            cursor = comment_start;
        }
        if comments.is_empty() {
            None
        } else {
            // Reverse to get source order (earliest first).
            comments.reverse();
            Some(comments.join("\n"))
        }
    }

    /// Emits all JSDoc comments preceding a declaration at `range`, if any
    /// exist in the source text. Each comment is printed on its own line
    /// with the current indentation, followed by a newline.
    fn emit_jsdoc_for_range(&mut self, range: TextRange) {
        if let Some(jsdoc) = self.extract_jsdoc(range) {
            self.raw(&jsdoc);
            self.newline();
        }
    }

    /// Returns `true` if `expression` is a bare `Symbol()` call.
    fn is_symbol_call(&self, expression: &crate::syntax::Expression) -> bool {
        if let crate::syntax::Expression::Call(call) = expression
            && let crate::syntax::Expression::Identifier(ident) = call.callee.data()
        {
            return self.text(ident.data().token()) == Some("Symbol");
        }
        false
    }

    /// Renders a type for declaration emit, widening literal types for
    /// `let`/`var` bindings as tsc does.
    fn render_inferred_type(&self, type_id: TypeId, kind: VariableKind) -> String {
        match (self.model.types().get(type_id), kind) {
            (Type::BooleanLiteral(_), VariableKind::Let | VariableKind::Var) => {
                "boolean".to_owned()
            }
            (Type::NumberLiteral(_), VariableKind::Let | VariableKind::Var) => "number".to_owned(),
            (Type::StringLiteral(_), VariableKind::Let | VariableKind::Var) => "string".to_owned(),
            (Type::BigIntLiteral(_), VariableKind::Let | VariableKind::Var) => "bigint".to_owned(),
            _ => render_type_declaration(self.model, type_id, self.current_indent_spaces()),
        }
    }

    fn emit_variable_decl(&mut self, declaration: &VariableDeclaration) {
        self.emit_declare_prefix();
        self.raw(variable_kind_str(declaration.kind));
        self.raw(" ");
        for (index, declarator) in declaration.declarations.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            let declarator = declarator.data();
            self.emit_pattern(&declarator.binding);
            if let Some(annotation) = &declarator.type_annotation {
                self.raw(": ");
                self.emit_type(&annotation.data().type_node);
            } else if let Some(initializer) = &declarator.initializer {
                // No explicit annotation: infer the type from the initializer
                // as tsc does in `.d.ts` emit.
                if self.is_symbol_call(initializer.data()) {
                    if declaration.kind == VariableKind::Const {
                        self.raw(": unique symbol");
                    } else {
                        self.raw(": symbol");
                    }
                } else if let Some(type_id) = self.model.node_type(initializer.id()) {
                    let rendered = self.render_inferred_type(type_id, declaration.kind);
                    if !rendered.is_empty() {
                        self.raw(": ");
                        self.raw(&rendered);
                    }
                }
            }
        }
        self.raw(";");
    }

    fn emit_function_signature_decl(&mut self, function: &FunctionLike) {
        self.raw("function");
        if let Some(name) = &function.name {
            self.raw(" ");
            self.emit_ident(name);
        }
        self.emit_type_parameters(&function.type_parameters);
        self.emit_params_decl(&function.parameters);
        if let Some(return_type) = &function.return_type {
            self.raw(": ");
            self.emit_type(&return_type.data().type_node);
        } else if let Some(name) = &function.name {
            // No explicit return annotation: look up the function's symbol
            // and infer the return type from its signature as tsc does.
            let name_text = self.text(name.data().token()).unwrap_or("");
            if let Some(symbol) = self.model.lookup_value(self.current_scope, name_text) {
                let type_id = self.model.symbol_type(symbol);
                if let Type::Function(signature) = self.model.types().get(type_id) {
                    let ret = signature.return_type();
                    let rendered =
                        render_type_declaration(self.model, ret, self.current_indent_spaces());
                    if !rendered.is_empty() {
                        self.raw(": ");
                        self.raw(&rendered);
                    }
                }
            }
        }
        self.raw(";");
    }

    fn emit_params_decl(&mut self, parameters: &[ParameterNode]) {
        self.raw("(");
        for (index, parameter) in parameters.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            let parameter = parameter.data();
            if let Some(accessibility) = parameter.modifiers.accessibility {
                self.raw(accessibility_str(accessibility));
                self.raw(" ");
            }
            if parameter.modifiers.is_readonly {
                self.raw("readonly ");
            }
            self.emit_pattern(&parameter.binding);
            if parameter.optional {
                self.raw("?");
            }
            if let Some(annotation) = &parameter.type_annotation {
                self.raw(": ");
                self.emit_type(&annotation.data().type_node);
            }
        }
        self.raw(")");
    }

    fn emit_class_core_decl(&mut self, class: &ClassDeclaration) {
        let range = self.anchor;
        if class.modifiers.is_abstract {
            self.raw("abstract ");
        }
        self.raw("class");
        if let Some(name) = &class.name {
            self.raw(" ");
            self.emit_ident(name);
        }
        self.emit_type_parameters(&class.type_parameters);
        if let Some(heritage) = &class.extends {
            self.raw(" extends ");
            self.emit_expression_prec(&heritage.expression, P_CALL_MEMBER);
            self.emit_type_arguments(&heritage.type_arguments);
        }
        if !class.implements.is_empty() {
            self.raw(" implements ");
            for (index, interface) in class.implements.iter().enumerate() {
                if index > 0 {
                    self.raw(", ");
                }
                self.emit_type(interface);
            }
        }
        self.raw(" ");
        self.emit_class_body_decl(&class.members, range);
    }
    fn emit_class_body_decl(&mut self, members: &[ClassMemberNode], range: TextRange) {
        self.raw("{");
        let has = members
            .iter()
            .any(|member| self.class_member_emits_decl(member.data()));
        if has {
            self.newline();
            self.indent += 1;
        }
        for member in members {
            if self.class_member_emits_decl(member.data()) {
                self.emit_jsdoc_for_range(member.range());
            }
            if self.emit_class_member_decl(member.data()) {
                self.newline();
            }
        }
        if has {
            self.indent -= 1;
        } else {
            self.newline();
        }
        self.raw_mapped_eol("}", range, '}');
    }

    fn class_member_emits_decl(&self, member: &ClassMember) -> bool {
        !matches!(
            member,
            ClassMember::StaticBlock(_) | ClassMember::Missing(_)
        )
    }

    fn emit_class_member_decl(&mut self, member: &ClassMember) -> bool {
        match member {
            ClassMember::Constructor(constructor) => {
                if let Some(accessibility) = constructor.modifiers.accessibility {
                    self.raw(accessibility_str(accessibility));
                    self.raw(" ");
                }
                self.raw("constructor");
                self.emit_params_decl(&constructor.parameters);
                self.raw(";");
                true
            }
            ClassMember::Method(method) => {
                self.emit_member_modifiers_decl(&method.modifiers);
                match method.modifier {
                    PropertyModifier::Get => self.raw("get "),
                    PropertyModifier::Set => self.raw("set "),
                    PropertyModifier::None => {}
                }
                self.emit_property_name(&method.name);
                if method.optional {
                    self.raw("?");
                }
                self.emit_type_parameters(&method.function.type_parameters);
                self.emit_params_decl(&method.function.parameters);
                if let Some(return_type) = &method.function.return_type {
                    self.raw(": ");
                    self.emit_type(&return_type.data().type_node);
                }
                self.raw(";");
                true
            }
            ClassMember::Property(property) => {
                self.emit_member_modifiers_decl(&property.modifiers);
                self.emit_property_name(&property.name);
                if property.optional {
                    self.raw("?");
                }
                if let Some(annotation) = &property.type_annotation {
                    self.raw(": ");
                    self.emit_type(&annotation.data().type_node);
                } else if let Some(initializer) = &property.initializer
                    && let Some(type_id) = self.model.node_type(initializer.id())
                {
                    let rendered =
                        render_type_declaration(self.model, type_id, self.current_indent_spaces());
                    if !rendered.is_empty() {
                        self.raw(": ");
                        self.raw(&rendered);
                    }
                }
                self.raw(";");
                true
            }
            ClassMember::AutoAccessor(accessor) => {
                self.emit_member_modifiers_decl(&accessor.modifiers);
                self.raw("accessor ");
                self.emit_property_name(&accessor.name);
                if let Some(annotation) = &accessor.type_annotation {
                    self.raw(": ");
                    self.emit_type(&annotation.data().type_node);
                }
                self.raw(";");
                true
            }
            ClassMember::IndexSignature(signature) => {
                if signature.readonly {
                    self.raw("readonly ");
                }
                self.raw("[");
                self.emit_params_decl_inner(&signature.parameters);
                self.raw("]: ");
                self.emit_type(&signature.type_annotation.data().type_node);
                self.raw(";");
                true
            }
            ClassMember::StaticBlock(_) => false,
            ClassMember::Missing(_) => {
                self.diag_here(codes::MISSING_MEMBER, "cannot emit a missing class member");
                false
            }
        }
    }

    fn emit_params_decl_inner(&mut self, parameters: &[ParameterNode]) {
        for (index, parameter) in parameters.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            let parameter = parameter.data();
            self.emit_pattern(&parameter.binding);
            if let Some(annotation) = &parameter.type_annotation {
                self.raw(": ");
                self.emit_type(&annotation.data().type_node);
            }
        }
    }

    fn emit_member_modifiers_decl(&mut self, modifiers: &DeclarationModifiers) {
        if let Some(accessibility) = modifiers.accessibility {
            self.raw(accessibility_str(accessibility));
            self.raw(" ");
        }
        if modifiers.is_static {
            self.raw("static ");
        }
        if modifiers.is_abstract {
            self.raw("abstract ");
        }
        if modifiers.is_readonly {
            self.raw("readonly ");
        }
    }

    fn emit_interface_decl(&mut self, interface: &InterfaceDeclaration) {
        self.raw("interface ");
        self.emit_ident(&interface.name);
        self.emit_type_parameters(&interface.type_parameters);
        if !interface.extends.is_empty() {
            self.raw(" extends ");
            for (index, reference) in interface.extends.iter().enumerate() {
                if index > 0 {
                    self.raw(", ");
                }
                self.emit_type_reference(reference);
            }
        }
        self.raw(" ");
        if interface.members.is_empty() {
            // Authority: importTag16 a.d.ts expands tight-authored
            // `export interface I {}` to `{\n}` (0 tight / 21 expand in
            // true declaration outputs). Object types keep the shared
            // tight branch below, so the split lives here, not there.
            self.raw("{");
            self.newline();
            self.raw("}");
            return;
        }
        self.emit_type_members_block(&interface.members);
    }

    fn emit_type_alias_decl(&mut self, alias: &TypeAliasDeclaration) {
        self.raw("type ");
        self.emit_ident(&alias.name);
        self.emit_type_parameters(&alias.type_parameters);
        self.raw(" = ");
        self.emit_type(&alias.type_node);
        self.raw(";");
    }

    fn emit_enum_decl(&mut self, declaration: &EnumDeclaration) {
        self.emit_declare_prefix();
        if declaration.is_const {
            self.raw("const ");
        }
        self.raw("enum ");
        self.emit_ident(&declaration.name);
        self.raw(" ");
        if declaration.members.is_empty() {
            self.raw("{}");
            return;
        }
        self.raw("{");
        self.newline();
        self.indent += 1;
        let count = declaration.members.len();
        for (index, member) in declaration.members.iter().enumerate() {
            let member = member.data();
            self.emit_property_name(&member.name);
            if let Some(initializer) = &member.initializer {
                self.raw(" = ");
                self.emit_expression_prec(initializer, P_ASSIGN);
            }
            if index + 1 < count {
                self.raw(",");
            }
            self.newline();
        }
        self.indent -= 1;
        self.raw("}");
    }

    fn emit_namespace_decl(&mut self, id: crate::syntax::NodeId, namespace: &NamespaceDeclaration) {
        self.emit_declare_prefix();
        match &namespace.name {
            NamespaceName::Identifier { name, keyword } => {
                self.raw(keyword.as_str());
                self.raw(" ");
                self.emit_ident(name);
            }
            NamespaceName::StringLiteral(name) => {
                self.raw("module ");
                self.emit_string(name);
            }
            NamespaceName::Global { .. } => self.raw("global"),
        }
        self.raw(" {");
        let body = namespace.body.data();
        if body.statements.is_empty() {
            self.raw("}");
            return;
        }
        self.newline();
        self.indent += 1;
        let saved_ambient = self.decl_ambient;
        self.decl_ambient = false;
        let saved_scope = self.current_scope;
        // Function declarations inside the body resolve unqualified names
        // (inferred return types) against the namespace's local scope, which
        // holds the member bindings, not the enclosing module scope.
        if let Some(scope) = self.model.namespace_local_scope(id) {
            self.current_scope = scope;
        }
        let saved_drop = self.decl_drop_member_export;
        // String-named `module "..."` bodies are external module declarations
        // and keep member `export`; identifier-named namespaces and `global`
        // expose members through the container, so tsc drops the keyword.
        self.decl_drop_member_export = !matches!(&namespace.name, NamespaceName::StringLiteral(_));
        for statement in &body.statements {
            if self.emit_declaration(statement) {
                self.newline();
            }
        }
        self.decl_drop_member_export = saved_drop;
        self.current_scope = saved_scope;
        self.decl_ambient = saved_ambient;
        self.indent -= 1;
        self.raw("}");
    }

    // ---- types ------------------------------------------------------------

    fn emit_type_parameters(&mut self, parameters: &Option<TypeParameterList>) {
        let Some(list) = parameters else {
            return;
        };
        if list.parameters.is_empty() {
            return;
        }
        self.raw("<");
        for (index, parameter) in list.parameters.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            self.emit_type_parameter(parameter.data());
        }
        self.raw(">");
    }

    fn emit_type_parameter(&mut self, parameter: &TypeParameter) {
        match parameter.variance {
            Variance::In => self.raw("in "),
            Variance::Out => self.raw("out "),
            Variance::InOut => self.raw("in out "),
            Variance::Invariant => {}
        }
        self.emit_ident(&parameter.name);
        if let Some(constraint) = &parameter.constraint {
            self.raw(" extends ");
            self.emit_type(constraint);
        }
        if let Some(default) = &parameter.default {
            self.raw(" = ");
            self.emit_type(default);
        }
    }

    fn emit_type_arguments(&mut self, arguments: &Option<TypeArgumentList>) {
        let Some(list) = arguments else {
            return;
        };
        if list.arguments.is_empty() {
            return;
        }
        self.raw("<");
        for (index, argument) in list.arguments.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            // tsc wraps generic function-type and constructor-type arguments
            // (those with their own type parameters) in parentheses to
            // disambiguate `<<T>() => T>` from a misplaced `<<`. Non-generic
            // function types like `() => number` stay unwrapped.
            // See baselines: declarationEmitFirstTypeArgumentGenericFunctionType.d.ts
            // and declFileForFunctionTypeAsTypeParameter.d.ts.
            let needs_parens = match self.unwrap_type(argument).data() {
                TypeNode::Function(ft) => ft
                    .type_parameters
                    .as_ref()
                    .is_some_and(|tp| !tp.parameters.is_empty()),
                TypeNode::Constructor(ct) => ct
                    .function
                    .type_parameters
                    .as_ref()
                    .is_some_and(|tp| !tp.parameters.is_empty()),
                _ => false,
            };
            if needs_parens {
                self.raw("(");
            }
            self.emit_type(argument);
            if needs_parens {
                self.raw(")");
            }
        }
        self.raw(">");
    }

    fn emit_type_reference(&mut self, reference: &TypeReference) {
        self.emit_entity_name(&reference.name);
        self.emit_type_arguments(&reference.type_arguments);
    }

    fn emit_type(&mut self, ty: &Ty) {
        let previous = self.anchor;
        self.anchor = ty.range();
        match ty.data() {
            TypeNode::Keyword(keyword) => self.raw(keyword_type_str(*keyword)),
            TypeNode::Literal(literal) => self.emit_type_literal(literal),
            TypeNode::Reference(reference) => self.emit_type_reference(reference),
            TypeNode::Union(members) => self.emit_union(members),
            TypeNode::Intersection(members) => self.emit_intersection(members),
            TypeNode::Array(element) => {
                self.emit_type_postfix_operand(element);
                self.raw("[]");
            }
            TypeNode::Tuple(tuple) => self.emit_tuple(tuple),
            TypeNode::Object(object) => self.emit_object_type(object),
            TypeNode::Function(function) => self.emit_function_type(function),
            TypeNode::Constructor(constructor) => {
                if constructor.is_abstract {
                    self.raw("abstract ");
                }
                self.raw("new ");
                self.emit_function_type_body_arrow(&constructor.function);
            }
            TypeNode::Query(query) => {
                self.raw("typeof ");
                self.emit_entity_name(&query.name);
                self.emit_type_arguments(&query.type_arguments);
            }
            TypeNode::Operator { operator, operand } => {
                self.raw(type_operator_str(*operator));
                self.raw(" ");
                self.emit_type_operator_operand(operand);
            }
            TypeNode::IndexedAccess(indexed) => {
                self.emit_type_postfix_operand(&indexed.object_type);
                self.raw("[");
                self.emit_type(&indexed.index_type);
                self.raw("]");
            }
            TypeNode::Conditional(conditional) => {
                self.emit_type(&conditional.check_type);
                self.raw(" extends ");
                self.emit_type(&conditional.extends_type);
                self.raw(" ? ");
                self.emit_type(&conditional.true_type);
                self.raw(" : ");
                self.emit_type(&conditional.false_type);
            }
            TypeNode::Mapped(mapped) => self.emit_mapped_type(mapped),
            TypeNode::Infer(infer) => {
                self.raw("infer ");
                self.emit_ident(&infer.parameter.data().name);
                if let Some(constraint) = &infer.parameter.data().constraint {
                    self.raw(" extends ");
                    self.emit_type(constraint);
                }
            }
            TypeNode::Import(import) => {
                self.raw("import(");
                self.emit_string(&import.argument);
                self.raw(")");
                if let Some(qualifier) = &import.qualifier {
                    self.raw(".");
                    self.emit_entity_name(qualifier);
                }
                self.emit_type_arguments(&import.type_arguments);
            }
            TypeNode::TemplateLiteral(template) => self.emit_template_literal_type(template),
            TypeNode::Parenthesized(inner) => self.emit_type(inner),
            TypeNode::This => self.raw("this"),
            TypeNode::Predicate(predicate) => self.emit_type_predicate(predicate),
            TypeNode::Missing(_) => {
                self.diag_here(codes::MISSING_TYPE, "cannot emit a missing type node");
                self.raw("any");
            }
        }
        self.anchor = previous;
    }

    fn emit_type_literal(&mut self, literal: &TypeLiteral) {
        match literal {
            TypeLiteral::String(node) => self.emit_token(node.data().token()),
            TypeLiteral::Number(node) => self.emit_token(node.data().token()),
            TypeLiteral::BigInt(node) => self.emit_token(node.data().token()),
            TypeLiteral::Boolean(node) => self.emit_token(node.data().token()),
            TypeLiteral::Null(node) => match self.text(node.data().token()) {
                Some(text) if !text.is_empty() => self.raw(text),
                _ => self.raw("null"),
            },
            TypeLiteral::Unary { operator, operand } => {
                self.raw(unary_operator_str(*operator));
                self.emit_type(operand);
            }
        }
    }

    fn emit_union(&mut self, members: &[Ty]) {
        for (index, member) in members.iter().enumerate() {
            if index > 0 {
                self.raw(" | ");
            }
            if is_low_precedence_type(self.unwrap_type(member)) {
                self.raw("(");
                self.emit_type(member);
                self.raw(")");
            } else {
                self.emit_type(member);
            }
        }
    }

    fn emit_intersection(&mut self, members: &[Ty]) {
        for (index, member) in members.iter().enumerate() {
            if index > 0 {
                self.raw(" & ");
            }
            let inner = self.unwrap_type(member);
            if is_low_precedence_type(inner) || matches!(inner.data(), TypeNode::Union(_)) {
                self.raw("(");
                self.emit_type(member);
                self.raw(")");
            } else {
                self.emit_type(member);
            }
        }
    }

    fn emit_type_postfix_operand(&mut self, ty: &Ty) {
        let inner = self.unwrap_type(ty);
        let wrap = is_low_precedence_type(inner)
            || matches!(
                inner.data(),
                TypeNode::Union(_) | TypeNode::Intersection(_) | TypeNode::Operator { .. }
            );
        if wrap {
            self.raw("(");
            self.emit_type(ty);
            self.raw(")");
        } else {
            self.emit_type(ty);
        }
    }

    fn emit_type_operator_operand(&mut self, ty: &Ty) {
        let inner = self.unwrap_type(ty);
        if is_low_precedence_type(inner)
            || matches!(inner.data(), TypeNode::Union(_) | TypeNode::Intersection(_))
        {
            self.raw("(");
            self.emit_type(ty);
            self.raw(")");
        } else {
            self.emit_type(ty);
        }
    }

    fn emit_tuple(&mut self, tuple: &TupleType) {
        if tuple.readonly {
            self.raw("readonly ");
        }
        self.raw("[");
        for (index, element) in tuple.elements.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            if element.rest {
                self.raw("...");
            }
            if let Some(name) = &element.name {
                self.emit_ident(name);
                if element.optional {
                    self.raw("?");
                }
                self.raw(": ");
                self.emit_type(&element.type_node);
            } else {
                self.emit_type(&element.type_node);
                if element.optional {
                    self.raw("?");
                }
            }
        }
        self.raw("]");
    }

    fn emit_object_type(&mut self, object: &ObjectType) {
        self.emit_type_members_block(&object.members);
    }

    fn emit_type_members_block(&mut self, members: &[TypeMemberNode]) {
        if members.is_empty() {
            self.raw("{}");
            return;
        }
        self.raw("{");
        self.newline();
        self.indent += 1;
        for member in members {
            self.emit_type_member(member.data());
            self.newline();
        }
        self.indent -= 1;
        self.raw("}");
    }

    fn emit_type_member(&mut self, member: &TypeMember) {
        match member {
            TypeMember::Property(property) => {
                if property.readonly {
                    self.raw("readonly ");
                }
                self.emit_property_name(&property.name);
                if property.optional {
                    self.raw("?");
                }
                if let Some(annotation) = &property.type_annotation {
                    self.raw(": ");
                    self.emit_type(&annotation.data().type_node);
                }
                self.raw(";");
            }
            TypeMember::Method(method) => {
                self.emit_property_name(&method.name);
                if method.optional {
                    self.raw("?");
                }
                self.emit_function_type_body(&method.function);
                self.raw(";");
            }
            TypeMember::Call(call) => {
                self.emit_function_type_body(&call.function);
                self.raw(";");
            }
            TypeMember::Construct(construct) => {
                self.raw("new ");
                self.emit_function_type_body(&construct.function.function);
                self.raw(";");
            }
            TypeMember::Index(index) => {
                if index.readonly {
                    self.raw("readonly ");
                }
                self.raw("[");
                self.emit_function_type_parameters(&index.parameters);
                self.raw("]: ");
                self.emit_type(&index.type_annotation.data().type_node);
                self.raw(";");
            }
            TypeMember::Missing(_) => {
                self.diag_here(codes::MISSING_MEMBER, "cannot emit a missing type member");
            }
        }
    }

    fn emit_function_type(&mut self, function: &FunctionType) {
        self.emit_function_type_body_arrow(function);
    }

    fn emit_function_type_body_arrow(&mut self, function: &FunctionType) {
        self.emit_type_parameters(&function.type_parameters);
        self.raw("(");
        self.emit_function_type_parameters(&function.parameters);
        self.raw(") => ");
        self.emit_type(&function.return_type);
    }

    fn emit_function_type_body(&mut self, function: &FunctionType) {
        self.emit_type_parameters(&function.type_parameters);
        self.raw("(");
        self.emit_function_type_parameters(&function.parameters);
        self.raw("): ");
        self.emit_type(&function.return_type);
    }

    fn emit_function_type_parameters(&mut self, parameters: &[FunctionTypeParameter]) {
        for (index, parameter) in parameters.iter().enumerate() {
            if index > 0 {
                self.raw(", ");
            }
            if parameter.rest {
                self.raw("...");
            }
            self.emit_ident(&parameter.name);
            if parameter.optional {
                self.raw("?");
            }
            self.raw(": ");
            self.emit_type(&parameter.type_annotation.data().type_node);
        }
    }

    fn emit_mapped_type(&mut self, mapped: &MappedType) {
        self.raw("{");
        self.newline();
        self.indent += 1;
        match mapped.readonly_modifier {
            MappedModifier::Preserve => {}
            MappedModifier::Add => self.raw("readonly "),
            MappedModifier::Remove => self.raw("-readonly "),
        }
        self.raw("[");
        self.emit_ident(&mapped.parameter.data().name);
        self.raw(" in ");
        if let Some(constraint) = &mapped.parameter.data().constraint {
            self.emit_type(constraint);
        }
        if let Some(name_type) = &mapped.name_type {
            self.raw(" as ");
            self.emit_type(name_type);
        }
        self.raw("]");
        match mapped.optional_modifier {
            MappedModifier::Preserve => {}
            MappedModifier::Add => self.raw("?"),
            MappedModifier::Remove => self.raw("-?"),
        }
        if let Some(value_type) = &mapped.value_type {
            self.raw(": ");
            self.emit_type(value_type);
        }
        self.raw(";");
        self.indent -= 1;
        self.newline();
        self.raw("}");
    }

    fn emit_template_literal_type(&mut self, template: &TemplateLiteralType) {
        if template.elements.is_empty() {
            return;
        }
        self.emit_token(template.elements[0].data().token());
        for (index, ty) in template.types.iter().enumerate() {
            self.emit_type(ty);
            if let Some(element) = template.elements.get(index + 1) {
                self.emit_token(element.data().token());
            }
        }
    }

    fn emit_type_predicate(&mut self, predicate: &TypePredicate) {
        if predicate.asserts {
            self.raw("asserts ");
        }
        self.emit_entity_name(&predicate.parameter_name);
        if let Some(ty) = &predicate.type_node {
            self.raw(" is ");
            self.emit_type(ty);
        }
    }

    fn unwrap_type<'t>(&self, ty: &'t Ty) -> &'t Ty {
        match ty.data() {
            TypeNode::Parenthesized(inner) => self.unwrap_type(inner),
            _ => ty,
        }
    }
}

// ---- free helpers ---------------------------------------------------------

/// UTF-16 length of `text`, for width arithmetic in mapping positions.
fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// Source range of an array-literal element, `None` for elisions and missing
/// placeholders, neither of which has a source token.
fn array_element_range(element: &ArrayElement) -> Option<TextRange> {
    match element {
        ArrayElement::Expression(expression) => Some(expression.range()),
        ArrayElement::Spread(spread) => Some(spread.argument.range()),
        _ => None,
    }
}

/// Source range of an array binding-pattern element.
fn array_binding_element_range(element: &ArrayBindingElement) -> Option<TextRange> {
    match element {
        ArrayBindingElement::Binding(binding) => Some(binding.range()),
        _ => None,
    }
}

/// Source range of a call argument.
fn call_argument_range(argument: &CallArgument) -> Option<TextRange> {
    match argument {
        CallArgument::Expression(expression) => Some(expression.range()),
        CallArgument::Spread(spread) => Some(spread.argument.range()),
        CallArgument::Missing(_) => None,
    }
}

/// Source range of a binding-property name, `None` for a missing name.
fn property_name_range(name: &PropertyName) -> Option<TextRange> {
    match name {
        PropertyName::Identifier(node) => Some(node.range()),
        PropertyName::Private(node) => Some(node.range()),
        PropertyName::String(node) => Some(node.range()),
        PropertyName::Number(node) => Some(node.range()),
        PropertyName::Computed(expression) => Some(expression.range()),
        PropertyName::Missing(_) => None,
    }
}

/// Source range spanning one object binding property: name through initializer.
fn object_binding_property_range(property: &ObjectBindingProperty) -> Option<TextRange> {
    let start = property_name_range(&property.name)?;
    let end = property.initializer.as_ref().map_or_else(
        || property.binding.range().end(),
        |initializer| initializer.range().end(),
    );
    TextRange::new(start.start(), end).ok()
}

fn is_parameter_property(parameter: &Parameter) -> bool {
    parameter.modifiers.accessibility.is_some()
        || parameter.modifiers.is_readonly
        || parameter.modifiers.is_override
}

const fn variable_kind_str(kind: VariableKind) -> &'static str {
    match kind {
        VariableKind::Var => "var",
        VariableKind::Let => "let",
        VariableKind::Const => "const",
        VariableKind::Using => "using",
        VariableKind::AwaitUsing => "await using",
    }
}

fn literal_range(literal: &Literal) -> TextRange {
    match literal {
        Literal::String(node) => node.range(),
        Literal::Number(node) => node.range(),
        Literal::BigInt(node) => node.range(),
        Literal::Boolean(node) => node.range(),
        Literal::Null(node) => node.range(),
        Literal::Regex(node) => node.range(),
    }
}

const fn accessibility_str(accessibility: Accessibility) -> &'static str {
    match accessibility {
        Accessibility::Public => "public",
        Accessibility::Protected => "protected",
        Accessibility::Private => "private",
    }
}

const fn binary_prec(operator: BinaryOperator) -> u8 {
    match operator {
        BinaryOperator::BitOr => P_BIT_OR,
        BinaryOperator::BitXor => P_BIT_XOR,
        BinaryOperator::BitAnd => P_BIT_AND,
        BinaryOperator::Equal
        | BinaryOperator::NotEqual
        | BinaryOperator::StrictEqual
        | BinaryOperator::StrictNotEqual => P_EQUALITY,
        BinaryOperator::LessThan
        | BinaryOperator::LessThanOrEqual
        | BinaryOperator::GreaterThan
        | BinaryOperator::GreaterThanOrEqual
        | BinaryOperator::In
        | BinaryOperator::Instanceof => P_RELATIONAL,
        BinaryOperator::LeftShift
        | BinaryOperator::SignedRightShift
        | BinaryOperator::UnsignedRightShift => P_SHIFT,
        BinaryOperator::Add | BinaryOperator::Subtract => P_ADDITIVE,
        BinaryOperator::Multiply | BinaryOperator::Divide | BinaryOperator::Remainder => {
            P_MULTIPLICATIVE
        }
        BinaryOperator::Exponentiate => P_EXPONENT,
    }
}

const fn binary_str(operator: BinaryOperator) -> &'static str {
    match operator {
        BinaryOperator::Add => "+",
        BinaryOperator::Subtract => "-",
        BinaryOperator::Multiply => "*",
        BinaryOperator::Divide => "/",
        BinaryOperator::Remainder => "%",
        BinaryOperator::Exponentiate => "**",
        BinaryOperator::LeftShift => "<<",
        BinaryOperator::SignedRightShift => ">>",
        BinaryOperator::UnsignedRightShift => ">>>",
        BinaryOperator::LessThan => "<",
        BinaryOperator::LessThanOrEqual => "<=",
        BinaryOperator::GreaterThan => ">",
        BinaryOperator::GreaterThanOrEqual => ">=",
        BinaryOperator::In => "in",
        BinaryOperator::Instanceof => "instanceof",
        BinaryOperator::Equal => "==",
        BinaryOperator::NotEqual => "!=",
        BinaryOperator::StrictEqual => "===",
        BinaryOperator::StrictNotEqual => "!==",
        BinaryOperator::BitAnd => "&",
        BinaryOperator::BitXor => "^",
        BinaryOperator::BitOr => "|",
    }
}

const fn logical_str(operator: LogicalOperator) -> &'static str {
    match operator {
        LogicalOperator::And => "&&",
        LogicalOperator::Or => "||",
        LogicalOperator::Nullish => "??",
    }
}

const fn assignment_str(operator: AssignmentOperator) -> &'static str {
    match operator {
        AssignmentOperator::Assign => "=",
        AssignmentOperator::AddAssign => "+=",
        AssignmentOperator::SubtractAssign => "-=",
        AssignmentOperator::MultiplyAssign => "*=",
        AssignmentOperator::DivideAssign => "/=",
        AssignmentOperator::RemainderAssign => "%=",
        AssignmentOperator::ExponentiateAssign => "**=",
        AssignmentOperator::LeftShiftAssign => "<<=",
        AssignmentOperator::SignedRightShiftAssign => ">>=",
        AssignmentOperator::UnsignedRightShiftAssign => ">>>=",
        AssignmentOperator::BitAndAssign => "&=",
        AssignmentOperator::BitXorAssign => "^=",
        AssignmentOperator::BitOrAssign => "|=",
        AssignmentOperator::LogicalAndAssign => "&&=",
        AssignmentOperator::LogicalOrAssign => "||=",
        AssignmentOperator::NullishAssign => "??=",
    }
}

const fn unary_operator_str(operator: UnaryOperator) -> &'static str {
    match operator {
        UnaryOperator::Plus => "+",
        UnaryOperator::Minus => "-",
        UnaryOperator::Not => "!",
        UnaryOperator::BitNot => "~",
        UnaryOperator::Typeof => "typeof ",
        UnaryOperator::Void => "void ",
        UnaryOperator::Delete => "delete ",
    }
}

const fn keyword_type_str(keyword: KeywordType) -> &'static str {
    match keyword {
        KeywordType::Any => "any",
        KeywordType::Unknown => "unknown",
        KeywordType::Never => "never",
        KeywordType::Void => "void",
        KeywordType::Undefined => "undefined",
        KeywordType::Null => "null",
        KeywordType::Boolean => "boolean",
        KeywordType::Number => "number",
        KeywordType::BigInt => "bigint",
        KeywordType::String => "string",
        KeywordType::Symbol => "symbol",
        KeywordType::Object => "object",
        KeywordType::Intrinsic => "intrinsic",
    }
}

const fn type_operator_str(operator: TypeOperator) -> &'static str {
    match operator {
        TypeOperator::Keyof => "keyof",
        TypeOperator::Unique => "unique",
        TypeOperator::Readonly => "readonly",
    }
}

fn is_low_precedence_type(ty: &Ty) -> bool {
    matches!(
        ty.data(),
        TypeNode::Function(_)
            | TypeNode::Constructor(_)
            | TypeNode::Conditional(_)
            | TypeNode::Infer(_)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::Recovered;
    use crate::source::{ScriptKind, Utf16Pos};
    use std::sync::Arc;

    /// Builds an AST with token ranges that point into a real source string, so
    /// the emitter resolves identifier and literal lexemes exactly as it would
    /// for a parser product.
    struct Builder {
        text: String,
        len: usize,
    }

    impl Builder {
        fn new() -> Self {
            Self {
                text: String::new(),
                len: 0,
            }
        }

        fn range(start: usize, end: usize) -> TextRange {
            TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered range")
        }

        fn token(&mut self, kind: TokenKind, lexeme: &str) -> Token {
            let start = self.len;
            self.text.push_str(lexeme);
            self.len += lexeme.encode_utf16().count();
            Token::new(kind, Self::range(start, self.len))
        }

        fn ident(&mut self, name: &str) -> IdentifierNode {
            let token = self.token(TokenKind::Identifier, name);
            Node::new(NodeId::new(0), token.range(), Identifier::new(token))
        }

        fn ident_expr(&mut self, name: &str) -> Expr {
            let ident = self.ident(name);
            let range = ident.range();
            Node::new(NodeId::new(0), range, Expression::Identifier(ident))
        }

        fn number(&mut self, literal: &str) -> Expr {
            let token = self.token(TokenKind::NumericLiteral, literal);
            let node = Node::new(NodeId::new(0), token.range(), NumericLiteral::new(token));
            let range = node.range();
            Node::new(
                NodeId::new(0),
                range,
                Expression::Literal(Literal::Number(node)),
            )
        }

        fn string(&mut self, literal: &str) -> StringLiteralNode {
            let token = self.token(TokenKind::StringLiteral, literal);
            Node::new(NodeId::new(0), token.range(), StringLiteral::new(token))
        }

        fn finish(self, statements: Vec<Stmt>) -> SourceFile {
            let source =
                Arc::new(SourceText::new(self.text).expect("test source fits the per-file budget"));
            let len = source.len_utf16();
            let full = TextRange::new(Utf16Pos::ZERO, len).expect("range");
            let eof = Token::new(
                TokenKind::EndOfFile,
                TextRange::new(len, len).expect("range"),
            );
            SourceFile::new(
                NodeId::new(0),
                SourceId::new(0),
                ScriptKind::TypeScript,
                full,
                source,
                Vec::new(),
                statements,
                eof,
                Vec::new(),
            )
        }
    }

    fn dummy() -> TextRange {
        TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("range")
    }

    fn expr(data: Expression) -> Expr {
        Node::new(NodeId::new(0), dummy(), data)
    }

    fn stmt(data: Statement) -> Stmt {
        Node::new(NodeId::new(0), dummy(), data)
    }

    fn expr_stmt(expression: Expr) -> Stmt {
        stmt(Statement::Expression(ExpressionStatement {
            expression: Box::new(expression),
        }))
    }

    fn binary(operator: BinaryOperator, left: Expr, right: Expr) -> Expr {
        expr(Expression::Binary(BinaryExpression {
            operator,
            left: Box::new(left),
            right: Box::new(right),
        }))
    }

    fn emit_output(file: &SourceFile, options: &EmitOptions) -> EmitOutput {
        let checked_file = SourceFile::new(
            file.id(),
            file.source_id(),
            file.script_kind(),
            file.range(),
            Arc::new(
                SourceText::new(file.source_text().as_str())
                    .expect("test source fits the per-file budget"),
            ),
            file.tokens().to_vec(),
            file.statements().to_vec(),
            *file.eof(),
            file.diagnostics().to_vec(),
        );
        let recovered = Recovered::clean(checked_file);
        let checked = crate::checker::check(&recovered);
        emit_checked(file, checked.product(), options, &EmitFileNames::default())
    }

    fn emit_js(file: &SourceFile) -> EmittedFile {
        emit_output(file, &EmitOptions::default())
            .javascript
            .expect("JavaScript output")
    }

    fn emit_declaration(file: &SourceFile) -> EmitOutput {
        let options = EmitOptions {
            declaration: true,
            emit_declaration_only: true,
            ..EmitOptions::default()
        };
        emit_output(file, &options)
    }

    fn javascript(output: &EmitOutput) -> &EmittedFile {
        output.javascript.as_ref().expect("JavaScript output")
    }

    fn declaration(output: &EmitOutput) -> &EmittedFile {
        output.declaration.as_ref().expect("declaration output")
    }

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // a + b * c -- no parentheses required.
        let tree = binary(
            BinaryOperator::Add,
            a,
            binary(BinaryOperator::Multiply, bb, c),
        );
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "a + b * c;\n");
    }

    #[test]
    fn lower_precedence_left_operand_is_parenthesized() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a + b) * c -- the additive left operand needs parentheses.
        let tree = binary(
            BinaryOperator::Multiply,
            binary(BinaryOperator::Add, a, bb),
            c,
        );
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a + b) * c;\n");
    }

    #[test]
    fn exponent_is_right_associative_and_forces_left_grouping() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a ** b) ** c must keep the left grouping; a ** b ** c must not add any.
        let left_grouped = binary(
            BinaryOperator::Exponentiate,
            binary(BinaryOperator::Exponentiate, a, bb),
            c,
        );
        let file = b.finish(vec![expr_stmt(left_grouped)]);
        assert_eq!(emit_js(&file).code, "(a ** b) ** c;\n");
    }

    #[test]
    fn unary_left_of_exponent_is_parenthesized() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let neg = expr(Expression::Unary(UnaryExpression {
            operator: UnaryOperator::Minus,
            argument: Box::new(a),
        }));
        let tree = binary(BinaryOperator::Exponentiate, neg, bb);
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(-a) ** b;\n");
    }

    #[test]
    fn nullish_and_logical_or_require_parentheses_when_mixed() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a || b) ?? c -- mixing ?? with || is a syntax error without parens.
        let or = expr(Expression::Logical(LogicalExpression {
            operator: LogicalOperator::Or,
            left: Box::new(a),
            right: Box::new(bb),
        }));
        let tree = expr(Expression::Logical(LogicalExpression {
            operator: LogicalOperator::Nullish,
            left: Box::new(or),
            right: Box::new(c),
        }));
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a || b) ?? c;\n");
    }

    #[test]
    fn object_literal_expression_statement_is_parenthesized() {
        let b = Builder::new();
        let object = expr(Expression::Object(ObjectLiteral {
            members: Vec::new(),
        }));
        let file = b.finish(vec![expr_stmt(object)]);
        assert_eq!(emit_js(&file).code, "({});\n");
    }

    #[test]
    fn arrow_object_body_is_parenthesized() {
        let b = Builder::new();
        let object = expr(Expression::Object(ObjectLiteral {
            members: Vec::new(),
        }));
        let arrow = expr(Expression::Arrow(ArrowFunction {
            is_async: false,
            type_parameters: None,
            parameters: Vec::new(),
            return_type: None,
            body: FunctionBody::Expression(Box::new(object)),
        }));
        let file = b.finish(vec![expr_stmt(arrow)]);
        assert_eq!(emit_js(&file).code, "() => ({});\n");
    }

    #[test]
    fn type_annotation_is_erased_in_javascript() {
        let mut b = Builder::new();
        let name = b.ident("x");
        let init = b.number("1");
        let annotation = Node::new(
            NodeId::new(0),
            dummy(),
            TypeAnnotation {
                type_node: Box::new(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeNode::Keyword(KeywordType::Number),
                )),
            },
        );
        let binding = Node::new(
            NodeId::new(0),
            name.range(),
            BindingPattern::Identifier(name),
        );
        let declarator = Node::new(
            NodeId::new(0),
            dummy(),
            VariableDeclarator {
                binding,
                definite: false,
                type_annotation: Some(annotation),
                initializer: Some(Box::new(init)),
            },
        );
        let declaration = stmt(Statement::Variable(VariableDeclaration {
            range: dummy(),
            kind: VariableKind::Let,
            declarations: vec![declarator],
        }));
        let file = b.finish(vec![declaration]);
        assert_eq!(emit_js(&file).code, "let x = 1;\n");
    }

    #[test]
    fn as_expression_is_erased_but_keeps_needed_parentheses() {
        let mut b = Builder::new();
        let a = b.ident_expr("a");
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        // (a + b as T) * c erases to (a + b) * c.
        let as_expr = expr(Expression::As(AsExpression {
            expression: Box::new(binary(BinaryOperator::Add, a, bb)),
            type_node: Some(Box::new(Node::new(
                NodeId::new(0),
                dummy(),
                TypeNode::Keyword(KeywordType::Any),
            ))),
        }));
        let tree = binary(BinaryOperator::Multiply, as_expr, c);
        let file = b.finish(vec![expr_stmt(tree)]);
        assert_eq!(emit_js(&file).code, "(a + b) * c;\n");
    }

    #[test]
    fn newline_policy_uses_configured_terminator() {
        let mut b = Builder::new();
        let first = expr_stmt(b.ident_expr("a"));
        let second = expr_stmt(b.ident_expr("b"));
        let file = b.finish(vec![first, second]);
        let options = EmitOptions::default().with_newline(Newline::CrLf);
        let output = emit_output(&file, &options);
        assert_eq!(javascript(&output).code, "a;\r\nb;\r\n");
    }

    #[test]
    fn missing_expression_reports_stable_diagnostic() {
        let b = Builder::new();
        let missing = expr(Expression::Missing(MissingNode::new(
            NodeKind::IdentifierExpression,
        )));
        let file = b.finish(vec![expr_stmt(missing)]);
        let output = emit_output(&file, &EmitOptions::default());
        assert_eq!(javascript(&output).code, "void 0;\n");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].code(), codes::MISSING_EXPRESSION);
        assert!(output.has_errors());
    }

    #[test]
    fn enum_lowers_to_runtime_object_with_reverse_mapping() {
        let mut b = Builder::new();
        let enum_name = b.ident("E");
        let member_a = Node::new(
            NodeId::new(1),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("A")),
                initializer: None,
            },
        );
        let member_b = Node::new(
            NodeId::new(2),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("B")),
                initializer: None,
            },
        );
        let declaration = Node::new(
            NodeId::new(3),
            dummy(),
            Statement::Enum(EnumDeclaration {
                is_const: false,
                name: enum_name,
                members: vec![member_a, member_b],
            }),
        );
        let file = b.finish(vec![declaration]);
        let expected = "var E;\n(function (E) {\n    E[E[\"A\"] = 0] = \"A\";\n    E[E[\"B\"] = 1] = \"B\";\n})(E || (E = {}));\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn enum_string_member_has_no_reverse_mapping() {
        let mut b = Builder::new();
        let enum_name = b.ident("E");
        let value = b.string("\"hi\"");
        let member = Node::new(
            NodeId::new(1),
            dummy(),
            EnumMember {
                name: PropertyName::Identifier(b.ident("A")),
                initializer: Some(Box::new(expr(Expression::Literal(Literal::String(value))))),
            },
        );
        let declaration = Node::new(
            NodeId::new(2),
            dummy(),
            Statement::Enum(EnumDeclaration {
                is_const: false,
                name: enum_name,
                members: vec![member],
            }),
        );
        let file = b.finish(vec![declaration]);
        let expected = "var E;\n(function (E) {\n    E[\"A\"] = \"hi\";\n})(E || (E = {}));\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn namespace_reports_unlowered_diagnostic_in_javascript() {
        let mut b = Builder::new();
        let name = b.ident("N");
        let body = Node::new(
            NodeId::new(0),
            dummy(),
            Block {
                statements: Vec::new(),
            },
        );
        let declaration = stmt(Statement::Namespace(NamespaceDeclaration {
            name: NamespaceName::Identifier {
                name,
                keyword: NamespaceKeyword::Namespace,
            },
            body,
        }));
        let file = b.finish(vec![declaration]);
        let output = emit_output(&file, &EmitOptions::default());
        assert_eq!(javascript(&output).code, "");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].code(), codes::NAMESPACE_UNLOWERED);
    }

    #[test]
    fn parameter_property_is_lowered_to_constructor_assignment() {
        let mut b = Builder::new();
        let class_name = b.ident("C");
        let param_name = b.ident("x");
        let binding = Node::new(
            NodeId::new(0),
            param_name.range(),
            BindingPattern::Identifier(param_name),
        );
        let parameter = Node::new(
            NodeId::new(0),
            dummy(),
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers {
                    accessibility: Some(Accessibility::Private),
                    is_readonly: false,
                    is_override: false,
                },
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let constructor = Node::new(
            NodeId::new(0),
            dummy(),
            ClassMember::Constructor(ConstructorDeclaration {
                decorators: Vec::new(),
                modifiers: DeclarationModifiers::default(),
                parameters: vec![parameter],
                body: Node::new(
                    NodeId::new(0),
                    dummy(),
                    Block {
                        statements: Vec::new(),
                    },
                ),
            }),
        );
        let class = stmt(Statement::Class(ClassDeclaration {
            decorators: Vec::new(),
            modifiers: DeclarationModifiers::default(),
            name: Some(class_name),
            type_parameters: None,
            extends: None,
            implements: Vec::new(),
            members: vec![constructor],
        }));
        let file = b.finish(vec![class]);
        let expected = "class C {\n    constructor(x) {\n        this.x = x;\n    }\n}\n";
        assert_eq!(emit_js(&file).code, expected);
    }

    #[test]
    fn declaration_mode_prints_type_alias_and_erases_bodies() {
        let mut b = Builder::new();
        let alias_name = b.ident("Id");
        let alias = stmt(Statement::TypeAlias(TypeAliasDeclaration {
            name: alias_name,
            type_parameters: None,
            type_node: Box::new(Node::new(
                NodeId::new(0),
                dummy(),
                TypeNode::Keyword(KeywordType::Number),
            )),
        }));
        let file = b.finish(vec![alias]);
        let output = emit_declaration(&file);
        assert_eq!(declaration(&output).code, "type Id = number;\n");
    }

    #[test]
    fn declaration_mode_emits_function_signature_without_body() {
        let mut b = Builder::new();
        let function_name = b.ident("f");
        let function = stmt(Statement::Function(FunctionDeclaration {
            function: FunctionLike {
                decorators: Vec::new(),
                name: Some(function_name),
                is_async: false,
                is_generator: false,
                type_parameters: None,
                parameters: Vec::new(),
                return_type: Some(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeAnnotation {
                        type_node: Box::new(Node::new(
                            NodeId::new(0),
                            dummy(),
                            TypeNode::Keyword(KeywordType::Void),
                        )),
                    },
                )),
                body: None,
            },
        }));
        let file = b.finish(vec![function]);
        let output = emit_declaration(&file);
        assert_eq!(declaration(&output).code, "declare function f(): void;\n");
    }

    #[test]
    fn union_type_parenthesizes_function_members() {
        let mut b = Builder::new();
        let alias_name = b.ident("U");
        let func_type = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Function(FunctionType {
                type_parameters: None,
                parameters: Vec::new(),
                return_type: Box::new(Node::new(
                    NodeId::new(0),
                    dummy(),
                    TypeNode::Keyword(KeywordType::Void),
                )),
                return_type_missing: false,
            }),
        );
        let number = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Keyword(KeywordType::Number),
        );
        let union = Node::new(
            NodeId::new(0),
            dummy(),
            TypeNode::Union(vec![func_type, number]),
        );
        let alias = stmt(Statement::TypeAlias(TypeAliasDeclaration {
            name: alias_name,
            type_parameters: None,
            type_node: Box::new(union),
        }));
        let file = b.finish(vec![alias]);
        let output = emit_declaration(&file);
        assert_eq!(
            declaration(&output).code,
            "type U = (() => void) | number;\n"
        );
    }

    #[test]
    fn optional_call_and_member_chain_round_trips() {
        let mut b = Builder::new();
        let object = b.ident_expr("a");
        let member = expr(Expression::Member(MemberExpression {
            object: Box::new(object),
            property: MemberProperty::Named(b.ident("b")),
            optional: true,
        }));
        let call = expr(Expression::Call(CallExpression {
            callee: Box::new(member),
            optional: true,
            type_arguments: None,
            arguments: Vec::new(),
        }));
        let file = b.finish(vec![expr_stmt(call)]);
        assert_eq!(emit_js(&file).code, "a?.b?.();\n");
    }

    #[test]
    fn conditional_test_lower_precedence_gets_parentheses() {
        let mut b = Builder::new();
        let bb = b.ident_expr("b");
        let c = b.ident_expr("c");
        let d = b.ident_expr("d");
        // (a = b) ? c : d -- assignment test must be parenthesized.
        let assign = expr(Expression::Assignment(AssignmentExpression {
            operator: AssignmentOperator::Assign,
            left: Node::new(
                NodeId::new(0),
                dummy(),
                AssignmentTarget::Identifier(b.ident("a2")),
            ),
            right: Box::new(bb),
        }));
        let conditional = expr(Expression::Conditional(ConditionalExpression {
            test: Box::new(assign),
            consequent: Box::new(c),
            alternate: Box::new(d),
        }));
        let file = b.finish(vec![expr_stmt(conditional)]);
        assert_eq!(emit_js(&file).code, "(a2 = b) ? c : d;\n");
    }

    #[test]
    fn export_type_reexport_with_source_erased_in_js() {
        let mut b = Builder::new();
        let specifier = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::TypeOnly,
                local: ModuleExportName::Identifier(b.ident("A")),
                exported: ModuleExportName::Identifier(b.ident("A")),
            },
        );
        let export_stmt = stmt(Statement::Export(ExportDeclaration::Named(
            ExportNamedDeclaration::Specifiers {
                type_only: false,
                specifiers: vec![specifier],
                source: Some(b.string("\"./mod\"")),
                attributes: None,
            },
        )));
        let file = b.finish(vec![export_stmt]);
        assert_eq!(emit_js(&file).code, "");
    }

    #[test]
    fn mixed_type_and_value_reexport_retains_value_exports() {
        let mut b = Builder::new();
        let type_spec = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::TypeOnly,
                local: ModuleExportName::Identifier(b.ident("A")),
                exported: ModuleExportName::Identifier(b.ident("A")),
            },
        );
        let val_spec = Node::new(
            NodeId::new(0),
            dummy(),
            ExportSpecifier {
                mode: ExportSpecifierMode::Value,
                local: ModuleExportName::Identifier(b.ident("B")),
                exported: ModuleExportName::Identifier(b.ident("B")),
            },
        );
        let export_stmt = stmt(Statement::Export(ExportDeclaration::Named(
            ExportNamedDeclaration::Specifiers {
                type_only: false,
                specifiers: vec![type_spec, val_spec],
                source: Some(b.string("\"./mod\"")),
                attributes: None,
            },
        )));
        let file = b.finish(vec![export_stmt]);
        assert_eq!(emit_js(&file).code, "export { B } from \"./mod\";\n");
    }

    #[test]
    fn export_assignment_emits_default_export_in_javascript_mode() {
        let input = "const answer = 42;
export = answer;";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "const answer = 42;
export default answer;
"
        );

        let reparsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(javascript(&output).code.as_str())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        assert!(reparsed.diagnostics().is_empty());
    }

    #[test]
    fn export_default_interface_is_erased_in_javascript() {
        let input = "export default interface Foo {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "");
    }

    #[test]
    fn empty_class_body_expands_in_javascript() {
        // Authority: `exnextmodulekindExportClassNameWithObject(target=es2015)`
        // emits `export class Object {}` as `export class Object {\n}`. The TS
        // emitter always expands class bodies: a strict doc-header-aware
        // census over 3846 single-unit `.ts` baselines finds zero single-line
        // classes in any `.js` output section (every `{}` keeper is an echo,
        // declaration-only, or error artifact).
        let input = "export class Object {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "export class Object {\n}\n");
    }

    #[test]
    fn empty_block_body_emits_spaced_braces_in_javascript() {
        // Authority: `expandoFunctionSymbolProperty.js` emits a tight source
        // `function inner() {}` as `function inner() { }`. The TS emitter
        // normalizes every empty block (function, method, arrow, try, static)
        // to `{ }`: 2011 spaced paren-blocks vs zero true-tight `.js`
        // outputs under the same strict census (every tight keeper is an
        // echo, declaration-only, error, or comment artifact).
        let input = "function foo() {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "function foo() { }\n");
    }

    #[test]
    fn single_line_function_body_stays_single_line_in_javascript() {
        // Authority: 292 true single-line function outputs in the stable
        // baselines (e.g. newOperatorErrorCases.js). A non-empty body
        // authored without a line break keeps `{ stmt; stmt; }`.
        let input = "function f() { return 1; }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "function f() { return 1; }\n");
    }

    #[test]
    fn multi_line_function_body_stays_expanded_in_javascript() {
        let input = "function f() {\n  return 1;\n}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "function f() {\n    return 1;\n}\n"
        );
    }

    #[test]
    fn single_line_arrow_block_body_stays_single_line_in_javascript() {
        // Authority: 3 true single-line arrow-block outputs in the stable baselines.
        let input = "const f = () => { return 1; };";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(javascript(&output).code, "const f = () => { return 1; };\n");
    }

    #[test]
    fn single_line_constructor_body_stays_single_line_in_javascript() {
        // The constructor's own body preserves one-line layout while the
        // class body around it still expands.
        let input = "class C { constructor() { this.x = 1; } }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "class C {\n    constructor() { this.x = 1; }\n}\n"
        );
    }

    #[test]
    fn constructor_parameter_property_always_expands_in_javascript() {
        // Parameter-property injections are synthesized at print time, so
        // the body expands even when authored on one line.
        let input = "class C { constructor(public x: number) {} }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            "class C {\n    constructor(x) {\n        this.x = x;\n    }\n}\n"
        );
    }

    #[test]
    fn single_line_object_literal_joins_members_in_javascript() {
        let input = "({ a: 1, b: 2 });";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({ a: 1, b: 2 });\n");
    }

    #[test]
    fn tight_authored_object_literal_gains_uniform_spacing_in_javascript() {
        // Authority: downlevelLetConst15 emits authored `{a: 1}` as `{ a: 1 }`.
        let input = "({a:1});";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({ a: 1 });\n");
    }

    #[test]
    fn multi_line_object_literal_stays_expanded_in_javascript() {
        let input = "({\n  a: 1\n});";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "({\n    a: 1\n});\n");
    }

    #[test]
    fn anonymous_function_expressions_space_before_parameters() {
        // Authority: 2dArrays (`function (val) { ... }`), FunctionExpression1_es6
        // (`function* () { }`), asyncAwaitIsolatedModules_es2017 (`async function ()`).
        // Named forms bind the space to the name: `function f(v)`, `function* g()`.
        let input = "var a = function(v) { return v; };\nvar b = function*(w) { yield w; };\nvar c = function named(x) { return x; };\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function (v)"), "{code}");
        assert!(code.contains("function* (w)"), "{code}");
        assert!(code.contains("function named(x)"), "{code}");
    }

    #[test]
    fn empty_function_body_authored_across_lines_keeps_two_lines() {
        // Authority: 285-baseline census — a newline-authored empty body
        // prints `{\n}` (ParameterList6 ctor shape); same-line keeps `{ }`.
        let input = "function f() {\n}\nclass C {\n  constructor() {\n  }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function f() {\n}\n"), "{code}");
        assert!(code.contains("constructor() {\n    }"), "{code}");
    }

    #[test]
    fn same_line_empty_bodies_keep_the_spaced_form() {
        let input = "function g() {}\nclass D { constructor() {} }\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("function g() { }"), "{code}");
        assert!(code.contains("constructor() { }"), "{code}");
    }

    #[test]
    fn statement_block_expands_even_when_authored_single_line() {
        // Authority: parser768531 baseline expands an authored single-line
        // standalone block; preservation belongs to function-family bodies.
        let input = "{ a: 3; } /x/;";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert_eq!(javascript(&output).code, "{\n    a: 3;\n}\n/x/;\n");
    }

    #[test]
    fn static_init_block_preserves_single_line_in_javascript() {
        // Authority: classThisReference(target=esnext).js keeps
        // `static { this; }` on its authored line while the class body
        // around it expands.
        let input = "class C { static { this; } static x = this; }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(
            javascript(&output).code.contains("static { this; }"),
            "{output:?}"
        );
    }

    #[test]
    fn empty_interface_body_expands_in_declaration_emit() {
        // Authority: importTag16 a.d.ts expands tight-authored
        // `export interface I {}` to `export interface I {\n}` (0 tight
        // / 21 expand in true declaration outputs; the 24 tights are
        // d.ts input copies echoed into the output zone, not outputs).
        let input = "export default interface Foo {}";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_declaration(parsed.product());
        assert_eq!(
            declaration(&output).code,
            "export default interface Foo {\n}\n"
        );
    }

    #[test]
    fn trailing_line_comment_follows_statement_in_javascript() {
        // Authority: arrayAugment prints `var y; // Expect no error here`
        // with removeComments off (the default).
        let input = "var x = 1; // first\nvar y; // Expect no error here\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var x = 1; // first\n"), "{code}");
        assert!(code.contains("var y; // Expect no error here\n"), "{code}");
    }

    #[test]
    fn bare_control_body_authored_same_line_stays_bare() {
        // Authority: APISample_* — `if (cond) return mod;` keeps its
        // brace-less authored form; a body authored on the next line
        // still wraps.
        let input = "function f(x) {\n    if (x) return 1;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("if (x) return 1;"), "{code}");
    }

    #[test]
    fn no_emit_helpers_omits_helper_definitions() {
        // Authority: asyncAliasReturnType_es6 — with noEmitHelpers the
        // __awaiter reference remains but no helper body is emitted.
        let options = EmitOptions {
            target: ScriptTarget::Es2015,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(): Promise<void> {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("return __awaiter(this, void 0, void 0, function* () {"),
            "{code}"
        );
        assert!(!code.contains("function __awaiter("), "{code}");
        assert!(!code.contains("function __generator("), "{code}");
    }

    #[test]
    fn es5_async_empty_body_lowers_to_generator_machine() {
        // Authority: es5-asyncFunction(target=es5) `empty` — a yield-free
        // body becomes the linear machine with the bare return sentinel.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function empty() {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function empty() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            return [2 /*return*/];\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_await_lowers_to_switch_machine() {
        // Authority: es5-asyncFunction(target=es5) `singleAwait` — each
        // statement-level await splits a labeled case and the resumed value
        // is consumed through _a.sent().
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function singleAwait() {\n    await x;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function singleAwait() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            switch (_a.label) {\n                case 0: return [4 /*yield*/, x];\n                case 1:\n                    _a.sent();\n                    return [2 /*return*/];\n            }\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_statements_hoist_vars_into_machine() {
        // Authority: awaitCallExpression5_es5(target=es5) `func` — var
        // declarations hoist outside __generator and rebind as assignments.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var a: boolean;\ndeclare var o: { fn(arg0: boolean, arg1: boolean, arg2: boolean): void; };\ndeclare function before(): void;\ndeclare function after(): void;\nasync function func(): Promise<void> {\n    before();\n    var b = o.fn(a, a, a);\n    after();\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function func() {\n    return __awaiter(this, void 0, void 0, function () {\n        var b;\n        return __generator(this, function (_a) {\n            before();\n            b = o.fn(a, a, a);\n            after();\n            return [2 /*return*/];\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn authored_switch_cases_never_inline() {
        // Authority: sourceMapValidationSwitch — authored single-statement
        // cases print one statement per line; only synthesized machine
        // cases print inline.
        let input = "var x = 10;\nswitch (x) {\ncase 5: x = 0;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("case 5:\n        x = 0;"), "{code}");
        assert!(!code.contains("case 5: x = 0;"), "{code}");
    }

    #[test]
    fn es5_async_arrow_becomes_function_expression() {
        // Authority: asyncArrowFunction1_es5(target=es5) — ES5 has no
        // arrows, so the lowered arrow is a function expression returning
        // the awaiter with a `void 0` receiver (arrows never bind `this`).
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "var foo = async (): Promise<void> => {\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "var foo = function () { return __awaiter(void 0, void 0, void 0, function () {\n    return __generator(this, function (_a) {\n        return [2 /*return*/];\n    });\n}); };";
        assert!(code.contains(expected), "{code}");
    }

    #[test]
    fn es5_async_if_branch_await_builds_labeled_machine() {
        // Authority: es5-asyncFunctionIfStatements(target=es5)
        // ifStatement2 — a suspending consequent builds the labeled shape:
        // negated-test break to the else label, the consequent, a break to
        // the end label, the alternate under the else label with an
        // explicit end-label assignment, and the end label itself.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, z;\nasync function ifStatement2() {\n    if (x) { await y; } else { z; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(
            code.contains("case 2:\n                    z;\n                    _a.label = 3;\n                case 3: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_while_body_await_builds_loop_machine() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5)
        // whileStatement2 — a suspending loop body builds the labeled
        // shape: guard at the head, resume translating to a head jump,
        // exit label after.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y;\nasync function whileStatement2() {\n    while (x) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(
            code.contains("case 1:\n                    _a.sent();\n                    return [3 /*break*/, 0];\n                case 2: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_do_while_builds_positive_guard_machine() {
        // Authority: es5-asyncFunctionDoStatements(target=es5)
        // doStatement1 — the do-while guard is positive (loop-back is the
        // taken branch) and continue jumps to the test label, not the head.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y;\nasync function doStatement1() {\n    do { await x; } while (y);\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case 2:\n                    if (y) return [3 /*break*/, 0];\n                    _a.label = 3;\n                case 3: return [2 /*return*/];"),
            "{code}"
        );
    }

    #[test]
    fn es5_async_for_clause_await_builds_phase_labels() {
        // Authority: es5-asyncFunctionForStatements(target=es5)
        // forStatement2 — the test clause suspends: init marks the test
        // label, the guard resumes from the yield, the update loops back
        // to the test label, and continue targets the update label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, z, a;\nasync function forStatement2() {\n    for (x; await y; z) { a; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case 0:\n                    x;\n                    _a.label = 1;\n                case 1: return [4 /*yield*/, y];"),
            "{code}"
        );
        assert!(
            code.contains(
                "case 3:\n                    z;\n                    return [3 /*break*/, 1];"
            ),
            "{code}"
        );
    }

    #[test]
    fn es5_labeled_while_with_labeled_continue_lowers() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5)
        // whileStatement7 — a clean labeled loop with a labeled continue
        // still lowers to the machine; the leaked-await walker once
        // refused every labeled loop body, and no other pin covers it.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nasync function f() {\n    A: while (x) { continue A; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("A: while (x) {\n                continue A;\n            }\n            return [2 /*return*/];"),
            "{code}"
        );
        assert!(!code.contains("function*"), "{code}");
    }

    #[test]
    fn es5_async_switch_case_await_builds_dispatch_chain() {
        // Authority: es5-asyncFunctionSwitchStatements(target=es5)
        // switchStatement2 — a suspending case test yields, and its
        // resume opens a dispatch over the held discriminant comparing
        // the sent value, falling through to the default body's label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x, y, a, b;\nasync function switchStatement2() {\n    switch (x) { case await y: a; break; default: b; break; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(
            code.contains("case _b.sent(): return [3 /*break*/, 2];"),
            "{code}"
        );
        assert!(code.contains("return [3 /*break*/, 3];"), "{code}");
    }

    #[test]
    fn es5_async_arrow_with_this_keeps_the_arrow() {
        // Bodies referencing `this` need the hoisted-capture machinery, so
        // the conversion refuses and the arrow form stays.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x;\nvar foo = async () => {\n    await x;\n    this.y = 1;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("() => __awaiter(this"), "{code}");
        assert!(
            !code.contains("void 0, void 0, void 0, function () {\n    var"),
            "{code}"
        );
    }

    #[test]
    fn arrow_single_param_parens_follow_the_authored_form() {
        // Authority: complicatedIndexesOfIntersectionsAreInferencable keeps
        // `props => {`; arrowFunctionContexts keeps `(props) =>` and `() =>`.
        // The AST drops the distinction, so the token stream answers.
        let input = "var a = props => { return props; };
var b = (props) => { return props; };
var c = () => 1;
";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var a = props => {"), "{code}");
        assert!(code.contains("var b = (props) => {"), "{code}");
        assert!(code.contains("var c = () =>"), "{code}");
    }

    #[test]
    fn trailing_comment_attaches_to_the_last_statement_on_its_line() {
        // tsc attaches a trailing comment to the last statement on the
        // source line only: `var a = 1; var b = 2; // note` prints the
        // comment after `b`, never duplicated after `a`.
        let input = "var a = 1; var b = 2; // note\nvar c = 3;\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &EmitOptions::default());
        let code = &javascript(&output).code;
        assert!(code.contains("var a = 1;\n"), "{code}");
        assert!(code.contains("var b = 2; // note\n"), "{code}");
    }

    #[test]
    fn decorators_round_trip_through_javascript_emit() {
        let input = "@classFirst @classSecond class C {\n\
                     @constructorFirst @constructorSecond\n\
                     constructor(@constructorParameterFirst @constructorParameterSecond parameter) {}\n\
                     @methodFirst @methodSecond\n\
                     method(@methodParameterFirst @methodParameterSecond parameter) {}\n\
                     @propertyFirst @propertySecond\n\
                     property = 1;\n\
                     @accessorFirst @accessorSecond\n\
                     accessor value = 2;\n\
                     }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());

        let output = emit_output(parsed.product(), &EmitOptions::default());
        assert!(!output.has_errors());
        assert_eq!(
            javascript(&output).code,
            concat!(
                "@classFirst\n",
                "@classSecond\n",
                "class C {\n",
                "    @constructorFirst\n",
                "    @constructorSecond\n",
                "    constructor(@constructorParameterFirst @constructorParameterSecond parameter) { }\n",
                "    @methodFirst\n",
                "    @methodSecond\n",
                "    method(@methodParameterFirst @methodParameterSecond parameter) { }\n",
                "    @propertyFirst\n",
                "    @propertySecond\n",
                "    property = 1;\n",
                "    @accessorFirst\n",
                "    @accessorSecond\n",
                "    accessor value = 2;\n",
                "}\n",
            ),
        );

        let reparsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(javascript(&output).code.as_str())
                    .expect("test source fits the per-file budget"),
            ),
        ));
        assert!(reparsed.diagnostics().is_empty());
        let file = reparsed.product();
        let source = file.source_text();
        let decorator_texts = |decorators: &[DecoratorNode]| {
            decorators
                .iter()
                .map(|decorator| {
                    let range = decorator.range();
                    let start = source
                        .utf16_to_byte(range.start())
                        .expect("decorator range starts on a source boundary");
                    let end = source
                        .utf16_to_byte(range.end())
                        .expect("decorator range ends on a source boundary");
                    &source.as_str()[start..end]
                })
                .collect::<Vec<_>>()
        };

        let Statement::Class(class) = file.statements()[0].data() else {
            panic!("expected a class declaration");
        };
        assert_eq!(
            decorator_texts(&class.decorators),
            ["@classFirst", "@classSecond"]
        );

        let ClassMember::Constructor(constructor) = class.members[0].data() else {
            panic!("expected a constructor");
        };
        assert_eq!(
            decorator_texts(&constructor.decorators),
            ["@constructorFirst", "@constructorSecond"]
        );
        assert_eq!(
            decorator_texts(&constructor.parameters[0].data().decorators),
            ["@constructorParameterFirst", "@constructorParameterSecond"]
        );

        let ClassMember::Method(method) = class.members[1].data() else {
            panic!("expected a method");
        };
        assert_eq!(
            decorator_texts(&method.function.decorators),
            ["@methodFirst", "@methodSecond"]
        );
        assert_eq!(
            decorator_texts(&method.function.parameters[0].data().decorators),
            ["@methodParameterFirst", "@methodParameterSecond"]
        );

        let ClassMember::Property(property) = class.members[2].data() else {
            panic!("expected a property");
        };
        assert_eq!(
            decorator_texts(&property.decorators),
            ["@propertyFirst", "@propertySecond"]
        );

        let ClassMember::AutoAccessor(accessor) = class.members[3].data() else {
            panic!("expected an auto-accessor");
        };
        assert_eq!(
            decorator_texts(&accessor.decorators),
            ["@accessorFirst", "@accessorSecond"]
        );
    }

    #[test]
    fn pr199_for_of_assignment_targets_lower_to_indexed_loops() {
        let source = "var target = {}; for (target[2 ** 1] of source(2 ** 3)) { use(target); }";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("fits")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let statement = parsed.product().statements().last().expect("loop");
        let crate::syntax::Statement::ForOf(for_of) = statement.data() else {
            panic!("expected a for-of AST for {source}");
        };
        assert!(matches!(
            for_of.binding,
            crate::syntax::ForBinding::Target(_)
        ));
        let output = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(!code.contains(" of "), "native for-of survived ES5: {code}");
        assert_eq!(code.matches("Math.pow(2, 3)").count(), 1, "{code}");
        assert_eq!(code.matches("Math.pow(2, 1)").count(), 1, "{code}");
        assert!(!code.contains("**"), "{code}");
        let assign = code
            .find("target[Math.pow(2, 1)] = ")
            .expect("indexed assignment");
        let use_call = code.find("use(target)").expect("body");
        assert!(assign < use_call, "{code}");
    }

    fn pr199_emit_at(input: &str, target: ScriptTarget) -> EmitOutput {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("fits")),
        ));
        assert!(
            parsed.diagnostics().is_empty(),
            "{:?}",
            parsed.diagnostics()
        );
        emit_output(
            parsed.product(),
            &EmitOptions {
                target,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        )
    }

    #[test]
    fn pr199_native_declarations_emit_keys_in_declarator_order() {
        let source = "declare function before(): number; \
            declare function key(): string; \
            declare function between(): number; \
            declare function laterKey(): string; \
            declare function after(): number; \
            declare function finish(): void; \
            function* g() { \
                const left = before(), C = class { [yield key()]() {} }, \
                    middle = between(), D = class { [yield laterKey()]() {} }, \
                    right = after(); \
                finish(); return [left, C, middle, D, right]; \
            }";
        for target in [ScriptTarget::Es2015, ScriptTarget::Es2016] {
            let output = pr199_emit_at(source, target);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            let code = &javascript(&output).code;
            let positions = [
                "before()",
                "key()",
                "C =",
                "between()",
                "laterKey()",
                "D =",
                "after()",
                "finish()",
            ]
            .map(|needle| {
                assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
                code.find(needle).expect("one occurrence")
            });
            assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
        }
    }

    #[test]
    fn pr199_async_native_declarations_do_not_lose_key_awaits() {
        let source = "declare function before(): number; \
            declare function key(): string; declare function after(): number; \
            async function g() { \
                const left = before(), C = class { [await key()]() {} }, right = after(); \
                return [left, C, right]; \
            }";
        let output = pr199_emit_at(source, ScriptTarget::Es2015);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let code = &javascript(&output).code;
        let positions = ["before()", "key()", "C =", "after()"].map(|needle| {
            assert_eq!(code.matches(needle).count(), 1, "{needle}: {code}");
            code.find(needle).expect("one occurrence")
        });
        assert!(positions.windows(2).all(|pair| pair[0] < pair[1]), "{code}");
        assert!(
            code.contains("yield"),
            "await must survive as a suspension: {code}"
        );
        assert!(!code.contains("await key()"), "raw await leaked: {code}");
    }

    #[test]
    fn es5_async_for_update_increment_lowers() {
        // Synthetic probe pinning the walker/machine contract: a for-update
        // `i++` (Update over an Identifier) counts as zero resumes after the
        // walker fix, so a suspending for-loop still lowers normally with
        // the update emitted as plain machine code.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any, i: any;\nasync function f() {\n    for (; x; i++) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        let expected = "function f() {\n    return __awaiter(this, void 0, void 0, function () {\n        return __generator(this, function (_a) {\n            switch (_a.label) {\n                case 0: _a.label = 1;\n                case 1:\n                    if (!x) return [3 /*break*/, 4];\n                    return [4 /*yield*/, y];\n                case 2:\n                    _a.sent();\n                    _a.label = 3;\n                case 3:\n                    i++;\n                    return [3 /*break*/, 1];\n                case 4: return [2 /*return*/];\n            }\n        });\n    });\n}";
        assert!(code.contains(expected), "{code}");
        assert!(!code.contains("function*"), "{code}");
    }

    #[test]
    fn es5_generator_update_computed_key_refuses() {
        // Synthetic probe pinning the walker/machine contract: a while-test
        // computed-key yield (`o[yield k]++` inside the test) counts as a
        // resume, so the loop cannot stay inline; lowering routes to eval,
        // which refuses with GENERATOR_REQUIRES_ES2015, and the native
        // generator survives — never the inline machine clone.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input =
            "declare var o: any, k: any;\nfunction* g() {\n    while (o[yield k]++ < 3) { }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(code.contains("function* g("), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn es5_async_temp_collision_with_user_var() {
        // Authority: awaitBinaryExpression5_es5 / asyncFunctionDeclaration9 —
        // when a user variable collides with the machine's default temp name,
        // the machine state parameter is renamed to _b and the user's _a stays
        // the hoisted var.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input =
            "async function f(x: any) {\n    var _a = 1;\n    await x;\n    return _a;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function (_b)"), "{code}");
        assert!(code.contains("_b.label"), "{code}");
        assert!(code.contains("_b.sent()"), "{code}");
        assert!(code.contains("var _a;"), "{code}");
        assert!(code.contains("_a = 1;"), "{code}");
    }

    #[test]
    fn es5_async_leaked_await_refuses() {
        // Authority: es5-asyncFunction(target=es5) leaked await in left-hand
        // of property access assignment cannot be lowered, so the native
        // generator fallback is kept.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(a: any, b: any, c: any) {\n    (await a).b = c;\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* ()"), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(!code.contains(".sent()"), "{code}");
    }

    #[test]
    fn es5_async_binary_expression_await_materializes() {
        // Authority: awaitBinaryExpression5_es5(target=es5) — the awaited
        // operand is evaluated first, then combined with the saved left value
        // through `.sent()`.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "async function f(a: any, b: any) {\n    return a + (await b);\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function (_b)"), "{code}");
        assert!(code.contains("_b.label"), "{code}");
        assert!(code.contains("_a + (_b.sent())"), "{code}");
    }

    #[test]
    fn es5_async_switch_discriminant_await_inline() {
        // Return-bearing cases must not ride the discriminant-inline path:
        // cloning them verbatim embeds a raw `return 10` in the machine's
        // inner function, which drops the value through the protocol. Until
        // the rebuilt-cases path routes returns through machine_statements,
        // this shape refuses with the diagnostic — never a silent clone.
        let output = emit_es5_clean(
            "declare var x: any;\nasync function f() { switch (await x) { case 1: return 10; default: return 20; } }\n",
        );
        let code = &javascript(&output).code;
        assert!(
            !code.contains("__generator(this,"),
            "raw returns must not clone into the machine: {code}"
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
        // A return-free discriminant case still lowers inline.
        let lowered = emit_es5_clean(
            "declare var x: any;\nasync function f() { switch (await x) { case 1: r = 10; } }\n",
        );
        let code = &javascript(&lowered).code;
        assert!(code.contains("switch (_a.sent())"), "{code}");
    }

    #[test]
    fn es5_async_labeled_loop_with_await_and_break_lowers() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5) — a labeled
        // while body with an await and a labeled break lowers to the machine;
        // the break becomes an explicit branch to the exit label.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any;\nasync function f() {\n    A: while (x) { await y; break A; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(!code.contains("function*"), "{code}");
        assert!(
            code.contains("__awaiter(this, void 0, void 0, function ("),
            "{code}"
        );
        assert!(code.contains("if (!x) return [3 /*break*/, 2];"), "{code}");
        assert!(code.contains("_a.sent();"), "{code}");
        assert!(code.contains("return [3 /*break*/, 2];"), "{code}");
    }

    #[test]
    fn es5_async_identifier_assignment_test_stays_inline() {
        // Authority: es5-asyncFunctionWhileStatements(target=es5) — a while
        // test that only assigns to an identifier carries no resume, so the
        // whole test clones verbatim into the machine instead of routing the
        // loop through eval.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any, y: any;\nasync function f() {\n    while (x = 1) { await y; }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("if (!(x = 1))"), "{code}");
        assert_eq!(
            code.matches("return [4 /*yield*/, y];").count(),
            1,
            "{code}"
        );
        assert!(!code.contains("function*"), "{code}");
    }
    #[test]
    fn es5_generator_object_spread_yield_refuses() {
        // Contract pin, not a mutation claim: a while-test object spread
        // carrying a yield (`{ ...(yield x) }`) is refused upstream by the
        // machine's object-member wildcard, so the native generator survives
        // whether or not count_yields tracks the spread — this pins the
        // refusal shape: never the inline machine clone.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any;\nfunction* g() {\n    while ({ ...(yield x) }) { }\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* g("), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    #[test]
    fn es5_generator_array_spread_yield_never_clones() {
        // Mutation-provable: an array-literal spread carrying a yield
        // (`[...(yield x)]` as a statement) must never lower to the inline
        // machine — contains_yield_array reports the spread's yield, the
        // lowering bails, and the native generator survives with
        // GENERATOR_REQUIRES_ES2015. Reverting the Spread arm resurrects
        // `__generator(this, ...)` wrapping a live yield.
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            no_emit_helpers: true,
            ..EmitOptions::default()
        };
        let input = "declare var x: any;\nfunction* g() {\n    [...(yield x)];\n}\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(parsed.product(), &options);
        let code = &javascript(&output).code;
        assert!(code.contains("function* g("), "{code}");
        assert!(!code.contains("__generator(this,"), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "{:?}",
            output.diagnostics
        );
    }

    // ------------------------------------------------------------------
    // Adversarial hardening: the walker-duality contract as an invariant,
    // not a shape list. Assumptions under test (IDs cited per test):
    //   WD-1 duality: no emitted machine embeds a live yield outside a
    //       `return [4 /*yield*/, ...]` split (generic leak detector).
    //   WD-2 sentinel shapes (TaggedTemplate/Satisfies/TypeAssertion/JSX)
    //       are eval-refused, never inline-cloned.
    //   WD-3 count == segments eval mints: machine case labels are
    //       contiguous 0..=max and unique (gap detector; boundaries
    //       0/1/2/3 suspensions).
    //   WD-4 nested function-likes own their suspensions: cloning them
    //       is correct, their internal yield is legal.
    //   WD-5 non-block loop bodies refuse, never miscompile.
    //   WD-6/7 Import (source+options) and Conditional/Logical counts
    //       feed exact label arithmetic.
    //   WD-8 labeled-loop delegation covers nested awaited bodies.
    //   WD-9 recursive walkers survive deep nesting without crashing.
    // ------------------------------------------------------------------

    /// B4: destructuring defaults lower to tsc's ES5 shape - a temp
    /// read then a `=== void 0` ternary - never erasing the default.
    #[test]
    fn destructuring_defaults_lower_to_ternary_declarators() {
        let cases = [
            (
                "var o:any;\nvar { a = 1 } = o;\n",
                "var _t0 = o.a, a = _t0 === void 0 ? 1 : _t0;",
            ),
            (
                "var o:any;\nvar { p: q = 2 } = o;\n",
                "var _t0 = o.p, q = _t0 === void 0 ? 2 : _t0;",
            ),
            (
                "var o:any;\nvar { x: { y } = {} } = o;\n",
                "var _t0 = o.x, _t1 = _t0 === void 0 ? {} : _t0, y = _t1.y;",
            ),
            (
                "var arr:any;\nvar [c = 3, , [d = 4] = []] = arr;\n",
                "var _t0 = arr[0], c = _t0 === void 0 ? 3 : _t0, _t1 = arr[2], _t2 = _t1 === void 0 ? [] : _t1, _t3 = _t2[0], d = _t3 === void 0 ? 4 : _t3;",
            ),
        ];
        for (src, expected) in cases {
            let out = emit_es5_clean(src);
            let code = javascript(&out).code.clone();
            assert!(
                code.contains(expected),
                "missing tsc default shape `{expected}` in:\n{code}"
            );
        }
    }

    /// B4: a default's suspension survives lowering - the machine splits
    /// the default selection and no live yield leaks.
    #[test]
    fn destructuring_default_suspension_splits_the_machine() {
        let out =
            emit_es5_clean("var o:any, k:any;\nfunction* g(){ var { m = (yield k) } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("=== void 0"),
            "selection test missing:\n{code}"
        );
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "suspension missing:\n{code}"
        );
        assert!(code.contains("m = _t"), "final bind missing:\n{code}");
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// B4: an await default must not land in a ternary - eval refuses
    /// Conditional, so the __awaiter inner generator would stay native
    /// `function*` at ES5. The branch form keeps the inner machine.
    #[test]
    fn destructuring_default_await_keeps_the_inner_machine() {
        let out = emit_es5_clean(
            "var o:any, k:any;\nasync function h(){ var { n = await k } = o; return n; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(code.contains("__awaiter("), "async wrapper: {code}");
        assert!(
            code.contains("__generator(this,"),
            "inner machine lost - await landed in a ternary:\n{code}"
        );
        assert!(!code.contains("? yield"), "ternary yield:\n{code}");
    }

    /// B4 walker: a suspending for-init binding signals refusal with the
    /// requires-es2015 diagnostic rather than cloning silently.
    #[test]
    fn for_init_suspending_binding_signals_refusal() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(
                "var o:any, k:any;\nfunction* g(){ for (var { a = (yield k) } = o;;) { break; } }\n",
            )
            .expect("fits")),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.message().contains("generators require")),
            "refusal must be signalled"
        );
    }

    /// B1: a suspending computed class key hoists out of the class
    /// IIFE in statement contexts - the arrow is a plain function and
    /// tsc 6.0.2 itself emits a SyntaxError for the in-IIFE form. The
    /// machine splits the hoisted key temp and the arrow stays clean.
    #[test]
    fn class_computed_key_suspension_hoists_out_of_the_iife() {
        let out = emit_es5_clean(
            "var k:any;\nfunction* g(){ var C = class { [yield k]() {} }; return C; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "the key's suspension must split:\n{code}"
        );
        assert!(
            code.contains("_t1 = _a.sent()"),
            "the key temp binds from sent():\n{code}"
        );
        assert!(
            code.contains("[_t1]()"),
            "the member reads the hoisted temp:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// B1: expression-position class expressions cannot hoist (no
    /// enclosing statement drains key_prelude), so they keep tsc's
    /// in-IIFE shape but carry the requires-es2015 refusal instead of
    /// breaking silently.
    #[test]
    fn class_computed_key_in_expression_position_signals_refusal() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new("var k:any;\nfunction* h(){ foo(class { [yield k]() {} }); }\n")
                    .expect("fits"),
            ),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.message().contains("generators require")),
            "expression-position suspension must refuse loudly"
        );
    }

    /// B7: if-without-else is the empty else, not a refusal - both the
    /// inline clean clone and the suspending labeled shape must lower.
    #[test]
    fn if_without_else_lowers_in_the_machine() {
        let suspending =
            emit_es5_clean("var c:any, x:any;\nfunction* g(){ if (c) { yield x; } yield 2; }\n");
        let code = javascript(&suspending).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, x]"),
            "the branch suspension must split:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let clean =
            emit_es5_clean("var c:any, x:any;\nfunction* g(){ yield 1; if (c) { x = 1; } }\n");
        let code = javascript(&clean).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(code.contains("if (c)"), "clean if clones inline:\n{code}");
    }

    /// Bot-round B4 gaps: the suspending-declaration path must keep
    /// sibling identifier declarators, declare computed-key temps,
    /// bind array rest, exclude computed keys from object rest with
    /// tsc's runtime coercion, and rewrite awaited sources so the
    /// __awaiter inner generator still machine-converts.
    #[test]
    fn suspending_declarations_keep_sibling_and_rest_semantics() {
        let out = emit_es5_clean(
            "var y:any, obj:any;\nfunction* g(){ var x = 5, { a = (yield y) } = obj; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("x = 5"),
            "sibling declarator dropped:\n{code}"
        );
        let out = emit_es5_clean(
            "var k:any, arr:any;\nfunction* g(){ var [a = (yield k), ...r] = arr; }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("r = arr.slice(1)"),
            "array rest discarded:\n{code}"
        );
        let out =
            emit_es5_clean("var k:any, o:any;\nfunction* g(){ var { [k]: v, ...rest } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("typeof _t0 === \"symbol\" ? _t0 : _t0 + \"\""),
            "computed key must be excluded at runtime (tsc shape):\n{code}"
        );
        let out = emit_es5_clean("var k:any, o:any;\nfunction* g(){ var { [yield k]: v } = o; }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("var v, _t0, _t1"), "temps declared:\n{code}");
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let out = emit_es5_clean("var k:any;\nasync function h(){ var { a } = await k; }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("__generator(this,"),
            "awaited source must rewrite so the inner machine converts:\n{code}"
        );
    }

    /// B1 order: computed keys evaluate in member order, so hoisting
    /// must move the whole prelude - partitioning suspending keys away
    /// from clean ones reorders evaluation.
    #[test]
    fn class_computed_keys_evaluate_in_member_order() {
        let out = emit_es5_clean(
            "var k1:any, k2:any;\nfunction* g(){ var C = class { [k1()](){} [yield k2()](){} }; }\n",
        );
        let code = javascript(&out).code.clone();
        let clean_first = code.find("k1()").expect("clean key evaluated");
        let suspending = code.find("k2()").expect("suspending key evaluated");
        assert!(
            clean_first < suspending,
            "member order must survive hoisting:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
        let out = emit_es5_clean(
            "var k1:any, k2:any;\nfunction* g(){ var C = class { [yield k1()](){} [k2()](){} }; }\n",
        );
        let code = javascript(&out).code.clone();
        let suspending = code.find("k1()").expect("suspending key evaluated");
        let clean_second = code.find("k2()").expect("clean key evaluated");
        assert!(
            suspending < clean_second,
            "member order must survive hoisting (suspending first):\n{code}"
        );
    }

    /// B1 visibility: an await inside a class computed key or heritage
    /// clause in expression position cannot lower - there is no hoist
    /// channel - and must refuse the generator natively under the
    /// requires-es2015 diagnostic, never bury the raw await inside a
    /// synthesized arrow the machine cannot see through.
    #[test]
    fn class_expression_awaits_refuse_natively() {
        for src in [
            "var k:any;\nasync function h(){ foo(class { [await k](){} }); }\n",
            "var f:any;\nasync function h(){ return class extends (await f()) {}; }\n",
        ] {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(src).expect("fits")),
            ));
            let out = emit_output(
                parsed.product(),
                &EmitOptions {
                    target: ScriptTarget::Es5,
                    no_emit_helpers: true,
                    ..EmitOptions::default()
                },
            );
            let code = javascript(&out).code.clone();
            assert!(
                !code.contains("__generator(this,"),
                "machine must refuse: {src}\n{code}"
            );
            assert!(
                out.diagnostics
                    .iter()
                    .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
                "refusal must be signalled: {src}"
            );
        }
    }

    /// A suspending static-field initializer (postlude) refuses the
    /// same way a key prelude does: the unlowered class keeps the
    /// suspension visible and the generator stays native under the
    /// signal - never a live yield inside the synthesized arrow.
    #[test]
    fn class_static_field_suspension_refuses_natively() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new(
                    "var k:any;\nfunction* g(){ var C = class { static x = yield k; }; }\n",
                )
                .expect("fits"),
            ),
        ));
        let out = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = javascript(&out).code.clone();
        assert!(
            !code.contains("__generator(this,"),
            "machine must refuse the static-field suspension:\n{code}"
        );
        assert!(
            out.diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must be signalled"
        );
    }

    /// A for-of body suspending in a generator machine-splits through
    /// the lowered classic loop - the ladder's machine slice composing
    /// with the plain lowering.
    #[test]
    fn for_of_suspension_machine_splits_through_the_lowered_loop() {
        let out =
            emit_es5_clean("var it:any;\nfunction* g(){ for (const k of it) { yield k; } }\n");
        let code = javascript(&out).code.clone();
        assert!(code.contains("__generator(this,"), "machine form: {code}");
        assert!(
            code.contains("[4 /*yield*/, k]"),
            "the body's suspension must split:\n{code}"
        );
        assert!(
            code.contains("_t1[_t0]"),
            "the binding reads the indexed element:\n{code}"
        );
        assert!(live_yield_leak(&code).is_none(), "live yield leaked");
    }

    /// A braceless for-of body is one statement, not a missing one:
    /// the emitted loop must still contain it.
    #[test]
    fn braceless_for_of_body_survives_lowering() {
        let out =
            emit_es5_clean("var arr:any;\nfunction f(){ for (const k of arr) console.log(k); }\n");
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("console.log(k)"),
            "the braceless body statement must survive:\n{code}"
        );
    }

    /// A destructuring binding in a for-of head composes with the
    /// destructuring lowering: the element read becomes the binding's
    /// initializer inside the loop body.
    #[test]
    fn for_of_pattern_binding_composes_with_destructuring() {
        let out = emit_es5_clean(
            "var arr:any;\nfor (const { a, b = 2 } of arr) { console.log(a + b); }\n",
        );
        let code = javascript(&out).code.clone();
        assert!(
            code.contains("void 0 ? 2 :"),
            "the binding default must lower inside the loop:\n{code}"
        );
        assert!(
            code.contains(".a"),
            "the member read must bind from the element:\n{code}"
        );
    }

    /// Emits `input` at es5 without helpers; panics on parse diagnostics.
    fn emit_es5_clean(input: &str) -> EmitOutput {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(input).expect("test source fits the per-file budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        )
    }

    /// WD-1: in machine form, every `yield` must sit inside a split marker
    /// `/*yield*/`; a bare yield is a live suspension cloned into a plain
    /// function (the miscompile class). Returns the offending snippet text.
    fn live_yield_leak(code: &str) -> Option<String> {
        if !code.contains("__generator(this,") {
            return None; // native refusal form: the generator owns its yields
        }
        code.lines()
            // Strip the protocol marker spans first: a line can carry both a
            // legitimate `return [4 /*yield*/, x]` split and a cloned live
            // yield; the marker must not exempt the whole line.
            .find(|line| {
                let stripped = line.replace("/*yield*/", "");
                // The match must end as a token: `yielding` is an
                // identifier, not the keyword.
                stripped.match_indices("yield").any(|(i, _)| {
                    stripped[i + 5..]
                        .chars()
                        .next()
                        .is_none_or(|c| !(c.is_alphanumeric() || c == '_' || c == '$'))
                })
            })
            .map(|line| line.trim().to_owned())
    }

    /// WD-1b: in machine form, every return must be a protocol return
    /// (`return [`) — a bare `return expr;` in the machine body exits the
    /// inner function directly and the runtime silently drops the value.
    /// Battery-scoped: snippets are flat (no nested function bodies, whose
    /// returns are legal); the nested-ownership contract has its own pin.
    fn raw_return_leak(code: &str) -> Option<String> {
        if !code.contains("__generator(this,") {
            return None;
        }
        code.lines()
            .find(|line| {
                let l = line.trim();
                // `return` must end as a token: `returning = 1;` is a
                // plain assignment, not a protocol-breaking return.
                let boundary = !l.starts_with("return")
                    || l[6..]
                        .chars()
                        .next()
                        .is_none_or(|c| c.is_whitespace() || c == ';' || c == '}' || c == '(');
                l.starts_with("return")
                    && boundary
                    && !l.starts_with("return [")
                    && !l.starts_with("return __generator")
                    && !l.starts_with("return __awaiter")
                    && l.ends_with(';')
            })
            .map(|line| line.trim().to_owned())
    }

    /// WD-3: the machine switch's case labels must be unique and contiguous
    /// from 0 (a gap or duplicate means count_yields disagreed with the
    /// segments eval actually minted).
    fn machine_case_labels(code: &str) -> Vec<u32> {
        // Any state parameter (_a, or _b after a temp collision); raw
        // labels with no dedup — the caller's equality assert fails on a
        // duplicate, which is the failure this helper guards.
        let start = code
            .match_indices("switch (_")
            .map(|(i, _)| i)
            .find(|&i| code[i..].contains(".label)"))
            .expect("machine switch");
        let body = &code[start..];
        let mut labels: Vec<u32> = body
            .split("case ")
            .skip(1)
            .filter_map(|rest| rest.split(':').next())
            .filter_map(|n| n.parse().ok())
            .collect();
        labels.sort_unstable();
        labels
    }

    #[test]
    fn es5_async_return_in_loop_body_never_drops_value() {
        // A cloned `return y` inside the machine body returns straight out
        // of the inner function; the runtime treats the non-array as done
        // with `void 0` — the value is silently dropped. The loop body
        // cannot lower a return, so the machine must refuse (until a
        // return-protocol slice lands), never clone.
        let output = emit_es5_clean(
            "declare var x: any, y: any;\nasync function f() { while (x) { return y; } }\n",
        );
        let code = &javascript(&output).code;
        assert!(
            !code.contains("__generator(this,"),
            "machine must not embed a raw return: {code}"
        );
        assert!(code.contains("return y;"), "value preserved: {code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
    }

    #[test]
    fn walker_duality_battery_never_clones_live_yield() {
        // WD-1: each snippet puts a suspending shape behind each clone gate,
        // with its derived expectation: `true` lowers to the machine (and
        // must not leak), `false` refuses (native form + the requires-es2015
        // diagnostic + no machine). Expectations were derived from emitted
        // output; all-refusing output fails every `true` row.
        let snippets: [(&str, &str, bool); 31] = [
            (
                "update-computed-while",
                "declare var o: any, k: any;\nfunction* g() { while (o[k ? k : 0][`x`], o[yield k]++ < 3) { } }\n",
                false,
            ),
            (
                "array-spread-statement",
                "declare var x: any;\nfunction* g() { [...(yield x)]; }\n",
                false,
            ),
            (
                "array-spread-while-body",
                "declare var x: any, y: any;\nfunction* g() { while (y) { [...(yield x)]; } }\n",
                false,
            ),
            (
                "object-spread-do-test",
                "declare var x: any;\nfunction* g() { do { } while ({ ...(yield x) }); }\n",
                false,
            ),
            (
                "assignment-pattern-while",
                "declare var x: any, y: any;\nfunction* g() { while ({ a: x } = y) { yield x; } }\n",
                false,
            ),
            (
                "template-expr-statement",
                "declare var x: any;\nfunction* g() { `${yield x}`; }\n",
                true,
            ),
            (
                "conditional-expr-statement",
                "declare var x: any, y: any;\nfunction* g() { return (yield x) ? y : (yield x); }\n",
                false,
            ),
            (
                "logical-expr-statement",
                "declare var x: any, y: any;\nfunction* g() { return (yield x) || (yield y); }\n",
                false,
            ),
            (
                "import-expr-machine",
                "declare var x: any;\nfunction* g() { return import(yield x); }\n",
                true,
            ),
            (
                "new-suspending-args",
                "declare var x: any;\nfunction* g() { return new C(yield x); }\n",
                false,
            ),
            (
                "nested-if-await-while",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { if (y) { await z; } } }\n",
                false,
            ),
            (
                "nested-if-await-labeled",
                "declare var x: any, y: any, z: any;\nasync function f() { A: while (x) { if (y) { await z; break A; } } }\n",
                false,
            ),
            (
                "nested-if-await-do",
                "declare var x: any, y: any, z: any;\nasync function f() { do { if (y) { await z; } } while (x); }\n",
                false,
            ),
            (
                "nested-if-await-if-arm",
                "declare var x: any, y: any, z: any;\nasync function f() { if (x) { if (y) { await z; } } }\n",
                false,
            ),
            (
                "return-in-while-body",
                "declare var x: any, y: any;\nasync function f() { while (x) { return y; } }\n",
                false,
            ),
            (
                "return-in-labeled-body",
                "declare var x: any, y: any;\nasync function f() { A: while (x) { return y; } }\n",
                false,
            ),
            (
                "return-in-if-branch",
                "declare var y: any, z: any;\nasync function f() { if (y) { return z; } }\n",
                false,
            ),
            (
                "clean-nested-while-clones",
                "declare var x: any, z: any;\nasync function f() { while (x) { while (z) { } } }\n",
                true,
            ),
            (
                "call-spread-arg",
                "declare var f: any, x: any;\nfunction* g() { f(...(yield x)); }\n",
                false,
            ),
            (
                "method-computed-name",
                "declare var k: any;\nfunction* g() { ({ [yield k]() {} }); }\n",
                false,
            ),
            (
                "nonblock-nested-return",
                "declare var x: any, z: any;\nasync function f() { while (x) { while (z) return z; } }\n",
                false,
            ),
            (
                "as-cast-lowers",
                "declare var k: any;\nfunction* g() { while ((yield k) as any) { } }\n",
                true,
            ),
            (
                "call-spread-while-test",
                "declare var f: any, x: any;\nfunction* g() { while (f(...(yield x)) < 3) { } }\n",
                false,
            ),
            (
                "method-computed-while-test",
                "declare var k: any;\nfunction* g() { while ({ [yield k]() {} }) { } }\n",
                false,
            ),
            (
                "yield-nested-lowers-with-exact-labels",
                "declare var a: any;\nfunction* g() { while (yield (yield a)) {} }\n",
                true,
            ),
            (
                "for-var-init-yield-splits",
                "declare var x: any, c: any;\nfunction* g() { for (var x = yield 1; c;) {} }\n",
                true,
            ),
            (
                "switch-case-return-refuses",
                "declare var x: any, y: any;\nfunction* g() { while (y) { switch (x) { case 1: return 42; } } }\n",
                false,
            ),
            (
                "switch-multi-yield-case-test",
                "declare var d: any, a: any, b: any, x: any;\nfunction* g() { switch (d) { case (yield a) + (yield b): x = 1; break; default: x = 2; } }\n",
                true,
            ),
            (
                "computed-key-temps-are-var-at-es5",
                "declare var x: any, k: any, o: any;\nfunction* g() { while (x) { var { [k]: v } = o; } }\n",
                true,
            ),
            ("bare-yield-lowers", "function* g() { yield; }\n", true),
            (
                "async-arrow-refusal-signals",
                "declare var x: any, y: any, z: any;\nvar f = async () => { while (x) { if (y) { await z; } } };\n",
                false,
            ),
        ];
        for (name, input, lowers) in snippets {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            let machine = code.contains("__generator(this,");
            let native = code.contains("function*");
            let diag = output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015);
            assert_eq!(
                machine, lowers,
                "[{name}] expected lower={lowers}: machine={machine} native={native}\n{code}"
            );
            if let Some(leak) = live_yield_leak(code) {
                panic!("[{name}] live yield cloned into machine: {leak}");
            }
            if let Some(leak) = raw_return_leak(code) {
                panic!("[{name}] raw return in machine body drops value: {leak}");
            }
            if !lowers {
                assert!(native, "[{name}] refusal must keep the native form\n{code}");
                assert!(diag, "[{name}] refusal must signal TS-EMIT-1102\n{code}");
            }
        }
    }

    #[test]
    fn sentinel_shapes_route_to_refusal_not_clone() {
        // WD-2: eval has no accepting arms for these shapes; the sentinel
        // count must send them there, never through the inline clone gate.
        for (name, input) in [
            (
                "tagged-template",
                "declare var tag: any, k: any;\nfunction* g() { while (tag`x ${yield k}`) { } }\n",
            ),
            (
                "type-assertion",
                "declare var k: any;\nfunction* g() { while (<any>(yield k)) { } }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            assert!(
                code.contains("function* g(")
                    && output
                        .diagnostics
                        .iter()
                        .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
                "[{name}] sentinel shape must refuse with the native form + diagnostic:\n{code}"
            );
        }
        // JSX expressions need TypeScriptReact parsing; the same sentinel
        // contract applies: refuse or lower, never a cloned live yield.
        let jsx_input = "declare var k: any;\nfunction* g() { while (<div>{yield k}</div>) { } }\n";
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScriptReact,
            Arc::new(SourceText::new(jsx_input).expect("fits budget")),
        ));
        assert!(parsed.diagnostics().is_empty());
        let output = emit_output(
            parsed.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(
            code.contains("function* g(") || live_yield_leak(code).is_none(),
            "jsx row must refuse or lower safely, got:\n{code}"
        );
    }

    #[test]
    fn machine_case_labels_are_contiguous_and_unique() {
        // WD-3 + WD-6 + WD-7, boundaries 0/1/2/3 suspensions on both sides
        // of every count.
        for (name, input) in [
            (
                "zero",
                "declare var x: any;\nasync function f() { while (x) { } }\n",
            ),
            (
                "one",
                "declare var x: any, y: any;\nasync function f() { while (x) { await y; } }\n",
            ),
            (
                "two",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { await y; await z; } }\n",
            ),
            (
                "three-test-split",
                "declare var o: any, k: any, y: any;\nasync function f() { while (o[await k]++ < 3) { await y; } }\n",
            ),
            (
                "import-two-suspensions",
                "declare var a: any, b: any;\nasync function f() { return import(await a, { m: await b }); }\n",
            ),
            (
                "conditional-three",
                "declare var a: any, b: any, c: any;\nasync function f() { return (await a) ? await b : await c; }\n",
            ),
            (
                "nested-yield-labels",
                "declare var a: any;\nfunction* g() { while (yield (yield a)) {} }\n",
            ),
            (
                "for-var-init-split-labels",
                "declare var x: any, c: any;\nfunction* g() { for (var x = yield 1; yield c;) { yield x; } }\n",
            ),
            (
                "jump-guard-exact-count",
                "declare var x: any, y: any, z: any;\nasync function f() { while (x) { if (y) continue; await z; } }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            let machine_switch = code
                .match_indices("switch (_")
                .map(|(i, _)| i)
                .find(|&i| code[i..].contains(".label)"));
            if machine_switch.is_none() {
                if !code.contains("__generator(this,") {
                    // Not lowered at all: the only honest alternative is a
                    // signalled refusal — a silent skip would hide a
                    // lowering regression.
                    assert!(
                        code.contains("function*")
                            && output.diagnostics.iter().any(|d| {
                                d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015
                            }),
                        "[{name}] neither machine nor signalled refusal:\n{code}"
                    );
                }
                // A degenerate zero-resume machine needs no dispatch
                // switch; there are no labels to check.
                continue;
            }
            let labels = machine_case_labels(code);
            assert!(!labels.is_empty(), "[{name}] machine without labels");
            let expected: Vec<u32> = (0..=*labels.last().expect("non-empty")).collect();
            assert_eq!(
                labels, expected,
                "[{name}] case labels must be contiguous: {code}"
            );
        }
    }

    #[test]
    fn nested_function_likes_own_suspensions_when_cloned() {
        // WD-4: a method member owns its yields, so the object clones as
        // clean into the machine and the INTERNAL yield stays legal.
        // The method body holds a real suspension: ownership means the
        // machine lowers with exactly one resume (the await) and the
        // method's yield survives verbatim inside the cloned object —
        // a walker that wrongly descended into the body would mint a
        // second resume or refuse outright.
        let output = emit_es5_clean(
            "declare var x: any;\nasync function f() {\n    while ({ *m() { yield 1; } }) { await x; }\n}\n",
        );
        let code = &javascript(&output).code;
        assert!(code.contains("__generator(this,"), "lowers: {code}");
        assert!(
            code.contains("*m() {"),
            "generator method cloned intact: {code}"
        );
        assert!(code.contains("yield 1;"), "method owns its yield: {code}");
        assert_eq!(
            code.matches(".sent()").count(),
            1,
            "one machine resume: {code}"
        );
        assert!(
            !code.contains("function* ("),
            "inner function not native: {code}"
        );
    }

    #[test]
    fn non_block_loop_bodies_refuse() {
        // WD-5: single-statement bodies are outside the accepted set; the
        // only valid outcomes are refusal with a diagnostic.
        for (name, input) in [
            (
                "while",
                "declare var x: any, y: any;\nasync function f() { while (x) await y; }\n",
            ),
            (
                "for",
                "declare var x: any, y: any;\nasync function f() { for (; x;) await y; }\n",
            ),
            (
                "do",
                "declare var x: any, y: any;\nasync function f() { do await y; while (x); }\n",
            ),
        ] {
            let output = emit_es5_clean(input);
            let code = &javascript(&output).code;
            assert!(
                !code.contains("__generator(this,")
                    && code.contains("function*")
                    && output
                        .diagnostics
                        .iter()
                        .any(|d| { d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015 }),
                "[{name}] non-block body must refuse with the diagnostic, never lower or clone: {code}"
            );
        }
    }

    #[test]
    fn labeled_nested_await_delegation_refuses_until_nested_if_slice() {
        // WD-8: branch_awaits delegates through nested statement shapes.
        let output = emit_es5_clean(
            "declare var x: any, y: any, z: any;\nasync function f() {\n    A: while (x) { if (y) { await z; break A; } }\n}\n",
        );
        let code = &javascript(&output).code;
        // Safety contract: refuse-or-lower, never a live await cloned
        // outside the generator that owns it. (Full lowering of nested
        // control flow inside labeled loop bodies is a banked machine
        // slice; until then the refusal form is the correct output.)
        assert!(
            code.contains("function*") || code.contains("__generator(this,"),
            "must refuse or lower: {code}"
        );
        assert!(live_yield_leak(code).is_none(), "{code}");
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.code() == transforms::codes::GENERATOR_REQUIRES_ES2015),
            "refusal must signal: {:?}",
            output.diagnostics
        );
    }

    #[test]
    fn deep_nesting_walkers_do_not_crash() {
        // WD-9: the parser's nesting bound (MAX_DEPTH = 256) is the
        // boundary, tested from both sides. Below it the fixture parses
        // clean and the recursive walkers emit some form; above it the
        // parser declines with the descriptive P010 diagnostic — never a
        // crash, never a silent skip. (A `-` chain lexes as `--` decrement
        // pairs and never parses; parens give real expression depth.)
        let fixture = |depth: usize| {
            format!(
                "declare var y: any;\nasync function f() {{ {}await y{}; }}\n",
                "(".repeat(depth),
                ")".repeat(depth)
            )
        };
        let parse = |input: String| {
            crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(input.as_str()).expect("fits budget")),
            ))
        };
        let below = parse(fixture(56));
        assert!(
            below.diagnostics().is_empty(),
            "depth 56 must parse clean: {:?}",
            below.diagnostics()
        );
        let output = emit_output(
            below.product(),
            &EmitOptions {
                target: ScriptTarget::Es5,
                no_emit_helpers: true,
                ..EmitOptions::default()
            },
        );
        let code = &javascript(&output).code;
        assert!(
            code.contains("__generator(this,") || code.contains("function*"),
            "some emitted form at depth 56: {code}"
        );
        let above = parse(fixture(400));
        assert!(
            !above.diagnostics().is_empty(),
            "depth 400 must be rejected, not accepted"
        );
        assert!(
            above
                .diagnostics()
                .iter()
                .any(|d| d.code().as_str().contains("P010")),
            "rejection must be the descriptive nesting-bound diagnostic: {:?}",
            above.diagnostics()
        );
    }

    #[test]
    fn es5_generator_import_source_materializes_before_options_yield() {
        // A clean source operand with side effects must run before the
        // options suspend: materialize into a temp in the pre-suspension
        // segment, never reassemble it inside the resume where its effects
        // would slip past the suspension.
        let output = emit_es5_clean(
            "declare var f: any, b: any;\nfunction* g() { return import(f(), { m: yield b }); }\n",
        );
        let code = &javascript(&output).code;
        let case0 = code
            .split("case 0:")
            .nth(1)
            .and_then(|rest| rest.split("case 1:").next())
            .expect("two segments");
        let source_pos = case0.find("_a = f();").expect("source temp");
        let yield_pos = case0.find("/*yield*/").expect("split marker");
        assert!(
            source_pos < yield_pos,
            "source materializes before the yield: {code}"
        );
        assert!(
            code.contains("import(_a,"),
            "resume reassembles from the temp: {code}"
        );
    }

    #[test]
    fn es5_async_nested_async_arrow_keeps_its_awaits() {
        // A nested async arrow owns its awaits: the outer function's
        // await-to-yield rewrite must stop at the nested body, and the
        // nested arrow keeps its own `await` for its own lowering pass.
        // (Await inside a NON-async function is invalid input the parser
        // does not yet reject — banked as a checker slice.)
        let output = emit_es5_clean(
            "declare var k: any;\nasync function f() { var g = async () => { return await k; }; }\n",
        );
        let code = &javascript(&output).code;
        // The nested arrow lowers itself: its own __awaiter machine with
        // the await in protocol form ([4 /*yield*/, k]) — no live yield.
        assert_eq!(
            code.matches("__awaiter").count(),
            2,
            "both the outer function and the nested arrow lower: {code}"
        );
        assert!(code.contains("/*yield*/, k"), "protocol form: {code}");
        assert!(live_yield_leak(code).is_none(), "{code}");
    }

    #[test]
    fn machine_state_name_terminates_past_the_alphabet() {
        // Declaring _a.._z plus _state exhausted the old allocator's fixed
        // fallback and hung compilation forever. A regression must fail
        // this test, not wedge the runner, so the emit runs on a thread
        // with a hard timeout.
        // The skip set is built from BODY statements, so the alphabet must
        // be declared inside the generator, not as ambient `declare var`.
        let input = "function* g() { var _a, _b, _c, _d, _e, _f, _g, _h, _i, _j, _k, _l, _m, _n, _o, _p, _q, _r, _s, _t, _u, _v, _w, _x, _y, _z, _state; yield 1; }\n";
        let (tx, rx) = std::sync::mpsc::channel();
        let parsed_input = input.to_owned();
        std::thread::spawn(move || {
            let parsed = crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(SourceText::new(parsed_input.as_str()).expect("fits budget")),
            ));
            let output = emit_output(
                parsed.product(),
                &EmitOptions {
                    target: ScriptTarget::Es5,
                    no_emit_helpers: true,
                    ..EmitOptions::default()
                },
            );
            let _ = tx.send(javascript(&output).code.clone());
        });
        let code = rx
            .recv_timeout(std::time::Duration::from_secs(10))
            .expect("allocator must terminate past the alphabet");
        assert!(code.contains("__generator(this,"), "{code}");
    }
}
