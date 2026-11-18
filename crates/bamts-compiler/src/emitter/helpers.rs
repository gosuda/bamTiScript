//! Import-helpers / tslib policy for emit.
//!
//! The existing printer emits helper *calls* (`__awaiter`, `__rest`, …) when a
//! transform has requested them. This module decides, deterministically, which
//! helper texts are included and whether they are inlined or imported from
//! `tslib`. Request order never affects output: helpers are expanded through a
//! fixed dependency graph and emitted in [`HelperKind`] discriminant order.
//!
//! # Guarantees
//! * **At most once.** A helper appears in the prelude at most once even when
//!   requested repeatedly or pulled in as a dependency of several others.
//! * **Stable order.** `[B, A]` and `[A, B]` produce byte-identical preludes.
//! * **Closed catalog.** Unknown helpers cannot be manufactured at runtime; the
//!   [`HelperKind`] enum is the whole set.
//! * **Exact semantics.** Helpers whose contract is stronger than the external
//!   provider stay inline even when `importHelpers` is enabled.
//! * **Negative paths.** Importing helpers into a non-module file under ESM
//!   style, or requesting a helper the catalog cannot satisfy, yields a typed
//!   [`Diagnostic`] rather than silent fallback.

use std::collections::BTreeSet;

use crate::diagnostic::Diagnostic;
use crate::source::{SourceId, TextRange, Utf16Pos};
use crate::syntax::SourceFile;

/// Stable diagnostic identifiers produced by helper policy.
pub mod codes {
    use crate::diagnostic::DiagnosticCode;

    /// `importHelpers` with ESM style requires the file to be an external module.
    pub const IMPORT_HELPERS_REQUIRES_MODULE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1401");
    /// A helper was requested that this catalog does not define.
    pub const UNKNOWN_HELPER: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1402");
}

/// How helper references are bound in the generated file.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HelperStyle {
    /// Emit each helper as a local `function` declaration.
    Inline,
    /// `import { __helper } from "tslib"`.
    EsModule,
    /// `var __helper = require("tslib").__helper;`.
    CommonJs,
}

/// Immutable helper-emit options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HelperOptions {
    /// When true, bind helpers from [`HelperOptions::module_specifier`] instead
    /// of inlining their bodies.
    pub import_helpers: bool,
    /// Assume inline helpers exist globally; emit no inline helper definitions
    /// (`noEmitHelpers`). External imports still emit when `import_helpers`
    /// is enabled.
    pub no_emit_helpers: bool,
    pub style: HelperStyle,
    /// The module specifier used for imported helpers. Defaults to `tslib`.
    pub module_specifier: String,
}

impl Default for HelperOptions {
    fn default() -> Self {
        Self {
            import_helpers: false,
            no_emit_helpers: false,
            style: HelperStyle::Inline,
            module_specifier: String::from("tslib"),
        }
    }
}

impl HelperOptions {
    /// Inline helpers with the default `tslib` specifier unused.
    #[must_use]
    pub fn inline() -> Self {
        Self::default()
    }

    /// Import helpers as ESM named bindings from `tslib`.
    #[must_use]
    pub fn es_module() -> Self {
        Self {
            import_helpers: true,
            no_emit_helpers: false,
            style: HelperStyle::EsModule,
            module_specifier: String::from("tslib"),
        }
    }

    /// Import helpers as CommonJS `require` bindings from `tslib`.
    #[must_use]
    pub fn common_js() -> Self {
        Self {
            import_helpers: true,
            no_emit_helpers: false,
            style: HelperStyle::CommonJs,
            module_specifier: String::from("tslib"),
        }
    }

    /// Returns a copy that binds helpers from `module_specifier`.
    #[must_use]
    pub fn with_module_specifier(mut self, module_specifier: impl Into<String>) -> Self {
        self.module_specifier = module_specifier.into();
        self
    }
}

/// One emit helper. Discriminant order is the emit order, which follows the
/// order tsc 7.0.2 prints helpers in its baselines: no baseline puts a later
/// variant before an earlier one that it also contains.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HelperKind {
    Extends,
    CreateBinding,
    Assign,
    SetModuleDefault,
    Decorate,
    ExportStar,
    ImportStar,
    Metadata,
    Param,
    Awaiter,
    Generator,
    AddDisposableResource,
    DisposeResources,
    ImportDefault,
    ClassPrivateFieldGet,
    ClassPrivateFieldSet,
    ClassPrivateFieldIn,
    Rest,
    Values,
    Read,
    SpreadArray,
    PropKey,
}

impl HelperKind {
    /// Returns every helper this catalog defines, in emit order.
    #[must_use]
    pub const fn all() -> &'static [Self] {
        &[
            Self::Extends,
            Self::CreateBinding,
            Self::Assign,
            Self::SetModuleDefault,
            Self::Decorate,
            Self::ExportStar,
            Self::ImportStar,
            Self::Metadata,
            Self::Param,
            Self::Awaiter,
            Self::Generator,
            Self::AddDisposableResource,
            Self::DisposeResources,
            Self::ImportDefault,
            Self::ClassPrivateFieldGet,
            Self::ClassPrivateFieldSet,
            Self::ClassPrivateFieldIn,
            Self::Rest,
            Self::Values,
            Self::Read,
            Self::SpreadArray,
            Self::PropKey,
        ]
    }

    /// Returns the runtime identifier (`__awaiter`, …).
    #[must_use]
    pub const fn ident(self) -> &'static str {
        match self {
            Self::Extends => "__extends",
            Self::Assign => "__assign",
            Self::Rest => "__rest",
            Self::Decorate => "__decorate",
            Self::Param => "__param",
            Self::Metadata => "__metadata",
            Self::Awaiter => "__awaiter",
            Self::Generator => "__generator",
            Self::AddDisposableResource => "__addDisposableResource",
            Self::DisposeResources => "__disposeResources",
            Self::ExportStar => "__exportStar",
            Self::CreateBinding => "__createBinding",
            Self::SetModuleDefault => "__setModuleDefault",
            Self::Values => "__values",
            Self::Read => "__read",
            Self::SpreadArray => "__spreadArray",
            Self::ImportStar => "__importStar",
            Self::ImportDefault => "__importDefault",
            Self::ClassPrivateFieldGet => "__classPrivateFieldGet",
            Self::ClassPrivateFieldSet => "__classPrivateFieldSet",
            Self::ClassPrivateFieldIn => "__classPrivateFieldIn",
            Self::PropKey => "__propKey",
        }
    }

    /// Returns helpers that must appear before this one.
    #[must_use]
    pub const fn dependencies(self) -> &'static [Self] {
        match self {
            Self::Awaiter => &[],
            Self::ExportStar => &[Self::CreateBinding],
            Self::ImportStar => &[Self::CreateBinding, Self::SetModuleDefault],
            _ => &[],
        }
    }

    /// Returns whether the configured external provider satisfies this helper's contract.
    #[must_use]
    pub const fn can_import(self) -> bool {
        !matches!(self, Self::PropKey)
    }

    /// Returns the inlined `function` declaration, including a trailing newline.
    #[must_use]
    pub const fn inline_source(self) -> &'static str {
        match self {
            Self::Extends => include_str!("helper_text/extends.js"),
            Self::Assign => include_str!("helper_text/assign.js"),
            Self::Rest => include_str!("helper_text/rest.js"),
            Self::Decorate => include_str!("helper_text/decorate.js"),
            Self::Param => include_str!("helper_text/param.js"),
            Self::Metadata => include_str!("helper_text/metadata.js"),
            Self::Awaiter => {
                "var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {\n    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }\n    return new (P || (P = Promise))(function (resolve, reject) {\n        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }\n        function rejected(value) { try { step(generator[\"throw\"](value)); } catch (e) { reject(e); } }\n        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }\n        step((generator = generator.apply(thisArg, _arguments || [])).next());\n    });\n};\n"
            }
            Self::Generator => {
                "var __generator = (this && this.__generator) || function (thisArg, body) {\n    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g = Object.create((typeof Iterator === \"function\" ? Iterator : Object).prototype);\n    return g.next = verb(0), g[\"throw\"] = verb(1), g[\"return\"] = verb(2), typeof Symbol === \"function\" && (g[Symbol.iterator] = function() { return this; }), g;\n    function verb(n) { return function (v) { return step([n, v]); }; }\n    function step(op) {\n        if (f) throw new TypeError(\"Generator is already executing.\");\n        while (g && (g = 0, op[0] && (_ = 0)), _) try {\n            if (f = 1, y && (t = op[0] & 2 ? y[\"return\"] : op[0] ? y[\"throw\"] || ((t = y[\"return\"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;\n            if (y = 0, t) op = [op[0] & 2, t.value];\n            switch (op[0]) {\n                case 0: case 1: t = op; break;\n                case 4: _.label++; return { value: op[1], done: false };\n                case 5: _.label++; y = op[1]; op = [0]; continue;\n                case 7: op = _.ops.pop(); _.trys.pop(); continue;\n                default:\n                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }\n                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }\n                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }\n                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }\n                    if (t[2]) _.ops.pop();\n                    _.trys.pop(); continue;\n            }\n            op = body.call(thisArg, _);\n        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }\n        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };\n    }\n};\n"
            }
            Self::AddDisposableResource => include_str!("helper_text/addDisposableResource.js"),
            Self::DisposeResources => include_str!("helper_text/disposeResources.js"),
            Self::ExportStar => include_str!("helper_text/exportStar.js"),
            Self::CreateBinding => include_str!("helper_text/createBinding.js"),
            Self::SetModuleDefault => include_str!("helper_text/setModuleDefault.js"),
            Self::Values => include_str!("helper_text/values.js"),
            Self::Read => include_str!("helper_text/read.js"),
            Self::SpreadArray => include_str!("helper_text/spreadArray.js"),
            Self::ImportStar => include_str!("helper_text/importStar.js"),
            Self::ImportDefault => include_str!("helper_text/importDefault.js"),
            Self::ClassPrivateFieldGet => include_str!("helper_text/classPrivateFieldGet.js"),
            Self::ClassPrivateFieldSet => include_str!("helper_text/classPrivateFieldSet.js"),
            Self::ClassPrivateFieldIn => include_str!("helper_text/classPrivateFieldIn.js"),
            Self::PropKey => {
                "function __propKey(value) {\n    var exotic, method, primitive, type = typeof value;\n    if (value === null || (type !== \"object\" && type !== \"function\")) return type === \"symbol\" ? value : \"\" + value;\n    exotic = typeof Symbol === \"function\" && Symbol.toPrimitive ? value[Symbol.toPrimitive] : void 0;\n    if (exotic !== void 0 && exotic !== null) {\n        if (typeof exotic !== \"function\") throw new TypeError(\"@@toPrimitive must be a function\");\n        primitive = exotic.call(value, \"string\");\n        type = typeof primitive;\n        if (primitive !== null && (type === \"object\" || type === \"function\")) throw new TypeError(\"@@toPrimitive must return a primitive value\");\n        return type === \"symbol\" ? primitive : \"\" + primitive;\n    }\n    method = value.toString;\n    if (typeof method === \"function\") {\n        primitive = method.call(value);\n        type = typeof primitive;\n        if (primitive === null || (type !== \"object\" && type !== \"function\")) return type === \"symbol\" ? primitive : \"\" + primitive;\n    }\n    method = value.valueOf;\n    if (typeof method === \"function\") {\n        primitive = method.call(value);\n        type = typeof primitive;\n        if (primitive === null || (type !== \"object\" && type !== \"function\")) return type === \"symbol\" ? primitive : \"\" + primitive;\n    }\n    throw new TypeError(\"Cannot convert object to primitive value\");\n}\n"
            }
        }
    }

    /// Parses a helper identifier into a catalog entry.
    #[must_use]
    pub fn from_ident(name: &str) -> Option<Self> {
        Self::all()
            .iter()
            .copied()
            .find(|kind| kind.ident() == name)
    }
}

/// The recovered helper prelude plus any policy diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HelperEmit {
    /// Text to prepend to the emitted program. Empty when no helper is required.
    pub prelude: String,
    /// Helpers included in `prelude`, in emit order.
    pub helpers: Vec<HelperKind>,
    /// Whether imported helpers are reached through one namespace binding
    /// (`const tslib_1 = require("tslib");`) that the caller emits itself.
    pub tslib_binding: bool,
    /// Policy diagnostics in canonical [`Diagnostic`] order.
    pub diagnostics: Vec<Diagnostic>,
}

impl HelperEmit {
    /// Returns whether any diagnostic is an error.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|diagnostic| !diagnostic.is_warning())
    }
}

/// Expands `requested` through the dependency graph and emits a prelude.
///
/// `file` is consulted only when `options.import_helpers` is true and the style
/// is [`HelperStyle::EsModule`]: a non-module file then produces
/// [`codes::IMPORT_HELPERS_REQUIRES_MODULE`] and no prelude.
#[must_use]
pub fn emit_helpers(
    requested: &[HelperKind],
    options: &HelperOptions,
    file: Option<&SourceFile>,
) -> HelperEmit {
    let source_is_module = file.is_some_and(crate::checker::source_is_module);
    emit_closed(
        close_helpers(requested),
        options,
        file,
        Vec::new(),
        options.import_helpers,
        source_is_module,
    )
}

/// Emits helpers using the caller's effective module classification.
///
/// Project emission uses this when synthesized imports make a source a module
/// even though its original syntax has no import or export.
#[must_use]
pub(super) fn emit_helpers_for_source(
    requested: &[HelperKind],
    options: &HelperOptions,
    file: &SourceFile,
    source_is_module: bool,
) -> HelperEmit {
    emit_closed(
        close_helpers(requested),
        options,
        Some(file),
        Vec::new(),
        options.import_helpers && source_is_module,
        source_is_module,
    )
}

/// Resolves helper identifiers, recording [`codes::UNKNOWN_HELPER`] for names
/// that are not in the tslib catalog, then emits a prelude.
#[must_use]
pub fn emit_helpers_named(
    names: &[&str],
    options: &HelperOptions,
    file: Option<&SourceFile>,
    source_id: SourceId,
    range: TextRange,
) -> HelperEmit {
    let mut requested = Vec::new();
    let mut diagnostics = Vec::new();
    for name in names {
        match HelperKind::from_ident(name) {
            Some(kind) => requested.push(kind),
            None => diagnostics.push(Diagnostic::error(
                codes::UNKNOWN_HELPER,
                source_id,
                range,
                "emit helper is not in the tslib catalog",
            )),
        }
    }
    let source_is_module = file.is_some_and(crate::checker::source_is_module);
    emit_closed(
        close_helpers(&requested),
        options,
        file,
        diagnostics,
        options.import_helpers,
        source_is_module,
    )
}

fn close_helpers(requested: &[HelperKind]) -> Vec<HelperKind> {
    let mut set = BTreeSet::new();
    let mut stack: Vec<HelperKind> = requested.to_vec();
    while let Some(kind) = stack.pop() {
        if set.insert(kind) {
            stack.extend(kind.dependencies().iter().copied());
        }
    }
    set.into_iter().collect()
}

fn emit_closed(
    helpers: Vec<HelperKind>,
    options: &HelperOptions,
    file: Option<&SourceFile>,
    mut diagnostics: Vec<Diagnostic>,
    import_helpers: bool,
    source_is_module: bool,
) -> HelperEmit {
    if helpers.is_empty() {
        diagnostics.sort();
        return HelperEmit {
            prelude: String::new(),
            helpers,
            tslib_binding: false,
            diagnostics,
        };
    }
    let external_imports = import_helpers && options.style != HelperStyle::Inline;
    let (imported, inline_only): (Vec<_>, Vec<_>) = if external_imports {
        helpers
            .iter()
            .copied()
            .partition(|helper| helper.can_import())
    } else {
        (Vec::new(), helpers.clone())
    };
    if !imported.is_empty() && options.style == HelperStyle::EsModule && !source_is_module {
        let (source_id, range) = file.map_or((SourceId::new(0), empty_range()), |file| {
            (file.source_id(), file.range())
        });
        diagnostics.push(Diagnostic::error(
            codes::IMPORT_HELPERS_REQUIRES_MODULE,
            source_id,
            range,
            "importHelpers with ESM bindings requires an import or export in the file",
        ));
        diagnostics.sort();
        return HelperEmit {
            prelude: String::new(),
            helpers: Vec::new(),
            tslib_binding: false,
            diagnostics,
        };
    }

    let inline_prelude = if options.no_emit_helpers {
        String::new()
    } else {
        inline_prelude(&inline_only)
    };
    let prelude = match options.style {
        HelperStyle::Inline => inline_prelude,
        HelperStyle::EsModule if external_imports => {
            let mut prelude = if imported.is_empty() {
                String::new()
            } else {
                es_import_prelude(&imported, &options.module_specifier)
            };
            prelude.push_str(&inline_prelude);
            prelude
        }
        HelperStyle::EsModule | HelperStyle::CommonJs => inline_prelude,
    };

    diagnostics.sort();
    HelperEmit {
        prelude,
        helpers,
        tslib_binding: options.style == HelperStyle::CommonJs && !imported.is_empty(),
        diagnostics,
    }
}

fn inline_prelude(helpers: &[HelperKind]) -> String {
    fn append(helper: HelperKind, emitted: &mut BTreeSet<HelperKind>, prelude: &mut String) {
        if !emitted.insert(helper) {
            return;
        }
        for dependency in helper.dependencies() {
            append(*dependency, emitted, prelude);
        }
        prelude.push_str(helper.inline_source());
    }

    let mut emitted = BTreeSet::new();
    let mut prelude = String::new();
    // Canonical catalog order regardless of request order: the documented
    // promise is that [B, A] and [A, B] produce byte-identical preludes,
    // and tsc's own order is deterministic (awaiter before generator).
    let ordered: BTreeSet<HelperKind> = helpers.iter().copied().collect();
    for helper in ordered {
        append(helper, &mut emitted, &mut prelude);
    }
    prelude
}

fn es_import_prelude(helpers: &[HelperKind], specifier: &str) -> String {
    let mut prelude = String::from("import { ");
    for (index, helper) in helpers.iter().enumerate() {
        if index > 0 {
            prelude.push_str(", ");
        }
        prelude.push_str(helper.ident());
    }
    prelude.push_str(" } from ");
    push_quoted(&mut prelude, specifier);
    prelude.push_str(";\n");
    prelude
}

fn push_quoted(out: &mut String, value: &str) {
    out.push('"');
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            other => out.push(other),
        }
    }
    out.push('"');
}

fn empty_range() -> TextRange {
    TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("zero range is ordered")
}

#[cfg(test)]
mod tests {
    use super::{HelperKind, HelperOptions, HelperStyle, codes, emit_helpers, emit_helpers_named};
    use crate::parser;
    use crate::scanner;
    use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
    use std::sync::Arc;

    fn dummy_range() -> TextRange {
        TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("range")
    }

    fn parse(source: &str) -> crate::syntax::SourceFile {
        parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(SourceText::new(source).expect("static test source fits size limit")),
        ))
        .into_product()
    }

    #[test]
    fn request_order_does_not_change_prelude_bytes() {
        let options = HelperOptions::inline();
        let ab = emit_helpers(&[HelperKind::Rest, HelperKind::Assign], &options, None);
        let ba = emit_helpers(&[HelperKind::Assign, HelperKind::Rest], &options, None);
        assert_eq!(ab.prelude, ba.prelude);
        assert_eq!(ab.helpers, vec![HelperKind::Assign, HelperKind::Rest]);
        assert_eq!(ba.helpers, vec![HelperKind::Assign, HelperKind::Rest]);
        assert!(ab.prelude.find("__assign").unwrap() < ab.prelude.find("__rest").unwrap());
    }

    #[test]
    fn prelude_order_is_request_order_independent() {
        // The documented contract: [B, A] and [A, B] produce byte-identical
        // preludes. Canonical catalog order is structural, not caller luck.
        let canonical = emit_helpers(
            &[HelperKind::Awaiter, HelperKind::Generator],
            &HelperOptions::inline(),
            None,
        );
        let reversed = emit_helpers(
            &[HelperKind::Generator, HelperKind::Awaiter],
            &HelperOptions::inline(),
            None,
        );
        assert_eq!(canonical.prelude, reversed.prelude);
        assert!(
            canonical.prelude.find("__awaiter").unwrap()
                < canonical.prelude.find("__generator").unwrap(),
            "awaiter precedes generator: {}",
            canonical.prelude
        );
    }

    #[test]
    fn awaiter_emits_alone_in_the_tsc_guard_form() {
        // tsc 7.0.2 binds helpers as `var __awaiter = (this && this.__awaiter)
        // || function ...` and emits no __generator alongside the awaiter:
        // native-generator targets never need it.
        let emitted = emit_helpers(&[HelperKind::Awaiter], &HelperOptions::inline(), None);
        assert_eq!(emitted.helpers, vec![HelperKind::Awaiter]);
        assert!(
            emitted
                .prelude
                .starts_with("var __awaiter = (this && this.__awaiter) || function (thisArg"),
            "{}",
            emitted.prelude
        );
        assert!(emitted.prelude.contains("function adopt(value)"));
        assert!(!emitted.prelude.contains("__generator"));
    }

    #[test]
    fn every_inline_helper_parses_as_one_complete_statement() {
        for kind in HelperKind::all() {
            let parsed = parser::parse(scanner::scan(
                SourceId::new(0),
                ScriptKind::TypeScript,
                Arc::new(
                    SourceText::new(kind.inline_source()).expect("helper text fits size limit"),
                ),
            ));
            assert!(
                parsed.diagnostics().is_empty(),
                "{}: {:?}",
                kind.ident(),
                parsed.diagnostics()
            );
            assert_eq!(parsed.product().statements().len(), 1, "{}", kind.ident());
        }
    }

    #[test]
    fn esm_import_lists_helpers_in_catalog_order() {
        let file = parse("export const x = 1;\n");
        let emitted = emit_helpers(
            &[HelperKind::Generator, HelperKind::Awaiter],
            &HelperOptions::es_module(),
            Some(&file),
        );
        assert!(!emitted.has_errors());
        assert_eq!(
            emitted.prelude,
            "import { __awaiter, __generator } from \"tslib\";\n"
        );
    }

    #[test]
    fn commonjs_binds_imported_helpers_through_one_namespace() {
        let emitted = emit_helpers(&[HelperKind::Rest], &HelperOptions::common_js(), None);
        assert!(emitted.prelude.is_empty());
        assert!(emitted.tslib_binding);
    }

    #[test]
    fn custom_specifier_is_quoted_identically_in_both_import_styles() {
        let file = parse("import \"./mod\";\n");
        let options = HelperOptions::es_module().with_module_specifier("custom-lib");
        let esm = emit_helpers(&[HelperKind::Assign], &options, Some(&file));
        assert_eq!(esm.prelude, "import { __assign } from \"custom-lib\";\n");

        let cjs = emit_helpers(
            &[HelperKind::Assign],
            &HelperOptions::common_js().with_module_specifier("custom-lib"),
            None,
        );
        assert!(cjs.prelude.is_empty());
        assert!(cjs.tslib_binding);
    }

    #[test]
    fn esm_import_helpers_on_a_script_is_an_error_and_emits_nothing() {
        let file = parse("const x = 1;\n");
        assert!(!crate::checker::source_is_module(&file));
        let emitted = emit_helpers(
            &[HelperKind::Awaiter],
            &HelperOptions::es_module(),
            Some(&file),
        );
        assert!(emitted.has_errors());
        assert!(emitted.prelude.is_empty());
        assert!(emitted.helpers.is_empty());
        assert_eq!(
            emitted.diagnostics[0].code(),
            codes::IMPORT_HELPERS_REQUIRES_MODULE
        );
    }

    #[test]
    fn imported_helpers_still_emit_with_no_emit_helpers() {
        let file = parse("export const x = 1;\n");
        let mut esm = HelperOptions::es_module();
        esm.no_emit_helpers = true;
        let esm = emit_helpers(
            &[HelperKind::Awaiter, HelperKind::PropKey],
            &esm,
            Some(&file),
        );
        assert!(!esm.has_errors());
        assert_eq!(esm.prelude, "import { __awaiter } from \"tslib\";\n");

        let mut common_js = HelperOptions::common_js();
        common_js.no_emit_helpers = true;
        let common_js = emit_helpers(
            &[HelperKind::Awaiter, HelperKind::PropKey],
            &common_js,
            None,
        );
        assert!(!common_js.has_errors());
        assert!(common_js.prelude.is_empty());
        assert!(common_js.tslib_binding);
    }

    #[test]
    fn unknown_helper_name_is_diagnosed_and_known_names_still_emit() {
        let emitted = emit_helpers_named(
            &["__rest", "__notAHelper"],
            &HelperOptions::inline(),
            None,
            SourceId::new(0),
            dummy_range(),
        );
        assert!(emitted.has_errors());
        assert_eq!(emitted.diagnostics[0].code(), codes::UNKNOWN_HELPER);
        assert_eq!(emitted.helpers, vec![HelperKind::Rest]);
        assert!(
            emitted
                .prelude
                .contains("var __rest = (this && this.__rest) ||")
        );
    }

    #[test]
    fn empty_request_emits_empty_prelude() {
        let emitted = emit_helpers(&[], &HelperOptions::inline(), None);
        assert!(emitted.prelude.is_empty());
        assert!(emitted.helpers.is_empty());
        assert!(!emitted.has_errors());
    }

    #[test]
    fn inline_bodies_start_with_the_catalog_identifier() {
        for kind in HelperKind::all() {
            let source = kind.inline_source();
            let plain = source.starts_with("function ") && source.contains(kind.ident());
            let guard = source.starts_with(&format!(
                "var {} = (this && this.{}) || ",
                kind.ident(),
                kind.ident()
            ));
            assert!(plain || guard, "{}", kind.ident());
            assert!(source.ends_with('\n'));
        }
    }

    #[test]
    fn helpers_print_in_the_order_the_tsc_baselines_do() {
        // Authority: amdDependencyCommentName4 (createBinding, setModuleDefault,
        // importStar, importDefault) and the baselines that print __awaiter or
        // __generator before __importDefault and __rest.
        let emitted = emit_helpers(
            &[
                HelperKind::Rest,
                HelperKind::ImportDefault,
                HelperKind::Awaiter,
                HelperKind::ImportStar,
                HelperKind::Decorate,
                HelperKind::Extends,
            ],
            &HelperOptions::inline(),
            None,
        );
        assert_eq!(
            emitted.helpers,
            vec![
                HelperKind::Extends,
                HelperKind::CreateBinding,
                HelperKind::SetModuleDefault,
                HelperKind::Decorate,
                HelperKind::ImportStar,
                HelperKind::Awaiter,
                HelperKind::ImportDefault,
                HelperKind::Rest,
            ]
        );
    }

    #[test]
    fn import_helpers_false_inlines_even_when_style_is_esm() {
        let options = HelperOptions {
            import_helpers: false,
            no_emit_helpers: false,
            style: HelperStyle::EsModule,
            module_specifier: String::from("tslib"),
        };
        let emitted = emit_helpers(&[HelperKind::Rest], &options, None);
        assert!(
            emitted
                .prelude
                .starts_with("var __rest = (this && this.__rest) ||")
        );
        assert!(!emitted.prelude.contains("import"));
    }

    #[test]
    fn two_identical_requests_are_byte_stable() {
        let options = HelperOptions::inline();
        let left = emit_helpers(
            &[
                HelperKind::SpreadArray,
                HelperKind::Awaiter,
                HelperKind::Rest,
            ],
            &options,
            None,
        );
        let right = emit_helpers(
            &[
                HelperKind::SpreadArray,
                HelperKind::Awaiter,
                HelperKind::Rest,
            ],
            &options,
            None,
        );
        assert_eq!(left, right);
    }
}
