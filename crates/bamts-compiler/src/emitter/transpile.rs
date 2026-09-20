//! Single-file syntactic-first transpilation.
//!
//! This module scans, parses, checks, transforms, and emits one isolated source
//! file. It performs the only checker pass in the transpile path, then delegates
//! to the checked emitter with the resulting semantic model.

use std::sync::Arc;

use crate::checker;
use crate::diagnostic::{Diagnostic, Recovered};
use crate::parser;
use crate::scanner;
use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
use crate::syntax::SourceFile;

use super::{EmitFileNames, EmitOptions, EmitOutput, emit_checked};

/// Stable diagnostic identifiers produced by single-file transpilation.
pub mod codes {
    use crate::diagnostic::DiagnosticCode;

    /// The source exceeds the compiler's bounded per-file text budget.
    pub const SOURCE_TOO_LARGE: DiagnosticCode = DiagnosticCode::new("TS-EMIT-1601");
}

/// Transpiles an already-parsed file without reporting semantic diagnostics.
///
/// The semantic model is still built because the shared printer uses enum and
/// symbol facts, but single-file transpilation exposes only scanner, parser,
/// option, and transform diagnostics.
#[must_use]
pub fn transpile(
    file: &Recovered<SourceFile>,
    options: &EmitOptions,
    names: &EmitFileNames,
) -> EmitOutput {
    let checked = checker::check(file);
    let (model, _) = checked.into_parts();
    let source_file = file.product();
    let mut output = emit_checked(source_file, &model, options, names);

    output
        .diagnostics
        .extend(file.diagnostics().iter().cloned());
    output.diagnostics.sort();
    output.diagnostics.dedup();
    output
}

/// Scans, parses, checks, and transpiles one source text in a single call.
#[must_use]
pub fn transpile_text(
    source_id: SourceId,
    script_kind: ScriptKind,
    text: impl Into<Arc<str>>,
    options: &EmitOptions,
    names: &EmitFileNames,
) -> EmitOutput {
    let source = match SourceText::new(text) {
        Ok(source) => Arc::new(source),
        Err(_error) => {
            return EmitOutput {
                diagnostics: vec![Diagnostic::error(
                    codes::SOURCE_TOO_LARGE,
                    source_id,
                    TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO)
                        .expect("zero-width diagnostic range is ordered"),
                    "source text exceeds the per-file budget",
                )],
                ..EmitOutput::default()
            };
        }
    };
    let scanned = scanner::scan(source_id, script_kind, source);
    let parsed = parser::parse(scanned);
    transpile(&parsed, options, names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{JsxEmit, SourceId};
    use std::collections::BTreeMap;

    use super::super::ModuleKind;
    use super::super::transforms::ScriptTarget;

    fn names() -> EmitFileNames {
        EmitFileNames {
            source_name: Arc::from("input.ts"),
            js_file_name: Some(Arc::from("output.js")),
            declaration_file_name: Some(Arc::from("output.d.ts")),
            source_root: None,
            ..EmitFileNames::default()
        }
    }

    fn one(source: &str, options: &EmitOptions) -> EmitOutput {
        transpile_text(
            SourceId::new(1),
            ScriptKind::TypeScript,
            Arc::from(source),
            options,
            &names(),
        )
    }

    fn one_jsx(source: &str, options: &EmitOptions) -> EmitOutput {
        transpile_text(
            SourceId::new(1),
            ScriptKind::TypeScriptReact,
            Arc::from(source),
            options,
            &EmitFileNames {
                source_name: Arc::from("input.tsx"),
                js_file_name: Some(Arc::from("output.jsx")),
                declaration_file_name: Some(Arc::from("output.d.ts")),
                source_root: None,
                ..EmitFileNames::default()
            },
        )
    }

    #[test]
    fn removes_type_annotations() {
        let options = EmitOptions {
            target: ScriptTarget::EsNext,
            ..EmitOptions::default()
        };
        let out = one("const x: number = 1;", &options);
        let js = out.javascript.expect("javascript output").code;
        assert!(js.contains("const x = 1;"), "got:\n{js}");
    }
    #[test]
    fn semantic_type_errors_do_not_escape_single_file_transpile() {
        let options = EmitOptions {
            target: ScriptTarget::EsNext,
            ..EmitOptions::default()
        };
        let out = one("const x: string = 1;", &options);
        assert!(!out.has_errors(), "{:?}", out.diagnostics);
        assert!(
            out.javascript
                .expect("javascript output")
                .code
                .contains("const x = 1;")
        );
    }

    #[test]
    fn emits_isolated_declaration() {
        let options = EmitOptions {
            declaration: true,
            isolated_declarations: true,
            ..EmitOptions::default()
        };
        let out = one("export const value: number = 1;", &options);
        let dts = out.declaration.expect("declaration output").code;
        assert!(dts.contains("value"), "got:\n{dts}");
    }

    #[test]
    fn emit_declaration_only_skips_javascript() {
        let options = EmitOptions {
            declaration: true,
            emit_declaration_only: true,
            ..EmitOptions::default()
        };
        let out = one("export const value: number = 1;", &options);
        assert!(out.javascript.is_none());
        assert!(out.declaration.is_some());
    }

    #[test]
    fn rejects_invalid_target() {
        let mut options = EmitOptions::default();
        let diagnostic = options
            .apply_directive("target", "es9999", SourceId::new(0))
            .expect("diagnostic");
        assert_eq!(diagnostic.code(), super::super::codes::INVALID_OPTION_VALUE);
    }

    #[test]
    fn directives_build_canonical_emit_options() {
        let directives = BTreeMap::from([
            ("importhelpers".to_owned(), "true".to_owned()),
            ("module".to_owned(), "es2015".to_owned()),
            ("target".to_owned(), "es2015".to_owned()),
        ]);
        let (options, diagnostics) = EmitOptions::from_directives(&directives, SourceId::new(0));
        assert!(
            diagnostics.is_empty(),
            "unexpected diagnostics: {diagnostics:?}"
        );
        assert_eq!(options.target, ScriptTarget::Es2015);
        assert_eq!(options.module, Some(ModuleKind::Es2015));
        assert!(options.import_helpers);
    }

    #[test]
    fn private_field_below_es2022_is_an_error() {
        let options = EmitOptions {
            target: ScriptTarget::Es2015,
            ..EmitOptions::default()
        };
        let out = one("class C { #x = 1; }", &options);
        assert!(
            out.diagnostics.iter().any(|diagnostic| diagnostic.code()
                == super::super::transforms::codes::PRIVATE_FIELD_REQUIRES_ES2022),
            "private field should be rejected below ES2022: {:?}",
            out.diagnostics
        );
    }

    #[test]
    fn import_helpers_fall_back_to_inline_helpers_for_scripts() {
        let esm_options = EmitOptions {
            target: ScriptTarget::Es5,
            import_helpers: true,
            module: Some(ModuleKind::Es2015),
            ..EmitOptions::default()
        };
        let esm = one("async function f() { return 1; }", &esm_options);
        assert!(
            !esm.has_errors(),
            "unexpected diagnostics: {:?}",
            esm.diagnostics
        );
        let esm_js = esm.javascript.expect("javascript output").code;
        assert!(esm_js.contains("var __awaiter ="));
        assert!(!esm_js.contains("from \"tslib\""));

        let common_js_options = EmitOptions {
            module: Some(ModuleKind::CommonJs),
            ..esm_options
        };
        let common_js = one("async function f() { return 1; }", &common_js_options);
        assert!(
            !common_js.has_errors(),
            "unexpected diagnostics: {:?}",
            common_js.diagnostics
        );
        let common_js = common_js.javascript.expect("javascript output").code;
        assert!(common_js.contains("var __awaiter ="));
        assert!(!common_js.contains("require(\"tslib\")"));
    }

    #[test]
    fn import_helpers_take_precedence_over_no_emit_helpers_for_modules() {
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            import_helpers: true,
            no_emit_helpers: true,
            module: Some(ModuleKind::Es2015),
            ..EmitOptions::default()
        };
        let out = one("export async function f() { return 1; }", &options);
        assert!(
            !out.has_errors(),
            "unexpected diagnostics: {:?}",
            out.diagnostics
        );
        let js = out.javascript.expect("javascript output").code;
        assert!(js.contains("from \"tslib\";"), "got:\n{js}");
        assert!(js.contains("__awaiter"), "got:\n{js}");
        assert!(js.contains("__generator"), "got:\n{js}");
        assert!(!js.contains("var __awaiter ="));
    }

    #[test]
    fn syntax_error_is_reported() {
        let out = one("const x =", &EmitOptions::default());
        assert!(!out.diagnostics.is_empty(), "parser error missing");
    }

    #[test]
    fn output_is_deterministic() {
        let options = EmitOptions::default();
        let first = one("let a: number = 1;\nlet b: string = 'x';", &options);
        let second = one("let a: number = 1;\nlet b: string = 'x';", &options);
        assert_eq!(first, second);
    }

    #[test]
    fn source_map_uses_printer_mappings() {
        let options = EmitOptions {
            source_map: true,
            ..EmitOptions::default()
        };
        let out = one("if (true) {\n  const x: number = 1;\n}", &options);
        let map = out
            .javascript
            .expect("javascript output")
            .source_map
            .expect("source map requested");
        assert_eq!(map.file(), Some("output.js"));
        assert_eq!(map.sources(), &["input.ts"]);
        assert!(
            map.mappings().iter().any(|mapping| {
                mapping.generated.column > 0
                    && mapping
                        .original
                        .is_some_and(|original| original.position.column > 0)
            }),
            "printer did not record a nested statement column: {:?}",
            map.mappings()
        );
        map.validate().expect("valid source map");
    }

    #[test]
    fn preserve_and_react_native_print_structural_jsx() {
        let source = "const view = <ns:Tag data-id=\"x\" {...props}>before{...items}<this.Widget /></ns:Tag>;";
        for emit in [JsxEmit::Preserve, JsxEmit::ReactNative] {
            let options = EmitOptions {
                jsx: Some(emit),
                ..EmitOptions::default()
            };
            let output = one_jsx(source, &options);
            let code = output.javascript.expect("JavaScript output").code;
            assert_eq!(
                code,
                "const view = <ns:Tag data-id=\"x\" {...props}>before{...items}<this.Widget /></ns:Tag>;\n"
            );
        }
    }

    #[test]
    fn classic_jsx_uses_factory_and_assign_helper_demand() {
        let options = EmitOptions {
            jsx: Some(JsxEmit::React),
            ..EmitOptions::default()
        };
        let output = one_jsx(
            "const view = <Box a=\"x\" {...props}>child</Box>;",
            &options,
        );
        let code = output.javascript.expect("JavaScript output").code;
        assert!(code.contains("function __assign"), "{code}");
        assert!(code.contains("React.createElement"), "{code}");
        assert!(!code.contains("<Box"), "{code}");
    }

    #[test]
    fn automatic_jsx_emits_collision_free_esm_runtime_import() {
        let options = EmitOptions {
            jsx: Some(JsxEmit::ReactJsx),
            ..EmitOptions::default()
        };
        let output = one_jsx("const _jsx = 1; const view = <div />;", &options);
        let code = output.javascript.expect("JavaScript output").code;
        assert!(
            code.starts_with("import { jsx as _jsx_1 } from \"react/jsx-runtime\";\n"),
            "{code}"
        );
        assert!(code.contains("_jsx_1(\"div\""), "{code}");
    }

    #[test]
    fn automatic_jsx_module_can_import_helpers() {
        let options = EmitOptions {
            target: ScriptTarget::Es5,
            import_helpers: true,
            jsx: Some(JsxEmit::ReactJsx),
            ..EmitOptions::default()
        };
        let output = one_jsx(
            "const view = <div />; async function f() { return 1; }",
            &options,
        );
        assert!(
            !output.has_errors(),
            "unexpected diagnostics: {:?}",
            output.diagnostics
        );
        let code = output.javascript.expect("JavaScript output").code;
        assert!(code.contains("from \"tslib\";"), "{code}");
        assert!(code.contains("from \"react/jsx-runtime\";"), "{code}");
        assert!(
            !code.contains("var __awaiter = (this && this.__awaiter)"),
            "{code}"
        );
    }

    #[test]
    fn automatic_jsx_emits_commonjs_runtime_bindings() {
        let options = EmitOptions {
            module: Some(ModuleKind::CommonJs),
            jsx: Some(JsxEmit::ReactJsx),
            ..EmitOptions::default()
        };
        let output = one_jsx("const view = <><span /><span /></>;", &options);
        let code = output.javascript.expect("JavaScript output").code;
        // The `__esModule` marker precedes every require prelude, matching
        // upstream module emit (commonjsSafeImport 282283386).
        assert!(
            code.starts_with(
                "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nvar _jsxRuntime = require(\"react/jsx-runtime\");\n",
            ),
            "{code}"
        );
        assert!(code.contains("var _jsxs = _jsxRuntime.jsxs;"), "{code}");
        assert!(
            code.contains("var _Fragment = _jsxRuntime.Fragment;"),
            "{code}"
        );
    }

    #[test]
    fn development_jsx_uses_dev_runtime_and_metadata() {
        let options = EmitOptions {
            jsx: Some(JsxEmit::ReactJsxDev),
            ..EmitOptions::default()
        };
        let output = one_jsx("const view = <div />;", &options);
        let code = output.javascript.expect("JavaScript output").code;
        assert!(code.contains("jsxDEV as _jsxDEV"), "{code}");
        assert!(code.contains("react/jsx-dev-runtime"), "{code}");
        assert!(code.contains("_jsxDEV(\"div\""), "{code}");
        assert!(code.contains("fileName: \"input.tsx\""), "{code}");
    }

    #[test]
    fn declaration_output_never_prints_jsx_initializer() {
        let options = EmitOptions {
            declaration: true,
            emit_declaration_only: true,
            jsx: Some(JsxEmit::ReactJsx),
            ..EmitOptions::default()
        };
        let output = one_jsx("export const view: unknown = <div />;", &options);
        let code = output.declaration.expect("declaration output").code;
        assert_eq!(code, "export declare const view: unknown;\n");
        assert!(!code.contains("<div"));
        assert!(!code.contains("_jsx"));
    }
}
