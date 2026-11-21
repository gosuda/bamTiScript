//! TS6133 and TS6192 for unused imports under `noUnusedLocals`.
//!
//! The check walks import declarations with the binder's scopes. A binding
//! counts as used when a recorded reference resolves to it, when a
//! source-less export specifier names it, or when it is the classic JSX
//! factory. A declaration whose bindings are all unused reports once at the
//! declaration; a partially used one reports each unused binding at its name.

use std::collections::HashSet;

use crate::diagnostic::Diagnostic;
use crate::source::{JsxEmit, ScriptKind, TextRange};
use crate::syntax::{
    IdentifierNode, ImportBinding, ImportDeclaration, ImportEqualsDeclaration, ImportSpecifierMode,
    SourceFile, Statement, Stmt,
};

use super::binder::{ScopeId, SemanticModel};
use super::unused_reads::{
    FileReads, all_unused_diagnostic, exported_local_names, file_reads, is_exported_name,
    is_symbol_read, unused_diagnostic,
};

/// Options the unused-import check reads.
pub(crate) struct UnusedImportOptions {
    pub(crate) jsx: Option<JsxEmit>,
    pub(crate) jsx_custom_factory: bool,
}

/// TS6133 and TS6192 diagnostics for the unused imports of one source file.
#[must_use]
pub(crate) fn unused_import_diagnostics(
    source: &SourceFile,
    model: &SemanticModel,
    options: UnusedImportOptions,
) -> Vec<Diagnostic> {
    if source.source_text().is_declaration_file() {
        return Vec::new();
    }
    let pragma = pragma_factories(source);
    let mut exported = exported_local_names(source);
    let mut declarations = Vec::new();
    collect_statements(
        source.statements(),
        model.module_scope(),
        model,
        &mut declarations,
    );
    if is_classic_jsx(options.jsx) {
        match &pragma.factory {
            Some(factory) => {
                exported.insert(factory.clone());
            }
            None => {
                if classic_factory_used(source, &options) {
                    exported.insert("React".to_owned());
                }
            }
        }
        if let Some(fragment) = &pragma.fragment {
            exported.insert(fragment.clone());
        }
    }
    let reads = file_reads(source, model);
    let mut diagnostics = Vec::new();
    for declaration in &declarations {
        report_declaration(
            source,
            model,
            &reads,
            &exported,
            declaration,
            &mut diagnostics,
        );
    }
    diagnostics
}

/// The classic JSX factory is an implicit use of the `React` binding.
fn classic_factory_used(source: &SourceFile, options: &UnusedImportOptions) -> bool {
    is_react_file(source) && is_classic_jsx(options.jsx) && !options.jsx_custom_factory
}

/// A classic JSX factory or fragment read the file selects with a pragma.
struct PragmaFactories {
    factory: Option<String>,
    fragment: Option<String>,
}

/// The `@jsx` and `@jsxFrag` factories a file selects in its comments.
fn pragma_factories(source: &SourceFile) -> PragmaFactories {
    let mut factories = PragmaFactories {
        factory: None,
        fragment: None,
    };
    for token in source.tokens() {
        match token.kind() {
            crate::syntax::TokenKind::LineComment | crate::syntax::TokenKind::BlockComment => {
                if let Some(text) = source.token_text(token) {
                    scan_pragma_comment(text, &mut factories);
                }
            }
            _ => {}
        }
    }
    factories
}

/// Records the last `@jsx` factory and `@jsxFrag` fragment in one comment.
fn scan_pragma_comment(text: &str, factories: &mut PragmaFactories) {
    let mut rest = text;
    while let Some(found) = rest.find("@jsx") {
        let after = &rest[found + "@jsx".len()..];
        rest = after;
        if let Some(tail) = after
            .strip_prefix("Frag")
            .or_else(|| after.strip_prefix("frag"))
        {
            if let Some(name) = pragma_name(tail) {
                factories.fragment = if name == "null" { None } else { Some(name) };
            }
        } else if let Some(name) = pragma_name(after) {
            factories.factory = Some(name);
        }
    }
}

/// The root name after a pragma key, or nothing without a separating space.
fn pragma_name(after: &str) -> Option<String> {
    let mut chars = after.chars();
    match chars.next() {
        Some(' ') | Some('\t') | Some('\r') | Some('\n') => {}
        _ => return None,
    }
    let name: String = after
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '$')
        .collect();
    if name.is_empty() {
        return None;
    }
    Some(name)
}

fn is_react_file(source: &SourceFile) -> bool {
    matches!(
        source.script_kind(),
        ScriptKind::TypeScriptReact | ScriptKind::JavaScriptReact
    )
}

fn is_classic_jsx(jsx: Option<JsxEmit>) -> bool {
    matches!(
        jsx,
        Some(JsxEmit::React | JsxEmit::Preserve | JsxEmit::ReactNative)
    )
}

/// One import binding under inspection.
struct ImportTarget {
    scope: ScopeId,
    local: IdentifierNode,
    type_only: bool,
}

/// One import declaration and its bindings.
struct ImportDeclarationTargets {
    range: TextRange,
    bindings: Vec<ImportTarget>,
}

fn collect_statements(
    statements: &[Stmt],
    scope: ScopeId,
    model: &SemanticModel,
    declarations: &mut Vec<ImportDeclarationTargets>,
) {
    for statement in statements {
        collect_statement(statement, scope, model, declarations);
    }
}

fn collect_statement(
    statement: &Stmt,
    scope: ScopeId,
    model: &SemanticModel,
    declarations: &mut Vec<ImportDeclarationTargets>,
) {
    match statement.data() {
        Statement::Import(import) => {
            if let Some(declaration) = collect_import(import, scope, statement.range()) {
                declarations.push(declaration);
            }
        }
        Statement::ImportEquals(import) => {
            declarations.push(collect_import_equals(import, scope, statement.range()))
        }
        Statement::Namespace(namespace) => {
            let child = model.namespace_local_scope(statement.id()).unwrap_or(scope);
            collect_statements(
                &namespace.body.data().statements,
                child,
                model,
                declarations,
            );
        }
        Statement::Declare(_) => {}
        _ => {}
    }
}

fn collect_import(
    import: &ImportDeclaration,
    scope: ScopeId,
    range: TextRange,
) -> Option<ImportDeclarationTargets> {
    if import.type_only {
        return None;
    }
    let clause = import.clause.as_ref()?;
    let mut bindings = Vec::new();
    if let Some(default) = &clause.default {
        push_target(&mut bindings, scope, default.clone(), false);
    }
    match &clause.binding {
        Some(ImportBinding::Namespace(name)) => {
            push_target(&mut bindings, scope, name.clone(), false);
        }
        Some(ImportBinding::Named(specifiers)) => {
            for specifier in specifiers {
                push_target(
                    &mut bindings,
                    scope,
                    specifier.data().local.clone(),
                    matches!(specifier.data().mode, ImportSpecifierMode::TypeOnly),
                );
            }
        }
        None => {}
    }
    if bindings.is_empty() {
        return None;
    }
    Some(ImportDeclarationTargets { range, bindings })
}

fn push_target(
    bindings: &mut Vec<ImportTarget>,
    scope: ScopeId,
    local: IdentifierNode,
    type_only: bool,
) {
    bindings.push(ImportTarget {
        scope,
        local,
        type_only,
    });
}

fn collect_import_equals(
    import: &ImportEqualsDeclaration,
    scope: ScopeId,
    range: TextRange,
) -> ImportDeclarationTargets {
    ImportDeclarationTargets {
        range,
        bindings: vec![ImportTarget {
            scope,
            local: import.local.clone(),
            type_only: import.is_type_only,
        }],
    }
}

/// The local name of a reportable import binding, if it is neither
/// type-only nor underscore-prefixed. Exported names are resolved
/// separately so shadowed locals are still checked.
fn plain_import_name(source: &SourceFile, target: &ImportTarget) -> Option<String> {
    if target.type_only {
        return None;
    }
    let name = source.identifier_text(target.local.data().token())?;
    let name: &str = &name;
    if name.starts_with('_') {
        return None;
    }
    Some(name.to_owned())
}

fn report_declaration(
    source: &SourceFile,
    model: &SemanticModel,
    reads: &FileReads,
    exported: &HashSet<String>,
    declaration: &ImportDeclarationTargets,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut unused = Vec::new();
    for target in &declaration.bindings {
        let Some(name) = plain_import_name(source, target) else {
            continue;
        };
        let Some(symbol) = model.lookup_value(target.scope, &name) else {
            continue;
        };
        if is_exported_name(model, exported, &name, symbol) {
            continue;
        }
        if is_symbol_read(reads, symbol, target.local.range()) {
            continue;
        }
        unused.push((target.local.range(), name));
    }
    if unused.len() > 1 {
        diagnostics.push(all_unused_diagnostic(source, declaration.range));
        return;
    }
    for (range, name) in unused {
        diagnostics.push(unused_diagnostic(source, range, &name));
    }
}

// Diagnostics use the shared constructors so imports and locals agree on
// code, message, and span for the same unused shape.

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::checker::binder::bind_source;
    use crate::source::{SourceId, SourceText};

    fn check(text: &str) -> Vec<Diagnostic> {
        check_with_options(
            text,
            UnusedImportOptions {
                jsx: None,
                jsx_custom_factory: false,
            },
        )
    }

    fn check_with_options(text: &str, options: UnusedImportOptions) -> Vec<Diagnostic> {
        check_with_kind(text, ScriptKind::TypeScript, options)
    }

    fn check_with_kind(
        text: &str,
        kind: ScriptKind,
        options: UnusedImportOptions,
    ) -> Vec<Diagnostic> {
        let source_text = Arc::new(SourceText::new(text).expect("test source fits the budget"));
        let parsed =
            crate::parser::parse(crate::scanner::scan(SourceId::new(0), kind, source_text));
        let file = parsed.product();
        let (model, _) = bind_source(file);
        unused_import_diagnostics(file, &model, options)
    }

    fn codes(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    #[test]
    fn unused_named_default_and_namespace_bindings_share_one_statement_error() {
        let text = "import { a } from \"./m\";\nimport d from \"./m\";\nimport * as ns from \"./m\";\nexport {};\n";
        let diagnostics = check(text);
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133", "6133", "6133"]);
        let starts: Vec<usize> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.range().start().get())
            .collect();
        let expected_a = text.find("{ a }").expect("a binding") + "{ ".len();
        let expected_d = text.find("import d ").expect("d binding") + "import ".len();
        let expected_ns = text.find("* as ns").expect("ns binding") + "* as ".len();
        assert_eq!(
            starts,
            [expected_a, expected_d, expected_ns],
            "{diagnostics:?}"
        );
        let messages: Vec<_> = diagnostics.iter().map(Diagnostic::message).collect();
        assert!(messages.contains(&"'a' is declared but its value is never read."));
        assert!(messages.contains(&"'d' is declared but its value is never read."));
        assert!(messages.contains(&"'ns' is declared but its value is never read."));
    }

    #[test]
    fn imported_type_used_in_annotation_is_clean() {
        let diagnostics = check("import { T } from \"./m\";\nlet x: T;\nexport {};\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn reexported_binding_is_clean() {
        let diagnostics = check("import { u } from \"./m\";\nexport { u };\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn underscore_prefixed_import_is_clean() {
        let diagnostics = check("import { _q } from \"./m\";\nexport {};\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn side_effect_import_is_clean() {
        let diagnostics = check("import \"./m\";\nexport {};\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn classic_jsx_factory_import_is_clean() {
        let classic = UnusedImportOptions {
            jsx: Some(JsxEmit::React),
            jsx_custom_factory: false,
        };
        let factory = check_with_kind(
            "import React from \"react\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            classic,
        );
        assert!(factory.is_empty(), "{factory:?}");
    }

    #[test]
    fn pragma_factory_and_fragment_count_as_uses() {
        let pragma = UnusedImportOptions {
            jsx: Some(JsxEmit::React),
            jsx_custom_factory: false,
        };
        let diagnostics = check_with_kind(
            "/** @jsx h\n * @jsxFrag Fragment\n */\nimport { h, Fragment, other } from \"./renderer\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            pragma,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
        assert_eq!(
            diagnostics[0].message(),
            "'other' is declared but its value is never read."
        );
    }
    #[test]
    fn custom_factory_reports_unrelated_unused() {
        let options = UnusedImportOptions {
            jsx: Some(JsxEmit::React),
            jsx_custom_factory: true,
        };
        let diagnostics = check_with_kind(
            "import { unused } from \"./m\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            options,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
    }

    #[test]
    fn custom_factory_reports_react_itself() {
        let options = UnusedImportOptions {
            jsx: Some(JsxEmit::React),
            jsx_custom_factory: true,
        };
        let diagnostics = check_with_kind(
            "import React from \"react\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            options,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
    }

    #[test]
    fn pragma_ignored_under_automatic_jsx() {
        let options = UnusedImportOptions {
            jsx: Some(JsxEmit::ReactJsx),
            jsx_custom_factory: false,
        };
        let diagnostics = check_with_kind(
            "/** @jsx h */\nimport { h } from \"./r\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            options,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
    }

    #[test]
    fn jsx_frag_null_clears_fragment_use() {
        let options = UnusedImportOptions {
            jsx: Some(JsxEmit::React),
            jsx_custom_factory: false,
        };
        let diagnostics = check_with_kind(
            "/** @jsx h\n * @jsxFrag null\n */\nimport { h, Fragment } from \"./r\";\nexport const el = 1;\n",
            ScriptKind::TypeScriptReact,
            options,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
        assert_eq!(
            diagnostics[0].message(),
            "'Fragment' is declared but its value is never read."
        );
    }

    #[test]
    fn all_unused_multi_binding_reports_6192_at_declaration() {
        let diagnostics = check("import { a, b } from \"./m\";\nexport {};\n");
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6192"]);
        assert_eq!(diagnostics[0].range().start().get(), 0, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].message(),
            "All imports in import declaration are unused."
        );
    }

    #[test]
    fn single_unused_in_multi_binding_reports_name() {
        let text = "import { a, b } from \"./m\";\nexport const x = a;\n";
        let diagnostics = check(text);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
        assert_eq!(
            diagnostics[0].message(),
            "'b' is declared but its value is never read."
        );
        let expected = text.find(", b }").expect("b binding") + ", ".len();
        assert_eq!(
            diagnostics[0].range().start().get(),
            expected,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn namespace_internal_export_does_not_mark_import_used() {
        let text = "import { a } from \"./m\";\nnamespace N { export { a }; }\n";
        let diagnostics = check(text);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
        assert_eq!(
            diagnostics[0].message(),
            "'a' is declared but its value is never read."
        );
        let expected = text.find("{ a }").expect("a binding") + "{ ".len();
        assert_eq!(
            diagnostics[0].range().start().get(),
            expected,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn import_equals_unused_reports() {
        let text = "import r = require(\"./m\");\nexport {};\n";
        let diagnostics = check(text);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
        assert_eq!(
            diagnostics[0].message(),
            "'r' is declared but its value is never read."
        );
        let expected = text.find("import r").expect("r binding") + "import ".len();
        assert_eq!(
            diagnostics[0].range().start().get(),
            expected,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn declaration_file_imports_are_clean() {
        let source_text = std::sync::Arc::new(
            crate::source::SourceText::new("import { a } from \"./m\";\n")
                .expect("test source fits the budget")
                .with_declaration_file(true),
        );
        let parsed = crate::parser::parse(crate::scanner::scan(
            crate::source::SourceId::new(0),
            ScriptKind::TypeScript,
            source_text,
        ));
        let file = parsed.product();
        let (model, _) = crate::checker::binder::bind_source(file);
        let diagnostics = unused_import_diagnostics(
            file,
            &model,
            UnusedImportOptions {
                jsx: None,
                jsx_custom_factory: false,
            },
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn namespace_nested_import_reports() {
        let diagnostics = check("namespace N { import { a } from \"./m\"; }\nexport {};\n");
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(codes(&diagnostics), ["6133"]);
    }
}
