//! Optional record updates retain defaults and strict-null write semantics.

use std::sync::Arc;

use bamts_compiler::{
    checker::{
        ProgramCheckInput, ProgramCheckOptions, SemanticModel, TypeId, check_program_with_options,
    },
    diagnostic::DiagnosticSeverity,
    lint::{LintProfile, LintTable},
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checked_model(source: &str, kind: ScriptKind, expected: &[&str]) -> SemanticModel {
    let source_id = SourceId::new(0);
    let scanned = scanner::scan(
        source_id,
        kind,
        Arc::new(SourceText::new(source).expect("fixture source fits")),
    );
    let files = [parser::parse(scanned)];
    let checked = check_program_with_options(
        ProgramCheckInput {
            files: &files,
            edges: &[],
        },
        &LintTable::new(LintProfile::Default),
        ProgramCheckOptions::standard().with_strict_null_checks(true),
    );
    let codes: Vec<_> = files[0]
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert_eq!(codes, expected, "{source}");
    let mut program = checked.into_product();
    program
        .remove_file(source_id)
        .expect("fixture semantic model")
}

fn binding_type(model: &SemanticModel, name: &str) -> TypeId {
    let symbol = model
        .scopes()
        .iter()
        .find_map(|scope| scope.value(name))
        .unwrap_or_else(|| panic!("binding {name} exists"));
    model.symbol_type(symbol)
}

#[test]
fn optional_record_spreads_preserve_required_defaults_and_value_unions() {
    let model = checked_model(
        r#"
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const replacement: Record<keyof typeof Keys, string>;
declare const unionExpected: number | string;
const numberDefault = { value: 0, ...optional };
const numberShape: { value: number } = numberDefault;
const numberValue = numberDefault.value;
const mixedDefault = { value: "fallback", ...optional };
const mixedShape: { value: number | string } = mixedDefault;
const mixedValue = mixedDefault.value;
const requiredReplacement = { value: 0, ...replacement };
const stringValue = requiredReplacement.value;
const wrongNumber: string = numberDefault.value;
const wrongUnion: boolean = mixedDefault.value;
const wrongReplacement: number = requiredReplacement.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 3],
    );
    assert_eq!(binding_type(&model, "numberValue"), model.types().number());
    assert_eq!(
        binding_type(&model, "mixedValue"),
        binding_type(&model, "unionExpected"),
    );
    assert_eq!(binding_type(&model, "stringValue"), model.types().string());
}

#[test]
fn optional_record_spreads_preserve_absence_and_explicit_undefined() {
    let model = checked_model(
        r#"
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const explicit: Partial<Record<keyof typeof Keys, number | undefined>>;
declare const expected: number | undefined;
const noDefault = { ...optional };
const missingDefault: { value: number } = noDefault;
const maybeValue = noDefault.value;
const withDefault = { value: 0, ...explicit };
const explicitValue = withDefault.value;
const unsafe: number = withDefault.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 2],
    );
    let expected = binding_type(&model, "expected");
    assert_eq!(binding_type(&model, "maybeValue"), expected);
    assert_eq!(binding_type(&model, "explicitValue"), expected);
}

#[test]
fn jsx_optional_record_spreads_preserve_defaults_without_hiding_overrides() {
    checked_model(
        r#"
namespace JSX {
    interface Element {}
    interface IntrinsicElements {
        div: { value: number };
        span: { value: number | string };
    }
}
class Keys { static value = 0; }
declare const optional: Partial<Record<keyof typeof Keys, number>>;
declare const strings: Partial<Record<keyof typeof Keys, string>>;
declare const required: Record<keyof typeof Keys, number>;
const accepted = <div value={0} {...optional} />;
const mixed = <span value={0} {...strings} />;
const replaced = <div value={"fallback"} {...required} />;
const wrongOverride = <div value={0} {...strings} />;
const missingDefault = <div {...optional} />;
"#,
        ScriptKind::TypeScriptReact,
        &["BAMTS-C022"; 2],
    );
}

#[test]
fn optional_record_writes_admit_undefined_without_erasing_value_checks() {
    checked_model(
        r#"
class Keys { static value = 0; }
type Fields<T> = Partial<Record<keyof typeof Keys, T>>;
declare let optional: Fields<number>;
declare let ordinary: { value?: number };
declare let intersected: Fields<number> & { tag: string };
declare let required: Record<keyof typeof Keys, number>;
declare const unread: Fields<number>;
optional.value = undefined;
optional["value"] = undefined;
ordinary.value = undefined;
intersected.value = undefined;
optional.value = 1;
const safe: number | undefined = unread.value;
required.value = undefined;
optional.value = "wrong";
ordinary.value = "wrong";
const unsafe: number = unread.value;
"#,
        ScriptKind::TypeScript,
        &["BAMTS-C004"; 4],
    );
}
