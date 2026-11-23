//! Runtime copies and control flow read the current shape of retained records.

use std::sync::Arc;

use bamts_compiler::{
    checker::{JSX_ATTRIBUTES_NOT_ASSIGNABLE, PROPERTY_DOES_NOT_EXIST, TYPE_NOT_ASSIGNABLE, check},
    diagnostic::DiagnosticSeverity,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn check_codes(source: &str, kind: ScriptKind, expected: &[&str]) {
    let scanned = scanner::scan(
        SourceId::new(0),
        kind,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let parsed = parser::parse(scanned);
    let checked = check(&parsed);
    let codes: Vec<_> = parsed
        .diagnostics()
        .iter()
        .chain(checked.diagnostics())
        .filter(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error)
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert_eq!(codes, expected, "{source}");
}

#[test]
fn jsx_spread_contributes_named_members_of_a_retained_record() {
    check_codes(
        r#"
namespace JSX {
    interface Element {}
    interface IntrinsicElements {
        div: { value: number };
        span: { value: string };
    }
}
class Columns { static value = 1; }
declare const row: Record<keyof typeof Columns, number>;
const accepted = <div {...row} />;
const rejected = <span {...row} />;
"#,
        ScriptKind::TypeScriptReact,
        &[JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()],
    );
}

#[test]
fn object_rest_omits_named_members_of_a_retained_record() {
    check_codes(
        r#"
class Columns { static value = 1; }
declare const row: Record<keyof typeof Columns, number>;
const { value, ...rest } = row;
const taken: number = value;
const kept: number = rest.prototype;
const omitted = rest.value;
"#,
        ScriptKind::TypeScript,
        &[PROPERTY_DOES_NOT_EXIST.as_str()],
    );
}

#[test]
fn in_guard_narrows_a_union_to_a_retained_record() {
    check_codes(
        r#"
class Columns { static value = 1; }
declare const candidate: Record<keyof typeof Columns, number> | { text: string };
if ("value" in candidate) {
    const accepted: number = candidate.value;
    const rejected: string = candidate.value;
} else {
    const other: string = candidate.text;
}
"#,
        ScriptKind::TypeScript,
        &[TYPE_NOT_ASSIGNABLE.as_str()],
    );
}

#[test]
fn in_guard_keeps_optional_object_and_record_members_in_both_branches() {
    check_codes(
        r#"
class Columns { static value = 1; }
declare const record: Partial<Record<keyof typeof Columns, number>> | { text: string };
declare const object: { value?: number } | { text: string };
if (!("value" in record)) {
    const unsafe = record.text;
} else {
    const present: number | undefined = record.value;
}
if (!("value" in object)) {
    const unsafe = object.text;
} else {
    const present: number | undefined = object.value;
}
"#,
        ScriptKind::TypeScript,
        &[PROPERTY_DOES_NOT_EXIST.as_str(); 2],
    );
}

#[test]
fn typeof_object_narrows_a_union_to_a_retained_record() {
    check_codes(
        r#"
class Columns { static value = 1; }
declare const candidate: Record<keyof typeof Columns, number> | string;
if (typeof candidate === "object") {
    const property: number = candidate.value;
} else {
    const text: string = candidate;
}
"#,
        ScriptKind::TypeScript,
        &[],
    );
}
