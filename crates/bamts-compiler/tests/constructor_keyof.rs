//! Constructor key domains retain declaration visibility and name spelling.

use std::sync::Arc;

use bamts_compiler::{
    checker::check,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText},
};

fn checker_codes(source: &str) -> Vec<String> {
    let scanned = scanner::scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
    );
    let checked = check(&parser::parse(scanned));
    checked
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str().to_owned())
        .filter(|code| code.starts_with("BAMTS-C"))
        .collect()
}

fn assert_checks(source: &str) {
    let codes = checker_codes(source);
    assert!(codes.is_empty(), "{codes:?}\n{source}");
}

fn assert_assignment_errors(source: &str, expected: usize) {
    let codes = checker_codes(source);
    assert_eq!(
        codes,
        vec!["BAMTS-C004"; expected],
        "only the deliberate key assignments should fail:\n{source}"
    );
}

#[test]
fn constructor_keys_include_public_statics_and_exclude_non_public_statics() {
    assert_checks(
        r#"
class C {
    static visible = 1;
    private static hidden = 2;
    protected static guarded = 3;
}
class D extends C { static own = 4; }
type K = keyof typeof D;
const visible: K = "visible";
const own: K = "own";
const prototype: K = "prototype";
"#,
    );
    assert_assignment_errors(
        r#"
class C {
    static visible = 1;
    private static hidden = 2;
    protected static guarded = 3;
}
class D extends C {}
const hidden: keyof typeof C = "hidden";
const guarded: keyof typeof C = "guarded";
const inherited: keyof typeof D = "guarded";
"#,
        3,
    );
}

#[test]
fn enum_keys_exclude_reverse_indexes_without_disabling_reverse_reads() {
    assert_checks(
        r#"
enum E { First, Second }
type K = keyof typeof E;
const first: K = "First";
const second: K = "Second";
const reverse: string = E[0];
"#,
    );
    assert_assignment_errors(
        r#"
enum E { First, Second }
const numeric: keyof typeof E = 123;
const reverse: keyof typeof E = "0";
const missing: keyof typeof E = "Missing";
"#,
        3,
    );
}

#[test]
fn heterogeneous_enum_keys_also_exclude_reverse_indexes() {
    assert_checks(
        r#"
enum E { Numeric = 1, Text = "text" }
const numeric: keyof typeof E = "Numeric";
const text: keyof typeof E = "Text";
const reverse: string = E[1];
"#,
    );
    assert_assignment_errors(
        r#"
enum E { Numeric = 1, Text = "text" }
const arbitrary: keyof typeof E = 42;
"#,
        1,
    );
}

#[test]
fn declared_numeric_indexes_still_contribute_number_keys() {
    assert_checks(
        r#"
interface Numbers { [index: number]: string; }
const key: keyof Numbers = 123;
"#,
    );
}

#[test]
fn constructor_keys_distinguish_quoted_and_numeric_declarations() {
    assert_checks(
        r#"
class C {
    static "01" = 1;
    static "1" = 1;
    static 2 = 1;
    static 2.5 = 1;
    static [3] = 1;
    static ["04"] = 1;
    static 5() { return 1; }
    static get 6() { return 1; }
}
class D extends C {}
type K = keyof typeof D;
const leadingZero: K = "01";
const quoted: K = "1";
const numeric: K = 2;
const fractional: K = 2.5;
const computedNumeric: K = 3;
const computedString: K = "04";
const method: K = 5;
const accessor: K = 6;
"#,
    );
    assert_assignment_errors(
        r#"
class C { static "01" = 1; static "1" = 1; static 2 = 1; }
const quotedAsNumber: keyof typeof C = 1;
const numericAsString: keyof typeof C = "2";
"#,
        2,
    );
}

#[test]
fn numeric_key_origin_survives_generic_instantiation() {
    assert_checks(
        r#"
interface Members<T> { "01": T; "1": T; 2: T; 3(): T; }
type K = keyof Members<number>;
const leadingZero: K = "01";
const quoted: K = "1";
const numeric: K = 2;
const method: K = 3;
"#,
    );
    assert_assignment_errors(
        r#"
interface Members<T> { "1": T; 2: T; }
const quotedAsNumber: keyof Members<number> = 1;
const numericAsString: keyof Members<number> = "2";
"#,
        2,
    );
}

#[test]
fn numeric_key_origin_survives_object_spread() {
    assert_checks(
        r#"
const source = { "01": 1, "1": 1, 2: 1, 3() { return 1; } };
const copy = { ...source };
const leadingZero: keyof typeof copy = "01";
const quoted: keyof typeof copy = "1";
const numeric: keyof typeof copy = 2;
const method: keyof typeof copy = 3;
"#,
    );
    assert_assignment_errors(
        r#"
const source = { "1": 1, 2: 1 };
const copy = { ...source };
const quotedAsNumber: keyof typeof copy = 1;
const numericAsString: keyof typeof copy = "2";
"#,
        2,
    );
}

#[test]
fn record_keys_keep_their_literal_kind() {
    assert_checks(
        r#"
type R = Record<"01" | "1" | 2, number>;
const leadingZero: keyof R = "01";
const quoted: keyof R = "1";
const numeric: keyof R = 2;
"#,
    );
}
