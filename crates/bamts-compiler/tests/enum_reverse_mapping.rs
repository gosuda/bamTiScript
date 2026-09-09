//! A numeric enum carries a reverse-mapping index signature at runtime and a
//! string enum does not, so `E[0]` is valid for one and not the other. The
//! binder must settle that classification before member accesses are typed:
//! the enum plan reconciles later, and a late correction cannot retract an
//! accepted access. These cases guard the classification, not its plumbing.

use std::sync::Arc;

use bamts_compiler::{
    checker::check,
    parser, scanner,
    source::{ScriptKind, SourceId, SourceText, TextRange},
};

/// Checker diagnostics for one TypeScript source, lint codes excluded.
fn checker_diagnostics(source: &str) -> Vec<(String, TextRange)> {
    let source_text =
        Arc::new(SourceText::new(source).expect("test source fits the per-file budget"));
    let scanned = scanner::scan(SourceId::new(0), ScriptKind::TypeScript, source_text);
    let checked = check(&parser::parse(scanned));
    checked
        .diagnostics()
        .iter()
        .filter(|diagnostic| diagnostic.code().as_str().starts_with("BAMTS-C"))
        .map(|diagnostic| (diagnostic.code().as_str().to_owned(), diagnostic.range()))
        .collect()
}

fn source_range(source: &str, start: usize, end: usize) -> TextRange {
    let source_text = SourceText::new(source).expect("test source fits the per-file budget");
    source_text
        .range(
            source_text
                .byte_to_utf16(start)
                .expect("diagnostic start is a source boundary"),
            source_text
                .byte_to_utf16(end)
                .expect("diagnostic end is a source boundary"),
        )
        .expect("diagnostic range endpoints are ordered")
}

/// C057 for `E[0]` is anchored on the computed key expression, not on an
/// unrelated diagnostic from an escaped member access in the initializer.
fn e_index_key_range(source: &str) -> TextRange {
    let member_start = source
        .find("E[0]")
        .expect("the regression source contains the E[0] lookup");
    source_range(
        source,
        member_start + "E[".len(),
        member_start + "E[0".len(),
    )
}

fn has_code_at(diagnostics: &[(String, TextRange)], code: &str, range: TextRange) -> bool {
    diagnostics
        .iter()
        .any(|(actual_code, actual_range)| actual_code == code && *actual_range == range)
}

/// Checker diagnostic codes for one TypeScript source, lint codes excluded.
fn checker_codes(source: &str) -> Vec<String> {
    checker_diagnostics(source)
        .into_iter()
        .map(|(code, _)| code)
        .collect()
}

#[test]
fn escaped_intermediate_string_reference_reports_c057_at_e_index() {
    let source = r#"namespace N { export enum F { A = "a" } }
enum E { B = N.\u0046.A }
const v = E[0];
"#;
    let diagnostics = checker_diagnostics(source);
    assert_eq!(
        diagnostics,
        [("BAMTS-C057".to_owned(), e_index_key_range(source))]
    );
}

#[test]
fn escaped_final_string_reference_reports_c057_at_e_index() {
    let source = r#"enum E { A = "a", B = E.\u0041 }
const v = E[0];
"#;
    let diagnostics = checker_diagnostics(source);
    assert_eq!(
        diagnostics,
        [("BAMTS-C057".to_owned(), e_index_key_range(source))]
    );
}

#[test]
fn escaped_member_references_are_clean_without_index_lookup() {
    for source in [
        r#"namespace N { export enum F { A = "a" } }
enum E { B = N.\u0046.A }
"#,
        r#"enum E { A = "a", B = E.\u0041 }
"#,
    ] {
        let diagnostics = checker_diagnostics(source);
        assert!(
            diagnostics.is_empty(),
            "escaped member reference should resolve cleanly: {diagnostics:?}"
        );
    }
}

#[test]
fn escaped_numeric_member_references_do_not_report_c057_at_e_index() {
    for source in [
        r#"namespace N { export enum F { A = 1 } }
enum E { B = N.\u0046.A }
const v = E[0];
"#,
        r#"enum E { A = 1, B = E.\u0041 }
const v = E[0];
"#,
    ] {
        let diagnostics = checker_diagnostics(source);
        assert!(
            diagnostics.is_empty(),
            "numeric escaped member reference should resolve cleanly: {diagnostics:?}"
        );
    }
}

#[test]
fn string_members_reject_a_numeric_lookup() {
    for source in [
        // A bare literal, and the wrappers that leave it a string.
        "enum E { A = \"a\" }\nconst v = E[0];\n",
        "enum E { A = `a` }\nconst v = E[0];\n",
        "enum E { A = (\"a\") }\nconst v = E[0];\n",
        "enum E { A = \"a\" as string }\nconst v = E[0];\n",
        // A reference to an earlier member, bare and qualified.
        "enum E { A = \"a\", B = A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = E.A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = E[\"A\"] }\nconst v = E[0];\n",
        // A member of another enum, which resolves by symbol, whether it
        // is named directly or through a namespace.
        "enum F { A = \"a\" }\nenum E { B = F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = \"a\" } }\nenum E { B = N.F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = \"a\" } }\nenum E { B = N[\"F\"].A }\nconst v = E[0];\n",
        "enum E { A = \"a\" }\nenum E { B = A }\nconst v = E[0];\n",
        // Concatenation is a string when either side is.
        "enum E { A = \"a\", B = A + A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = A + 1 }\nconst v = E[0];\n",
    ] {
        let diagnostics = checker_diagnostics(source);
        assert!(
            has_code_at(&diagnostics, "BAMTS-C057", e_index_key_range(source)),
            "a string enum has no reverse mapping: {source}\n{diagnostics:?}"
        );
    }
}

#[test]
fn numeric_members_keep_their_reverse_mapping() {
    for source in [
        // Auto-numbered, literal, and computed members are all numeric.
        "enum E { A }\nconst v = E[0];\n",
        "enum E { A = 1 }\nconst v = E[0];\n",
        "enum E { A = Math.random() }\nconst v = E[0];\n",
        "enum E { A = 1 << 2 }\nconst v = E[0];\n",
        // A reference resolving to a numeric member stays numeric, whether
        // it names this enum or another one.
        "enum E { A = 1, B = A + A }\nconst v = E[0];\n",
        "enum F { A = 1 }\nenum E { B = F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = 1 } }\nenum E { B = N.F.A }\nconst v = E[0];\n",
        "namespace N { export enum F { A = 1 } }\nenum E { B = N[\"F\"].A }\nconst v = E[0];\n",
        "enum E { A = \"a\", B = 1 }\nconst v = E[0];\n",
    ] {
        assert!(
            checker_codes(source).is_empty(),
            "a numeric enum keeps its reverse mapping: {source}"
        );
    }
}

#[test]
fn an_unresolvable_reference_stays_numeric() {
    // The classification has to be right before the plan runs, so a
    // reference the binder cannot settle keeps the index signature rather
    // than reporting a member that may well exist.
    assert!(
        checker_codes("enum E { A = Unknown.member }\nconst v = E[0];\n")
            .iter()
            .all(|code| code != "BAMTS-C057"),
        "an unsettled reference must not claim the enum is string-valued"
    );
}
