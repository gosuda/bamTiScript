//! TypeScript 7 facet comparators and BAMTS↔TS diagnostic code map.
//!
//! Comparators decide conformance parity without false passes:
//!
//! * Diagnostics compare position, category, severity, and BAMTS↔TS code
//!   correspondence. General compiler wording is not exact.
//! * `.types`, `.symbols`, and `.d.ts` compare structurally, never by raw
//!   whitespace/bytes. `.d.ts` parses through the exact BAMTS parser and
//!   canonicalizes from the AST: declaration-set containers (file, namespace,
//!   interface, class, object-type members) reorder only groups with provably
//!   distinct simple identities, while overloads, merge groups, call/construct
//!   signatures, and every positional list keep source order because order is
//!   semantic there. `.types`/`.symbols` use their explicit section/record
//!   schemas with indentation ownership and the same group rule. A baseline
//!   that does not parse without recovery can never pass.
//! * `.js` compares behavioral parity by running programs under a pinned
//!   [`crate::corpus::NodeOracle`] (exactly Node 24.18.0) with corpus timeout
//!   and output limits. Caller-forged [`crate::corpus::OracleOutcome`] values are not a proof
//!   path. Empty stdout cannot pass on its own.
//!
//! The diagnostic code map at [`DIAGNOSTIC_CODE_MAP_PATH`] must enumerate every
//! current `BAMTS-L001…L015`, parser, and checker diagnostic codes.
//! Unmapped entries are first-class evidence, not invented TypeScript codes.

use serde::{Deserialize, Serialize};

mod code_map;
mod diagnostics;
mod js_emit;
mod structural;

pub use code_map::{
    DIAGNOSTIC_CODE_MAP_PATH, DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION, DiagnosticCodeMap,
    DiagnosticCodeMapping, DiagnosticMappingStatus, REQUIRED_BAMTS_DIAGNOSTIC_CODES,
    load_diagnostic_code_map, parse_diagnostic_code_map,
};
pub use diagnostics::compare_diagnostics;
pub use js_emit::{
    VerifiedJsOutcome, compare_declaration_emit, compare_js, compare_js_cases, compare_js_emit,
};
pub use structural::{compare_dts, compare_source_map, compare_symbols, compare_types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FacetVerdict {
    /// Observable parity succeeded under the facet's rule.
    Pass,
    /// Observable mismatch under the facet's rule.
    Fail {
        /// Stable, human-readable mismatch reason.
        reason: String,
    },
    /// Comparison did not prove parity (for example empty JS stdout).
    Unproven {
        /// Stable, human-readable reason parity remains unproven.
        reason: String,
    },
}

impl FacetVerdict {
    /// Returns true only for [`FacetVerdict::Pass`].
    #[must_use]
    pub const fn is_pass(&self) -> bool {
        matches!(self, Self::Pass)
    }

    /// Returns true only for [`FacetVerdict::Fail`].
    #[must_use]
    pub const fn is_fail(&self) -> bool {
        matches!(self, Self::Fail { .. })
    }

    /// Returns true only for [`FacetVerdict::Unproven`].
    #[must_use]
    pub const fn is_unproven(&self) -> bool {
        matches!(self, Self::Unproven { .. })
    }
}

/// TypeScript-compatible diagnostic category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiagnosticCategory {
    Warning,
    Error,
    Suggestion,
    Message,
}

/// Diagnostic severity compared by the diagnostics facet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum FacetSeverity {
    Error,
    Warning,
}

/// Source position compared by the diagnostics facet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct SourcePosition {
    /// 1-based line number.
    pub line: u32,
    /// 0-based character offset within the line.
    pub character: u32,
}

/// One diagnostic observation used by the diagnostics comparator.
///
/// Exact `messageText` is intentionally absent: compiler diagnostic wording is
/// not part of this facet. Node API exact message parity belongs to later units.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct FacetDiagnostic {
    /// Unit basename (`b.ts`) the diagnostic belongs to, so two diagnostics
    /// at the same line/column in different files never compare equal.
    pub unit: String,
    pub position: SourcePosition,
    pub category: DiagnosticCategory,
    pub severity: FacetSeverity,
    /// BAMTS code (`BAMTS-L001`) or TypeScript code (`2304` / `TS2304`).
    pub code: String,
}

fn compare_structural(
    facet: &str,
    expected: &str,
    actual: &str,
    canonicalize: fn(&str) -> Result<Vec<String>, ()>,
) -> FacetVerdict {
    let expected_norm = match canonicalize(expected) {
        Ok(norm) => norm,
        Err(()) => {
            return FacetVerdict::Unproven {
                reason: format!("expected {facet} baseline could not be parsed without recovery"),
            };
        }
    };
    let actual_norm = match canonicalize(actual) {
        Ok(norm) => norm,
        Err(()) => {
            return FacetVerdict::Fail {
                reason: format!("actual {facet} output could not be parsed without recovery"),
            };
        }
    };
    if expected_norm == actual_norm {
        FacetVerdict::Pass
    } else {
        FacetVerdict::Fail {
            reason: format!(
                "{facet} structural mismatch {}",
                describe_difference(&expected_norm, &actual_norm, facet)
            ),
        }
    }
}

/// Longest excerpt of a differing line kept in a reason.
const EXCERPT_CHARS: usize = 100;

/// `[category]: where`, naming the first difference between two normalized
/// outputs. The category is a plain word, so rows that differ the same way group
/// together. The lines themselves sit in backticks, so a family ignores them.
fn describe_difference(expected: &[String], actual: &[String], facet: &str) -> String {
    let common = expected
        .iter()
        .zip(actual)
        .take_while(|(left, right)| left == right)
        .count();
    match (expected.get(common), actual.get(common)) {
        (None, Some(extra)) => {
            let kind = match facet {
                "types" => "extra-record",
                "symbols" => "extra-row",
                _ => "extra-lines",
            };
            format!(
                "[{kind}]: actual has {} extra line(s) from line {}: `{}`",
                actual.len() - common,
                common + 1,
                excerpt(extra)
            )
        }
        (Some(missing), None) => {
            let kind = match facet {
                "types" => "missing-record",
                "symbols" => "missing-row",
                _ => "missing-lines",
            };
            format!(
                "[{kind}]: actual ends at line {common}; expected continues with `{}`",
                excerpt(missing)
            )
        }
        (Some(left), Some(right)) => {
            let mut sorted_expected = expected.to_vec();
            let mut sorted_actual = actual.to_vec();
            sorted_expected.sort();
            sorted_actual.sort();
            let category = if sorted_expected == sorted_actual {
                "order".to_owned()
            } else {
                line_difference(left, right, facet)
            };
            format!(
                "[{category}]: line {} expected `{}` actual `{}`",
                common + 1,
                excerpt(left),
                excerpt(right)
            )
        }
        // The slices differ, so one of them has a line at `common`.
        (None, None) => "[text]: outputs differ".to_owned(),
    }
}

fn line_difference(expected: &str, actual: &str, facet: &str) -> String {
    let unquoted = |text: &str| text.replace('\'', "\"");
    let unpunctuated = |text: &str| text.trim_end_matches([';', ',']).to_owned();
    if (facet == "types" || facet == "symbols")
        && let (Some(left), Some(right)) = (canonical_tokens(expected), canonical_tokens(actual))
    {
        return canvas_difference(facet, &left, &right).to_owned();
    }
    if expected.split_whitespace().eq(actual.split_whitespace()) {
        return "spacing".to_owned();
    }
    if expected.eq_ignore_ascii_case(actual) {
        return "case".to_owned();
    }
    if unquoted(expected) == unquoted(actual) {
        return "quote-style".to_owned();
    }
    if unpunctuated(expected) == unpunctuated(actual) {
        return "punctuation".to_owned();
    }
    let (left, right) = (line_kind(expected), line_kind(actual));
    if left == right {
        "text".to_owned()
    } else {
        format!("{left}-vs-{right}")
    }
}

fn canonical_tokens(line: &str) -> Option<Vec<(&str, &str)>> {
    let mut tokens = Vec::new();
    for part in line.split('|') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let (length, token) = part.split_once(':')?;
        if length.is_empty() || !length.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        tokens.push((length, token));
    }
    if tokens.is_empty() {
        return None;
    }
    Some(tokens)
}

fn canvas_difference(facet: &str, left: &[(&str, &str)], right: &[(&str, &str)]) -> &'static str {
    if left.iter().any(|(_, token)| *token == "===")
        || right.iter().any(|(_, token)| *token == "===")
    {
        return "section-header";
    }
    if strip_caret_tail(left) == strip_caret_tail(right) && left != right {
        return "caret-line";
    }
    let (Some(sep_left), Some(sep_right)) = (separator_index(left), separator_index(right)) else {
        return "type-text";
    };
    if name_range(left, sep_left) != name_range(right, sep_right) {
        if facet == "symbols" {
            return symbol_name_difference(
                left,
                right,
                name_range(left, sep_left),
                name_range(right, sep_right),
            );
        }
        return "record-name";
    }
    if facet == "symbols" && decl_skeleton(left) == decl_skeleton(right) && left != right {
        return "decl-position";
    }
    if rendered_has_any(right, sep_right) && !rendered_has_any(left, sep_left) {
        return "type-any";
    }
    "type-text"
}

fn strip_caret_tail<'t>(tokens: &'t [(&'t str, &'t str)]) -> &'t [(&'t str, &'t str)] {
    let mut end = tokens.len();
    while end > 0 && tokens[end - 1].1 == "^" {
        end -= 1;
    }
    if end > 0 && tokens[end - 1].1 == ":" {
        end -= 1;
    }
    &tokens[..end]
}

fn separator_index(tokens: &[(&str, &str)]) -> Option<usize> {
    tokens.iter().position(|(_, token)| *token == ":")
}

fn name_range<'t>(tokens: &'t [(&'t str, &'t str)], sep: usize) -> &'t [(&'t str, &'t str)] {
    let start = usize::from(!tokens.is_empty() && tokens[0].1 == ">");
    &tokens[start..sep]
}

fn symbol_name_difference(
    left: &[(&str, &str)],
    right: &[(&str, &str)],
    name_left: &[(&str, &str)],
    name_right: &[(&str, &str)],
) -> &'static str {
    if name_right.is_empty() {
        return "symbol-name-empty-actual";
    }
    if name_left.is_empty() {
        return "symbol-name-empty-expected";
    }
    match (
        left.first().is_some_and(|(_, token)| *token == ">"),
        right.first().is_some_and(|(_, token)| *token == ">"),
    ) {
        (true, false) => "symbol-row-vs-source",
        (false, true) => "source-vs-symbol-row",
        _ => "symbol-name",
    }
}

fn rendered_has_any(tokens: &[(&str, &str)], sep: usize) -> bool {
    tokens[sep..].iter().any(|(_, token)| *token == "any")
}

fn decl_skeleton<'t>(tokens: &[(&'t str, &'t str)]) -> Vec<&'t str> {
    let mut skeleton = Vec::new();
    let mut index = 0;
    while index < tokens.len() {
        if tokens[index].1 == "Decl" && tokens.get(index + 1).is_some_and(|next| next.1 == "(") {
            skeleton.push("Decl(..)");
            let mut depth = 0;
            while index < tokens.len() {
                if tokens[index].1 == "(" {
                    depth += 1;
                }
                if tokens[index].1 == ")" {
                    depth -= 1;
                    if depth == 0 {
                        index += 1;
                        break;
                    }
                }
                index += 1;
            }
            continue;
        }
        skeleton.push(tokens[index].1);
        index += 1;
    }
    skeleton
}

/// The kind of JavaScript line, from its first token. A small closed set, so
/// the pairs a mismatch can name stay few.
fn line_kind(line: &str) -> &'static str {
    const KINDS: [(&str, &[&str]); 10] = [
        ("comment", &["//", "/*", "*"]),
        ("import", &["import "]),
        ("export", &["export "]),
        ("declare", &["declare "]),
        ("binding", &["var ", "let ", "const "]),
        ("function", &["function ", "async function "]),
        ("class", &["class ", "abstract class "]),
        ("strict", &["\"use strict\"", "'use strict'"]),
        ("brace", &["}", "{", ")", "]"]),
        (
            "cjs",
            &[
                "exports.",
                "module.exports",
                "Object.defineProperty(exports",
            ],
        ),
    ];
    let line = line.trim();
    if line.is_empty() {
        return "blank";
    }
    KINDS
        .iter()
        .find(|(_, prefixes)| prefixes.iter().any(|prefix| line.starts_with(prefix)))
        .map_or("other", |(kind, _)| kind)
}

/// A line cut to a readable length, with backticks replaced so it can sit in one.
fn excerpt(line: &str) -> String {
    let line = line.trim().replace('`', "'");
    if line.chars().count() <= EXCERPT_CHARS {
        return line;
    }
    let mut cut: String = line.chars().take(EXCERPT_CHARS).collect();
    cut.push('…');
    cut
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::BTreeMap, fs, path::Path};
    use crate::ErrorCode;
    use crate::corpus::{CaseSpec, NodeOracle, OracleOutcome, Provenance};

    fn js_reason(expected: &str, actual: &str) -> String {
        match compare_js_emit(expected, actual) {
            FacetVerdict::Fail { reason } => reason,
            other => panic!("a difference must fail, got {other:?}"),
        }
    }

    #[test]
    fn a_mismatch_names_its_category_and_the_first_differing_line() {
        let cases: [(&str, &str, &str, &[&str]); 12] = [
            (
                "a\nb",
                "a\nb\nc\nd",
                "extra-lines",
                &["2 extra line(s) from line 3", "`c`"],
            ),
            (
                "a\nb\nc",
                "a\nb",
                "missing-lines",
                &["ends at line 2", "`c`"],
            ),
            (
                "a\nb\nc",
                "a\nc\nb",
                "order",
                &["line 2", "expected `b`", "actual `c`"],
            ),
            (
                "var x = 1;",
                "var  x =  1;",
                "spacing",
                &["line 1", "expected `var x = 1;`"],
            ),
            ("let s = 'a';", "let s = \"a\";", "quote-style", &["line 1"]),
            (
                "f()",
                "f();",
                "punctuation",
                &["expected `f()`", "actual `f();`"],
            ),
            ("Foo();", "foo();", "case", &["line 1"]),
            (
                "ok\na = 1;",
                "ok\na = 2;",
                "text",
                &["line 2", "expected `a = 1;`", "actual `a = 2;`"],
            ),
            (
                "// note\nok",
                "var x = 1;\nok",
                "comment-vs-binding",
                &["line 1", "expected `// note`"],
            ),
            (
                "class C {",
                "var C = (function () {",
                "class-vs-binding",
                &["line 1"],
            ),
            (
                "exports.a = 1;",
                "var a = 1;",
                "cjs-vs-binding",
                &["actual `var a = 1;`"],
            ),
            (
                "var x = 1;",
                "export var x = 1;",
                "binding-vs-export",
                &["line 1"],
            ),
        ];
        for (expected, actual, category, mentions) in cases {
            let reason = js_reason(expected, actual);
            assert!(
                reason.starts_with(&format!("javascript structural mismatch [{category}]: ")),
                "{category}: {reason}"
            );
            for mention in mentions {
                assert!(reason.contains(mention), "{category}: {reason}");
            }
        }
    }

    #[test]
    fn a_mismatch_stays_a_failure_and_equal_output_still_passes() {
        assert!(compare_js_emit("a = 1;", "a = 2;").is_fail());
        assert!(compare_js_emit("a = 1;\r\n", "a = 1;  \n").is_pass());
    }

    #[test]
    fn a_reason_excerpts_long_lines_and_never_nests_backticks() {
        let long = "x".repeat(400);
        let reason = js_reason("ok", &format!("ok\n{long}"));
        assert!(reason.len() < 200, "{} bytes: {reason}", reason.len());
        let tick = js_reason("a `b` c", "a `d` c");
        assert_eq!(tick.matches('`').count() % 2, 0, "{tick}");
        assert!(!tick.contains("`b`"), "{tick}");
    }

    #[test]
    fn rows_that_differ_in_category_not_in_content_share_a_family() {
        use crate::sweep_report::family_name;
        let family =
            |expected: &str, actual: &str| family_name("javascript", &js_reason(expected, actual));
        assert_eq!(
            family("a = 1;", "a = 2;"),
            family("return f(x);", "return g(y);")
        );
        assert_eq!(family("f()", "f();"), family("g(1, 2)", "g(1, 2);"));
        assert_ne!(family("a = 1;", "a = 2;"), family("f()", "f();"));
        assert_eq!(
            family("// a", "var x = 1;"),
            family("// b c", "let y = f(z);")
        );
        assert_ne!(family("// a", "var x = 1;"), family("// a", "class X {"));
        assert_ne!(family("// a", "var x = 1;"), family("var x = 1;", "// a"));
        assert_ne!(family("a\nb", "a\nb\nc"), family("a\nb\nc", "a\nb"));
    }

    fn empty_map_json(entries: &[(&str, DiagnosticMappingStatus, Option<u32>)]) -> String {
        let evidence = "fixture evidence";
        let mut items = Vec::new();
        for (code, status, ts_code) in entries {
            let status = match status {
                DiagnosticMappingStatus::Mapped => "mapped",
                DiagnosticMappingStatus::Unmapped => "unmapped",
            };
            let ts = match ts_code {
                Some(value) => value.to_string(),
                None => "null".to_owned(),
            };
            items.push(format!(
                concat!(
                    "{{\"bamtsCode\":\"{code}\",\"evidence\":\"{evidence}\",",
                    "\"status\":\"{status}\",\"tsCode\":{ts}}}"
                ),
                code = code,
                evidence = evidence,
                status = status,
                ts = ts
            ));
        }
        format!("{{\"schemaVersion\":1,\"entries\":[{}]}}", items.join(","))
    }

    fn complete_unmapped_json() -> String {
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| (*code, DiagnosticMappingStatus::Unmapped, None))
                .collect();
        empty_map_json(&entries)
    }

    fn with_mapped(bamts: &str, ts_code: u32) -> String {
        with_mappings(&[(bamts, ts_code)])
    }

    fn with_mappings(mappings: &[(&str, u32)]) -> String {
        let mapped: BTreeMap<&str, u32> = mappings.iter().copied().collect();
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| match mapped.get(code) {
                    Some(ts_code) => (*code, DiagnosticMappingStatus::Mapped, Some(*ts_code)),
                    None => (*code, DiagnosticMappingStatus::Unmapped, None),
                })
                .collect();
        empty_map_json(&entries)
    }

    fn diag(
        line: u32,
        character: u32,
        category: DiagnosticCategory,
        severity: FacetSeverity,
        code: &str,
    ) -> FacetDiagnostic {
        FacetDiagnostic {
            unit: String::new(),
            position: SourcePosition { line, character },
            category,
            severity,
            code: code.to_owned(),
        }
    }

    fn outcome(stdout: &[u8], exit_code: i32) -> OracleOutcome {
        OracleOutcome {
            timed_out: false,
            exit_code: Some(exit_code),
            signal: None,
            stdout: stdout.to_vec(),
            stdout_truncated: false,
            stderr: Vec::new(),
            stderr_truncated: false,
            compile_stderr: Vec::new(),
            compile_stderr_truncated: false,
        }
    }

    fn verified(stdout: &[u8], exit_code: i32) -> VerifiedJsOutcome {
        // Test-only seam for parity-key logic. Production proof requires
        // [`VerifiedJsOutcome::capture`] through a pinned [`NodeOracle`].
        VerifiedJsOutcome {
            outcome: outcome(stdout, exit_code),
        }
    }

    fn fixture_case(id: &str, entrypoint: &str) -> CaseSpec {
        CaseSpec {
            id: id.to_owned(),
            provenance: Provenance::ExternalGit {
                repository: format!("https://example.com/{id}"),
                commit: "a".repeat(40),
            },
            license: "MIT".into(),
            source_dir: format!("projects/{id}"),
            entrypoint: entrypoint.to_owned(),
            node_args: Vec::new(),
            expected_timeout_ms: 5_000,
            constructs: vec!["fixture".into()],
            source_files: vec![entrypoint.to_owned()],
            compiler_args: Vec::new(),
        }
    }

    #[test]
    fn diagnostic_count_mismatches_label_unmatched_codes_and_direction() {
        let map = parse_diagnostic_code_map(&with_mapped("BAMTS-C002", 2304)).unwrap();
        let diagnostic = |code| diag(1, 0, DiagnosticCategory::Error, FacetSeverity::Error, code);
        let matched = diagnostic("BAMTS-C002");
        let canonical = diagnostic("TS2304");
        for code in ["TS2322", "TS2345", "BAMTS-L001"] {
            let unmatched = diagnostic(code);
            let expected = [unmatched.clone(), matched.clone()];
            let actual = [canonical.clone()];
            assert_eq!(
                compare_diagnostics(&expected, &actual, &map),
                FacetVerdict::Fail {
                    reason: format!(
                        "diagnostic count mismatch [missing {code}]: expected 2 actual 1"
                    )
                }
            );
            assert_eq!(
                compare_diagnostics(&actual, &expected, &map),
                FacetVerdict::Fail {
                    reason: format!(
                        "diagnostic count mismatch [extra {code}]: expected 1 actual 2"
                    )
                }
            );
            assert_eq!(
                compare_diagnostics(&[unmatched], &[], &map),
                FacetVerdict::Fail {
                    reason: format!(
                        "diagnostic count mismatch [missing {code}]: expected 1 actual 0"
                    )
                }
            );
        }
    }

    #[test]
    fn diagnostic_count_labels_cancel_aliases_one_for_one_and_ignore_input_order() {
        let map = parse_diagnostic_code_map(&with_mapped("BAMTS-C002", 2304)).unwrap();
        let diagnostic = |code| diag(1, 0, DiagnosticCategory::Error, FacetSeverity::Error, code);
        let expected = [
            diagnostic("BAMTS-C002"),
            diagnostic("TS2304"),
            diagnostic("TS9999"),
        ];
        let actual = [diagnostic("2304"), diagnostic("TS9999")];
        let verdict = FacetVerdict::Fail {
            reason: "diagnostic count mismatch [missing TS2304]: expected 3 actual 2".into(),
        };
        assert_eq!(compare_diagnostics(&expected, &actual, &map), verdict);
        let mut reversed = expected.clone();
        reversed.reverse();
        assert_eq!(compare_diagnostics(&reversed, &actual, &map), verdict);
        assert!(compare_diagnostics(&expected[..1], &actual[..1], &map).is_pass());
        assert!(matches!(
            compare_diagnostics(&expected[..1], &actual[1..], &map),
            FacetVerdict::Fail { reason }
                if reason == "diagnostic[0] code correspondence mismatch: `BAMTS-C002` vs `TS9999`"
        ));
    }

    #[test]
    fn diagnostics_match_on_position_category_severity_and_code() {
        let map = parse_diagnostic_code_map(&complete_unmapped_json()).unwrap();
        let expected = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let actual = expected.clone();
        assert!(compare_diagnostics(&expected, &actual, &map).is_pass());
    }

    #[test]
    fn diagnostics_mismatch_by_position() {
        let map = parse_diagnostic_code_map(&complete_unmapped_json()).unwrap();
        let expected = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let actual = [diag(
            2,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let verdict = compare_diagnostics(&expected, &actual, &map);
        assert!(verdict.is_fail());
        assert!(format!("{verdict:?}").contains("position"));
    }

    #[test]
    fn diagnostics_mismatch_by_category() {
        let map = parse_diagnostic_code_map(&complete_unmapped_json()).unwrap();
        let expected = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let actual = [diag(
            1,
            0,
            DiagnosticCategory::Warning,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let verdict = compare_diagnostics(&expected, &actual, &map);
        assert!(verdict.is_fail());
        assert!(format!("{verdict:?}").contains("category"));
    }

    #[test]
    fn diagnostics_mismatch_by_severity() {
        let map = parse_diagnostic_code_map(&complete_unmapped_json()).unwrap();
        let expected = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let actual = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Warning,
            "BAMTS-L001",
        )];
        let verdict = compare_diagnostics(&expected, &actual, &map);
        assert!(verdict.is_fail());
        assert!(format!("{verdict:?}").contains("severity"));
    }

    #[test]
    fn diagnostics_mismatch_by_unmapped_code_identity() {
        let map = parse_diagnostic_code_map(&complete_unmapped_json()).unwrap();
        let expected = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-L001",
        )];
        let actual = [diag(
            1,
            0,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "1002",
        )];
        let verdict = compare_diagnostics(&expected, &actual, &map);
        assert!(verdict.is_fail());
        assert!(format!("{verdict:?}").contains("code correspondence"));
    }

    #[test]
    fn diagnostics_match_through_documented_code_correspondence() {
        let map = parse_diagnostic_code_map(&with_mapped("BAMTS-C002", 2304)).unwrap();
        let expected = [diag(
            4,
            2,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "BAMTS-C002",
        )];
        let actual = [diag(
            4,
            2,
            DiagnosticCategory::Error,
            FacetSeverity::Error,
            "TS2304",
        )];
        assert!(compare_diagnostics(&expected, &actual, &map).is_pass());
    }

    #[test]
    fn diagnostics_match_when_typescript_codes_reverse_bamts_lexical_order() {
        // BAMTS-C001 < BAMTS-C002, but mapped TS100/TS99 sort as TS100 < TS99.
        // Sorting raw code strings before zip falsely fails this valid set.
        let map =
            parse_diagnostic_code_map(&with_mappings(&[("BAMTS-C001", 99), ("BAMTS-C002", 100)]))
                .unwrap();
        let expected = [
            diag(
                1,
                0,
                DiagnosticCategory::Error,
                FacetSeverity::Error,
                "BAMTS-C001",
            ),
            diag(
                1,
                0,
                DiagnosticCategory::Error,
                FacetSeverity::Error,
                "BAMTS-C002",
            ),
        ];
        let actual = [
            diag(
                1,
                0,
                DiagnosticCategory::Error,
                FacetSeverity::Error,
                "TS100",
            ),
            diag(
                1,
                0,
                DiagnosticCategory::Error,
                FacetSeverity::Error,
                "TS99",
            ),
        ];
        assert!(compare_diagnostics(&expected, &actual, &map).is_pass());
    }

    #[test]
    fn types_labels_name_the_kind_but_keep_the_verdict() {
        let passing = compare_types(
            "=== anyPropertyAccess.ts ===\n>var x: any\n",
            "=== anyPropertyAccess.ts ===\n>var x: any\n",
        );
        assert!(passing.is_pass());
        let failing = compare_types(">a : any\n", ">b : any\n");
        match &failing {
            FacetVerdict::Fail { reason } => {
                assert!(reason.contains("[record-name]"), "{reason}")
            }
            other => panic!("expected Fail, got {other:?}"),
        }
        assert!(failing.is_fail());
        let passing = compare_symbols(
            "=== aliasUsedAsNameValue_2.ts ===\n>b : Symbol(b, Decl(aliasUsedAsNameValue_2.ts, 2, 49))\n",
            "=== aliasUsedAsNameValue_2.ts ===\n>b : Symbol(b, Decl(aliasUsedAsNameValue_2.ts, 2, 49))\n",
        );
        assert!(passing.is_pass());
        let failing = compare_symbols(
            ">a : Symbol(a, Decl(aliasUsedAsNameValue_2.ts, 5, 10))\n",
            ">a : Symbol(a, Decl(aliasUsedAsNameValue_1.ts, 0, 18))\n",
        );
        match &failing {
            FacetVerdict::Fail { reason } => {
                assert!(reason.contains("[decl-position]"), "{reason}")
            }
            other => panic!("expected Fail, got {other:?}"),
        }
        assert!(failing.is_fail());
    }

    #[test]
    fn types_differences_name_their_kind() {
        let cases: [(&str, &str, &str); 7] = [
            (
                "section-header",
                "=== anyPropertyAccess.ts ===\n",
                "=== incrementOperatorWithAnyOtherType.ts ===\n",
            ),
            (
                "caret-line",
                ">x : any\n>  : ^^^\n",
                ">x : any\n>  : ^^^^^^\n",
            ),
            ("record-name", ">a : any\n", ">b : any\n"),
            ("type-any", ">y : null\n", ">y : any\n"),
            ("type-text", ">x : number\n", ">x : string\n"),
            (
                "missing-record",
                "=== anyPropertyAccess.ts ===\n>a : any\n",
                "=== anyPropertyAccess.ts ===\n",
            ),
            (
                "extra-record",
                "=== anyPropertyAccess.ts ===\n",
                "=== anyPropertyAccess.ts ===\n>a : any\n",
            ),
        ];
        for (label, expected, actual) in cases {
            let verdict = compare_types(expected, actual);
            match &verdict {
                FacetVerdict::Fail { reason } => {
                    assert!(
                        reason.contains(&format!("[{label}]")),
                        "expected [{label}] in {reason}"
                    );
                }
                other => panic!("{label}: expected Fail, got {other:?}"),
            }
            assert!(verdict.is_fail());
        }
    }

    #[test]
    fn symbols_differences_name_their_kind() {
        let cases: [(&str, &str, &str); 5] = [
            (
                "section-header",
                "=== anyPropertyAccess.ts ===\n",
                "=== aliasUsedAsNameValue_2.ts ===\n",
            ),
            (
                "symbol-name",
                ">b : Symbol(b, Decl(aliasUsedAsNameValue_2.ts, 2, 49))\n",
                ">mod : Symbol(mod, Decl(aliasUsedAsNameValue_2.ts, 0, 0))\n",
            ),
            (
                "decl-position",
                ">a : Symbol(a, Decl(aliasUsedAsNameValue_2.ts, 5, 10))\n",
                ">a : Symbol(a, Decl(aliasUsedAsNameValue_1.ts, 0, 18))\n",
            ),
            (
                "missing-row",
                "=== anyPropertyAccess.ts ===\n>d : Symbol(d, Decl(anyPropertyAccess.ts, 4, 3))\n",
                "=== anyPropertyAccess.ts ===\n",
            ),
            (
                "extra-row",
                "=== anyPropertyAccess.ts ===\n",
                "=== anyPropertyAccess.ts ===\n>d : Symbol(d, Decl(anyPropertyAccess.ts, 4, 3))\n",
            ),
        ];
        for (label, expected, actual) in cases {
            let verdict = compare_symbols(expected, actual);
            match &verdict {
                FacetVerdict::Fail { reason } => {
                    assert!(
                        reason.contains(&format!("[{label}]")),
                        "expected [{label}] in {reason}"
                    );
                }
                other => panic!("{label}: expected Fail, got {other:?}"),
            }
            assert!(verdict.is_fail());
        }
    }

    #[test]
    fn symbols_name_mismatches_split_observed_shapes() {
        let empty_actual = compare_symbols(
            ">arg : Symbol(arg, Decl(invalidUnicodeEscapeSequance.ts, 0, 3))\n",
            "> : Symbol(, Decl(invalidUnicodeEscapeSequance.ts, 0, 3))\n",
        );
        let empty_expected = compare_symbols(
            "> : Symbol((Missing), Decl(FunctionPropertyAssignments4_es6.ts, 0, 9))\n",
            ">v : Symbol(v, Decl(FunctionPropertyAssignments4_es6.ts, 0, 3))\n",
        );
        let row_vs_source = compare_symbols(
            ">v : Symbol(v, Decl(parservoidInQualifiedName1.ts, 0, 3))\n\
             >x : Symbol(x, Decl(parservoidInQualifiedName1.ts, 0, 13))\n",
            ">v : Symbol(v, Decl(parservoidInQualifiedName1.ts, 0, 3))\n\
             var v : void.x;\n",
        );
        let ordinary = compare_symbols(
            ">b : Symbol(b, Decl(aliasUsedAsNameValue_2.ts, 2, 49))\n",
            ">mod : Symbol(mod, Decl(aliasUsedAsNameValue_2.ts, 0, 0))\n",
        );
        let punctuation = compare_symbols(
            ">\"\" : Symbol(\"\", Decl(quoted.ts, 0, 4))\n",
            ">\"?\" : Symbol(\"?\", Decl(quoted.ts, 0, 4))\n",
        );
        let labels = [
            ("symbol-name-empty-actual", &empty_actual),
            ("symbol-name-empty-expected", &empty_expected),
            ("symbol-row-vs-source", &row_vs_source),
            ("symbol-name", &ordinary),
            ("symbol-name", &punctuation),
        ];
        for (label, verdict) in labels {
            match verdict {
                FacetVerdict::Fail { reason } => {
                    assert!(
                        reason.contains(&format!("[{label}]")),
                        "expected [{label}] in {reason}"
                    );
                }
                other => panic!("{label}: expected Fail, got {other:?}"),
            }
        }
    }

    #[test]
    fn symbols_source_line_against_symbol_row_names_the_reverse() {
        let verdict = compare_symbols(
            "var v : void.x;\n",
            ">v : Symbol(v, Decl(parservoidInQualifiedName1.ts, 0, 3))\n\
             >x : Symbol(x, Decl(parservoidInQualifiedName1.ts, 0, 13))\n",
        );
        match &verdict {
            FacetVerdict::Fail { reason } => {
                assert!(reason.contains("[source-vs-symbol-row]"), "{reason}")
            }
            other => panic!("expected Fail, got {other:?}"),
        }
    }

    #[test]
    fn structural_symbols_survive_formatting_and_order_normalization() {
        let expected = "[Global]\n  x : Symbol(x)\n  y : Symbol(y)\n";
        let actual = "[Global]\n  y :   Symbol(y)\n\n  x : Symbol(x)\n";
        assert!(compare_symbols(expected, actual).is_pass());
    }

    #[test]
    fn structural_symbols_reject_semantic_differences() {
        let expected = "x : Symbol(x)\n";
        let actual = "x : Symbol(z)\n";
        assert!(compare_symbols(expected, actual).is_fail());
    }

    #[test]
    fn structural_symbols_handle_multiple_sections_without_cross_section_leak() {
        // Records from one section must not bleed into the next.
        let expected = "[Global]\n  x : Symbol(x)\n[File: a.ts]\n  y : Symbol(y)\n";
        let actual = "[Global]\n  x : Symbol(x)\n[File: a.ts]\n  z : Symbol(z)\n";
        assert!(compare_symbols(expected, actual).is_fail());
        assert!(compare_symbols(expected, expected).is_pass());
    }

    #[test]
    fn structural_source_map_normalizes_key_order_and_whitespace() {
        // Upstream's baseliner writes compact single-line JSON; key order and
        // in-line whitespace carry no map meaning.
        let expected = "{\"version\":3,\"file\":\"a.js\",\"sources\":[\"a.ts\"],\"names\":[],\"mappings\":\"AAAA\"}";
        let actual = "{ \"mappings\" : \"AAAA\", \"names\" : [], \"sources\" : [\"a.ts\"], \"file\" : \"a.js\", \"version\" : 3 }";
        assert!(compare_source_map(expected, actual).is_pass());
    }

    #[test]
    fn structural_source_map_normalizes_empty_sourceroot() {
        // Upstream always serializes `sourceRoot` (empty when unset); absent
        // and empty carry the same map meaning.
        let expected =
            "{\"version\":3,\"sourceRoot\":\"\",\"sources\":[\"a.ts\"],\"mappings\":\"AAAA\"}";
        let actual = "{\"mappings\":\"AAAA\",\"sources\":[\"a.ts\"],\"version\":3}";
        assert!(compare_source_map(expected, actual).is_pass());
    }

    #[test]
    fn structural_source_map_preserves_mappings_and_array_order() {
        let expected = "{\"version\":3,\"sources\":[\"a.ts\",\"b.ts\"],\"mappings\":\"AAAA;ACDE\"}";
        let reordered_sources =
            "{\"version\":3,\"sources\":[\"b.ts\",\"a.ts\"],\"mappings\":\"AAAA;ACDE\"}";
        let changed_mappings =
            "{\"version\":3,\"sources\":[\"a.ts\",\"b.ts\"],\"mappings\":\"AAAA;ACDF\"}";
        assert!(compare_source_map(expected, expected).is_pass());
        assert!(compare_source_map(expected, reordered_sources).is_fail());
        assert!(compare_source_map(expected, changed_mappings).is_fail());
    }

    #[test]
    fn structural_source_map_never_passes_unparseable_json() {
        let malformed = "{\"version\":3,";
        let valid = "{\"version\":3}";
        assert!(compare_source_map(malformed, valid).is_unproven());
        assert!(compare_source_map(valid, malformed).is_fail());
    }

    #[test]
    fn structural_dts_ignores_comments_and_whitespace_but_not_tokens() {
        let expected = "export declare const x: number;\nexport declare const y: string;\n";
        let actual =
            "export declare const y: string;\n/* note */\nexport   declare  const  x: number;\n";
        assert!(compare_dts(expected, actual).is_pass());

        let semantic = "export declare const x: string;\n";
        assert!(compare_dts(expected, semantic).is_fail());
    }

    #[test]
    fn structural_dts_normalizes_punctuation_whitespace_without_merging_tokens() {
        let compact = "interface A{x:string;literal:\"a b\";}";
        let spaced = "interface A { x : string ; literal : \"a b\" ; }";
        assert!(compare_dts(compact, spaced).is_pass());

        let changed_literal = "interface A { x : string; literal: \"ab\"; }";
        assert!(compare_dts(compact, changed_literal).is_fail());

        let compact_optional = "interface A { x?: string; }";
        let spaced_optional = "interface A { x? : string; }";
        assert!(compare_dts(compact_optional, spaced_optional).is_pass());

        let adjacent_arrow = "type F = (x: string) => number;";
        let split_arrow = "type F = (x: string) = > number;";
        assert!(compare_dts(adjacent_arrow, split_arrow).is_fail());
    }

    #[test]
    fn structural_dts_preserves_semantic_triple_slash_references() {
        let node = "/// <reference types=\"node\" />\nexport declare const x: number;\n";
        let bun = "/// <reference types=\"bun\" />\nexport declare const x: number;\n";
        let absent = "export declare const x: number;\n";
        assert!(compare_dts(node, bun).is_fail());
        assert!(compare_dts(node, absent).is_fail());

        let comment = "/// implementation note\nexport declare const x: number;\n";
        assert!(compare_dts(comment, absent).is_pass());
    }

    #[test]
    fn structural_dts_preserves_function_overload_order() {
        // `ReturnType<typeof f>` observes the LAST overload, so reversing the
        // overloads changes the declaration program; the comparator must fail.
        let expected =
            "declare function f(x: string): \"s\";\ndeclare function f(x: number): \"n\";\n";
        let reversed =
            "declare function f(x: number): \"n\";\ndeclare function f(x: string): \"s\";\n";
        assert!(compare_dts(expected, reversed).is_fail());

        // A different function still sorts as a distinct declaration.
        let with_g = "declare function f(x: string): \"s\";\ndeclare function g(): void;\n";
        let reordered = "declare function g(): void;\ndeclare function f(x: string): \"s\";\n";
        assert!(compare_dts(with_g, reordered).is_pass());
    }

    #[test]
    fn structural_dts_preserves_cross_kind_merge_order() {
        // `function build` + `namespace build` merge into one symbol with an
        // ordering constraint; swapping them must fail.
        let expected = "declare function build(x: string): \"s\";\ndeclare namespace build {\n  const version: string;\n}\n";
        let reversed = "declare namespace build {\n  const version: string;\n}\ndeclare function build(x: string): \"s\";\n";
        assert!(compare_dts(expected, reversed).is_fail());
    }

    #[test]
    fn structural_dts_preserves_interface_call_signature_order() {
        // Call signatures on an interface are overloads: the last one wins for
        // `ReturnType<F>`, so their order is semantic.
        let expected = "interface F {\n  (x: string): \"s\";\n  (x: number): \"n\";\n}\n";
        let reversed = "interface F {\n  (x: number): \"n\";\n  (x: string): \"s\";\n}\n";
        assert!(compare_dts(expected, reversed).is_fail());

        // Distinct named members still sort.
        let members_a = "interface F {\n  x: string;\n  y: number;\n}\n";
        let members_b = "interface F {\n  y: number;\n  x: string;\n}\n";
        assert!(compare_dts(members_a, members_b).is_pass());
    }

    #[test]
    fn structural_dts_preserves_intersection_constituent_order() {
        // Intersection constituent order is observable through ReturnType
        // overload resolution; reversing the constituents must fail.
        let expected = "type F = ((x: string) => \"s\") & ((x: number) => \"n\");\n";
        let reversed = "type F = ((x: number) => \"n\") & ((x: string) => \"s\");\n";
        assert!(compare_dts(expected, reversed).is_fail());
    }

    #[test]
    fn structural_dts_preserves_triple_slash_prologue_order() {
        let a_then_b = "/// <reference path=\"a.d.ts\" />\n/// <reference path=\"b.d.ts\" />\ndeclare function f(): void;\n";
        let b_then_a = "/// <reference path=\"b.d.ts\" />\n/// <reference path=\"a.d.ts\" />\ndeclare function f(): void;\n";
        assert!(compare_dts(a_then_b, b_then_a).is_fail());
    }

    #[test]
    fn structural_dts_does_not_truncate_template_literal_types() {
        // `//` inside a template-literal type is text, not a comment: the two
        // types differ and must not collapse to the same prefix.
        let expected = "type A = `https://x.com/a`;\n";
        let actual = "type A = `https://y.org/b`;\n";
        assert!(compare_dts(expected, actual).is_fail());
        assert!(compare_dts(expected, expected).is_pass());
    }

    #[test]
    fn structural_dts_does_not_truncate_block_comment_text_in_templates() {
        let expected = "type A = `foo /*a*/ bar`;\n";
        let actual = "type A = `foo /*b*/ bar`;\n";
        assert!(compare_dts(expected, actual).is_fail());
    }

    #[test]
    fn structural_types_preserves_function_overload_order() {
        // Overload resolution observes the last signature, so reversing two
        // same-name records must fail.
        let expected =
            "=== a.ts ===\n> function f(a: string): \"s\"\n> function f(b: number): \"n\"\n";
        let reversed =
            "=== a.ts ===\n> function f(b: number): \"n\"\n> function f(a: string): \"s\"\n";
        assert!(compare_types(expected, reversed).is_fail());

        // Distinct names still sort.
        let distinct_a = "=== a.ts ===\n> function g(): void\n> function f(): void\n";
        let distinct_b = "=== a.ts ===\n> function f(): void\n> function g(): void\n";
        assert!(compare_types(distinct_a, distinct_b).is_pass());
    }

    #[test]
    fn structural_types_preserves_nested_owner_members() {
        // A member hoisted out of its owner type is a semantic difference.
        let expected = "=== a.ts ===\n> type TypeC = {\n>   memberA: number;\n> }\n";
        let hoisted = "=== a.ts ===\n>   memberA: number;\n> type TypeC = {\n> }\n";
        assert!(compare_types(expected, hoisted).is_fail());
        assert!(compare_types(expected, expected).is_pass());
    }

    #[test]
    fn structural_dts_canonicalizes_parameter_object_members() {
        let expected = "interface I { m(p: { a: string; b: number }): void; }\n";
        let swapped = "interface I { m(p: { b: number; a: string }): void; }\n";
        assert!(compare_dts(expected, swapped).is_pass());

        let index_expected = "interface I { [k: string]: { a: string; b: number }; }\n";
        let index_swapped = "interface I { [k: string]: { b: number; a: string }; }\n";
        assert!(compare_dts(index_expected, index_swapped).is_pass());
    }

    #[test]
    fn structural_dts_canonicalizes_variable_annotations() {
        let expected = "declare const x: { a: string; b: number };\n";
        let swapped = "declare const x: { b: number; a: string };\n";
        assert!(compare_dts(expected, swapped).is_pass());
    }

    #[test]
    fn structural_dts_normalizes_nested_generic_angle_brackets() {
        let compact = "type T = A<B<C>>;\n";
        let spaced = "type T = A<B<C> >;\n";
        assert!(compare_dts(compact, spaced).is_pass());
        assert!(compare_dts(compact, compact).is_pass());
    }

    #[test]
    fn structural_dts_equates_dotted_and_explicit_namespaces() {
        let dotted = "namespace A.B { export interface I {} }\n";
        let explicit = "namespace A { namespace B { export interface I {} } }\n";
        assert!(compare_dts(dotted, explicit).is_pass());
    }

    #[test]
    fn structural_dts_ignores_inert_triple_slash_outside_prologue() {
        // A directive inside a namespace body is inert in TypeScript.
        let clean = "namespace N { interface A {} }\n";
        let with_directive = "namespace N { /// <reference path=\"x\" />\ninterface A {} }\n";
        assert!(compare_dts(clean, with_directive).is_pass());

        let tail_directive = "namespace N {\ninterface A {}\n/// <reference path=\"x\" />\n}\n";
        assert!(compare_dts(clean, tail_directive).is_pass());
    }

    #[test]
    fn structural_types_ignores_inert_triple_slash_in_records() {
        let clean = "=== a.ts ===\n> var x: number\n";
        let with_directive = "=== a.ts ===\n> var x: number /// <reference path=\"i\" />\n";
        assert!(compare_types(clean, with_directive).is_pass());
    }

    #[test]
    fn structural_dts_ignores_triple_slash_inside_comments_and_after_statements() {
        let in_comment = "/*\n/// <reference path=\"x\" />\n*/\ndeclare const a: number;\n";
        let plain = "/*\n  note\n*/\ndeclare const a: number;\n";
        assert!(compare_dts(in_comment, plain).is_pass());

        let after_statement = "declare const a: number;\n/// <reference path=\"x\" />\n";
        let no_directive = "declare const a: number;\n";
        assert!(compare_dts(after_statement, no_directive).is_pass());
    }

    #[test]
    fn structural_dts_sorts_distinct_string_named_modules() {
        let alpha_beta = "declare module \"alpha\" { export interface A {} }\ndeclare module \"beta\" { export interface B {} }\n";
        let beta_alpha = "declare module \"beta\" { export interface B {} }\ndeclare module \"alpha\" { export interface A {} }\n";
        assert!(compare_dts(alpha_beta, beta_alpha).is_pass());

        // Same-name augmentations stay ordered.
        let first = "declare module \"alpha\" { export interface A {} }\ndeclare module \"alpha\" { export interface B {} }\n";
        let second = "declare module \"alpha\" { export interface B {} }\ndeclare module \"alpha\" { export interface A {} }\n";
        assert!(compare_dts(first, second).is_fail());
    }

    #[test]
    fn structural_dts_normalizes_import_quote_style() {
        let double = "import { X } from \"a\";\nimport { Y } from \"b\";\n";
        let single = "import { X } from 'a';\nimport { Y } from 'b';\n";
        assert!(compare_dts(double, single).is_pass());
    }

    #[test]
    fn structural_dts_rejects_recovered_actual_but_unproves_recovered_expected() {
        // `= >` is a parse error: the actual side cannot pass.
        let expected = "type F = (x: string) => number;\n";
        let recovered_actual = "type F = (x: string) = > number;\n";
        assert!(compare_dts(expected, recovered_actual).is_fail());

        // A recovered expected baseline is Unproven, never Pass.
        let recovered_expected = "type F = (x: string) = > number;\n";
        let actual = "type F = (x: string) = > number;\n";
        assert!(compare_dts(recovered_expected, actual).is_unproven());
    }

    #[test]
    fn structural_dts_rejects_owner_member_swap_across_declarations() {
        // Global line-bag sorting makes these identical; owner/member association
        // must keep `x` under A and `y` under B.
        let expected = "interface A {\n  x: string;\n}\ninterface B {\n  y: number;\n}\n";
        let swapped = "interface A {\n  y: number;\n}\ninterface B {\n  x: string;\n}\n";
        assert!(compare_dts(expected, swapped).is_fail());
        assert!(compare_dts(expected, expected).is_pass());
    }

    #[test]
    fn structural_dts_rejects_nested_brace_owner_member_swap() {
        // Flat member-line sorting under A collapses nested objects and would
        // falsely pass this cross-owner nested property swap.
        let expected = "\
interface A {
  outer1: {
    x: string;
  };
  outer2: {
    y: number;
  };
}
";
        let swapped = "\
interface A {
  outer1: {
    y: number;
  };
  outer2: {
    x: string;
  };
}
";
        let reordered_siblings = "\
interface A {
  outer2: {
    y: number;
  };
  outer1: {
    x: string;
  };
}
";
        assert!(compare_dts(expected, swapped).is_fail());
        assert!(compare_dts(expected, reordered_siblings).is_pass());
    }

    #[test]
    fn structural_symbols_rejects_nested_indent_owner_member_swap() {
        // Flat sorting under [Global] would make these identical by erasing the
        // A/B ownership of nested symbol members.
        let expected = "\
[Global]
  A : Symbol(A)
    x : Symbol(x)
  B : Symbol(B)
    y : Symbol(y)
";
        let swapped = "\
[Global]
  A : Symbol(A)
    y : Symbol(y)
  B : Symbol(B)
    x : Symbol(x)
";
        let reordered_siblings = "\
[Global]
  B : Symbol(B)
    y : Symbol(y)
  A : Symbol(A)
    x : Symbol(x)
";
        assert!(compare_symbols(expected, swapped).is_fail());
        assert!(compare_symbols(expected, reordered_siblings).is_pass());
    }

    #[test]
    fn js_behavior_matches_on_stdout_and_exit_code() {
        let expected = verified(b"hello\n", 0);
        let actual = verified(b"hello\n", 0);
        assert!(compare_js(&expected, &actual).is_pass());
    }

    #[test]
    fn js_behavior_mismatches_stdout() {
        let expected = verified(b"hello\n", 0);
        let actual = verified(b"HELLO\n", 0);
        assert!(compare_js(&expected, &actual).is_fail());
    }

    #[test]
    fn js_behavior_mismatches_exit_code() {
        let expected = verified(b"hello\n", 0);
        let actual = verified(b"hello\n", 1);
        assert!(compare_js(&expected, &actual).is_fail());
    }

    #[test]
    fn empty_output_js_parity_is_unproven_not_pass() {
        let expected = verified(b"", 0);
        let actual = verified(b"", 0);
        let verdict = compare_js(&expected, &actual);
        assert!(verdict.is_unproven());
        assert!(!verdict.is_pass());
    }

    #[test]
    #[ignore = "requires Node 24.18.0 or /proc/self/clear_refs permission; external_blocked in this environment"]
    fn forged_unpinned_js_outcomes_are_not_a_public_proof_path() {
        // Old public compare_js(&OracleOutcome, &OracleOutcome) returned Pass for
        // matching caller-forged bytes with no Node 24.18.0 / timeout / cap proof.
        // Public construction is now VerifiedJsOutcome::capture via NodeOracle.
        let forged_expected = outcome(b"hello\n", 0);
        let forged_actual = outcome(b"hello\n", 0);
        assert!(
            js_emit::compare_js_outcomes(&forged_expected, &forged_actual).is_pass(),
            "private outcome key still matches; proof requires capture()"
        );

        let root = std::env::temp_dir().join(format!(
            "bamts-facets-forged-js-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(&root).expect("temp root");
        let entry = "case.js";
        fs::write(root.join(entry), "console.log('hello');\n").expect("write case");
        let oracle = NodeOracle::discover(&root).expect("pinned Node 24.18.0");
        let case = fixture_case("forged-js", entry);
        let verified_expected =
            VerifiedJsOutcome::capture(&oracle, &case).expect("capture expected");
        let verified_actual = VerifiedJsOutcome::capture(&oracle, &case).expect("capture actual");
        assert!(compare_js(&verified_expected, &verified_actual).is_pass());
        let _ = fs::remove_dir_all(&root);

        // No public OracleOutcome → VerifiedJsOutcome conversion exists.
        assert!(std::mem::size_of::<VerifiedJsOutcome>() > 0);
        assert_eq!(crate::corpus::NODE_VERSION, "24.18.0");
    }

    #[test]
    fn committed_code_map_is_complete_against_required_registry() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let map = load_diagnostic_code_map(&root).expect("committed diagnostic code map");
        assert_eq!(map.entries().count(), REQUIRED_BAMTS_DIAGNOSTIC_CODES.len());

        // S1 mapped scanner (L) codes and U2.6 mapped checker (C) codes;
        // parser (P) codes stay unmapped except the two resolved parser
        // correspondences below. Checker codes emitted without a tsc-verified
        // counterpart stay unmapped: the registry rows name their compiler
        // constants (verification/diagnostic-code-map.json).
        const MAPPED_PARSER_CODES: [(&str, u32); 3] =
            [("BAMTS-P017", 1163), ("BAMTS-P020", 1141), ("BAMTS-P021", 1048)];
        const UNMAPPED_CHECKER_CODES: [&str; 19] = [
            "BAMTS-C060",
            "BAMTS-C061",
            "BAMTS-C062",
            "BAMTS-C063",
            "BAMTS-C064",
            "BAMTS-C065",
            "BAMTS-C068",
            "BAMTS-C069",
            "BAMTS-C073",
            "BAMTS-C074",
            "BAMTS-C075",
            "BAMTS-C076",
            "BAMTS-C077",
            "BAMTS-C078",
            "BAMTS-C079",
            "BAMTS-C082",
            "BAMTS-C104",
            "BAMTS-C105",
            "BAMTS-C106",
        ];
        let mut mapped = 0;
        for code in REQUIRED_BAMTS_DIAGNOSTIC_CODES {
            let entry = map.get(code).expect(code);
            assert!(!entry.evidence.trim().is_empty());
            if UNMAPPED_CHECKER_CODES.contains(&code) {
                assert_eq!(entry.status, DiagnosticMappingStatus::Unmapped, "{code}");
                assert!(entry.ts_code.is_none());
                continue;
            }
            if let Some((_, ts_code)) =
                MAPPED_PARSER_CODES.iter().find(|(name, _)| *name == code)
            {
                assert_eq!(entry.status, DiagnosticMappingStatus::Mapped, "{code}");
                assert_eq!(entry.ts_code, Some(*ts_code), "{code}");
                mapped += 1;
                continue;
            }
            if code.starts_with("BAMTS-L") || code.starts_with("BAMTS-C") {
                assert_eq!(
                    entry.status,
                    DiagnosticMappingStatus::Mapped,
                    "{code} must be mapped"
                );
                assert!(entry.ts_code.is_some());
                assert_ne!(entry.ts_code, Some(0));
                mapped += 1;
            } else {
                assert_eq!(entry.status, DiagnosticMappingStatus::Unmapped);
                assert!(entry.ts_code.is_none());
            }
        }
        assert_eq!(
            map.unmapped_count(),
            REQUIRED_BAMTS_DIAGNOSTIC_CODES.len() - mapped
        );
    }

    #[test]
    fn excess_property_code_corresponds_to_ts2353() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let map = load_diagnostic_code_map(&root).expect("committed diagnostic code map");
        assert_eq!(map.typescript_code("BAMTS-C067"), Some(2353));
        let expected =
            [diag(1, 31, DiagnosticCategory::Error, FacetSeverity::Error, "TS2353")];
        let actual =
            [diag(1, 31, DiagnosticCategory::Error, FacetSeverity::Error, "BAMTS-C067")];
        assert_eq!(compare_diagnostics(&expected, &actual, &map), FacetVerdict::Pass);
        let suggested =
            [diag(12, 20, DiagnosticCategory::Error, FacetSeverity::Error, "TS2561")];
        let same_site =
            [diag(12, 20, DiagnosticCategory::Error, FacetSeverity::Error, "BAMTS-C067")];
        assert!(compare_diagnostics(&suggested, &same_site, &map).is_fail());
    }

    #[test]
    fn yield_outside_generator_code_corresponds_to_ts1163() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let map = load_diagnostic_code_map(&root).expect("committed diagnostic code map");
        assert_eq!(map.typescript_code("BAMTS-P017"), Some(1163));
        let expected =
            [diag(2, 4, DiagnosticCategory::Error, FacetSeverity::Error, "TS1163")];
        let actual =
            [diag(2, 4, DiagnosticCategory::Error, FacetSeverity::Error, "BAMTS-P017")];
        assert_eq!(compare_diagnostics(&expected, &actual, &map), FacetVerdict::Pass);
        let diverged =
            [diag(3, 4, DiagnosticCategory::Error, FacetSeverity::Error, "TS2304")];
        let same_site =
            [diag(3, 4, DiagnosticCategory::Error, FacetSeverity::Error, "BAMTS-P017")];
        assert!(compare_diagnostics(&diverged, &same_site, &map).is_fail());
    }

    #[test]
    fn non_string_module_name_code_corresponds_to_ts1141() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let map = load_diagnostic_code_map(&root).expect("committed diagnostic code map");
        assert_eq!(map.typescript_code("BAMTS-P020"), Some(1141));
        let expected =
            [diag(1, 23, DiagnosticCategory::Error, FacetSeverity::Error, "TS1141")];
        let actual =
            [diag(1, 23, DiagnosticCategory::Error, FacetSeverity::Error, "BAMTS-P020")];
        assert_eq!(compare_diagnostics(&expected, &actual, &map), FacetVerdict::Pass);
    }

    #[test]
    fn duplicate_bamts_code_is_rejected() {
        let mut json = complete_unmapped_json();
        json = json.replacen(
            "\"bamtsCode\":\"BAMTS-L002\"",
            "\"bamtsCode\":\"BAMTS-L001\"",
            1,
        );
        let err = parse_diagnostic_code_map(&json).expect_err("duplicate");
        assert_eq!(err.code(), ErrorCode::Duplicate);
    }

    #[test]
    fn shared_typescript_mapping_across_bamts_codes_is_allowed() {
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| match *code {
                    "BAMTS-L001" | "BAMTS-L002" => {
                        (*code, DiagnosticMappingStatus::Mapped, Some(1002))
                    }
                    _ => (*code, DiagnosticMappingStatus::Unmapped, None),
                })
                .collect();
        let map = parse_diagnostic_code_map(&empty_map_json(&entries)).expect("valid map");
        assert_eq!(map.typescript_code("BAMTS-L001"), Some(1002));
        assert_eq!(map.typescript_code("BAMTS-L002"), Some(1002));
    }

    #[test]
    fn malformed_bamts_code_is_rejected() {
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| {
                    if *code == "BAMTS-L001" {
                        ("BAMTS-L1", DiagnosticMappingStatus::Unmapped, None)
                    } else {
                        (*code, DiagnosticMappingStatus::Unmapped, None)
                    }
                })
                .collect();
        let err = parse_diagnostic_code_map(&empty_map_json(&entries)).expect_err("malformed");
        assert_eq!(err.code(), ErrorCode::Schema);
    }

    #[test]
    fn unknown_bamts_code_is_rejected() {
        let mut entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| (*code, DiagnosticMappingStatus::Unmapped, None))
                .collect();
        // Well-formed L/P/C shape, but outside the current required registry.
        entries.push(("BAMTS-L099", DiagnosticMappingStatus::Unmapped, None));
        let err = parse_diagnostic_code_map(&empty_map_json(&entries)).expect_err("unknown");
        assert_eq!(err.code(), ErrorCode::Schema);
        assert!(err.to_string().contains("unknown BAMTS diagnostic code"));
    }

    #[test]
    fn missing_required_code_is_rejected() {
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .filter(|code| **code != "BAMTS-C019")
                .map(|code| (*code, DiagnosticMappingStatus::Unmapped, None))
                .collect();
        let err = parse_diagnostic_code_map(&empty_map_json(&entries)).expect_err("missing");
        assert_eq!(err.code(), ErrorCode::SetMismatch);
    }

    #[test]
    fn unmapped_entry_cannot_carry_typescript_code() {
        let entries: Vec<(&str, DiagnosticMappingStatus, Option<u32>)> =
            REQUIRED_BAMTS_DIAGNOSTIC_CODES
                .iter()
                .map(|code| {
                    if *code == "BAMTS-L001" {
                        (*code, DiagnosticMappingStatus::Unmapped, Some(1002))
                    } else {
                        (*code, DiagnosticMappingStatus::Unmapped, None)
                    }
                })
                .collect();
        let err = parse_diagnostic_code_map(&empty_map_json(&entries)).expect_err("lying unmapped");
        assert_eq!(err.code(), ErrorCode::Schema);
    }

    #[test]
    fn unknown_field_in_code_map_is_rejected() {
        let json = complete_unmapped_json().replacen(
            "\"schemaVersion\":1",
            "\"schemaVersion\":1,\"rogue\":true",
            1,
        );
        let err = parse_diagnostic_code_map(&json).expect_err("unknown field");
        assert_eq!(err.code(), ErrorCode::Json);
    }
}
