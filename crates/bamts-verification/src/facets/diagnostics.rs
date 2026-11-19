use std::cmp::Ordering;

use super::{
    DiagnosticCategory, DiagnosticCodeMap, FacetDiagnostic, FacetSeverity, FacetVerdict,
    SourcePosition,
};

/// Compares diagnostics on unit, position, category, severity, and code
/// correspondence. The unit basename is checked first so two diagnostics at
/// the same line/column in different files never compare equal.
pub fn compare_diagnostics(
    expected: &[FacetDiagnostic],
    actual: &[FacetDiagnostic],
    code_map: &DiagnosticCodeMap,
) -> FacetVerdict {
    let mut expected_rows = expected.to_vec();
    let mut actual_rows = actual.to_vec();
    // Sort by unit/position/category/severity plus a correspondence-canonical
    // code so BAMTS↔TS pairs still align when raw code strings reverse order.
    expected_rows.sort_by_key(|row| diagnostic_sort_key(row, code_map));
    actual_rows.sort_by_key(|row| diagnostic_sort_key(row, code_map));

    if expected_rows.len() != actual_rows.len() {
        return FacetVerdict::Fail {
            reason: format!(
                "diagnostic count mismatch{}: expected {} actual {}",
                count_mismatch_label(&expected_rows, &actual_rows, code_map),
                expected_rows.len(),
                actual_rows.len()
            ),
        };
    }

    for (index, (left, right)) in expected_rows.iter().zip(actual_rows.iter()).enumerate() {
        if left.unit != right.unit {
            return FacetVerdict::Fail {
                reason: format!(
                    "diagnostic[{index}] unit mismatch: expected {} actual {}",
                    left.unit, right.unit
                ),
            };
        }
        if left.position != right.position {
            return FacetVerdict::Fail {
                reason: format!(
                    "diagnostic[{index}] position mismatch: expected {}:{} actual {}:{}",
                    left.position.line,
                    left.position.character,
                    right.position.line,
                    right.position.character
                ),
            };
        }
        if left.category != right.category {
            return FacetVerdict::Fail {
                reason: format!(
                    "diagnostic[{index}] category mismatch: expected {:?} actual {:?}",
                    left.category, right.category
                ),
            };
        }
        if left.severity != right.severity {
            return FacetVerdict::Fail {
                reason: format!(
                    "diagnostic[{index}] severity mismatch: expected {:?} actual {:?}",
                    left.severity, right.severity
                ),
            };
        }
        if !codes_correspond(&left.code, &right.code, code_map) {
            return FacetVerdict::Fail {
                reason: format!(
                    "diagnostic[{index}] code correspondence mismatch: `{}` vs `{}`",
                    left.code, right.code
                ),
            };
        }
    }

    FacetVerdict::Pass
}

fn diagnostic_sort_key(
    row: &FacetDiagnostic,
    code_map: &DiagnosticCodeMap,
) -> (
    String,
    SourcePosition,
    DiagnosticCategory,
    FacetSeverity,
    String,
) {
    (
        row.unit.clone(),
        row.position,
        row.category,
        row.severity,
        correspondence_canonical_code(&row.code, code_map),
    )
}

fn count_mismatch_label(
    expected_rows: &[FacetDiagnostic],
    actual_rows: &[FacetDiagnostic],
    code_map: &DiagnosticCodeMap,
) -> String {
    let mut expected = expected_rows
        .iter()
        .map(|row| diagnostic_sort_key(row, code_map));
    let mut actual = actual_rows
        .iter()
        .map(|row| diagnostic_sort_key(row, code_map));
    let mut left = expected.next();
    let mut right = actual.next();
    loop {
        match (&left, &right) {
            (Some(expected_key), Some(actual_key)) => match expected_key.cmp(actual_key) {
                Ordering::Less => return format!(" [missing {}]", expected_key.4),
                Ordering::Greater => return format!(" [extra {}]", actual_key.4),
                Ordering::Equal => {
                    left = expected.next();
                    right = actual.next();
                }
            },
            (Some(expected_key), None) => return format!(" [missing {}]", expected_key.4),
            (None, Some(actual_key)) => return format!(" [extra {}]", actual_key.4),
            (None, None) => return String::new(),
        }
    }
}

/// Map BAMTS/TS spellings onto one sortable identity when a correspondence exists.
fn correspondence_canonical_code(code: &str, code_map: &DiagnosticCodeMap) -> String {
    if let Some(ts_code) = code_map.typescript_code(code) {
        return format!("TS{ts_code}");
    }
    if let Some(ts_code) = parse_typescript_code(code) {
        return format!("TS{ts_code}");
    }
    code.to_owned()
}

fn parse_typescript_code(code: &str) -> Option<u32> {
    let digits = code
        .strip_prefix("TS")
        .or_else(|| code.strip_prefix("ts"))
        .unwrap_or(code);
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn codes_correspond(left: &str, right: &str, code_map: &DiagnosticCodeMap) -> bool {
    if left == right {
        return true;
    }
    bamts_matches_typescript(left, right, code_map)
        || bamts_matches_typescript(right, left, code_map)
}

fn bamts_matches_typescript(bamts: &str, typescript: &str, code_map: &DiagnosticCodeMap) -> bool {
    let Some(ts_code) = code_map.typescript_code(bamts) else {
        return false;
    };
    typescript_code_matches(typescript, ts_code)
}

fn typescript_code_matches(code: &str, ts_code: u32) -> bool {
    parse_typescript_code(code) == Some(ts_code)
}
