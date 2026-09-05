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
//!   and output limits. Caller-forged [`OracleOutcome`] values are not a proof
//!   path. Empty stdout cannot pass on its own.
//!
//! The diagnostic code map at [`DIAGNOSTIC_CODE_MAP_PATH`] must enumerate every
//! current `BAMTS-L001…L011`, parser, and checker diagnostic codes.
//! Unmapped entries are first-class evidence, not invented TypeScript codes.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    sync::Arc,
};

use bamts_compiler::parser;
use bamts_compiler::scanner;
use bamts_compiler::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
use bamts_compiler::syntax::{
    BindingPattern, ClassDeclaration, ClassMember, ClassMemberNode, ExportDeclaration,
    ExportDefaultValue, ExportNamedDeclaration, FunctionLike, FunctionType, IdentifierNode,
    InterfaceDeclaration, NamespaceName, Node, NumericLiteralNode, PropertyName, SourceFile,
    Statement, Stmt, StringLiteralNode, Ty, TypeArgumentList, TypeMember, TypeMemberNode, TypeNode,
    TypeParameterList, VariableDeclaration,
};
use serde::{Deserialize, Serialize};

use crate::corpus::{CaseSpec, NodeOracle, OracleOutcome};
use crate::{ErrorCode, Result, VerificationError};

/// Repository-relative path to the BAMTS↔TS diagnostic correspondence table.
pub const DIAGNOSTIC_CODE_MAP_PATH: &str = "verification/diagnostic-code-map.json";

/// Schema version accepted by the diagnostic code map loader.
pub const DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION: u32 = 1;

/// Every current BAMTS diagnostic code the map must cover exactly once.
pub const REQUIRED_BAMTS_DIAGNOSTIC_CODES: [&str; 104] = [
    "BAMTS-L001",
    "BAMTS-L002",
    "BAMTS-L003",
    "BAMTS-L004",
    "BAMTS-L005",
    "BAMTS-L006",
    "BAMTS-L007",
    "BAMTS-L008",
    "BAMTS-L009",
    "BAMTS-L010",
    "BAMTS-L011",
    "BAMTS-P001",
    "BAMTS-P002",
    "BAMTS-P003",
    "BAMTS-P004",
    "BAMTS-P005",
    "BAMTS-P006",
    "BAMTS-P007",
    "BAMTS-P009",
    "BAMTS-P010",
    "BAMTS-P011",
    "BAMTS-P012",
    "BAMTS-C001",
    "BAMTS-C002",
    "BAMTS-C003",
    "BAMTS-C004",
    "BAMTS-C005",
    "BAMTS-C006",
    "BAMTS-C007",
    "BAMTS-C008",
    "BAMTS-C009",
    "BAMTS-C010",
    "BAMTS-C011",
    "BAMTS-C012",
    "BAMTS-C013",
    "BAMTS-C014",
    "BAMTS-C015",
    "BAMTS-C016",
    "BAMTS-C017",
    "BAMTS-C018",
    "BAMTS-C019",
    "BAMTS-C020",
    "BAMTS-C021",
    "BAMTS-C022",
    "BAMTS-C023",
    "BAMTS-C024",
    "BAMTS-C025",
    "BAMTS-C026",
    "BAMTS-C027",
    "BAMTS-C028",
    "BAMTS-C029",
    "BAMTS-C030",
    "BAMTS-C031",
    "BAMTS-C032",
    "BAMTS-C033",
    "BAMTS-C034",
    "BAMTS-C035",
    "BAMTS-C036",
    "BAMTS-C037",
    "BAMTS-C038",
    "BAMTS-C039",
    "BAMTS-C040",
    "BAMTS-C041",
    "BAMTS-C042",
    "BAMTS-C043",
    "BAMTS-C044",
    "BAMTS-C045",
    "BAMTS-C046",
    "BAMTS-C047",
    "BAMTS-C048",
    "BAMTS-C049",
    "BAMTS-C050",
    "BAMTS-C051",
    "BAMTS-C052",
    "BAMTS-C053",
    "BAMTS-C054",
    "BAMTS-C055",
    "BAMTS-C057",
    "BAMTS-C058",
    "BAMTS-C059",
    "BAMTS-C066",
    "BAMTS-C070",
    "BAMTS-C071",
    "BAMTS-C072",
    "BAMTS-C080",
    "BAMTS-C081",
    "BAMTS-C086",
    "BAMTS-C087",
    "BAMTS-C088",
    "BAMTS-C089",
    "BAMTS-C090",
    "BAMTS-C091",
    "BAMTS-C092",
    "BAMTS-C093",
    "BAMTS-C094",
    "BAMTS-C095",
    "BAMTS-C096",
    "BAMTS-C097",
    "BAMTS-C098",
    "BAMTS-C099",
    "BAMTS-C100",
    "BAMTS-C101",
    "BAMTS-C102",
    "BAMTS-C103",
];
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

/// Mapping status for one BAMTS diagnostic code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiagnosticMappingStatus {
    Mapped,
    Unmapped,
}

/// One BAMTS↔TS correspondence row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct DiagnosticCodeMapping {
    pub bamts_code: String,
    pub ts_code: Option<u32>,
    pub status: DiagnosticMappingStatus,
    pub evidence: String,
}

/// Validated BAMTS↔TS diagnostic correspondence table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticCodeMap {
    entries: BTreeMap<String, DiagnosticCodeMapping>,
}

impl DiagnosticCodeMap {
    /// Returns every validated mapping in BAMTS-code order.
    pub fn entries(&self) -> impl Iterator<Item = &DiagnosticCodeMapping> {
        self.entries.values()
    }

    /// Looks up a BAMTS diagnostic code.
    #[must_use]
    pub fn get(&self, bamts_code: &str) -> Option<&DiagnosticCodeMapping> {
        self.entries.get(bamts_code)
    }

    /// Returns the mapped TypeScript numeric code, if the BAMTS code is mapped.
    #[must_use]
    pub fn typescript_code(&self, bamts_code: &str) -> Option<u32> {
        self.entries
            .get(bamts_code)
            .and_then(|entry| match entry.status {
                DiagnosticMappingStatus::Mapped => entry.ts_code,
                DiagnosticMappingStatus::Unmapped => None,
            })
    }

    /// Counts entries explicitly marked unmapped.
    #[must_use]
    pub fn unmapped_count(&self) -> usize {
        self.entries
            .values()
            .filter(|entry| entry.status == DiagnosticMappingStatus::Unmapped)
            .count()
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct RawDiagnosticCodeMap {
    schema_version: u32,
    entries: Vec<DiagnosticCodeMapping>,
}

/// Loads and fully validates `verification/diagnostic-code-map.json` under `root`.
pub fn load_diagnostic_code_map(root: &Path) -> Result<DiagnosticCodeMap> {
    let path = root.join(DIAGNOSTIC_CODE_MAP_PATH);
    let text = fs::read_to_string(&path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })?;
    parse_diagnostic_code_map(&text)
}

/// Parses and fully validates a diagnostic code map document.
pub fn parse_diagnostic_code_map(text: &str) -> Result<DiagnosticCodeMap> {
    let raw: RawDiagnosticCodeMap = serde_json::from_str(text)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("{error}")))?;
    validate_diagnostic_code_map(raw)
}

fn validate_diagnostic_code_map(raw: RawDiagnosticCodeMap) -> Result<DiagnosticCodeMap> {
    if raw.schema_version != DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION {
        return Err(schema_error(format!(
            "schemaVersion must be {DIAGNOSTIC_CODE_MAP_SCHEMA_VERSION}, found {}",
            raw.schema_version
        )));
    }

    let required: BTreeSet<&str> = REQUIRED_BAMTS_DIAGNOSTIC_CODES.iter().copied().collect();
    let mut entries = BTreeMap::new();

    for entry in raw.entries {
        validate_mapping_row(&entry)?;

        if entries.contains_key(&entry.bamts_code) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate BAMTS diagnostic code `{}`", entry.bamts_code),
            ));
        }

        if !required.contains(entry.bamts_code.as_str()) {
            return Err(schema_error(format!(
                "unknown BAMTS diagnostic code `{}`",
                entry.bamts_code
            )));
        }

        entries.insert(entry.bamts_code.clone(), entry);
    }

    let present: BTreeSet<&str> = entries.keys().map(String::as_str).collect();
    let missing: Vec<&str> = required.difference(&present).copied().collect();
    if !missing.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "diagnostic code map missing required BAMTS codes: {}",
                missing.join(", ")
            ),
        ));
    }

    Ok(DiagnosticCodeMap { entries })
}

fn validate_mapping_row(entry: &DiagnosticCodeMapping) -> Result<()> {
    if !is_well_formed_bamts_code(&entry.bamts_code) {
        return Err(schema_error(format!(
            "malformed BAMTS diagnostic code `{}`",
            entry.bamts_code
        )));
    }

    if entry.evidence.trim().is_empty() {
        return Err(schema_error(format!(
            "mapping for `{}` must include non-empty evidence",
            entry.bamts_code
        )));
    }

    match entry.status {
        DiagnosticMappingStatus::Unmapped => {
            if entry.ts_code.is_some() {
                return Err(schema_error(format!(
                    "unmapped entry `{}` must not invent a TypeScript code",
                    entry.bamts_code
                )));
            }
        }
        DiagnosticMappingStatus::Mapped => {
            let Some(ts_code) = entry.ts_code else {
                return Err(schema_error(format!(
                    "mapped entry `{}` requires a TypeScript code",
                    entry.bamts_code
                )));
            };
            if ts_code == 0 {
                return Err(schema_error(format!(
                    "mapped entry `{}` has malformed TypeScript code 0",
                    entry.bamts_code
                )));
            }
        }
    }

    Ok(())
}

fn is_well_formed_bamts_code(code: &str) -> bool {
    let Some((prefix, number)) = code.split_once('-') else {
        return false;
    };
    if prefix != "BAMTS" {
        return false;
    }
    let mut chars = number.chars();
    let Some(family) = chars.next() else {
        return false;
    };
    if !matches!(family, 'L' | 'P' | 'C') {
        return false;
    }
    let digits: String = chars.collect();
    digits.len() == 3 && digits.chars().all(|ch| ch.is_ascii_digit())
}

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
                "diagnostic count mismatch: expected {} actual {}",
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

/// Structural comparator for `.types` baselines.
pub fn compare_types(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("types", expected, actual, |text| {
        Ok(canonicalize_record_baseline(
            text,
            is_types_section,
            types_record,
        ))
    })
}

/// Structural comparator for `.symbols` baselines.
pub fn compare_symbols(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("symbols", expected, actual, |text| {
        Ok(canonicalize_record_baseline(
            text,
            is_symbols_section,
            symbols_record,
        ))
    })
}

/// Structural comparator for emitted `.d.ts` declaration baselines.
///
/// Both sides are parsed with the exact BAMTS parser and canonicalized from the
/// AST. A baseline that does not parse without recovery can never pass.
pub fn compare_dts(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("d.ts", expected, actual, canonicalize_dts)
}

/// Structural comparator for JSON source-map baselines.
///
/// JSON object-key order and insignificant whitespace do not carry map meaning;
/// array order and scalar values remain significant.
pub fn compare_source_map(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("source-map", expected, actual, canonicalize_json)
}

fn canonicalize_json(text: &str) -> Result<Vec<String>, ()> {
    let mut lines = Vec::new();
    for line in text.replace("\r\n", "\n").replace('\r', "\n").lines() {
        let trimmed = line.trim();
        // Visualization trailers and blank lines carry no map meaning.
        if trimmed.is_empty() || trimmed.starts_with("//// https://") {
            continue;
        }
        if let Some(name) = trimmed
            .strip_prefix("//// [")
            .and_then(|rest| rest.strip_suffix(']'))
        {
            lines.push(format!("//// [{name}]"));
            continue;
        }
        if !trimmed.starts_with('{') && !trimmed.starts_with('[') {
            lines.push(trimmed.to_owned());
            continue;
        }
        let mut value: serde_json::Value = serde_json::from_str(trimmed).map_err(|_| ())?;
        // Upstream's serializer always writes `sourceRoot` (empty when unset);
        // absent and empty carry the same map meaning, so normalize to absent.
        if let Some(map) = value.as_object_mut()
            && map.get("sourceRoot").and_then(serde_json::Value::as_str) == Some("")
        {
            map.remove("sourceRoot");
        }
        lines.push(serde_json::to_string(&value).map_err(|_| ())?);
    }
    Ok(lines)
}

/// Line-wise comparator for `.js` emit baselines.
///
/// Newlines are normalized to `\n` and trailing spaces are stripped. Marker
/// order and code text stay source-order; emit is not a declaration set.
pub fn compare_js_emit(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("javascript", expected, actual, canonicalize_js_emit)
}

fn canonicalize_js_emit(text: &str) -> Result<Vec<String>, ()> {
    Ok(text
        .replace("\r\n", "\n")
        .replace('\r', "\n")
        .lines()
        .map(|line| line.trim_end().to_owned())
        .collect())
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
            reason: format!("{facet} structural mismatch after formatting/order normalization"),
        }
    }
}

/// Declared identity of one element in a declaration-set container.
///
/// Only a simple declared name is a provably distinct identity. Every other
/// shape (computed/string names, call/construct/index signatures, anonymous
/// declarations, augmentations) keeps source order because order is semantic
/// for overloads, merge groups, and ordered type members.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DeclIdentity {
    Simple(String),
    Anonymous,
}

/// Sort declaration-set elements only when every element has a simple identity
/// and no two share a name. Any duplicate name (a merge group or overload set)
/// or anonymous identity keeps the full source order, because order is
/// semantic there. This is the one case where order is provably irrelevant.
fn sort_declaration_groups(items: &mut [(DeclIdentity, String)]) {
    if items.len() < 2 {
        return;
    }
    let mut names = BTreeSet::new();
    for (identity, _) in items.iter() {
        let DeclIdentity::Simple(name) = identity else {
            return;
        };
        names.insert(name.as_str());
    }
    if names.len() != items.len() {
        return;
    }
    items.sort_by(|left, right| left.0.cmp(&right.0));
}

/// Parses declaration text with the exact BAMTS parser, failing on any
/// recovery diagnostic so structurally invalid baselines can never pass.
fn parse_dts_source(text: &str) -> Result<SourceFile, ()> {
    let source = SourceText::new(text.to_owned()).map_err(|_| ())?;
    let scanned = scanner::scan(SourceId::new(0), ScriptKind::TypeScript, Arc::new(source));
    let parsed = parser::parse(scanned);
    if !parsed.diagnostics().is_empty() {
        return Err(());
    }
    Ok(parsed.into_parts().0)
}

fn canonicalize_dts(text: &str) -> Result<Vec<String>, ()> {
    let file = parse_dts_source(text)?;
    let mut canonical = triple_slash_directives(text);
    canonical.extend(canonical_statement_list(file.statements(), &file));
    Ok(canonical)
}

/// Semantic `/// <reference ... />` directives in source order. They are an
/// ordered prologue: reordering, changing, or removing one changes the
/// declaration program, so they must compare exactly. TypeScript honors them
/// only in the file prologue before any statement, and a directive inside a
/// block comment or string is inert, so collection stops at the first
/// non-comment, non-directive line and skips block-comment bodies.
fn triple_slash_directives(text: &str) -> Vec<String> {
    let mut directives = Vec::new();
    let mut in_block_comment = false;
    for line in text.lines() {
        let trimmed = line.trim_start_matches('\u{feff}').trim();
        if in_block_comment {
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.is_empty() {
            continue;
        }
        if is_semantic_triple_slash_directive(line.trim_start_matches('\u{feff}')) {
            directives.push(normalize_record_line(trimmed));
            continue;
        }
        if trimmed.starts_with("/*") {
            if !trimmed.contains("*/") {
                in_block_comment = true;
            }
            continue;
        }
        if trimmed.starts_with("//") {
            continue;
        }
        // First real statement ends the prologue.
        break;
    }
    directives
}

fn canonical_statement_list(statements: &[Stmt], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = statements
        .iter()
        .map(|statement| canonical_statement(statement, file))
        .collect();
    sort_declaration_groups(&mut items);
    items
        .into_iter()
        .map(|(_, raw)| normalize_block_lines(&strip_comments(&raw)))
        .collect()
}

fn canonical_statement(statement: &Stmt, file: &SourceFile) -> (DeclIdentity, String) {
    match statement.data() {
        Statement::Declare(inner) => {
            let (identity, inner_raw) = canonical_statement(inner, file);
            let head = slice_range(file, statement.range().start(), inner.range().start());
            let tail = slice_range(file, inner.range().end(), statement.range().end());
            (identity, assemble(&[head, inner_raw, tail]))
        }
        Statement::Export(export) => canonical_export(export, statement.range(), file),
        Statement::Namespace(namespace) => {
            let mut items: Vec<(DeclIdentity, String)> = namespace
                .body
                .data()
                .statements
                .iter()
                .map(|child| canonical_statement(child, file))
                .collect();
            sort_declaration_groups(&mut items);
            let raw: Vec<String> = items.into_iter().map(|(_, raw)| raw).collect();
            let identity = namespace_identity(&namespace.name, file);
            let body_statements = &namespace.body.data().statements;
            let body_range = namespace.body.range();
            let range = statement.range();
            if is_synthetic_dotted_body(body_statements, body_range) {
                // `namespace A.B { ... }` desugars to A with a synthetic body
                // whose node range begins at the dot. Canonicalize it into the
                // same shape as explicit `namespace A { namespace B { ... } }`
                // by dropping the dot from the head and the child's leading dot.
                let child_raw = raw
                    .first()
                    .map(|child| child.trim_start_matches('.').to_owned())
                    .unwrap_or_default();
                let head = slice_range(file, range.start(), body_range.start());
                let head = head
                    .trim_end_matches(['.', ' ', '\t', '\r', '\n'])
                    .to_owned();
                let tail = slice_range(file, body_range.end(), range.end());
                (
                    identity,
                    assemble(&[
                        head,
                        "{".to_owned(),
                        format!("namespace {child_raw}"),
                        "}".to_owned(),
                        tail,
                    ]),
                )
            } else {
                (
                    identity,
                    assemble_statement_container(file, range, body_range, body_statements, raw),
                )
            }
        }
        Statement::Interface(interface) => {
            let members = canonical_type_members(&interface.members, file);
            let identity = DeclIdentity::Simple(identifier_text(file, &interface.name));
            let head = declaration_head(
                file,
                statement.range(),
                &interface.members,
                interface_head_children(interface),
            );
            (
                identity,
                assemble_member_container(
                    file,
                    statement.range(),
                    &interface.members,
                    members,
                    head,
                ),
            )
        }
        Statement::Class(class) => {
            let identity = match &class.name {
                Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
                None => DeclIdentity::Anonymous,
            };
            let members = canonical_class_members(&class.members, file);
            let head = declaration_head(
                file,
                statement.range(),
                &class.members,
                class_head_children(class),
            );
            (
                identity,
                assemble_member_container(file, statement.range(), &class.members, members, head),
            )
        }
        Statement::TypeAlias(alias) => {
            let mut children = type_parameter_children(alias.type_parameters.as_ref());
            children.push(&alias.type_node);
            (
                DeclIdentity::Simple(identifier_text(file, &alias.name)),
                rebuild_children(file, statement.range(), children),
            )
        }
        Statement::Variable(variable) => {
            let mut children: Vec<&Ty> = Vec::new();
            for declarator in &variable.declarations {
                if let Some(annotation) = &declarator.data().type_annotation {
                    children.push(&*annotation.data().type_node);
                }
            }
            (
                variable_identity(variable, file),
                rebuild_children(file, statement.range(), children),
            )
        }
        Statement::Function(function) => (
            function_identity(&function.function.name, file),
            rebuild_children(
                file,
                statement.range(),
                function_like_children(&function.function),
            ),
        ),
        Statement::Enum(enum_declaration) => (
            DeclIdentity::Simple(identifier_text(file, &enum_declaration.name)),
            slice_node(file, statement.range()),
        ),
        Statement::Import(import) => {
            let specifier = unquote(&module_specifier_text(file, &import.source));
            let identity = DeclIdentity::Simple(specifier.clone());
            let raw = replace_string_child(file, statement.range(), &import.source, &specifier);
            (identity, raw)
        }
        _ => (DeclIdentity::Anonymous, slice_node(file, statement.range())),
    }
}

/// True when a namespace body is the parser's synthetic dotted desugaring: a
/// single child whose range begins exactly at the body range (no braces).
fn is_synthetic_dotted_body(statements: &[Stmt], body_range: TextRange) -> bool {
    statements.len() == 1 && statements[0].range().start() == body_range.start()
}

/// Canonicalizes the head of a member-bearing declaration (type parameters,
/// heritage, implements) while the members themselves are handled separately.
fn declaration_head<T>(
    file: &SourceFile,
    range: TextRange,
    members: &[Node<T>],
    head_children: Vec<&Ty>,
) -> String {
    let Some(first) = members.first() else {
        return rebuild_children(file, range, head_children);
    };
    let head_range = TextRange::new(range.start(), first.range().start()).unwrap_or(range);
    if head_children.is_empty() {
        slice_range(file, head_range.start(), head_range.end())
    } else {
        rebuild_children(file, head_range, head_children)
    }
}

fn interface_head_children(interface: &InterfaceDeclaration) -> Vec<&Ty> {
    let mut children = type_parameter_children(interface.type_parameters.as_ref());
    for reference in &interface.extends {
        if let Some(arguments) = &reference.type_arguments {
            children.extend(arguments.arguments.iter());
        }
    }
    children
}

fn class_head_children(class: &ClassDeclaration) -> Vec<&Ty> {
    let mut children = type_parameter_children(class.type_parameters.as_ref());
    if let Some(heritage) = &class.extends
        && let Some(arguments) = &heritage.type_arguments
    {
        children.extend(arguments.arguments.iter());
    }
    for implemented in &class.implements {
        children.push(implemented);
    }
    children
}

fn canonical_export(
    export: &ExportDeclaration,
    range: TextRange,
    file: &SourceFile,
) -> (DeclIdentity, String) {
    match export {
        ExportDeclaration::Named(export_named) => match export_named {
            ExportNamedDeclaration::Declaration(inner) => {
                let (identity, inner_raw) = canonical_statement(inner, file);
                let head = slice_range(file, range.start(), inner.range().start());
                let tail = slice_range(file, inner.range().end(), range.end());
                (identity, assemble(&[head, inner_raw, tail]))
            }
            ExportNamedDeclaration::Specifiers { .. } => {
                (DeclIdentity::Anonymous, slice_node(file, range))
            }
        },
        ExportDeclaration::Default(default) => {
            let identity = match &default.value {
                ExportDefaultValue::Function(function) => function_identity(&function.name, file),
                ExportDefaultValue::Class(class) => match &class.name {
                    Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
                    None => DeclIdentity::Anonymous,
                },
                ExportDefaultValue::Expression(_) | ExportDefaultValue::Missing(_) => {
                    DeclIdentity::Anonymous
                }
                ExportDefaultValue::Interface(interface) => {
                    DeclIdentity::Simple(identifier_text(file, &interface.name))
                }
            };
            (identity, slice_node(file, range))
        }
        ExportDeclaration::All(_) | ExportDeclaration::Assignment(_) => {
            (DeclIdentity::Anonymous, slice_node(file, range))
        }
    }
}

fn variable_identity(variable: &VariableDeclaration, file: &SourceFile) -> DeclIdentity {
    let Some(first) = variable.declarations.first() else {
        return DeclIdentity::Anonymous;
    };
    match first.data().binding.data() {
        BindingPattern::Identifier(identifier) => {
            DeclIdentity::Simple(identifier_text(file, identifier))
        }
        BindingPattern::Object(_)
        | BindingPattern::Array(_)
        | BindingPattern::Rest(_)
        | BindingPattern::Assignment(_)
        | BindingPattern::Missing(_) => DeclIdentity::Anonymous,
    }
}

fn function_identity(name: &Option<IdentifierNode>, file: &SourceFile) -> DeclIdentity {
    match name {
        Some(name) => DeclIdentity::Simple(identifier_text(file, name)),
        None => DeclIdentity::Anonymous,
    }
}

fn namespace_identity(name: &NamespaceName, file: &SourceFile) -> DeclIdentity {
    match name {
        NamespaceName::Identifier { name, .. } => DeclIdentity::Simple(identifier_text(file, name)),
        NamespaceName::StringLiteral(literal) => {
            // Distinct external modules are provably distinct identities; two
            // augmentations of the same module share one key and stay ordered.
            DeclIdentity::Simple(unquote(&module_specifier_text(file, literal)))
        }
        NamespaceName::Global { .. } => DeclIdentity::Anonymous,
    }
}

/// A member name is a simple identity when it is an identifier, string literal,
/// or numeric literal. Identifiers and string literals with the same text are
/// the same property key in TypeScript, so they share one merge group (order is
/// semantic across them).
fn property_identity(name: &PropertyName, file: &SourceFile) -> DeclIdentity {
    match name {
        PropertyName::Identifier(identifier) => {
            DeclIdentity::Simple(identifier_text(file, identifier))
        }
        PropertyName::String(literal) => {
            DeclIdentity::Simple(unquote(&module_specifier_text(file, literal)))
        }
        PropertyName::Number(literal) => DeclIdentity::Simple(numeric_text(file, literal)),
        PropertyName::Computed(_) | PropertyName::Private(_) | PropertyName::Missing(_) => {
            DeclIdentity::Anonymous
        }
    }
}

fn unquote(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.len() >= 2 && matches!(bytes[0], b'"' | b'\'') && bytes[bytes.len() - 1] == bytes[0] {
        text[1..text.len() - 1].to_owned()
    } else {
        text.to_owned()
    }
}

fn identifier_text(file: &SourceFile, identifier: &IdentifierNode) -> String {
    file.token_text(identifier.data().token())
        .unwrap_or("")
        .to_owned()
}

fn numeric_text(file: &SourceFile, literal: &NumericLiteralNode) -> String {
    file.token_text(literal.data().token())
        .unwrap_or("")
        .to_owned()
}

fn module_specifier_text(file: &SourceFile, literal: &StringLiteralNode) -> String {
    file.token_text(literal.data().token())
        .unwrap_or("")
        .to_owned()
}

fn slice_node(file: &SourceFile, range: TextRange) -> String {
    slice_range(file, range.start(), range.end())
}

fn slice_range(file: &SourceFile, start: Utf16Pos, end: Utf16Pos) -> String {
    let source = file.source_text().as_str();
    let start = file.source_text().utf16_to_byte(start).unwrap_or(0);
    let end = file
        .source_text()
        .utf16_to_byte(end)
        .unwrap_or(source.len());
    source[start..end].to_owned()
}

fn assemble(parts: &[String]) -> String {
    parts.join("\n")
}

/// Assembles a statement whose body is a statement list (namespace/module/global
/// bodies). The body's own delimiters (`{`/`}` for real bodies, none for
/// synthetic dotted tails) come from source slices around the child ranges, so
/// the brace shape is preserved while sorted children keep their own text.
fn assemble_statement_container(
    file: &SourceFile,
    range: TextRange,
    body_range: TextRange,
    statements: &[Stmt],
    sorted_raw: Vec<String>,
) -> String {
    let head = slice_range(file, range.start(), body_range.start());
    let tail = slice_range(file, body_range.end(), range.end());
    if statements.is_empty() {
        let body = slice_range(file, body_range.start(), body_range.end());
        return assemble(&[head, body, tail]);
    }
    let first = statements[0].range().start();
    let last_end = statements[statements.len() - 1].range().end();
    let body_head = slice_range(file, body_range.start(), first);
    let body_tail = slice_range(file, last_end, body_range.end());
    let mut parts = vec![head, body_head];
    for (index, raw) in sorted_raw.iter().enumerate() {
        if index > 0 {
            parts.push("\n".to_owned());
        }
        parts.push(raw.clone());
    }
    parts.push(body_tail);
    if !tail.is_empty() {
        parts.push(tail);
    }
    assemble(&parts)
}

/// Assembles a node (interface/class/object type) whose members are sorted.
/// Inter-member separators (`;` and whitespace) are dropped because they are
/// irrelevant formatting; each member keeps its own canonical text.
fn assemble_member_container<T>(
    file: &SourceFile,
    range: TextRange,
    members: &[Node<T>],
    sorted_raw: Vec<String>,
    head: String,
) -> String {
    if members.is_empty() {
        return slice_node(file, range);
    }
    let last_end = members[members.len() - 1].range().end();
    let mut tail = slice_range(file, last_end, range.end());
    tail = trim_member_separators(&tail).to_owned();
    let mut parts = vec![head];
    for (index, raw) in sorted_raw.iter().enumerate() {
        if index > 0 {
            parts.push("\n".to_owned());
        }
        parts.push(trim_member_separators(raw).to_owned());
    }
    if !tail.is_empty() {
        parts.push(tail);
    }
    assemble(&parts)
}

fn trim_member_separators(text: &str) -> &str {
    text.trim()
        .trim_start_matches(';')
        .trim_end_matches(';')
        .trim()
}

fn canonical_type_members(members: &[TypeMemberNode], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = members
        .iter()
        .map(|member| canonical_type_member(member, file))
        .collect();
    sort_declaration_groups(&mut items);
    items.into_iter().map(|(_, raw)| raw).collect()
}

fn canonical_type_member(member: &TypeMemberNode, file: &SourceFile) -> (DeclIdentity, String) {
    let identity = match member.data() {
        TypeMember::Property(property) => property_identity(&property.name, file),
        TypeMember::Method(method) => property_identity(&method.name, file),
        TypeMember::Call(_)
        | TypeMember::Construct(_)
        | TypeMember::Index(_)
        | TypeMember::Missing(_) => DeclIdentity::Anonymous,
    };
    let raw = match member.data() {
        TypeMember::Property(property) => {
            let Some(annotation) = &property.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        TypeMember::Method(method) => {
            function_type_children(file, member.range(), &method.function)
        }
        TypeMember::Call(call) => function_type_children(file, member.range(), &call.function),
        TypeMember::Construct(construct) => {
            function_type_children(file, member.range(), &construct.function.function)
        }
        TypeMember::Index(index) => {
            let mut children: Vec<&Ty> = index
                .parameters
                .iter()
                .map(|parameter| &*parameter.type_annotation.data().type_node)
                .collect();
            children.push(&*index.type_annotation.data().type_node);
            rebuild_children(file, member.range(), children)
        }
        TypeMember::Missing(_) => slice_node(file, member.range()),
    };
    (identity, raw)
}

fn canonical_class_members(members: &[ClassMemberNode], file: &SourceFile) -> Vec<String> {
    let mut items: Vec<(DeclIdentity, String)> = members
        .iter()
        .map(|member| canonical_class_member(member, file))
        .collect();
    sort_declaration_groups(&mut items);
    items.into_iter().map(|(_, raw)| raw).collect()
}

fn canonical_class_member(member: &ClassMemberNode, file: &SourceFile) -> (DeclIdentity, String) {
    let identity = match member.data() {
        ClassMember::Constructor(_)
        | ClassMember::StaticBlock(_)
        | ClassMember::IndexSignature(_)
        | ClassMember::Missing(_) => DeclIdentity::Anonymous,
        ClassMember::Method(method) => property_identity(&method.name, file),
        ClassMember::Property(property) => property_identity(&property.name, file),
        ClassMember::AutoAccessor(accessor) => property_identity(&accessor.name, file),
    };
    let raw = match member.data() {
        ClassMember::Method(method) => rebuild_children(
            file,
            member.range(),
            function_like_children(&method.function),
        ),
        ClassMember::Property(property) => {
            let Some(annotation) = &property.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        ClassMember::AutoAccessor(accessor) => {
            let Some(annotation) = &accessor.type_annotation else {
                return (identity, slice_node(file, member.range()));
            };
            replace_type_child(file, member.range(), &annotation.data().type_node)
        }
        ClassMember::IndexSignature(index) => {
            let mut children: Vec<&Ty> = Vec::new();
            for parameter in &index.parameters {
                if let Some(annotation) = &parameter.data().type_annotation {
                    children.push(&*annotation.data().type_node);
                }
            }
            children.push(&*index.type_annotation.data().type_node);
            rebuild_children(file, member.range(), children)
        }
        ClassMember::Constructor(_) | ClassMember::StaticBlock(_) | ClassMember::Missing(_) => {
            slice_node(file, member.range())
        }
    };
    (identity, raw)
}

/// Ordered type children of a function-like declaration: type-parameter
/// constraints/defaults, parameter annotations, then the return annotation.
fn function_like_children(function: &FunctionLike) -> Vec<&Ty> {
    let mut children = type_parameter_children(function.type_parameters.as_ref());
    for parameter in &function.parameters {
        if let Some(annotation) = &parameter.data().type_annotation {
            children.push(&*annotation.data().type_node);
        }
    }
    if let Some(return_type) = &function.return_type {
        children.push(&*return_type.data().type_node);
    }
    children
}

/// Replaces the single child type inside `range` with its canonical form so
/// nested object-type members canonicalize wherever they appear.
fn replace_type_child(file: &SourceFile, range: TextRange, child: &Ty) -> String {
    let head = slice_range(file, range.start(), child.range().start());
    let tail = slice_range(file, child.range().end(), range.end());
    assemble(&[head, canonical_type(child, file), tail])
}

/// Replaces a string-literal child with normalized (unquoted) text so quote
/// style is formatting-only.
fn replace_string_child(
    file: &SourceFile,
    range: TextRange,
    literal: &StringLiteralNode,
    replacement: &str,
) -> String {
    let head = slice_range(file, range.start(), literal.range().start());
    let tail = slice_range(file, literal.range().end(), range.end());
    assemble(&[head, replacement.to_owned(), tail])
}

/// Canonicalizes a type node: object-type member lists are grouped and sorted
/// by the declaration rule; every other AST `Vec` (union/intersection
/// constituents, tuple elements, parameters, type arguments, heritage, enum
/// members) keeps source order because order is semantic there.
fn canonical_type(ty: &Ty, file: &SourceFile) -> String {
    let range = ty.range();
    match ty.data() {
        TypeNode::Object(object) => {
            let members = canonical_type_members(&object.members, file);
            let head = declaration_head(file, range, &object.members, Vec::new());
            assemble_member_container(file, range, &object.members, members, head)
        }
        TypeNode::Union(types) => rebuild_children(file, range, types.iter().collect()),
        TypeNode::Intersection(types) => rebuild_children(file, range, types.iter().collect()),
        TypeNode::Array(inner) => rebuild_children(file, range, vec![&**inner]),
        TypeNode::Parenthesized(inner) => rebuild_children(file, range, vec![&**inner]),
        TypeNode::Tuple(tuple) => rebuild_children(
            file,
            range,
            tuple
                .elements
                .iter()
                .map(|element| &*element.type_node)
                .collect(),
        ),
        TypeNode::Function(function) => function_type_children(file, range, function),
        TypeNode::Constructor(construct) => {
            function_type_children(file, range, &construct.function)
        }
        TypeNode::Reference(reference) => {
            type_argument_children(file, range, reference.type_arguments.as_ref())
        }
        TypeNode::Query(query) => {
            type_argument_children(file, range, query.type_arguments.as_ref())
        }
        TypeNode::Operator { operand, .. } => rebuild_children(file, range, vec![&**operand]),
        TypeNode::IndexedAccess(access) => {
            rebuild_children(file, range, vec![&*access.object_type, &*access.index_type])
        }
        TypeNode::Conditional(conditional) => rebuild_children(
            file,
            range,
            vec![
                &*conditional.check_type,
                &*conditional.extends_type,
                &*conditional.true_type,
                &*conditional.false_type,
            ],
        ),
        TypeNode::Mapped(mapped) => {
            let mut children: Vec<&Ty> = Vec::new();
            if let Some(constraint) = &mapped.parameter.data().constraint {
                children.push(&**constraint);
            }
            if let Some(name) = &mapped.name_type {
                children.push(&**name);
            }
            if let Some(value) = &mapped.value_type {
                children.push(&**value);
            }
            rebuild_children(file, range, children)
        }
        TypeNode::Infer(infer) => match &infer.parameter.data().constraint {
            Some(constraint) => rebuild_children(file, range, vec![&**constraint]),
            None => slice_node(file, range),
        },
        TypeNode::Import(import) => {
            type_argument_children(file, range, import.type_arguments.as_ref())
        }
        TypeNode::TemplateLiteral(template) => {
            rebuild_children(file, range, template.types.iter().collect())
        }
        TypeNode::Predicate(predicate) => match &predicate.type_node {
            Some(inner) => rebuild_children(file, range, vec![&**inner]),
            None => slice_node(file, range),
        },
        TypeNode::Keyword(_) | TypeNode::Literal(_) | TypeNode::This | TypeNode::Missing(_) => {
            slice_node(file, range)
        }
    }
}

fn function_type_children(file: &SourceFile, range: TextRange, function: &FunctionType) -> String {
    let mut children: Vec<&Ty> = type_parameter_children(function.type_parameters.as_ref());
    children.extend(
        function
            .parameters
            .iter()
            .map(|parameter| &*parameter.type_annotation.data().type_node),
    );
    children.push(&*function.return_type);
    rebuild_children(file, range, children)
}

fn type_parameter_children(parameters: Option<&TypeParameterList>) -> Vec<&Ty> {
    let mut children = Vec::new();
    let Some(parameters) = parameters else {
        return children;
    };
    for parameter in &parameters.parameters {
        if let Some(constraint) = &parameter.data().constraint {
            children.push(&**constraint);
        }
        if let Some(default) = &parameter.data().default {
            children.push(&**default);
        }
    }
    children
}

fn type_argument_children(
    file: &SourceFile,
    range: TextRange,
    arguments: Option<&TypeArgumentList>,
) -> String {
    match arguments {
        Some(arguments) => rebuild_children(file, range, arguments.arguments.iter().collect()),
        None => slice_node(file, range),
    }
}

/// Rebuilds `range`'s source text with every child type replaced by its
/// canonical form, preserving ordered children and the gaps between them.
fn rebuild_children(file: &SourceFile, range: TextRange, children: Vec<&Ty>) -> String {
    if children.is_empty() {
        return slice_node(file, range);
    }
    let mut parts: Vec<String> = Vec::new();
    let mut cursor = range.start();
    for child in children {
        parts.push(slice_range(file, cursor, child.range().start()));
        parts.push(canonical_type(child, file));
        cursor = child.range().end();
    }
    parts.push(slice_range(file, cursor, range.end()));
    assemble(&parts)
}

/// One record in a structural baseline section, positioned by indentation.
struct BaselineRecord {
    identity: DeclIdentity,
    content: String,
    children: Vec<BaselineRecord>,
}

/// Canonicalizes a `.types`/`.symbols` baseline. Section headers stay in
/// source order. Within each section, records form an indentation tree whose
/// children are grouped and sorted only when every identity is a distinct
/// simple name; all other order is preserved.
fn canonicalize_record_baseline(
    text: &str,
    is_section_header: fn(&str) -> bool,
    record_of: fn(&str) -> Option<(usize, DeclIdentity, String)>,
) -> Vec<String> {
    let mut canonical: Vec<String> = Vec::new();
    let mut records: Vec<(usize, DeclIdentity, String)> = Vec::new();
    let flush = |canonical: &mut Vec<String>, records: &mut Vec<(usize, DeclIdentity, String)>| {
        let mut tree: Vec<(DeclIdentity, String)> = build_baseline_tree(records)
            .iter()
            .map(|node| (node.identity.clone(), canonical_baseline_node(node)))
            .collect();
        records.clear();
        sort_declaration_groups(&mut tree);
        for (_, content) in tree {
            canonical.push(content);
        }
    };
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if is_section_header(trimmed) {
            flush(&mut canonical, &mut records);
            canonical.push(normalize_record_line(trimmed));
        } else if let Some(record) = record_of(line) {
            records.push(record);
        } else {
            // An unrecognized display line acts as an order barrier.
            flush(&mut canonical, &mut records);
            canonical.push(normalize_record_line(trimmed));
        }
    }
    flush(&mut canonical, &mut records);
    canonical
}

fn build_baseline_tree(records: &[(usize, DeclIdentity, String)]) -> Vec<BaselineRecord> {
    struct Node {
        indent: usize,
        identity: DeclIdentity,
        content: String,
        parent: Option<usize>,
        children: Vec<usize>,
    }
    let mut nodes: Vec<Node> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    for (indent, identity, content) in records {
        while stack
            .last()
            .is_some_and(|&top| nodes[top].indent >= *indent)
        {
            stack.pop();
        }
        let index = nodes.len();
        let parent = stack.last().copied();
        nodes.push(Node {
            indent: *indent,
            identity: identity.clone(),
            content: content.clone(),
            parent,
            children: Vec::new(),
        });
        if let Some(parent) = parent {
            nodes[parent].children.push(index);
        }
        stack.push(index);
    }
    fn convert(nodes: &[Node], index: usize) -> BaselineRecord {
        BaselineRecord {
            identity: nodes[index].identity.clone(),
            content: nodes[index].content.clone(),
            children: nodes[index]
                .children
                .iter()
                .map(|&child| convert(nodes, child))
                .collect(),
        }
    }
    (0..nodes.len())
        .filter(|&index| nodes[index].parent.is_none())
        .map(|index| convert(&nodes, index))
        .collect()
}

fn canonical_baseline_node(node: &BaselineRecord) -> String {
    let mut children: Vec<(DeclIdentity, String)> = node
        .children
        .iter()
        .map(|child| (child.identity.clone(), canonical_baseline_node(child)))
        .collect();
    sort_declaration_groups(&mut children);
    let mut out = normalize_record_line(&strip_comments(&node.content));
    for (_, child) in children {
        out.push('\n');
        out.push_str(&child);
    }
    out
}

fn is_types_section(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with("===") && trimmed.ends_with("===")
}

fn types_record(line: &str) -> Option<(usize, DeclIdentity, String)> {
    let trimmed = line.trim_start();
    let after_marker = trimmed.strip_prefix('>')?;
    let content = after_marker.trim_start();
    if content.is_empty() {
        return None;
    }
    // Indentation is the whitespace before `>` plus the whitespace after it, so
    // `>   memberA` nests under a `> type T = {` owner exactly like tsc emits.
    let indent = leading_indent(trimmed) + leading_indent(after_marker);
    Some((indent, types_record_identity(content), content.to_owned()))
}

/// The declared identity of a `.types` display record: the first identifier
/// after an optional declaration keyword, so `> var x: number` and
/// `> function f(...)` identify as `x` and `f` and overloads merge. A trailing
/// `:` is stripped so `x:` and `x :` formatting both identify as `x` and stay
/// one merge group.
fn types_record_identity(content: &str) -> DeclIdentity {
    let mut words = content.split_whitespace();
    let Some(first) = words.next() else {
        return DeclIdentity::Anonymous;
    };
    let name = if is_declaration_keyword(first) {
        words.next().unwrap_or("")
    } else {
        first
    };
    // Cut parameter lists so every overload of `f` identifies as `f` and stays
    // one source-ordered merge group: `f(a:` and `f(b:` both reduce to `f`.
    let name = name.split('(').next().unwrap_or("").trim_end_matches(':');
    if name.is_empty() {
        DeclIdentity::Anonymous
    } else {
        DeclIdentity::Simple(name.to_owned())
    }
}

fn is_declaration_keyword(word: &str) -> bool {
    matches!(
        word,
        "var"
            | "let"
            | "const"
            | "function"
            | "class"
            | "interface"
            | "type"
            | "enum"
            | "namespace"
            | "module"
            | "declare"
            | "export"
            | "default"
            | "abstract"
            | "async"
            | "readonly"
            | "static"
            | "get"
            | "set"
            | "accessor"
            | "new"
            | "method"
            | "property"
            | "constructor"
            | "import"
            | "from"
    )
}

fn is_symbols_section(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.starts_with('[') && trimmed.ends_with(']')
}

fn symbols_record(line: &str) -> Option<(usize, DeclIdentity, String)> {
    let indent = leading_indent(line);
    let content = line.trim_start();
    if content.starts_with('[') && content.ends_with(']') {
        return None;
    }
    let (name, _) = content.split_once(" : ")?;
    let name = name.trim();
    if name.is_empty() {
        return None;
    }
    Some((
        indent,
        DeclIdentity::Simple(name.to_owned()),
        content.to_owned(),
    ))
}

fn normalize_block_lines(text: &str) -> String {
    text.lines()
        .map(normalize_record_line)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn normalize_record_line(line: &str) -> String {
    let mut output = String::new();
    let mut chars = line.char_indices().peekable();
    while let Some((start, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        let end = if matches!(ch, '"' | '\'' | '`') {
            string_token_end(line, &mut chars, ch)
        } else if ch.is_ascii_digit() {
            number_token_end(line, &mut chars)
        } else if is_identifier_char(ch) {
            token_end(line, &mut chars, is_identifier_char)
        } else {
            punctuation_token_end(line, start, ch, &mut chars)
        };
        let token = &line[start..end];
        output.push_str(&token.len().to_string());
        output.push(':');
        output.push_str(token);
        output.push('|');
    }
    output
}

fn string_token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    quote: char,
) -> usize {
    let mut escaped = false;
    for (index, ch) in chars.by_ref() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
        } else if ch == quote {
            return index + ch.len_utf8();
        }
    }
    line.len()
}

fn number_token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    let mut end = line.len();
    let mut exponent = false;
    while let Some(&(index, ch)) = chars.peek() {
        let continues = ch.is_ascii_alphanumeric()
            || matches!(ch, '_' | '.')
            || (exponent && matches!(ch, '+' | '-'));
        if !continues {
            end = index;
            break;
        }
        exponent = matches!(ch, 'e' | 'E');
        chars.next();
    }
    end
}

fn punctuation_token_end(
    line: &str,
    start: usize,
    first: char,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
) -> usize {
    // `>>`/`>>>` are deliberately absent: the parser splits them in type
    // context, so `A<B<C>>` and `A<B<C> >` are both valid and must normalize
    // to the same two `>` tokens. `>>=` stays compound because it only occurs
    // as a single operator in expressions.
    const COMPOUND: &[&str] = &[
        ">>>=", "===", "!==", "<<=", ">>=", "**=", "&&=", "||=", "??=", "...", "=>", "==", "!=",
        "<=", ">=", "++", "--", "&&", "||", "??", "?.", "**", "<<", "+=", "-=", "*=", "/=", "%=",
        "&=", "|=", "^=", "</", "/>",
    ];
    let remainder = &line[start..];
    let length = COMPOUND
        .iter()
        .find(|token| remainder.starts_with(**token))
        .map_or(first.len_utf8(), |token| token.len());
    let end = start + length;
    while chars.peek().is_some_and(|(index, _)| *index < end) {
        chars.next();
    }
    end
}

fn token_end(
    line: &str,
    chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>,
    continues: fn(char) -> bool,
) -> usize {
    let mut end = line.len();
    while let Some(&(index, ch)) = chars.peek() {
        if !continues(ch) {
            end = index;
            break;
        }
        chars.next();
    }
    end
}

fn is_identifier_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '$') || !ch.is_ascii()
}

fn leading_indent(line: &str) -> usize {
    line.chars()
        .take_while(|ch| *ch == ' ' || *ch == '\t')
        .map(|ch| if ch == '\t' { 4 } else { 1 })
        .sum()
}

fn strip_comments(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut index = 0;
    let mut in_line_comment = false;
    let mut in_block_comment = false;
    let mut in_string: Option<u8> = None;

    while index < bytes.len() {
        let byte = bytes[index];
        if in_line_comment {
            if byte == b'\n' {
                in_line_comment = false;
                output.push('\n');
            }
            index += 1;
            continue;
        }
        if in_block_comment {
            if byte == b'*' && index + 1 < bytes.len() && bytes[index + 1] == b'/' {
                in_block_comment = false;
                index += 2;
                continue;
            }
            if byte == b'\n' {
                output.push('\n');
            }
            index += 1;
            continue;
        }
        if let Some(quote) = in_string {
            output.push(byte as char);
            if byte == b'\\' && index + 1 < bytes.len() {
                output.push(bytes[index + 1] as char);
                index += 2;
                continue;
            }
            if byte == quote {
                in_string = None;
            }
            index += 1;
            continue;
        }

        if byte == b'"' || byte == b'\'' || byte == b'`' {
            in_string = Some(byte);
            output.push(byte as char);
            index += 1;
            continue;
        }
        if byte == b'/' && index + 1 < bytes.len() {
            match bytes[index + 1] {
                b'/' => {
                    // Every line comment is stripped, including triple-slash
                    // directives: only the file prologue carries semantic
                    // directives, and `triple_slash_directives` collects those
                    // from the raw text separately. A directive outside the
                    // prologue is inert and must not leak into the canonical
                    // form.
                    in_line_comment = true;
                    index += 2;
                    continue;
                }
                b'*' => {
                    in_block_comment = true;
                    index += 2;
                    continue;
                }
                _ => {}
            }
        }
        output.push(byte as char);
        index += 1;
    }

    output
}

fn is_semantic_triple_slash_directive(comment: &str) -> bool {
    let Some(reference) = comment
        .trim()
        .strip_prefix("///")
        .map(str::trim)
        .and_then(|body| body.strip_prefix("<reference"))
    else {
        return false;
    };
    if !reference.starts_with(char::is_whitespace) || !reference.trim_end().ends_with("/>") {
        return false;
    }
    ["path", "types", "lib", "no-default-lib"]
        .iter()
        .any(|attribute| {
            reference.match_indices(attribute).any(|(index, _)| {
                reference[..index]
                    .chars()
                    .next_back()
                    .is_some_and(char::is_whitespace)
                    && reference[index + attribute.len()..]
                        .trim_start()
                        .starts_with('=')
            })
        })
}

/// JS facet observation captured under a pinned, bounded [`NodeOracle`].
///
/// Raw [`OracleOutcome`] values are forgeable and therefore insufficient as a
/// public proof input. Construction goes through [`VerifiedJsOutcome::capture`],
/// which requires Node [`crate::corpus::NODE_VERSION`] verification plus case
/// timeout/output bounds enforced by the oracle runner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedJsOutcome {
    outcome: OracleOutcome,
}

impl VerifiedJsOutcome {
    /// Runs `case` under `oracle` (pinned Node [`crate::corpus::NODE_VERSION`],
    /// bounded I/O).
    ///
    /// `NodeOracle::new` / `discover` already verify the pinned interpreter
    /// before `run_case` applies case timeout and output caps.
    pub fn capture(oracle: &NodeOracle, case: &CaseSpec) -> Result<Self> {
        Ok(Self {
            outcome: oracle.run_case(case)?,
        })
    }

    /// Borrows the captured oracle outcome for inspection.
    #[must_use]
    pub fn outcome(&self) -> &OracleOutcome {
        &self.outcome
    }
}

/// Behavioral `.js` comparator for oracle-proven outcomes.
///
/// Matching empty stdout cannot pass: the facet returns
/// [`FacetVerdict::Unproven`] so another owned facet must prove the case.
pub fn compare_js(expected: &VerifiedJsOutcome, actual: &VerifiedJsOutcome) -> FacetVerdict {
    compare_js_outcomes(expected.outcome(), actual.outcome())
}

/// Runs both programs under pinned [`NodeOracle`] instances, then compares
/// stdout bytes and exit code under the same parity key and limits as `corpus.rs`.
pub fn compare_js_cases(
    expected_oracle: &NodeOracle,
    expected_case: &CaseSpec,
    actual_oracle: &NodeOracle,
    actual_case: &CaseSpec,
) -> Result<FacetVerdict> {
    let expected = VerifiedJsOutcome::capture(expected_oracle, expected_case)?;
    let actual = VerifiedJsOutcome::capture(actual_oracle, actual_case)?;
    Ok(compare_js(&expected, &actual))
}

fn compare_js_outcomes(expected: &OracleOutcome, actual: &OracleOutcome) -> FacetVerdict {
    if !expected.is_reliable() {
        return FacetVerdict::Fail {
            reason: "expected JS outcome is unreliable (timeout or truncated stdout)".to_owned(),
        };
    }
    if !actual.is_reliable() {
        return FacetVerdict::Fail {
            reason: "actual JS outcome is unreliable (timeout or truncated stdout)".to_owned(),
        };
    }

    if expected.exit_code != actual.exit_code {
        return FacetVerdict::Fail {
            reason: format!(
                "JS exit_code mismatch: expected {:?} actual {:?}",
                expected.exit_code, actual.exit_code
            ),
        };
    }

    if expected.stdout != actual.stdout {
        return FacetVerdict::Fail {
            reason: format!(
                "JS stdout mismatch: expected {} bytes actual {} bytes",
                expected.stdout.len(),
                actual.stdout.len()
            ),
        };
    }

    if expected.stdout.is_empty() {
        return FacetVerdict::Unproven {
            reason:
                "empty stdout cannot prove JS facet parity by itself; prove via another owned facet"
                    .to_owned(),
        };
    }

    FacetVerdict::Pass
}

fn schema_error(detail: impl Into<String>) -> VerificationError {
    VerificationError::new(ErrorCode::Schema, detail)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::{OracleOutcome, Provenance};

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
    fn structural_types_survive_formatting_and_order_normalization() {
        let expected = "=== a.ts ===\n> var x: number\n> var y: string\n";
        let actual = "=== a.ts ===\n\n>   var   y:   string\n> var x: number\n";
        assert!(compare_types(expected, actual).is_pass());
    }

    #[test]
    fn structural_types_reject_semantic_differences() {
        let expected = "> var x: number\n";
        let actual = "> var x: string\n";
        assert!(compare_types(expected, actual).is_fail());
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
            compare_js_outcomes(&forged_expected, &forged_actual).is_pass(),
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
        // parser (P) codes are still unmapped and will be resolved by later
        // slices.
        let mut mapped = 0;
        for code in REQUIRED_BAMTS_DIAGNOSTIC_CODES {
            let entry = map.get(code).expect(code);
            assert!(!entry.evidence.trim().is_empty());
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
