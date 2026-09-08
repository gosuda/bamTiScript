//! Types-facet sampler: compile stratified sample cases, emit `.types`,
//! compare against authority baselines, classify first-delta families, and
//! write a structured report to `target/tmp/`.
//!
//! The sample list is read from the file path in `BAMTS_TYPES_SAMPLE`
//! (one logical path per line). An optional cfg mapping can be provided
//! via `BAMTS_TYPES_CFG` (JSONL with `{"case":"...","cfg":"..."}` rows);
//! if unset, `{sample_path}.cfg.jsonl` is tried.
//!
//! The authority root is read from `BAMTS_AUTHORITY_ROOT` (default:
//! `/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests`).
//!
//! Run with:
//!   BAMTS_TYPES_SAMPLE=path/to/sample.txt \
//!   cargo test -p bamts-verification --test types_facet_sampler -- --ignored --nocapture

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

use bamts_verification::catalog::parse_case_configuration;
use bamts_verification::check_cells::{
    CasePragmas, case_stem, compile_case_with_pragmas, emit_types_baseline, entry_virtual_path,
    parse_case_pragmas, split_case_units,
};
use bamts_verification::facets::{FacetVerdict, compare_types};
use bamts_verification::suite::decode_case_source;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn authority_root() -> PathBuf {
    PathBuf::from(env::var("BAMTS_AUTHORITY_ROOT").unwrap_or_else(|_| {
        "/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests".to_owned()
    }))
}

fn baseline_dir() -> PathBuf {
    authority_root().join("tests/baselines/reference")
}

/// One case in the sample.
struct SampleCase {
    logical_path: String,
    cfg: String,
}

impl SampleCase {
    /// Pragmas driving compile and baseline selection for this case.
    ///
    /// A supplied cfg names the exact catalog configuration to compile (the
    /// compiler-lane `<variant>` from `<variant>#<observable>`); an empty cfg
    /// keeps the source-directive behavior (`parse_case_pragmas`, first
    /// declared value per option). Unknown variants and directive parse
    /// failures panic: the sampler never silently falls back to a variant
    /// the caller did not request.
    fn pragmas(&self, source_text: &str) -> CasePragmas {
        match self.cfg.as_str() {
            "" => parse_case_pragmas(source_text),
            variant => {
                let configurations = parse_case_configuration(source_text)
                    .unwrap_or_else(|error| panic!("{}: {error}", self.logical_path));
                let configuration = configurations
                    .iter()
                    .find(|item| item.name == variant)
                    .unwrap_or_else(|| {
                        panic!("{}: no configuration `{variant}`", self.logical_path)
                    });
                CasePragmas::from_configuration(configuration)
            }
        }
    }
}

/// Result of analyzing one case.
#[derive(Clone)]
struct AnalysisResult {
    case: String,
    cfg: String,
    outcome: Outcome,
}

#[derive(Debug, Clone)]
enum Outcome {
    Pass,
    Mismatch {
        family: String,
        first_expected: String,
        first_actual: String,
        expected_line: usize,
        actual_line: usize,
        section: String,
    },
    CompileError(String),
    NoBaseline,
    BaselineUnproven,
}

/// Parse the sample file list and optional cfg mapping.
fn load_sample() -> Vec<SampleCase> {
    let sample_path = env::var("BAMTS_TYPES_SAMPLE")
        .expect("BAMTS_TYPES_SAMPLE must point to a sample list file (one logical path per line)");
    let cfg_path =
        env::var("BAMTS_TYPES_CFG").unwrap_or_else(|_| format!("{sample_path}.cfg.jsonl"));

    let cases: Vec<String> = fs::read_to_string(&sample_path)
        .unwrap_or_else(|_| panic!("failed to read sample list: {sample_path}"))
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.trim().to_owned())
        .collect();

    // Build case -> cfg map from optional JSONL file
    let mut cfg_map: BTreeMap<String, String> = BTreeMap::new();
    if let Ok(cfg_text) = fs::read_to_string(&cfg_path) {
        for line in cfg_text.lines() {
            if line.is_empty() {
                continue;
            }
            if let Ok(val) = serde_json::from_str::<serde_json::Value>(line)
                && let (Some(case), Some(cfg)) = (val["case"].as_str(), val["cfg"].as_str())
            {
                cfg_map.insert(case.to_owned(), cfg.to_owned());
            }
        }
    }

    cases
        .into_iter()
        .map(|case| {
            let cfg = cfg_map.get(&case).cloned().unwrap_or_default();
            SampleCase {
                logical_path: case,
                cfg,
            }
        })
        .collect()
}

/// Resolve the authority case source path from the logical path.
fn authority_case_path(logical: &str) -> PathBuf {
    let stripped = logical
        .strip_prefix("compiler/tests/cases/")
        .or_else(|| logical.strip_prefix("conformance/tests/cases/"))
        .unwrap_or(logical);
    authority_root().join("tests/cases").join(stripped)
}

/// Resolve the baseline file for a case stem and its compile options.
fn resolve_baseline_fs(stem: &str, pragmas: &CasePragmas) -> Option<PathBuf> {
    let base = baseline_dir();
    // Authority trees nest baselines one level down
    // (`reference/<area>/*.types`); scan the top level and one down.
    let mut dirs = vec![base.clone()];
    if let Ok(entries) = fs::read_dir(&base) {
        dirs.extend(
            entries
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.is_dir()),
        );
    }
    let plain_name = format!("{stem}.types");
    let prefix = format!("{stem}(");
    let mut plain: Option<PathBuf> = None;
    let mut variants: Vec<(String, PathBuf)> = Vec::new();
    for dir in &dirs {
        let Ok(entries) = fs::read_dir(dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if name == plain_name {
                plain = Some(entry.path());
            } else if name.starts_with(&prefix) && name.ends_with(").types") {
                let suffix = &name[prefix.len()..name.len() - ".types".len() - 1];
                variants.push((suffix.to_owned(), entry.path()));
            }
        }
    }

    let compile_options: Vec<(String, String)> = pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|v| (name.clone(), v.clone())))
        .collect();

    if !compile_options.is_empty() {
        let matches: Vec<_> = variants
            .iter()
            .filter(|(suffix, _)| suffix_matches_options(suffix, &compile_options))
            .collect();
        if matches.len() == 1 {
            return Some(matches[0].1.clone());
        }
    }

    if let Some(plain) = plain {
        return Some(plain);
    }

    variants.sort_by(|a, b| a.0.cmp(&b.0));
    variants.into_iter().next().map(|(_, p)| p)
}

/// Check if a variant suffix matches compile options.
fn suffix_matches_options(suffix: &str, compile_options: &[(String, String)]) -> bool {
    if suffix.is_empty() {
        return true;
    }
    let options: std::collections::HashMap<String, String> = compile_options
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    for part in suffix.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let Some((key, value)) = part.split_once('=') else {
            return false;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_ascii_lowercase();
        let Some(compile_value) = options.get(&key) else {
            return false;
        };
        if compile_value.to_ascii_lowercase() != value {
            return false;
        }
    }
    true
}

/// Mirror the comparator's whitespace handling: collapse every whitespace run
/// to one space before comparing, so display-echo spacing (e.g. `{ a, b }` vs
/// `{        a,        b    }`) is not reported as a delta the comparator
/// would normalize away. Caret runs stay token-distinct (`^ ^^^` differs
/// from `^^^^^^`), matching `facets::normalize_record_line` tokenization.
fn comparator_comparable(line: &str) -> String {
    line.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Whether a `>`-prefixed line is a caret annotation (`>  : ^^^`) rather than
/// a type record (`>display : type`). Caret lines have no display name before
/// the colon — their content after `>` starts with `:` or is empty.
fn is_caret_line(line: &str) -> bool {
    let after = line.strip_prefix('>').unwrap_or(line);
    let content = after.trim_start();
    content.starts_with(':') || content.trim().is_empty()
}

/// Find the first differing line pair, prioritizing type records (`>`).
/// Skips the `//// [path] ////` marker line (line 1) and empty lines.
fn first_diff(expected: &str, actual: &str) -> Option<(usize, String, usize, String)> {
    let exp_lines: Vec<&str> = expected.lines().collect();
    let act_lines: Vec<&str> = actual.lines().collect();

    // Collect all type-record lines (starting with '>') from both sides,
    // excluding caret lines (`>  : ^^^`). Caret lines are visual annotations
    // of the preceding `>display : type` record; when the type string differs
    // the caret line differs too, but that is a type-display issue, not a
    // wrong-expression issue. Including them causes misalignment: the first
    // diff lands on a caret line, `classify_diff` sees an empty display vs a
    // real display, and misclassifies as `wrong-expression-typed` instead of
    // `type-display-mismatch-other`.
    // Verified: `argumentsBindsToFunctionScopeArgumentList.types:7` has
    // `>foo : (a: any) => void` followed by `>    : ^ ^^^^^^^^^^^^^^`.

    let exp_records: Vec<(usize, &str)> = exp_lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with('>') && !is_caret_line(l))
        .map(|(i, l)| (i, *l))
        .collect();
    let act_records: Vec<(usize, &str)> = act_lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with('>') && !is_caret_line(l))
        .map(|(i, l)| (i, *l))
        .collect();

    // If actual has no record lines but expected does, report first expected
    if act_records.is_empty() && !exp_records.is_empty() {
        let (ln, line) = exp_records[0];
        return Some((
            ln + 1,
            line.trim_end().to_owned(),
            0,
            "<MISSING>".to_owned(),
        ));
    }

    // Compare record lines pairwise
    let max = exp_records.len().max(act_records.len());
    for i in 0..max {
        let (exp_ln, exp_line) = exp_records.get(i).copied().unwrap_or((0, "<MISSING>"));
        let (act_ln, act_line) = act_records.get(i).copied().unwrap_or((0, "<MISSING>"));
        let exp_norm = comparator_comparable(exp_line);
        let act_norm = comparator_comparable(act_line);
        if exp_norm != act_norm {
            return Some((
                exp_ln + 1,
                exp_norm.to_owned(),
                act_ln + 1,
                act_norm.to_owned(),
            ));
        }
    }

    // If all record lines match, fall back to first non-record, non-marker diff
    let max = exp_lines.len().max(act_lines.len());
    for i in 1..max {
        let exp = exp_lines.get(i).copied().unwrap_or("<MISSING>");
        let act = act_lines.get(i).copied().unwrap_or("<MISSING>");
        if exp.trim().is_empty() && act.trim().is_empty() {
            continue;
        }
        if exp.trim_start().starts_with("===") && act.trim_start().starts_with("===") {
            // Section header mismatch — report it
            let exp_norm = comparator_comparable(exp);
            let act_norm = comparator_comparable(act);
            if exp_norm != act_norm {
                return Some((i + 1, exp_norm.to_owned(), i + 1, act_norm.to_owned()));
            }
            continue;
        }
        let exp_norm = comparator_comparable(exp);
        let act_norm = comparator_comparable(act);
        if exp_norm != act_norm {
            return Some((i + 1, exp_norm.to_owned(), i + 1, act_norm.to_owned()));
        }
    }
    None
}

/// Extract the section name from a line like "=== foo.ts ==="
fn section_of(line: &str) -> String {
    let trimmed = line.trim();
    if trimmed.starts_with("===") && trimmed.ends_with("===") {
        trimmed
            .trim_start_matches('=')
            .trim_end_matches('=')
            .trim()
            .to_owned()
    } else {
        String::new()
    }
}

/// Find the section context around a diff line.
fn section_context(text: &str, line_num: usize) -> String {
    let lines: Vec<&str> = text.lines().collect();
    for i in (0..line_num.saturating_sub(1)).rev() {
        let s = section_of(lines[i]);
        if !s.is_empty() {
            return s;
        }
    }
    String::new()
}

/// Extract the display name (left side of ` : `) from a `>display : type` record.
fn extract_display(line: &str) -> String {
    let after_marker = line.strip_prefix('>').unwrap_or(line);
    let content = after_marker.trim_start();
    if let Some(colon_pos) = content.find(" : ") {
        content[..colon_pos].trim().to_owned()
    } else {
        content.trim().to_owned()
    }
}

/// Extract the type string (right side of ` : `) from a `>display : type` record.
fn extract_type_string(line: &str) -> String {
    let after_marker = line.strip_prefix('>').unwrap_or(line);
    let content = after_marker.trim_start();
    if let Some(colon_pos) = content.find(" : ") {
        content[colon_pos + 3..].trim().to_owned()
    } else {
        String::new()
    }
}

/// Classify a diff into a family pattern for the types facet.
///
/// Observer-owned families (fixable in check_cells.rs):
/// - section-header-mismatch: multi-unit section naming differs
/// - duplicate-record: same record emitted twice
/// - record-ordering: records in wrong order
///
/// Compiler-owned families (handed off, not fixed here):
/// - ctor-literal-for-named-type: constructor-side type renders structurally
/// - any-for-specific-type: unresolved symbol falls back to `any`
/// - wrong-expression-typed: different sub-expression typed
/// - parameter-typed-instead-of-function: function expression not typed
/// - type-display-mismatch-other: wrong type string
/// - missing-records: checker coverage gap
/// - union-type-mismatch: union collapsed to any
/// - literal-for-widened-type: literal not widened
/// - typeof-display-missing: no typeof rendering
/// - generic-type-arg-mismatch: generic class constructor renders structurally
/// - structural-expansion-for-named: type alias not resolved
/// - promise-structural-for-named: Promise modeled as ad-hoc structural type
fn classify_diff(
    expected: &str,
    actual: &str,
    exp_line: &str,
    act_line: &str,
    _section: &str,
) -> String {
    let exp_is_record = exp_line.starts_with('>');
    let act_is_record = act_line.starts_with('>');

    // Section header mismatch
    if exp_line.starts_with("===") || act_line.starts_with("===") {
        return "section-header-mismatch".to_owned();
    }

    // Missing record in actual
    if exp_is_record && act_line == "<MISSING>" {
        // Check if it's a total coverage gap (many missing records)
        let exp_record_count = expected
            .lines()
            .filter(|l| l.starts_with('>') && !is_caret_line(l))
            .count();
        let act_record_count = actual
            .lines()
            .filter(|l| l.starts_with('>') && !is_caret_line(l))
            .count();
        if act_record_count == 0 {
            return "missing-records-total".to_owned();
        }
        if exp_record_count > 0 && act_record_count < exp_record_count / 2 {
            return "missing-records-partial".to_owned();
        }
        return "missing-record".to_owned();
    }

    // Extra record in actual
    if act_is_record && exp_line == "<MISSING>" {
        return "extra-record-in-actual".to_owned();
    }

    // Both are record lines but differ
    if exp_is_record && act_is_record {
        let exp_display = extract_display(exp_line);
        let act_display = extract_display(act_line);
        let exp_type = extract_type_string(exp_line);
        let act_type = extract_type_string(act_line);

        // Same display, different type — type display/inference issue
        if exp_display == act_display {
            // Classify by type mismatch pattern
            if act_type == "any" && exp_type != "any" {
                return "any-for-specific-type".to_owned();
            }
            if act_type.starts_with("{ new ") && !exp_type.starts_with("{ new ") {
                return "ctor-literal-for-named-type".to_owned();
            }
            if exp_type.starts_with("typeof ") && !act_type.starts_with("typeof ") {
                return "typeof-display-missing".to_owned();
            }
            if exp_type.contains(" | ") && !act_type.contains(" | ") {
                return "union-type-mismatch".to_owned();
            }
            // Literal where widened type expected
            let exp_literals = ["number", "string", "boolean"];
            let act_literals = ["1", "0", "true", "false", "\""];
            let exp_is_widened = exp_literals.iter().any(|w| exp_type == *w);
            let act_is_literal = act_literals.iter().any(|l| act_type.starts_with(l));
            if exp_is_widened && act_is_literal {
                return "literal-for-widened-type".to_owned();
            }
            if act_type.contains("__bamts_promise")
                || (act_type.starts_with("{ ") && exp_type.contains("Promise<"))
            {
                return "promise-structural-for-named".to_owned();
            }
            if exp_type.starts_with("{ ") && !act_type.starts_with("{ ") {
                return "structural-expansion-for-named".to_owned();
            }
            return "type-display-mismatch-other".to_owned();
        }

        // Different display — different expression typed
        // Check if actual is a parameter where function type expected
        if exp_display.contains('(') && !act_display.contains('(') {
            return "parameter-typed-instead-of-function".to_owned();
        }
        return "wrong-expression-typed".to_owned();
    }

    // Source line content differs (non-record)
    if !exp_is_record && !act_is_record {
        return "source-line-content-diff".to_owned();
    }

    "unclassified".to_owned()
}

#[test]
#[ignore]
fn types_facet_sample() {
    let sample = load_sample();
    let mut results: Vec<AnalysisResult> = Vec::new();

    for case in &sample {
        let case_path = authority_case_path(&case.logical_path);
        let source_text = match fs::read(&case_path).map(|bytes| decode_case_source(&bytes)) {
            Ok(text) => text,
            Err(_) => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::NoBaseline,
                });
                continue;
            }
        };
        let harness_logical = case
            .logical_path
            .strip_prefix("compiler/")
            .or_else(|| case.logical_path.strip_prefix("conformance/"))
            .unwrap_or(&case.logical_path)
            .to_owned();

        let pragmas = case.pragmas(&source_text);
        if pragmas.no_types_and_symbols {
            results.push(AnalysisResult {
                case: case.logical_path.clone(),
                cfg: case.cfg.clone(),
                outcome: Outcome::Pass,
            });
            continue;
        }

        let units = split_case_units(&harness_logical, &source_text);
        let entry = entry_virtual_path(&harness_logical, &units);

        let compiled = match compile_case_with_pragmas(&units, &entry, &pragmas) {
            Ok(case) => case,
            Err(error) => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::CompileError(format!("{error:?}")),
                });
                continue;
            }
        };

        let emitted = emit_types_baseline(&compiled, &harness_logical);
        let stem = case_stem(&harness_logical);
        let baseline_path = match resolve_baseline_fs(stem, &pragmas) {
            Some(path) => path,
            None => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::NoBaseline,
                });
                continue;
            }
        };

        let expected = match fs::read_to_string(&baseline_path) {
            Ok(text) => text,
            Err(_) => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::NoBaseline,
                });
                continue;
            }
        };

        let verdict = compare_types(&expected, &emitted);
        match verdict {
            FacetVerdict::Pass => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::Pass,
                });
            }
            FacetVerdict::Fail { .. } => {
                if let Some((exp_ln, exp_line, act_ln, act_line)) = first_diff(&expected, &emitted)
                {
                    let section = section_context(&expected, exp_ln);
                    let family = classify_diff(&expected, &emitted, &exp_line, &act_line, &section);
                    results.push(AnalysisResult {
                        case: case.logical_path.clone(),
                        cfg: case.cfg.clone(),
                        outcome: Outcome::Mismatch {
                            family,
                            first_expected: exp_line,
                            first_actual: act_line,
                            expected_line: exp_ln,
                            actual_line: act_ln,
                            section,
                        },
                    });
                } else {
                    let family = classify_diff(
                        &expected,
                        &emitted,
                        "(order-only mismatch)",
                        "(order-only mismatch)",
                        "",
                    );
                    results.push(AnalysisResult {
                        case: case.logical_path.clone(),
                        cfg: case.cfg.clone(),
                        outcome: Outcome::Mismatch {
                            family,
                            first_expected: "(order-only mismatch)".to_owned(),
                            first_actual: "(order-only mismatch)".to_owned(),
                            expected_line: 0,
                            actual_line: 0,
                            section: String::new(),
                        },
                    });
                }
            }
            FacetVerdict::Unproven { .. } => {
                results.push(AnalysisResult {
                    case: case.logical_path.clone(),
                    cfg: case.cfg.clone(),
                    outcome: Outcome::BaselineUnproven,
                });
            }
        }
    }

    // Aggregate results
    let mut pass_count = 0usize;
    let mut no_baseline = 0usize;
    let mut compile_error = 0usize;
    let mut unproven = 0usize;
    let mut mismatch_count = 0usize;
    let mut families: BTreeMap<String, Vec<AnalysisResult>> = BTreeMap::new();

    for result in &results {
        match &result.outcome {
            Outcome::Pass => pass_count += 1,
            Outcome::NoBaseline => no_baseline += 1,
            Outcome::CompileError(e) => {
                compile_error += 1;
                eprintln!("COMPILE_ERROR: {} | {}", result.case, e);
            }
            Outcome::BaselineUnproven => unproven += 1,
            Outcome::Mismatch { .. } => {
                mismatch_count += 1;
            }
        }
    }

    // Group mismatches by family
    for result in &results {
        if let Outcome::Mismatch { family, .. } = &result.outcome {
            families
                .entry(family.clone())
                .or_default()
                .push(result.clone());
        }
    }

    let total = results.len();

    // Build the report text
    let sample_path = env::var("BAMTS_TYPES_SAMPLE").unwrap_or_default();
    let auth_root = authority_root();
    let mut report = String::new();

    report.push_str("=== TYPES FACET SAMPLE ANALYSIS ===\n");
    report.push_str(&format!("Sample file: {sample_path}\n"));
    report.push_str(&format!("Authority root: {}\n", auth_root.display()));
    report.push_str(&format!("Total sampled: {total}\n"));
    report.push_str(&format!("Pass: {pass_count}\n"));
    report.push_str(&format!("Mismatch: {mismatch_count}\n"));
    report.push_str(&format!("Compile error: {compile_error}\n"));
    report.push_str(&format!("No baseline: {no_baseline}\n"));
    report.push_str(&format!("Unproven: {unproven}\n\n"));

    report.push_str("=== FAMILY TABLE (sorted by count) ===\n");
    let mut sorted_families: Vec<_> = families.iter().collect();
    sorted_families.sort_by_key(|(_, cases)| std::cmp::Reverse(cases.len()));

    for (family, cases) in &sorted_families {
        let count = cases.len();
        let pct = if mismatch_count > 0 {
            count as f64 / mismatch_count as f64 * 100.0
        } else {
            0.0
        };
        let extrapolated = (count as f64 / total as f64 * 13510.0).round() as usize;
        let compiler_count = cases
            .iter()
            .filter(|c| c.case.starts_with("compiler/"))
            .count();
        let conformance_count = count - compiler_count;
        report.push_str(&format!(
            "\n--- {family} (sample={count}, {pct:.1}%, extrapolated~{extrapolated}, compiler={compiler_count}, conformance={conformance_count}) ---\n"
        ));
        for r in cases.iter().take(3) {
            if let Outcome::Mismatch {
                first_expected,
                first_actual,
                expected_line,
                actual_line,
                section,
                ..
            } = &r.outcome
            {
                report.push_str(&format!("  CASE: {}\n", r.case));
                report.push_str(&format!("  CFG:  {}\n", r.cfg));
                report.push_str(&format!("  SECTION: {section}\n"));
                report.push_str(&format!(
                    "  EXPECTED line {expected_line}: {first_expected}\n"
                ));
                report.push_str(&format!("  ACTUAL   line {actual_line}: {first_actual}\n"));
            }
        }
    }

    report.push_str("\n=== MACHINE_READABLE ===\n");
    for (family, cases) in &sorted_families {
        let compiler_count = cases
            .iter()
            .filter(|c| c.case.starts_with("compiler/"))
            .count();
        let conformance_count = cases.len() - compiler_count;
        let pct = if mismatch_count > 0 {
            cases.len() as f64 / mismatch_count as f64 * 100.0
        } else {
            0.0
        };
        let extrapolated = (cases.len() as f64 / total as f64 * 13510.0).round() as usize;
        report.push_str(&format!(
            "FAMILY\t{}\t{}\t{:.1}\t{}\t{}\t{}\n",
            family,
            cases.len(),
            pct,
            extrapolated,
            compiler_count,
            conformance_count
        ));
    }

    // Write report to target/tmp/
    let report_dir = repo_root().join("target/tmp/types-facet-sampler");
    fs::create_dir_all(&report_dir).ok();
    let report_path = report_dir.join("report.txt");
    fs::write(&report_path, &report).ok();

    // Print summary to stderr (for --nocapture)
    eprintln!("\n=== TYPES FACET SAMPLE ANALYSIS ===");
    eprintln!("Total sampled: {total}");
    eprintln!("Pass: {pass_count}");
    eprintln!("Mismatch: {mismatch_count}");
    eprintln!("Compile error: {compile_error}");
    eprintln!("No baseline: {no_baseline}");
    eprintln!("Unproven: {unproven}");

    eprintln!("\n=== FAMILY TABLE (sorted by count) ===");
    for (family, cases) in &sorted_families {
        let count = cases.len();
        let pct = if mismatch_count > 0 {
            count as f64 / mismatch_count as f64 * 100.0
        } else {
            0.0
        };
        let extrapolated = (count as f64 / total as f64 * 13510.0).round() as usize;
        let compiler_count = cases
            .iter()
            .filter(|c| c.case.starts_with("compiler/"))
            .count();
        let conformance_count = count - compiler_count;
        eprintln!(
            "\n--- {family} (sample={count}, {pct:.1}%, extrapolated~{extrapolated}, compiler={compiler_count}, conformance={conformance_count}) ---"
        );
        for r in cases.iter().take(3) {
            if let Outcome::Mismatch {
                first_expected,
                first_actual,
                expected_line,
                actual_line,
                section,
                ..
            } = &r.outcome
            {
                eprintln!("  CASE: {}", r.case);
                eprintln!("  CFG:  {}", r.cfg);
                eprintln!("  SECTION: {section}");
                eprintln!("  EXPECTED line {expected_line}: {first_expected}");
                eprintln!("  ACTUAL   line {actual_line}: {first_actual}");
            }
        }
    }

    eprintln!("\n=== MACHINE_READABLE ===");
    for (family, cases) in &sorted_families {
        let compiler_count = cases
            .iter()
            .filter(|c| c.case.starts_with("compiler/"))
            .count();
        let conformance_count = cases.len() - compiler_count;
        let pct = if mismatch_count > 0 {
            cases.len() as f64 / mismatch_count as f64 * 100.0
        } else {
            0.0
        };
        let extrapolated = (cases.len() as f64 / total as f64 * 13510.0).round() as usize;
        eprintln!(
            "FAMILY\t{}\t{}\t{:.1}\t{}\t{}\t{}",
            family,
            cases.len(),
            pct,
            extrapolated,
            compiler_count,
            conformance_count
        );
    }

    eprintln!("\nReport written to: {}", report_path.display());
}

/// LCS-based alignment of record lines to sub-cluster wrong-expression-typed.
///
/// For each wrong-expression-typed case, align expected vs actual `>` records
/// using LCS. Cases where the display names differ at aligned positions are
/// (a) observer-side (wrong node set/order). Cases where expected records have
/// no match in actual are (b) compiler-side (missing type_of_expr entries).
#[test]
#[ignore]
fn types_facet_wrong_expr_diagnostic() {
    let sample = load_sample();
    let mut observer_side: Vec<String> = Vec::new();
    let mut compiler_side: Vec<String> = Vec::new();
    let mut ambiguous: Vec<String> = Vec::new();

    for case in &sample {
        let case_path = authority_case_path(&case.logical_path);
        let source_text = match fs::read(&case_path).map(|bytes| decode_case_source(&bytes)) {
            Ok(text) => text,
            Err(_) => continue,
        };
        let harness_logical = case
            .logical_path
            .strip_prefix("compiler/")
            .or_else(|| case.logical_path.strip_prefix("conformance/"))
            .unwrap_or(&case.logical_path)
            .to_owned();
        let pragmas = case.pragmas(&source_text);
        if pragmas.no_types_and_symbols {
            continue;
        }
        let units = split_case_units(&harness_logical, &source_text);
        let entry = entry_virtual_path(&harness_logical, &units);
        let compiled = match compile_case_with_pragmas(&units, &entry, &pragmas) {
            Ok(c) => c,
            Err(_) => continue,
        };
        let emitted = emit_types_baseline(&compiled, &harness_logical);
        let stem = case_stem(&harness_logical);
        let baseline_path = match resolve_baseline_fs(stem, &pragmas) {
            Some(p) => p,
            None => continue,
        };
        let expected = match fs::read_to_string(&baseline_path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let verdict = compare_types(&expected, &emitted);
        if verdict != FacetVerdict::Pass
            && let Some((_, exp_line, _, act_line)) = first_diff(&expected, &emitted)
        {
            let family = classify_diff(&expected, &emitted, &exp_line, &act_line, "");
            if family != "wrong-expression-typed" {
                continue;
            }
            // Extract record lines (only `>display : type` lines, not
            // caret lines), using the same predicate as `first_diff`.
            let exp_records: Vec<&str> = expected
                .lines()
                .filter(|l| l.starts_with('>') && !is_caret_line(l))
                .collect();
            let act_records: Vec<&str> = emitted
                .lines()
                .filter(|l| l.starts_with('>') && !is_caret_line(l))
                .collect();

            // LCS alignment on display names
            let exp_displays: Vec<String> =
                exp_records.iter().map(|l| extract_display(l)).collect();
            let act_displays: Vec<String> =
                act_records.iter().map(|l| extract_display(l)).collect();

            // Simple LCS on display names
            let m = exp_displays.len();
            let n = act_displays.len();
            let mut dp = vec![vec![0usize; n + 1]; m + 1];
            for i in 1..=m {
                for j in 1..=n {
                    if exp_displays[i - 1] == act_displays[j - 1] {
                        dp[i][j] = dp[i - 1][j - 1] + 1;
                    } else {
                        dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
                    }
                }
            }
            let lcs_len = dp[m][n];
            let match_ratio = if m > 0 {
                lcs_len as f64 / m as f64
            } else {
                0.0
            };

            // If most expected displays match actual displays, the diff is
            // at a specific position — likely (a) observer emitting wrong
            // node at that position. If many expected displays are missing,
            // it's (b) compiler not recording type_of_expr for those nodes.
            let exp_only = m.saturating_sub(lcs_len);
            let act_only = n.saturating_sub(lcs_len);

            let label = format!(
                "{} | exp_records={} act_records={} lcs={} exp_only={} act_only={} match_ratio={:.2} | EXP:{} | ACT:{}",
                case.logical_path,
                m,
                n,
                lcs_len,
                exp_only,
                act_only,
                match_ratio,
                exp_line,
                act_line
            );

            if exp_only > 3 && match_ratio < 0.5 {
                compiler_side.push(label);
            } else if exp_only <= 2 && act_only <= 2 {
                observer_side.push(label);
            } else {
                ambiguous.push(label);
            }
        }
    }

    eprintln!("\n=== WRONG-EXPRESSION-TYPED SUB-CLUSTER ===");
    eprintln!("Observer-side (a): {}", observer_side.len());
    for l in &observer_side {
        eprintln!("  {l}");
    }
    eprintln!("\nCompiler-side (b): {}", compiler_side.len());
    for l in &compiler_side {
        eprintln!("  {l}");
    }
    eprintln!("\nAmbiguous: {}", ambiguous.len());
    for l in &ambiguous {
        eprintln!("  {l}");
    }
}
