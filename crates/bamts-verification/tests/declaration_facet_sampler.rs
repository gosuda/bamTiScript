//! Declaration/source-map/javascript facet sampler: compile stratified sample cases
//! through the same code path the harness uses (`observe_declaration` /
//! `observe_source_map` / `observe_javascript` in `check_cells.rs`), compare
//! against authority baselines, classify first-delta families, and write a
//! structured report to `target/tmp/`.
//!
//! The facet is selected by `BAMTS_FACET` (`declaration`, `source-map`, or
//! `javascript`).  The sample list is read from the file path in
//! `BAMTS_FACET_SAMPLE` (one logical path per line).  An optional cfg mapping
//! can be provided via `BAMTS_FACET_CFG` (JSONL with `{"case":"...","cfg":"..."}`
//! rows); if unset, `{sample_path}.cfg.jsonl` is tried.
//!
//! The authority root is read from `BAMTS_AUTHORITY_ROOT` (default:
//! `/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests`).
//!
//! Run with:
//!   BAMTS_FACET=declaration \
//!   BAMTS_FACET_SAMPLE=path/to/sample.txt \
//!   cargo test -p bamts-verification --test declaration_facet_sampler -- --ignored --nocapture

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

use bamts_compiler::pipeline::FrontendMode;
use bamts_verification::check_cells::{
    CasePragmas, baseline_area, case_stem, compile_case_frontend, emit_declaration_baseline,
    emit_javascript_baseline, emit_source_map_baseline, entry_virtual_path, extract_dts_sections,
    parse_case_pragmas, resolve_baseline_file, split_case_units,
};
use bamts_verification::facets::{FacetVerdict, compare_js_emit, compare_source_map};

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
    EmitError(String),
    NoBaseline,
    BaselineUnproven,
    InlineSourceMapGap,
}

/// Parse the sample file list and optional cfg mapping.
fn load_sample() -> Vec<SampleCase> {
    let sample_path = env::var("BAMTS_FACET_SAMPLE").unwrap_or_else(|_| {
        "/home/alpha/compiler/bamTiScript/target/tmp/cluster-declaration/declaration_sample.txt"
            .to_owned()
    });
    let cfg_path =
        env::var("BAMTS_FACET_CFG").unwrap_or_else(|_| format!("{sample_path}.cfg.jsonl"));

    let cases: Vec<String> = fs::read_to_string(&sample_path)
        .unwrap_or_else(|_| panic!("failed to read sample list: {sample_path}"))
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.trim().to_owned())
        .collect();

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
/// logical_path is like "compiler/tests/cases/compiler/foo.ts" or
/// "conformance/tests/cases/conformance/types/any/foo.ts"
fn authority_case_path(logical: &str) -> PathBuf {
    let stripped = logical
        .strip_prefix("compiler/tests/cases/")
        .or_else(|| logical.strip_prefix("conformance/tests/cases/"))
        .unwrap_or(logical);
    authority_root().join("tests/cases").join(stripped)
}

/// Baseline resolution delegates to the shared area-aware implementation
/// in check_cells so all facet samplers select the same file.
fn resolve_baseline_fs(
    stem: &str,
    area: &str,
    pragmas: &CasePragmas,
    extension: &str,
) -> Option<PathBuf> {
    resolve_baseline_file(&baseline_dir(), stem, area, extension, pragmas)
}

/// Extract compile option pairs from pragmas (mirrors private harness helper).
fn compile_option_pairs(pragmas: &CasePragmas) -> Vec<(String, String)> {
    pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|value| (name.clone(), value.clone())))
        .collect()
}

/// Whether the selected compile options ask for an inline source map.
fn is_inline_source_map(compile_options: &[(String, String)]) -> bool {
    compile_options
        .iter()
        .any(|(name, value)| name == "inlinesourcemap" && value.eq_ignore_ascii_case("true"))
}

/// Find the first differing line pair. Skips empty lines.
fn first_diff(expected: &str, actual: &str) -> Option<(usize, String, usize, String)> {
    let exp_lines: Vec<&str> = expected.lines().collect();
    let act_lines: Vec<&str> = actual.lines().collect();
    let max = exp_lines.len().max(act_lines.len());
    for i in 0..max {
        let exp = exp_lines.get(i).copied().unwrap_or("<MISSING>");
        let act = act_lines.get(i).copied().unwrap_or("<MISSING>");
        let exp_norm = exp.trim_end();
        let act_norm = act.trim_end();
        if exp_norm != act_norm {
            return Some((i + 1, exp_norm.to_owned(), i + 1, act_norm.to_owned()));
        }
    }
    None
}

/// Extract the section name from a `//// [name]` header line.
fn section_of(line: &str) -> String {
    let trimmed = line.trim();
    if trimmed.starts_with("//// [")
        && let Some(end) = trimmed.find(']')
    {
        return trimmed[6..end].to_owned();
    }
    String::new()
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

/// Classify a diff into a family pattern.
fn classify_diff(
    facet: &str,
    _expected: &str,
    actual: &str,
    exp_line: &str,
    act_line: &str,
    _section: &str,
) -> String {
    let exp_is_header = exp_line.starts_with("//// [");
    let act_is_header = act_line.starts_with("//// [");

    let base = if act_line == "<MISSING>" {
        if exp_is_header {
            "missing-section".to_owned()
        } else {
            "missing-content-line".to_owned()
        }
    } else if exp_line == "<MISSING>" {
        if act_is_header {
            "extra-section".to_owned()
        } else {
            "extra-content-line".to_owned()
        }
    } else if exp_is_header && act_is_header {
        "section-header-diff".to_owned()
    } else if exp_is_header != act_is_header {
        "section-boundary-shift".to_owned()
    } else if facet == "declaration" {
        classify_declaration_diff(exp_line, act_line)
    } else if facet == "javascript" {
        classify_javascript_diff(exp_line, act_line)
    } else {
        classify_source_map_diff(exp_line, act_line)
    };

    // Check if actual is entirely empty (total mismatch)
    let act_nonempty = actual.lines().any(|l| !l.trim().is_empty());
    if !act_nonempty && !base.starts_with("total") {
        format!("total:{base}")
    } else {
        base
    }
}

fn classify_declaration_diff(exp_line: &str, act_line: &str) -> String {
    let exp_has_declare = exp_line.contains("declare ");
    let act_has_declare = act_line.contains("declare ");
    if exp_has_declare && !act_has_declare {
        return "missing-declare-keyword".to_owned();
    }
    if !exp_has_declare && act_has_declare {
        return "extra-declare-keyword".to_owned();
    }
    let exp_has_export = exp_line.contains("export ");
    let act_has_export = act_line.contains("export ");
    if exp_has_export && !act_has_export {
        return "missing-export-modifier".to_owned();
    }
    if !exp_has_export && act_has_export {
        return "extra-export-modifier".to_owned();
    }
    let exp_has_readonly = exp_line.contains("readonly ");
    let act_has_readonly = act_line.contains("readonly ");
    if exp_has_readonly && !act_has_readonly {
        return "missing-readonly".to_owned();
    }
    if !exp_has_readonly && act_has_readonly {
        return "extra-readonly".to_owned();
    }
    if exp_line.contains("?:") && !act_line.contains("?:") {
        return "optional-property-diff".to_owned();
    }
    if !exp_line.contains("?:") && act_line.contains("?:") {
        return "extra-optional-property".to_owned();
    }
    // Check for type annotation differences
    let exp_colon = exp_line.rfind(": ");
    let act_colon = act_line.rfind(": ");
    if let (Some(ei), Some(ai)) = (exp_colon, act_colon) {
        let exp_type = &exp_line[ei..];
        let act_type = &act_line[ai..];
        if exp_type != act_type {
            return "type-annotation-diff".to_owned();
        }
    }
    "declaration-content-diff".to_owned()
}

fn classify_source_map_diff(exp_line: &str, act_line: &str) -> String {
    // JSON field-level classification
    for field in [
        "version",
        "file",
        "sourceRoot",
        "sources",
        "sourcesContent",
        "names",
        "mappings",
    ] {
        let pat = format!("\"{field}\"");
        if exp_line.contains(&pat) || act_line.contains(&pat) {
            let exp_has = exp_line.contains(&pat);
            let act_has = act_line.contains(&pat);
            if exp_has && !act_has {
                return format!("missing-{field}-field");
            }
            if !exp_has && act_has {
                return format!("extra-{field}-field");
            }
            return format!("{field}-value-diff");
        }
    }
    "sourcemap-content-diff".to_owned()
}

/// Extract only the `.js` sections from a baseline by name (never by position).
/// A baseline `.js` file may contain `//// [name.js]`, `//// [name.d.ts]`,
/// and echo sections; we keep only the `.js` output sections and the document
/// header, dropping `.d.ts`, echoes, and everything else.
fn extract_js_sections(baseline: &str) -> String {
    let mut out = String::new();
    let mut in_js_section = false;
    for line in baseline.lines() {
        if line.starts_with("//// [")
            && let Some(end) = line.find(']')
        {
            let name = &line[6..end];
            in_js_section = name.ends_with(".js");
        }
        if in_js_section {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

/// Classify a javascript facet first-delta into a family pattern.
///
/// Families:
/// - `helper-missing:<name>` — a tslib helper call that the baseline has but
///   our emit does not (or vice-versa).  Checked by scanning for known helper
///   identifiers in the expected/actual lines.
/// - `downlevel-missing:<feature>` — the baseline lowers a feature (class
///   fields, optional chaining, nullish coalescing, async, for-of,
///   destructuring, template, exponent) but our emit keeps native syntax, or
///   the baseline keeps native syntax but our emit lowers it.
/// - `formatting:<shape>` — blank lines, indentation, parens, trailing comma,
///   semicolons, prologue, module-wrapper, or other printer-level differences.
fn classify_javascript_diff(exp_line: &str, act_line: &str) -> String {
    // Helper-missing: one side has a tslib helper call the other lacks.
    const HELPERS: &[&str] = &[
        "__awaiter",
        "__generator",
        "__extends",
        "__assign",
        "__rest",
        "__spreadArray",
        "__values",
        "__read",
        "__decorate",
        "__classPrivateFieldGet",
        "__classPrivateFieldSet",
        "__classPrivateFieldIn",
        "__metadata",
        "__param",
        "__exportStar",
        "__createBinding",
        "__importDefault",
        "__importStar",
    ];
    for helper in HELPERS {
        let exp_has = exp_line.contains(helper);
        let act_has = act_line.contains(helper);
        if exp_has && !act_has {
            return format!("helper-missing:{helper}");
        }
        if !exp_has && act_has {
            return format!("helper-extra:{helper}");
        }
    }

    // Downlevel-missing: the baseline lowered a feature but we kept native
    // syntax, or vice-versa.  We detect by looking for native syntax on one
    // side and lowered syntax on the other.

    // Optional chaining: `?.` native vs lowered `&&` / ternary
    if exp_line.contains("?.") && !act_line.contains("?.") {
        return "downlevel-missing:optional-chaining".to_owned();
    }
    if !exp_line.contains("?.") && act_line.contains("?.") {
        return "downlevel-extra:optional-chaining".to_owned();
    }

    // Nullish coalescing: `??` native vs lowered `||` / ternary
    if exp_line.contains("??") && !act_line.contains("??") {
        return "downlevel-missing:nullish-coalescing".to_owned();
    }
    if !exp_line.contains("??") && act_line.contains("??") {
        return "downlevel-extra:nullish-coalescing".to_owned();
    }

    // Logical assignment: `||=`, `&&=`, `??=`
    for op in ["||=", "&&=", "??="] {
        if exp_line.contains(op) && !act_line.contains(op) {
            return "downlevel-missing:logical-assignment".to_owned();
        }
        if !exp_line.contains(op) && act_line.contains(op) {
            return "downlevel-extra:logical-assignment".to_owned();
        }
    }

    // Exponentiation: `**` native vs `Math.pow` lowered
    if exp_line.contains("**") && !act_line.contains("**") {
        return "downlevel-missing:exponentiation".to_owned();
    }
    if !exp_line.contains("**") && act_line.contains("**") {
        return "downlevel-extra:exponentiation".to_owned();
    }
    if exp_line.contains("Math.pow") && !act_line.contains("Math.pow") {
        return "downlevel-missing:exponentiation".to_owned();
    }

    // Async functions: `async` keyword
    if exp_line.contains("async ") && !act_line.contains("async ") {
        return "downlevel-missing:async".to_owned();
    }
    if !exp_line.contains("async ") && act_line.contains("async ") {
        return "downlevel-extra:async".to_owned();
    }

    // For-of: `for...of` native vs lowered loop
    if exp_line.contains("for (") && exp_line.contains(" of ") && !act_line.contains(" of ") {
        return "downlevel-missing:for-of".to_owned();
    }

    // Destructuring: `{ a, b } =` or `[a, b] =` native vs lowered
    if (exp_line.contains("{ ") || exp_line.contains("["))
        && exp_line.contains(" = ")
        && !act_line.contains("{ ")
        && !act_line.contains("[")
    {
        return "downlevel-missing:destructuring".to_owned();
    }

    // Template literals: backtick strings
    if exp_line.contains('`') && !act_line.contains('`') {
        return "downlevel-missing:template".to_owned();
    }
    if !exp_line.contains('`') && act_line.contains('`') {
        return "downlevel-extra:template".to_owned();
    }

    // Class fields: `x = 1` inside class body vs `this.x = 1` in constructor
    if exp_line.contains("this.") && !act_line.contains("this.") {
        return "downlevel-missing:class-fields".to_owned();
    }
    if !exp_line.contains("this.") && act_line.contains("this.") {
        return "downlevel-extra:class-fields".to_owned();
    }

    // Formatting families
    if exp_line.trim().is_empty() && !act_line.trim().is_empty() {
        return "formatting:blank-line".to_owned();
    }
    if !exp_line.trim().is_empty() && act_line.trim().is_empty() {
        return "formatting:blank-line".to_owned();
    }
    // Indentation difference (same content, different leading whitespace)
    let exp_trimmed = exp_line.trim_start();
    let act_trimmed = act_line.trim_start();
    if exp_trimmed == act_trimmed && exp_line != act_line {
        return "formatting:indentation".to_owned();
    }
    // Trailing comma
    if exp_line.ends_with(',') && !act_line.ends_with(',') {
        return "formatting:trailing-comma".to_owned();
    }
    if !exp_line.ends_with(',') && act_line.ends_with(',') {
        return "formatting:trailing-comma".to_owned();
    }
    // Semicolon difference
    if exp_line.ends_with(';') && !act_line.ends_with(';') {
        return "formatting:semicolon".to_owned();
    }
    if !exp_line.ends_with(';') && act_line.ends_with(';') {
        return "formatting:semicolon".to_owned();
    }
    // Parenthesization difference
    if exp_trimmed == act_trimmed {
        return "formatting:parens".to_owned();
    }
    // Prologue: "use strict" presence/absence
    if exp_line.contains("\"use strict\"") || act_line.contains("\"use strict\"") {
        return "formatting:prologue".to_owned();
    }
    // Module wrapper: require/exports/Object.defineProperty
    if exp_line.contains("Object.defineProperty(exports")
        || act_line.contains("Object.defineProperty(exports")
    {
        return "formatting:module-wrapper".to_owned();
    }
    if exp_line.contains("require(") || act_line.contains("require(") {
        return "formatting:module-wrapper".to_owned();
    }
    if exp_line.contains("exports.") || act_line.contains("exports.") {
        return "formatting:module-wrapper".to_owned();
    }

    "formatting:other".to_owned()
}

/// Total applicable population for extrapolation, per facet.
fn extrapolation_denominator(facet: &str) -> f64 {
    match facet {
        "declaration" => 2215.0,
        "source-map" => 237.0,
        "javascript" => 14060.0,
        _ => 1000.0,
    }
}

#[test]
#[ignore]
fn declaration_facet_sample() {
    let facet = env::var("BAMTS_FACET").unwrap_or_else(|_| "declaration".to_owned());
    assert!(
        facet == "declaration" || facet == "source-map" || facet == "javascript",
        "BAMTS_FACET must be 'declaration', 'source-map', or 'javascript', got: {facet}"
    );

    let sample = load_sample();
    let mut results: Vec<AnalysisResult> = Vec::new();

    for case in &sample {
        let case_path = authority_case_path(&case.logical_path);
        let source_text = match fs::read_to_string(&case_path) {
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

        let pragmas = parse_case_pragmas(&source_text);
        let units = split_case_units(&harness_logical, &source_text);
        let entry = entry_virtual_path(&harness_logical, &units);
        let compile_options = compile_option_pairs(&pragmas);

        // Source-map: skip inline source maps (known producer gap)
        if facet == "source-map" && is_inline_source_map(&compile_options) {
            results.push(AnalysisResult {
                case: case.logical_path.clone(),
                cfg: case.cfg.clone(),
                outcome: Outcome::InlineSourceMapGap,
            });
            continue;
        }

        let mode = match facet.as_str() {
            "declaration" => FrontendMode::Declaration,
            _ => FrontendMode::JavaScript,
        };

        let compiled = match compile_case_frontend(&units, &entry, &pragmas, mode) {
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

        // Emit
        let emitted = if facet == "declaration" {
            match emit_declaration_baseline(&compiled) {
                Ok(text) => text,
                Err(detail) => {
                    results.push(AnalysisResult {
                        case: case.logical_path.clone(),
                        cfg: case.cfg.clone(),
                        outcome: Outcome::EmitError(detail),
                    });
                    continue;
                }
            }
        } else if facet == "javascript" {
            match emit_javascript_baseline(&compiled, &harness_logical) {
                Ok(text) => text,
                Err(detail) => {
                    results.push(AnalysisResult {
                        case: case.logical_path.clone(),
                        cfg: case.cfg.clone(),
                        outcome: Outcome::EmitError(detail),
                    });
                    continue;
                }
            }
        } else {
            let inline_sources = compile_options
                .iter()
                .any(|(name, value)| name == "inlinesources" && value.eq_ignore_ascii_case("true"));
            match emit_source_map_baseline(&compiled, inline_sources) {
                Ok(text) => text,
                Err(detail) => {
                    results.push(AnalysisResult {
                        case: case.logical_path.clone(),
                        cfg: case.cfg.clone(),
                        outcome: Outcome::EmitError(detail),
                    });
                    continue;
                }
            }
        };

        // Resolve baseline
        let (extension, comparator) = match facet.as_str() {
            "declaration" | "javascript" => {
                ("js", compare_js_emit as fn(&str, &str) -> FacetVerdict)
            }
            _ => (
                "js.map",
                compare_source_map as fn(&str, &str) -> FacetVerdict,
            ),
        };

        let stem = case_stem(&harness_logical);
        let baseline_path =
            match resolve_baseline_fs(stem, baseline_area(&harness_logical), &pragmas, extension) {
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

        let raw_baseline = match fs::read_to_string(&baseline_path) {
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

        // For declaration, extract only the .d.ts sections from the .js
        // baseline.  For javascript, extract only the `.js` sections by name
        // from BOTH the baseline and the emitted document (never by position
        // — the last section is often `.d.ts`), so the first diff lands
        // inside a `.js` section rather than at an echo header.
        let expected = if facet == "declaration" {
            extract_dts_sections(&raw_baseline, units.len())
        } else if facet == "javascript" {
            extract_js_sections(&raw_baseline)
        } else {
            raw_baseline
        };
        let emitted = if facet == "javascript" {
            extract_js_sections(&emitted)
        } else {
            emitted
        };

        let verdict = comparator(&expected, &emitted);
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
                    let family =
                        classify_diff(&facet, &expected, &emitted, &exp_line, &act_line, &section);
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
                        &facet,
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
    let mut emit_error = 0usize;
    let mut unproven = 0usize;
    let mut mismatch_count = 0usize;
    let mut inline_gap = 0usize;
    let mut families: BTreeMap<String, Vec<AnalysisResult>> = BTreeMap::new();

    for result in &results {
        match &result.outcome {
            Outcome::Pass => pass_count += 1,
            Outcome::NoBaseline => no_baseline += 1,
            Outcome::CompileError(e) => {
                compile_error += 1;
                eprintln!("COMPILE_ERROR: {} | {}", result.case, e);
            }
            Outcome::EmitError(e) => {
                emit_error += 1;
                eprintln!("EMIT_ERROR: {} | {}", result.case, e);
            }
            Outcome::BaselineUnproven => unproven += 1,
            Outcome::InlineSourceMapGap => inline_gap += 1,
            Outcome::Mismatch { .. } => mismatch_count += 1,
        }
    }

    for result in &results {
        if let Outcome::Mismatch { family, .. } = &result.outcome {
            families
                .entry(family.clone())
                .or_default()
                .push(result.clone());
        }
    }

    let total = results.len();
    let denom = extrapolation_denominator(&facet);

    // Build the report text
    let sample_path = env::var("BAMTS_FACET_SAMPLE").unwrap_or_default();
    let auth_root = authority_root();
    let mut report = String::new();

    let facet_upper = facet.to_uppercase();
    report.push_str(&format!("=== {facet_upper} FACET SAMPLE ANALYSIS ===\n"));
    report.push_str(&format!("Facet: {facet}\n"));
    report.push_str(&format!("Sample file: {sample_path}\n"));
    report.push_str(&format!("Authority root: {}\n", auth_root.display()));
    report.push_str(&format!("Total sampled: {total}\n"));
    report.push_str(&format!("Pass: {pass_count}\n"));
    report.push_str(&format!("Mismatch: {mismatch_count}\n"));
    report.push_str(&format!("Compile error: {compile_error}\n"));
    report.push_str(&format!("Emit error: {emit_error}\n"));
    report.push_str(&format!("No baseline: {no_baseline}\n"));
    report.push_str(&format!("Unproven: {unproven}\n"));
    report.push_str(&format!("Inline source map gap: {inline_gap}\n\n"));

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
        let extrapolated = (count as f64 / total as f64 * denom).round() as usize;
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
        let extrapolated = (cases.len() as f64 / total as f64 * denom).round() as usize;
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
    let report_dir = repo_root().join(format!("target/tmp/{facet}-facet-sampler"));
    fs::create_dir_all(&report_dir).ok();
    let report_path = report_dir.join("report.txt");
    fs::write(&report_path, &report).ok();

    // Print summary to stderr (for --nocapture)
    eprintln!("\n=== {facet_upper} FACET SAMPLE ANALYSIS ===");
    eprintln!("Total sampled: {total}");
    eprintln!("Pass: {pass_count}");
    eprintln!("Mismatch: {mismatch_count}");
    eprintln!("Compile error: {compile_error}");
    eprintln!("Emit error: {emit_error}");
    eprintln!("No baseline: {no_baseline}");
    eprintln!("Unproven: {unproven}");
    eprintln!("Inline source map gap: {inline_gap}");

    eprintln!("\n=== FAMILY TABLE (sorted by count) ===");
    for (family, cases) in &sorted_families {
        let count = cases.len();
        let pct = if mismatch_count > 0 {
            count as f64 / mismatch_count as f64 * 100.0
        } else {
            0.0
        };
        let extrapolated = (count as f64 / total as f64 * denom).round() as usize;
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
        let extrapolated = (cases.len() as f64 / total as f64 * denom).round() as usize;
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
