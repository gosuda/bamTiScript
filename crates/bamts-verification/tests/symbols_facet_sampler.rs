//! Symbols-facet sampler: compile stratified sample cases, emit `.symbols`,
//! compare against authority baselines, classify first-delta families, and
//! write a structured report to `target/tmp/`.
//!
//! The sample list is read from the file path in `BAMTS_SYMBOLS_SAMPLE`
//! (one logical path per line). An optional cfg mapping can be provided
//! via `BAMTS_SYMBOLS_CFG` (JSONL with `{"case":"...","cfg":"..."}` rows);
//! if unset, `{sample_path}.cfg.jsonl` is tried.
//!
//! The authority root is read from `BAMTS_AUTHORITY_ROOT` (default:
//! `/home/alpha/compiler/bamTiScript/target/authority/typescript-7.0.2-tests`).
//!
//! Run with:
//!   BAMTS_SYMBOLS_SAMPLE=path/to/sample.txt \
//!   cargo test -p bamts-verification --test symbols_facet_sampler -- --ignored --nocapture

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

use bamts_verification::check_cells::{
    CasePragmas, baseline_area, case_stem, compile_case_with_pragmas, emit_symbols_baseline,
    entry_virtual_path, parse_case_pragmas, resolve_baseline_file, split_case_units,
};
use bamts_verification::facets::{FacetVerdict, compare_symbols};

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
    NoBaseline,
    BaselineUnproven,
}

/// Parse the sample file list and optional cfg mapping.
fn load_sample() -> Vec<SampleCase> {
    let sample_path = env::var("BAMTS_SYMBOLS_SAMPLE").expect(
        "BAMTS_SYMBOLS_SAMPLE must point to a sample list file (one logical path per line)",
    );
    let cfg_path =
        env::var("BAMTS_SYMBOLS_CFG").unwrap_or_else(|_| format!("{sample_path}.cfg.jsonl"));

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
fn resolve_baseline_fs(stem: &str, area: &str, pragmas: &CasePragmas) -> Option<PathBuf> {
    resolve_baseline_file(&baseline_dir(), stem, area, "symbols", pragmas)
}

/// Find the first differing line pair, prioritizing symbol lines (`>`).
/// Skips the `//// [path] ////` marker line (line 1) and empty lines.
/// For section header mismatches, reports them as source-line diffs.
/// For symbol lines, finds the first `>` line that differs in content.
fn first_diff(expected: &str, actual: &str) -> Option<(usize, String, usize, String)> {
    let exp_lines: Vec<&str> = expected.lines().collect();
    let act_lines: Vec<&str> = actual.lines().collect();

    // Strategy: find the first symbol line (starting with '>') in expected
    // that either doesn't appear in actual at all, or differs from the
    // corresponding actual symbol line. This bypasses section naming and
    // source echo differences to find the real semantic mismatch.

    // Collect all symbol lines from both sides
    let exp_symbols: Vec<(usize, &str)> = exp_lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with('>'))
        .map(|(i, l)| (i, *l))
        .collect();
    let act_symbols: Vec<(usize, &str)> = act_lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.starts_with('>'))
        .map(|(i, l)| (i, *l))
        .collect();
    // If actual has no symbol lines but expected does, report first expected
    if act_symbols.is_empty() && !exp_symbols.is_empty() {
        let (ln, line) = exp_symbols[0];
        return Some((
            ln + 1,
            line.trim_end().to_owned(),
            0,
            "<MISSING>".to_owned(),
        ));
    }

    // Compare symbol lines pairwise
    let max = exp_symbols.len().max(act_symbols.len());
    for i in 0..max {
        let (exp_ln, exp_line) = exp_symbols.get(i).copied().unwrap_or((0, "<MISSING>"));
        let (act_ln, act_line) = act_symbols.get(i).copied().unwrap_or((0, "<MISSING>"));
        let exp_norm = exp_line.trim_end();
        let act_norm = act_line.trim_end();
        if exp_norm != act_norm {
            return Some((
                exp_ln + 1,
                exp_norm.to_owned(),
                act_ln + 1,
                act_norm.to_owned(),
            ));
        }
    }

    // If all symbol lines match, fall back to first non-symbol, non-marker diff
    let max = exp_lines.len().max(act_lines.len());
    for i in 1..max {
        // Skip line 0 (marker), section headers, and empty lines
        let exp = exp_lines.get(i).copied().unwrap_or("<MISSING>");
        let act = act_lines.get(i).copied().unwrap_or("<MISSING>");
        if exp.trim().is_empty() && act.trim().is_empty() {
            continue;
        }
        if exp.trim_start().starts_with("===") && act.trim_start().starts_with("===") {
            continue;
        }
        let exp_norm = exp.trim_end();
        let act_norm = act.trim_end();
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

/// Classify a diff into a family pattern.
///
/// `expected` and `actual` are the full baseline texts; `exp_line` and
/// `act_line` are the first differing lines. `section` is the section
/// header context around the diff.
fn classify_diff(
    expected: &str,
    actual: &str,
    exp_line: &str,
    act_line: &str,
    section: &str,
) -> String {
    // Use section to distinguish library vs case-file mismatches
    let in_lib = section.contains("lib.");

    // Use full texts to distinguish total vs partial symbol mismatches
    let exp_sym_count = expected.lines().filter(|l| l.starts_with('>')).count();
    let act_sym_count = actual.lines().filter(|l| l.starts_with('>')).count();
    let total_mismatch = exp_sym_count > 0 && act_sym_count == 0;

    // Check if expected has a symbol line that actual is missing
    let exp_is_symbol = exp_line.starts_with('>');
    let act_is_symbol = act_line.starts_with('>');

    let base = if exp_is_symbol && act_line == "<MISSING>" {
        // Missing symbol line in actual
        if exp_line.contains("Decl(lib.") {
            "missing-lib-symbol-ref".to_owned()
        } else if exp_line.contains("Symbol(") && exp_line.contains(".isSunk") {
            "missing-class-member-ref".to_owned()
        } else if exp_line.contains("Symbol(") {
            if exp_line.contains('.') && !exp_line.contains("Decl(lib") {
                "missing-qualified-member-symbol".to_owned()
            } else {
                "missing-declaration-symbol".to_owned()
            }
        } else {
            "missing-symbol-line".to_owned()
        }
    } else if act_is_symbol && exp_line == "<MISSING>" {
        "extra-symbol-line-in-actual".to_owned()
    } else if exp_is_symbol && act_is_symbol {
        // Both are symbol lines but differ
        let exp_decl = extract_decl(exp_line);
        let act_decl = extract_decl(act_line);
        let exp_name = extract_symbol_name(exp_line);
        let act_name = extract_symbol_name(act_line);
        if exp_name == act_name {
            // Same name, different Decl — coordinate issue
            if exp_decl.contains("lib.") && !act_decl.contains("lib.") {
                "lib-decl-coords-missing".to_owned()
            } else if exp_decl.contains("--, --") {
                "lib-decl-placeholder-coords".to_owned()
            } else {
                // Check if actual has extra Decl entries (duplicate declarations)
                let exp_decl_count = exp_decl.matches("Decl(").count();
                let act_decl_count = act_decl.matches("Decl(").count();
                if exp_decl_count != act_decl_count {
                    "wrong-decl-count".to_owned()
                } else {
                    // Check if it's just ordering of Decl entries.
                    // Use extract_decl_coords to compare actual coordinate
                    // strings, not literal "Decl(" substrings (which are
                    // always identical and make the sort+compare trivially
                    // equal, misclassifying coordinate errors as order diffs).
                    let exp_coords = extract_decl_coords(exp_line);
                    let act_coords = extract_decl_coords(act_line);
                    if exp_coords.len() == act_coords.len() {
                        let mut exp_sorted = exp_coords.clone();
                        let mut act_sorted = act_coords.clone();
                        exp_sorted.sort();
                        act_sorted.sort();
                        if exp_sorted == act_sorted {
                            "decl-order-diff".to_owned()
                        } else {
                            "wrong-decl-coordinates".to_owned()
                        }
                    } else {
                        "wrong-decl-coordinates".to_owned()
                    }
                }
            }
        } else if exp_name.contains('.') || act_name.contains('.') {
            // Different names at the same symbol-line index — qualification difference
            "wrong-symbol-qualification".to_owned()
        } else {
            // Check if the Decl coordinates are the same (same position, wrong name)
            let exp_coords = extract_decl_coords(exp_line);
            let act_coords = extract_decl_coords(act_line);
            if exp_coords == act_coords && !exp_coords.is_empty() {
                "wrong-symbol-name-same-pos".to_owned()
            } else {
                // Completely different symbols — binder tracks different declarations
                "wrong-symbol-entirely".to_owned()
            }
        }
    } else if exp_line == "<MISSING>" {
        "extra-source-line-in-actual".to_owned()
    } else if act_line == "<MISSING>" {
        "missing-source-line-in-actual".to_owned()
    } else {
        // Source line content differs
        "source-line-content-diff".to_owned()
    };

    // Incorporate section and totality context into the family name
    if in_lib && !base.starts_with("lib") {
        format!("lib:{base}")
    } else if total_mismatch && !base.starts_with("total") {
        format!("total:{base}")
    } else {
        base
    }
}

fn extract_decl(line: &str) -> String {
    // Extract everything inside Symbol(...)
    if let Some(start) = line.find("Symbol(")
        && let Some(end) = line.rfind(')')
    {
        return line[start..=end].to_owned();
    }
    String::new()
}

fn extract_symbol_name(line: &str) -> String {
    // Extract the name before the first comma inside Symbol(...)
    if let Some(start) = line.find("Symbol(") {
        let rest = &line[start + 7..];
        if let Some(comma) = rest.find(',') {
            return rest[..comma].trim().to_owned();
        }
    }
    String::new()
}

/// Extract just the Decl coordinates (unit, line, col) from a symbol line,
/// ignoring the symbol name. Returns "unit,line,col" for each Decl.
fn extract_decl_coords(line: &str) -> Vec<String> {
    let mut coords = Vec::new();
    let decl = extract_decl(line);
    // Find all Decl(...) entries
    let mut rest = decl.as_str();
    while let Some(start) = rest.find("Decl(") {
        rest = &rest[start + 5..];
        if let Some(end) = rest.find(')') {
            coords.push(rest[..end].to_owned());
            rest = &rest[end + 1..];
        } else {
            break;
        }
    }
    coords
}

#[test]
#[ignore]
fn symbols_facet_sample() {
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
        // The harness uses logical paths without the catalog prefix
        // (e.g. "tests/cases/compiler/foo.ts", not "compiler/tests/cases/compiler/foo.ts")
        let harness_logical = case
            .logical_path
            .strip_prefix("compiler/")
            .or_else(|| case.logical_path.strip_prefix("conformance/"))
            .unwrap_or(&case.logical_path)
            .to_owned();

        let pragmas = parse_case_pragmas(&source_text);
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

        let emitted = emit_symbols_baseline(&compiled, &harness_logical);
        let stem = case_stem(&harness_logical);
        let baseline_path =
            match resolve_baseline_fs(stem, baseline_area(&harness_logical), &pragmas) {
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

        let verdict = compare_symbols(&expected, &emitted);
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
                    // Structural mismatch but no simple line diff found
                    // (e.g., order normalization issue)
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
    let sample_path = env::var("BAMTS_SYMBOLS_SAMPLE").unwrap_or_default();
    let auth_root = authority_root();
    let mut report = String::new();

    report.push_str("=== SYMBOLS FACET SAMPLE ANALYSIS ===\n");
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
        let extrapolated = (count as f64 / total as f64 * 12105.0).round() as usize;
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
        let extrapolated = (cases.len() as f64 / total as f64 * 12105.0).round() as usize;
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
    let report_dir = repo_root().join("target/tmp/symbols-facet-sampler");
    fs::create_dir_all(&report_dir).ok();
    let report_path = report_dir.join("report.txt");
    fs::write(&report_path, &report).ok();

    // Print summary to stderr (for --nocapture)
    eprintln!("\n=== SYMBOLS FACET SAMPLE ANALYSIS ===");
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
        let extrapolated = (count as f64 / total as f64 * 12105.0).round() as usize;
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
        let extrapolated = (cases.len() as f64 / total as f64 * 12105.0).round() as usize;
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
