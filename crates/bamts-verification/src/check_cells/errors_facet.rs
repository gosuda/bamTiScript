use super::*;
/// Resolve the `.errors.txt` baselines owned by one case, filtered to the
/// variant that matches the compile options actually used.
///
/// A baseline is owned when its first `//// [path] ////` marker names the
/// case's full logical path; a marker-less baseline is owned only when the
/// case is the stem's sole case input in the index. When variant baselines
/// exist (e.g. `(target=es5)`), only the variant matching the compile options
/// is selected; the plain baseline is used as a fallback when no variant matches.
pub fn resolve_errors_baselines(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    logical_path: &str,
    compile_options: &[(String, String)],
) -> Result<DiagnosticsBaselines> {
    let stem = case_stem(logical_path);
    let Some(candidates) = groups.get(&(stem.to_owned(), "errors.txt".to_owned())) else {
        return Ok(DiagnosticsBaselines::default());
    };
    let sole_input = case_inputs_with_stem(snapshot, stem) == [logical_path];
    let mut variants = Vec::new();
    let mut plain = Vec::new();
    let mut contents = BTreeMap::new();
    for (suffix, path) in candidates {
        let (owner, text) = baseline_owner(snapshot, path)?;
        contents.insert(path.clone(), text);
        let owned = match owner {
            Some(owner) => owner == logical_path,
            None => sole_input,
        };
        if !owned {
            continue;
        }
        if suffix.is_empty() {
            plain.push(path.clone());
        } else if suffix_matches_options(suffix, compile_options) {
            variants.push(path.clone());
        }
    }
    let mut owned = if !variants.is_empty() {
        variants
    } else {
        plain
    };
    owned.sort();
    owned.dedup();
    Ok(DiagnosticsBaselines { owned, contents })
}

/// Parse an `.errors.txt` baseline into file-anchored and global rows.
///
/// Strict row grammar: `^<file>(<l>,<c>): (error|warning) TS\d+: <msg>` and
/// `^(error|warning) TS\d+: <msg>` for file-less globals. `!!!` summaries,
/// `====` source dumps, caret lines, and blank separators are skipped.
pub fn parse_errors_baseline(text: &str) -> ErrorsBaseline {
    let mut baseline = ErrorsBaseline::default();
    for line in text.lines() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() || line.starts_with(' ') || line.starts_with('\t') {
            // Source dumps and caret lines are indented.
            continue;
        }
        if line.starts_with("!!!") || line.starts_with("====") {
            continue;
        }
        if let Some(diagnostic) = parse_file_row(line) {
            baseline.diagnostics.push(diagnostic);
        } else if let Some(global) = parse_global_row(line) {
            baseline.globals.push(global);
        }
    }
    baseline
}

/// Parse `file(l,c): (error|warning) TS\d+: message`.
fn parse_file_row(line: &str) -> Option<ErrorsDiagnostic> {
    let open = line.find('(')?;
    let (unit, rest) = line.split_at(open);
    let unit = unit.trim();
    if unit.is_empty() {
        return None;
    }
    let rest = rest.strip_prefix('(')?;
    let (position, rest) = rest.split_once("): ")?;
    let (line_no, character) = position.split_once(',')?;
    let line_no: u32 = line_no.trim().parse().ok()?;
    let character: u32 = character.trim().parse().ok()?;
    let (category, code, message) = parse_category_code(rest)?;
    Some(ErrorsDiagnostic {
        unit: unit.to_owned(),
        line: line_no,
        character: character.saturating_sub(1),
        category,
        code,
        message,
    })
}

/// Parse `(error|warning) TS\d+: message` (no file anchor).
fn parse_global_row(line: &str) -> Option<GlobalDiagnostic> {
    let (_, code, message) = parse_category_code(line)?;
    Some(GlobalDiagnostic { code, message })
}

/// Parse the shared `<category> TS<code>: <message>` tail.
fn parse_category_code(rest: &str) -> Option<(String, String, String)> {
    let (category, rest) = rest.split_once(' ')?;
    if !matches!(category, "error" | "warning") {
        return None;
    }
    let (code, message) = rest.split_once(": ")?;
    let digits = code.strip_prefix("TS")?;
    if digits.is_empty() || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    Some((category.to_owned(), code.to_owned(), message.to_owned()))
}

/// Flatten a checked case into the diagnostics comparator's actual side.
///
/// Positions are 1-based line / 0-based UTF-16 character over the unit text;
/// BAMTS codes carry their `BAMTS-*` spelling for the code map, category
/// follows `error` vs `warning`, and severity mirrors the compiler's
/// error/warning split. The unit basename is carried so a cross-unit position
/// collision cannot pass the check.
pub(crate) fn facet_position(source: &SourceText, position: Utf16Pos) -> Result<SourcePosition> {
    let (line, character) = source.line_column(position).map_err(|error| {
        VerificationError::new(
            ErrorCode::Schema,
            format!(
                "diagnostic offset {} lies outside its unit text: {error}",
                position.get(),
            ),
        )
    })?;
    let line = u32::try_from(line + 1).map_err(|error| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("diagnostic line does not fit u32: {error}"),
        )
    })?;
    let character = u32::try_from(character).map_err(|error| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("diagnostic character does not fit u32: {error}"),
        )
    })?;
    Ok(SourcePosition { line, character })
}

pub fn collect_facet_diagnostics(case: &CheckedCase) -> Result<Vec<FacetDiagnostic>> {
    let mut diagnostics = Vec::new();
    for (unit, output) in case.reached_units() {
        let unit_name = unit_basename(&unit.virtual_path);
        let source = SourceText::new(unit.text.clone())
            .unwrap_or_else(|_| panic!("unit text was bound-checked before compile"));
        for diagnostic in output.diagnostics() {
            let position = facet_position(&source, diagnostic.range().start())?;
            let severity = match diagnostic.severity() {
                DiagnosticSeverity::Error => FacetSeverity::Error,
                DiagnosticSeverity::Warning => FacetSeverity::Warning,
            };
            let category = match diagnostic.severity() {
                DiagnosticSeverity::Error => DiagnosticCategory::Error,
                DiagnosticSeverity::Warning => DiagnosticCategory::Warning,
            };
            diagnostics.push(FacetDiagnostic {
                unit: unit_name.clone(),
                position,
                category,
                severity,
                code: diagnostic.code().as_str().to_owned(),
            });
        }
    }
    Ok(diagnostics)
}

/// Union the owned `.errors.txt` baselines into the comparator's expected
/// side. File-less global rows stay out: the compiler has no global-diagnostic
/// observation yet (they name option-deprecation semantics owned by S7/S5).
/// The unit basename printed by the baseline is carried through so a
/// cross-unit position collision cannot pass the check.
pub fn expected_facet_diagnostics(
    baselines: &DiagnosticsBaselines,
) -> Result<Vec<FacetDiagnostic>> {
    let mut expected = Vec::new();
    for path in &baselines.owned {
        let Some(text) = baselines.contents.get(path) else {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("diagnostics baseline `{path}` was selected without retained bytes"),
            ));
        };
        let parsed = parse_errors_baseline(text);
        for row in parsed.diagnostics {
            let category = if row.category == "warning" {
                DiagnosticCategory::Warning
            } else {
                DiagnosticCategory::Error
            };
            let severity = if row.category == "warning" {
                FacetSeverity::Warning
            } else {
                FacetSeverity::Error
            };
            expected.push(FacetDiagnostic {
                unit: row.unit,
                position: SourcePosition {
                    line: row.line,
                    character: row.character,
                },
                category,
                severity,
                code: row.code,
            });
        }
    }
    Ok(expected)
}

/// Run the diagnostics comparison for one compiled case.
pub fn check_diagnostics(
    ctx: &CheckContext,
    case: &CheckedCase,
    baselines: &DiagnosticsBaselines,
) -> Result<DiagnosticsOutcome> {
    let mut actual = collect_facet_diagnostics(case)?;
    actual.retain(|diagnostic| !diagnostic.code.starts_with("BAMTS-W"));
    let expected = expected_facet_diagnostics(baselines)?;
    let verdict = compare_diagnostics(&expected, &actual, &ctx.code_map);
    Ok(DiagnosticsOutcome {
        actual,
        expected,
        verdict,
    })
}

/// Execute the S2 `diagnostics` observation for one planned cell.
///
/// Failure-class discipline mirrors `execute_parse_check`: compile failures
/// are `FAIL_BEHAVIOR` (loader/bound) or `CRASH` (panic); comparator `Fail`
/// is `FAIL_DIAGNOSTIC`; `Unproven` is an oracle-side `HARNESS_ERROR`; a pass
/// records the emitted/expected counts in the detail.
pub(crate) fn execute_diagnostics_check(
    ctx: &CheckContext,
    snapshot: &(impl SnapshotAssets + ?Sized),
    plan: &PlannedCell,
    index_entry: &IndexEntry,
) -> Result<CellResult> {
    let text = read_case_text(snapshot, index_entry)?;
    let pragmas = parse_case_pragmas(&text);
    Ok(cell_result(
        plan,
        observe_diagnostics(ctx, snapshot, index_entry, &text, &pragmas),
    ))
}

/// Run the diagnostics comparator against the selected pragma variation.
pub(crate) fn observe_diagnostics(
    ctx: &CheckContext,
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let mut units = split_case_units(&index_entry.logical_path, text);
    let support = match shared_lib_support_files(snapshot, &mut units) {
        Ok(support) => support,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baselines = match resolve_errors_baselines(
        snapshot,
        &ctx.baseline_groups,
        &index_entry.logical_path,
        &compile_options,
    ) {
        Ok(baselines) => baselines,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    match compile_case_with_support(&units, &entry, pragmas, &support) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let outcome = match check_diagnostics(ctx, &case, &baselines) {
                Ok(outcome) => outcome,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            match outcome.verdict {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: format!(
                        "diagnostic parity: {} expected, {} emitted",
                        outcome.expected.len(),
                        outcome.actual.len()
                    ),
                    artifact: serde_json::to_vec(&outcome.actual).ok(),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailDiagnostic,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("diagnostics oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}
