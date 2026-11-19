use super::*;

/// Emit the declaration slice of an upstream `.js` baseline document: one
/// `//// [<output>.d.ts]` section per reached unit that declares, framed
/// exactly like upstream's `doJsEmitBaseline` `fileOutput` sections (header
/// without trailing slashes, newline-terminated code, no separator between
/// declaration sections).
pub fn emit_declaration_baseline(case: &CheckedCase) -> std::result::Result<String, String> {
    let options = case.options();
    let bundle = bundle_output_name(options)?;
    let mut out = String::new();
    for (unit, output) in case.reached_units_in_module_order() {
        let name = unit_basename(&unit.virtual_path);
        // Declaration inputs and JSON inputs produce no declaration output;
        // upstream's output mapping skips them entirely.
        if is_declaration_input_name(&name) || is_json_input_name(&name) {
            continue;
        }
        let section = output_section_name(&name, bundle.as_deref(), declaration_extension);
        // The declaration lane's frontend output already carries the
        // declaration; the fallback covers a caller that hands this function a
        // JavaScript-lane case.
        let Some(declaration) = declaration_code(output)
            .map(str::to_owned)
            .or_else(|| declaration_text_for(output, &section, &name))
        else {
            continue;
        };
        push_output_section(&mut out, &section, &declaration);
    }
    if out.is_empty() {
        return Err("declaration emit reached no case units".to_owned());
    }
    Ok(out)
}

/// Extract the declaration output sections (header + body) of an upstream
/// `.js` baseline document. The `declaration` observable speaks only about
/// this slice; input echoes, `.js` outputs, and `[DtsFileErrors]` markers stay
/// out of the comparison.
///
/// `echo_count` is the number of input-file echo sections at the top of the
/// document (one per `// @filename:` unit). Upstream's `doJsEmitBaseline`
/// writes all input echoes first, then generated outputs; a `.d.ts`-named
/// section in the echo zone is an input echo, not a generated declaration.
/// Skipping `echo_count` sections before extracting prevents echo
/// contamination when a case has `.d.ts` inputs alongside generated
/// declarations of the same basename.
#[must_use]
pub fn extract_dts_sections(baseline: &str, echo_count: usize) -> String {
    let mut out = String::new();
    let mut in_section = false;
    let mut sections_seen = 0usize;
    for line in baseline.lines() {
        match section_header_name(line) {
            Some(name) => {
                sections_seen += 1;
                in_section = sections_seen > echo_count && is_declaration_section_name(name);
                if in_section {
                    out.push_str(line.trim_end());
                    out.push('\n');
                }
            }
            None if in_section => {
                out.push_str(line.trim_end());
                out.push('\n');
            }
            None => {}
        }
    }
    out
}

/// Run the declaration emit comparator against the selected pragma variation.
///
/// The upstream `.js` baseline document embeds declaration output as
/// `//// [<stem>.d.ts]` sections (harness `doJsEmitBaseline`); the comparator
/// compares only those sections with the javascript facet's line-wise
/// normalization. Compile failures are `FAIL_BEHAVIOR`/`CRASH`; a missing
/// owned `.js` baseline is a classification/execution drift `HARNESS_ERROR`.
pub(crate) fn observe_declaration(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baseline_path =
        match resolve_stem_baseline(groups, &index_entry.logical_path, "js", &compile_options) {
            Ok(path) => path,
            Err(error) => {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: error.to_string(),
                    artifact: None,
                };
            }
        };
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::Declaration) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail:
                        "classification/execution drift: no owned `.js` baseline document for the declaration facet"
                            .to_owned(),
                    artifact: None,
                };
            };
            let emitted = match emit_declaration_baseline(&case) {
                Ok(emitted) => emitted,
                Err(detail) => {
                    return CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail,
                        artifact: None,
                    };
                }
            };
            let bytes = match read_verified_snapshot_asset(snapshot, &baseline_path) {
                Ok(bytes) => bytes,
                Err(error) => {
                    return CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: error.to_string(),
                        artifact: None,
                    };
                }
            };
            let expected = extract_dts_sections(&String::from_utf8_lossy(&bytes), units.len());
            match compare_declaration_emit(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "declaration parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("declaration oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}
