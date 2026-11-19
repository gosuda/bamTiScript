use super::*;
/// Extract the `.tsbuildinfo` body content from an upstream `.js` baseline
/// document. Returns just the body lines (without the `//// [name]` header)
/// so the comparator can compare against the raw emitted content.
pub fn extract_tsbuildinfo_sections(baseline: &str) -> String {
    let mut out = String::new();
    let mut in_section = false;
    for line in baseline.lines() {
        match section_header_name(line) {
            Some(name) => {
                in_section = is_tsbuildinfo_section_name(name);
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

/// Whether the case's resolved options turn on build-info emission, mirroring
/// the catalog's `ObservableKind::BuildInfo` source predicate: `incremental`
/// or `composite` must be true (a bare `tsBuildInfoFile` does not emit —
/// optionsTsBuildInfoFileWithoutIncrementalAndComposite writes no artifact).
pub(super) fn build_info_implied(pragmas: &CasePragmas) -> bool {
    let config_source = build_tsconfig(pragmas);
    let Ok(value) = bamts_compiler::project::parse_jsonc(&config_source) else {
        return false;
    };
    let bamts_compiler::project::JsonValue::Object(obj) = &value else {
        return false;
    };
    let Some(compiler) = obj
        .get("compilerOptions")
        .and_then(|value| value.as_object())
    else {
        return false;
    };
    ["incremental", "composite"].iter().any(|key| {
        matches!(
            compiler.get(key),
            Some(bamts_compiler::project::JsonValue::Bool(true))
        )
    })
}

/// Produce the BAMTS `.tsbuildinfo` content for a compiled case.
///
/// Constructs a [`BuildInfo`] from the program's source modules and the
/// canonical compiler-options signature, then encodes it in the on-disk JSON
/// format. The output is deterministic for the same inputs. Returns empty
/// when the config implies no build-info emission (`incremental` or
/// `composite` unset).
#[must_use]
pub fn emit_build_info_baseline(case: &CheckedCase, pragmas: &CasePragmas) -> String {
    if !build_info_implied(pragmas) {
        return String::new();
    }
    let config_source = build_tsconfig(pragmas);
    let option_signature = match bamts_compiler::project::parse_jsonc(&config_source) {
        Ok(value) => match &value {
            bamts_compiler::project::JsonValue::Object(obj) => match obj.get("compilerOptions") {
                Some(compiler) => canonical_json(compiler),
                None => "null".to_owned(),
            },
            _ => "null".to_owned(),
        },
        Err(_) => "null".to_owned(),
    };
    let sources: BTreeMap<std::path::PathBuf, Arc<str>> = case
        .program()
        .modules()
        .iter()
        .map(|module| {
            (
                module.path().to_path_buf(),
                source_signature(module.source().as_str()),
            )
        })
        .collect();
    let info = BuildInfo {
        version: Arc::from(BUILD_INFO_SCHEMA),
        options: Arc::from(option_signature),
        sources,
        outputs: std::collections::BTreeSet::new(),
        signature: Arc::from("0000000000000000"),
    };
    match info.encode() {
        Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
        Err(error) => format!("build-info encode error: {error}"),
    }
}

/// Run the build-info comparator against the selected pragma variation.
///
/// The upstream `.js` baseline document may embed `.tsbuildinfo` output as
/// `//// [name.tsbuildinfo]` sections; the comparator compares only those
/// sections with the javascript facet's line-wise normalization. Compile
/// failures are `FAIL_BEHAVIOR`/`CRASH`; a missing owned `.js` baseline is a
/// classification/execution drift `HARNESS_ERROR`. No baseline in the entire
/// 7.0.2 reference tree carries a `.tsbuildinfo` section (the harness drops
/// the artifact as environment dependent), so the no-section path is the
/// live one: it demands emission exactly when the config implies it
/// (`incremental` or `composite`) and no artifact otherwise.
pub(crate) fn observe_build_info(
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
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::JavaScript) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.js` baseline".to_owned(),
                    artifact: None,
                };
            };
            let emitted = emit_build_info_baseline(&case, pragmas);
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
            let expected = String::from_utf8_lossy(&bytes).into_owned();
            let expected_sections = extract_tsbuildinfo_sections(&expected);
            if expected_sections.is_empty() {
                // Upstream never baselines `.tsbuildinfo` content: zero
                // sections exist across the entire 7.0.2 reference tree.
                // With no expected bytes the contract is emission-shape:
                // produce an artifact exactly when the config implies one
                // (`incremental`/`composite`), none otherwise.
                let implied = build_info_implied(pragmas);
                let produced =
                    !emitted.is_empty() && !emitted.starts_with("build-info encode error:");
                return match (implied, produced) {
                    (true, true) => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "build-info produced; content not baselined upstream".to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                    (true, false) => CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail: "config implies a .tsbuildinfo artifact but the \
                            producer emitted none"
                            .to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                    (false, false) => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "config implies no .tsbuildinfo artifact; none emitted".to_owned(),
                        artifact: Some(
                            "config implies no .tsbuildinfo artifact; none emitted\n"
                                .as_bytes()
                                .to_vec(),
                        ),
                    },
                    (false, true) => CompilerCheckObservation {
                        class: FailureClass::FailBehavior,
                        detail: "producer emitted a .tsbuildinfo artifact the config \
                            does not imply"
                            .to_owned(),
                        artifact: Some(emitted.into_bytes()),
                    },
                };
            }
            match compare_js_emit(&expected_sections, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "build-info parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("build-info oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}
