use super::*;

/// A [`ResolutionHost`] backed by the real filesystem, confined to a project
/// root. Used by the trace comparator to re-resolve import specifiers with
/// `resolve_module_name_with_trace` against the same files the loader saw.
struct FilesystemResolutionHost;

impl ResolutionHost for FilesystemResolutionHost {
    fn file_exists(&self, path: &Path) -> bool {
        path.is_file()
    }

    fn directory_exists(&self, path: &Path) -> bool {
        path.is_dir()
    }

    fn read_file(&self, path: &Path) -> Option<Arc<str>> {
        fs::read_to_string(path).ok().map(Arc::from)
    }
}

/// Determine the `ModuleResolutionKind` from compiler options. Upstream test
/// cases default to `bundler` when `moduleResolution` is not set; `node16` and
/// `nodenext` are parsed when present.
fn resolution_kind(options: &CompilerOptions) -> ModuleResolutionKind {
    match options.module_resolution() {
        Some(value) => ModuleResolutionKind::parse(value).unwrap_or(ModuleResolutionKind::Bundler),
        None => ModuleResolutionKind::Bundler,
    }
}
pub(crate) fn collect_resolution_trace(
    program: &ResolvedProgram,
    options: &CompilerOptions,
) -> ResolutionTraceLog {
    collect_trace_with_skip(program, options, None)
}

pub(crate) fn collect_case_resolution_trace(case: &CheckedCase) -> ResolutionTraceLog {
    let program = case.program();
    collect_trace_with_skip(program, case.options(), Some(program.entrypoint_id()))
}

fn collect_trace_with_skip(
    program: &ResolvedProgram,
    options: &CompilerOptions,
    skip: Option<SourceId>,
) -> ResolutionTraceLog {
    let root = program.root();
    let kind = resolution_kind(options);
    let host = FilesystemResolutionHost;
    let mut cache = ResolutionCache::new();
    let mut log = ResolutionTraceLog::default();
    for module in program.modules() {
        if Some(module.source_id()) == skip {
            continue;
        }
        let importer = module.path();
        for edge in module.dependencies() {
            if edge.kind() == ModuleEdgeKind::DynamicRuntime {
                continue;
            }
            let _ = resolve_module_name_with_trace(
                root,
                options,
                importer,
                edge.specifier(),
                (kind, edge.mode(), edge.flavor()),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            );
        }
    }
    log
}

/// Record the `trace` observable: compile the case, re-resolve each import
/// specifier through `resolve_module_name_with_trace` to produce upstream
/// `traceResolution` log lines, and compare the collected lines against the
/// `<stem>.trace.json` baseline. Resolution kinds the tracer does not cover
/// (`DirectoryPackage`, `PackageImport`, `PackageName`, `PathsMapping`) are
/// reported honestly as producer-missing detail rather than fabricated.
pub(crate) fn observe_trace(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    let baseline_path = match resolve_stem_baseline(
        groups,
        &index_entry.logical_path,
        "trace.json",
        &compile_options,
    ) {
        Ok(path) => path,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: error.to_string(),
                artifact: None,
            };
        }
    };
    let case = match compile_case_with_pragmas(&units, &entry, pragmas) {
        Err(error) => return compile_failure_observation(error),
        Ok(case) => case,
    };
    let Some(baseline_path) = baseline_path else {
        return CompilerCheckObservation {
            class: FailureClass::Inapplicable,
            detail: "trace observable inapplicable: no owned `.trace.json` baseline for this case/configuration".to_owned(),
            artifact: None,
        };
    };
    let log = collect_case_resolution_trace(&case);
    let unsupported: Vec<&str> = log
        .unsupported()
        .iter()
        .map(|kind| match kind {
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::DirectoryPackage => {
                "DirectoryPackage"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PackageImport => {
                "PackageImport"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PackageName => {
                "PackageName"
            }
            bamts_compiler::project::resolution_trace::UnsupportedTraceKind::PathsMapping => {
                "PathsMapping"
            }
        })
        .collect();
    let produced_lines = log.lines();
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
    let expected_text = String::from_utf8_lossy(&bytes).into_owned();
    let expected_lines: Vec<String> = match serde_json::from_str::<Vec<String>>(&expected_text) {
        Ok(lines) => lines,
        Err(error) => {
            return CompilerCheckObservation {
                class: FailureClass::HarnessError,
                detail: format!(
                    "trace baseline `{baseline_path}` is not a JSON string array: {error}"
                ),
                artifact: None,
            };
        }
    };
    let produced_json = serde_json::to_string_pretty(produced_lines)
        .unwrap_or_default()
        .into_bytes();
    if produced_lines == expected_lines.as_slice() {
        CompilerCheckObservation {
            class: FailureClass::Pass,
            detail: String::new(),
            artifact: Some(produced_json),
        }
    } else if !unsupported.is_empty() {
        CompilerCheckObservation {
            class: FailureClass::HarnessError,
            detail: format!(
                "producer missing: resolution tracer does not cover {{{}}}; produced {} of {} expected trace lines",
                unsupported.join(", "),
                produced_lines.len(),
                expected_lines.len()
            ),
            artifact: Some(produced_json),
        }
    } else {
        CompilerCheckObservation {
            class: FailureClass::FailBehavior,
            detail: format!(
                "trace mismatch: produced {} lines, expected {} lines",
                produced_lines.len(),
                expected_lines.len()
            ),
            artifact: Some(produced_json),
        }
    }
}
