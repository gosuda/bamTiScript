use super::*;

/// Whether the selected compile options ask for an inline source map, which
/// upstream baselines only through the `.sourcemap.txt` record.
pub(super) fn is_inline_source_map(compile_options: &[(String, String)]) -> bool {
    compile_options
        .iter()
        .any(|(name, value)| name == "inlinesourcemap" && value.eq_ignore_ascii_case("true"))
}

/// The precise gap an inline-source-map `source-map` obligation records: the
/// `.js.map` JSON facet does not exist for inline maps, and the comparable
/// artifact — the `.sourcemap.txt` sourcemap record — has no producer yet.
pub(super) fn inline_source_map_producer_gap() -> String {
    "producer missing: `.sourcemap.txt` sourcemap-record producer (inline source maps are never baselined as `.js.map` upstream)".to_owned()
}

/// Emit the source-map slice of an upstream `.js.map` baseline document: the
/// `//// [<output>.js.map]` sections (when `sourceMap` is on) followed by the
/// `//// [<output>.d.ts.map]` sections (when `declarationMap` is on), each
/// carrying the real printer map as Source Map v3 JSON. Upstream's
/// `DoSourcemapBaseline` writes exactly `result.Maps`, whose order is the
/// program's source order per surface, so JavaScript maps precede declaration
/// maps. Maps are produced through the public emitter surface with external-map
/// naming (`file`, `sources`, and the `sourceMappingURL` mirror upstream's
/// per-file baseline shape).
pub fn emit_source_map_baseline(
    case: &CheckedCase,
    inline_sources: bool,
) -> std::result::Result<String, String> {
    let program_options = case.options();
    let mut out = String::new();
    let jsx_preserve = program_options.jsx() == Some(JsxEmit::Preserve);
    let bundle = bundle_output_name(program_options)?;
    let source_map = program_options.source_map();
    let declaration_map = program_options.declaration_map();
    // An `emitDeclarationOnly` compile produces no JavaScript at all, so its
    // `.js.map` baseline carries only declaration maps.
    let want_js_map = source_map && !program_options.emit_declaration_only();
    let want_dts_map = declaration_map;
    let mut js_maps: Vec<(String, String)> = Vec::new();
    let mut dts_maps: Vec<(String, String)> = Vec::new();
    for (unit, output) in case.reached_units_in_module_order() {
        let source_name = unit_basename(&unit.virtual_path);
        if is_declaration_input_name(&source_name) || is_json_input_name(&source_name) {
            continue;
        }
        let js_name = output_section_name(&source_name, bundle.as_deref(), |name| {
            output_extension(name, jsx_preserve).to_owned()
        });
        let dts_name = output_section_name(&source_name, bundle.as_deref(), declaration_extension);
        let names = EmitFileNames {
            source_name: Arc::from(source_name.as_str()),
            js_file_name: Some(Arc::from(js_name.as_str())),
            js_source_name: Some(Arc::from(source_name.as_str())),
            js_source_map_url: Some(Arc::from(format!("{js_name}.map").as_str())),
            declaration_file_name: Some(Arc::from(dts_name.as_str())),
            declaration_source_name: Some(Arc::from(source_name.as_str())),
            declaration_source_map_url: Some(Arc::from(format!("{dts_name}.map").as_str())),
            ..EmitFileNames::default()
        };
        let mut options = EmitOptions {
            source_map: want_js_map,
            declaration: want_dts_map || program_options.declaration(),
            emit_declaration_only: program_options.emit_declaration_only(),
            declaration_map: want_dts_map,
            inline_sources,
            ..EmitOptions::default()
        };
        // Forward the resolved program's emit fields (target, always_strict,
        // module, jsx) the same way pipeline.rs does, so the verification
        // lane and the CLI cannot diverge on downleveling, the strict-mode
        // prologue, or module-wrapper structure.
        let prog = case.program();
        let check = prog.check_options();
        options.apply_emit_fields(
            check.target(),
            check.always_strict(),
            prog.is_commonjs().then_some(ModuleKind::CommonJs),
            prog.use_define_for_class_fields(),
            prog.import_helpers(),
        );
        options.es_module_interop = prog.es_module_interop().unwrap_or(true);
        options.no_emit_helpers = check.no_emit_helpers();
        options.remove_comments = check.remove_comments();
        options.verbatim_module_syntax = prog.verbatim_module_syntax();
        match prog.jsx_routing_decision(ProgramOutputKind::JavaScript) {
            JsxRoutingDecision::Emit | JsxRoutingDecision::TransformAndEmit => {
                options.jsx = prog.jsx();
                options.jsx_factory = prog.jsx_factory().map(Arc::from);
                options.jsx_fragment_factory = prog.jsx_fragment_factory().map(Arc::from);
                options.jsx_import_source = prog.jsx_import_source().map(Arc::from);
            }
            JsxRoutingDecision::Lower | JsxRoutingDecision::RejectPreservedNative => {
                unreachable!("JavaScript output never selects a native JSX route");
            }
        }
        let emitted = emit_checked(
            output.source_file(),
            output.semantic_model(),
            &options,
            &names,
        );
        if want_js_map {
            let Some(map) = emitted
                .javascript
                .as_ref()
                .and_then(|file| file.source_map.as_ref())
            else {
                return Err(format!(
                    "unit `{}` produced no javascript source map",
                    unit.virtual_path
                ));
            };
            js_maps.push((format!("{js_name}.map"), map.to_json()));
        }
        if want_dts_map {
            let Some(map) = emitted
                .declaration
                .as_ref()
                .and_then(|file| file.source_map.as_ref())
            else {
                return Err(format!(
                    "unit `{}` produced no declaration source map",
                    unit.virtual_path
                ));
            };
            dts_maps.push((format!("{dts_name}.map"), map.to_json()));
        }
    }
    // Upstream's `result.Maps` consumes one `.js.map` per source file in
    // program order, then appends the unhandled declaration maps sorted by
    // unit name, so JavaScript maps always precede declaration maps.
    for (section, json) in js_maps {
        push_map_section(&mut out, &section, &json);
    }
    dts_maps.sort_by(|left, right| left.0.cmp(&right.0));
    for (section, json) in dts_maps {
        push_map_section(&mut out, &section, &json);
    }
    // `emitDeclarationOnly` without `declarationMap` requests no map at all;
    // only a case with no units is malformed.
    if out.is_empty() && case.units.is_empty() {
        return Err("source-map emit reached no case units".to_owned());
    }
    Ok(out)
}

/// Run the source-map comparator against the selected pragma variation.
///
/// External-map configurations (`sourcemap=true`) compare the emitted maps
/// against the owned `.js.map` baseline under JSON canonicalization. Inline
/// configurations have no `.js.map` baseline upstream and are recorded as the
/// precise producer gap instead. A non-inline configuration with no owned
/// `.js.map` baseline is a classification/execution drift `HARNESS_ERROR`.
pub(crate) fn observe_source_map(
    snapshot: &(impl SnapshotAssets + ?Sized),
    groups: &BaselineGroups,
    index_entry: &IndexEntry,
    text: &str,
    pragmas: &CasePragmas,
) -> CompilerCheckObservation {
    let units = split_case_units(&index_entry.logical_path, text);
    let entry = entry_virtual_path(&index_entry.logical_path, &units);
    let compile_options = compile_option_pairs(pragmas);
    if is_inline_source_map(&compile_options) {
        return CompilerCheckObservation {
            class: FailureClass::HarnessError,
            detail: inline_source_map_producer_gap(),
            artifact: None,
        };
    }
    let baseline_path = match resolve_stem_baseline(
        groups,
        &index_entry.logical_path,
        "js.map",
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
    match compile_case_frontend(&units, &entry, pragmas, FrontendMode::JavaScript) {
        Err(error) => compile_failure_observation(error),
        Ok(case) => {
            let Some(baseline_path) = baseline_path else {
                return CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: "classification/execution drift: no owned `.js.map` baseline"
                        .to_owned(),
                    artifact: None,
                };
            };
            let inline_sources = compile_options
                .iter()
                .any(|(name, value)| name == "inlinesources" && value.eq_ignore_ascii_case("true"));
            let emitted = match emit_source_map_baseline(&case, inline_sources) {
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
            let expected = String::from_utf8_lossy(&bytes).into_owned();
            match compare_source_map(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "source-map parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("source-map oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}
