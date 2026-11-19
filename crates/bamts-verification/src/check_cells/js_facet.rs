use super::*;

/// Run the javascript emit comparator against the selected pragma variation.
pub(crate) fn observe_javascript(
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
                return match emit_javascript_baseline(&case, &index_entry.logical_path) {
                    Err(detail) if detail == NO_JAVASCRIPT_OUTPUT => CompilerCheckObservation {
                        class: FailureClass::Pass,
                        detail: "no javascript output and no javascript baseline".to_owned(),
                        artifact: Some(Vec::new()),
                    },
                    _ => CompilerCheckObservation {
                        class: FailureClass::HarnessError,
                        detail: "classification/execution drift: no owned `.js` baseline"
                            .to_owned(),
                        artifact: None,
                    },
                };
            };
            let emitted = match emit_javascript_baseline(&case, &index_entry.logical_path) {
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
            match compare_js_emit(&expected, &emitted) {
                FacetVerdict::Pass => CompilerCheckObservation {
                    class: FailureClass::Pass,
                    detail: "javascript parity".to_owned(),
                    artifact: Some(emitted.into_bytes()),
                },
                FacetVerdict::Fail { reason } => CompilerCheckObservation {
                    class: FailureClass::FailBehavior,
                    detail: reason,
                    artifact: None,
                },
                FacetVerdict::Unproven { reason } => CompilerCheckObservation {
                    class: FailureClass::HarnessError,
                    detail: format!("javascript oracle could not prove parity: {reason}"),
                    artifact: None,
                },
            }
        }
    }
}

/// What `emit_javascript_baseline` reports when the case emits no section: upstream
/// then writes no `.js` baseline at all.
const NO_JAVASCRIPT_OUTPUT: &str = "javascript emit reached no case units";

/// The directory components every emitting unit shares, which tsc drops from
/// the paths under `outDir`.
pub(crate) fn common_directory<'a>(paths: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut common: Option<Vec<&str>> = None;
    for path in paths {
        let mut parts: Vec<&str> = path.split('/').filter(|part| !part.is_empty()).collect();
        parts.pop();
        common = Some(match common {
            None => parts,
            Some(previous) => previous
                .into_iter()
                .zip(parts)
                .take_while(|(left, right)| left == right)
                .map(|(left, _)| left)
                .collect(),
        });
    }
    common.unwrap_or_default()
}

/// The output path `fullEmitPaths` prints: `outDir`, the unit's directories
/// below the common source directory, then the section name.
pub(crate) fn emitted_path(
    directory: &str,
    common: &[&str],
    unit_path: &str,
    section: &str,
) -> String {
    let parts: Vec<&str> = unit_path
        .split('/')
        .filter(|part| !part.is_empty())
        .collect();
    let below = parts
        .get(common.len()..parts.len().saturating_sub(1))
        .unwrap_or_default();
    let mut path = String::from(directory);
    for part in below {
        path.push('/');
        path.push_str(part);
    }
    path.push('/');
    path.push_str(section);
    path
}

/// Whether the program compiles JavaScript inputs: `allowJs`, `checkJs` (which
/// implies it), or a tsconfig unit that sets `allowJs` itself.
fn compiles_scripts(case: &CheckedCase) -> bool {
    let options = case.options();
    options.allow_js()
        || options.check_js()
        || case.units.iter().any(|(unit, _)| {
            is_config_unit_name(&unit_basename(&unit.virtual_path))
                && unit
                    .text
                    .to_ascii_lowercase()
                    .replace(char::is_whitespace, "")
                    .contains("\"allowjs\":true")
        })
}

/// The `outDir` that `fullEmitPaths` prints in front of every section name.
pub(super) fn full_emit_directory(pragmas: &CasePragmas) -> Option<String> {
    let value = |name: &str| {
        pragmas
            .options
            .iter()
            .find(|(key, _)| key == name)
            .and_then(|(_, values)| values.first())
    };
    value("fullemitpaths").filter(|flag| flag.eq_ignore_ascii_case("true"))?;
    let directory = value("outdir")?.trim_end_matches('/');
    Some(directory.strip_prefix("./").unwrap_or(directory).to_owned())
}

pub fn emit_javascript_baseline(
    case: &CheckedCase,
    logical_path: &str,
) -> std::result::Result<String, String> {
    // Upstream `doJsEmitBaseline` framing: a `//// [<case>] ////` document
    // header, one `//// [<basename>]` echo per compiled unit, a blank-line
    // block separator, then the `//// [<output>.js]` sections, then — when the
    // compile declares — a `\n\n` separator and the `//// [<output>.d.ts]`
    // sections. Comparing the whole document keeps the echo honest alongside
    // the emit.
    //
    // Every echo is the unit's bytes verbatim: the separator belongs to the
    // block, not to any unit, so it is appended once after the last one. A
    // unit that ends with a newline keeps it, which is what puts the extra
    // blank line before the emit sections in upstream's documents.
    let options = case.options();
    let jsx_preserve = options.jsx() == Some(JsxEmit::Preserve);
    let bundle = bundle_output_name(options)?;
    let mut out = format!("//// [{logical_path}] ////\n\n");
    let units: Vec<_> = case.reached_units().collect();
    for (unit, _) in &units {
        let name = unit_basename(&unit.virtual_path);
        if name.eq_ignore_ascii_case("tsconfig.json") {
            continue;
        }
        out.push_str(&format!("//// [{name}]\n"));
        out.push_str(&unit.text);
    }
    out.push_str("\n\n");
    // Upstream's `result.JS` is empty for an `emitDeclarationOnly` compile, so
    // the document carries no `.js` sections at all; its `result.DTS` is empty
    // unless declaration emit is on. The section set follows those two maps.
    let mut outputs = 0usize;
    let imported = runtime_imported_source_ids(case);
    let emitted = if case.no_resolve() {
        case.reached_units().collect()
    } else {
        case.reached_units_in_module_order()
    };
    let emit_directory = case.emit_directory();
    let common = common_directory(
        emitted
            .iter()
            .filter(|(unit, _)| !is_declaration_input_name(&unit_basename(&unit.virtual_path)))
            .map(|(unit, _)| unit.virtual_path.as_str()),
    );
    let placed = |section: &str, unit: &CaseUnit| match emit_directory {
        Some(directory) => emitted_path(directory, &common, &unit.virtual_path, section),
        None => section.to_owned(),
    };
    if !options.emit_declaration_only() {
        for (unit, output) in &emitted {
            let name = unit_basename(&unit.virtual_path);
            if is_declaration_input_name(&name)
                || (is_script_input_name(&name) && !compiles_scripts(case))
            {
                continue;
            }
            if is_json_input_name(&name) {
                if bundle.is_some() {
                    continue;
                }
                if options.out_dir().is_none() {
                    continue;
                }
                if is_config_unit_name(&name) || name.eq_ignore_ascii_case("package.json") {
                    continue;
                }
                if unit
                    .virtual_path
                    .split('/')
                    .any(|part| part == "node_modules")
                {
                    continue;
                }
                if !imported.contains(&output.source_file().source_id()) {
                    continue;
                }
                let body = output
                    .emit()
                    .and_then(|emit| emit.javascript.as_ref())
                    .map(|javascript| javascript.code.as_str())
                    .unwrap_or("");
                push_output_section(&mut out, &placed(&name, unit), body);
                outputs += 1;
                continue;
            }
            let Some(emit) = output.emit() else {
                return Err(format!(
                    "unit `{}` produced no javascript emit",
                    unit.virtual_path
                ));
            };
            let Some(javascript) = emit.javascript.as_ref() else {
                return Err(format!(
                    "unit `{}` produced no javascript slot",
                    unit.virtual_path
                ));
            };
            let js_name = output_section_name(&name, bundle.as_deref(), |name| {
                output_extension(name, jsx_preserve).to_owned()
            });
            push_output_section(&mut out, &placed(&js_name, unit), &javascript.code);
            outputs += 1;
        }
    }
    if options.declaration() || options.emit_declaration_only() {
        let mut declarations = Vec::new();
        for (unit, output) in &emitted {
            let name = unit_basename(&unit.virtual_path);
            if is_declaration_input_name(&name)
                || is_json_input_name(&name)
                || (is_script_input_name(&name) && !compiles_scripts(case))
            {
                continue;
            }
            let section = output_section_name(&name, bundle.as_deref(), declaration_extension);
            let Some(declaration) = declaration_code(output)
                .map(str::to_owned)
                .or_else(|| declaration_text_for(output, &section, &name))
            else {
                continue;
            };
            declarations.push((placed(&section, unit), declaration));
        }
        if !declarations.is_empty() {
            // Upstream writes the `\r\n\r\n` block separator and then the
            // declaration sections back to back, with no per-file separator.
            out.push_str("\n\n");
            for (section, code) in declarations {
                out.push_str(&format!("//// [{section}]\n{code}"));
                outputs += 1;
            }
        }
    }
    if outputs == 0 {
        return Err(NO_JAVASCRIPT_OUTPUT.to_owned());
    }
    Ok(out)
}

/// The bundle output name (`outFile`) upstream gives every unit's JavaScript
/// output, as a basename. Upstream's per-unit output path is the `outFile`
/// path itself, and the baseline prints only its basename.
pub(super) fn bundle_output_name(options: &CompilerOptions) -> std::result::Result<Option<String>, String> {
    let Some(path) = options.out_file() else {
        return Ok(None);
    };
    let Some(name) = path.file_name() else {
        return Ok(None);
    };
    let Some(basename) = name.to_str() else {
        return Err("outFile path is not valid UTF-8".to_owned());
    };
    Ok(Some(basename.to_owned()))
}
fn runtime_imported_source_ids(case: &CheckedCase) -> HashSet<SourceId> {
    let program = case.program();
    let entry = program.entrypoint_id();
    let mut imported = HashSet::new();
    for module in program.modules() {
        if module.source_id() == entry {
            continue;
        }
        for edge in module.dependencies() {
            if edge.is_unresolved() {
                continue;
            }
            if edge.kind() == ModuleEdgeKind::TypeOnly {
                continue;
            }
            if let Some(target) = edge.target().local_source_id() {
                imported.insert(target);
            }
        }
    }
    imported
}

/// The `//// [<name>]` section header for one unit's output of a given kind.
/// A per-file compile names the section after the unit basename; an `outFile`
/// compile names every output after the bundle. Either way the name is that
/// file's basename with `extension` swapped in, and a name already carrying
/// the extension is returned untouched so a `.d.ts` bundle stays `.d.ts`
/// rather than becoming `.d.d.ts`.
pub(super) fn output_section_name(
    unit_name: &str,
    bundle: Option<&str>,
    extension: impl Fn(&str) -> String,
) -> String {
    let name = match bundle {
        Some(bundle) => bundle,
        None => unit_name,
    };
    let extension = extension(name);
    if name.to_ascii_lowercase().ends_with(&extension) {
        return name.to_owned();
    }
    replace_extension(name, &extension)
}

/// The declaration text one unit's frontend output carries, when it carries
/// one.
pub(super) fn declaration_code(output: &FrontendOutput) -> Option<&str> {
    output
        .emit()
        .and_then(|emit| emit.declaration.as_ref())
        .map(|declaration| declaration.code.as_str())
}

/// The declaration text for one unit whose frontend output carries only
/// JavaScript.
///
/// The `javascript` lane runs the transform surface, whose `EmitOutput` has no
/// declaration slot, while upstream's `doJsEmitBaseline` documents the
/// declaration sections of the same compile. Re-emitting the unit through the
/// public emitter with declaration emit on produces exactly the text the
/// `declaration` lane documents: the declaration view of `EmitOptions` carries
/// only newline, indent, `isolatedDeclarations`, `stripPrivate`, and
/// `declarationMap`, none of which the lane routing changes.
/// `emit_declaration_only` keeps the call from re-emitting the JavaScript.
pub(super) fn declaration_text_for(
    output: &FrontendOutput,
    dts_name: &str,
    source_name: &str,
) -> Option<String> {
    let names = EmitFileNames {
        source_name: Arc::from(source_name),
        declaration_file_name: Some(Arc::from(dts_name)),
        ..EmitFileNames::default()
    };
    let options = EmitOptions {
        declaration: true,
        emit_declaration_only: true,
        ..EmitOptions::default()
    };
    let emitted = emit_checked(
        output.source_file(),
        output.semantic_model(),
        &options,
        &names,
    );
    emitted.declaration.map(|declaration| declaration.code)
}

/// Append one `//// [<section>]` output section whose body is newline-terminated.
pub(super) fn push_output_section(out: &mut String, section: &str, code: &str) {
    out.push_str(&format!("//// [{section}]\n{code}"));
    if !code.ends_with('\n') {
        out.push('\n');
    }
}

/// Append one `//// [<section>]` source-map section carrying map JSON.
pub(super) fn push_map_section(out: &mut String, section: &str, json: &str) {
    out.push_str(&format!("//// [{section}]\n{json}"));
    if !out.ends_with('\n') {
        out.push('\n');
    }
}

/// The JavaScript output extension upstream derives for one input name
/// (`outputpaths.GetOutputExtension`): `.json` stays `.json`; `.tsx`/`.jsx`
/// become `.jsx` only under `jsx: preserve`; `.mts`/`.mjs` become `.mjs`;
/// `.cts`/`.cjs` become `.cjs`; everything else becomes `.js`.
#[must_use]
pub fn output_extension(file_name: &str, jsx_preserve: bool) -> &'static str {
    let lower = file_name.to_lowercase();
    if lower.ends_with(".json") {
        ".json"
    } else if jsx_preserve && (lower.ends_with(".tsx") || lower.ends_with(".jsx")) {
        ".jsx"
    } else if lower.ends_with(".mts") || lower.ends_with(".mjs") {
        ".mjs"
    } else if lower.ends_with(".cts") || lower.ends_with(".cjs") {
        ".cjs"
    } else {
        ".js"
    }
}

/// The `//// [<name>]` section header for one unit's JavaScript output. The
/// baseline prints the output path's basename, so only the extension changes
/// from the unit name (`a.ts` ⇒ `a.js`, `file.tsx` ⇒ `file.jsx` under
/// `jsx: preserve`, `m.cts` ⇒ `m.cjs`).
#[must_use]
pub fn javascript_section_name(unit_name: &str, jsx_preserve: bool) -> String {
    replace_extension(unit_name, output_extension(unit_name, jsx_preserve))
}

/// The declaration-output extension upstream derives for one input name
/// (`tspath.GetDeclarationEmitExtensionForPath`).
#[must_use]
pub fn declaration_extension(file_name: &str) -> String {
    let lower = file_name.to_lowercase();
    if lower.ends_with(".mjs") || lower.ends_with(".mts") {
        ".d.mts".to_owned()
    } else if lower.ends_with(".cjs") || lower.ends_with(".cts") {
        ".d.cts".to_owned()
    } else if lower.ends_with(".ts")
        || lower.ends_with(".tsx")
        || lower.ends_with(".js")
        || lower.ends_with(".jsx")
    {
        ".d.ts".to_owned()
    } else if let Some((_, extension)) = lower.rsplit_once('.') {
        format!(".d.{extension}.ts")
    } else {
        ".d.ts".to_owned()
    }
}

/// Swap a unit basename to its declaration-output name (`a.ts` ⇒ `a.d.ts`,
/// `.mjs`/`.mts` ⇒ `.d.mts`, `.cjs`/`.cts` ⇒ `.d.cts`), matching upstream's
/// declaration emit extension rule for per-file output naming.
#[must_use]
pub fn declaration_section_name(unit_name: &str) -> String {
    replace_extension(unit_name, &declaration_extension(unit_name))
}

/// Replaces `file_name`'s extension with `extension`, appending it when the
/// name has none.
pub(super) fn replace_extension(file_name: &str, extension: &str) -> String {
    match file_name.rsplit_once('.') {
        Some((stem, _)) => format!("{stem}{extension}"),
        None => format!("{file_name}{extension}"),
    }
}
