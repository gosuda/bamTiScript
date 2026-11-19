use super::*;

/// Compile one materialized case (all units) into its checked product.
///
/// Materializes the units under a fresh temp root, loads the entry unit
/// through [`ProgramLoader`], and runs [`compile_program_frontend`] in check
/// mode. All units are written even though the loader only reads the ones
/// reachable from the entry's module graph, so `.d.ts`/library-style units
/// Build a JSONC `tsconfig.json` source from a case's `@option` pragmas.
/// Upstream cases default to `strict: true` unless the case explicitly says
/// otherwise, so the harness supplies that default when no `@strict` directive
/// is present. Only the first value of each comma-split option is used.
pub(super) fn build_tsconfig(pragmas: &CasePragmas) -> String {
    let mut options: Vec<(String, String)> = Vec::new();
    for (name, values) in &pragmas.options {
        let Some(value) = values.first() else {
            continue;
        };
        let json = match name.as_str() {
            "strict"
            | "strictnullchecks"
            | "noimplicitany"
            | "allowjs"
            | "checkjs"
            | "resolvejsonmodule"
            | "noemit"
            | "noemithelpers"
            | "removecomments"
            | "declaration"
            | "alwaysstrict"
            | "exactoptionalpropertytypes"
            | "nouncheckedindexedaccess"
            | "strictpropertyinitialization"
            | "incremental"
            | "composite"
            | "emitdeclarationonly"
            | "sourcemap"
            | "declarationmap"
            | "usedefineforclassfields"
            | "importhelpers"
            | "experimentaldecorators"
            | "emitdecoratormetadata"
            | "esmoduleinterop" => value.eq_ignore_ascii_case("true").to_string(),
            "lib" => {
                let items: Vec<String> = values
                    .iter()
                    .flat_map(|v| v.split(','))
                    .map(|s| s.trim())
                    .filter(|s| !s.is_empty())
                    .map(|s| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
                    .collect();
                format!("[{}]", items.join(", "))
            }
            "typeroots" => {
                let items: Vec<String> = values
                    .iter()
                    .flat_map(|v| v.split(','))
                    .map(|s| s.trim())
                    .filter(|s| !s.is_empty())
                    .map(|s| s.strip_prefix('/').unwrap_or(s))
                    .map(|s| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")))
                    .collect();
                format!("[{}]", items.join(", "))
            }
            _ => format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\"")),
        };
        let key = match name.as_str() {
            "typeroots" => "typeRoots",
            "strictnullchecks" => "strictNullChecks",
            "noimplicitany" => "noImplicitAny",
            "allowjs" => "allowJs",
            "checkjs" => "checkJs",
            "resolvejsonmodule" => "resolveJsonModule",
            "moduleresolution" => "moduleResolution",
            "noemithelpers" => "noEmitHelpers",
            "removecomments" => "removeComments",
            "noemit" => "noEmit",
            "alwaysstrict" => "alwaysStrict",
            "usedefineforclassfields" => "useDefineForClassFields",
            "importhelpers" => "importHelpers",
            "esmoduleinterop" => "esModuleInterop",
            "experimentaldecorators" => "experimentalDecorators",
            "emitdecoratormetadata" => "emitDecoratorMetadata",
            "verbatimmodulesyntax" => "verbatimModuleSyntax",
            "exactoptionalpropertytypes" => "exactOptionalPropertyTypes",
            "nouncheckedindexedaccess" => "noUncheckedIndexedAccess",
            "strictpropertyinitialization" => "strictPropertyInitialization",
            "emitdeclarationonly" => "emitDeclarationOnly",
            "sourcemap" => "sourceMap",
            "declarationmap" => "declarationMap",
            "tsbuildinfofile" => "tsBuildInfoFile",
            "outfile" => "outFile",
            "outdir" => "outDir",
            "declarationdir" => "declarationDir",
            _ => name.as_str(),
        };
        options.push((key.to_owned(), json));
    }
    if !options.iter().any(|(name, _)| name == "strict") {
        options.push(("strict".to_owned(), "true".to_owned()));
    }
    // The authority harness pins `alwaysStrict` on rather than deriving it from
    // `strict`, which is why 2456 baselines declaring `@strict: false` still
    // carry a `"use strict"` prologue. Leaving it unset lets the compiler fall
    // back to `strict` and drops the prologue on every one of them.
    if !options.iter().any(|(name, _)| name == "alwaysStrict") {
        options.push(("alwaysStrict".to_owned(), "true".to_owned()));
    }
    let compiler_options = options
        .iter()
        .map(|(name, value)| format!("\"{name}\": {value}"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = String::new();
    source.push('{');
    source.push_str("\"compilerOptions\": {");
    source.push_str(&compiler_options);
    source.push_str("}}");
    source
}

/// Harness virtual roots a case may reference: `/.lib/*` maps to the
/// authority `tests/lib` tree and `/.ts/*` maps to the pinned TypeScript
/// package output, mirroring tsc's own harness mounts. Only quoted
/// specifier prefixes count; anything containing `..` is ignored so a
/// reference can never escape its mount root.
pub(super) fn mount_specifiers_in(text: &str) -> Vec<String> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut searched = 0;
    while searched < text.len() {
        let rest = &text[searched..];
        let offset = rest
            .find("/.lib/")
            .into_iter()
            .chain(rest.find("/.ts/"))
            .min();
        let Some(offset) = offset else {
            break;
        };
        let start = searched + offset;
        searched = start + 1;
        if !matches!(
            bytes.get(start.saturating_sub(1)).copied(),
            Some(b'\'') | Some(b'"')
        ) {
            continue;
        }
        let quote = bytes[start - 1] as char;
        let after = &text[start + 1..];
        let Some(length) = after.find(quote) else {
            break;
        };
        let specifier = &text[start..start + 1 + length];
        if !specifier.contains("..") && !found.iter().any(|existing| existing == specifier) {
            found.push(specifier.to_owned());
        }
        searched = start + 1 + length + 1;
    }
    found
}

/// Locates the workspace checkout this crate was built from.
fn workspace_root() -> Option<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    root.is_dir().then_some(root)
}

/// Locates the pinned authority tree: an explicit `BAMTS_AUTHORITY_ROOT`
/// first, else the workspace checkout's `target/authority` copy, else the
/// in-repo `.references` testdata the authority copy is fetched from. The
/// last fallback keeps `cargo test` hermetic: a bare checkout has no
/// `target/authority` tree (it needs the network), yet the served `tests/lib`
/// files are identical in both places. Missing trees mean missing mounts,
/// and the case compiles exactly as before.
fn mount_authority_root() -> Option<PathBuf> {
    if let Ok(root) = std::env::var("BAMTS_AUTHORITY_ROOT") {
        let path = PathBuf::from(root);
        if path.is_dir() {
            return Some(path);
        }
    }
    if let Some(root) = workspace_root() {
        let candidate = root.join("target/authority/typescript-7.0.2-tests");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    reference_testdata_root()
}

/// The in-repo `.references` TypeScript testdata, found by walking up from
/// this crate so worktree checkouts resolve it too.
pub(super) fn reference_testdata_root() -> Option<PathBuf> {
    let mut directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let candidate = directory.join(".references/typescript/tsc/testdata");
        if candidate.join("tests/lib").is_dir() {
            return Some(candidate);
        }
        if !directory.pop() {
            return None;
        }
    }
}

/// Copies the harness mount files a case's units reference into the temp
/// root, preserving the virtual layout so the generated `paths` mapping
/// resolves them. `/.lib/*` comes from the authority `tests/lib` tree and
/// `/.ts/*` from the pinned TypeScript package output. Reports which
/// virtual roots were served; missing sources stay unmapped and the case
/// compiles exactly as before.
fn write_mount_files(root: &Path, units: &[CaseUnit]) -> Vec<&'static str> {
    let specifiers: Vec<String> = units
        .iter()
        .flat_map(|unit| mount_specifiers_in(&unit.text))
        .collect();
    if specifiers.is_empty() {
        return Vec::new();
    }
    let authority = mount_authority_root();
    let package = workspace_root().and_then(|root| {
        let candidate = root.join("node_modules/typescript/lib");
        candidate.is_dir().then_some(candidate)
    });
    let mut served = Vec::new();
    for specifier in &specifiers {
        let (prefix, source) = if let Some(rest) = specifier.strip_prefix("/.lib/") {
            (
                "/.lib/",
                authority
                    .as_ref()
                    .map(|root| root.join("tests/lib").join(rest)),
            )
        } else if let Some(rest) = specifier.strip_prefix("/.ts/") {
            ("/.ts/", package.as_ref().map(|root| root.join(rest)))
        } else {
            continue;
        };
        let Some(source) = source else {
            continue;
        };
        let Ok(bytes) = fs::read(&source) else {
            continue;
        };
        let target = root.join(&specifier[1..]);
        let Some(parent) = target.parent() else {
            continue;
        };
        if fs::create_dir_all(parent).is_err() || fs::write(&target, bytes).is_err() {
            continue;
        }
        if !served.contains(&prefix) {
            served.push(prefix);
        }
    }
    served
}

/// Returns a copy of `base` with `key` set to `value`, preserving the
/// position of an existing key and appending a new one. The shared
/// primitive for layering generated, in-case, and harness configuration
/// without ever dropping a mapping the case declares itself.
fn object_set(base: &JsonObject, key: &str, value: JsonValue) -> JsonObject {
    let mut entries = Vec::with_capacity(base.entries().len() + 1);
    let mut replaced = false;
    for (existing, current) in base.entries() {
        if existing.as_ref() == key {
            entries.push((Arc::clone(existing), value.clone()));
            replaced = true;
        } else {
            entries.push((Arc::clone(existing), current.clone()));
        }
    }
    if !replaced {
        entries.push((Arc::from(key), value));
    }
    JsonObject::from_entries(entries)
}

/// Merges harness mount `paths` mappings into a generated tsconfig
/// document. An existing `paths` entry keeps its own mapping, so a case
/// that maps its own specifiers never loses them to the mounts; mounts
/// only fill gaps. Anything unparseable passes through untouched.
pub(super) fn inject_mount_paths(config_source: String, served: &[&str]) -> String {
    if served.is_empty() {
        return config_source;
    }
    let Ok(JsonValue::Object(root)) = parse_jsonc(&config_source) else {
        return config_source;
    };
    let Some(compiler) = root.get("compilerOptions").and_then(JsonValue::as_object) else {
        return config_source;
    };
    let mut paths = match compiler.get("paths").and_then(JsonValue::as_object) {
        Some(existing) => JsonObject::from_entries(
            existing
                .entries()
                .iter()
                .map(|(key, value)| (Arc::clone(key), value.clone()))
                .collect(),
        ),
        None => JsonObject::from_entries(Vec::new()),
    };
    for prefix in served {
        let mut pattern = String::from(*prefix);
        pattern.push('*');
        if paths.get(&pattern).is_some() {
            continue;
        }
        let target = format!("./{stem}*", stem = &prefix[1..]);
        paths = object_set(
            &paths,
            &pattern,
            JsonValue::Array(Arc::from(vec![JsonValue::String(Arc::from(
                target.as_str(),
            ))])),
        );
    }
    let compiler = object_set(compiler, "paths", JsonValue::Object(paths));
    let root = object_set(&root, "compilerOptions", JsonValue::Object(compiler));
    canonical_json(&JsonValue::Object(root))
}
pub fn compile_case(
    units: &[CaseUnit],
    entry_name: &str,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_with_pragmas(units, entry_name, &CasePragmas::default())
}

pub fn compile_case_with_pragmas(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_with_support(units, entry_name, pragmas, &[])
}

pub fn compile_case_with_support(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    support: &[CaseUnit],
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_frontend_with_support(units, entry_name, pragmas, FrontendMode::Check, support)
}

pub fn compile_case_frontend(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    mode: FrontendMode,
) -> std::result::Result<CheckedCase, CaseCompileError> {
    compile_case_frontend_with_support(units, entry_name, pragmas, mode, &[])
}

pub fn compile_case_frontend_with_support(
    units: &[CaseUnit],
    entry_name: &str,
    pragmas: &CasePragmas,
    mode: FrontendMode,
    support: &[CaseUnit],
) -> std::result::Result<CheckedCase, CaseCompileError> {
    let temp = TempDir::new("bamts-check-cell")
        .map_err(|error| CaseCompileError::Load(format!("temp root: {error}")))?;
    for unit in units {
        if unit.text.len() > bamts_compiler::source::MAX_SOURCE_BYTES {
            return Err(CaseCompileError::SourceBound(format!(
                "unit `{}` exceeds the {}-byte frontend source bound",
                unit.virtual_path,
                bamts_compiler::source::MAX_SOURCE_BYTES
            )));
        }
        let path = temp.path().join(&unit.virtual_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| CaseCompileError::Load(format!("unit dir: {error}")))?;
        }
        fs::write(&path, &unit.text)
            .map_err(|error| CaseCompileError::Load(format!("unit write: {error}")))?;
    }
    let served = write_mount_files(temp.path(), units);
    for file in support {
        let path = temp.path().join(&file.virtual_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| CaseCompileError::Load(format!("support dir: {error}")))?;
        }
        fs::write(&path, &file.text)
            .map_err(|error| CaseCompileError::Load(format!("support write: {error}")))?;
    }
    // Upstream TypeScript test programs compile every unit together, not just
    // the ones reachable from a single entry. Create a synthetic entrypoint that
    // imports every unit so the S2 harness observes the same program shape.
    const ENTRY: &str = "__bamts_check_entry__.ts";
    let mut entry_source = String::new();
    for (index, unit) in units.iter().enumerate() {
        let specifier = unit.virtual_path.replace('\\', "/");
        if is_check_cell_declaration_path(&specifier) {
            entry_source.push_str(&format!(
                "import type * as _bamts_entry_{index} from \"./{specifier}\";\n"
            ));
        } else {
            entry_source.push_str(&format!("import \"./{specifier}\";\n"));
        }
    }
    fs::write(temp.path().join(ENTRY), entry_source)
        .map_err(|error| CaseCompileError::Load(format!("entry write: {error}")))?;
    let compile = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ProjectRoot::new(temp.path())
            .map_err(|error| CaseCompileError::Load(format!("project root: {error}")))?;
        let config_source = build_tsconfig(pragmas);
        let config_source = inject_mount_paths(config_source, &served);
        let config = ProjectConfig::parse(&root, temp.path().join("tsconfig.json"), &config_source)
            .map_err(|error| CaseCompileError::Load(format!("config: {error}")))?;
        let options = config.options().clone();
        let loader = ProgramLoader::new(&root, config.options())
            .map_err(|error| CaseCompileError::Load(format!("loader: {error}")))?
            .tolerating_unresolved_imports();
        let program = loader
            .load(Path::new(ENTRY))
            .map_err(|error| CaseCompileError::Load(error.to_string()))?;
        let output = compile_program_frontend(&program, mode);
        Ok::<_, CaseCompileError>((program, output, options))
    }));
    let (program, output, options) = match compile {
        Ok(Ok(parts)) => parts,
        Ok(Err(error)) => return Err(error),
        Err(_) => {
            return Err(CaseCompileError::Panic(
                "compiler panicked while checking the case".to_owned(),
            ));
        }
    };
    let pairs = pair_units_with_modules(units, temp.path(), &program);
    // The synthetic entry is not part of the case, so it is intentionally absent
    // from `pairs`. Any diagnostics it produced are also ignored.
    Ok(CheckedCase {
        units: pairs,
        entry: entry_name.to_owned(),
        output,
        program,
        options,
        emit_directory: full_emit_directory(pragmas),
        no_resolve: pragma_enabled(pragmas, "noresolve"),
    })
}

/// Match each unit to its resolved module by canonical path. The loader
/// canonicalizes every module path under the confined root, so unit paths are
/// canonicalized the same way before comparison.
fn pair_units_with_modules(
    units: &[CaseUnit],
    root: &Path,
    program: &ResolvedProgram,
) -> Vec<(CaseUnit, Option<usize>)> {
    units
        .iter()
        .map(|unit| {
            let canonical = canonicalize(root.join(&unit.virtual_path)).ok();
            let index = canonical.and_then(|canonical| {
                program
                    .modules()
                    .iter()
                    .position(|module| module.path() == canonical)
            });
            (unit.clone(), index)
        })
        .collect()
}

pub(super) fn compile_option_pairs(pragmas: &CasePragmas) -> Vec<(String, String)> {
    pragmas
        .options
        .iter()
        .filter_map(|(name, values)| values.first().map(|value| (name.clone(), value.clone())))
        .collect()
}

pub(super) fn read_case_text(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> Result<String> {
    let bytes = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)?;
    Ok(decode_case_source(&bytes))
}

pub(super) fn compile_failure_observation(error: CaseCompileError) -> CompilerCheckObservation {
    let detail = match &error {
        CaseCompileError::Load(detail)
        | CaseCompileError::SourceBound(detail)
        | CaseCompileError::Panic(detail) => detail.clone(),
    };
    CompilerCheckObservation {
        class: error.failure_class(),
        detail,
        artifact: None,
    }
}

pub(super) fn cell_result(plan: &PlannedCell, observation: CompilerCheckObservation) -> CellResult {
    CellResult {
        entry_id: plan.entry.id.clone(),
        facet: plan.entry.facet,
        backend: plan.backend,
        class: observation.class,
        detail: observation.detail,
    }
}

fn pragma_enabled(pragmas: &CasePragmas, name: &str) -> bool {
    pragmas
        .options
        .iter()
        .find(|(key, _)| key == name)
        .and_then(|(_, values)| values.first())
        .is_some_and(|value| value.eq_ignore_ascii_case("true"))
}
