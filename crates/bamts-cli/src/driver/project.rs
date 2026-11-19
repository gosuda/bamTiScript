use super::*;
use bamts_compiler::project::build_mode::BuildInfo;
use bamts_compiler::project::canonical::slash_text;
use bamts_compiler::project::effective::compile_project;
use bamts_compiler::project::effective::compile_project_references;
use bamts_compiler::project::effective::EffectiveProject;
use bamts_compiler::project::effective::load_reference_closure;
use bamts_compiler::project::effective::MaterializeError;
use bamts_compiler::project::effective::ProjectBuildOptions;
use bamts_compiler::project::effective::ProjectCompileError;
use bamts_compiler::project::effective::ProjectCompileOptions;
use bamts_compiler::project::effective::ProjectCompileResult;
use bamts_compiler::project::effective::ProjectLoadRequest;
use bamts_compiler::project::effective::ProjectOptionOverrides;
use bamts_compiler::project::JsonObject;
use bamts_compiler::project::JsonValue;
use bamts_compiler::project::references::resolve_config_file_name;
use bamts_compiler::service::filesystem::OsFileSystem;
use crate::cli::tsc_args::TscDispatchMode;
use crate::cli::tsc_args::TscExitStatus;
use crate::cli::tsc_args::TscOptionValue;
use crate::output::publish_atomic;
use crate::output::StdAtomicFs;
use serde::ser::SerializeMap;
use serde::ser::Serializer;
use serde::ser::SerializeSeq;
use serde::Serialize;
use std::io::Write;
use std::sync::Arc;

pub(super) fn execute_tsc_project(
    command: &ParsedTscCommand,
    cwd: &Path,
) -> Result<CommandOutcome, DriverError> {
    if let Some(option) = command.first_unsupported_option(TscDispatchMode::Project) {
        return Ok(unsupported_option_outcome(option));
    }
    let filesystem = match OsFileSystem::new(cwd) {
        Ok(filesystem) => filesystem,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let request = ProjectLoadRequest {
        config_path: Some(project_config_path(
            cwd,
            command.project().unwrap_or("tsconfig.json"),
        )),
        cwd: cwd.to_path_buf(),
        overrides: project_overrides(command),
        allow_missing_config: false,
        source_files: None,
    };
    let project = match EffectiveProject::load(&request, &filesystem) {
        Ok(project) => project,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    // TypeScript 7.0.2 prints the final merged configuration instead of
    // compiling: no project compilation, reference compilation, emit, or
    // writes happen on this route. The project was loaded exactly once above.
    if command.flag("showConfig") {
        return show_config_outcome(&ProjectShowConfig::new(&project));
    }
    let compile_options = ProjectCompileOptions {
        emit: !command.flag("listFilesOnly"),
        ..ProjectCompileOptions::default()
    };
    let result = match compile_project(&project, &compile_options, &filesystem) {
        Ok(result) => result,
        Err(error) => return Ok(project_compile_error_outcome(error, command, cwd)),
    };
    if !result.up_to_date {
        publish_project_result(&result)?;
    }
    Ok(project_result_outcome(command, &result))
}

pub(super) fn execute_tsc_build(
    command: &ParsedTscCommand,
    cwd: &Path,
) -> Result<CommandOutcome, DriverError> {
    if let Some(option) = command.first_unsupported_option(TscDispatchMode::Build) {
        return Ok(unsupported_option_outcome(option));
    }
    let filesystem = match OsFileSystem::new(cwd) {
        Ok(filesystem) => filesystem,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let root = match ProjectRoot::new(cwd) {
        Ok(root) => root,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let configs = if command.file_names.is_empty() {
        vec![project_config_path(cwd, "tsconfig.json")]
    } else {
        command
            .file_names
            .iter()
            .map(|path| project_config_path(cwd, path))
            .collect()
    };
    if command.flag("clean") {
        let (_, graph) = match load_reference_closure(&root, &configs, &filesystem) {
            Ok(closure) => closure,
            Err(error) => return Ok(project_error_outcome(error.to_string())),
        };
        let mut order = match graph.topological_order() {
            Ok(order) => order,
            Err(error) => return Ok(project_error_outcome(error.to_string())),
        };
        order.reverse();
        for path in order {
            let Some(info_path) = graph
                .node(&path)
                .and_then(|node| node.build_info_path.as_deref())
            else {
                continue;
            };
            let Ok(bytes) = fs::read(info_path) else {
                continue;
            };
            let Ok(info) = BuildInfo::decode(&bytes) else {
                continue;
            };
            if !command.flag("dry") {
                for output in info.outputs {
                    if let Err(source) = fs::remove_file(&output)
                        && source.kind() != io::ErrorKind::NotFound
                    {
                        return Err(DriverError::ProjectConfig {
                            path: output,
                            message: source.to_string(),
                        });
                    }
                }
                let _ = fs::remove_file(info_path);
            }
        }
        return Ok(CommandOutcome::default());
    }

    let stop_on_error = command
        .options
        .get("stopBuildOnErrors")
        .and_then(|value| value.as_bool())
        .unwrap_or(true);
    let report = match compile_project_references(
        &root,
        &configs,
        cwd,
        ProjectBuildOptions {
            force: command.flag("force"),
            stop_on_error,
        },
        &filesystem,
    ) {
        Ok(report) => report,
        Err(error) => return Ok(project_error_outcome(error.to_string())),
    };
    let mut stdout = Vec::new();
    let mut has_errors = false;
    let mut outputs_generated = false;
    for project in report.projects {
        if command.flag("verbose") && !command.flag("dry") {
            if project.result.up_to_date {
                writeln!(
                    stdout,
                    "Project '{}' is up to date",
                    slash_text(&project.config_path)
                )
                .expect("writing to Vec cannot fail");
            } else {
                writeln!(
                    stdout,
                    "Building project '{}'...",
                    slash_text(&project.config_path)
                )
                .expect("writing to Vec cannot fail");
            }
        }
        let outcome = project_result_outcome(command, &project.result);
        stdout.extend_from_slice(&outcome.stdout);
        has_errors |= outcome.exit_code != TscExitStatus::Success.code();
        if command.flag("dry") {
            writeln!(stdout, "Would build {}", slash_text(&project.config_path))
                .expect("writing to Vec cannot fail");
        } else if !project.result.up_to_date {
            publish_project_result(&project.result)?;
            outputs_generated |= project.result.emitted;
        }
    }
    has_errors |= !report.blocked.is_empty();
    Ok(CommandOutcome {
        stdout,
        stderr: Vec::new(),
        exit_code: TscExitStatus::from_compilation(has_errors, outputs_generated).code(),
        truncation: None,
    })
}

pub(super) fn project_overrides(command: &ParsedTscCommand) -> ProjectOptionOverrides {
    let boolean = |name: &str| command.options.get(name).and_then(|value| value.as_bool());
    let string = |name: &str| command.option_str(name).map(Arc::<str>::from);
    ProjectOptionOverrides {
        no_emit: boolean("noEmit"),
        no_emit_on_error: boolean("noEmitOnError"),
        declaration: boolean("declaration"),
        declaration_map: boolean("declarationMap"),
        source_map: boolean("sourceMap"),
        inline_source_map: boolean("inlineSourceMap"),
        inline_sources: boolean("inlineSources"),
        out_dir: command.option_str("outDir").map(PathBuf::from),
        root_dir: command.option_str("rootDir").map(PathBuf::from),
        map_root: command.option_str("mapRoot").map(Arc::from),
        out_file: command.option_str("outFile").map(PathBuf::from),
        always_strict: boolean("alwaysStrict"),
        ts_build_info_file: command.option_str("tsBuildInfoFile").map(PathBuf::from),
        strict: boolean("strict"),
        no_implicit_any: boolean("noImplicitAny"),
        strict_null_checks: boolean("strictNullChecks"),
        strict_property_initialization: boolean("strictPropertyInitialization"),
        allow_js: boolean("allowJs"),
        check_js: boolean("checkJs"),
        jsx: command.option_str("jsx").map(Arc::from),
        source_root: command.option_str("sourceRoot").map(Arc::from),
        target: string("target"),
        module: string("module"),
        module_resolution: string("moduleResolution"),
        module_detection: string("moduleDetection"),
        new_line: string("newLine"),
        jsx_factory: string("jsxFactory"),
        jsx_fragment_factory: string("jsxFragmentFactory"),
        jsx_import_source: string("jsxImportSource"),
        resolve_json_module: boolean("resolveJsonModule"),
        declaration_dir: command.option_str("declarationDir").map(PathBuf::from),
        base_url: command.option_str("baseUrl").map(PathBuf::from),
        emit_declaration_only: boolean("emitDeclarationOnly"),
        incremental: boolean("incremental"),
        composite: boolean("composite"),
        es_module_interop: boolean("esModuleInterop"),
        import_helpers: boolean("importHelpers"),
        isolated_modules: boolean("isolatedModules"),
        verbatim_module_syntax: boolean("verbatimModuleSyntax"),
        trace_resolution: boolean("traceResolution"),
        lib: command
            .options
            .get("lib")
            .and_then(|value| value.as_list())
            .map(|items| Arc::from(items.to_vec())),
    }
}

pub(super) fn project_config_path(cwd: &Path, path: &str) -> PathBuf {
    let path = PathBuf::from(path);
    let path = if path.is_absolute() {
        path
    } else {
        cwd.join(path)
    };
    resolve_config_file_name(path)
}

pub(super) fn publish_project_result(result: &ProjectCompileResult) -> Result<(), DriverError> {
    let mut atomic = StdAtomicFs;
    for (path, bytes) in &result.outputs.files {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
                path: parent.to_path_buf(),
                source,
            })?;
        }
        publish_atomic(&mut atomic, path, bytes).map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
    }
    if let Some((path, info)) = &result.build_info {
        let bytes = info.encode().map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|source| DriverError::CreateDirectory {
                path: parent.to_path_buf(),
                source,
            })?;
        }
        publish_atomic(&mut atomic, path, &bytes).map_err(|error| DriverError::ProjectConfig {
            path: path.clone(),
            message: error.to_string(),
        })?;
    }
    Ok(())
}

pub(super) fn project_result_outcome(
    command: &ParsedTscCommand,
    result: &ProjectCompileResult,
) -> CommandOutcome {
    let diagnostics = map_parse_diagnostics(&result.diagnostics);
    let has_errors = diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Error);
    let names = result
        .sources
        .iter()
        .map(|source| slash_text(&source.path))
        .collect::<Vec<_>>();
    let mut sources = result
        .sources
        .iter()
        .zip(&names)
        .map(|(source, name)| DiagnosticSource {
            id: source.id,
            name,
            text: &source.text,
        })
        .collect::<Vec<_>>();
    let tsconfig_name = result
        .tsconfig_source
        .as_ref()
        .map(|tsconfig| slash_text(&tsconfig.path));
    if let (Some(tsconfig), Some(name)) = (&result.tsconfig_source, &tsconfig_name) {
        sources.push(DiagnosticSource {
            id: tsconfig.id,
            name,
            text: &tsconfig.text,
        });
    }
    let format = if command.pretty() {
        TscDiagnosticFormat::Pretty
    } else {
        TscDiagnosticFormat::PrettyFalse
    };
    let mut stdout = if command.flag("listFilesOnly") {
        Vec::new()
    } else {
        tsc_diagnostics::render(format, &diagnostics, &sources).into_bytes()
    };
    if command.flag("listFiles") || command.flag("listFilesOnly") {
        for name in &names {
            writeln!(stdout, "{name}").expect("writing to Vec cannot fail");
        }
    }
    CommandOutcome {
        stdout,
        exit_code: if command.flag("listFilesOnly") {
            TscExitStatus::Success.code()
        } else {
            TscExitStatus::from_compilation(has_errors, result.emitted).code()
        },
        ..CommandOutcome::default()
    }
}

pub(super) fn project_compile_error_outcome(
    error: ProjectCompileError,
    command: &ParsedTscCommand,
    cwd: &Path,
) -> CommandOutcome {
    match error {
        unsupported @ ProjectCompileError::UnsupportedOption { .. } => {
            not_implemented(&unsupported.to_string())
        }
        ProjectCompileError::ConfigNotFound { path } => {
            config_not_found_outcome(command, cwd, &path)
        }
        ProjectCompileError::Materialize(
            materialize @ (MaterializeError::FilesListEmpty { .. }
            | MaterializeError::NoInputs { .. }),
        ) => project_diagnostic_outcome(materialize.to_string()),
        other => project_error_outcome(other.to_string()),
    }
}

pub(super) fn config_not_found_outcome(
    command: &ParsedTscCommand,
    cwd: &Path,
    config_path: &Path,
) -> CommandOutcome {
    let Some(project) = command.project() else {
        return tsc_error_outcome(
            "TS5081",
            format!(
                "Cannot find a tsconfig.json file at the current directory: {}.",
                slash_text(config_path)
            ),
        );
    };
    let project_path = Path::new(project);
    if project_path
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
    {
        return tsc_error_outcome(
            "TS5083",
            format!("Cannot read file '{}'.", slash_text(config_path)),
        );
    }
    let directory = if project_path.is_absolute() {
        project_path.to_path_buf()
    } else {
        cwd.join(project_path)
    };
    tsc_error_outcome(
        "TS5057",
        format!(
            "Cannot find a tsconfig.json file at the specified directory: '{}'.",
            slash_text(&directory)
        ),
    )
}

pub(super) fn project_diagnostic_outcome(message: String) -> CommandOutcome {
    CommandOutcome {
        stdout: format!("error {message}\n").into_bytes(),
        exit_code: TscExitStatus::DiagnosticsPresentOutputsSkipped.code(),
        ..CommandOutcome::default()
    }
}

pub(super) fn project_error_outcome(message: String) -> CommandOutcome {
    tsc_error_outcome("TS5083", message)
}

pub(super) fn tsc_error_outcome(code: &str, message: String) -> CommandOutcome {
    CommandOutcome {
        stdout: format!("error {code}: {message}\n").into_bytes(),
        exit_code: TscExitStatus::DiagnosticsPresentOutputsSkipped.code(),
        ..CommandOutcome::default()
    }
}

pub(super) fn not_implemented(message: &str) -> CommandOutcome {
    CommandOutcome {
        stderr: format!("error TS5047: {message}\n").into_bytes(),
        exit_code: TscExitStatus::NotImplemented.code(),
        ..CommandOutcome::default()
    }
}

pub(super) fn unsupported_option_outcome(option: &str) -> CommandOutcome {
    not_implemented(&format!(
        "Compiler option '--{option}' has no canonical native driver mapping."
    ))
}

// ---------------------------------------------------------------------------
// `--showConfig`: borrowed TypeScript 7.0.2 configuration serialization.
//
// The document is a `serde::Serialize` view over the immutable
// `bamts_compiler::project::JsonValue` graph. Nothing is cloned into
// `serde_json::Value`; rendering walks the borrowed entries in declaration
// order so the output is byte-deterministic. Serialization failure is typed,
// not unwrapped: [`DriverError::ShowConfigRender`] carries the io error.
// ---------------------------------------------------------------------------

/// Renders one borrowed effective-configuration document as TypeScript
/// `--showConfig` bytes: four-space `serde_json` indentation plus exactly one
/// trailing newline. The writer failure is the io error itself, and a JSON
/// serialization failure (non-finite number) is reported as io::InvalidData
/// through the same typed [`DriverError::ShowConfigRender`] channel.
pub(super) fn render_show_config_document<T: Serialize>(document: &T) -> Result<Vec<u8>, DriverError> {
    let mut buffer = Vec::new();
    let mut serializer = serde_json::Serializer::with_formatter(
        &mut buffer,
        serde_json::ser::PrettyFormatter::with_indent(b"    "),
    );
    document
        .serialize(&mut serializer)
        .map_err(|error| DriverError::ShowConfigRender {
            source: io::Error::new(io::ErrorKind::InvalidData, error.to_string()),
        })?;
    buffer.push(b'\n');
    Ok(buffer)
}

/// One typed key/value slot of the direct-route `--showConfig` document.
/// Direct dispatch emits only options explicitly supplied on the command
/// line, in the lexical order of the parsed `BTreeMap` — which matches
/// TypeScript 7.0.2's observed output order (verified by probe: `strict`
/// precedes `target` regardless of argv order). Enum values were already
/// canonicalized to lower case by the argv parser.
pub(super) enum DirectCompilerOption<'a> {
    Bool(bool),
    Text(&'a str),
    Items(&'a [String]),
    Number(i32),
}

impl Serialize for DirectCompilerOption<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Bool(value) => serializer.serialize_bool(*value),
            Self::Text(value) => serializer.serialize_str(value),
            Self::Items(values) => serializer.collect_seq(values.iter()),
            Self::Number(value) => serializer.serialize_i32(*value),
        }
    }
}

/// The direct-route `--showConfig` document: effective CLI compiler options
/// plus the argv file list, rendered relative to the process working
/// directory with TypeScript's `./` prefix (probe-verified).
pub(super) struct DirectShowConfig<'a> {
    pub(super) command: &'a ParsedTscCommand,
    pub(super) cwd: &'a Path,
}

impl Serialize for DirectShowConfig<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let options: Vec<(&'static str, DirectCompilerOption<'_>)> =
            direct_compiler_options(self.command).collect();
        let files: Vec<String> = self
            .command
            .file_names
            .iter()
            .map(|name| {
                let path = self.cwd.join(name);
                ProjectShowConfig::relative_path(self.cwd, &path)
            })
            .collect();
        let mut state = serializer.serialize_map(Some(2))?;
        state.serialize_entry("compilerOptions", &SerializeMapEntries(options.iter()))?;
        state.serialize_entry("files", &files)?;
        state.end()
    }
}

/// Serializes a borrowed compiler-option sequence as a JSON object so the
/// document keeps TypeScript's key order instead of a struct field order.
pub(super) struct SerializeMapEntries<I>(I);

impl<'a> Serialize
    for SerializeMapEntries<std::slice::Iter<'a, (&'static str, DirectCompilerOption<'a>)>>
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_map(Some(self.0.len()))?;
        for (key, value) in self.0.clone() {
            state.serialize_entry(key, value)?;
        }
        state.end()
    }
}

/// Borrowed compiler-options serializer: emits the canonical explicit
/// `JsonObject` entries first, then the synthesized implied entries,
/// inside one `compilerOptions` map — matching TypeScript 7.0.2, which
/// nests implied options inside `compilerOptions` rather than emitting
/// them as top-level document keys.
pub(super) struct CompilerOptionsView<'a> {
    canonical: &'a JsonValue,
    implied: &'a [(String, JsonValue)],
}

impl Serialize for CompilerOptionsView<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.canonical {
            JsonValue::Object(explicit) => {
                let mut state = serializer
                    .serialize_map(Some(explicit.entries().len() + self.implied.len()))?;
                for (key, value) in explicit.entries() {
                    state.serialize_entry(key.as_ref(), &JsonViewRef(value))?;
                }
                for (name, value) in self.implied {
                    state.serialize_entry(name.as_str(), &JsonViewRef(value))?;
                }
                state.end()
            }
            other => JsonViewRef(other).serialize(serializer),
        }
    }
}

pub(super) struct ProjectShowConfig<'a> {
    project: &'a EffectiveProject,
}

impl<'a> ProjectShowConfig<'a> {
    pub(super) fn new(project: &'a EffectiveProject) -> Self {
        Self { project }
    }

    /// Lexical relative path from `base` to `path` in TypeScript showConfig
    /// form: descendants and equal paths get a leading `./`, parents and
    /// siblings use `../` components. Both inputs are absolute; incompatible
    /// Windows prefixes or roots fall back to the absolute path text rather
    /// than producing a meaningless cross-root traversal.
    pub(super) fn relative_path(base: &Path, path: &Path) -> String {
        /// Splits an absolute path into its filesystem root (prefix +
        /// rootdir) and the remaining normal components. Non-normal
        /// components (`.`, `..`) cause `None` so the caller falls back
        /// to the absolute text instead of mis-rendering.
        fn split_absolute(p: &Path) -> Option<(String, Vec<String>)> {
            let mut root = String::new();
            let mut normals = Vec::new();
            for component in p.components() {
                match component {
                    std::path::Component::Prefix(prefix) => {
                        root.push_str(&prefix.as_os_str().to_string_lossy());
                    }
                    std::path::Component::RootDir => {
                        root.push('/');
                    }
                    std::path::Component::Normal(segment) => {
                        normals.push(
                            segment
                                .to_string_lossy()
                                .replace(std::path::MAIN_SEPARATOR, "/"),
                        );
                    }
                    std::path::Component::CurDir | std::path::Component::ParentDir => return None,
                }
            }
            if root.is_empty() {
                return None;
            }
            Some((root, normals))
        }
        let Some((base_root, base_normals)) = split_absolute(base) else {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        };
        let Some((path_root, path_normals)) = split_absolute(path) else {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        };
        if base_root != path_root {
            return path
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, "/");
        }
        let shared = base_normals
            .iter()
            .zip(path_normals.iter())
            .take_while(|(from, to)| from == to)
            .count();
        let mut relative = String::new();
        for _ in shared..base_normals.len() {
            relative.push_str("../");
        }
        if relative.is_empty() {
            relative.push_str("./");
        }
        relative.push_str(&path_normals[shared..].join("/"));
        relative
    }
}

impl Serialize for ProjectShowConfig<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let raw = self.project.config().config().raw();
        let config_directory = self
            .project
            .config_path()
            .parent()
            .expect("config path always has a parent directory");

        let mut state = serializer.serialize_map(None)?;
        let empty_object = JsonValue::Object(JsonObject::from_entries(Vec::new()));
        let compiler_options = raw.get("compilerOptions").unwrap_or(&empty_object);
        let canonical = canonicalize_compiler_options(compiler_options, config_directory);
        // TypeScript 7.0.2 nests the implied options it reports for the
        // supported target/module surface inside `compilerOptions`, appended
        // after the explicit entries. Each implication applies only when the
        // user did not set the option explicitly.
        let implied: Vec<(String, JsonValue)> = implied_compiler_options(raw);
        state.serialize_entry(
            "compilerOptions",
            &CompilerOptionsView {
                canonical: &canonical,
                implied: &implied,
            },
        )?;
        let references: Vec<SerializeReferenceEntry> = self
            .project
            .references()
            .iter()
            .map(|reference| SerializeReferenceEntry {
                base: config_directory,
                path: reference.path(),
            })
            .collect();
        if !references.is_empty() {
            state.serialize_entry("references", &references)?;
        }
        let files: Vec<String> = self
            .project
            .source_files()
            .iter()
            .map(|path| Self::relative_path(config_directory, path))
            .collect();
        if !files.is_empty() {
            state.serialize_entry("files", &files)?;
        }
        if let Some(include) = raw.get("include") {
            let paths: Vec<String> = include
                .as_array()
                .into_iter()
                .flatten()
                .map(|value| {
                    Self::relative_path(
                        config_directory,
                        Path::new(value.as_str().expect("include entry is a string")),
                    )
                })
                .collect();
            state.serialize_entry("include", &paths)?;
        }
        if let Some(exclude) = raw.get("exclude") {
            let paths: Vec<String> = exclude
                .as_array()
                .into_iter()
                .flatten()
                .map(|value| {
                    Self::relative_path(
                        config_directory,
                        Path::new(value.as_str().expect("exclude entry is a string")),
                    )
                })
                .collect();
            state.serialize_entry("exclude", &paths)?;
        }

        state.end()
    }
}

/// Rewrites compiler-option values onto their canonical TypeScript form:
/// enum values are lower-cased (`ES2022` → `es2022`, `NODE16` →
/// `node16`, …), and path-like fields that the effective-config loader
/// rewrote to absolute form are relativized back against the config
/// directory so the output matches TypeScript's `--showConfig` text.
pub(super) fn canonicalize_compiler_options(options: &JsonValue, config_directory: &Path) -> JsonValue {
    const ENUM_OPTIONS: &[&str] = &[
        "target",
        "module",
        "jsx",
        "moduleResolution",
        "moduleDetection",
        "newLine",
    ];
    const PATH_FIELDS: &[&str] = &[
        "baseUrl",
        "rootDir",
        "outDir",
        "declarationDir",
        "outFile",
        "tsBuildInfoFile",
    ];
    let Some(object) = options.as_object() else {
        return options.clone();
    };
    let base_url = object
        .get("baseUrl")
        .and_then(JsonValue::as_str)
        .map(PathBuf::from)
        .unwrap_or_else(|| config_directory.to_path_buf());
    let entries = object
        .entries()
        .iter()
        .map(|(key, value)| {
            let key_str = key.as_ref();
            let value = if ENUM_OPTIONS.contains(&key_str) {
                match value {
                    JsonValue::String(text) => {
                        JsonValue::String(Arc::from(text.to_ascii_lowercase().as_str()))
                    }
                    other => other.clone(),
                }
            } else if PATH_FIELDS.contains(&key_str) {
                match value {
                    JsonValue::String(text) => JsonValue::String(Arc::from(
                        ProjectShowConfig::relative_path(config_directory, Path::new(&**text))
                            .as_str(),
                    )),
                    other => other.clone(),
                }
            } else if key_str == "typeRoots" {
                match value {
                    JsonValue::Array(items) => {
                        let relativized: Vec<JsonValue> = items
                            .iter()
                            .map(|item| {
                                let text = item.as_str().expect("typeRoots entry is a string");
                                JsonValue::String(Arc::from(
                                    ProjectShowConfig::relative_path(
                                        config_directory,
                                        Path::new(text),
                                    )
                                    .as_str(),
                                ))
                            })
                            .collect();
                        JsonValue::Array(Arc::from(relativized))
                    }
                    other => other.clone(),
                }
            } else if key_str == "paths" {
                match value {
                    JsonValue::Object(mappings) => {
                        let rewritten: Vec<(Arc<str>, JsonValue)> = mappings
                            .entries()
                            .iter()
                            .map(|(pattern, targets)| {
                                let relativized = match targets {
                                    JsonValue::Array(items) => {
                                        let relativized: Vec<JsonValue> = items
                                            .iter()
                                            .map(|item| {
                                                let text = item
                                                    .as_str()
                                                    .expect("paths target is a string");
                                                JsonValue::String(Arc::from(
                                                    ProjectShowConfig::relative_path(
                                                        &base_url,
                                                        Path::new(text),
                                                    )
                                                    .as_str(),
                                                ))
                                            })
                                            .collect();
                                        JsonValue::Array(Arc::from(relativized))
                                    }
                                    other => other.clone(),
                                };
                                (Arc::clone(pattern), relativized)
                            })
                            .collect();
                        JsonValue::Object(JsonObject::from_entries(rewritten))
                    }
                    other => other.clone(),
                }
            } else {
                match value {
                    JsonValue::Object(nested) => canonicalize_compiler_options(
                        &JsonValue::Object(nested.clone()),
                        config_directory,
                    ),
                    other => other.clone(),
                }
            };
            (key.clone(), value)
        })
        .collect();
    JsonValue::Object(JsonObject::from_entries(entries))
}

/// Computes the implied compiler options TypeScript 7.0.2 appends to a
/// project `--showConfig` document, derived from observable CLI probes:
/// - `module` implies `moduleResolution` (node16/node18 → "node16",
///   node20/nodenext → that module) and `moduleDetection: "force"`;
///   node16/node18 also imply `resolveJsonModule: false`.
/// - `target` implies `module` (pre-es2022 targets → "es6"/"es2020",
///   esnext → "esnext") and `useDefineForClassFields: false` for
///   pre-es2022 targets.
///
/// Every implication applies only when the option is not explicitly set.
pub(super) fn implied_compiler_options(raw: &JsonObject) -> Vec<(String, JsonValue)> {
    let Some(options) = raw.get("compilerOptions").and_then(JsonValue::as_object) else {
        return Vec::new();
    };
    let text = |name: &str| options.get(name).and_then(JsonValue::as_str);
    let set = |name: &str| options.get(name).is_some();
    let mut implied: Vec<(String, JsonValue)> = Vec::new();

    if let Some(module) = text("module") {
        if !set("moduleResolution") {
            let resolution = match module {
                "node16" | "node18" => Some("node16"),
                "node20" | "nodenext" => Some(module),
                _ => None,
            };
            if let Some(resolution) = resolution {
                implied.push((
                    "moduleResolution".to_owned(),
                    JsonValue::String(Arc::from(resolution)),
                ));
            }
        }
        if !set("moduleDetection") && matches!(module, "node16" | "node18" | "node20" | "nodenext")
        {
            implied.push((
                "moduleDetection".to_owned(),
                JsonValue::String(Arc::from("force")),
            ));
        }
        if !set("resolveJsonModule") && matches!(module, "node16" | "node18") {
            implied.push(("resolveJsonModule".to_owned(), JsonValue::Bool(false)));
        }
    }

    if let Some(target) = text("target") {
        if !set("module") {
            let module = match target {
                "es6" | "es2015" | "es2016" | "es2017" | "es2018" | "es2019" => Some("es6"),
                "es2020" | "es2021" => Some("es2020"),
                "esnext" => Some("esnext"),
                _ => None,
            };
            if let Some(module) = module {
                implied.push(("module".to_owned(), JsonValue::String(Arc::from(module))));
            }
        }
        if !set("useDefineForClassFields")
            && matches!(
                target,
                "es6" | "es2015" | "es2016" | "es2017" | "es2018" | "es2019" | "es2020" | "es2021"
            )
        {
            implied.push(("useDefineForClassFields".to_owned(), JsonValue::Bool(false)));
        }
    }

    implied
}

/// One `references` entry serialized relative to the config directory.
pub(super) struct SerializeReferenceEntry<'a> {
    base: &'a Path,
    path: &'a Path,
}

impl Serialize for SerializeReferenceEntry<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_map(Some(1))?;
        state.serialize_entry(
            "path",
            &ProjectShowConfig::relative_path(self.base, self.path),
        )?;
        state.end()
    }
}

/// Renders a showConfig document and wraps it in a success outcome.
pub(super) fn show_config_outcome<T: Serialize>(document: &T) -> Result<CommandOutcome, DriverError> {
    Ok(CommandOutcome {
        stdout: render_show_config_document(document)?,
        exit_code: TscExitStatus::Success.code(),
        ..CommandOutcome::default()
    })
}

/// Iterates the parsed direct command in the lexical order of the
/// `BTreeMap`, which matches TypeScript 7.0.2's observed output order
/// (verified by probe: `strict` precedes `target` for both argv orders).
/// Only parser-validated option names are emitted.
pub(super) fn direct_compiler_options(
    command: &ParsedTscCommand,
) -> impl Iterator<Item = (&'static str, DirectCompilerOption<'_>)> {
    command.options.iter().filter_map(|(name, value)| {
        // Dispatch controls are consumed by routing, not compiler state.
        if matches!(
            name.as_str(),
            "help" | "version" | "init" | "showConfig" | "ignoreConfig" | "pretty" | "project"
        ) {
            return None;
        }
        let name = crate::cli::tsc_args::canonical_option_name(name)?;
        let value = match value {
            TscOptionValue::Bool(value) => DirectCompilerOption::Bool(*value),
            TscOptionValue::String(value) => DirectCompilerOption::Text(value.as_str()),
            TscOptionValue::Number(value) => DirectCompilerOption::Number(*value),
            TscOptionValue::List(values) => DirectCompilerOption::Items(values.as_slice()),
            TscOptionValue::Null => return None,
        };
        Some((name, value))
    })
}

/// Shared serializer body over any referenced JSON value.
pub(super) struct JsonViewRef<'a>(&'a JsonValue);

impl Serialize for JsonViewRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            JsonValue::Null => serializer.serialize_none(),
            JsonValue::Bool(value) => serializer.serialize_bool(*value),
            JsonValue::Number(value) => {
                if let Ok(number) = value.parse::<i64>() {
                    serializer.serialize_i64(number)
                } else if let Ok(number) = value.parse::<u64>() {
                    serializer.serialize_u64(number)
                } else if let Ok(number) = value.parse::<f64>() {
                    serializer.serialize_f64(number)
                } else {
                    Err(serde::ser::Error::custom(format!(
                        "invalid JSON number {value:?}"
                    )))
                }
            }
            JsonValue::String(value) => serializer.serialize_str(value),
            JsonValue::Array(values) => {
                let mut state = serializer.serialize_seq(Some(values.len()))?;
                for value in values.iter() {
                    state.serialize_element(&JsonViewRef(value))?;
                }
                state.end()
            }
            JsonValue::Object(object) => {
                let mut state = serializer.serialize_map(Some(object.entries().len()))?;
                for (key, value) in object.entries() {
                    state.serialize_entry(key.as_ref(), &JsonViewRef(value))?;
                }
                state.end()
            }
        }
    }
}
