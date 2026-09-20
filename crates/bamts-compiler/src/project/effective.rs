use super::{
    CompilerOptions, JsonObject, JsonValue, PathError, ProjectRoot,
    build_mode::{
        BUILD_INFO_SCHEMA, BuildInfo, BuildOutputs, is_project_up_to_date, options_signature,
        project_signature, source_signature,
    },
    output::{ArtifactKind, ArtifactSelection, OutputMapError, PlanRequest, map_output_paths},
    references::{ReferenceError, ReferenceGraph, resolve_config_file_name},
    tsconfig::{ProjectReference, ResolvedExtends, TsConfig, TsConfigError, resolve_extends},
};
use crate::{
    diagnostic::Diagnostic,
    emitter::{self, EmitFileNames, EmitOptions},
    lint::{LintProfile, LintTable},
    pipeline::{FrontendMode, compile_program_frontend_with_lints},
    program::{JsxRoutingDecision, ProgramLoader, ProgramOutputKind},
    service::filesystem::{FileSystem, FileSystemError},
    source::{JsxEmit, SourceId, SourceText},
};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
    io::ErrorKind,
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProjectOptionOverrides {
    pub no_emit: Option<bool>,
    pub no_emit_on_error: Option<bool>,
    pub declaration_map: Option<bool>,
    pub inline_source_map: Option<bool>,
    pub inline_sources: Option<bool>,
    pub declaration: Option<bool>,
    pub source_map: Option<bool>,
    pub out_dir: Option<PathBuf>,
    pub root_dir: Option<PathBuf>,
    pub map_root: Option<Arc<str>>,
    pub out_file: Option<PathBuf>,
    pub ts_build_info_file: Option<PathBuf>,
    pub strict: Option<bool>,
    pub no_implicit_any: Option<bool>,
    pub strict_null_checks: Option<bool>,
    pub strict_property_initialization: Option<bool>,
    pub always_strict: Option<bool>,
    pub allow_js: Option<bool>,
    pub check_js: Option<bool>,
    pub jsx: Option<Arc<str>>,
    pub source_root: Option<Arc<str>>,
    // Enum / string-valued compiler options forwarded from argv.
    pub target: Option<Arc<str>>,
    pub module: Option<Arc<str>>,
    pub module_resolution: Option<Arc<str>>,
    pub module_detection: Option<Arc<str>>,
    pub new_line: Option<Arc<str>>,
    pub jsx_factory: Option<Arc<str>>,
    pub jsx_fragment_factory: Option<Arc<str>>,
    pub jsx_import_source: Option<Arc<str>>,
    pub resolve_json_module: Option<bool>,
    pub declaration_dir: Option<PathBuf>,
    pub base_url: Option<PathBuf>,
    // Boolean compiler options forwarded from argv.
    pub emit_declaration_only: Option<bool>,
    pub incremental: Option<bool>,
    pub composite: Option<bool>,
    pub es_module_interop: Option<bool>,
    pub isolated_modules: Option<bool>,
    pub verbatim_module_syntax: Option<bool>,
    pub trace_resolution: Option<bool>,
    // List-valued compiler option forwarded from argv.
    pub lib: Option<Arc<[String]>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectLoadRequest {
    pub config_path: Option<PathBuf>,
    pub cwd: PathBuf,
    pub overrides: ProjectOptionOverrides,
    pub allow_missing_config: bool,
    /// Explicit roots supplied by direct CLI compilation.
    pub source_files: Option<Vec<PathBuf>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectiveProject {
    root: ProjectRoot,
    config_path: PathBuf,
    options: CompilerOptions,
    source_files: Arc<[PathBuf]>,
    references: Arc<[ProjectReference]>,
    build_info_path: Option<PathBuf>,
    config: TsConfig,
}

impl EffectiveProject {
    pub fn load(
        request: &ProjectLoadRequest,
        fs: &dyn FileSystem,
    ) -> Result<Self, ProjectCompileError> {
        let cwd = fs
            .normalize(&request.cwd)
            .map_err(ProjectCompileError::FileSystem)?;
        let root = ProjectRoot::new(&cwd).map_err(ProjectCompileError::Path)?;
        let requested = request
            .config_path
            .as_deref()
            .unwrap_or_else(|| Path::new("tsconfig.json"));
        let config_path = root
            .resolve_from(&cwd, requested)
            .map_err(ProjectCompileError::Path)?;
        // Direct CLI compilation supplies its own roots and no configuration
        // document: the effective options come only from the overrides.
        let (raw, diagnostic_patterns) = match &request.source_files {
            Some(_) => (
                JsonObject::from_entries(Vec::new()),
                DiagnosticPatterns::default(),
            ),
            None => {
                let source = match fs.read(&config_path) {
                    Ok(source) => source,
                    Err(error)
                        if error.kind() == ErrorKind::NotFound && request.allow_missing_config =>
                    {
                        String::from("{}")
                    }
                    Err(error) if error.kind() == ErrorKind::NotFound => {
                        return Err(ProjectCompileError::ConfigNotFound { path: config_path });
                    }
                    Err(error) => return Err(ProjectCompileError::FileSystem(error)),
                };
                load_merged_raw(&root, &config_path, &source, fs)?
            }
        };
        let raw = apply_overrides(&root, &cwd, raw, &request.overrides)?;
        let raw = normalize_composite_options(raw);
        let config =
            TsConfig::parse_value(&root, &config_path, raw).map_err(ProjectCompileError::Config)?;
        let source_files = match &request.source_files {
            Some(paths) => materialize_explicit_sources(&root, paths)?,
            None => materialize_sources(&root, &config, &diagnostic_patterns, fs)?,
        };
        let build_info_path = effective_build_info_path(&root, &config)?;

        Ok(Self {
            root,
            config_path,
            options: config.options().clone(),
            source_files,
            references: Arc::from(config.references()),
            build_info_path,
            config,
        })
    }

    #[must_use]
    pub const fn root(&self) -> &ProjectRoot {
        &self.root
    }

    #[must_use]
    pub fn config_path(&self) -> &Path {
        &self.config_path
    }

    #[must_use]
    pub const fn options(&self) -> &CompilerOptions {
        &self.options
    }

    #[must_use]
    pub fn source_files(&self) -> &[PathBuf] {
        &self.source_files
    }

    #[must_use]
    pub fn references(&self) -> &[ProjectReference] {
        &self.references
    }

    #[must_use]
    pub fn build_info_path(&self) -> Option<&Path> {
        self.build_info_path.as_deref()
    }

    #[must_use]
    pub const fn config(&self) -> &TsConfig {
        &self.config
    }
}

/// Controls one canonical project compilation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectCompileOptions {
    /// Produce configured artifacts. `noEmit` still takes precedence.
    pub emit: bool,
    /// Ignore an otherwise valid incremental build-info record.
    pub force: bool,
    /// Already-built reference signatures, keyed by referenced config path.
    pub upstream_signatures: BTreeMap<PathBuf, Arc<str>>,
}

impl Default for ProjectCompileOptions {
    fn default() -> Self {
        Self {
            emit: true,
            force: false,
            upstream_signatures: BTreeMap::new(),
        }
    }
}

/// A source retained from the one shared resolved program graph.
#[derive(Clone, Debug)]
pub struct ProjectSource {
    pub id: SourceId,
    pub path: PathBuf,
    pub text: Arc<SourceText>,
}

/// Canonical project compilation output.
#[derive(Clone, Debug)]
pub struct ProjectCompileResult {
    pub diagnostics: Vec<Diagnostic>,
    pub sources: Arc<[ProjectSource]>,
    pub outputs: BuildOutputs,
    pub emitted: bool,
    pub up_to_date: bool,
    pub build_info: Option<(PathBuf, BuildInfo)>,
}

/// Loads, checks, and emits a materialized project through one shared program graph.
pub fn compile_project<F: FileSystem + Clone>(
    project: &EffectiveProject,
    options: &ProjectCompileOptions,
    fs: &F,
) -> Result<ProjectCompileResult, ProjectCompileError> {
    if project.options().out_file().is_some() {
        return Err(ProjectCompileError::UnsupportedOption { option: "outFile" });
    }
    if project.options().source_map() && project.options().inline_source_map() {
        return Err(ProjectCompileError::UnsupportedOption {
            option: "sourceMap with inlineSourceMap",
        });
    }
    if project.options().inline_sources()
        && !project.options().source_map()
        && !project.options().inline_source_map()
    {
        return Err(ProjectCompileError::UnsupportedOption {
            option: "inlineSources without sourceMap or inlineSourceMap",
        });
    }

    let loader =
        ProgramLoader::with_file_system(project.root(), project.options(), Arc::new(fs.clone()))
            .map_err(|error| ProjectCompileError::Load(Arc::from(error.to_string())))?;
    let program = loader
        .load_roots(project.source_files())
        .map_err(|error| ProjectCompileError::Load(Arc::from(error.to_string())))?;
    let sources: Arc<[ProjectSource]> = program
        .modules()
        .iter()
        .map(|module| ProjectSource {
            id: module.source_id(),
            path: module.path().to_path_buf(),
            text: Arc::clone(module.source()),
        })
        .collect::<Vec<_>>()
        .into();
    let program_sources = sources
        .iter()
        .map(|source| source.path.clone())
        .collect::<Vec<_>>();

    let should_emit = options.emit && !project.options().no_emit();
    let selection = ArtifactSelection {
        javascript: should_emit && !project.options().emit_declaration_only(),
        declaration: should_emit
            && (project.options().declaration()
                || project.options().composite()
                || project.options().emit_declaration_only()),
        source_map: should_emit
            && !project.options().emit_declaration_only()
            && project.options().source_map()
            && !project.options().inline_source_map(),
        declaration_map: should_emit
            && (project.options().declaration()
                || project.options().composite()
                || project.options().emit_declaration_only())
            && project.options().declaration_map(),
    };
    // Root loading applies module-resolution extension substitution, so distinct configured
    // inputs can collapse to one program module before their output collision is visible.
    if should_emit && project.source_files().len() != program.roots().len() {
        map_output_paths(PlanRequest {
            project_root: project.root().path(),
            sources: project.source_files(),
            root_dir: project.options().root_dir(),
            out_dir: project.options().out_dir(),
            declaration_dir: project.options().declaration_dir(),
            jsx_preserve: project.options().jsx() == Some(JsxEmit::Preserve),
            artifacts: selection,
        })
        .map_err(ProjectCompileError::Output)?;
    }

    let output_plan = should_emit
        .then(|| {
            map_output_paths(PlanRequest {
                project_root: project.root().path(),
                sources: &program_sources,
                root_dir: project.options().root_dir(),
                out_dir: project.options().out_dir(),
                declaration_dir: project.options().declaration_dir(),
                jsx_preserve: project.options().jsx() == Some(JsxEmit::Preserve),
                artifacts: selection,
            })
        })
        .transpose()
        .map_err(ProjectCompileError::Output)?;

    let build_state = build_state(project, &program, output_plan.as_ref(), options)?;
    if !options.force
        && should_emit
        && let Some((path, current)) = &build_state
        && let Ok(encoded) = fs.read(path)
        && let Ok(previous) = BuildInfo::decode(encoded.as_bytes())
    {
        let outputs_present = previous
            .outputs
            .iter()
            .filter(|path| fs.metadata(path).is_ok())
            .cloned()
            .collect();
        let graph = single_project_graph(project)?;
        let node = graph
            .node(project.config_path())
            .expect("single-project graph contains its config");
        if is_project_up_to_date(
            &previous,
            node,
            &current.options,
            &current.sources,
            &options.upstream_signatures,
            &outputs_present,
        ) {
            return Ok(ProjectCompileResult {
                diagnostics: Vec::new(),
                sources,
                outputs: BuildOutputs::default(),
                emitted: false,
                up_to_date: true,
                build_info: Some((path.clone(), previous)),
            });
        }
    }

    let checked = compile_program_frontend_with_lints(
        &program,
        FrontendMode::Check,
        &LintTable::new(LintProfile::Default),
    );
    let mut diagnostics = checked
        .modules()
        .iter()
        .flat_map(|module| module.diagnostics().iter().cloned())
        .collect::<Vec<_>>();
    let pre_emit_errors = diagnostics
        .iter()
        .any(|diagnostic| !diagnostic.is_warning());
    if !should_emit || (project.options().no_emit_on_error() && pre_emit_errors) {
        diagnostics.sort();
        diagnostics.dedup();
        return Ok(ProjectCompileResult {
            diagnostics,
            sources,
            outputs: BuildOutputs::default(),
            emitted: false,
            up_to_date: false,
            build_info: None,
        });
    }

    let plan = output_plan.expect("emitting project has an output plan");
    let mut planned_by_source: BTreeMap<PathBuf, BTreeMap<ArtifactKind, PathBuf>> = BTreeMap::new();
    for artifact in plan.artifacts.values() {
        planned_by_source
            .entry(artifact.source.clone())
            .or_default()
            .insert(artifact.kind, artifact.path.clone());
    }
    let jsx_route = program.jsx_routing_decision(ProgramOutputKind::JavaScript);
    let mut outputs = BuildOutputs::default();
    for module in checked.modules() {
        let source_path = sources
            .iter()
            .find(|source| source.id == module.source_file().source_id())
            .map(|source| source.path.as_path())
            .expect("frontend output retains every resolved module");
        let Some(planned) = planned_by_source.get(source_path) else {
            continue;
        };
        let (mut emit_options, option_diagnostics) =
            emit_options(project.options(), module.source_file().source_id());
        emit_options.declaration = selection.declaration;
        emit_options.emit_declaration_only = selection.declaration && !selection.javascript;
        diagnostics.extend(option_diagnostics);
        match jsx_route {
            JsxRoutingDecision::Emit | JsxRoutingDecision::TransformAndEmit => {
                emit_options.jsx = program.jsx();
                emit_options.jsx_factory = program.jsx_factory().map(Arc::from);
                emit_options.jsx_fragment_factory = program.jsx_fragment_factory().map(Arc::from);
                emit_options.jsx_import_source = program.jsx_import_source().map(Arc::from);
            }
            JsxRoutingDecision::Lower | JsxRoutingDecision::RejectPreservedNative => {
                unreachable!("JavaScript output never selects a native JSX route");
            }
        }
        let names = source_map_names(source_path, planned, &plan, project.options());
        let emitted = emitter::emit_checked(
            module.source_file(),
            module.semantic_model(),
            &emit_options,
            &names,
        );
        diagnostics.extend(emitted.diagnostics.iter().cloned());
        for (kind, path) in planned {
            let bytes = match kind {
                ArtifactKind::JavaScript => emitted
                    .javascript
                    .as_ref()
                    .map(|file| file.code.as_bytes().to_vec()),
                ArtifactKind::Declaration => emitted
                    .declaration
                    .as_ref()
                    .map(|file| file.code.as_bytes().to_vec()),
                ArtifactKind::SourceMap => emitted
                    .javascript
                    .as_ref()
                    .and_then(|file| file.source_map.as_ref())
                    .map(|map| map.to_json().into_bytes()),
                ArtifactKind::DeclarationMap => emitted
                    .declaration
                    .as_ref()
                    .and_then(|file| file.source_map.as_ref())
                    .map(|map| map.to_json().into_bytes()),
            };
            if let Some(bytes) = bytes {
                outputs.files.insert(path.clone(), bytes);
            }
        }
    }
    diagnostics.sort();
    diagnostics.dedup();
    if project.options().no_emit_on_error()
        && diagnostics
            .iter()
            .any(|diagnostic| !diagnostic.is_warning())
    {
        outputs.files.clear();
    }
    let emitted = !outputs.files.is_empty();
    Ok(ProjectCompileResult {
        diagnostics,
        sources,
        outputs,
        emitted,
        up_to_date: false,
        build_info: emitted.then_some(build_state).flatten(),
    })
}

/// One surface's source-map naming computed at the emitter boundary.
struct SurfaceMapNames {
    source_name: Option<Arc<str>>,
    source_map_url: Option<Arc<str>>,
}

/// Joins `segments` onto `base` with one separating slash, trimming both edges.
fn join_url_segments(base: &str, suffix: &str) -> String {
    let trimmed_base = base.trim_end_matches('/');
    let trimmed_suffix = suffix.trim_start_matches('/');
    let mut joined = String::with_capacity(trimmed_base.len() + trimmed_suffix.len() + 1);
    joined.push_str(trimmed_base);
    joined.push('/');
    joined.push_str(trimmed_suffix);
    joined
}

/// Returns true when `value` looks like a scheme-qualified URL rather than a path.
fn is_url_like(value: &str) -> bool {
    if let Some((scheme, rest)) = value.split_once(':') {
        return scheme.len() >= 2
            && scheme
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'-' | b'.'))
            && scheme
                .bytes()
                .next()
                .is_some_and(|byte| byte.is_ascii_alphabetic())
            && (rest.starts_with("//") || scheme.eq_ignore_ascii_case("file"));
    }
    false
}

/// Computes the map `sources` entry and `sourceMappingURL` for one output surface.
///
/// * Without `sourceRoot`, `sources` carries the lexical path from the physical
///   map file's directory back to the original source.
/// * With any `sourceRoot`, `sources` is relative to the common source base and
///   the raw normalized `sourceRoot` rides in the map JSON.
/// * `mapRoot` only rewrites `sourceMappingURL`. Relative roots resolve from the
///   common source base (rootDir when configured, else the derived common
///   directory); absolute and URL roots keep their identity.
fn surface_map_names(
    source_path: &Path,
    output_path: &Path,
    map_path: &Path,
    map_root: Option<&str>,
    source_root: Option<&str>,
    common_source_dir: &Path,
    has_explicit_source_root: bool,
) -> SurfaceMapNames {
    // Keep the source-relative directory, but take the complete output file
    // name verbatim so dotted source basenames do not duplicate suffixes.
    let output_name = output_path.file_name().unwrap_or_default();
    let mut output_relative = match source_path.strip_prefix(common_source_dir) {
        Ok(relative) => relative.to_path_buf(),
        Err(_) => PathBuf::from(output_name),
    };
    output_relative.set_file_name(output_name);
    // The map `sources` entry keeps the original source path relative to the
    // common source base, independent of the emitted surface.
    let source_relative = match source_path.strip_prefix(common_source_dir) {
        Ok(relative) => relative.to_path_buf(),
        Err(_) => source_path
            .file_name()
            .map(PathBuf::from)
            .unwrap_or_default(),
    };

    // With any explicit sourceRoot the map `sources` entry is the source path
    // relative to the common source base; without one it is the path from the
    // map directory back to the original source.
    let source_name = match source_root {
        Some(root) if has_explicit_source_root && !root.is_empty() => {
            Some(Arc::<str>::from(source_relative.to_string_lossy().as_ref()))
        }
        _ => {
            let map_directory = map_path.parent().unwrap_or_else(|| Path::new(""));
            let relative_to_map = relative_path_between(map_directory, source_path);
            Some(Arc::<str>::from(relative_to_map.to_string_lossy().as_ref()))
        }
    };

    let source_map_url = map_root.map(|root| {
        let source_relative_identity = format!("{}.map", output_relative.to_string_lossy());
        if is_url_like(root) || root.starts_with('/') {
            Arc::<str>::from(join_url_segments(root, &source_relative_identity))
        } else {
            let base = common_source_dir.join(root);
            let output_directory = output_path.parent().unwrap_or_else(|| Path::new(""));
            let url =
                relative_path_between(output_directory, &base.join(&source_relative_identity));
            Arc::<str>::from(url.to_string_lossy().as_ref())
        }
    });

    SurfaceMapNames {
        source_name,
        source_map_url,
    }
}

/// Lexical relative path from `from` to `to`, using `..` segments when needed.
fn relative_path_between(from: &Path, to: &Path) -> PathBuf {
    let from = super::output::normalize_lexically(from)
        .expect("generated source-map base path is lexically valid");
    let to = super::output::normalize_lexically(to)
        .expect("generated source-map target path is lexically valid");
    let mut from_components = from
        .components()
        .filter(|component| matches!(component, std::path::Component::Normal(_)))
        .peekable();
    let mut to_components = to
        .components()
        .filter(|component| matches!(component, std::path::Component::Normal(_)))
        .peekable();
    let mut relative = PathBuf::new();
    while from_components.peek().is_some() && from_components.peek() == to_components.peek() {
        from_components.next();
        to_components.next();
    }
    for _ in from_components {
        relative.push("..");
    }
    for component in to_components {
        relative.push(component.as_os_str());
    }
    if relative.as_os_str().is_empty() {
        relative.push(".");
    }
    relative
}

/// Builds the per-surface `EmitFileNames` for one planned source.
fn source_map_names(
    source_path: &Path,
    planned: &BTreeMap<ArtifactKind, PathBuf>,
    plan: &super::super::project::output::OutputPlan,
    options: &CompilerOptions,
) -> EmitFileNames {
    let javascript = planned.get(&ArtifactKind::JavaScript);
    let declaration = planned.get(&ArtifactKind::Declaration);
    let js_map = planned.get(&ArtifactKind::SourceMap).cloned().or_else(|| {
        options.inline_source_map().then(|| {
            let mut path = javascript
                .expect("inline source map has JavaScript")
                .as_os_str()
                .to_os_string();
            path.push(".map");
            PathBuf::from(path)
        })
    });
    let declaration_map = planned.get(&ArtifactKind::DeclarationMap);
    let map_root = options.map_root().filter(|root| !root.is_empty());
    let source_root = options.source_root();
    let has_explicit_source_root = source_root.is_some_and(|root| !root.is_empty());

    let js_surface = js_map
        .as_ref()
        .zip(javascript)
        .map(|(map_path, js_path)| {
            surface_map_names(
                source_path,
                js_path,
                map_path,
                map_root,
                source_root,
                &plan.common_source_dir,
                has_explicit_source_root,
            )
        })
        .unwrap_or(SurfaceMapNames {
            source_name: None,
            source_map_url: None,
        });
    let declaration_surface = declaration_map
        .zip(declaration)
        .map(|(map_path, declaration_path)| {
            surface_map_names(
                source_path,
                declaration_path,
                map_path,
                map_root,
                source_root,
                &plan.common_source_dir,
                has_explicit_source_root,
            )
        })
        .unwrap_or(SurfaceMapNames {
            source_name: None,
            source_map_url: None,
        });

    EmitFileNames {
        source_name: path_to_arc(source_path),
        js_file_name: javascript
            .and_then(|path| path.file_name())
            .map(|name| Arc::from(name.to_string_lossy().as_ref())),
        declaration_file_name: declaration
            .and_then(|path| path.file_name())
            .map(|name| Arc::from(name.to_string_lossy().as_ref())),
        source_root: source_root.map(Arc::from),
        js_source_name: js_surface.source_name,
        js_source_map_url: js_surface.source_map_url,
        declaration_source_name: declaration_surface.source_name,
        declaration_source_map_url: declaration_surface.source_map_url,
    }
}

fn emit_options(options: &CompilerOptions, source_id: SourceId) -> (EmitOptions, Vec<Diagnostic>) {
    // All fields go through the directive parser so invalid-value diagnostics
    // are produced exactly as before. The shared fields (target, always_strict,
    // module) are then re-applied through `apply_emit_fields` — the single
    // mapping point the project (CLI) and program (lane) paths share — so the
    // two paths cannot diverge on downleveling or the strict-mode prologue.
    let mut directives = BTreeMap::new();
    for (name, value) in [
        ("target", options.target()),
        ("module", options.module()),
        ("jsx", options.jsx().map(JsxEmit::as_str)),
        ("newLine", options.new_line()),
    ] {
        if let Some(value) = value {
            directives.insert(name.to_owned(), value.to_owned());
        }
    }
    for (name, enabled) in [
        ("sourceMap", options.source_map()),
        ("inlineSourceMap", options.inline_source_map()),
        ("declarationMap", options.declaration_map()),
        ("inlineSources", options.inline_sources()),
        ("alwaysStrict", options.always_strict()),
        ("noEmitHelpers", options.no_emit_helpers()),
    ] {
        if enabled {
            directives.insert(name.to_owned(), String::from("true"));
        }
    }
    let (mut emit_options, diagnostics) = EmitOptions::from_directives(&directives, source_id);

    // Re-apply the shared fields through the single mapping point.
    let target = options
        .target()
        .and_then(emitter::parse_target)
        .unwrap_or(emitter::ScriptTarget::EsNext);
    let always_strict = options.always_strict();
    let module = options.module().and_then(emitter::parse_module);
    emit_options.apply_emit_fields(
        target,
        always_strict,
        module,
        options.use_define_for_class_fields(),
        options.import_helpers(),
    );

    (emit_options, diagnostics)
}

fn single_project_graph(project: &EffectiveProject) -> Result<ReferenceGraph, ProjectCompileError> {
    ReferenceGraph::from_tsconfigs(project.root(), &[project.config()])
        .map_err(|error| ProjectCompileError::Reference(Arc::from([error])))
}

fn build_state(
    project: &EffectiveProject,
    program: &crate::program::ResolvedProgram,
    output_plan: Option<&super::output::OutputPlan>,
    options: &ProjectCompileOptions,
) -> Result<Option<(PathBuf, BuildInfo)>, ProjectCompileError> {
    let Some(path) = project.build_info_path() else {
        return Ok(None);
    };
    let graph = single_project_graph(project)?;
    let node = graph
        .node(project.config_path())
        .expect("single-project graph contains its config");
    let option_signature = options_signature(project.config().config());
    let sources = program
        .modules()
        .iter()
        .map(|module| {
            (
                module.path().to_path_buf(),
                source_signature(module.source().as_str()),
            )
        })
        .collect();
    let outputs = output_plan
        .map(|plan| plan.artifacts.keys().cloned().collect())
        .unwrap_or_default();
    let signature = project_signature(
        node,
        &option_signature,
        &sources,
        &options.upstream_signatures,
    );
    Ok(Some((
        path.to_path_buf(),
        BuildInfo {
            version: Arc::from(BUILD_INFO_SCHEMA),
            options: option_signature,
            sources,
            outputs,
            signature,
        },
    )))
}

/// Controls deterministic project-reference traversal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProjectBuildOptions {
    pub force: bool,
    pub stop_on_error: bool,
}

impl Default for ProjectBuildOptions {
    fn default() -> Self {
        Self {
            force: false,
            stop_on_error: true,
        }
    }
}

/// One dependency-first project result in a build report.
#[derive(Clone, Debug)]
pub struct ProjectBuildEntry {
    pub config_path: PathBuf,
    pub result: ProjectCompileResult,
}

/// Canonical reference-build report.
#[derive(Clone, Debug, Default)]
pub struct ProjectBuildReport {
    pub projects: Vec<ProjectBuildEntry>,
    pub blocked: Arc<[PathBuf]>,
}

/// Compiles a reference closure in deterministic dependency-first order.
pub fn compile_project_references<F: FileSystem + Clone>(
    root: &ProjectRoot,
    initial_config_paths: &[PathBuf],
    cwd: &Path,
    options: ProjectBuildOptions,
    fs: &F,
) -> Result<ProjectBuildReport, ProjectCompileError> {
    let (_, graph) = load_reference_closure(root, initial_config_paths, fs)?;
    let order = graph
        .topological_order()
        .map_err(|error| ProjectCompileError::Reference(Arc::from([error])))?;
    let mut signatures = BTreeMap::new();
    let mut projects = Vec::new();
    let mut blocked = Vec::new();
    let mut failed = false;
    for config_path in order {
        if failed && options.stop_on_error {
            blocked.push(config_path);
            continue;
        }
        let project = EffectiveProject::load(
            &ProjectLoadRequest {
                config_path: Some(config_path.clone()),
                cwd: cwd.to_path_buf(),
                overrides: ProjectOptionOverrides::default(),
                allow_missing_config: false,
                source_files: None,
            },
            fs,
        )?;
        let upstream_signatures = graph
            .node(&config_path)
            .into_iter()
            .flat_map(|node| node.references.iter())
            .filter_map(|reference| {
                signatures
                    .get(reference.path())
                    .cloned()
                    .map(|signature| (reference.path().to_path_buf(), signature))
            })
            .collect();
        let result = compile_project(
            &project,
            &ProjectCompileOptions {
                emit: true,
                force: options.force,
                upstream_signatures,
            },
            fs,
        )?;
        failed = result
            .diagnostics
            .iter()
            .any(|diagnostic| !diagnostic.is_warning());
        if let Some((_, info)) = &result.build_info {
            signatures.insert(config_path.clone(), Arc::clone(&info.signature));
        }
        projects.push(ProjectBuildEntry {
            config_path,
            result,
        });
    }
    Ok(ProjectBuildReport {
        projects,
        blocked: blocked.into(),
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MaterializeError {
    FilesListEmpty {
        config_path: PathBuf,
    },
    NoInputs {
        config_path: PathBuf,
        include: Arc<[Arc<str>]>,
        exclude: Arc<[Arc<str>]>,
    },
    MissingFiles {
        config_path: PathBuf,
        paths: Arc<[PathBuf]>,
    },
    Path(PathError),
    FileSystem(FileSystemError),
}

impl fmt::Display for MaterializeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FilesListEmpty { config_path } => write!(
                formatter,
                "TS18002: The 'files' list in config file '{}' is empty.",
                config_path.display()
            ),
            Self::NoInputs {
                config_path,
                include,
                exclude,
            } => write!(
                formatter,
                "TS18003: No inputs were found in config file '{}'. Specified 'include' paths were '{:?}' and 'exclude' paths were '{:?}'.",
                config_path.display(),
                include,
                exclude
            ),
            Self::MissingFiles { config_path, paths } => write!(
                formatter,
                "config file '{}' names missing input files: {}",
                config_path.display(),
                paths
                    .iter()
                    .map(|path| path.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Path(error) => error.fmt(formatter),
            Self::FileSystem(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for MaterializeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProjectCompileError {
    ConfigNotFound { path: PathBuf },
    Config(TsConfigError),
    Materialize(MaterializeError),
    Reference(Arc<[ReferenceError]>),
    Load(Arc<str>),
    Output(OutputMapError),
    UnsupportedOption { option: &'static str },
    Path(PathError),
    FileSystem(FileSystemError),
}

impl fmt::Display for ProjectCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ConfigNotFound { path } => {
                write!(formatter, "project config not found: {}", path.display())
            }
            Self::Config(error) => error.fmt(formatter),
            Self::Materialize(error) => error.fmt(formatter),
            Self::Reference(errors) => {
                for (index, error) in errors.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str("; ")?;
                    }
                    error.fmt(formatter)?;
                }
                Ok(())
            }
            Self::Load(message) => formatter.write_str(message),
            Self::Output(error) => error.fmt(formatter),
            Self::UnsupportedOption { option } => {
                write!(
                    formatter,
                    "compiler option '{option}' is unsupported for project compilation"
                )
            }
            Self::Path(error) => error.fmt(formatter),
            Self::FileSystem(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ProjectCompileError {}

impl From<MaterializeError> for ProjectCompileError {
    fn from(error: MaterializeError) -> Self {
        Self::Materialize(error)
    }
}

#[derive(Default)]
struct DiagnosticPatterns {
    include: Option<PatternSource>,
    exclude: Option<PatternSource>,
}

struct PatternSource {
    directory: PathBuf,
    values: Arc<[Arc<str>]>,
}

impl DiagnosticPatterns {
    fn capture(&mut self, raw: &JsonObject, config_path: &Path) {
        let Some(directory) = config_path.parent() else {
            return;
        };
        if let Some(values) = raw_pattern_list(raw, "include") {
            self.include = Some(PatternSource {
                directory: directory.to_path_buf(),
                values,
            });
        }
        if let Some(values) = raw_pattern_list(raw, "exclude") {
            self.exclude = Some(PatternSource {
                directory: directory.to_path_buf(),
                values,
            });
        }
    }
}

fn raw_pattern_list(raw: &JsonObject, name: &str) -> Option<Arc<[Arc<str>]>> {
    raw.get(name).and_then(JsonValue::as_array).map(|values| {
        Arc::from(
            values
                .iter()
                .filter_map(JsonValue::as_str)
                .map(Arc::<str>::from)
                .collect::<Vec<_>>(),
        )
    })
}

fn load_merged_raw(
    root: &ProjectRoot,
    config_path: &Path,
    source: &str,
    fs: &dyn FileSystem,
) -> Result<(JsonObject, DiagnosticPatterns), ProjectCompileError> {
    let chain = resolve_extends(
        root,
        config_path,
        source,
        &|path| fs.read(path).ok().map(Arc::from),
        128,
    )
    .map_err(ProjectCompileError::Config)?;
    let derived = parse_object(source).map_err(ProjectCompileError::Config)?;
    merge_config_layers(root, &chain, config_path, &derived)
}

fn parse_object(source: &str) -> Result<JsonObject, TsConfigError> {
    let value = super::parse_jsonc(source).map_err(TsConfigError::from)?;
    value
        .as_object()
        .cloned()
        .ok_or_else(|| super::tsconfig::TsConfigDiagnostic::RootNotObject.into())
}

fn merge_config_layers(
    root: &ProjectRoot,
    chain: &[ResolvedExtends],
    derived_path: &Path,
    derived_raw: &JsonObject,
) -> Result<(JsonObject, DiagnosticPatterns), ProjectCompileError> {
    let mut merged = JsonObject::from_entries(Vec::new());
    let mut patterns = DiagnosticPatterns::default();
    for layer in chain.iter().rev() {
        let raw = parse_object(layer.source()).map_err(ProjectCompileError::Config)?;
        patterns.capture(&raw, layer.path());
        let rewritten = rewrite_layer_paths(root, layer.path(), &raw, &merged)?;
        merged = merge_objects(&merged, &rewritten);
    }
    patterns.capture(derived_raw, derived_path);
    let rewritten = rewrite_layer_paths(root, derived_path, derived_raw, &merged)?;
    Ok((merge_objects(&merged, &rewritten), patterns))
}

fn merge_objects(base: &JsonObject, derived: &JsonObject) -> JsonObject {
    let mut entries = base.entries().to_vec();
    for (key, value) in derived.entries() {
        let value = if key.as_ref() == "compilerOptions" {
            match (
                entries
                    .iter()
                    .find(|(candidate, _)| candidate.as_ref() == key.as_ref())
                    .and_then(|(_, value)| value.as_object()),
                value.as_object(),
            ) {
                (Some(base), Some(derived)) => JsonValue::Object(merge_objects(base, derived)),
                _ => value.clone(),
            }
        } else {
            value.clone()
        };
        set_entry(&mut entries, key, value);
    }
    JsonObject::from_entries(entries)
}

fn rewrite_layer_paths(
    root: &ProjectRoot,
    config_path: &Path,
    raw: &JsonObject,
    inherited: &JsonObject,
) -> Result<JsonObject, ProjectCompileError> {
    let directory = config_path.parent().ok_or_else(|| {
        ProjectCompileError::Path(PathError::PathHasNoParent {
            path: config_path.to_path_buf(),
        })
    })?;
    let mut entries = raw.entries().to_vec();
    for field in ["files", "include", "exclude"] {
        if let Some(value) = raw.get(field) {
            set_named_entry(
                &mut entries,
                field,
                rewrite_string_array(root, directory, value)?,
            );
        }
    }
    if let Some(value) = raw.get("references") {
        set_named_entry(
            &mut entries,
            "references",
            rewrite_references(root, directory, value)?,
        );
    }
    if let Some(compiler) = raw.get("compilerOptions").and_then(JsonValue::as_object) {
        let inherited_compiler = inherited
            .get("compilerOptions")
            .and_then(JsonValue::as_object);
        let rewritten = rewrite_compiler_paths(root, directory, compiler, inherited_compiler)?;
        set_named_entry(
            &mut entries,
            "compilerOptions",
            JsonValue::Object(rewritten),
        );
    }
    Ok(JsonObject::from_entries(entries))
}

fn rewrite_compiler_paths(
    root: &ProjectRoot,
    directory: &Path,
    compiler: &JsonObject,
    inherited: Option<&JsonObject>,
) -> Result<JsonObject, ProjectCompileError> {
    let mut entries = compiler.entries().to_vec();
    let inherited_base = inherited
        .and_then(|object| object.get("baseUrl"))
        .and_then(JsonValue::as_str)
        .map(PathBuf::from);
    let base_url = match compiler.get("baseUrl") {
        Some(value) => {
            let value = value
                .as_str()
                .ok_or_else(|| invalid_config_field("baseUrl"))?;
            root.resolve_from(directory, value)
                .map_err(ProjectCompileError::Path)?
        }
        None => inherited_base.unwrap_or_else(|| directory.to_path_buf()),
    };
    for field in [
        "baseUrl",
        "rootDir",
        "outDir",
        "declarationDir",
        "outFile",
        "tsBuildInfoFile",
    ] {
        if let Some(value) = compiler.get(field) {
            set_named_entry(
                &mut entries,
                field,
                rewrite_path_value(root, directory, value, field)?,
            );
        }
    }
    for field in ["mapRoot", "sourceRoot"] {
        if let Some(value) = compiler.get(field) {
            let value = value.as_str().ok_or_else(|| invalid_config_field(field))?;
            set_named_entry(&mut entries, field, JsonValue::String(Arc::from(value)));
        }
    }
    if let Some(value) = compiler.get("typeRoots") {
        set_named_entry(
            &mut entries,
            "typeRoots",
            rewrite_string_array(root, directory, value)?,
        );
    }
    if let Some(value) = compiler.get("paths") {
        let mappings = value
            .as_object()
            .ok_or_else(|| invalid_config_field("paths"))?;
        let mut rewritten = Vec::with_capacity(mappings.entries().len());
        for (pattern, targets) in mappings.entries() {
            rewritten.push((
                Arc::clone(pattern),
                rewrite_string_array(root, &base_url, targets)?,
            ));
        }
        set_named_entry(
            &mut entries,
            "paths",
            JsonValue::Object(JsonObject::from_entries(rewritten)),
        );
    }
    Ok(JsonObject::from_entries(entries))
}

fn invalid_config_field(field: &'static str) -> ProjectCompileError {
    ProjectCompileError::Config(
        super::ConfigError::InvalidField {
            field: Arc::from(field),
            expected: "a path string",
        }
        .into(),
    )
}

fn rewrite_path_value(
    root: &ProjectRoot,
    directory: &Path,
    value: &JsonValue,
    field: &'static str,
) -> Result<JsonValue, ProjectCompileError> {
    let value = value.as_str().ok_or_else(|| invalid_config_field(field))?;
    let path = root
        .resolve_from(directory, value)
        .map_err(ProjectCompileError::Path)?;
    Ok(JsonValue::String(path_to_arc(&path)))
}

fn rewrite_string_array(
    root: &ProjectRoot,
    directory: &Path,
    value: &JsonValue,
) -> Result<JsonValue, ProjectCompileError> {
    let values = value
        .as_array()
        .ok_or_else(|| invalid_config_field("path list"))?;
    let mut rewritten = Vec::with_capacity(values.len());
    for value in values {
        let value = value
            .as_str()
            .ok_or_else(|| invalid_config_field("path list"))?;
        let path = root
            .resolve_from(directory, value)
            .map_err(ProjectCompileError::Path)?;
        rewritten.push(JsonValue::String(path_to_arc(&path)));
    }
    Ok(JsonValue::Array(Arc::from(rewritten)))
}

fn rewrite_references(
    root: &ProjectRoot,
    directory: &Path,
    value: &JsonValue,
) -> Result<JsonValue, ProjectCompileError> {
    let references = value
        .as_array()
        .ok_or_else(|| invalid_config_field("references"))?;
    let mut rewritten = Vec::with_capacity(references.len());
    for reference in references {
        let object = reference
            .as_object()
            .ok_or_else(|| invalid_config_field("references"))?;
        let mut entries = object.entries().to_vec();
        if let Some(path) = object.get("path") {
            set_named_entry(
                &mut entries,
                "path",
                rewrite_path_value(root, directory, path, "references.path")?,
            );
        }
        rewritten.push(JsonValue::Object(JsonObject::from_entries(entries)));
    }
    Ok(JsonValue::Array(Arc::from(rewritten)))
}

fn apply_overrides(
    root: &ProjectRoot,
    cwd: &Path,
    raw: JsonObject,
    overrides: &ProjectOptionOverrides,
) -> Result<JsonObject, ProjectCompileError> {
    let mut top = raw.entries().to_vec();
    let mut compiler = raw
        .get("compilerOptions")
        .and_then(JsonValue::as_object)
        .map_or_else(Vec::new, |object| object.entries().to_vec());
    for (key, value) in [
        ("noEmit", overrides.no_emit),
        ("noEmitOnError", overrides.no_emit_on_error),
        ("declaration", overrides.declaration),
        ("declarationMap", overrides.declaration_map),
        ("sourceMap", overrides.source_map),
        ("inlineSourceMap", overrides.inline_source_map),
        ("inlineSources", overrides.inline_sources),
        ("strict", overrides.strict),
        ("noImplicitAny", overrides.no_implicit_any),
        ("strictNullChecks", overrides.strict_null_checks),
        (
            "strictPropertyInitialization",
            overrides.strict_property_initialization,
        ),
        ("allowJs", overrides.allow_js),
        ("checkJs", overrides.check_js),
        ("alwaysStrict", overrides.always_strict),
        ("emitDeclarationOnly", overrides.emit_declaration_only),
        ("incremental", overrides.incremental),
        ("composite", overrides.composite),
        ("esModuleInterop", overrides.es_module_interop),
        ("isolatedModules", overrides.isolated_modules),
        ("verbatimModuleSyntax", overrides.verbatim_module_syntax),
        ("traceResolution", overrides.trace_resolution),
        ("resolveJsonModule", overrides.resolve_json_module),
    ] {
        if let Some(value) = value {
            set_named_entry(&mut compiler, key, JsonValue::Bool(value));
        }
    }
    for (key, value) in [
        ("outDir", overrides.out_dir.as_deref()),
        ("rootDir", overrides.root_dir.as_deref()),
        ("outFile", overrides.out_file.as_deref()),
        ("tsBuildInfoFile", overrides.ts_build_info_file.as_deref()),
        ("declarationDir", overrides.declaration_dir.as_deref()),
        ("baseUrl", overrides.base_url.as_deref()),
    ] {
        if let Some(value) = value {
            let value = root
                .resolve_from(cwd, value)
                .map_err(ProjectCompileError::Path)?;
            set_named_entry(&mut compiler, key, JsonValue::String(path_to_arc(&value)));
        }
    }
    for (key, value) in [
        ("mapRoot", overrides.map_root.as_deref()),
        ("sourceRoot", overrides.source_root.as_deref()),
        ("jsx", overrides.jsx.as_deref()),
        ("target", overrides.target.as_deref()),
        ("module", overrides.module.as_deref()),
        ("moduleResolution", overrides.module_resolution.as_deref()),
        ("moduleDetection", overrides.module_detection.as_deref()),
        ("newLine", overrides.new_line.as_deref()),
        ("jsxFactory", overrides.jsx_factory.as_deref()),
        (
            "jsxFragmentFactory",
            overrides.jsx_fragment_factory.as_deref(),
        ),
        ("jsxImportSource", overrides.jsx_import_source.as_deref()),
    ] {
        if let Some(value) = value {
            set_named_entry(&mut compiler, key, JsonValue::String(Arc::from(value)));
        }
    }
    if let Some(lib) = &overrides.lib {
        let entries: Vec<JsonValue> = lib
            .iter()
            .map(|item| JsonValue::String(Arc::from(item.as_str())))
            .collect();
        set_named_entry(&mut compiler, "lib", JsonValue::Array(Arc::from(entries)));
    }
    if !compiler.is_empty() {
        set_named_entry(
            &mut top,
            "compilerOptions",
            JsonValue::Object(JsonObject::from_entries(compiler)),
        );
    }
    Ok(JsonObject::from_entries(top))
}

fn normalize_composite_options(raw: JsonObject) -> JsonObject {
    let Some(options) = raw.get("compilerOptions").and_then(JsonValue::as_object) else {
        return raw;
    };
    if options.get("composite").and_then(JsonValue::as_bool) != Some(true) {
        return raw;
    }
    let mut compiler = options.entries().to_vec();
    for key in ["declaration", "incremental"] {
        if options.get(key).is_none() {
            set_named_entry(&mut compiler, key, JsonValue::Bool(true));
        }
    }
    let mut top = raw.entries().to_vec();
    set_named_entry(
        &mut top,
        "compilerOptions",
        JsonValue::Object(JsonObject::from_entries(compiler)),
    );
    JsonObject::from_entries(top)
}

fn set_entry(entries: &mut Vec<(Arc<str>, JsonValue)>, key: &Arc<str>, value: JsonValue) {
    if let Some((_, current)) = entries
        .iter_mut()
        .find(|(candidate, _)| candidate.as_ref() == key.as_ref())
    {
        *current = value;
    } else {
        entries.push((Arc::clone(key), value));
    }
}

fn set_named_entry(entries: &mut Vec<(Arc<str>, JsonValue)>, key: &'static str, value: JsonValue) {
    let key = Arc::<str>::from(key);
    set_entry(entries, &key, value);
}

fn path_to_arc(path: &Path) -> Arc<str> {
    Arc::from(path.to_string_lossy().as_ref())
}

fn materialize_explicit_sources(
    root: &ProjectRoot,
    paths: &[PathBuf],
) -> Result<Arc<[PathBuf]>, MaterializeError> {
    let mut sources = BTreeSet::new();
    for path in paths {
        let path = root.resolve(path).map_err(MaterializeError::Path)?;
        sources.insert(path);
    }
    Ok(sources.into_iter().collect::<Vec<_>>().into())
}

fn materialize_sources(
    root: &ProjectRoot,
    config: &TsConfig,
    diagnostic_patterns: &DiagnosticPatterns,
    fs: &dyn FileSystem,
) -> Result<Arc<[PathBuf]>, MaterializeError> {
    let project = config.config();
    let raw = project.raw();
    if raw
        .get("files")
        .and_then(JsonValue::as_array)
        .is_some_and(<[JsonValue]>::is_empty)
    {
        return Err(MaterializeError::FilesListEmpty {
            config_path: project.path().to_path_buf(),
        });
    }

    let mut sources = BTreeSet::new();
    let mut missing = BTreeSet::new();
    for path in project.files() {
        match fs.metadata(path) {
            Ok(_) => {
                let path = fs.normalize(path).map_err(MaterializeError::FileSystem)?;
                sources.insert(root.confine(path).map_err(MaterializeError::Path)?);
            }
            Err(error) if error.kind() == ErrorKind::NotFound => {
                missing.insert(path.clone());
            }
            Err(error) => return Err(MaterializeError::FileSystem(error)),
        }
    }
    if !missing.is_empty() {
        return Err(MaterializeError::MissingFiles {
            config_path: project.path().to_path_buf(),
            paths: Arc::from(missing.into_iter().collect::<Vec<_>>()),
        });
    }

    let directory = project.path().parent().ok_or_else(|| {
        MaterializeError::Path(PathError::PathHasNoParent {
            path: project.path().to_path_buf(),
        })
    })?;
    let render_patterns = |source: &PatternSource| {
        Arc::from(
            source
                .values
                .iter()
                .map(|value| {
                    let value_path = Path::new(value.as_ref());
                    if value_path.is_absolute() {
                        return Arc::clone(value);
                    }
                    Arc::<str>::from(
                        relative_path_between(directory, &source.directory.join(value_path))
                            .to_string_lossy()
                            .as_ref(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let diagnostic_include = diagnostic_patterns
        .include
        .as_ref()
        .map(&render_patterns)
        .unwrap_or_else(|| {
            if raw.get("files").is_none() {
                Arc::from([Arc::<str>::from("**/*")])
            } else {
                Arc::from([])
            }
        });
    let diagnostic_exclude = diagnostic_patterns
        .exclude
        .as_ref()
        .map(render_patterns)
        .unwrap_or_else(|| Arc::from([]));
    let include: Arc<[Arc<str>]> = if raw.get("include").is_none() && raw.get("files").is_none() {
        Arc::from([Arc::<str>::from(
            directory.join("**/*").to_string_lossy().as_ref(),
        )])
    } else {
        Arc::from(project.include())
    };
    let mut exclude: Vec<Arc<str>> = if raw.get("exclude").is_none() {
        ["node_modules", "bower_components", "jspm_packages"]
            .into_iter()
            .map(|name| Arc::from(directory.join(name).join("**/*").to_string_lossy().as_ref()))
            .collect()
    } else {
        project.exclude().to_vec()
    };
    for pattern in &mut exclude {
        if contains_wildcard(pattern) {
            continue;
        }
        match fs.read_dir(Path::new(pattern.as_ref())) {
            Ok(_) => {
                *pattern = Arc::from(
                    Path::new(pattern.as_ref())
                        .join("**/*")
                        .to_string_lossy()
                        .as_ref(),
                );
            }
            Err(error)
                if matches!(error.kind(), ErrorKind::NotFound | ErrorKind::NotADirectory) => {}
            Err(error) => return Err(MaterializeError::FileSystem(error)),
        }
    }
    if let Some(out_dir) = project.options().out_dir() {
        exclude.push(Arc::from(out_dir.join("**/*").to_string_lossy().as_ref()));
    }

    for pattern in include.iter() {
        expand_include(
            root,
            pattern.as_ref(),
            &exclude,
            project.options().allow_js(),
            fs,
            &mut sources,
        )?;
    }
    if sources.is_empty() {
        return Err(MaterializeError::NoInputs {
            config_path: project.path().to_path_buf(),
            include: diagnostic_include,
            exclude: diagnostic_exclude,
        });
    }
    Ok(Arc::from(sources.into_iter().collect::<Vec<_>>()))
}

fn expand_include(
    root: &ProjectRoot,
    pattern: &str,
    exclude: &[Arc<str>],
    allow_js: bool,
    fs: &dyn FileSystem,
    sources: &mut BTreeSet<PathBuf>,
) -> Result<(), MaterializeError> {
    let path = Path::new(pattern);
    if !contains_wildcard(pattern) {
        if supported_extension(path, allow_js) {
            if fs.metadata(path).is_ok() && !excluded(path, exclude) {
                let normalized = fs.normalize(path).map_err(MaterializeError::FileSystem)?;
                sources.insert(root.confine(normalized).map_err(MaterializeError::Path)?);
            }
            return Ok(());
        }
        match fs.read_dir(path) {
            Ok(_) => return walk_directory(root, path, None, exclude, allow_js, fs, sources),
            Err(error)
                if matches!(error.kind(), ErrorKind::NotFound | ErrorKind::NotADirectory) =>
            {
                return Ok(());
            }
            Err(error) => return Err(MaterializeError::FileSystem(error)),
        }
    }

    let prefix = wildcard_prefix(path);
    match fs.read_dir(&prefix) {
        Ok(_) => walk_directory(root, &prefix, Some(pattern), exclude, allow_js, fs, sources),
        Err(error) if matches!(error.kind(), ErrorKind::NotFound | ErrorKind::NotADirectory) => {
            Ok(())
        }
        Err(error) => Err(MaterializeError::FileSystem(error)),
    }
}

fn walk_directory(
    root: &ProjectRoot,
    directory: &Path,
    pattern: Option<&str>,
    exclude: &[Arc<str>],
    allow_js: bool,
    fs: &dyn FileSystem,
    sources: &mut BTreeSet<PathBuf>,
) -> Result<(), MaterializeError> {
    let mut pending = vec![directory.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let mut entries = fs
            .read_dir(&directory)
            .map_err(MaterializeError::FileSystem)?;
        entries.sort();
        for entry in entries.into_iter().rev() {
            match fs.metadata(&entry) {
                Ok(_) => {
                    if supported_extension(&entry, allow_js)
                        && pattern.is_none_or(|pattern| glob_matches(pattern, &entry))
                        && !excluded(&entry, exclude)
                    {
                        let normalized =
                            fs.normalize(&entry).map_err(MaterializeError::FileSystem)?;
                        sources.insert(root.confine(normalized).map_err(MaterializeError::Path)?);
                    }
                }
                Err(error) if error.kind() == ErrorKind::InvalidInput => {
                    if !excluded_directory(&entry, exclude) {
                        pending.push(entry);
                    }
                }
                Err(error) if error.kind() == ErrorKind::NotFound => {}
                Err(error) => return Err(MaterializeError::FileSystem(error)),
            }
        }
    }
    Ok(())
}

fn contains_wildcard(pattern: &str) -> bool {
    pattern.bytes().any(|byte| matches!(byte, b'*' | b'?'))
}

fn wildcard_prefix(path: &Path) -> PathBuf {
    let mut prefix = PathBuf::new();
    for component in path.components() {
        let text = component.as_os_str().to_string_lossy();
        if contains_wildcard(&text) {
            break;
        }
        prefix.push(component.as_os_str());
    }
    prefix
}

fn supported_extension(path: &Path, allow_js: bool) -> bool {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    let always = [".d.ts", ".d.mts", ".d.cts", ".ts", ".tsx", ".mts", ".cts"];
    always.iter().any(|extension| name.ends_with(extension))
        || (allow_js
            && [".js", ".jsx", ".mjs", ".cjs"]
                .iter()
                .any(|extension| name.ends_with(extension)))
}

fn excluded(path: &Path, patterns: &[Arc<str>]) -> bool {
    patterns.iter().any(|pattern| glob_matches(pattern, path))
}

fn excluded_directory(path: &Path, patterns: &[Arc<str>]) -> bool {
    patterns.iter().any(|pattern| {
        let prefix = wildcard_prefix(Path::new(pattern.as_ref()));
        prefix == path || glob_matches(pattern, path)
    })
}

fn glob_matches(pattern: &str, path: &Path) -> bool {
    let pattern: Vec<String> = Path::new(pattern)
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect();
    let path: Vec<String> = path
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect();
    glob_segments(&pattern, &path)
}

fn glob_segments(pattern: &[String], path: &[String]) -> bool {
    match pattern.split_first() {
        None => path.is_empty(),
        Some((head, tail)) if head == "**" => {
            glob_segments(tail, path)
                || path
                    .split_first()
                    .is_some_and(|(_, rest)| glob_segments(pattern, rest))
        }
        Some((head, tail)) => path.split_first().is_some_and(|(candidate, rest)| {
            segment_matches(head, candidate) && glob_segments(tail, rest)
        }),
    }
}

fn segment_matches(pattern: &str, candidate: &str) -> bool {
    let pattern = pattern.as_bytes();
    let candidate = candidate.as_bytes();
    let mut current = vec![false; candidate.len() + 1];
    current[0] = true;
    for token in pattern {
        let mut next = vec![false; candidate.len() + 1];
        match token {
            b'*' => {
                let mut reachable = false;
                for index in 0..=candidate.len() {
                    reachable |= current[index];
                    next[index] = reachable;
                }
            }
            b'?' => {
                next[1..].copy_from_slice(&current[..candidate.len()]);
            }
            literal => {
                for index in 0..candidate.len() {
                    next[index + 1] = current[index] && candidate[index] == *literal;
                }
            }
        }
        current = next;
    }
    current[candidate.len()]
}

pub fn load_reference_closure(
    root: &ProjectRoot,
    initial_config_paths: &[PathBuf],
    fs: &dyn FileSystem,
) -> Result<(Vec<TsConfig>, ReferenceGraph), ProjectCompileError> {
    let mut queue: VecDeque<PathBuf> = initial_config_paths
        .iter()
        .map(|path| canonical_config_path(root, path, fs))
        .collect::<Result<BTreeSet<_>, _>>()?
        .into_iter()
        .collect();
    let mut configs = BTreeMap::new();
    while let Some(path) = queue.pop_front() {
        if configs.contains_key(&path) {
            continue;
        }
        let source = fs.read(&path).map_err(|error| {
            if error.kind() == ErrorKind::NotFound {
                ProjectCompileError::ConfigNotFound { path: path.clone() }
            } else {
                ProjectCompileError::FileSystem(error)
            }
        })?;
        let (raw, _) = load_merged_raw(root, &path, &source, fs)?;
        let config =
            TsConfig::parse_value(root, &path, raw).map_err(ProjectCompileError::Config)?;
        let mut referenced = BTreeSet::new();
        for reference in config.references() {
            referenced.insert(canonical_config_path(root, reference.path(), fs)?);
        }
        queue.extend(referenced);
        configs.insert(path, config);
    }
    let configs: Vec<TsConfig> = configs.into_values().collect();
    let borrowed: Vec<&TsConfig> = configs.iter().collect();
    let graph = ReferenceGraph::from_tsconfigs(root, &borrowed)
        .map_err(|error| ProjectCompileError::Reference(Arc::from([error])))?;
    let diagnostics = graph.validate();
    if !diagnostics.is_empty() {
        return Err(ProjectCompileError::Reference(Arc::from(diagnostics)));
    }
    graph
        .topological_order()
        .map_err(|error| ProjectCompileError::Reference(Arc::from([error])))?;
    Ok((configs, graph))
}

fn canonical_config_path(
    root: &ProjectRoot,
    path: &Path,
    fs: &dyn FileSystem,
) -> Result<PathBuf, ProjectCompileError> {
    let path = resolve_config_file_name(path.to_path_buf());
    let confined = root.confine(path).map_err(ProjectCompileError::Path)?;
    fs.normalize(&confined)
        .map_err(ProjectCompileError::FileSystem)
}

fn effective_build_info_path(
    root: &ProjectRoot,
    config: &TsConfig,
) -> Result<Option<PathBuf>, ProjectCompileError> {
    let graph = ReferenceGraph::from_tsconfigs(root, &[config])
        .map_err(|error| ProjectCompileError::Reference(Arc::from([error])))?;
    Ok(graph
        .node(config.config().path())
        .and_then(|node| node.build_info_path.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::service::filesystem::OsFileSystem;
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "bamts-effective-{}-{}",
                std::process::id(),
                NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn write(&self, path: &str, source: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, source).unwrap();
        }

        fn filesystem(&self) -> OsFileSystem {
            OsFileSystem::new(&self.0).unwrap()
        }

        fn request(&self, config: &str) -> ProjectLoadRequest {
            ProjectLoadRequest {
                config_path: Some(PathBuf::from(config)),
                cwd: self.0.clone(),
                overrides: ProjectOptionOverrides::default(),
                allow_missing_config: false,
                source_files: None,
            }
        }

        fn direct_request(&self, sources: &[&str]) -> ProjectLoadRequest {
            ProjectLoadRequest {
                config_path: None,
                cwd: self.0.clone(),
                overrides: ProjectOptionOverrides::default(),
                allow_missing_config: true,
                source_files: Some(sources.iter().map(PathBuf::from).collect()),
            }
        }
    }

    #[test]
    fn explicit_source_files_skip_the_config_document() {
        let fixture = Fixture::new();
        fixture.write("root.ts", "export const root = 1;\n");
        fixture.write("extra/extra.ts", "export const extra = 2;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"include":["**/*"],"compilerOptions":{"declaration":true}}"#,
        );
        let filesystem = fixture.filesystem();
        let project = EffectiveProject::load(&fixture.direct_request(&["root.ts"]), &filesystem)
            .expect("inferred project loads");
        assert_eq!(project.source_files(), &[fixture.0.join("root.ts")]);
        assert!(!project.options().declaration());
        assert!(!project.options().source_map());
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).ok();
        }
    }

    #[test]
    fn extends_preserves_path_origins_and_override_precedence() {
        let fixture = Fixture::new();
        fixture.write("base/src/base.ts", "export const base = 1;");
        fixture.write("app/src/base.ts", "export const decoy = 1;");
        fixture.write(
            "base/tsconfig.json",
            r#"{"compilerOptions":{"strict":true},"include":["src/**/*.ts"]}"#,
        );
        fixture.write(
            "app/tsconfig.json",
            r#"{"extends":"../base/tsconfig.json"}"#,
        );
        let fs = fixture.filesystem();
        let inherited = EffectiveProject::load(&fixture.request("app/tsconfig.json"), &fs).unwrap();
        assert!(inherited.options().strict());
        assert_eq!(
            inherited.source_files(),
            &[fixture.0.join("base/src/base.ts")]
        );

        let mut overridden = fixture.request("app/tsconfig.json");
        overridden.overrides.strict = Some(false);
        let overridden = EffectiveProject::load(&overridden, &fs).unwrap();
        assert!(!overridden.options().strict());
    }

    #[test]
    fn strict_family_cli_overrides_reach_effective_options() {
        // The native tsc command line pins the member names (TS showConfig
        // baselines: noImplicitAny 35227919..., strictNullChecks 385f6fd5...,
        // strictPropertyInitialization b3dadd75...): a `--strict` request with
        // explicit member opt-outs must keep those members off.
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export const a = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{}}"#,
        );
        let fs = fixture.filesystem();
        let mut request = fixture.request("tsconfig.json");
        request.overrides.strict = Some(true);
        request.overrides.no_implicit_any = Some(false);
        request.overrides.strict_null_checks = Some(false);
        request.overrides.strict_property_initialization = Some(false);

        let project = EffectiveProject::load(&request, &fs).unwrap();
        assert!(project.options().strict());
        assert!(!project.options().no_implicit_any());
        assert!(!project.options().strict_null_checks());
        assert!(!project.options().strict_property_initialization());
        assert!(
            project.options().always_strict(),
            "alwaysStrict inherits strict"
        );
    }

    #[test]
    fn derived_compiler_options_win_without_erasing_inherited_keys() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export {};\n");
        fixture.write(
            "base.json",
            r#"{"compilerOptions":{"strict":true,"allowJs":true},"include":["src/a.ts"]}"#,
        );
        fixture.write(
            "tsconfig.json",
            r#"{"extends":"./base.json","compilerOptions":{"strict":false}}"#,
        );
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap();
        assert!(!project.options().strict());
        assert!(project.options().allow_js());
    }
    #[test]
    fn composite_normalization_preserves_explicit_false() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export {};\n");
        fixture.write(
            "tsconfig.json",
            r#"{
                "files":["a.ts"],
                "compilerOptions":{
                    "composite":true,
                    "declaration":false,
                    "incremental":false
                }
            }"#,
        );
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap();
        assert!(project.options().composite());
        assert!(!project.options().declaration());
        assert!(!project.options().incremental());
    }

    #[test]
    fn empty_files_reports_ts18002() {
        let fixture = Fixture::new();
        fixture.write("tsconfig.json", r#"{"files":[]}"#);
        let error =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap_err();
        assert!(matches!(
            &error,
            ProjectCompileError::Materialize(MaterializeError::FilesListEmpty { .. })
        ));
        assert!(error.to_string().starts_with("TS18002:"));
    }

    #[test]
    fn empty_expansion_reports_ts18003() {
        let fixture = Fixture::new();
        fixture.write("tsconfig.json", r#"{"include":["missing/**/*.ts"]}"#);
        let error =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap_err();
        assert!(matches!(
            &error,
            ProjectCompileError::Materialize(MaterializeError::NoInputs { .. })
        ));
        assert!(error.to_string().starts_with("TS18003:"));
    }

    #[test]
    fn files_include_exclude_allow_js_and_out_dir_are_deterministic() {
        let fixture = Fixture::new();
        fixture.write("forced/kept.ts", "export {};\n");
        fixture.write("src/a.ts", "export {};\n");
        fixture.write("src/z.js", "export {};\n");
        fixture.write("src/data.json", "{}\n");
        fixture.write("src/excluded/no.ts", "export {};\n");
        fixture.write("src/out/generated.ts", "export {};\n");
        fixture.write(
            "tsconfig.json",
            r#"{
                "files":["forced/kept.ts","forced/kept.ts"],
                "include":["src/**/*"],
                "exclude":["src/excluded","forced"],
                "compilerOptions":{"allowJs":true,"outDir":"src/out"}
            }"#,
        );
        let fs = fixture.filesystem();
        let first = EffectiveProject::load(&fixture.request("tsconfig.json"), &fs).unwrap();
        let second = EffectiveProject::load(&fixture.request("tsconfig.json"), &fs).unwrap();
        let expected = vec![
            fixture.0.join("forced/kept.ts"),
            fixture.0.join("src/a.ts"),
            fixture.0.join("src/z.js"),
        ];
        assert_eq!(first.source_files(), expected);
        assert_eq!(first.source_files(), second.source_files());
    }

    #[test]
    fn default_include_and_excludes_skip_dependency_directories_and_out_dir() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export {};\n");
        fixture.write("ignored.js", "export {};\n");
        fixture.write("node_modules/dep/index.ts", "export {};\n");
        fixture.write("dist/generated.ts", "export {};\n");
        fixture.write("tsconfig.json", r#"{"compilerOptions":{"outDir":"dist"}}"#);
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap();
        assert_eq!(project.source_files(), &[fixture.0.join("a.ts")]);
    }
    #[test]
    fn reference_closure_is_recursive_and_dependency_first() {
        let fixture = Fixture::new();
        fixture.write("app/tsconfig.json", r#"{"references":[{"path":"../lib"}]}"#);
        fixture.write(
            "lib/tsconfig.json",
            r#"{"references":[{"path":"../shared"}]}"#,
        );
        fixture.write("shared/tsconfig.json", "{}");
        let root = ProjectRoot::new(&fixture.0).unwrap();
        let (configs, graph) = load_reference_closure(
            &root,
            &[fixture.0.join("app/tsconfig.json")],
            &fixture.filesystem(),
        )
        .unwrap();
        assert_eq!(configs.len(), 3);
        assert_eq!(
            graph.topological_order().unwrap(),
            vec![
                fixture.0.join("shared/tsconfig.json"),
                fixture.0.join("lib/tsconfig.json"),
                fixture.0.join("app/tsconfig.json"),
            ]
        );
    }

    #[test]
    fn reference_closure_reports_missing_config() {
        let fixture = Fixture::new();
        fixture.write("tsconfig.json", r#"{"references":[{"path":"./missing"}]}"#);
        let root = ProjectRoot::new(&fixture.0).unwrap();
        let error = load_reference_closure(
            &root,
            &[fixture.0.join("tsconfig.json")],
            &fixture.filesystem(),
        )
        .unwrap_err();
        assert!(matches!(error, ProjectCompileError::ConfigNotFound { .. }));
    }

    #[test]
    fn reference_closure_reports_cycle() {
        let fixture = Fixture::new();
        fixture.write(
            "a/tsconfig.json",
            r#"{"compilerOptions":{"composite":true},"references":[{"path":"../b"}]}"#,
        );
        fixture.write(
            "b/tsconfig.json",
            r#"{"compilerOptions":{"composite":true},"references":[{"path":"../a"}]}"#,
        );
        let root = ProjectRoot::new(&fixture.0).unwrap();
        let error = load_reference_closure(
            &root,
            &[fixture.0.join("a/tsconfig.json")],
            &fixture.filesystem(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            ProjectCompileError::Reference(ref errors)
                if errors.iter().any(|error| matches!(error, ReferenceError::Cycle { .. }))
        ));
    }

    #[test]
    fn package_extends_materializes_inherited_sources() {
        let fixture = Fixture::new();
        fixture.write(
            "app/node_modules/preset/tsconfig.json",
            r#"{"compilerOptions":{"strict":true},"files":["src/base.ts"]}"#,
        );
        fixture.write(
            "app/node_modules/preset/src/base.ts",
            "export const base = 1;\n",
        );
        fixture.write("app/tsconfig.json", r#"{"extends":"preset"}"#);

        let project =
            EffectiveProject::load(&fixture.request("app/tsconfig.json"), &fixture.filesystem())
                .unwrap();
        assert!(project.options().strict());
        assert_eq!(
            project.source_files(),
            &[fixture.0.join("app/node_modules/preset/src/base.ts")]
        );
    }

    #[test]
    fn inline_sources_requires_a_javascript_map_in_projects() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export const a = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"inlineSources":true}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let error = compile_project(&project, &ProjectCompileOptions::default(), &filesystem)
            .expect_err("inlineSources without a JavaScript map must fail");
        assert!(matches!(
            error,
            ProjectCompileError::UnsupportedOption {
                option: "inlineSources without sourceMap or inlineSourceMap"
            }
        ));
    }

    #[test]
    fn compile_project_reuses_graph_emits_maps_and_tracks_incremental_hashes() {
        let fixture = Fixture::new();
        fixture.write("src/shared.ts", "export const shared = 1;\n");
        fixture.write(
            "src/a.ts",
            "import { shared } from \"./shared\";\nexport const a = shared;\n",
        );
        fixture.write(
            "src/b.ts",
            "import { shared } from \"./shared\";\nexport const b = shared;\n",
        );
        fixture.write(
            "tsconfig.json",
            r#"{
                "files":["src/a.ts","src/b.ts"],
                "compilerOptions":{
                    "rootDir":"src",
                    "outDir":"dist",
                    "declaration":true,
                    "sourceMap":true,
                    "inlineSources":true,
                    "declarationMap":true,
                    "incremental":true
                }
            }"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let first =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
        assert_eq!(
            first
                .sources
                .iter()
                .map(|source| source.path.clone())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([
                fixture.0.join("src/a.ts"),
                fixture.0.join("src/b.ts"),
                fixture.0.join("src/shared.ts"),
            ])
        );
        for relative in [
            "dist/a.js",
            "dist/a.js.map",
            "dist/a.d.ts",
            "dist/a.d.ts.map",
            "dist/b.js",
            "dist/b.js.map",
            "dist/b.d.ts",
            "dist/b.d.ts.map",
            "dist/shared.js",
            "dist/shared.js.map",
            "dist/shared.d.ts",
            "dist/shared.d.ts.map",
        ] {
            assert!(
                first.outputs.files.contains_key(&fixture.0.join(relative)),
                "{relative}"
            );
        }
        for (path, bytes) in &first.outputs.files {
            let text = std::str::from_utf8(bytes).expect("text artifact");
            if path.to_string_lossy().ends_with(".d.ts.map") {
                assert!(!text.contains("\"sourcesContent\""), "{}", path.display());
            } else if path.to_string_lossy().ends_with(".js.map") {
                assert!(text.contains("\"sourcesContent\""), "{}", path.display());
            }
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, bytes).unwrap();
        }
        let (info_path, first_info) = first.build_info.clone().expect("incremental build info");
        fs::write(&info_path, first_info.encode().unwrap()).unwrap();

        let unchanged =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
        assert!(unchanged.up_to_date);
        assert!(unchanged.outputs.files.is_empty());

        fixture.write(
            "src/b.ts",
            "import { shared } from \"./shared\";\nexport const b = shared + 1;\n",
        );
        let changed_project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let changed = compile_project(
            &changed_project,
            &ProjectCompileOptions::default(),
            &filesystem,
        )
        .unwrap();
        assert!(!changed.up_to_date);
        assert_ne!(
            changed.build_info.as_ref().unwrap().1.signature,
            first_info.signature
        );
    }

    #[test]
    fn compile_project_enforces_no_emit_and_no_emit_on_error() {
        let fixture = Fixture::new();
        fixture.write("bad.ts", "const value = ;\n");
        fixture.write(
            "no-emit.json",
            r#"{"files":["bad.ts"],"compilerOptions":{"noEmit":true,"incremental":true}}"#,
        );
        fixture.write(
            "no-emit-on-error.json",
            r#"{"files":["bad.ts"],"compilerOptions":{"outDir":"dist","noEmitOnError":true}}"#,
        );
        let filesystem = fixture.filesystem();
        let no_emit =
            EffectiveProject::load(&fixture.request("no-emit.json"), &filesystem).unwrap();
        let report =
            compile_project(&no_emit, &ProjectCompileOptions::default(), &filesystem).unwrap();
        assert!(!report.diagnostics.is_empty());
        assert!(!report.emitted);
        assert!(report.outputs.files.is_empty());
        assert!(report.build_info.is_none());

        let gated =
            EffectiveProject::load(&fixture.request("no-emit-on-error.json"), &filesystem).unwrap();
        let report =
            compile_project(&gated, &ProjectCompileOptions::default(), &filesystem).unwrap();
        assert!(!report.diagnostics.is_empty());
        assert!(!report.emitted);
        assert!(report.outputs.files.is_empty());
    }

    #[test]
    fn compile_project_routes_effective_jsx_options_to_javascript_emit() {
        let fixture = Fixture::new();
        fixture.write("main.tsx", "export const view = <div />;\n");
        fixture.write(
            "runtime/jsx-runtime.ts",
            "export function jsx() {} export function jsxs() {} export const Fragment = 0;\n",
        );
        fixture.write(
            "tsconfig.json",
            r#"{"files":["main.tsx"],"compilerOptions":{"jsx":"react-jsx","jsxImportSource":"./runtime","outDir":"dist"}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let report =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/main.js"))
                .expect("project JavaScript output"),
        )
        .unwrap();
        assert!(javascript.contains("./runtime/jsx-runtime"));
        assert!(!javascript.contains("<div"));
    }

    #[test]
    fn always_strict_emits_use_strict_prologue() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "const a = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"alwaysStrict":true,"outDir":"dist"}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        assert!(project.options().always_strict());
        let report =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/a.js"))
                .expect("project JavaScript output"),
        )
        .unwrap();
        assert!(
            javascript.starts_with("\"use strict\";\n"),
            "alwaysStrict emits the prologue: {javascript}"
        );
    }

    #[test]
    fn strict_implies_always_strict_prologue() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "const a = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"strict":true,"outDir":"dist"}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        assert!(project.options().always_strict());
        let report =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/a.js"))
                .expect("project JavaScript output"),
        )
        .unwrap();
        assert!(
            javascript.starts_with("\"use strict\";\n"),
            "strict implies alwaysStrict: {javascript}"
        );
    }

    #[test]
    fn compile_project_rejects_output_collisions_before_emission() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export const typed = 1;\n");
        fixture.write("src/a.js", "export const javascript = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts","src/a.js"],"compilerOptions":{"allowJs":true,"rootDir":"src","outDir":"dist"}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let error =
            compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap_err();
        assert!(matches!(
            error,
            ProjectCompileError::Output(OutputMapError::Collision { .. })
        ));
        assert!(!fixture.0.join("dist/a.js").exists());
    }

    fn map_json(report: &ProjectCompileResult, path: &Path) -> serde_helpers::MapView {
        serde_helpers::MapView::parse(
            report
                .outputs
                .files
                .get(path)
                .unwrap_or_else(|| panic!("missing output {}", path.display())),
        )
    }

    #[test]
    fn contract_examples_match_type_script_7_source_map_naming() {
        let fixture = Fixture::new();
        fixture.write("src/sub/x.ts", "export const x = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{
                "files":["src/sub/x.ts"],
                "compilerOptions":{
                    "rootDir":"src",
                    "outDir":"dist",
                    "declaration":true,
                    "sourceMap":true,
                    "declarationMap":true
                }
            }"#,
        );

        let run = |map_root: Option<&str>, source_root: Option<&str>| {
            let filesystem = fixture.filesystem();
            let mut request = fixture.request("tsconfig.json");
            request.overrides.map_root = map_root.map(Arc::from);
            request.overrides.source_root = source_root.map(Arc::from);
            let project = EffectiveProject::load(&request, &filesystem).unwrap();
            let report =
                compile_project(&project, &ProjectCompileOptions::default(), &filesystem).unwrap();
            assert!(report.emitted);
            // Physical map files stay beside the planned outputs.
            assert!(
                report
                    .outputs
                    .files
                    .contains_key(&fixture.0.join("dist/sub/x.js.map"))
            );
            assert!(
                report
                    .outputs
                    .files
                    .contains_key(&fixture.0.join("dist/sub/x.d.ts.map"))
            );
            report
        };

        // Relative mapRoot, no sourceRoot: URL is relative to the emitting file
        // and `sources` is the path from the map directory to the source.
        let report = run(Some("maps"), None);
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.js"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            javascript.contains("//# sourceMappingURL=../../src/maps/sub/x.js.map"),
            "{javascript}"
        );
        let map = map_json(&report, &fixture.0.join("dist/sub/x.js.map"));
        // Upstream always writes the key: 256 of the 259 map JSON lines in the
        // TypeScript 7.0.2 authority baselines carry `"sourceRoot":""`, and all
        // 259 carry the key. An unset root serializes as the empty string.
        assert_eq!(map.source_root.as_deref(), Some(""));
        assert_eq!(map.sources, vec!["../../src/sub/x.ts".to_owned()]);

        // Relative mapRoot with sourceRoot: sources collapse to the common base
        // and the raw (normalized) sourceRoot rides in the JSON for both maps.
        let report = run(Some("maps"), Some("../sourceroot"));
        let map = map_json(&report, &fixture.0.join("dist/sub/x.js.map"));
        assert_eq!(map.source_root.as_deref(), Some("../sourceroot/"));
        assert_eq!(map.sources, vec!["sub/x.ts".to_owned()]);
        let declaration_map = map_json(&report, &fixture.0.join("dist/sub/x.d.ts.map"));
        assert_eq!(
            declaration_map.source_root.as_deref(),
            Some("../sourceroot/")
        );
        assert_eq!(declaration_map.sources, vec!["sub/x.ts".to_owned()]);

        // URL mapRoot: verbatim URL joined with the source-relative identity.
        let report = run(Some("https://maps.example.com/cdn"), None);
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.js"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            javascript.contains("//# sourceMappingURL=https://maps.example.com/cdn/sub/x.js.map",),
            "{javascript}"
        );
        let declaration = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.d.ts"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            declaration
                .contains("//# sourceMappingURL=https://maps.example.com/cdn/sub/x.d.ts.map",),
            "{declaration}"
        );
        let map = map_json(&report, &fixture.0.join("dist/sub/x.js.map"));
        assert_eq!(map.sources, vec!["../../src/sub/x.ts".to_owned()]);

        // Absolute mapRoot: absolute URL with the source-relative identity.
        let report = run(Some("/abs/maps"), None);
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.js"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            javascript.contains("//# sourceMappingURL=/abs/maps/sub/x.js.map"),
            "{javascript}"
        );

        let report = run(Some("../maps"), None);
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.js"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            javascript.contains("//# sourceMappingURL=../../maps/sub/x.js.map"),
            "{javascript}"
        );

        let report = run(Some(""), None);
        let javascript = std::str::from_utf8(
            report
                .outputs
                .files
                .get(&fixture.0.join("dist/sub/x.js"))
                .unwrap(),
        )
        .unwrap();
        assert!(
            javascript.contains("//# sourceMappingURL=x.js.map"),
            "{javascript}"
        );
    }

    #[test]
    fn inline_maps_and_dotted_basenames_keep_source_relative_identity() {
        let fixture = Fixture::new();
        fixture.write("src/sub/name.part.ts", "export const value = 1;\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/sub/name.part.ts"],"compilerOptions":{"rootDir":"src","outDir":"dist","inlineSourceMap":true,"sourceRoot":"https://src.example/"}}"#,
        );
        let filesystem = fixture.filesystem();
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &filesystem).unwrap();
        let source = fixture.0.join("src/sub/name.part.ts");
        let mut planned = BTreeMap::new();
        planned.insert(
            ArtifactKind::JavaScript,
            fixture.0.join("dist/sub/name.part.js"),
        );
        let plan = super::super::output::OutputPlan {
            project_root: fixture.0.clone(),
            common_source_dir: fixture.0.join("src"),
            artifacts: BTreeMap::new(),
        };
        let names = source_map_names(&source, &planned, &plan, project.options());
        assert_eq!(names.js_source_name.as_deref(), Some("sub/name.part.ts"));

        let dotted = surface_map_names(
            &source,
            &fixture.0.join("dist/sub/name.part.js"),
            &fixture.0.join("dist/sub/name.part.js.map"),
            Some("https://maps.example/"),
            None,
            &fixture.0.join("src"),
            false,
        );
        assert_eq!(
            dotted.source_map_url.as_deref(),
            Some("https://maps.example/sub/name.part.js.map")
        );
    }

    #[test]
    fn project_config_parses_and_preserves_raw_map_options() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export {};\n");
        fixture.write(
            "tsconfig.json",
            r#"{"files":["src/a.ts"],"compilerOptions":{"mapRoot":"maps/","sourceRoot":"https://src.example.com/"}}"#,
        );
        let project =
            EffectiveProject::load(&fixture.request("tsconfig.json"), &fixture.filesystem())
                .unwrap();
        assert_eq!(project.options().map_root(), Some("maps/"));
        assert_eq!(
            project.options().source_root(),
            Some("https://src.example.com/")
        );
    }

    #[test]
    fn cli_string_overrides_reach_project_options_verbatim() {
        let fixture = Fixture::new();
        fixture.write("src/a.ts", "export {};\n");
        fixture.write("tsconfig.json", r#"{"files":["src/a.ts"]}"#);
        let mut request = fixture.request("tsconfig.json");
        request.overrides.map_root = Some(Arc::from("https://maps.example.com/cdn"));
        request.overrides.source_root = Some(Arc::from("/abs/root"));
        let project = EffectiveProject::load(&request, &fixture.filesystem()).unwrap();
        assert_eq!(
            project.options().map_root(),
            Some("https://maps.example.com/cdn")
        );
        assert_eq!(project.options().source_root(), Some("/abs/root"));
    }
}

/// Minimal reader for the map JSON fields these tests assert on.
#[cfg(test)]
mod serde_helpers {
    use crate::project::{JsonObject, JsonValue};

    pub struct MapView {
        pub source_root: Option<String>,
        pub sources: Vec<String>,
    }

    impl MapView {
        pub fn parse(bytes: &[u8]) -> MapView {
            let text = std::str::from_utf8(bytes).expect("UTF-8 map JSON");
            let object: JsonObject = crate::project::parse_jsonc(text)
                .expect("map JSON parses")
                .as_object()
                .expect("map JSON object")
                .clone();
            let source_root = object
                .get("sourceRoot")
                .and_then(JsonValue::as_str)
                .map(str::to_owned);
            let sources = object
                .get("sources")
                .and_then(JsonValue::as_array)
                .map(|values| {
                    values
                        .iter()
                        .map(|value| value.as_str().expect("string source").to_owned())
                        .collect()
                })
                .unwrap_or_default();
            MapView {
                source_root,
                sources,
            }
        }
    }
}
