//! Compiler-owned whole-program loading and canonical module identity.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use bamts_bytecode::{
    Binding, BindingId, BindingKind, Constant, ConstantId, EcmaString, EcmaStringBuilder, Edge,
    EdgeId, EdgeKind, EdgeTarget, Export, ExportSource, ModuleId, Program as BytecodeProgram,
    ProgramModule, ProgramVerifyError, Verified,
};
use bamts_cancel::{CancellationToken, Cancelled};

use crate::{
    checker::ProgramCheckOptions,
    diagnostic::DiagnosticCode,
    enum_plan::EnumFacts,
    jsx_desugar::{
        JsxEmitOptions, JsxRuntimeBinding, JsxRuntimeImportStyle, JsxSourceDesugarPlan,
        desugar_source_jsx,
    },
    lower::{self, LowerError, LowerOptions},
    namespace_plan::NamespaceFacts,
    parser,
    pipeline::ProgramFrontendOutput,
    project::{
        CompilerOptions, ModuleResolutionError, PackageError, PackageJson, PackageMode,
        PackageTarget, ProjectRoot, ResolutionConditions, ResolutionFlavor, plan_relative_module,
        resolution::ResolutionMode,
    },
    scanner,
    service::filesystem::{FileSystem, FileSystemError, OsFileSystem},
    source::{
        JsxEmit, MAX_SOURCE_BYTES, NodeIdSource, ScriptKind, SourceId, SourceIdentity,
        SourcePositionError, SourceText, TextRange, Utf16Pos,
    },
    syntax::{
        ExportDeclaration, ExportDefaultValue, ExportNamedDeclaration, ExportSpecifierMode,
        ImportBinding, ImportSpecifierMode, ModuleExportName, SourceFile, Statement, TokenKind,
        VariableKind,
    },
};
/// Stable diagnostic code for a per-file source budget breach.
pub const SOURCE_TOO_LARGE: DiagnosticCode = DiagnosticCode::new("BAMTS-R001");
/// Stable diagnostic code for a session aggregate source budget breach.
pub const SESSION_TOO_LARGE: DiagnosticCode = DiagnosticCode::new("BAMTS-R002");

/// Aggregate UTF-8 byte budget for every canonical source in one loaded graph.
///
/// A graph at exactly 256 MiB is accepted. Loading one byte more fails with
/// ProgramLoadError::SessionTooLarge.
pub const MAX_SESSION_SOURCE_BYTES: usize = 256 * 1024 * 1024;

/// The semantic role of one resolved module dependency.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModuleEdgeKind {
    StaticRuntime,
    TypeOnly,
    DynamicRuntime,
}

/// The canonical identity of a resolved module dependency.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModuleTarget {
    Local(SourceId),
    External(Arc<str>),
}

impl ModuleTarget {
    #[must_use]
    pub const fn local_source_id(&self) -> Option<SourceId> {
        match self {
            Self::Local(source_id) => Some(*source_id),
            Self::External(_) => None,
        }
    }

    #[must_use]
    pub fn external_specifier(&self) -> Option<&str> {
        match self {
            Self::Local(_) => None,
            Self::External(specifier) => Some(specifier),
        }
    }
}

/// One source-anchored, resolved dependency. `target` is the runtime and lowering
/// identity; `type_target` is a checker-only declaration overlay when one exists.
/// `flavor` and `mode` record the exact resolution inputs used for `target`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleEdge {
    kind: ModuleEdgeKind,
    flavor: ResolutionFlavor,
    mode: ResolutionMode,
    specifier: Arc<str>,
    target: ModuleTarget,
    type_target: Option<ModuleTarget>,
    range: TextRange,
}
impl ModuleEdge {
    #[must_use]
    pub const fn kind(&self) -> ModuleEdgeKind {
        self.kind
    }
    /// Returns the resolution flavor used for `target`.
    ///
    /// A separate `type_target` overlay, when present, was resolved as
    /// [`ResolutionFlavor::Types`].
    #[must_use]
    pub const fn flavor(&self) -> ResolutionFlavor {
        self.flavor
    }

    #[must_use]
    pub const fn mode(&self) -> ResolutionMode {
        self.mode
    }

    #[must_use]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[must_use]
    pub const fn target(&self) -> &ModuleTarget {
        &self.target
    }

    #[must_use]
    pub const fn type_target(&self) -> Option<&ModuleTarget> {
        self.type_target.as_ref()
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }
}

/// A module loaded exactly once under its canonical filesystem identity.
#[derive(Clone, Debug)]
pub struct ResolvedModule {
    identity: SourceIdentity,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
    dependencies: Arc<[ModuleEdge]>,
    jsx_plan: Option<JsxSourceDesugarPlan>,
}

impl ResolvedModule {
    #[must_use]
    pub const fn identity(&self) -> &SourceIdentity {
        &self.identity
    }

    #[must_use]
    pub const fn source_id(&self) -> SourceId {
        self.identity.source_id()
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        self.identity.path()
    }

    #[must_use]
    pub const fn script_kind(&self) -> ScriptKind {
        self.script_kind
    }

    #[must_use]
    pub const fn source(&self) -> &Arc<SourceText> {
        &self.source
    }

    #[must_use]
    pub fn dependencies(&self) -> &[ModuleEdge] {
        &self.dependencies
    }

    pub(crate) const fn jsx_plan(&self) -> Option<&JsxSourceDesugarPlan> {
        self.jsx_plan.as_ref()
    }
}

/// Output path used to make the JSX routing decision.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramOutputKind {
    JavaScript,
    NativeExecutable,
}

/// The single program-level decision for JSX emission versus lowering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JsxRoutingDecision {
    Emit,
    TransformAndEmit,
    Lower,
    RejectPreservedNative,
}

/// The canonical whole-program value shared by every compiler and execution phase.
///
/// Runtime and type-only modules are stored in deterministic dependency-first DFS
/// postorder. Declaration overlays and their type dependencies are appended afterward.
/// Cycles remain ordinary edges; each canonical file appears exactly once. Overlays are
/// reachable only through [`ModuleEdge::type_target`], so runtime traversal follows only
/// [`ModuleEdge::target`].
#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    root: ProjectRoot,
    roots: Arc<[SourceId]>,
    modules: Arc<[ResolvedModule]>,
    module_indices: HashMap<SourceId, usize>,
    commonjs: bool,
    no_implicit_any: bool,
    strict_null_checks: bool,
    strict_property_initialization: bool,
    always_strict: bool,
    no_emit_helpers: bool,
    use_define_for_class_fields: Option<bool>,
    import_helpers: Option<bool>,
    target: crate::emitter::ScriptTarget,
    libs: crate::checker::intrinsic_environment::LibSet,
    check_js: bool,
    jsx: Option<JsxEmit>,
    jsx_factory: Option<Arc<str>>,
    jsx_fragment_factory: Option<Arc<str>>,
    jsx_import_source: Option<Arc<str>>,
}

impl ResolvedProgram {
    #[must_use]
    pub const fn root(&self) -> &ProjectRoot {
        &self.root
    }

    #[must_use]
    pub const fn use_define_for_class_fields(&self) -> Option<bool> {
        self.use_define_for_class_fields
    }

    #[must_use]
    pub const fn import_helpers(&self) -> Option<bool> {
        self.import_helpers
    }

    #[must_use]
    pub fn roots(&self) -> &[SourceId] {
        &self.roots
    }

    #[must_use]
    pub fn entrypoint_id(&self) -> SourceId {
        self.roots[0]
    }

    #[must_use]
    pub fn entrypoint(&self) -> &ResolvedModule {
        self.module(self.entrypoint_id())
            .expect("resolved program always contains every root")
    }

    #[must_use]
    pub fn modules(&self) -> &[ResolvedModule] {
        &self.modules
    }

    #[must_use]
    pub fn module(&self, source_id: SourceId) -> Option<&ResolvedModule> {
        self.module_indices
            .get(&source_id)
            .map(|index| &self.modules[*index])
    }

    /// Whether compiler options select the CommonJS wrapper environment.
    #[must_use]
    pub const fn is_commonjs(&self) -> bool {
        self.commonjs
    }

    #[must_use]
    pub const fn jsx(&self) -> Option<JsxEmit> {
        self.jsx
    }

    #[must_use]
    pub fn jsx_factory(&self) -> Option<&str> {
        self.jsx_factory.as_deref()
    }

    #[must_use]
    pub fn jsx_fragment_factory(&self) -> Option<&str> {
        self.jsx_fragment_factory.as_deref()
    }

    #[must_use]
    pub fn jsx_import_source(&self) -> Option<&str> {
        self.jsx_import_source.as_deref()
    }

    /// Selects the only valid JSX path for a requested program product.
    #[must_use]
    pub const fn jsx_routing_decision(&self, output: ProgramOutputKind) -> JsxRoutingDecision {
        match (output, self.jsx) {
            (
                ProgramOutputKind::JavaScript,
                None | Some(JsxEmit::Preserve | JsxEmit::ReactNative),
            ) => JsxRoutingDecision::Emit,
            (
                ProgramOutputKind::JavaScript,
                Some(JsxEmit::React | JsxEmit::ReactJsx | JsxEmit::ReactJsxDev),
            ) => JsxRoutingDecision::TransformAndEmit,
            (
                ProgramOutputKind::NativeExecutable,
                None | Some(JsxEmit::React | JsxEmit::ReactJsx | JsxEmit::ReactJsxDev),
            ) => JsxRoutingDecision::Lower,
            (
                ProgramOutputKind::NativeExecutable,
                Some(JsxEmit::Preserve | JsxEmit::ReactNative),
            ) => JsxRoutingDecision::RejectPreservedNative,
        }
    }

    /// Constructs the effective checker environment for this resolved program.
    ///
    /// The checker-relevant compiler options travel with the resolved program,
    /// so every consumer (project build, direct CLI, suite lane, npm API)
    /// observes the same strict-family configuration without reconstructing
    /// options from raw tsconfig text.
    #[must_use]
    pub fn check_options(&self) -> ProgramCheckOptions {
        if self.commonjs {
            ProgramCheckOptions::commonjs()
        } else {
            ProgramCheckOptions::standard()
        }
        .with_no_implicit_any(self.no_implicit_any)
        .with_strict_null_checks(self.strict_null_checks)
        .with_strict_property_initialization(self.strict_property_initialization)
        .with_always_strict(self.always_strict)
        .with_no_emit_helpers(self.no_emit_helpers)
        .with_script_target(self.target)
        .with_libs(self.libs)
        .with_check_js(self.check_js)
    }

    /// Returns the eager runtime closure in the program's canonical order.
    /// Type-only, dynamic, and external edges do not cause eager runtime initialization.
    #[must_use]
    pub fn runtime_modules(&self) -> Vec<&ResolvedModule> {
        let mut reachable = HashSet::new();
        let mut pending = self.roots.to_vec();
        while let Some(source_id) = pending.pop() {
            if !reachable.insert(source_id) {
                continue;
            }
            let module = self
                .module(source_id)
                .expect("every local edge target belongs to the resolved program");
            pending.extend(module.dependencies().iter().filter_map(|edge| {
                match (edge.kind, edge.target()) {
                    (ModuleEdgeKind::StaticRuntime, ModuleTarget::Local(source_id)) => {
                        Some(*source_id)
                    }
                    _ => None,
                }
            }));
        }
        self.modules
            .iter()
            .filter(|module| reachable.contains(&module.source_id()))
            .collect()
    }
}

/// A typed module-resolution failure anchored at the importing source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnresolvedModuleDiagnostic {
    importer: Arc<Path>,
    specifier: Arc<str>,
    kind: ModuleEdgeKind,
    range: TextRange,
}

impl UnresolvedModuleDiagnostic {
    #[must_use]
    pub fn importer(&self) -> &Path {
        &self.importer
    }

    #[must_use]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[must_use]
    pub const fn kind(&self) -> ModuleEdgeKind {
        self.kind
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }
}

/// Fail-fast program loading errors. No partially resolved graph is exposed.
#[derive(Debug)]
pub enum ProgramLoadError {
    Cancelled {
        path: PathBuf,
        source: Cancelled,
    },
    NoRoots,
    InvalidRoot(io::Error),
    EntryOutsideRoot(PathBuf),
    TraversalRejected {
        path: PathBuf,
        root: PathBuf,
    },
    Read {
        path: PathBuf,
        source: io::Error,
    },
    UnsupportedSource(PathBuf),
    Source {
        path: PathBuf,
        source: SourcePositionError,
    },
    TooManySources,
    IllFormedModuleSpecifier {
        importer: PathBuf,
        range: TextRange,
    },
    InvalidSpecifier {
        diagnostic: UnresolvedModuleDiagnostic,
        source: ModuleResolutionError,
    },
    InvalidPackage {
        diagnostic: UnresolvedModuleDiagnostic,
        source: PackageError,
    },
    UnresolvedModule(UnresolvedModuleDiagnostic),
    JsxPlan {
        path: PathBuf,
        message: Arc<str>,
    },
    /// One source file exceeded the 16 MiB per-file input budget.
    SourceTooLarge {
        path: PathBuf,
        len: usize,
    },
    /// Loading one more source would exceed the 256 MiB session budget.
    SessionTooLarge {
        path: PathBuf,
        total: usize,
    },
}

impl fmt::Display for ProgramLoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled { path, .. } => write!(
                formatter,
                "program loading cancelled while processing {}",
                path.display()
            ),
            Self::NoRoots => formatter.write_str("program requires at least one root source"),
            Self::InvalidRoot(error) => {
                write!(formatter, "cannot canonicalize project root: {error}")
            }
            Self::EntryOutsideRoot(path) => {
                write!(
                    formatter,
                    "entrypoint {} is outside the project root",
                    path.display()
                )
            }
            Self::TraversalRejected { path, root } => write!(
                formatter,
                "resolved path {} escapes project root {}",
                path.display(),
                root.display()
            ),
            Self::Read { path, source } => {
                write!(formatter, "cannot read {}: {source}", path.display())
            }
            Self::UnsupportedSource(path) => {
                write!(
                    formatter,
                    "unsupported source extension: {}",
                    path.display()
                )
            }
            Self::Source { path, source } => {
                write!(
                    formatter,
                    "cannot index source {}: {source}",
                    path.display()
                )
            }
            Self::TooManySources => {
                formatter.write_str("program contains more than u32::MAX sources")
            }
            Self::IllFormedModuleSpecifier { importer, .. } => write!(
                formatter,
                "module specifier in {} is not well-formed UTF-16",
                importer.display()
            ),
            Self::InvalidSpecifier { diagnostic, source } => write!(
                formatter,
                "invalid module specifier {:?} in {}: {source}",
                diagnostic.specifier(),
                diagnostic.importer().display()
            ),
            Self::InvalidPackage { diagnostic, source } => write!(
                formatter,
                "invalid package specifier {:?} in {}: {source}",
                diagnostic.specifier(),
                diagnostic.importer().display()
            ),
            Self::UnresolvedModule(diagnostic) => write!(
                formatter,
                "cannot resolve {:?} from {}",
                diagnostic.specifier(),
                diagnostic.importer().display()
            ),
            Self::JsxPlan { path, message } => {
                write!(
                    formatter,
                    "cannot plan JSX in {}: {message}",
                    path.display()
                )
            }
            Self::SourceTooLarge { path, len } => write!(
                formatter,
                "source file {} is {len} bytes, exceeding the {MAX_SOURCE_BYTES}-byte per-file budget",
                path.display()
            ),
            Self::SessionTooLarge { path, total } => write!(
                formatter,
                "loading {} would raise the session source total to {total} bytes, exceeding the {MAX_SESSION_SOURCE_BYTES}-byte session budget",
                path.display()
            ),
        }
    }
}
impl ProgramLoadError {
    /// Stable diagnostic code for a frontend budget breach, when applicable.
    #[must_use]
    pub const fn code(&self) -> Option<DiagnosticCode> {
        match self {
            Self::SourceTooLarge { .. } => Some(SOURCE_TOO_LARGE),
            Self::SessionTooLarge { .. } => Some(SESSION_TOO_LARGE),
            _ => None,
        }
    }
}

impl std::error::Error for ProgramLoadError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Cancelled { source, .. } => Some(source),
            Self::InvalidRoot(error) | Self::Read { source: error, .. } => Some(error),
            Self::Source { source, .. } => Some(source),
            Self::InvalidSpecifier { source, .. } => Some(source),
            Self::InvalidPackage { source, .. } => Some(source),
            _ => None,
        }
    }
}
fn file_system_io(error: FileSystemError) -> io::Error {
    io::Error::new(error.kind(), error)
}

/// Loads one or more roots and their complete local module graph.
#[derive(Clone)]
pub struct ProgramLoader {
    root: ProjectRoot,
    options: CompilerOptions,
    fs: Arc<dyn FileSystem>,
}

impl fmt::Debug for ProgramLoader {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProgramLoader")
            .field("root", &self.root)
            .field("options", &self.options)
            .finish_non_exhaustive()
    }
}

impl ProgramLoader {
    /// Creates a loader using the project's already-validated compiler options.
    pub fn new(root: &ProjectRoot, options: &CompilerOptions) -> Result<Self, ProgramLoadError> {
        let fs = Arc::new(
            OsFileSystem::new(root.path())
                .map_err(|error| ProgramLoadError::InvalidRoot(file_system_io(error)))?,
        );
        Self::with_file_system(root, options, fs)
    }

    /// Creates a loader over a caller-provided, root-confined filesystem.
    pub fn with_file_system(
        root: &ProjectRoot,
        options: &CompilerOptions,
        fs: Arc<dyn FileSystem>,
    ) -> Result<Self, ProgramLoadError> {
        let canonical = fs
            .normalize(root.path())
            .map_err(|error| ProgramLoadError::InvalidRoot(file_system_io(error)))?;
        let root = ProjectRoot::new(canonical).map_err(|error| {
            ProgramLoadError::InvalidRoot(io::Error::new(io::ErrorKind::InvalidInput, error))
        })?;
        Ok(Self {
            root,
            options: options.clone(),
            fs,
        })
    }

    /// Resolves and loads an entrypoint. The entrypoint may be root-relative or absolute.
    pub fn load(&self, entrypoint: impl AsRef<Path>) -> Result<ResolvedProgram, ProgramLoadError> {
        self.load_with_cancel(entrypoint, &CancellationToken::new())
    }

    /// Resolves and loads an entrypoint with cooperative cancellation.
    pub fn load_with_cancel(
        &self,
        entrypoint: impl AsRef<Path>,
        cancel: &CancellationToken,
    ) -> Result<ResolvedProgram, ProgramLoadError> {
        let entrypoint = entrypoint.as_ref().to_path_buf();
        self.load_roots_with_cancel(&[entrypoint], cancel)
    }

    /// Resolves a canonical root set into one shared module graph.
    pub fn load_roots(&self, roots: &[PathBuf]) -> Result<ResolvedProgram, ProgramLoadError> {
        self.load_roots_with_cancel(roots, &CancellationToken::new())
    }

    fn load_roots_with_cancel(
        &self,
        roots: &[PathBuf],
        cancel: &CancellationToken,
    ) -> Result<ResolvedProgram, ProgramLoadError> {
        let cancellation_path = roots.first().map_or(self.root.path(), PathBuf::as_path);
        check_load_cancel(cancel, cancellation_path)?;
        if roots.is_empty() {
            return Err(ProgramLoadError::NoRoots);
        }

        let mut requested_roots = roots.to_vec();
        requested_roots.sort();
        requested_roots.dedup();

        let mut canonical_roots = BTreeSet::new();
        for root in requested_roots {
            check_load_cancel(cancel, &root)?;
            let requested = self
                .root
                .resolve(&root)
                .map_err(|_| ProgramLoadError::EntryOutsideRoot(root.clone()))?;
            let selected = self
                .select_absolute(&requested, ResolutionFlavor::Runtime)?
                .ok_or_else(|| ProgramLoadError::Read {
                    path: requested,
                    source: io::Error::new(io::ErrorKind::NotFound, "root source does not exist"),
                })?;
            check_load_cancel(cancel, &selected)?;
            canonical_roots.insert(selected);
        }

        let ambient = ambient_resolution_mode(&self.options);
        let mut state = LoadState {
            loader: self,
            identities: HashMap::new(),
            modules: Vec::new(),
            overlay_worklist: Vec::new(),
            type_overlays: Vec::new(),
            session_bytes: 0,
            ambient,
            cancel,
        };
        let mut root_ids = Vec::with_capacity(canonical_roots.len());
        for root in canonical_roots {
            check_load_cancel(cancel, &root)?;
            root_ids.push(state.visit(root)?);
        }
        state.load_declaration_overlays()?;
        check_load_cancel(cancel, cancellation_path)?;
        let module_indices = state
            .modules
            .iter()
            .enumerate()
            .map(|(index, module)| (module.source_id(), index))
            .collect();
        let target = self
            .options
            .target()
            .and_then(crate::emitter::parse_target)
            .unwrap_or_default();
        let libs = if self.options.lib().is_empty() {
            crate::checker::intrinsic_environment::LibSet::default_for_target(target)
        } else {
            crate::checker::intrinsic_environment::LibSet::from_lib_names(self.options.lib())
        };
        Ok(ResolvedProgram {
            root: self.root.clone(),
            roots: Arc::from(root_ids),
            modules: Arc::from(state.modules),
            module_indices,
            commonjs: ambient == ResolutionMode::Require,
            no_implicit_any: self.options.no_implicit_any(),
            strict_null_checks: self.options.strict_null_checks(),
            strict_property_initialization: self.options.strict_property_initialization(),
            always_strict: self.options.always_strict(),
            no_emit_helpers: self.options.no_emit_helpers(),
            use_define_for_class_fields: self.options.use_define_for_class_fields(),
            import_helpers: self.options.import_helpers(),
            target,
            libs,
            check_js: self.options.check_js(),
            jsx: self.options.jsx(),
            jsx_factory: self.options.jsx_factory().map(Arc::from),
            jsx_fragment_factory: self.options.jsx_fragment_factory().map(Arc::from),
            jsx_import_source: self.options.jsx_import_source().map(Arc::from),
        })
    }

    fn jsx_plan(
        &self,
        path: &Path,
        file: &SourceFile,
        source: &SourceText,
    ) -> Result<Option<JsxSourceDesugarPlan>, ProgramLoadError> {
        let Some(emit @ (JsxEmit::React | JsxEmit::ReactJsx | JsxEmit::ReactJsxDev)) =
            self.options.jsx()
        else {
            return Ok(None);
        };
        let options = JsxEmitOptions {
            emit,
            factory: self.options.jsx_factory().map(Arc::from),
            fragment_factory: self.options.jsx_fragment_factory().map(Arc::from),
            import_source: self.options.jsx_import_source().map(Arc::from),
            import_style: if ambient_resolution_mode(&self.options) == ResolutionMode::Require {
                JsxRuntimeImportStyle::CommonJs
            } else {
                JsxRuntimeImportStyle::EsModule
            },
            file_name: Some(Arc::from(path.to_string_lossy().into_owned())),
        };
        let mut ids = NodeIdSource::after(file.id());
        desugar_source_jsx(file, source, &options, &mut ids)
            .map(Some)
            .map_err(|error| ProgramLoadError::JsxPlan {
                path: path.to_path_buf(),
                message: Arc::from(error.to_string()),
            })
    }

    fn select_absolute(
        &self,
        requested: &Path,
        flavor: ResolutionFlavor,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        let relative = requested.strip_prefix(self.root.path()).map_err(|_| {
            ProgramLoadError::TraversalRejected {
                path: requested.to_path_buf(),
                root: self.root.path().to_path_buf(),
            }
        })?;
        let specifier = format!("./{}", relative.to_string_lossy().replace('\\', "/"));
        let synthetic_importer = self.root.path().join("__bamts_program__.ts");
        let plan = plan_relative_module(
            &self.root,
            synthetic_importer,
            &specifier,
            flavor,
            self.options.resolve_json_module(),
        )
        .map_err(|source| ProgramLoadError::InvalidSpecifier {
            diagnostic: diagnostic(
                self.root.path(),
                &specifier,
                edge_kind(flavor),
                TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO)
                    .expect("equal range endpoints are valid"),
            ),
            source,
        })?;
        self.canonical_selection(plan.candidates(), flavor)
    }

    fn canonical_selection(
        &self,
        candidates: &[PathBuf],
        flavor: ResolutionFlavor,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        if flavor == ResolutionFlavor::Runtime {
            for candidate in candidates {
                if is_declaration_path(candidate) || !self.is_file(candidate)? {
                    continue;
                }
                return self.canonical_candidate(candidate).map(Some);
            }
        }
        for candidate in candidates {
            if self.is_file(candidate)? {
                return self.canonical_candidate(candidate).map(Some);
            }
        }
        Ok(None)
    }

    fn canonical_candidate(&self, candidate: &Path) -> Result<PathBuf, ProgramLoadError> {
        let canonical = self
            .fs
            .normalize(candidate)
            .map_err(|error| ProgramLoadError::Read {
                path: candidate.to_path_buf(),
                source: file_system_io(error),
            })?;
        if !canonical.starts_with(self.root.path()) {
            return Err(ProgramLoadError::TraversalRejected {
                path: canonical,
                root: self.root.path().to_path_buf(),
            });
        }
        Ok(canonical)
    }

    fn is_file(&self, path: &Path) -> Result<bool, ProgramLoadError> {
        match self.fs.metadata(path) {
            Ok(_) => Ok(true),
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::InvalidInput
                ) =>
            {
                Ok(false)
            }
            Err(error) => Err(ProgramLoadError::Read {
                path: path.to_path_buf(),
                source: file_system_io(error),
            }),
        }
    }

    fn resolve_edge(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        cancel: &CancellationToken,
    ) -> Result<ResolvedEdge, ProgramLoadError> {
        let flavor = if edge.kind == ModuleEdgeKind::TypeOnly || is_declaration_path(importer) {
            ResolutionFlavor::Types
        } else {
            ResolutionFlavor::Runtime
        };
        if edge.specifier.starts_with("node:") {
            return Ok(ResolvedEdge {
                target: ResolvedEdgeTarget::External(Arc::clone(&edge.specifier)),
                type_overlay: None,
                flavor,
            });
        }
        if let Some(target) = self.resolve_local(importer, edge, flavor, cancel)? {
            let type_overlay = self.type_overlay(importer, edge, &target, cancel)?;
            return Ok(ResolvedEdge {
                target,
                type_overlay,
                flavor,
            });
        }
        if flavor == ResolutionFlavor::Types && split_package_specifier(&edge.specifier).is_some() {
            return Ok(ResolvedEdge {
                target: ResolvedEdgeTarget::External(Arc::clone(&edge.specifier)),
                type_overlay: None,
                flavor,
            });
        }
        Err(ProgramLoadError::UnresolvedModule(diagnostic(
            importer,
            &edge.specifier,
            edge.kind,
            edge.range,
        )))
    }

    fn resolve_local(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
        cancel: &CancellationToken,
    ) -> Result<Option<ResolvedEdgeTarget>, ProgramLoadError> {
        if edge.specifier.starts_with("./") || edge.specifier.starts_with("../") {
            let plan = plan_relative_module(
                &self.root,
                importer,
                &edge.specifier,
                flavor,
                self.options.resolve_json_module(),
            )
            .map_err(|source| ProgramLoadError::InvalidSpecifier {
                diagnostic: diagnostic(importer, &edge.specifier, edge.kind, edge.range),
                source,
            })?;
            return Ok(self
                .canonical_selection(plan.candidates(), flavor)?
                .map(ResolvedEdgeTarget::Local));
        }
        if edge.specifier.starts_with('#') {
            return self.resolve_package_import(importer, edge, flavor, cancel);
        }
        Ok(match self.resolve_mapped(&edge.specifier, flavor)? {
            Some(mapped) => Some(ResolvedEdgeTarget::Local(mapped)),
            None => self
                .resolve_package(importer, edge, flavor, cancel)?
                .map(ResolvedEdgeTarget::Local),
        })
    }

    fn type_overlay(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        runtime_target: &ResolvedEdgeTarget,
        cancel: &CancellationToken,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        if edge.kind == ModuleEdgeKind::TypeOnly || is_declaration_path(importer) {
            return Ok(None);
        }
        let ResolvedEdgeTarget::Local(runtime_path) = runtime_target else {
            return Ok(None);
        };
        let Some(ResolvedEdgeTarget::Local(type_path)) =
            self.resolve_local(importer, edge, ResolutionFlavor::Types, cancel)?
        else {
            return Ok(None);
        };
        Ok((type_path != *runtime_path).then_some(type_path))
    }

    fn resolve_mapped(
        &self,
        specifier: &str,
        flavor: ResolutionFlavor,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        for mapping in self.options.paths() {
            let Some(capture) = pattern_capture(mapping.pattern(), specifier) else {
                continue;
            };
            for target in mapping.targets() {
                let target = PathBuf::from(target.to_string_lossy().replace('*', capture));
                if let Some(selected) = self.select_absolute(&target, flavor)? {
                    return Ok(Some(selected));
                }
            }
        }
        Ok(None)
    }

    fn resolve_package(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
        cancel: &CancellationToken,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        let Some((package_name, subpath)) = split_package_specifier(&edge.specifier) else {
            return Ok(None);
        };
        let mut directory = importer.parent();
        while let Some(current) = directory {
            check_load_cancel(cancel, current)?;
            if !current.starts_with(self.root.path()) {
                break;
            }
            let package_directory = current.join("node_modules").join(package_name);
            let package_path = package_directory.join("package.json");
            if self.is_file(&package_path)? {
                check_load_cancel(cancel, &package_path)?;
                let package_source =
                    self.fs
                        .read(&package_path)
                        .map_err(|error| ProgramLoadError::Read {
                            path: package_path.clone(),
                            source: file_system_io(error),
                        })?;
                check_load_cancel(cancel, &package_path)?;
                let package = PackageJson::parse(&self.root, &package_path, &package_source)
                    .map_err(|source| ProgramLoadError::InvalidPackage {
                        diagnostic: diagnostic(importer, &edge.specifier, edge.kind, edge.range),
                        source,
                    })?;
                let mode = if flavor == ResolutionFlavor::Types {
                    PackageMode::Types
                } else {
                    edge.mode.package_mode()
                };
                let conditions = ResolutionConditions::for_mode(mode);
                let target = package
                    .resolve_export(&self.root, &subpath, mode, &conditions)
                    .map_err(|source| ProgramLoadError::InvalidPackage {
                        diagnostic: diagnostic(importer, &edge.specifier, edge.kind, edge.range),
                        source,
                    })?;
                return self.select_absolute(&target, flavor);
            }
            if current == self.root.path() {
                break;
            }
            directory = current.parent();
        }
        Ok(None)
    }
    fn resolve_package_import(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
        cancel: &CancellationToken,
    ) -> Result<Option<ResolvedEdgeTarget>, ProgramLoadError> {
        let mut directory = importer.parent();
        while let Some(current) = directory {
            check_load_cancel(cancel, current)?;
            if !current.starts_with(self.root.path()) {
                break;
            }
            let package_path = current.join("package.json");
            if self.is_file(&package_path)? {
                check_load_cancel(cancel, &package_path)?;
                let package_source =
                    self.fs
                        .read(&package_path)
                        .map_err(|error| ProgramLoadError::Read {
                            path: package_path.clone(),
                            source: file_system_io(error),
                        })?;
                check_load_cancel(cancel, &package_path)?;
                let package = PackageJson::parse(&self.root, &package_path, &package_source)
                    .map_err(|source| ProgramLoadError::InvalidPackage {
                        diagnostic: diagnostic(importer, &edge.specifier, edge.kind, edge.range),
                        source,
                    })?;
                let mode = if flavor == ResolutionFlavor::Types {
                    PackageMode::Types
                } else {
                    edge.mode.package_mode()
                };
                let conditions = ResolutionConditions::for_mode(mode);
                let target = package
                    .resolve_import(&self.root, &edge.specifier, &conditions)
                    .map_err(|source| ProgramLoadError::InvalidPackage {
                        diagnostic: diagnostic(importer, &edge.specifier, edge.kind, edge.range),
                        source,
                    })?;
                return match target {
                    PackageTarget::Path(path) => Ok(self
                        .select_absolute(&path, flavor)?
                        .map(ResolvedEdgeTarget::Local)),
                    PackageTarget::External(specifier) => {
                        let external = UnresolvedEdge {
                            kind: edge.kind,
                            mode: edge.mode,
                            specifier,
                            range: edge.range,
                        };
                        match self.resolve_mapped(&external.specifier, flavor)? {
                            Some(mapped) => Ok(Some(ResolvedEdgeTarget::Local(mapped))),
                            None => match self
                                .resolve_package(importer, &external, flavor, cancel)?
                            {
                                Some(package) => Ok(Some(ResolvedEdgeTarget::Local(package))),
                                None => Ok(Some(ResolvedEdgeTarget::External(external.specifier))),
                            },
                        }
                    }
                };
            }
            if current == self.root.path() {
                break;
            }
            directory = current.parent();
        }
        Ok(None)
    }
}

#[derive(Clone, Debug)]
enum ResolvedEdgeTarget {
    Local(PathBuf),
    External(Arc<str>),
}

#[derive(Clone, Debug)]
struct ResolvedEdge {
    target: ResolvedEdgeTarget,
    type_overlay: Option<PathBuf>,
    flavor: ResolutionFlavor,
}

#[derive(Clone, Debug)]
struct PendingEdge {
    edge: UnresolvedEdge,
    type_overlay: Option<PathBuf>,
    flavor: ResolutionFlavor,
}
/// Adds one canonical source's UTF-8 bytes to the session total.
fn accumulate_session_bytes(session_bytes: usize, added: usize) -> Result<usize, usize> {
    let total = session_bytes.saturating_add(added);
    if total > MAX_SESSION_SOURCE_BYTES {
        return Err(total);
    }
    Ok(total)
}

struct LoadState<'a> {
    loader: &'a ProgramLoader,
    identities: HashMap<PathBuf, SourceId>,
    modules: Vec<ResolvedModule>,
    overlay_worklist: Vec<PathBuf>,
    type_overlays: Vec<(SourceId, usize, PathBuf)>,
    session_bytes: usize,
    ambient: ResolutionMode,
    cancel: &'a CancellationToken,
}

impl LoadState<'_> {
    fn load_declaration_overlays(&mut self) -> Result<(), ProgramLoadError> {
        let mut next = 0;
        while next < self.overlay_worklist.len() {
            let path = self.overlay_worklist[next].clone();
            next += 1;
            check_load_cancel(self.cancel, &path)?;
            if !self.identities.contains_key(&path) {
                self.visit(path)?;
            }
        }

        let module_indices: HashMap<SourceId, usize> = self
            .modules
            .iter()
            .enumerate()
            .map(|(index, module)| (module.source_id(), index))
            .collect();
        for (importer, dependency_index, path) in &self.type_overlays {
            let type_source_id = *self
                .identities
                .get(path)
                .expect("every recorded declaration overlay was loaded");
            let module_index = module_indices[importer];
            let module = &mut self.modules[module_index];
            let mut dependencies = module.dependencies.to_vec();
            dependencies[*dependency_index].type_target = Some(ModuleTarget::Local(type_source_id));
            module.dependencies = Arc::from(dependencies);
        }
        Ok(())
    }
    /// Loads `entrypoint` and its local import graph with an explicit stack.
    ///
    /// SourceIds are assigned in DFS preorder (first discovery). Modules are
    /// appended in DFS postorder. Local edges are resolved left-to-right; a path
    /// already present in `identities` is reused immediately, which both
    /// deduplicates diamonds and retains cycle edges without re-entering.
    fn visit(&mut self, entrypoint: PathBuf) -> Result<SourceId, ProgramLoadError> {
        struct Frame {
            path: PathBuf,
            source_id: SourceId,
            script_kind: ScriptKind,
            source: Arc<SourceText>,
            remaining: std::vec::IntoIter<UnresolvedEdge>,
            jsx_plan: Option<JsxSourceDesugarPlan>,
            dependencies: Vec<ModuleEdge>,
            /// Local edge whose target visit is in flight (child on the stack).
            pending_edge: Option<PendingEdge>,
        }

        enum Resume {
            Enter(PathBuf),
            Advance,
        }

        let mut stack: Vec<Frame> = Vec::new();
        let mut resume = Resume::Enter(entrypoint);

        loop {
            match &resume {
                Resume::Enter(path) => check_load_cancel(self.cancel, path)?,
                Resume::Advance => {
                    let path = stack
                        .last()
                        .map_or(self.loader.root.path(), |frame| frame.path.as_path());
                    check_load_cancel(self.cancel, path)?;
                }
            }
            match resume {
                Resume::Enter(path) => {
                    if let Some(&source_id) = self.identities.get(&path) {
                        let Some(parent) = stack.last_mut() else {
                            return Ok(source_id);
                        };
                        let pending = parent.pending_edge.take().expect(
                            "deduplicated or cyclic local resume belongs to a pending edge",
                        );
                        let dependency_index = parent.dependencies.len();
                        parent.dependencies.push(ModuleEdge {
                            kind: pending.edge.kind,
                            flavor: pending.flavor,
                            mode: pending.edge.mode,
                            specifier: pending.edge.specifier,
                            target: ModuleTarget::Local(source_id),
                            type_target: None,
                            range: pending.edge.range,
                        });
                        if let Some(path) = pending.type_overlay {
                            self.type_overlays.push((
                                parent.source_id,
                                dependency_index,
                                path.clone(),
                            ));
                            self.overlay_worklist.push(path);
                        }
                        resume = Resume::Advance;
                        continue;
                    }

                    let source_id = SourceId::new(
                        u32::try_from(self.identities.len())
                            .map_err(|_| ProgramLoadError::TooManySources)?,
                    );
                    self.identities.insert(path.clone(), source_id);

                    let script_kind = script_kind(&path)
                        .ok_or_else(|| ProgramLoadError::UnsupportedSource(path.clone()))?;
                    check_load_cancel(self.cancel, &path)?;
                    let text =
                        self.loader
                            .fs
                            .read(&path)
                            .map_err(|error| ProgramLoadError::Read {
                                path: path.clone(),
                                source: file_system_io(error),
                            })?;
                    check_load_cancel(self.cancel, &path)?;
                    let len = text.len();
                    let source = SourceText::new(text).map_err(|source| match source {
                        SourcePositionError::SourceTooLarge { .. } => {
                            ProgramLoadError::SourceTooLarge {
                                path: path.clone(),
                                len,
                            }
                        }
                        source => ProgramLoadError::Source {
                            path: path.clone(),
                            source,
                        },
                    })?;
                    let source = source.with_declaration_file(is_declaration_path(&path));
                    self.session_bytes = accumulate_session_bytes(self.session_bytes, len)
                        .map_err(|total| ProgramLoadError::SessionTooLarge {
                            path: path.clone(),
                            total,
                        })?;
                    let source = Arc::new(source);
                    let scanned = scanner::scan_with_cancel(
                        source_id,
                        script_kind,
                        Arc::clone(&source),
                        self.cancel.clone(),
                    )
                    .map_err(|_| cancelled_load(&path))?;
                    let parsed = parser::parse_with_cancel(scanned, self.cancel.clone())
                        .map_err(|_| cancelled_load(&path))?;
                    check_load_cancel(self.cancel, &path)?;
                    let mut unresolved =
                        collect_edges(parsed.product(), self.ambient).map_err(|range| {
                            ProgramLoadError::IllFormedModuleSpecifier {
                                importer: path.clone(),
                                range,
                            }
                        })?;
                    let jsx_plan = if parsed.diagnostics().is_empty() {
                        check_load_cancel(self.cancel, &path)?;
                        self.loader.jsx_plan(&path, parsed.product(), &source)?
                    } else {
                        None
                    };
                    check_load_cancel(self.cancel, &path)?;
                    if let Some(specifier) = jsx_plan
                        .as_ref()
                        .and_then(|plan| plan.demand.module_specifier.as_ref())
                        && !unresolved.iter().any(|edge| {
                            edge.specifier.as_ref() == specifier.as_ref()
                                && edge.kind == ModuleEdgeKind::StaticRuntime
                        })
                    {
                        unresolved.push(UnresolvedEdge {
                            kind: ModuleEdgeKind::StaticRuntime,
                            mode: self.ambient,
                            specifier: Arc::clone(specifier),
                            range: parsed.product().range(),
                        });
                    }
                    let dependencies = Vec::with_capacity(unresolved.len());
                    stack.push(Frame {
                        path,
                        source_id,
                        script_kind,
                        source,
                        remaining: unresolved.into_iter(),
                        jsx_plan,
                        dependencies,
                        pending_edge: None,
                    });
                    resume = Resume::Advance;
                }
                Resume::Advance => {
                    let descend = {
                        let frame = stack
                            .last_mut()
                            .expect("Advance always runs with a frame on the stack");
                        loop {
                            check_load_cancel(self.cancel, &frame.path)?;
                            let Some(edge) = frame.remaining.next() else {
                                break None;
                            };
                            let resolved =
                                self.loader.resolve_edge(&frame.path, &edge, self.cancel)?;
                            match resolved.target {
                                ResolvedEdgeTarget::Local(target_path) => {
                                    frame.pending_edge = Some(PendingEdge {
                                        edge,
                                        type_overlay: resolved.type_overlay,
                                        flavor: resolved.flavor,
                                    });
                                    break Some(target_path);
                                }
                                ResolvedEdgeTarget::External(specifier) => {
                                    frame.dependencies.push(ModuleEdge {
                                        kind: edge.kind,
                                        flavor: resolved.flavor,
                                        mode: edge.mode,
                                        specifier: edge.specifier,
                                        target: ModuleTarget::External(specifier),
                                        type_target: None,
                                        range: edge.range,
                                    });
                                }
                            }
                        }
                    };

                    if let Some(target_path) = descend {
                        resume = Resume::Enter(target_path);
                        continue;
                    }

                    let frame = stack
                        .pop()
                        .expect("finished module must have a frame on the stack");
                    let source_id = frame.source_id;
                    self.modules.push(ResolvedModule {
                        identity: SourceIdentity::new(source_id, Arc::from(frame.path)),
                        script_kind: frame.script_kind,
                        source: frame.source,
                        jsx_plan: frame.jsx_plan,
                        dependencies: Arc::from(frame.dependencies),
                    });

                    let Some(parent) = stack.last_mut() else {
                        return Ok(source_id);
                    };
                    let pending = parent
                        .pending_edge
                        .take()
                        .expect("finished child always completes a parent local edge");
                    let dependency_index = parent.dependencies.len();
                    parent.dependencies.push(ModuleEdge {
                        kind: pending.edge.kind,
                        flavor: pending.flavor,
                        mode: pending.edge.mode,
                        specifier: pending.edge.specifier,
                        target: ModuleTarget::Local(source_id),
                        type_target: None,
                        range: pending.edge.range,
                    });
                    if let Some(path) = pending.type_overlay {
                        self.type_overlays
                            .push((parent.source_id, dependency_index, path.clone()));
                        self.overlay_worklist.push(path);
                    }
                    resume = Resume::Advance;
                }
            }
        }
    }
}
fn cancelled_load(path: &Path) -> ProgramLoadError {
    ProgramLoadError::Cancelled {
        path: path.to_path_buf(),
        source: Cancelled,
    }
}

fn check_load_cancel(cancel: &CancellationToken, path: &Path) -> Result<(), ProgramLoadError> {
    cancel.check().map_err(|_| cancelled_load(path))
}

#[derive(Clone, Debug)]
struct UnresolvedEdge {
    kind: ModuleEdgeKind,
    mode: ResolutionMode,
    specifier: Arc<str>,
    range: TextRange,
}

fn collect_edges(
    source: &SourceFile,
    ambient: ResolutionMode,
) -> Result<Vec<UnresolvedEdge>, TextRange> {
    let mut edges = Vec::new();
    for statement in source.statements() {
        match statement.data() {
            Statement::Import(import) => {
                let kind = if import_is_type_only(import) {
                    ModuleEdgeKind::TypeOnly
                } else {
                    ModuleEdgeKind::StaticRuntime
                };
                push_literal_edge(source, &mut edges, kind, ambient, &import.source)?;
            }
            Statement::ImportEquals(import) => {
                if let crate::syntax::ExternalModuleReference::Require(specifier) =
                    &import.reference
                {
                    let kind = if import.is_type_only {
                        ModuleEdgeKind::TypeOnly
                    } else {
                        ModuleEdgeKind::StaticRuntime
                    };
                    push_literal_edge(
                        source,
                        &mut edges,
                        kind,
                        ResolutionMode::Require,
                        specifier,
                    )?;
                }
            }
            Statement::Export(ExportDeclaration::All(export)) => {
                let kind = if export.type_only {
                    ModuleEdgeKind::TypeOnly
                } else {
                    ModuleEdgeKind::StaticRuntime
                };
                push_literal_edge(source, &mut edges, kind, ambient, &export.source)?;
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                type_only,
                specifiers,
                source: Some(module),
                ..
            })) => {
                let only_types = *type_only
                    || (!specifiers.is_empty()
                        && specifiers.iter().all(|specifier| {
                            specifier.data().mode == ExportSpecifierMode::TypeOnly
                        }));
                push_literal_edge(
                    source,
                    &mut edges,
                    if only_types {
                        ModuleEdgeKind::TypeOnly
                    } else {
                        ModuleEdgeKind::StaticRuntime
                    },
                    ambient,
                    module,
                )?;
            }
            _ => {}
        }
    }
    let ill_formed = {
        let mut collector = DynamicEdgeCollector {
            source,
            edges: &mut edges,
            ambient,
            ill_formed: None,
        };
        collector.scan_statements(source.statements());
        collector.ill_formed
    };
    if let Some(range) = ill_formed {
        return Err(range);
    }
    let tokens: Vec<_> = source
        .tokens()
        .iter()
        .filter(|token| {
            !matches!(
                token.kind(),
                TokenKind::Whitespace
                    | TokenKind::LineComment
                    | TokenKind::BlockComment
                    | TokenKind::Shebang
            )
        })
        .collect();
    for window in tokens.windows(3) {
        if window[0].kind() != TokenKind::KwImport
            || window[1].kind() != TokenKind::LParen
            || window[2].kind() != TokenKind::StringLiteral
            || edges.iter().any(|edge| edge.range == window[2].range())
        {
            continue;
        }
        let Some(value) = source.token_text(window[2]).and_then(unquote) else {
            continue;
        };
        let specifier = value.to_utf8_strict().map_err(|_| window[2].range())?;
        edges.push(UnresolvedEdge {
            kind: ModuleEdgeKind::TypeOnly,
            mode: ambient,
            specifier: Arc::from(specifier),
            range: window[2].range(),
        });
    }
    Ok(edges)
}

struct DynamicEdgeCollector<'a> {
    source: &'a SourceFile,
    edges: &'a mut Vec<UnresolvedEdge>,
    ambient: ResolutionMode,
    ill_formed: Option<TextRange>,
}

impl DynamicEdgeCollector<'_> {
    fn push_literal_edge(
        &mut self,
        kind: ModuleEdgeKind,
        literal: &crate::syntax::StringLiteralNode,
    ) {
        if self.ill_formed.is_none() {
            self.ill_formed =
                push_literal_edge(self.source, self.edges, kind, self.ambient, literal).err();
        }
    }

    fn scan_statements(&mut self, statements: &[crate::syntax::Stmt]) {
        for statement in statements {
            self.scan_statement(statement);
        }
    }

    fn scan_statement(&mut self, statement: &crate::syntax::Stmt) {
        use crate::syntax::{ExportDefaultValue, ForInitializer, Statement};

        match statement.data() {
            Statement::Variable(declaration) => {
                for declarator in &declaration.declarations {
                    self.scan_pattern(&declarator.data().binding);
                    if let Some(initializer) = &declarator.data().initializer {
                        self.scan_expression(initializer);
                    }
                }
            }
            Statement::Function(declaration) => self.scan_function(&declaration.function),
            Statement::Class(class) => self.scan_class(class),
            Statement::Enum(declaration) => {
                for member in &declaration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.scan_expression(initializer);
                    }
                }
            }
            Statement::Namespace(namespace) => {
                self.scan_statements(&namespace.body.data().statements)
            }
            Statement::Declare(inner)
            | Statement::Labeled(crate::syntax::LabeledStatement { body: inner, .. }) => {
                self.scan_statement(inner)
            }
            Statement::Block(block) => self.scan_statements(&block.data().statements),
            Statement::Expression(expression) => self.scan_expression(&expression.expression),
            Statement::If(value) => {
                self.scan_expression(&value.test);
                self.scan_statement(&value.consequent);
                if let Some(alternate) = &value.alternate {
                    self.scan_statement(alternate);
                }
            }
            Statement::Switch(value) => {
                self.scan_expression(&value.discriminant);
                for case in &value.cases {
                    if let Some(test) = &case.data().test {
                        self.scan_expression(test);
                    }
                    self.scan_statements(&case.data().consequent);
                }
            }
            Statement::For(value) => {
                if let Some(initializer) = &value.initializer {
                    match initializer {
                        ForInitializer::Variable(declaration) => {
                            for declarator in &declaration.declarations {
                                self.scan_pattern(&declarator.data().binding);
                                if let Some(initializer) = &declarator.data().initializer {
                                    self.scan_expression(initializer);
                                }
                            }
                        }
                        ForInitializer::Expression(expression) => self.scan_expression(expression),
                    }
                }
                if let Some(test) = &value.test {
                    self.scan_expression(test);
                }
                if let Some(update) = &value.update {
                    self.scan_expression(update);
                }
                self.scan_statement(&value.body);
            }
            Statement::ForIn(value) => {
                self.scan_for_binding(&value.binding);
                self.scan_expression(&value.object);
                self.scan_statement(&value.body);
            }
            Statement::ForOf(value) => {
                self.scan_for_binding(&value.binding);
                self.scan_expression(&value.iterable);
                self.scan_statement(&value.body);
            }
            Statement::While(value) => {
                self.scan_expression(&value.test);
                self.scan_statement(&value.body);
            }
            Statement::DoWhile(value) => {
                self.scan_statement(&value.body);
                self.scan_expression(&value.test);
            }
            Statement::Try(value) => {
                self.scan_statements(&value.block.data().statements);
                if let Some(handler) = &value.handler {
                    if let Some(binding) = &handler.data().binding {
                        self.scan_pattern(binding);
                    }
                    self.scan_statements(&handler.data().body.data().statements);
                }
                if let Some(finalizer) = &value.finalizer {
                    self.scan_statements(&finalizer.data().statements);
                }
            }
            Statement::With(value) => {
                self.scan_expression(&value.object);
                self.scan_statement(&value.body);
            }
            Statement::Return(value) => {
                if let Some(argument) = &value.argument {
                    self.scan_expression(argument);
                }
            }
            Statement::Throw(value) => self.scan_expression(&value.argument),
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => self.scan_statement(inner),
            Statement::Export(ExportDeclaration::Default(value)) => match &value.value {
                ExportDefaultValue::Function(function) => self.scan_function(function),
                ExportDefaultValue::Class(class) => self.scan_class(class),
                ExportDefaultValue::Expression(expression) => self.scan_expression(expression),
                ExportDefaultValue::Interface(_) => {}
                ExportDefaultValue::Missing(_) => {}
            },
            Statement::Export(ExportDeclaration::Assignment(expression)) => {
                self.scan_expression(expression)
            }
            _ => {}
        }
    }

    fn scan_for_binding(&mut self, binding: &crate::syntax::ForBinding) {
        match binding {
            crate::syntax::ForBinding::Variable(declaration) => {
                for declarator in &declaration.declarations {
                    self.scan_pattern(&declarator.data().binding);
                    if let Some(initializer) = &declarator.data().initializer {
                        self.scan_expression(initializer);
                    }
                }
            }
            crate::syntax::ForBinding::Target(target) => self.scan_target(target),
        }
    }

    fn scan_parameters(&mut self, parameters: &[crate::syntax::ParameterNode]) {
        for parameter in parameters {
            self.scan_decorators(&parameter.data().decorators);
            self.scan_pattern(&parameter.data().binding);
            if let Some(initializer) = &parameter.data().initializer {
                self.scan_expression(initializer);
            }
        }
    }

    fn scan_decorators(&mut self, decorators: &[crate::syntax::DecoratorNode]) {
        for decorator in decorators {
            self.scan_expression(&decorator.data().expression);
        }
    }

    fn scan_pattern(&mut self, pattern: &crate::syntax::Pattern) {
        use crate::syntax::{ArrayBindingElement, BindingPattern, PropertyName};
        match pattern.data() {
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    if let PropertyName::Computed(expression) = &property.name {
                        self.scan_expression(expression);
                    }
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                    self.scan_pattern(&property.binding);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(inner) = element {
                        self.scan_pattern(inner);
                    }
                }
            }
            BindingPattern::Rest(rest) => self.scan_pattern(&rest.argument),
            BindingPattern::Assignment(value) => {
                self.scan_pattern(&value.left);
                self.scan_expression(&value.right);
            }
            BindingPattern::Identifier(_) | BindingPattern::Missing(_) => {}
        }
    }

    fn scan_function(&mut self, function: &crate::syntax::FunctionLike) {
        self.scan_parameters(&function.parameters);
        if let Some(body) = &function.body {
            match body {
                crate::syntax::FunctionBody::Block(block) => {
                    self.scan_statements(&block.data().statements)
                }
                crate::syntax::FunctionBody::Expression(expression) => {
                    self.scan_expression(expression)
                }
                crate::syntax::FunctionBody::Missing(_) => {}
            }
        }
    }

    fn scan_class(&mut self, class: &crate::syntax::ClassDeclaration) {
        use crate::syntax::{ClassMember, PropertyName};
        self.scan_decorators(&class.decorators);
        if let Some(heritage) = &class.extends {
            self.scan_expression(&heritage.expression);
        }
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(value) => {
                    self.scan_decorators(&value.decorators);
                    self.scan_parameters(&value.parameters);
                    self.scan_statements(&value.body.data().statements);
                }
                ClassMember::Method(value) => {
                    self.scan_decorators(&value.function.decorators);
                    if let PropertyName::Computed(expression) = &value.name {
                        self.scan_expression(expression);
                    }
                    self.scan_function(&value.function);
                }
                ClassMember::Property(value) => {
                    self.scan_decorators(&value.decorators);
                    if let PropertyName::Computed(expression) = &value.name {
                        self.scan_expression(expression);
                    }
                    if let Some(initializer) = &value.initializer {
                        self.scan_expression(initializer);
                    }
                }
                ClassMember::AutoAccessor(value) => {
                    self.scan_decorators(&value.decorators);
                    if let PropertyName::Computed(expression) = &value.name {
                        self.scan_expression(expression);
                    }
                    if let Some(initializer) = &value.initializer {
                        self.scan_expression(initializer);
                    }
                }
                ClassMember::StaticBlock(block) => self.scan_statements(&block.data().statements),
                ClassMember::IndexSignature(_) | ClassMember::Missing(_) => {}
            }
        }
    }

    fn scan_expression(&mut self, expression: &crate::syntax::Expr) {
        use crate::syntax::{
            ArrayElement, Expression, Literal, MemberProperty, ObjectMember, PropertyName,
        };
        match expression.data() {
            Expression::Template(value) => {
                for expression in &value.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::TaggedTemplate(value) => {
                self.scan_expression(&value.tag);
                for expression in &value.template.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::Array(value) => {
                for element in &value.elements {
                    match element {
                        ArrayElement::Expression(value) => self.scan_expression(value),
                        ArrayElement::Spread(value) => self.scan_expression(&value.argument),
                        _ => {}
                    }
                }
            }
            Expression::Object(value) => {
                for member in &value.members {
                    match member.data() {
                        ObjectMember::Property(value) => {
                            if let PropertyName::Computed(key) = &value.name {
                                self.scan_expression(key);
                            }
                            self.scan_expression(&value.value);
                        }
                        ObjectMember::Method(value) => {
                            if let PropertyName::Computed(key) = &value.name {
                                self.scan_expression(key);
                            }
                            self.scan_function(&value.function);
                        }
                        ObjectMember::Spread(value) => self.scan_expression(&value.argument),
                        ObjectMember::Missing(_) => {}
                    }
                }
            }
            Expression::Function(value) => self.scan_function(&value.function),
            Expression::Class(value) => self.scan_class(&value.class),
            Expression::Arrow(value) => {
                self.scan_parameters(&value.parameters);
                match &value.body {
                    crate::syntax::FunctionBody::Block(block) => {
                        self.scan_statements(&block.data().statements)
                    }
                    crate::syntax::FunctionBody::Expression(value) => self.scan_expression(value),
                    crate::syntax::FunctionBody::Missing(_) => {}
                }
            }
            Expression::Call(value) => {
                self.scan_expression(&value.callee);
                self.scan_arguments(&value.arguments);
            }
            Expression::New(value) => {
                self.scan_expression(&value.callee);
                self.scan_arguments(&value.arguments);
            }
            Expression::Member(value) => {
                self.scan_expression(&value.object);
                if let MemberProperty::Computed(value) = &value.property {
                    self.scan_expression(value);
                }
            }
            Expression::Await(value) => self.scan_expression(&value.argument),
            Expression::Yield(value) => {
                if let Some(argument) = &value.argument {
                    self.scan_expression(argument);
                }
            }
            Expression::Unary(value) => self.scan_expression(&value.argument),
            Expression::Update(value) => self.scan_target(&value.argument),
            Expression::Binary(value) => {
                self.scan_expression(&value.left);
                self.scan_expression(&value.right);
            }
            Expression::Logical(value) => {
                self.scan_expression(&value.left);
                self.scan_expression(&value.right);
            }
            Expression::Conditional(value) => {
                self.scan_expression(&value.test);
                self.scan_expression(&value.consequent);
                self.scan_expression(&value.alternate);
            }
            Expression::Assignment(value) => {
                self.scan_target(&value.left);
                self.scan_expression(&value.right);
            }
            Expression::Sequence(value) => {
                for expression in &value.expressions {
                    self.scan_expression(expression);
                }
            }
            Expression::Parenthesized(value) => self.scan_expression(value),
            Expression::As(value) => self.scan_expression(&value.expression),
            Expression::Satisfies(value) => self.scan_expression(&value.expression),
            Expression::TypeAssertion(value) => self.scan_expression(&value.expression),
            Expression::NonNull(value) => self.scan_expression(&value.expression),
            Expression::Import(value) => {
                if let Expression::Literal(Literal::String(literal)) = value.source.data() {
                    self.push_literal_edge(ModuleEdgeKind::DynamicRuntime, literal);
                }
                self.scan_expression(&value.source);
                if let Some(options) = &value.options {
                    self.scan_expression(options);
                }
            }
            Expression::JsxElement(value) => {
                self.scan_jsx_attributes(&value.opening.data().attributes);
                self.scan_jsx_children(&value.children);
            }
            Expression::JsxSelfClosingElement(value) => {
                self.scan_jsx_attributes(&value.attributes);
            }
            Expression::JsxFragment(value) => self.scan_jsx_children(&value.children),
            Expression::Identifier(_)
            | Expression::This
            | Expression::Super
            | Expression::Literal(_)
            | Expression::Meta(_)
            | Expression::Missing(_) => {}
        }
    }

    fn scan_jsx_attributes(&mut self, attributes: &[crate::syntax::JsxAttributeItem]) {
        for entry in attributes {
            match entry {
                crate::syntax::JsxAttributeItem::Attribute(attribute) => {
                    if let Some(crate::syntax::JsxAttributeInitializer::Expression(container)) =
                        &attribute.data().initializer
                        && let Some(expression) = &container.data().expression
                    {
                        self.scan_expression(expression);
                    }
                }
                crate::syntax::JsxAttributeItem::Spread(spread) => {
                    self.scan_expression(&spread.data().expression);
                }
            }
        }
    }

    fn scan_jsx_children(&mut self, children: &[crate::syntax::JsxChild]) {
        for child in children {
            match child {
                crate::syntax::JsxChild::ExpressionContainer(container) => {
                    if let Some(expression) = &container.data().expression {
                        self.scan_expression(expression);
                    }
                }
                crate::syntax::JsxChild::Spread(spread) => {
                    self.scan_expression(&spread.data().expression);
                }
                crate::syntax::JsxChild::Element(expression) => self.scan_expression(expression),
                crate::syntax::JsxChild::Text(_) => {}
            }
        }
    }

    fn scan_arguments(&mut self, arguments: &[crate::syntax::CallArgument]) {
        for argument in arguments {
            match argument {
                crate::syntax::CallArgument::Expression(value) => self.scan_expression(value),
                crate::syntax::CallArgument::Spread(value) => self.scan_expression(&value.argument),
                crate::syntax::CallArgument::Missing(_) => {}
            }
        }
    }

    fn scan_target(&mut self, target: &crate::syntax::AssignmentTargetNode) {
        use crate::syntax::{
            AssignmentArrayElement, AssignmentTarget, MemberProperty, PropertyName,
        };
        match target.data() {
            AssignmentTarget::Member(value) => {
                self.scan_expression(&value.object);
                if let MemberProperty::Computed(value) = &value.property {
                    self.scan_expression(value);
                }
            }
            AssignmentTarget::Object(value) => {
                for property in &value.properties {
                    if let PropertyName::Computed(key) = &property.name {
                        self.scan_expression(key);
                    }
                    if let Some(initializer) = &property.initializer {
                        self.scan_expression(initializer);
                    }
                    self.scan_target(&property.target);
                }
            }
            AssignmentTarget::Array(value) => {
                for element in &value.elements {
                    if let AssignmentArrayElement::Target(value) = element {
                        self.scan_target(value);
                    }
                }
            }
            AssignmentTarget::Identifier(_) | AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(operand) => {
                self.scan_expression(operand);
            }
        }
    }
}

fn import_clause_is_type_only(clause: Option<&crate::syntax::ImportClause>) -> bool {
    let Some(clause) = clause else {
        return false;
    };
    clause.default.is_none()
        && matches!(
            &clause.binding,
            Some(ImportBinding::Named(specifiers))
                if !specifiers.is_empty()
                    && specifiers.iter().all(|specifier| {
                        specifier.data().mode == ImportSpecifierMode::TypeOnly
                    })
        )
}

fn import_is_type_only(import: &crate::syntax::ImportDeclaration) -> bool {
    import.type_only || import_clause_is_type_only(import.clause.as_ref())
}

fn push_literal_edge(
    source: &SourceFile,
    edges: &mut Vec<UnresolvedEdge>,
    kind: ModuleEdgeKind,
    mode: ResolutionMode,
    literal: &crate::syntax::StringLiteralNode,
) -> Result<(), TextRange> {
    let Some(value) = source.token_text(literal.data().token()).and_then(unquote) else {
        return Ok(());
    };
    let specifier = value.to_utf8_strict().map_err(|_| literal.range())?;
    edges.push(UnresolvedEdge {
        kind,
        mode,
        specifier: Arc::from(specifier),
        range: literal.range(),
    });
    Ok(())
}

pub(crate) fn unquote(text: &str) -> Option<EcmaString> {
    let quote = text.as_bytes().first().copied()?;
    if !matches!(quote, b'\'' | b'"') || text.as_bytes().last().copied() != Some(quote) {
        return None;
    }
    let body = &text[1..text.len() - 1];
    let bytes = body.as_bytes();
    let mut output = EcmaStringBuilder::with_capacity(body.encode_utf16().count());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'\\' {
            let character = body[index..].chars().next()?;
            output.push_code_point(u32::from(character)).ok()?;
            index += character.len_utf8();
            continue;
        }
        index += 1;
        let escaped = *bytes.get(index)?;
        index += 1;
        match escaped {
            b'b' => output.push_unit(0x0008),
            b'f' => output.push_unit(0x000C),
            b'n' => output.push_unit(u16::from(b'\n')),
            b'r' => output.push_unit(u16::from(b'\r')),
            b't' => output.push_unit(u16::from(b'\t')),
            b'v' => output.push_unit(0x000B),
            b'0' => output.push_unit(0),
            b'\n' => {}
            b'\r' => {
                if bytes.get(index) == Some(&b'\n') {
                    index += 1;
                }
            }
            b'x' => {
                let value = parse_hex(bytes.get(index..index + 2)?)?;
                output.push_unit(value as u16);
                index += 2;
            }
            b'u' if bytes.get(index) == Some(&b'{') => {
                let end = bytes[index + 1..].iter().position(|byte| *byte == b'}')? + index + 1;
                let value = parse_hex(bytes.get(index + 1..end)?)?;
                output.push_code_point(value).ok()?;
                index = end + 1;
            }
            b'u' => {
                let value = parse_hex(bytes.get(index..index + 4)?)?;
                output.push_unit(value as u16);
                index += 4;
            }
            _ if escaped.is_ascii() => output.push_unit(u16::from(escaped)),
            _ => {
                let character = body[index - 1..].chars().next()?;
                output.push_code_point(u32::from(character)).ok()?;
                index += character.len_utf8() - 1;
            }
        }
    }
    Some(output.finish())
}

fn parse_hex(bytes: &[u8]) -> Option<u32> {
    if bytes.is_empty() {
        return None;
    }
    bytes.iter().try_fold(0_u32, |value, byte| {
        char::from(*byte)
            .to_digit(16)
            .map(|digit| value * 16 + digit)
    })
}

fn script_kind(path: &Path) -> Option<ScriptKind> {
    match path.extension()?.to_str()? {
        "ts" | "mts" | "cts" => Some(ScriptKind::TypeScript),
        "tsx" => Some(ScriptKind::TypeScriptReact),
        "js" | "mjs" | "cjs" => Some(ScriptKind::JavaScript),
        "jsx" => Some(ScriptKind::JavaScriptReact),
        "json" => Some(ScriptKind::Json),
        _ => None,
    }
}

fn is_declaration_path(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    name.ends_with(".d.ts") || name.ends_with(".d.mts") || name.ends_with(".d.cts")
}

fn pattern_capture<'a>(pattern: &str, specifier: &'a str) -> Option<&'a str> {
    let Some(star) = pattern.find('*') else {
        return (pattern == specifier).then_some("");
    };
    let (prefix, suffix_with_star) = pattern.split_at(star);
    let suffix = &suffix_with_star[1..];
    specifier.strip_prefix(prefix)?.strip_suffix(suffix)
}

fn split_package_specifier(specifier: &str) -> Option<(&str, String)> {
    if specifier.is_empty() || specifier.starts_with('/') || specifier.starts_with('#') {
        return None;
    }
    let component_count = if specifier.starts_with('@') { 2 } else { 1 };
    let mut boundaries = specifier.match_indices('/').map(|(index, _)| index);
    let boundary = if component_count == 1 {
        boundaries.next()
    } else {
        boundaries.nth(1)
    };
    match boundary {
        Some(index) => Some((
            &specifier[..index],
            format!("./{}", &specifier[index + 1..]),
        )),
        None if component_count == 1 || specifier.matches('/').count() == 1 => {
            Some((specifier, ".".to_owned()))
        }
        None => None,
    }
}

fn diagnostic(
    importer: &Path,
    specifier: &str,
    kind: ModuleEdgeKind,
    range: TextRange,
) -> UnresolvedModuleDiagnostic {
    UnresolvedModuleDiagnostic {
        importer: Arc::from(importer),
        specifier: Arc::from(specifier),
        kind,
        range,
    }
}

const fn edge_kind(flavor: ResolutionFlavor) -> ModuleEdgeKind {
    match flavor {
        ResolutionFlavor::Runtime => ModuleEdgeKind::StaticRuntime,
        ResolutionFlavor::Types => ModuleEdgeKind::TypeOnly,
    }
}

/// Derives the ambient module resolution mode from the module format option.
///
/// Edges without an explicit mode — plain imports, re-exports, dynamic
/// imports, and synthetic JSX runtime demands — resolve with this mode. Only
/// `import … = require(…)` pins [`ResolutionMode::Require`] per edge.
fn ambient_resolution_mode(options: &CompilerOptions) -> ResolutionMode {
    if options
        .module()
        .is_some_and(|module| module.eq_ignore_ascii_case("commonjs"))
    {
        ResolutionMode::Require
    } else {
        ResolutionMode::Import
    }
}

/// Compiler-only identity and resolved-edge provenance for one executable module.
#[derive(Clone, Debug)]
pub struct ExecutableModuleProvenance {
    module: ModuleId,
    source: SourceIdentity,
    edges: Arc<[ModuleEdge]>,
}

impl ExecutableModuleProvenance {
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }

    #[must_use]
    pub const fn source(&self) -> &SourceIdentity {
        &self.source
    }

    /// Canonical compiler edges, including identities intentionally absent from the wire format.
    #[must_use]
    pub fn edges(&self) -> &[ModuleEdge] {
        &self.edges
    }

    pub fn type_only_edges(&self) -> impl Iterator<Item = &ModuleEdge> {
        self.edges
            .iter()
            .filter(|edge| edge.kind() == ModuleEdgeKind::TypeOnly)
    }
}

/// The compiler's sole executable product: one verified wire program plus non-wire provenance.
#[derive(Clone, Debug)]
pub struct ExecutableProgram {
    wire: BytecodeProgram<Verified>,
    provenance: Vec<ExecutableModuleProvenance>,
}

impl ExecutableProgram {
    #[must_use]
    pub const fn wire(&self) -> &BytecodeProgram<Verified> {
        &self.wire
    }

    #[must_use]
    pub fn provenance(&self) -> &[ExecutableModuleProvenance] {
        &self.provenance
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramLowerPhase {
    Frontend,
    Metadata,
    Module,
    Link,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramLowerErrorKind {
    Cancelled(Cancelled),
    FrontendEntrypointMismatch {
        resolved: SourceId,
        frontend: SourceId,
    },
    MissingFrontend {
        source: SourceId,
    },
    UnexpectedFrontend {
        source: SourceId,
    },
    InvalidModuleName,
    IllFormedMetadataString,
    MissingRuntimeEdge {
        specifier: String,
    },
    ConflictingRuntimeEdge {
        specifier: String,
    },
    Lower(LowerError),
    Link(ProgramVerifyError),
    UnsupportedJsxMode {
        mode: JsxEmit,
    },
}

/// A whole-program lowering failure anchored to a canonical module path and phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramLowerError {
    pub module: PathBuf,
    pub phase: ProgramLowerPhase,
    pub kind: ProgramLowerErrorKind,
}

impl fmt::Display for ProgramLowerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "program lowering failed in {} during {:?}: {:?}",
            self.module.display(),
            self.phase,
            self.kind
        )
    }
}

impl std::error::Error for ProgramLowerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.kind {
            ProgramLowerErrorKind::Cancelled(error) => Some(error),
            ProgramLowerErrorKind::Lower(error) => Some(error),
            ProgramLowerErrorKind::Link(error) => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone)]
struct RawEdge {
    specifier: String,
    target: EdgeTarget,
    external_identity: Option<String>,
    kind: EdgeKind,
}

#[derive(Clone)]
enum RawBindingKind {
    Hoisted,
    Lexical,
    Imported { edge: EdgeId, name: String },
    Namespace { edge: EdgeId },
    ImportEquals { edge: EdgeId },
}

#[derive(Clone)]
struct RawBinding {
    name: String,
    kind: RawBindingKind,
}

#[derive(Clone)]
enum RawExportSource {
    Local(String),
    Indirect { edge: EdgeId, name: String },
}

#[derive(Clone)]
struct RawExport {
    name: String,
    source: RawExportSource,
}

struct RawModule {
    name: String,
    edges: Vec<RawEdge>,
    bindings: Vec<RawBinding>,
    exports: Vec<RawExport>,
    stars: Vec<EdgeId>,
    jsx_plan: Option<JsxSourceDesugarPlan>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ExportOrigin {
    Local(ModuleId, String),
    Indirect(ModuleId, String),
    External(String, String),
}

/// Lowers one canonical resolved program and its matching frontend products.
///
/// Static linkage becomes live metadata only. Dynamic imports remain instructions
/// backed by dynamic-capable edges.
///
/// # Errors
/// Returns a path- and phase-typed failure for frontend mismatch, metadata construction,
/// module lowering/verification, or final program linking.
pub fn lower_program(
    resolved: &ResolvedProgram,
    frontend: &ProgramFrontendOutput,
    options: LowerOptions,
) -> Result<ExecutableProgram, ProgramLowerError> {
    lower_program_with_cancel(resolved, frontend, options, &CancellationToken::new())
}

/// Lowers one canonical resolved program with cooperative cancellation.
pub fn lower_program_with_cancel(
    resolved: &ResolvedProgram,
    frontend: &ProgramFrontendOutput,
    options: LowerOptions,
    cancel: &CancellationToken,
) -> Result<ExecutableProgram, ProgramLowerError> {
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Frontend,
    )?;
    if frontend.entrypoint_id() != resolved.entrypoint_id() {
        return Err(program_lower_error(
            resolved.entrypoint().path(),
            ProgramLowerPhase::Frontend,
            ProgramLowerErrorKind::FrontendEntrypointMismatch {
                resolved: resolved.entrypoint_id(),
                frontend: frontend.entrypoint_id(),
            },
        ));
    }
    if let JsxRoutingDecision::RejectPreservedNative =
        resolved.jsx_routing_decision(ProgramOutputKind::NativeExecutable)
    {
        return Err(program_lower_error(
            resolved.entrypoint().path(),
            ProgramLowerPhase::Frontend,
            ProgramLowerErrorKind::UnsupportedJsxMode {
                mode: resolved
                    .jsx()
                    .expect("native JSX rejection requires a configured JSX mode"),
            },
        ));
    }
    for output in frontend.modules() {
        check_lower_cancel(
            cancel,
            resolved.entrypoint().path(),
            ProgramLowerPhase::Frontend,
        )?;
        let source = output.source_file().source_id();
        if resolved.module(source).is_none() {
            return Err(program_lower_error(
                resolved.entrypoint().path(),
                ProgramLowerPhase::Frontend,
                ProgramLowerErrorKind::UnexpectedFrontend { source },
            ));
        }
    }

    let module_ids: HashMap<_, _> = resolved
        .modules()
        .iter()
        .enumerate()
        .map(|(index, module)| (module.source_id(), ModuleId::new(index as u32)))
        .collect();
    let mut raw_modules = Vec::with_capacity(resolved.modules().len());
    for module in resolved.modules() {
        check_lower_cancel(cancel, module.path(), ProgramLowerPhase::Metadata)?;
        let output = frontend.module(module.source_id()).ok_or_else(|| {
            program_lower_error(
                module.path(),
                ProgramLowerPhase::Frontend,
                ProgramLowerErrorKind::MissingFrontend {
                    source: module.source_id(),
                },
            )
        })?;
        let name = normalized_module_name(resolved.root(), module.path()).ok_or_else(|| {
            program_lower_error(
                module.path(),
                ProgramLowerPhase::Metadata,
                ProgramLowerErrorKind::InvalidModuleName,
            )
        })?;
        raw_modules.push(collect_raw_module(
            module,
            output.source_file(),
            output.semantic_model().enum_facts(),
            output.semantic_model().namespace_facts(),
            name,
            &module_ids,
        )?);
        check_lower_cancel(cancel, module.path(), ProgramLowerPhase::Metadata)?;
    }
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Metadata,
    )?;
    resolve_import_equals_bindings(&mut raw_modules);
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Metadata,
    )?;
    expand_star_exports(&mut raw_modules);
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Metadata,
    )?;

    let mut linked_modules = Vec::with_capacity(raw_modules.len());
    let mut provenance = Vec::with_capacity(raw_modules.len());
    for (index, (resolved_module, raw)) in resolved
        .modules()
        .iter()
        .zip(raw_modules.iter())
        .enumerate()
    {
        check_lower_cancel(cancel, resolved_module.path(), ProgramLowerPhase::Module)?;
        let output = frontend
            .module(resolved_module.source_id())
            .expect("frontend presence checked above");
        let file = output.source_file();
        let strings = linkage_strings(raw);
        let code = lower::assemble_program_module(
            file,
            options,
            &strings,
            raw.jsx_plan.as_ref(),
            output.semantic_model().enum_facts(),
            output.semantic_model().namespace_facts(),
        )
        .and_then(|module| {
            module.verify().map_err(|error| LowerError {
                source: file.source_id(),
                range: file.range(),
                kind: lower::LowerErrorKind::Verify(error),
            })
        })
        .map_err(|error| {
            program_lower_error(
                resolved_module.path(),
                ProgramLowerPhase::Module,
                ProgramLowerErrorKind::Lower(error),
            )
        })?;
        check_lower_cancel(cancel, resolved_module.path(), ProgramLowerPhase::Module)?;
        linked_modules.push(materialize_program_module(code, raw));
        provenance.push(ExecutableModuleProvenance {
            module: ModuleId::new(index as u32),
            source: resolved_module.identity().clone(),
            edges: Arc::from(resolved_module.dependencies()),
        });
    }
    let entry = module_ids[&resolved.entrypoint_id()];
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Link,
    )?;
    let wire = BytecodeProgram::link(linked_modules, entry).map_err(|error| {
        let path = error
            .module
            .and_then(|module| resolved.modules().get(module.get() as usize))
            .map_or_else(|| resolved.entrypoint().path(), ResolvedModule::path);
        program_lower_error(
            path,
            ProgramLowerPhase::Link,
            ProgramLowerErrorKind::Link(error),
        )
    })?;
    check_lower_cancel(
        cancel,
        resolved.entrypoint().path(),
        ProgramLowerPhase::Link,
    )?;
    Ok(ExecutableProgram { wire, provenance })
}
fn check_lower_cancel(
    cancel: &CancellationToken,
    path: &Path,
    phase: ProgramLowerPhase,
) -> Result<(), ProgramLowerError> {
    cancel
        .check()
        .map_err(|error| program_lower_error(path, phase, ProgramLowerErrorKind::Cancelled(error)))
}

fn collect_raw_module(
    module: &ResolvedModule,
    file: &SourceFile,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
    name: String,
    module_ids: &HashMap<SourceId, ModuleId>,
) -> Result<RawModule, ProgramLowerError> {
    let mut edges: Vec<RawEdge> = Vec::new();
    let mut edge_ids: HashMap<String, EdgeId> = HashMap::new();
    for dependency in module
        .dependencies()
        .iter()
        .filter(|edge| edge.kind() != ModuleEdgeKind::TypeOnly)
    {
        let kind = match dependency.kind() {
            ModuleEdgeKind::StaticRuntime => EdgeKind::Static,
            ModuleEdgeKind::DynamicRuntime => EdgeKind::Dynamic,
            ModuleEdgeKind::TypeOnly => unreachable!("type-only edges were filtered"),
        };
        let (target, external_identity) = match dependency.target() {
            ModuleTarget::Local(source) => (EdgeTarget::Local(module_ids[source]), None),
            ModuleTarget::External(identity) => (EdgeTarget::External, Some(identity.to_string())),
        };
        if let Some(existing) = edge_ids.get(dependency.specifier()).copied() {
            let edge: &mut RawEdge = &mut edges[existing.get() as usize];
            if edge.target != target || edge.external_identity != external_identity {
                return Err(program_lower_error(
                    module.path(),
                    ProgramLowerPhase::Metadata,
                    ProgramLowerErrorKind::ConflictingRuntimeEdge {
                        specifier: dependency.specifier().to_owned(),
                    },
                ));
            }
            edge.kind = edge.kind.union(kind);
            continue;
        }
        let id = EdgeId::new(edges.len() as u32);
        edge_ids.insert(dependency.specifier().to_owned(), id);
        edges.push(RawEdge {
            specifier: dependency.specifier().to_owned(),
            target,
            external_identity,
            kind,
        });
    }

    let edge = |specifier: String| {
        edge_ids.get(&specifier).copied().ok_or_else(|| {
            program_lower_error(
                module.path(),
                ProgramLowerPhase::Metadata,
                ProgramLowerErrorKind::MissingRuntimeEdge { specifier },
            )
        })
    };
    let mut bindings = Vec::new();
    let mut hoisted = Vec::new();
    lower::collect_var_names(file, file.statements(), &mut hoisted);
    bindings.extend(hoisted.into_iter().map(|name| RawBinding {
        name,
        kind: RawBindingKind::Hoisted,
    }));
    let mut exports = Vec::new();
    let mut stars = Vec::new();
    let mut exported_local_names = HashSet::new();
    for statement in file.statements() {
        collect_top_level_statement(
            module,
            file,
            enum_facts,
            namespace_facts,
            statement,
            &edge,
            &mut bindings,
            &mut exports,
            &mut stars,
            &mut exported_local_names,
        )?;
    }
    let mut hoisted_names = HashSet::new();
    bindings.retain(|binding| {
        !matches!(binding.kind, RawBindingKind::Hoisted)
            || hoisted_names.insert(binding.name.clone())
    });
    let mut binding_names: HashSet<String> = bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect();
    let mut jsx_plan = module.jsx_plan().cloned();
    if let Some(plan) = &mut jsx_plan
        && let Some(specifier) = &plan.demand.module_specifier
    {
        let edge_id = edge(specifier.to_string())?;
        let demanded: BTreeSet<_> = plan.demand.bindings.values().copied().collect();
        let mut runtime_names: BTreeMap<JsxRuntimeBinding, Arc<str>> = BTreeMap::new();
        for binding in demanded {
            let stem = format!("__bamts_jsx_{}", binding.export_name());
            let mut local = stem.clone();
            let mut suffix = 2_u32;
            while !binding_names.insert(local.clone()) {
                local = format!("{stem}_{suffix}");
                suffix += 1;
            }
            bindings.push(RawBinding {
                name: local.clone(),
                kind: RawBindingKind::Imported {
                    edge: edge_id,
                    name: binding.export_name().to_owned(),
                },
            });
            runtime_names.insert(binding, Arc::from(local));
        }
        plan.rebind_runtime_names(&runtime_names);
    }
    exports.retain(|export| match &export.source {
        RawExportSource::Local(name) => binding_names.contains(name),
        RawExportSource::Indirect { .. } => true,
    });
    Ok(RawModule {
        name,
        edges,
        bindings,
        exports,
        stars,
        jsx_plan,
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "top-level statement collection threads module binding/export accumulation state"
)]
fn collect_top_level_statement(
    module: &ResolvedModule,
    file: &SourceFile,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
    statement: &crate::syntax::Stmt,
    edge: &impl Fn(String) -> Result<EdgeId, ProgramLowerError>,
    bindings: &mut Vec<RawBinding>,
    exports: &mut Vec<RawExport>,
    stars: &mut Vec<EdgeId>,
    exported_local_names: &mut HashSet<String>,
) -> Result<(), ProgramLowerError> {
    match statement.data() {
        Statement::Import(import) if !import_is_type_only(import) => {
            // Const-enum binding elision is separate from type-only erasure: a
            // resolved const-enum named binding may omit its local runtime
            // binding while the non-type-only declaration still retains module
            // evaluation through the existing StaticRuntime raw edge
            // (side-effect-import shape). No manufactured binding is created.
            let edge_id = edge(metadata_string_literal(module, file, &import.source)?)?;
            if let Some(clause) = &import.clause {
                if let Some(default) = &clause.default {
                    bindings.push(RawBinding {
                        name: identifier(file, default),
                        kind: RawBindingKind::Imported {
                            edge: edge_id,
                            name: "default".to_owned(),
                        },
                    });
                }
                match &clause.binding {
                    Some(ImportBinding::Namespace(local)) => bindings.push(RawBinding {
                        name: identifier(file, local),
                        kind: RawBindingKind::Namespace { edge: edge_id },
                    }),
                    Some(ImportBinding::Named(specifiers)) => {
                        for specifier in specifiers {
                            if enum_facts.is_elided_import_specifier(specifier.id())
                                || specifier.data().mode == ImportSpecifierMode::TypeOnly
                            {
                                continue;
                            }
                            let specifier = specifier.data();
                            bindings.push(RawBinding {
                                name: identifier(file, &specifier.local),
                                kind: RawBindingKind::Imported {
                                    edge: edge_id,
                                    name: metadata_export_name(module, file, &specifier.imported)?,
                                },
                            });
                        }
                    }
                    None => {}
                }
            }
        }
        Statement::ImportEquals(import)
            if !import.is_type_only
                && let crate::syntax::ExternalModuleReference::Require(specifier) =
                    &import.reference =>
        {
            let edge_id = edge(metadata_string_literal(module, file, specifier)?)?;
            bindings.push(RawBinding {
                name: identifier(file, &import.local),
                kind: RawBindingKind::ImportEquals { edge: edge_id },
            });
        }
        Statement::ImportEquals(import)
            if !import.is_type_only
                && matches!(
                    &import.reference,
                    crate::syntax::ExternalModuleReference::Qualified(_)
                ) =>
        {
            bindings.push(RawBinding {
                name: identifier(file, &import.local),
                kind: RawBindingKind::Lexical,
            });
        }
        Statement::Variable(declaration)
            if matches!(declaration.kind, VariableKind::Let | VariableKind::Const) =>
        {
            for declarator in &declaration.declarations {
                let mut names = Vec::new();
                lower::collect_pattern_names(file, &declarator.data().binding, &mut names);
                bindings.extend(names.into_iter().map(|name| RawBinding {
                    name,
                    kind: RawBindingKind::Lexical,
                }));
            }
        }
        Statement::Function(declaration) => {
            if declaration.function.body.is_some()
                && let Some(name) = &declaration.function.name
            {
                bindings.push(RawBinding {
                    name: identifier(file, name),
                    kind: RawBindingKind::Hoisted,
                });
            }
        }
        Statement::Class(class) => {
            if let Some(name) = &class.name {
                let name = identifier(file, name);
                // `collect_var_names` already hoists merged namespace names, and
                // class/namespace merges share that one value slot.
                if !module_has_binding_namespace(file, namespace_facts, &name) {
                    bindings.push(RawBinding {
                        name,
                        kind: RawBindingKind::Lexical,
                    });
                }
            }
        }
        Statement::Enum(declaration) if !declaration.is_const => {
            bindings.push(RawBinding {
                name: identifier(file, &declaration.name),
                kind: RawBindingKind::Hoisted,
            });
        }
        Statement::Namespace(_) => {
            let plan = namespace_facts
                .declaration(statement.id())
                .expect("guarded namespace plan");
            if matches!(
                plan.acquisition(),
                crate::namespace_plan::ContainerAcquisition::Binding
            ) {
                let Statement::Namespace(declaration) = statement.data() else {
                    unreachable!("namespace plan belongs to namespace statement");
                };
                if let Some(identifier_node) = declaration.name.as_identifier() {
                    let name = identifier(file, identifier_node);
                    if !bindings.iter().any(|binding| binding.name == name) {
                        bindings.push(RawBinding {
                            name,
                            kind: RawBindingKind::Hoisted,
                        });
                    }
                }
            }
        }
        Statement::Export(export) => collect_export(
            module,
            file,
            enum_facts,
            namespace_facts,
            export,
            edge,
            bindings,
            exports,
            stars,
            exported_local_names,
        )?,
        _ => {}
    }
    Ok(())
}

#[expect(
    clippy::too_many_arguments,
    reason = "export collection threads module binding/export accumulation state"
)]
fn collect_export(
    module: &ResolvedModule,
    file: &SourceFile,
    enum_facts: &EnumFacts,
    namespace_facts: &NamespaceFacts,
    declaration: &ExportDeclaration,
    edge: &impl Fn(String) -> Result<EdgeId, ProgramLowerError>,
    bindings: &mut Vec<RawBinding>,
    exports: &mut Vec<RawExport>,
    stars: &mut Vec<EdgeId>,
    exported_local_names: &mut HashSet<String>,
) -> Result<(), ProgramLowerError> {
    match declaration {
        ExportDeclaration::Named(ExportNamedDeclaration::Declaration(statement)) => {
            collect_top_level_statement(
                module,
                file,
                enum_facts,
                namespace_facts,
                statement,
                edge,
                bindings,
                exports,
                stars,
                exported_local_names,
            )?;
            let has_runtime_value = match statement.data() {
                Statement::Function(declaration) => declaration.function.body.is_some(),
                Statement::Enum(declaration) => !declaration.is_const,
                Statement::Namespace(declaration) => namespace_facts
                    .declaration(statement.id())
                    .is_some_and(|plan| {
                        // Value-bearing bodies export as today. Empty
                        // `export namespace N {}` still contributes one local
                        // value export name; interface-only bodies do not.
                        plan.is_value_bearing()
                            || (matches!(
                                plan.acquisition(),
                                crate::namespace_plan::ContainerAcquisition::Binding
                            ) && declaration.body.data().statements.is_empty())
                    }),
                Statement::Declare(_) => false,
                _ => true,
            };
            if has_runtime_value {
                for name in lower::declared_names(file, statement) {
                    // Merged value declarations (namespace/namespace,
                    // class|function|enum + namespace, enum/enum) share one
                    // local export name. Specifier-form duplicates still pass
                    // through and fail link with DuplicateExport.
                    if !exported_local_names.insert(name.clone()) {
                        continue;
                    }
                    exports.push(RawExport {
                        name: name.clone(),
                        source: RawExportSource::Local(name),
                    });
                }
            }
        }
        ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
            type_only,
            specifiers,
            source,
            ..
        }) if !type_only => {
            if let Some(source) = source {
                let edge_id = edge(metadata_string_literal(module, file, source)?)?;
                for specifier in specifiers {
                    let specifier = specifier.data();
                    if specifier.mode == ExportSpecifierMode::TypeOnly {
                        continue;
                    }
                    exports.push(RawExport {
                        name: metadata_export_name(module, file, &specifier.exported)?,
                        source: RawExportSource::Indirect {
                            edge: edge_id,
                            name: metadata_export_name(module, file, &specifier.local)?,
                        },
                    });
                }
            } else {
                for specifier in specifiers {
                    let specifier = specifier.data();
                    if specifier.mode == ExportSpecifierMode::TypeOnly {
                        continue;
                    }
                    exports.push(RawExport {
                        name: metadata_export_name(module, file, &specifier.exported)?,
                        source: RawExportSource::Local(metadata_export_name(
                            module,
                            file,
                            &specifier.local,
                        )?),
                    });
                }
            }
        }
        ExportDeclaration::All(all) if !all.type_only => {
            let edge_id = edge(metadata_string_literal(module, file, &all.source)?)?;
            if let Some(exported) = &all.exported {
                let exported = metadata_export_name(module, file, exported)?;
                let binding = format!("*namespace:{exported}*");
                bindings.push(RawBinding {
                    name: binding.clone(),
                    kind: RawBindingKind::Namespace { edge: edge_id },
                });
                exports.push(RawExport {
                    name: exported,
                    source: RawExportSource::Local(binding),
                });
            } else {
                stars.push(edge_id);
            }
        }
        ExportDeclaration::Assignment(_) => {
            bindings.push(RawBinding {
                name: "*export=*".to_owned(),
                kind: RawBindingKind::Lexical,
            });
            exports.push(RawExport {
                name: "default".to_owned(),
                source: RawExportSource::Local("*export=*".to_owned()),
            });
        }
        ExportDeclaration::Default(default) => {
            let kind = match &default.value {
                ExportDefaultValue::Function(function) if function.body.is_some() => {
                    if let Some(name) = &function.name {
                        bindings.push(RawBinding {
                            name: identifier(file, name),
                            kind: RawBindingKind::Hoisted,
                        });
                    }
                    RawBindingKind::Hoisted
                }
                ExportDefaultValue::Class(class) => {
                    if let Some(name) = &class.name {
                        bindings.push(RawBinding {
                            name: identifier(file, name),
                            kind: RawBindingKind::Lexical,
                        });
                    }
                    RawBindingKind::Lexical
                }
                ExportDefaultValue::Expression(_) => RawBindingKind::Lexical,
                _ => return Ok(()),
            };
            bindings.push(RawBinding {
                name: "*default*".to_owned(),
                kind,
            });
            exports.push(RawExport {
                name: "default".to_owned(),
                source: RawExportSource::Local("*default*".to_owned()),
            });
        }
        _ => {}
    }
    Ok(())
}

/// Rewrites each `import x = require(...)` binding to its final form.
///
/// A local target that re-exports its entire value via `export =` exposes the
/// required module's value as the `default` export, so the binding becomes an
/// `Imported { name: "default" }` reference. Everything else (external modules,
/// local targets without `export =`) stays a namespace binding.
fn resolve_import_equals_bindings(modules: &mut [RawModule]) {
    let has_export_assignment: Vec<bool> = modules
        .iter()
        .map(|module| {
            module
                .bindings
                .iter()
                .any(|binding| binding.name == "*export=*")
        })
        .collect();
    for module in modules {
        for binding in &mut module.bindings {
            let edge = match &binding.kind {
                RawBindingKind::ImportEquals { edge } => *edge,
                _ => continue,
            };
            let target = module.edges[edge.get() as usize].target;
            binding.kind = match target {
                EdgeTarget::Local(target_id) if has_export_assignment[target_id.get() as usize] => {
                    RawBindingKind::Imported {
                        edge,
                        name: "default".to_owned(),
                    }
                }
                EdgeTarget::Local(_) | EdgeTarget::External => RawBindingKind::Namespace { edge },
            };
        }
    }
}

fn expand_star_exports(modules: &mut [RawModule]) {
    let explicit: Vec<BTreeSet<String>> = modules
        .iter()
        .map(|module| {
            module
                .exports
                .iter()
                .map(|export| export.name.clone())
                .collect()
        })
        .collect();
    let mut cache = HashMap::new();
    let mut additions: Vec<BTreeMap<String, BTreeSet<ExportOrigin>>> = modules
        .iter()
        .enumerate()
        .map(|(index, module)| {
            module
                .exports
                .iter()
                .map(|export| {
                    (
                        export.name.clone(),
                        BTreeSet::from([canonical_export_origin(
                            modules,
                            export_origin(ModuleId::new(index as u32), module, export),
                            &mut BTreeSet::new(),
                        )]),
                    )
                })
                .collect()
        })
        .collect();
    for (index, module) in modules.iter().enumerate() {
        for star in &module.stars {
            let EdgeTarget::Local(target) = module.edges[star.get() as usize].target else {
                continue;
            };
            let names: Vec<String> = {
                let mut names = modules[target.get() as usize]
                    .exports
                    .iter()
                    .map(|export| export.name.clone())
                    .collect::<Vec<_>>();
                names.extend(additions[target.get() as usize].keys().cloned());
                names.sort();
                names.dedup();
                names
            };
            for name in names {
                if name == "default" || explicit[index].contains(&name) {
                    continue;
                }
                let mut visited = BTreeSet::new();
                visited.insert((index, name.clone()));
                let candidates = star_export_origins(
                    modules,
                    &mut cache,
                    target.get() as usize,
                    &name,
                    &mut visited,
                );
                if !candidates.is_empty() {
                    additions[index].entry(name).or_default().extend(candidates);
                }
            }
        }
    }
    let mut selected: Vec<(usize, RawExport)> = Vec::new();
    for (index, module) in modules.iter().enumerate() {
        // Ambiguous star bindings are deliberately omitted.
        for (name, origin) in additions[index]
            .iter()
            .filter(|&(_name, candidates)| candidates.len() == 1)
            .map(|(name, candidates)| (name, candidates.first().expect("singleton candidate")))
        {
            // Explicit exports stay authoritative; do not re-materialize them via
            // cyclic star edges (that would trip link-time DuplicateExport).
            if explicit[index].contains(name) {
                continue;
            }
            let selected_edge = module.stars.iter().copied().find(|edge| {
                let EdgeTarget::Local(target) = module.edges[edge.get() as usize].target else {
                    return false;
                };
                let mut visited = BTreeSet::new();
                visited.insert((index, name.clone()));
                star_export_origins(
                    modules,
                    &mut cache,
                    target.get() as usize,
                    name,
                    &mut visited,
                )
                .contains(origin)
            });
            if let Some(edge) = selected_edge {
                selected.push((
                    index,
                    RawExport {
                        name: name.clone(),
                        source: RawExportSource::Indirect {
                            edge,
                            name: name.clone(),
                        },
                    },
                ));
            }
        }
    }
    for (index, export) in selected {
        modules[index].exports.push(export);
    }
}

fn star_export_origins(
    modules: &[RawModule],
    cache: &mut HashMap<(usize, String), BTreeSet<ExportOrigin>>,
    module_index: usize,
    name: &str,
    visited: &mut BTreeSet<(usize, String)>,
) -> BTreeSet<ExportOrigin> {
    if !visited.insert((module_index, name.to_owned())) {
        return BTreeSet::new();
    }
    if let Some(candidates) = cache.get(&(module_index, name.to_owned())) {
        return candidates.clone();
    }
    let module = &modules[module_index];
    let mut candidates = BTreeSet::new();
    if let Some(export) = module.exports.iter().find(|export| export.name == name) {
        // An explicit export ends traversal for this module; do not also collect
        // `export *` candidates (they must not compete with the explicit origin).
        candidates.insert(canonical_export_origin(
            modules,
            export_origin(ModuleId::new(module_index as u32), module, export),
            &mut BTreeSet::new(),
        ));
    } else if name != "default" {
        for star in &module.stars {
            let EdgeTarget::Local(target) = module.edges[star.get() as usize].target else {
                continue;
            };
            candidates.extend(star_export_origins(
                modules,
                cache,
                target.get() as usize,
                name,
                visited,
            ));
        }
    }
    cache.insert((module_index, name.to_owned()), candidates.clone());
    candidates
}

fn export_origin(module_id: ModuleId, module: &RawModule, export: &RawExport) -> ExportOrigin {
    match &export.source {
        RawExportSource::Local(name) => module
            .bindings
            .iter()
            .find(|binding| binding.name == *name)
            .and_then(|binding| match &binding.kind {
                RawBindingKind::Imported { edge, name } => {
                    Some(edge_export_origin(module, *edge, name))
                }
                _ => None,
            })
            .unwrap_or_else(|| ExportOrigin::Local(module_id, name.clone())),
        RawExportSource::Indirect { edge, name } => edge_export_origin(module, *edge, name),
    }
}

fn edge_export_origin(module: &RawModule, edge: EdgeId, name: &str) -> ExportOrigin {
    let edge = &module.edges[edge.get() as usize];
    match edge.target {
        EdgeTarget::Local(target) => ExportOrigin::Indirect(target, name.to_owned()),
        EdgeTarget::External => ExportOrigin::External(
            edge.external_identity
                .clone()
                .unwrap_or_else(|| edge.specifier.clone()),
            name.to_owned(),
        ),
    }
}

fn canonical_export_origin(
    modules: &[RawModule],
    origin: ExportOrigin,
    visited: &mut BTreeSet<(ModuleId, String)>,
) -> ExportOrigin {
    let ExportOrigin::Indirect(module_id, name) = &origin else {
        return origin;
    };
    if !visited.insert((*module_id, name.clone())) {
        return origin;
    }
    let module = &modules[module_id.get() as usize];
    let Some(export) = module.exports.iter().find(|export| export.name == *name) else {
        return origin;
    };
    let next = export_origin(*module_id, module, export);
    if next == origin {
        origin
    } else {
        canonical_export_origin(modules, next, visited)
    }
}

fn linkage_strings(module: &RawModule) -> Vec<String> {
    let mut strings = Vec::new();
    strings.push(module.name.clone());
    strings.extend(module.edges.iter().map(|edge| edge.specifier.clone()));
    for binding in &module.bindings {
        strings.push(binding.name.clone());
        if let RawBindingKind::Imported { name, .. } = &binding.kind {
            strings.push(name.clone());
        }
    }
    for export in &module.exports {
        strings.push(export.name.clone());
        if let RawExportSource::Indirect { name, .. } = &export.source {
            strings.push(name.clone());
        }
    }
    strings
}

fn materialize_program_module(
    code: bamts_bytecode::Module<Verified>,
    raw: &RawModule,
) -> ProgramModule<Verified> {
    let constant = |value: &str| {
        ConstantId::new(
            code.constants()
                .iter()
                .position(|constant| matches!(constant, Constant::String(text) if text.as_units().iter().copied().eq(value.encode_utf16())))
                .expect("all linkage strings were interned before verification") as u32,
        )
    };
    let binding_ids: HashMap<_, _> = raw
        .bindings
        .iter()
        .enumerate()
        .map(|(index, binding)| (binding.name.as_str(), BindingId::new(index as u32)))
        .collect();
    let name = constant(&raw.name);
    let edges = raw
        .edges
        .iter()
        .map(|edge| Edge {
            specifier: constant(&edge.specifier),
            target: edge.target,
            kind: edge.kind,
        })
        .collect();
    let bindings = raw
        .bindings
        .iter()
        .map(|binding| Binding {
            name: constant(&binding.name),
            kind: match &binding.kind {
                RawBindingKind::Hoisted => BindingKind::Hoisted,
                RawBindingKind::Lexical => BindingKind::Lexical,
                RawBindingKind::Imported { edge, name } => BindingKind::Imported {
                    edge: *edge,
                    name: constant(name),
                },
                RawBindingKind::Namespace { edge } => BindingKind::Namespace { edge: *edge },
                RawBindingKind::ImportEquals { .. } => {
                    unreachable!("import equals bindings are resolved before materialization")
                }
            },
        })
        .collect();
    let exports = raw
        .exports
        .iter()
        .map(|export| Export {
            name: constant(&export.name),
            source: match &export.source {
                RawExportSource::Local(name) => ExportSource::Local(binding_ids[name.as_str()]),
                RawExportSource::Indirect { edge, name } => ExportSource::Indirect {
                    edge: *edge,
                    name: constant(name),
                },
            },
        })
        .collect();
    ProgramModule {
        name,
        code,
        edges,
        bindings,
        exports,
    }
}

fn normalized_module_name(root: &ProjectRoot, path: &Path) -> Option<String> {
    let relative = path.strip_prefix(root.path()).ok()?;
    let mut name = String::new();
    for component in relative.components() {
        if !name.is_empty() {
            name.push('/');
        }
        name.push_str(component.as_os_str().to_str()?);
    }
    (!name.is_empty()).then_some(name)
}

fn module_has_binding_namespace(
    file: &SourceFile,
    namespace_facts: &NamespaceFacts,
    name: &str,
) -> bool {
    fn matches_namespace(
        file: &SourceFile,
        namespace_facts: &NamespaceFacts,
        statement: &crate::syntax::Stmt,
        name: &str,
    ) -> bool {
        let Statement::Namespace(declaration) = statement.data() else {
            return false;
        };
        let Some(identifier_node) = declaration.name.as_identifier() else {
            return false;
        };
        if identifier(file, identifier_node) != name {
            return false;
        }
        namespace_facts
            .declaration(statement.id())
            .is_some_and(|plan| {
                matches!(
                    plan.acquisition(),
                    crate::namespace_plan::ContainerAcquisition::Binding
                )
            })
    }

    file.statements()
        .iter()
        .any(|statement| match statement.data() {
            Statement::Namespace(_) => matches_namespace(file, namespace_facts, statement, name),
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => matches_namespace(file, namespace_facts, inner, name),
            _ => false,
        })
}

fn identifier(file: &SourceFile, node: &crate::syntax::IdentifierNode) -> String {
    file.identifier_text(node.data().token())
        .expect("parser identifier range belongs to its source")
        .into_owned()
}

fn metadata_string_literal(
    module: &ResolvedModule,
    file: &SourceFile,
    node: &crate::syntax::StringLiteralNode,
) -> Result<String, ProgramLowerError> {
    let value = file
        .token_text(node.data().token())
        .and_then(unquote)
        .ok_or_else(|| malformed_metadata_error(module))?;
    value
        .to_utf8_strict()
        .map_err(|_| malformed_metadata_error(module))
}

fn metadata_export_name(
    module: &ResolvedModule,
    file: &SourceFile,
    name: &ModuleExportName,
) -> Result<String, ProgramLowerError> {
    match name {
        ModuleExportName::Identifier(identifier_node) => Ok(identifier(file, identifier_node)),
        ModuleExportName::String(string) => metadata_string_literal(module, file, string),
        ModuleExportName::Missing(_) => Ok(String::new()),
    }
}

fn malformed_metadata_error(module: &ResolvedModule) -> ProgramLowerError {
    program_lower_error(
        module.path(),
        ProgramLowerPhase::Metadata,
        ProgramLowerErrorKind::IllFormedMetadataString,
    )
}

fn program_lower_error(
    module: &Path,
    phase: ProgramLowerPhase,
    kind: ProgramLowerErrorKind,
) -> ProgramLowerError {
    ProgramLowerError {
        module: module.to_path_buf(),
        phase,
        kind,
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::{
            Arc,
            atomic::{AtomicU64, Ordering},
        },
    };

    use super::{
        ExecutableProgram, JsxRoutingDecision, ModuleEdgeKind, ModuleTarget, ProgramLoadError,
        ProgramLoader, ProgramLowerErrorKind, ProgramLowerPhase, ProgramOutputKind,
        ResolutionFlavor, ResolutionMode, ResolvedProgram, lower_program,
        lower_program_with_cancel,
    };
    use crate::checker::ProgramCheckOptions;
    use crate::{
        lower::LowerOptions,
        pipeline::{FrontendMode, compile_program_frontend},
        project::{ProjectConfig, ProjectRoot},
        service::filesystem::{FileMetadata, FileSystem, FileSystemError, OsFileSystem},
        source::JsxEmit,
    };
    use bamts_bytecode::{
        BindingId, BindingKind, EcmaString, EdgeId, EdgeKind, EdgeTarget, ExportSource,
        Instruction, ProgramModule, ProgramVerifyErrorKind, ResolvedExport, Verified,
    };
    use bamts_cancel::CancellationToken;

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "bamts-program-{}-{}",
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

        fn loader(&self) -> ProgramLoader {
            self.loader_with_config("{}")
        }

        fn loader_with_config(&self, config_source: &str) -> ProgramLoader {
            let root = ProjectRoot::new(fs::canonicalize(&self.0).unwrap()).unwrap();
            let config =
                ProjectConfig::parse(&root, self.0.join("tsconfig.json"), config_source).unwrap();
            ProgramLoader::new(&root, config.options()).unwrap()
        }
    }
    struct CountingFileSystem {
        inner: OsFileSystem,
        shared: PathBuf,
        shared_reads: AtomicU64,
        total_reads: AtomicU64,
    }

    impl CountingFileSystem {
        fn new(root: &Path, shared: &Path) -> Self {
            let inner = OsFileSystem::new(root).unwrap();
            let shared = inner.normalize(shared).unwrap();
            Self {
                inner,
                shared,
                shared_reads: AtomicU64::new(0),
                total_reads: AtomicU64::new(0),
            }
        }
    }

    impl FileSystem for CountingFileSystem {
        fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError> {
            self.inner.normalize(path)
        }

        fn read(&self, path: &Path) -> Result<String, FileSystemError> {
            let path = self.inner.normalize(path)?;
            self.total_reads.fetch_add(1, Ordering::Relaxed);
            if path == self.shared {
                self.shared_reads.fetch_add(1, Ordering::Relaxed);
            }
            self.inner.read(&path)
        }

        fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError> {
            self.inner.metadata(path)
        }

        fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError> {
            self.inner.read_dir(path)
        }
    }
    struct CancellingFileSystem {
        inner: OsFileSystem,
        cancel: CancellationToken,
        cancel_at: u64,
        reads: AtomicU64,
    }

    impl CancellingFileSystem {
        fn new(root: &Path, cancel: CancellationToken, cancel_at: u64) -> Self {
            Self {
                inner: OsFileSystem::new(root).unwrap(),
                cancel,
                cancel_at,
                reads: AtomicU64::new(0),
            }
        }
    }

    impl FileSystem for CancellingFileSystem {
        fn normalize(&self, path: &Path) -> Result<PathBuf, FileSystemError> {
            self.inner.normalize(path)
        }

        fn read(&self, path: &Path) -> Result<String, FileSystemError> {
            let source = self.inner.read(path)?;
            let reads = self.reads.fetch_add(1, Ordering::Relaxed) + 1;
            if reads == self.cancel_at {
                self.cancel.cancel();
            }
            Ok(source)
        }

        fn metadata(&self, path: &Path) -> Result<FileMetadata, FileSystemError> {
            self.inner.metadata(path)
        }

        fn read_dir(&self, path: &Path) -> Result<Vec<PathBuf>, FileSystemError> {
            self.inner.read_dir(path)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn lower_fixture(fixture: &Fixture, entrypoint: &str) -> ExecutableProgram {
        let resolved = fixture.loader().load(entrypoint).unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        lower_program(
            &resolved,
            &frontend,
            LowerOptions {
                javascript_compatibility: true,
            },
        )
        .unwrap()
    }
    #[test]
    fn pre_cancelled_load_preserves_typed_path_context() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export const value = 1;");
        let cancel = CancellationToken::new();
        cancel.cancel();

        let error = fixture
            .loader()
            .load_with_cancel("main.ts", &cancel)
            .expect_err("pre-cancelled loading must stop before filesystem work");
        assert!(matches!(
            error,
            ProgramLoadError::Cancelled { path, .. } if path == Path::new("main.ts")
        ));
    }

    #[test]
    fn load_cancellation_after_read_stops_before_dependency_traversal() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import './dependency.js';");
        fixture.write("dependency.ts", "export const value = 1;");
        let cancel = CancellationToken::new();
        let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
        let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
        let filesystem = Arc::new(CancellingFileSystem::new(&fixture.0, cancel.clone(), 1));
        let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
        let loader =
            ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

        let error = loader
            .load_with_cancel("main.ts", &cancel)
            .expect_err("cancellation after the first read must stop traversal");
        assert!(matches!(
            error,
            ProgramLoadError::Cancelled { path, .. } if path.ends_with("main.ts")
        ));
        assert_eq!(filesystem.reads.load(Ordering::Relaxed), 1);
    }
    #[test]
    fn load_cancellation_after_package_read_retains_package_path() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import 'pkg';");
        fixture.write(
            "node_modules/pkg/package.json",
            r#"{"name":"pkg","exports":{".":"./index.ts"}}"#,
        );
        fixture.write("node_modules/pkg/index.ts", "export const value = 1;");
        let cancel = CancellationToken::new();
        let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
        let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
        let filesystem = Arc::new(CancellingFileSystem::new(&fixture.0, cancel.clone(), 2));
        let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
        let loader =
            ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

        let error = loader
            .load_with_cancel("main.ts", &cancel)
            .expect_err("cancellation after package.json read must stop package parsing");
        assert!(matches!(
            error,
            ProgramLoadError::Cancelled { path, .. } if path.ends_with("node_modules/pkg/package.json")
        ));
        assert_eq!(filesystem.reads.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn pre_cancelled_lowering_preserves_stage_and_path_context() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export const value = 1;");
        let resolved = fixture.loader().load("main.ts").unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let cancel = CancellationToken::new();
        cancel.cancel();

        let error =
            lower_program_with_cancel(&resolved, &frontend, LowerOptions::default(), &cancel)
                .expect_err("pre-cancelled lowering must stop at the frontend boundary");
        assert_eq!(error.module, resolved.entrypoint().path());
        assert_eq!(error.phase, ProgramLowerPhase::Frontend);
        assert!(matches!(error.kind, ProgramLowerErrorKind::Cancelled(_)));
    }

    #[test]
    fn malformed_surrogate_metadata_is_a_typed_error() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "const x = 1; export { x as \"\\uD800\" };");
        let resolved = fixture.loader().load("main.ts").unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let error = lower_program(
            &resolved,
            &frontend,
            LowerOptions {
                javascript_compatibility: true,
            },
        )
        .expect_err("ill-formed metadata must not reach host String conversion");
        assert_eq!(error.phase, ProgramLowerPhase::Metadata);
        assert_eq!(error.kind, ProgramLowerErrorKind::IllFormedMetadataString);
    }

    fn module_name(module: &ProgramModule<Verified>) -> String {
        match &module.code().constants()[module.name().get() as usize] {
            bamts_bytecode::Constant::String(name) => name
                .to_utf8_strict()
                .expect("compiler-produced module metadata is well-formed"),
            _ => panic!("verified module name is a string"),
        }
    }

    fn module<'a>(program: &'a ExecutableProgram, name: &str) -> &'a ProgramModule<Verified> {
        program
            .wire()
            .modules()
            .iter()
            .find(|module| module_name(module) == name)
            .unwrap_or_else(|| panic!("missing module {name}"))
    }

    fn constant_string(module: &ProgramModule<Verified>, id: bamts_bytecode::ConstantId) -> String {
        match &module.code().constants()[id.get() as usize] {
            bamts_bytecode::Constant::String(value) => value
                .to_utf8_strict()
                .expect("compiler-produced linkage metadata is well-formed"),
            _ => panic!("verified linkage constant is a string"),
        }
    }

    fn instructions(module: &ProgramModule<Verified>) -> impl Iterator<Item = Instruction> + '_ {
        module
            .code()
            .functions()
            .iter()
            .flat_map(|function| function.code().iter().copied())
    }

    fn names(program: &super::ResolvedProgram) -> Vec<&str> {
        program
            .modules()
            .iter()
            .map(|module| module.path().file_name().unwrap().to_str().unwrap())
            .collect()
    }

    #[test]
    fn program_lowering_inlines_a_local_const_enum_member() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "const enum K { X = 2, Y = X + 3 } K.Y !== 5;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(
            !instructions(main)
                .any(|instruction| matches!(instruction, Instruction::LoadGlobal { .. }))
        );
    }

    #[test]
    fn program_lowering_binds_a_qualified_import_equals_without_a_runtime_edge() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "declare namespace A { export namespace B { export const value: number; } } import X = A.B; const observed = X;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.edges().is_empty());
        let binding = main
            .bindings()
            .iter()
            .find(|binding| constant_string(main, binding.name) == "X")
            .expect("qualified import equals declares a module binding");
        assert!(matches!(binding.kind, BindingKind::Lexical));
        assert!(
            !instructions(main)
                .any(|instruction| matches!(instruction, Instruction::Import { .. }))
        );
    }

    #[test]
    fn program_lowering_erases_ambient_qualified_import_equals_without_load_global() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "declare namespace A { export namespace B { export const value: number; } } import X = A.B; type Alias = X;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(
            !instructions(main)
                .any(|instruction| matches!(instruction, Instruction::LoadGlobal { .. })),
            "ambient qualified import-equals must not fall back to LoadGlobal"
        );
    }

    #[test]
    fn program_lowering_elides_a_sole_imported_const_enum_binding() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export const enum K { X = 2, Y = X + 3 }");
        fixture.write(
            "main.ts",
            "import { K } from './a.ts'; if (K.Y !== 5) throw 'incorrect';",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.bindings().is_empty());
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        assert_eq!(constant_string(main, main.edges()[0].specifier), "./a.ts");
    }

    #[test]
    fn program_lowering_elides_only_imported_const_enum_bindings() {
        let fixture = Fixture::new();
        fixture.write(
            "a.ts",
            "export const enum K { X = 2, Y = X + 3 } export const value = 7;",
        );
        fixture.write(
            "main.ts",
            "import { K, value } from './a.ts'; if (K.Y !== 5 || value !== 7) throw 'incorrect';",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        assert_eq!(main.bindings().len(), 1);
        let binding = &main.bindings()[0];
        assert_eq!(constant_string(main, binding.name), "value");
        assert!(matches!(binding.kind, BindingKind::Imported { .. }));
    }

    #[test]
    fn program_lowering_distinguishes_same_named_enum_and_value_imports() {
        let fixture = Fixture::new();
        fixture.write("enum.ts", "export const enum K { Y = 5 }");
        fixture.write("value.ts", "export const K = 7;");
        fixture.write(
            "main.ts",
            "import { K as enum_k } from './enum.ts'; import { K } from './value.ts'; if (enum_k.Y !== 5 || K !== 7) throw 'incorrect';",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.bindings().len(), 1);
        let binding = &main.bindings()[0];
        assert_eq!(constant_string(main, binding.name), "K");
        assert!(matches!(binding.kind, BindingKind::Imported { .. }));
    }

    #[test]
    fn program_lowering_retains_module_evaluation_for_elided_const_enum_imports() {
        let fixture = Fixture::new();
        fixture.write(
            "enum_dep.ts",
            "export let evaluated = 0; evaluated += 1; export const enum K { X = 1, Y = X + 2 }",
        );
        fixture.write(
            "type_dep.ts",
            "export let type_evaluated = 0; type_evaluated += 1; export const enum OnlyType { Z = 9 }",
        );
        fixture.write(
            "mixed_dep.ts",
            "export const enum MixedEnum { A = 4 } export const value = 7;",
        );
        fixture.write(
            "main.ts",
            "import { K } from './enum_dep.ts'; import type { OnlyType } from './type_dep.ts'; import { MixedEnum, value } from './mixed_dep.ts'; type Shape = K; const typed: OnlyType = 9 as OnlyType; if (value !== 7) throw 'incorrect'; typed as Shape;",
        );

        let resolved = fixture.loader().load("main.ts").unwrap();
        let runtime: Vec<_> = resolved
            .runtime_modules()
            .iter()
            .map(|module| module.path().file_name().unwrap().to_str().unwrap())
            .collect();
        assert!(
            runtime.contains(&"enum_dep.ts"),
            "non-type-only const-enum import keeps the dependency in the runtime closure"
        );
        assert!(runtime.contains(&"mixed_dep.ts"));
        assert!(
            !runtime.contains(&"type_dep.ts"),
            "import type stays outside the runtime closure"
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let enum_dep = module(&executable, "enum_dep.ts");
        let mixed_dep = module(&executable, "mixed_dep.ts");

        assert!(
            main.edges().iter().any(|edge| {
                edge.kind == EdgeKind::Static
                    && constant_string(main, edge.specifier) == "./enum_dep.ts"
            }),
            "elided const-enum import retains a side-effect StaticRuntime edge"
        );
        assert!(
            main.bindings()
                .iter()
                .all(|binding| constant_string(main, binding.name) != "K"),
            "importer emits no runtime local for the const enum"
        );
        assert!(
            enum_dep
                .bindings()
                .iter()
                .all(|binding| constant_string(enum_dep, binding.name) != "K"),
            "exported const enum itself has no runtime binding"
        );
        assert!(
            enum_dep
                .bindings()
                .iter()
                .any(|binding| constant_string(enum_dep, binding.name) == "evaluated"),
            "observable top-level work in the enum module remains"
        );

        assert!(
            main.edges()
                .iter()
                .all(|edge| constant_string(main, edge.specifier) != "./type_dep.ts"),
            "import type is erased from wire edges"
        );
        let provenance = executable
            .provenance()
            .iter()
            .find(|item| item.source().path().ends_with("main.ts"))
            .expect("main provenance");
        assert!(
            provenance
                .type_only_edges()
                .any(|edge| edge.specifier() == "./type_dep.ts")
        );

        let mixed_edges: Vec<_> = main
            .edges()
            .iter()
            .filter(|edge| constant_string(main, edge.specifier) == "./mixed_dep.ts")
            .collect();
        assert_eq!(mixed_edges.len(), 1);
        assert_eq!(mixed_edges[0].kind, EdgeKind::Static);
        assert_eq!(
            main.bindings()
                .iter()
                .filter(|binding| matches!(binding.kind, BindingKind::Imported { .. }))
                .count(),
            1
        );
        let value = main
            .bindings()
            .iter()
            .find(|binding| constant_string(main, binding.name) == "value")
            .expect("mixed import keeps the real value binding once");
        assert!(matches!(value.kind, BindingKind::Imported { .. }));
        assert!(
            main.bindings()
                .iter()
                .all(|binding| constant_string(main, binding.name) != "MixedEnum")
        );
        assert!(
            mixed_dep
                .bindings()
                .iter()
                .all(|binding| constant_string(mixed_dep, binding.name) != "MixedEnum")
        );
    }

    #[test]
    fn program_lowering_binds_export_star_namespace_as_live_export_metadata() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 7;");
        fixture.write("main.ts", "export * as ns from './dep.ts';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);

        let binding = main
            .bindings()
            .iter()
            .find(|binding| constant_string(main, binding.name) == "*namespace:ns*")
            .expect("export * as ns keeps a synthetic namespace binding");
        assert!(
            matches!(binding.kind, BindingKind::Namespace { edge } if edge == EdgeId::new(0)),
            "namespace export binds the existing module namespace object"
        );

        let export = main
            .exports()
            .iter()
            .find(|export| constant_string(main, export.name) == "ns")
            .expect("export * as ns exposes the named export");
        assert!(
            matches!(export.source, ExportSource::Local(binding) if constant_string(main, main.bindings()[binding.get() as usize].name) == "*namespace:ns*"),
            "named namespace export points at the namespace binding"
        );
    }

    #[test]
    fn program_lowering_keeps_static_imports_live_without_snapshot_opcodes() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export let value = 1; value = 2;");
        fixture.write(
            "main.ts",
            "import { value as observed } from './dep.js'; export { observed };",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        let binding = main
            .bindings()
            .iter()
            .find(|binding| constant_string(main, binding.name) == "observed")
            .unwrap();
        assert!(matches!(binding.kind, BindingKind::Imported { .. }));
        assert!(!instructions(main).any(|instruction| matches!(
            instruction,
            Instruction::Import { .. }
                | Instruction::GetProperty { .. }
                | Instruction::Export { .. }
        )));

        let main_id = executable.wire().entry();
        let export = main
            .exports()
            .iter()
            .find(|export| constant_string(main, export.name) == "observed")
            .unwrap();
        assert!(matches!(export.source, ExportSource::Local(_)));
        assert!(matches!(
            executable.wire().resolve_export(main_id, &EcmaString::encode("observed")),
            Some(ResolvedExport::Local { module, .. })
                if module != main_id
        ));
    }

    #[test]
    fn program_lowering_links_external_import_equals_as_one_namespace_binding() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "import util = require('node:util'); util.parseArgs;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].target, EdgeTarget::External);
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        assert_eq!(main.bindings().len(), 1);
        let binding = &main.bindings()[0];
        assert_eq!(constant_string(main, binding.name), "util");
        assert!(matches!(
            binding.kind,
            BindingKind::Namespace { edge } if edge == EdgeId::new(0)
        ));
        assert!(!instructions(main).any(|instruction| matches!(
            instruction,
            Instruction::Import { .. } | Instruction::Export { .. }
        )));
    }

    #[test]
    fn program_lowering_links_local_import_equals_as_one_namespace_binding() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 7;");
        fixture.write("main.ts", "import dep = require('./dep.js'); dep.value;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert!(matches!(main.edges()[0].target, EdgeTarget::Local(_)));
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        assert_eq!(main.bindings().len(), 1);
        let binding = &main.bindings()[0];
        assert_eq!(constant_string(main, binding.name), "dep");
        assert!(matches!(
            binding.kind,
            BindingKind::Namespace { edge } if edge == EdgeId::new(0)
        ));
    }

    #[test]
    fn program_lowering_links_local_export_assignment_import_equals_as_default_binding() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export = { value: 7 };");
        fixture.write("main.ts", "import dep = require('./dep.js'); dep;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert!(matches!(main.edges()[0].target, EdgeTarget::Local(_)));
        assert_eq!(main.edges()[0].kind, EdgeKind::Static);
        assert_eq!(main.bindings().len(), 1);
        let binding = &main.bindings()[0];
        assert_eq!(constant_string(main, binding.name), "dep");
        assert!(matches!(
            binding.kind,
            BindingKind::Imported { edge, name }
                if edge == EdgeId::new(0) && constant_string(main, name) == "default"
        ));
    }

    #[test]
    fn program_lowering_records_namespace_imports() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 1; export default 2;");
        fixture.write(
            "main.ts",
            "import fallback, * as namespace from './dep.js'; fallback; namespace.value;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "namespace"
                && matches!(binding.kind, BindingKind::Namespace { .. })
        }));
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "fallback"
                && matches!(
                    binding.kind,
                    BindingKind::Imported { name, .. }
                        if constant_string(main, name) == "default"
                )
        }));
    }

    #[test]
    fn program_lowering_resolves_alias_reexports() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const original = 1;");
        fixture.write("main.ts", "export { original as renamed } from './dep.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let export = main
            .exports()
            .iter()
            .find(|export| constant_string(main, export.name) == "renamed")
            .unwrap();
        assert!(matches!(export.source, ExportSource::Indirect { .. }));
        assert!(matches!(
            executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode("renamed")),
            Some(ResolvedExport::Local { module, .. })
                if module != executable.wire().entry()
        ));
    }

    #[test]
    fn program_lowering_omits_ambiguous_star_exports() {
        let fixture = Fixture::new();
        fixture.write(
            "a.ts",
            "export const collision = 1; export const onlyA = 1;",
        );
        fixture.write(
            "b.ts",
            "export const collision = 2; export const onlyB = 2;",
        );
        fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let names: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert!(names.iter().any(|name| name == "onlyA"));
        assert!(names.iter().any(|name| name == "onlyB"));
        assert!(!names.iter().any(|name| name == "collision"));
    }

    #[test]
    fn program_lowering_keeps_diamond_star_reexports_unambiguous() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export const value = 1;");
        fixture.write("b.ts", "export { value } from './a.js';");
        fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.exports()
                .iter()
                .filter(|export| constant_string(main, export.name) == "value")
                .count(),
            1
        );
        assert!(
            executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
                .is_some()
        );
    }

    #[test]
    fn program_lowering_canonicalizes_external_reexport_identity() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export { readFile } from 'node:fs';");
        fixture.write("b.ts", "export { readFile } from 'node:fs';");
        fixture.write("main.ts", "export * from './a.js'; export * from './b.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.exports()
                .iter()
                .filter(|export| constant_string(main, export.name) == "readFile")
                .count(),
            1
        );
        assert!(matches!(
            executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode("readFile")),
            Some(ResolvedExport::External { .. })
        ));
    }

    #[test]
    fn program_lowering_discovers_transitive_star_exports() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export let value = 1;");
        fixture.write("mid.ts", "export * from './dep.js';");
        fixture.write("main.ts", "export * from './mid.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let export = main
            .exports()
            .iter()
            .find(|export| constant_string(main, export.name) == "value")
            .unwrap();
        assert!(matches!(export.source, ExportSource::Indirect { .. }));
        let resolved = executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
            .expect("transitive star export must resolve");
        let ResolvedExport::Local {
            module: resolved, ..
        } = resolved
        else {
            panic!("transitive star export must stay local");
        };
        assert_eq!(
            module_name(&executable.wire().modules()[resolved.get() as usize]),
            "dep.ts"
        );
    }

    #[test]
    fn program_lowering_preserves_explicit_shadowing_over_star_reexports() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 1;");
        fixture.write(
            "main.ts",
            "export { value as shadowed } from './dep.js'; export * from './dep.js';",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.exports().iter().any(|export| {
            constant_string(main, export.name) == "shadowed"
                && matches!(export.source, ExportSource::Indirect { .. })
        }));
        assert_eq!(
            main.exports()
                .iter()
                .filter(|export| constant_string(main, export.name) == "value")
                .count(),
            1
        );
        assert!(
            executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
                .is_some()
        );
    }

    #[test]
    fn program_lowering_downstream_star_prefers_explicit_over_star_collision() {
        let fixture = Fixture::new();
        fixture.write("other.ts", "export const value = 1;");
        fixture.write(
            "mid.ts",
            "export const value = 2; export * from './other.js';",
        );
        fixture.write("main.ts", "export * from './mid.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.exports()
                .iter()
                .filter(|export| constant_string(main, export.name) == "value")
                .count(),
            1
        );
        let resolved = executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
            .expect("downstream star must expose mid's explicit value unambiguously");
        let ResolvedExport::Local {
            module: resolved, ..
        } = resolved
        else {
            panic!("explicit-over-star reexport must stay local");
        };
        assert_eq!(
            module_name(&executable.wire().modules()[resolved.get() as usize]),
            "mid.ts"
        );
    }

    #[test]
    fn program_lowering_excludes_default_from_star_reexports() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export default 1; export const named = 2;");
        fixture.write("main.ts", "export * from './dep.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let names: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(names, ["named"]);
        assert!(
            executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode("default"))
                .is_none()
        );
    }

    #[test]
    fn program_lowering_terminates_cyclic_star_reexports_without_pollution() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "export * from './b.js'; export const a = 1;");
        fixture.write("b.ts", "export * from './a.js'; export const b = 2;");
        fixture.write("main.ts", "export * from './a.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let names: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(names, ["a", "b"]);
        for name in ["a", "b"] {
            let resolved = executable
                .wire()
                .resolve_export(executable.wire().entry(), &EcmaString::encode(name))
                .expect("cyclic star graph must resolve both direct exports");
            let ResolvedExport::Local {
                module: resolved, ..
            } = resolved
            else {
                panic!("star reexport must stay local");
            };
            assert_eq!(
                module_name(&executable.wire().modules()[resolved.get() as usize]),
                format!("{name}.ts")
            );
        }
    }

    #[test]
    fn program_lowering_star_reexports_track_live_imported_cells() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export let value = 1;");
        fixture.write(
            "mid.ts",
            "import { value } from './dep.js'; export { value };",
        );
        fixture.write("main.ts", "export * from './mid.js';");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let export = main
            .exports()
            .iter()
            .find(|export| constant_string(main, export.name) == "value")
            .unwrap();
        assert!(matches!(export.source, ExportSource::Indirect { .. }));
        let dep_index = executable
            .wire()
            .modules()
            .iter()
            .position(|candidate| module_name(candidate) == "dep.ts")
            .unwrap() as u32;
        let resolved = executable
            .wire()
            .resolve_export(executable.wire().entry(), &EcmaString::encode("value"))
            .expect("live imported cell reexport must resolve");
        let ResolvedExport::Local { module, binding } = resolved else {
            panic!("live imported cell reexport must stay local");
        };
        assert_eq!(module.get(), dep_index);
        assert_eq!(binding, BindingId::new(0));
    }

    #[test]
    fn program_lowering_materializes_default_expression_binding() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export default 1 + 2;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let binding_index = main
            .bindings()
            .iter()
            .position(|binding| constant_string(main, binding.name) == "*default*")
            .unwrap();
        assert_eq!(main.bindings()[binding_index].kind, BindingKind::Lexical);
        assert!(main.exports().iter().any(|export| {
            constant_string(main, export.name) == "default"
                && export.source
                    == ExportSource::Local(bamts_bytecode::BindingId::new(binding_index as u32))
        }));
        assert!(
            !instructions(main)
                .any(|instruction| matches!(instruction, Instruction::Export { .. }))
        );
    }

    #[test]
    fn program_lowering_materializes_export_assignment_as_default_export() {
        let fixture = Fixture::new();
        fixture.write("equal.ts", "export = 1 + 2;");
        fixture.write(
            "main.ts",
            "import * as equal from './equal.ts'; import fallback from './equal.ts';",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let equal = module(&executable, "equal.ts");
        let binding_index = equal
            .bindings()
            .iter()
            .position(|binding| constant_string(equal, binding.name) == "*export=*")
            .expect("export assignment owns a dedicated binding");
        assert_eq!(equal.bindings()[binding_index].kind, BindingKind::Lexical);
        assert!(equal.exports().iter().any(|export| {
            constant_string(equal, export.name) == "default"
                && export.source
                    == ExportSource::Local(bamts_bytecode::BindingId::new(binding_index as u32))
        }));
        assert!(
            !instructions(equal)
                .any(|instruction| matches!(instruction, Instruction::Export { .. }))
        );

        let main = module(&executable, "main.ts");
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "equal"
                && matches!(binding.kind, BindingKind::Namespace { .. })
        }));
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "fallback"
                && matches!(binding.kind, BindingKind::Imported { name, .. } if constant_string(main, name) == "default")
        }));
    }

    #[test]
    fn export_assignment_combined_with_default_export_is_rejected_during_link() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export = 1; export default 2;");

        let resolved = fixture.loader().load("main.ts").unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
        assert_eq!(error.phase, ProgramLowerPhase::Link);
        assert!(matches!(
            error.kind,
            ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
                kind: ProgramVerifyErrorKind::DuplicateExport { .. },
                ..
            })
        ));
    }

    #[test]
    fn program_lowering_initializes_default_named_class_binding() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export default class Foo {}; Foo;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "Foo" && binding.kind == BindingKind::Lexical
        }));
        let stored: Vec<_> = instructions(main)
            .filter_map(|instruction| match instruction {
                Instruction::StoreGlobal { name, .. } => Some(constant_string(main, name)),
                _ => None,
            })
            .collect();
        assert!(stored.iter().any(|name| name == "Foo"));
        assert!(stored.iter().any(|name| name == "*default*"));
    }

    #[test]
    fn program_lowering_erases_type_only_edges_from_wire_but_retains_provenance() {
        let fixture = Fixture::new();
        fixture.write("types.ts", "export interface Shape { value: number }");
        fixture.write(
            "main.ts",
            "import type { Shape } from './types.js'; let x: Shape;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert!(main.edges().is_empty());
        assert!(
            main.bindings()
                .iter()
                .all(|binding| { constant_string(main, binding.name) != "Shape" })
        );
        let provenance = executable
            .provenance()
            .iter()
            .find(|item| item.source().path().ends_with("main.ts"))
            .unwrap();
        assert_eq!(provenance.type_only_edges().count(), 1);
    }

    #[test]
    fn program_lowering_links_cycles_with_hoisted_and_tdz_bindings() {
        let fixture = Fixture::new();
        fixture.write(
            "a.ts",
            "import { fromB } from './b.js'; export let fromA = fromB; export var hoistedVar; export class LexicalClass {}",
        );
        fixture.write(
            "b.ts",
            "import { fromA } from './a.js'; export function fromB() { return fromA; }",
        );

        let executable = lower_fixture(&fixture, "a.ts");
        let a = module(&executable, "a.ts");
        let b = module(&executable, "b.ts");
        assert!(a.bindings().iter().any(|binding| {
            constant_string(a, binding.name) == "fromA" && binding.kind == BindingKind::Lexical
        }));
        assert!(a.bindings().iter().any(|binding| {
            constant_string(a, binding.name) == "hoistedVar" && binding.kind == BindingKind::Hoisted
        }));
        assert!(a.bindings().iter().any(|binding| {
            constant_string(a, binding.name) == "LexicalClass"
                && binding.kind == BindingKind::Lexical
        }));
        assert!(b.bindings().iter().any(|binding| {
            constant_string(b, binding.name) == "fromB" && binding.kind == BindingKind::Hoisted
        }));
        assert!(a.edges().iter().all(|edge| edge.kind == EdgeKind::Static));
        assert!(b.edges().iter().all(|edge| edge.kind == EdgeKind::Static));
    }

    #[test]
    fn program_lowering_keeps_dynamic_import_as_dynamic_instruction_edge() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 1;");
        fixture.write("main.ts", "const pending = import('./dep.js');");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::Dynamic);
        assert!(
            instructions(main)
                .any(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
        );
    }

    #[test]
    fn program_lowering_coalesces_static_and_dynamic_imports_of_one_target() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 1;");
        fixture.write(
            "main.ts",
            "import { value } from './dep.js'; const pending = import('./dep.js'); value;",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].kind, EdgeKind::StaticAndDynamic);
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "value"
                && matches!(binding.kind, BindingKind::Imported { .. })
        }));
        assert!(
            instructions(main)
                .any(|instruction| matches!(instruction, Instruction::ImportDynamic { .. }))
        );
    }

    #[test]
    fn program_lowering_emits_import_meta_without_linkage_metadata() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "const meta = import.meta; meta.url;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let loads = instructions(main)
            .filter(|instruction| matches!(instruction, Instruction::LoadImportMeta { .. }))
            .count();
        assert_eq!(loads, 1);
        assert!(main.edges().is_empty());
        assert!(main.bindings().iter().any(|binding| {
            constant_string(main, binding.name) == "meta"
                && matches!(binding.kind, BindingKind::Lexical)
        }));
        assert!(main.exports().is_empty());
        assert_eq!(module_name(main), "main.ts");
    }

    #[test]
    fn program_lowering_rejects_same_specifier_with_different_targets() {
        let fixture = Fixture::new();
        fixture.write("dep.ts", "export const value = 1;");
        fixture.write("other.ts", "export const other = 2;");
        fixture.write(
            "main.ts",
            "import { value } from './dep.js'; const pending = import('./dep.js'); import './other.js'; value;",
        );
        let mut resolved = fixture.loader().load("main.ts").unwrap();
        let other = resolved
            .modules()
            .iter()
            .find(|module| module.path().ends_with("other.ts"))
            .unwrap()
            .source_id();
        let modules = Arc::get_mut(&mut resolved.modules).unwrap();
        let main = modules
            .iter_mut()
            .find(|module| module.path().ends_with("main.ts"))
            .unwrap();
        let dependencies = Arc::make_mut(&mut main.dependencies);
        dependencies
            .iter_mut()
            .find(|edge| edge.kind == ModuleEdgeKind::DynamicRuntime)
            .unwrap()
            .target = ModuleTarget::Local(other);

        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
        assert_eq!(error.phase, ProgramLowerPhase::Metadata);
        assert_eq!(
            error.kind,
            ProgramLowerErrorKind::ConflictingRuntimeEdge {
                specifier: "./dep.js".to_owned(),
            }
        );
    }

    #[test]
    fn program_lowering_binds_export_namespace_as_single_value_export() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "export namespace N {}");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        let binding_index = main
            .bindings()
            .iter()
            .position(|binding| constant_string(main, binding.name) == "N")
            .expect("export namespace owns one local binding");
        assert_eq!(main.bindings()[binding_index].kind, BindingKind::Hoisted);
        let exports: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(exports, ["N"]);
        assert_eq!(
            main.exports()[0].source,
            ExportSource::Local(BindingId::new(binding_index as u32))
        );
    }

    #[test]
    fn program_lowering_merges_duplicate_export_namespaces_into_one_export() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "export namespace N { export const x = 1; } export namespace N { export const y = 2; }",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.bindings()
                .iter()
                .filter(|binding| constant_string(main, binding.name) == "N")
                .count(),
            1,
            "merged namespaces share one binding"
        );
        let exports: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(exports, ["N"]);
    }

    #[test]
    fn program_lowering_merges_export_function_and_export_namespace_without_duplicate_export() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "export function F() { return 1; } export namespace F { export const x = 2; }",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.bindings()
                .iter()
                .filter(|binding| constant_string(main, binding.name) == "F")
                .count(),
            1
        );
        let exports: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(exports, ["F"]);
    }

    #[test]
    fn program_lowering_merges_export_class_and_export_namespace_without_duplicate_export() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "export class C {} export namespace C { export const x = 1; }",
        );

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(
            main.bindings()
                .iter()
                .filter(|binding| constant_string(main, binding.name) == "C")
                .count(),
            1,
            "class/namespace merge must not emit DuplicateBinding"
        );
        let exports: Vec<_> = main
            .exports()
            .iter()
            .map(|export| constant_string(main, export.name))
            .collect();
        assert_eq!(exports, ["C"]);
    }

    #[test]
    fn program_lowering_preserves_true_duplicate_namespace_exports() {
        let fixture = Fixture::new();
        // Specifier-form duplicates remain link failures even after namespace merge
        // dedup for declaration exports.
        fixture.write("main.ts", "const N = 1; export { N }; export { N };");

        let resolved = fixture.loader().load("main.ts").unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
        assert_eq!(error.phase, ProgramLowerPhase::Link);
        assert!(matches!(
            error.kind,
            ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
                kind: ProgramVerifyErrorKind::DuplicateExport { .. },
                ..
            })
        ));
    }

    #[test]
    fn program_lowering_rejects_duplicate_exports_during_link() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "const value = 1; export { value }; export { value };",
        );
        let resolved = fixture.loader().load("main.ts").unwrap();
        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let error = lower_program(&resolved, &frontend, LowerOptions::default()).unwrap_err();
        assert_eq!(error.phase, ProgramLowerPhase::Link);
        assert!(matches!(
            error.kind,
            ProgramLowerErrorKind::Link(bamts_bytecode::ProgramVerifyError {
                kind: ProgramVerifyErrorKind::DuplicateExport { .. },
                ..
            })
        ));
    }

    #[test]
    fn program_lowering_preserves_external_identity_only_in_provenance() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import * as fs from 'node:fs'; fs.readFile;");

        let executable = lower_fixture(&fixture, "main.ts");
        let main = module(&executable, "main.ts");
        assert_eq!(main.edges().len(), 1);
        assert_eq!(main.edges()[0].target, EdgeTarget::External);
        let provenance = executable
            .provenance()
            .iter()
            .find(|item| item.source().path().ends_with("main.ts"))
            .unwrap();
        assert!(matches!(
            provenance.edges()[0].target(),
            ModuleTarget::External(specifier) if specifier.as_ref() == "node:fs"
        ));
    }

    #[test]
    fn program_lowering_is_deterministic_and_names_modules_root_relatively() {
        let fixture = Fixture::new();
        fixture.write("lib/dep.ts", "export const value = 1;");
        fixture.write("src/main.ts", "export { value } from '../lib/dep.js';");

        let first = lower_fixture(&fixture, "src/main.ts");
        let second = lower_fixture(&fixture, "src/main.ts");
        assert_eq!(first.wire().encode(), second.wire().encode());
        assert_eq!(
            first
                .wire()
                .modules()
                .iter()
                .map(module_name)
                .collect::<Vec<_>>(),
            ["lib/dep.ts", "src/main.ts"]
        );
        for (left, right) in first.wire().modules().iter().zip(second.wire().modules()) {
            assert_eq!(left.code().encode(), right.code().encode());
        }
    }

    #[test]
    fn resolves_extensions_and_directory_indexes_dependency_first() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import './leaf.js'; import './branch';");
        fixture.write("leaf.ts", "export const leaf = 1;");
        fixture.write("branch/index.ts", "export const branch = 1;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["leaf.ts", "index.ts", "main.ts"]);
    }

    #[test]
    fn excludes_type_only_dependencies_from_runtime_closure() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "import type { Shape } from './shape'; import { value } from './value'; void value;",
        );
        fixture.write("shape.ts", "export interface Shape { x: number }");
        fixture.write("value.ts", "export const value = 1;");

        let program = fixture.loader().load("main.ts").unwrap();
        let runtime: Vec<_> = program
            .runtime_modules()
            .iter()
            .map(|module| module.path().file_name().unwrap().to_str().unwrap())
            .collect();

        assert_eq!(runtime, ["value.ts", "main.ts"]);
        assert!(program.entrypoint().dependencies().iter().any(|edge| {
            edge.kind() == ModuleEdgeKind::TypeOnly && edge.specifier() == "./shape"
        }));
    }

    #[test]
    fn deduplicates_diamond_dependencies_by_canonical_path() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import './left'; import './right';");
        fixture.write("left.ts", "import './shared';");
        fixture.write("right.ts", "import './shared';");
        fixture.write("shared.ts", "export const shared = 1;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(
            names(&program),
            ["shared.ts", "left.ts", "right.ts", "main.ts"]
        );
        assert_eq!(program.modules().len(), 4);
    }

    #[test]
    fn multi_root_load_compiles_every_root_and_reads_shared_source_once() {
        let fixture = Fixture::new();
        fixture.write(
            "a.ts",
            "import { shared } from './shared'; export const a = shared;",
        );
        fixture.write(
            "b.ts",
            "import { shared } from './shared'; export const b = shared;",
        );
        fixture.write("shared.ts", "export const shared = 1;");

        let root = ProjectRoot::new(fs::canonicalize(&fixture.0).unwrap()).unwrap();
        let config = ProjectConfig::parse(&root, fixture.0.join("tsconfig.json"), "{}").unwrap();
        let filesystem = Arc::new(CountingFileSystem::new(&fixture.0, Path::new("shared.ts")));
        let loader_filesystem: Arc<dyn FileSystem> = filesystem.clone();
        let loader =
            ProgramLoader::with_file_system(&root, config.options(), loader_filesystem).unwrap();

        let program = loader
            .load_roots(&[PathBuf::from("b.ts"), PathBuf::from("a.ts")])
            .unwrap();
        let frontend = compile_program_frontend(&program, FrontendMode::Check);

        assert_eq!(names(&program), ["shared.ts", "a.ts", "b.ts"]);
        assert_eq!(program.roots().len(), 2);
        assert_eq!(frontend.modules().len(), 3);
        assert!(frontend.modules().iter().all(|module| !module.has_errors()));
        assert_eq!(filesystem.shared_reads.load(Ordering::Relaxed), 1);
        assert_eq!(filesystem.total_reads.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn multi_root_load_is_input_order_independent_and_keeps_explicit_dependency_root() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "import './shared'; export const a: string = 1;");
        fixture.write("b.ts", "import './shared'; export const b: boolean = 2;");
        fixture.write("shared.ts", "export const shared = 3;");
        let loader = fixture.loader();
        let forward = loader
            .load_roots(&[
                PathBuf::from("a.ts"),
                PathBuf::from("b.ts"),
                PathBuf::from("shared.ts"),
                PathBuf::from("a.ts"),
            ])
            .unwrap();
        let reversed = loader
            .load_roots(&[
                PathBuf::from("a.ts"),
                PathBuf::from("shared.ts"),
                PathBuf::from("b.ts"),
                PathBuf::from("a.ts"),
            ])
            .unwrap();

        let graph = |program: &super::ResolvedProgram| {
            program
                .modules()
                .iter()
                .map(|module| {
                    (
                        module.source_id(),
                        module
                            .path()
                            .strip_prefix(program.root().path())
                            .unwrap()
                            .to_path_buf(),
                        module
                            .dependencies()
                            .iter()
                            .map(|edge| {
                                (
                                    edge.kind(),
                                    edge.specifier().to_owned(),
                                    edge.target().clone(),
                                )
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let diagnostics = |program: &super::ResolvedProgram| {
            compile_program_frontend(program, FrontendMode::Check)
                .modules()
                .iter()
                .flat_map(|module| module.diagnostics().iter().cloned())
                .collect::<Vec<_>>()
        };

        let forward_diagnostics = diagnostics(&forward);
        let reversed_diagnostics = diagnostics(&reversed);
        assert!(!forward_diagnostics.is_empty());
        assert_eq!(forward.roots(), reversed.roots());
        assert_eq!(graph(&forward), graph(&reversed));
        assert_eq!(forward_diagnostics, reversed_diagnostics);
        assert_eq!(
            forward
                .roots()
                .iter()
                .map(|source_id| {
                    forward
                        .module(*source_id)
                        .unwrap()
                        .path()
                        .file_name()
                        .unwrap()
                        .to_str()
                        .unwrap()
                })
                .collect::<Vec<_>>(),
            ["a.ts", "b.ts", "shared.ts"]
        );
    }

    #[test]
    fn multi_root_load_rejects_missing_and_empty_root_sets_with_typed_errors() {
        let fixture = Fixture::new();
        fixture.write("present.ts", "export const present = true;");
        let loader = fixture.loader();

        let error = loader
            .load_roots(&[PathBuf::from("present.ts"), PathBuf::from("missing.ts")])
            .unwrap_err();
        assert!(matches!(
            error,
            ProgramLoadError::Read { path, source }
                if path.ends_with("missing.ts") && source.kind() == std::io::ErrorKind::NotFound
        ));
        assert!(matches!(
            loader.load_roots(&[]).unwrap_err(),
            ProgramLoadError::NoRoots
        ));
    }

    #[test]
    fn preserves_cycles_without_duplicate_modules() {
        let fixture = Fixture::new();
        fixture.write("a.ts", "import './b';");
        fixture.write("b.ts", "import './a';");

        let program = fixture.loader().load("a.ts").unwrap();
        let b = &program.modules()[0];

        assert_eq!(names(&program), ["b.ts", "a.ts"]);
        assert_eq!(
            b.dependencies()[0].target(),
            &ModuleTarget::Local(program.entrypoint_id())
        );
    }

    #[test]
    fn loads_a_long_acyclic_import_chain_iteratively() {
        // Deep enough that the previous recursive DFS would blow the thread stack,
        // but cheap to materialize: one tiny file per hop.
        const DEPTH: usize = 4096;
        let fixture = Fixture::new();
        for index in 0..DEPTH {
            let name = format!("m{index}.ts");
            let source = if index + 1 == DEPTH {
                "export {};\n".to_string()
            } else {
                format!("import './m{}.ts';\n", index + 1)
            };
            fixture.write(&name, &source);
        }

        let program = fixture.loader().load("m0.ts").unwrap();

        assert_eq!(program.modules().len(), DEPTH);
        assert_eq!(program.entrypoint_id().get(), 0);
        assert_eq!(
            program.modules().last().map(|module| module.source_id()),
            Some(program.entrypoint_id())
        );
        assert_eq!(
            program.modules()[0]
                .path()
                .file_name()
                .unwrap()
                .to_str()
                .unwrap(),
            format!("m{}.ts", DEPTH - 1)
        );
        assert_eq!(
            program.modules()[0].source_id().get(),
            u32::try_from(DEPTH - 1).unwrap()
        );
        assert_eq!(
            program.entrypoint().dependencies()[0].target(),
            &ModuleTarget::Local(program.modules()[DEPTH - 2].source_id())
        );
    }

    #[test]
    fn resolves_package_exports_entry() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import { answer } from 'waybread'; void answer;");
        fixture.write(
            "node_modules/waybread/package.json",
            r#"{"name":"waybread","exports":{".":{"import":"./src/entry.js"}}}"#,
        );
        fixture.write(
            "node_modules/waybread/src/entry.ts",
            "export const answer = 42;",
        );

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["entry.ts", "main.ts"]);
    }
    #[test]
    fn resolves_package_import_maps() {
        let fixture = Fixture::new();
        fixture.write(
            "package.json",
            r##"{"name":"root","imports":{"#waybread":"./src/alias.js"}}"##,
        );
        fixture.write(
            "main.ts",
            "import { answer } from '#waybread'; void answer;",
        );
        fixture.write("src/alias.ts", "export const answer = 42;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["alias.ts", "main.ts"]);
    }

    #[test]
    fn decodes_escaped_module_specifiers() {
        let fixture = Fixture::new();
        fixture.write("main.ts", r#"import './\u0066oo';"#);
        fixture.write("foo.ts", "export const answer = 42;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["foo.ts", "main.ts"]);
    }

    #[test]
    fn rejects_ill_formed_utf16_module_specifiers() {
        for source in [
            r#"import type { T } from "\uD800";"#,
            r#"type T = import("\uD800").T;"#,
        ] {
            let fixture = Fixture::new();
            fixture.write("main.ts", source);

            assert!(matches!(
                fixture.loader().load("main.ts"),
                Err(ProgramLoadError::IllFormedModuleSpecifier { .. })
            ));
        }
    }

    #[test]
    fn rejects_relative_traversal_before_loading() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import '../outside.ts';");

        let error = fixture.loader().load("main.ts").unwrap_err();

        assert!(matches!(
            error,
            ProgramLoadError::InvalidSpecifier { .. } | ProgramLoadError::UnresolvedModule(_)
        ));
    }

    #[test]
    fn retains_literal_dynamic_import_edges() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "async function load() { return import('./later'); }",
        );
        fixture.write("later.ts", "export const later = 1;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["later.ts", "main.ts"]);
        assert_eq!(
            program.entrypoint().dependencies()[0].kind(),
            ModuleEdgeKind::DynamicRuntime
        );
        assert_eq!(program.runtime_modules().len(), 1);
    }

    #[test]
    fn retains_dynamic_imports_from_class_decorators() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "@import('./class') class C {\n\
             @import('./constructor') constructor() {}\n\
             @import('./method') method() {}\n\
             @import('./property') property;\n\
             @import('./accessor') accessor value;\n\
             }",
        );
        for module in ["class", "constructor", "method", "property", "accessor"] {
            fixture.write(&format!("{module}.ts"), "export {};");
        }

        let program = fixture.loader().load("main.ts").unwrap();
        let dependencies = program.entrypoint().dependencies();
        assert_eq!(dependencies.len(), 5);
        assert!(
            dependencies
                .iter()
                .all(|dependency| dependency.kind() == ModuleEdgeKind::DynamicRuntime)
        );
        assert_eq!(
            dependencies
                .iter()
                .map(|dependency| dependency.specifier())
                .collect::<Vec<_>>(),
            [
                "./class",
                "./constructor",
                "./method",
                "./property",
                "./accessor",
            ]
        );
    }

    #[test]
    fn classifies_import_types_without_creating_dynamic_runtime_edges() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "type Shape = import('./shape').Shape; void 0;");
        fixture.write("shape.ts", "export interface Shape { x: number }");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["shape.ts", "main.ts"]);
        assert_eq!(
            program.entrypoint().dependencies()[0].kind(),
            ModuleEdgeKind::TypeOnly
        );
        assert_eq!(program.runtime_modules().len(), 1);
    }

    #[test]
    fn unresolved_runtime_edge_reports_typed_diagnostic() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import './missing';");

        let ProgramLoadError::UnresolvedModule(diagnostic) =
            fixture.loader().load("main.ts").unwrap_err()
        else {
            panic!("expected unresolved-module diagnostic");
        };

        assert_eq!(diagnostic.kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(diagnostic.specifier(), "./missing");
        assert_eq!(
            diagnostic.importer().file_name(),
            Some(Path::new("main.ts").as_os_str())
        );
    }

    #[test]
    fn retains_node_builtin_as_external_static_runtime_edge() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "import { parseArgs } from 'node:util'; void parseArgs;",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];

        assert_eq!(names(&program), ["main.ts"]);
        assert_eq!(edge.kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(edge.target().external_specifier(), Some("node:util"));
        assert_eq!(program.runtime_modules().len(), 1);
    }

    #[test]
    fn preserves_unresolved_type_package_as_external_identity() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import type { JsonValue } from 'type-fest';");

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];

        assert_eq!(edge.kind(), ModuleEdgeKind::TypeOnly);
        assert_eq!(edge.target().external_specifier(), Some("type-fest"));
        assert_eq!(program.runtime_modules().len(), 1);
    }

    #[test]
    fn unresolved_ordinary_runtime_package_is_rejected() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import 'waybread';");

        let ProgramLoadError::UnresolvedModule(diagnostic) =
            fixture.loader().load("main.ts").unwrap_err()
        else {
            panic!("expected unresolved-module diagnostic");
        };

        assert_eq!(diagnostic.kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(diagnostic.specifier(), "waybread");
    }

    #[test]
    fn retains_dynamic_engine_module_as_external_edge() {
        let fixture = Fixture::new();
        fixture.write(
            "package.json",
            r##"{"name":"root","imports":{"#engine":"engine:clock"}}"##,
        );
        fixture.write(
            "main.ts",
            "async function load() { return import('#engine'); }",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];

        assert_eq!(edge.kind(), ModuleEdgeKind::DynamicRuntime);
        assert_eq!(edge.specifier(), "#engine");
        assert_eq!(edge.target().external_specifier(), Some("engine:clock"));
        assert_eq!(program.runtime_modules().len(), 1);
    }

    #[test]
    fn local_type_package_takes_precedence_over_external_fallback() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import type { Shape } from 'waybread';");
        fixture.write(
            "node_modules/waybread/package.json",
            r#"{"name":"waybread","types":"./index.d.ts"}"#,
        );
        fixture.write(
            "node_modules/waybread/index.d.ts",
            "export interface Shape { x: number }",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];

        assert_eq!(names(&program), ["index.d.ts", "main.ts"]);
        assert!(matches!(edge.target(), ModuleTarget::Local(_)));
    }

    #[test]
    fn records_flavor_and_mode_for_type_only_runtime_and_dynamic_edges() {
        let fixture = Fixture::new();
        fixture.write("types.ts", "export interface Shape { value: number }");
        fixture.write("value.ts", "export const value = 1;");
        fixture.write("later.ts", "export const later = 2;");
        fixture.write(
            "main.ts",
            "import type { Shape } from './types.js';\n\
             import { value } from './value.js';\n\
             const observed: Shape = value;\n\
             const pending = import('./later.js');\n\
             void pending;",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let dependencies = program.entrypoint().dependencies();

        assert_eq!(
            names(&program),
            ["types.ts", "value.ts", "later.ts", "main.ts"]
        );
        assert_eq!(dependencies[0].kind(), ModuleEdgeKind::TypeOnly);
        assert_eq!(dependencies[0].flavor(), ResolutionFlavor::Types);
        assert_eq!(dependencies[0].mode(), ResolutionMode::Import);
        assert_eq!(dependencies[1].kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(dependencies[1].flavor(), ResolutionFlavor::Runtime);
        assert_eq!(dependencies[1].mode(), ResolutionMode::Import);
        assert_eq!(dependencies[2].kind(), ModuleEdgeKind::DynamicRuntime);
        assert_eq!(dependencies[2].flavor(), ResolutionFlavor::Runtime);
        assert_eq!(dependencies[2].mode(), ResolutionMode::Import);
    }

    #[test]
    fn import_equals_require_pins_require_mode_and_condition_target() {
        let fixture = Fixture::new();
        fixture.write(
            "node_modules/waybread/package.json",
            r#"{"name":"waybread","exports":{".":{"import":"./esm.js","require":"./cjs.js"}}}"#,
        );
        fixture.write("node_modules/waybread/esm.ts", "export const crumb = 1;");
        fixture.write("node_modules/waybread/cjs.ts", "export const crumb = 2;");
        fixture.write(
            "main.ts",
            "import loaf = require('waybread');\n\
             import { crumb } from 'waybread';\n\
             void loaf; void crumb;",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let dependencies = program.entrypoint().dependencies();

        assert_eq!(names(&program), ["cjs.ts", "esm.ts", "main.ts"]);
        assert_eq!(dependencies[0].kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(dependencies[0].flavor(), ResolutionFlavor::Runtime);
        assert_eq!(dependencies[0].mode(), ResolutionMode::Require);
        assert!(matches!(dependencies[0].target(), ModuleTarget::Local(_)));
        assert_eq!(dependencies[1].kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(dependencies[1].flavor(), ResolutionFlavor::Runtime);
        assert_eq!(dependencies[1].mode(), ResolutionMode::Import);
        assert!(matches!(dependencies[1].target(), ModuleTarget::Local(_)));
    }

    #[test]
    fn declaration_importer_edges_resolve_with_types_flavor() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import './lib';");
        fixture.write("lib.d.ts", "import './peer';");
        fixture.write("peer.ts", "export const value = 1;");

        let program = fixture.loader().load("main.ts").unwrap();

        assert_eq!(names(&program), ["peer.ts", "lib.d.ts", "main.ts"]);
        assert_eq!(
            program.entrypoint().dependencies()[0].flavor(),
            ResolutionFlavor::Runtime
        );
        let lib = &program.modules()[1];
        assert_eq!(
            lib.path().file_name().and_then(|name| name.to_str()),
            Some("lib.d.ts")
        );
        assert_eq!(lib.dependencies()[0].flavor(), ResolutionFlavor::Types);
        assert_eq!(lib.dependencies()[0].mode(), ResolutionMode::Import);
    }

    #[test]
    fn lowers_and_verifies_every_manifest_pinned_corpus_program() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .unwrap();
        let manifest = fs::read_to_string(repository.join("corpus/manifest.toml")).unwrap();
        let entrypoints: Vec<_> = manifest
            .lines()
            .filter_map(|line| {
                line.strip_prefix("entrypoint = \"")
                    .and_then(|value| value.strip_suffix('"'))
            })
            .collect();
        assert!(
            !entrypoints.is_empty(),
            "corpus manifest must declare projects"
        );

        let root = ProjectRoot::new(repository).unwrap();
        let config = ProjectConfig::parse(&root, root.path().join("tsconfig.json"), "{}").unwrap();
        let loader = ProgramLoader::new(&root, config.options()).unwrap();
        for entrypoint in entrypoints {
            let resolved = loader
                .load(entrypoint)
                .unwrap_or_else(|error| panic!("{entrypoint}: {error}"));
            let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
            let executable = lower_program(
                &resolved,
                &frontend,
                LowerOptions {
                    javascript_compatibility: true,
                },
            )
            .unwrap_or_else(|error| panic!("{entrypoint}: {error}"));
            assert_eq!(executable.wire().modules().len(), resolved.modules().len());
        }
    }

    #[test]
    fn compiler_module_option_controls_commonjs_wrapper_bindings() {
        let fixture = Fixture::new();
        fixture.write(
            "main.ts",
            "module; exports; require; __filename; __dirname;",
        );

        let commonjs = fixture
            .loader_with_config(r#"{"compilerOptions": {"module": "CommonJS"}}"#)
            .load("main.ts")
            .unwrap();
        assert!(commonjs.is_commonjs());
        let commonjs_frontend = compile_program_frontend(&commonjs, FrontendMode::Check);
        assert!(commonjs_frontend.modules().iter().all(|module| {
            module
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code().as_str() != "BAMTS-C002")
        }));

        let esm = fixture.loader().load("main.ts").unwrap();
        assert!(!esm.is_commonjs());
        let esm_frontend = compile_program_frontend(&esm, FrontendMode::Check);
        assert!(esm_frontend.modules().iter().any(|module| {
            module
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code().as_str() == "BAMTS-C002")
        }));
    }

    #[test]
    fn jsx_runtime_linkage_adds_default_runtime_to_resolved_graph() {
        let fixture = Fixture::new();
        fixture.write(
            "main.tsx",
            "import { jsx as authored } from 'react/jsx-runtime'; void authored; export const view = <div />;",
        );
        fixture.write(
            "node_modules/react/package.json",
            r#"{"name":"react","exports":{"./jsx-runtime":"./jsx-runtime.ts"}}"#,
        );
        fixture.write(
            "node_modules/react/jsx-runtime.ts",
            "export function jsx() {} export function jsxs() {} export const Fragment = 0;",
        );

        let program = fixture
            .loader_with_config(r#"{"compilerOptions":{"jsx":"react-jsx"}}"#)
            .load("main.tsx")
            .unwrap();
        let main = program.entrypoint();
        let runtime = main
            .dependencies()
            .iter()
            .find(|edge| edge.specifier() == "react/jsx-runtime")
            .expect("automatic JSX creates one ordinary runtime dependency");
        assert_eq!(runtime.kind(), ModuleEdgeKind::StaticRuntime);
        assert_eq!(
            main.dependencies()
                .iter()
                .filter(|edge| edge.specifier() == "react/jsx-runtime")
                .count(),
            1,
            "source-authored and generated runtime demand share one edge"
        );
        let ModuleTarget::Local(runtime_id) = runtime.target() else {
            panic!("fixture runtime resolves through the canonical local graph");
        };
        assert_eq!(
            program.module(*runtime_id).unwrap().path(),
            fixture.0.join("node_modules/react/jsx-runtime.ts")
        );
    }

    #[test]
    fn jsx_runtime_linkage_reuses_runtime_node_across_roots() {
        let fixture = Fixture::new();
        fixture.write("a.tsx", "export const a = <div />;");
        fixture.write("b.tsx", "export const b = <span />;");
        fixture.write(
            "runtime/jsx-runtime.ts",
            "export function jsx() {} export function jsxs() {} export const Fragment = 0;",
        );
        let program = fixture
            .loader_with_config(
                r#"{"compilerOptions":{"jsx":"react-jsx","jsxImportSource":"./runtime"}}"#,
            )
            .load_roots(&[PathBuf::from("b.tsx"), PathBuf::from("a.tsx")])
            .unwrap();
        let runtime_targets: Vec<_> = program
            .roots()
            .iter()
            .map(|root| {
                program
                    .module(*root)
                    .unwrap()
                    .dependencies()
                    .iter()
                    .find(|edge| edge.specifier() == "./runtime/jsx-runtime")
                    .unwrap()
                    .target()
                    .clone()
            })
            .collect();
        assert_eq!(runtime_targets[0], runtime_targets[1]);
        assert_eq!(
            program
                .modules()
                .iter()
                .filter(|module| module.path().ends_with("runtime/jsx-runtime.ts"))
                .count(),
            1
        );
    }

    #[test]
    fn jsx_runtime_linkage_reports_missing_runtime_through_resolver() {
        let fixture = Fixture::new();
        fixture.write("main.tsx", "export const view = <div />;");
        let error = fixture
            .loader_with_config(r#"{"compilerOptions":{"jsx":"react-jsx"}}"#)
            .load("main.tsx")
            .expect_err("missing automatic runtime must be a module-resolution error");
        let ProgramLoadError::UnresolvedModule(diagnostic) = error else {
            panic!("expected typed unresolved-module diagnostic");
        };
        assert_eq!(diagnostic.specifier(), "react/jsx-runtime");
    }

    #[test]
    fn jsx_runtime_linkage_uses_dev_source_and_collision_free_imported_bindings() {
        let fixture = Fixture::new();
        fixture.write(
            "main.tsx",
            "const __bamts_jsx_jsxDEV = 0; export const view = <><div /></>;",
        );
        fixture.write(
            "runtime/jsx-dev-runtime.ts",
            "export function jsxDEV() {} export const Fragment = 0;",
        );
        let resolved = fixture
            .loader_with_config(
                r#"{"compilerOptions":{"jsx":"react-jsxdev","jsxImportSource":"./runtime"}}"#,
            )
            .load("main.tsx")
            .unwrap();
        assert!(resolved.entrypoint().dependencies().iter().any(|edge| {
            edge.kind() == ModuleEdgeKind::StaticRuntime
                && edge.specifier() == "./runtime/jsx-dev-runtime"
        }));

        let frontend = compile_program_frontend(&resolved, FrontendMode::Check);
        let executable = lower_program(
            &resolved,
            &frontend,
            LowerOptions {
                javascript_compatibility: true,
            },
        )
        .unwrap();
        let main = module(&executable, "main.tsx");
        let imported: Vec<_> = main
            .bindings()
            .iter()
            .filter_map(|binding| match binding.kind {
                BindingKind::Imported { name, .. } => Some((
                    constant_string(main, binding.name),
                    constant_string(main, name),
                )),
                _ => None,
            })
            .collect();
        assert!(imported.contains(&("__bamts_jsx_jsxDEV_2".to_owned(), "jsxDEV".to_owned())));
        assert!(imported.contains(&("__bamts_jsx_Fragment".to_owned(), "Fragment".to_owned())));
        assert!(
            main.bindings()
                .iter()
                .all(|binding| constant_string(main, binding.name) != "_jsxDEV")
        );
    }

    #[test]
    fn jsx_runtime_linkage_preserve_and_classic_add_no_runtime_edge() {
        for jsx in ["preserve", "react"] {
            let fixture = Fixture::new();
            fixture.write("main.tsx", "export const view = <div />;");
            let config = format!(r#"{{"compilerOptions":{{"jsx":"{jsx}"}}}}"#);
            let program = fixture
                .loader_with_config(&config)
                .load("main.tsx")
                .unwrap();
            assert!(program.entrypoint().dependencies().is_empty(), "{jsx}");
        }
    }

    #[test]
    fn jsx_options_survive_loading_and_select_one_output_route() {
        let fixture = Fixture::new();
        fixture.write("main.tsx", "export const view = 1;");
        let program = fixture
            .loader_with_config(
                r#"{"compilerOptions":{
                    "jsx":"react-jsx",
                    "jsxFactory":"h",
                    "jsxFragmentFactory":"Fragment",
                    "jsxImportSource":"@scope/runtime"
                }}"#,
            )
            .load("main.tsx")
            .unwrap();

        assert_eq!(program.jsx(), Some(JsxEmit::ReactJsx));
        assert_eq!(program.jsx_factory(), Some("h"));
        assert_eq!(program.jsx_fragment_factory(), Some("Fragment"));
        assert_eq!(program.jsx_import_source(), Some("@scope/runtime"));
        assert_eq!(
            program.jsx_routing_decision(ProgramOutputKind::JavaScript),
            JsxRoutingDecision::TransformAndEmit
        );
        assert_eq!(
            program.jsx_routing_decision(ProgramOutputKind::NativeExecutable),
            JsxRoutingDecision::Lower
        );
    }
    #[test]
    fn declaration_overlay_preserves_runtime_target_identity() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import Queue from './index.js'; void Queue;");
        fixture.write("index.js", "export default class Queue {}");
        fixture.write(
            "index.d.ts",
            "export default class Queue<Value> { value: Value; }",
        );

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];
        let runtime_id = edge
            .target()
            .local_source_id()
            .expect("local runtime target");
        let type_id = edge
            .type_target()
            .and_then(ModuleTarget::local_source_id)
            .expect("local declaration overlay");

        assert_ne!(runtime_id, type_id);
        assert!(
            program
                .module(runtime_id)
                .unwrap()
                .path()
                .ends_with("index.js")
        );
        assert!(
            program
                .module(type_id)
                .unwrap()
                .path()
                .ends_with("index.d.ts")
        );
        assert!(
            program
                .module(type_id)
                .unwrap()
                .source()
                .is_declaration_file()
        );
        assert_eq!(
            program
                .runtime_modules()
                .iter()
                .filter(|module| module.source_id() == type_id)
                .count(),
            0,
            "checker overlay must not enter the eager runtime closure"
        );
    }

    #[test]
    fn runtime_edge_without_declaration_overlay_has_no_type_target() {
        let fixture = Fixture::new();
        fixture.write("main.ts", "import Queue from './index.js'; void Queue;");
        fixture.write("index.js", "export default class Queue {}");

        let program = fixture.loader().load("main.ts").unwrap();
        let edge = &program.entrypoint().dependencies()[0];

        assert!(edge.target().local_source_id().is_some());
        assert!(edge.type_target().is_none());
        assert_eq!(names(&program), ["index.js", "main.ts"]);
    }

    #[test]
    fn program_loader_enforces_source_budgets_and_stable_codes() {
        assert_eq!(
            super::accumulate_session_bytes(0, super::MAX_SESSION_SOURCE_BYTES),
            Ok(super::MAX_SESSION_SOURCE_BYTES)
        );
        assert_eq!(
            super::accumulate_session_bytes(super::MAX_SESSION_SOURCE_BYTES - 1, 2),
            Err(super::MAX_SESSION_SOURCE_BYTES + 1)
        );
        assert_eq!(
            super::accumulate_session_bytes(usize::MAX, 1),
            Err(usize::MAX)
        );

        let fixture = Fixture::new();
        fixture.write("main.ts", "import './left'; import './right';");
        fixture.write("left.ts", "import './shared';");
        fixture.write("right.ts", "import './shared';");
        fixture.write("shared.ts", "export const shared = 1;");
        let program = fixture.loader().load("main.ts").unwrap();
        assert_eq!(program.modules().len(), 4, "diamond imports load once");

        let exact = "a".repeat(crate::source::MAX_SOURCE_BYTES);
        fixture.write("exact.ts", &exact);
        fixture.loader().load("exact.ts").unwrap();

        let oversized = "a".repeat(crate::source::MAX_SOURCE_BYTES + 1);
        fixture.write("oversized.ts", &oversized);
        let error = fixture.loader().load("oversized.ts").unwrap_err();
        let ProgramLoadError::SourceTooLarge { path, len } = &error else {
            panic!("expected SourceTooLarge, got {error}");
        };
        assert_eq!(*len, crate::source::MAX_SOURCE_BYTES + 1);
        assert!(path.ends_with("oversized.ts"));
        assert_eq!(error.code(), Some(super::SOURCE_TOO_LARGE));
        assert!(std::error::Error::source(&error).is_none());

        let session = ProgramLoadError::SessionTooLarge {
            path: PathBuf::from("next.ts"),
            total: super::MAX_SESSION_SOURCE_BYTES + 1,
        };
        assert_eq!(session.code(), Some(super::SESSION_TOO_LARGE));
        assert!(session.to_string().contains("next.ts"));
        assert!(std::error::Error::source(&session).is_none());
    }

    /// Loads one file and returns its checker-facing effective configuration.
    fn resolved(main: &str, compiler_options: &str) -> ResolvedProgram {
        let fixture = Fixture::new();
        fixture.write("main.ts", main);
        let config = format!(r#"{{"compilerOptions":{compiler_options}}}"#);
        fixture
            .loader_with_config(&config)
            .load("main.ts")
            .expect("resolved program")
    }

    #[test]
    fn strict_family_options_reach_the_checker_environment() {
        // The suite default (see check_cells.rs build_tsconfig) is strict:true
        // unless a case pragma says otherwise, so strict-on is the wired shape.
        let options = resolved("export const value = 1;", r#"{"strict":true}"#).check_options();
        assert!(options.no_implicit_any());
        assert!(options.strict_null_checks());
        assert!(options.strict_property_initialization());
        assert!(options.always_strict());
        assert!(!options.is_commonjs());
        let off = resolved("export const value = 1;", r#"{"strict":false}"#).check_options();
        assert!(!off.no_implicit_any());
        assert!(!off.strict_null_checks());
        assert!(!off.strict_property_initialization());
        assert!(!off.always_strict());
    }

    #[test]
    fn individual_strict_members_override_the_master_switch() {
        // Upstream optionsStrictPropertyInitializationStrict.ts (sha256
        // 4c5f28823ac849778d69aed835f56cfff163dfb871c3d31496a0d0b46531c749)
        // pairs `strict` with explicit strictPropertyInitialization; the
        // showConfig baselines pin the member names as overridable:
        // noImplicitAny 35227919..., strictNullChecks 385f6fd5...,
        // strictPropertyInitialization b3dadd75...
        let mixed = resolved(
            "export const value = 1;",
            r#"{"strict":true,"noImplicitAny":false,"strictNullChecks":false,
                "strictPropertyInitialization":false,"alwaysStrict":false}"#,
        )
        .check_options();
        assert!(!mixed.no_implicit_any());
        assert!(!mixed.strict_null_checks());
        assert!(!mixed.strict_property_initialization());
        assert!(!mixed.always_strict());
    }

    #[test]
    fn module_and_target_still_select_environment_and_es5() {
        let es5 = resolved(
            "export const value = 1;",
            r#"{"module":"commonjs","target":"es5","alwaysStrict":true}"#,
        )
        .check_options();
        assert!(es5.is_commonjs());
        assert!(es5.es5());
        assert!(es5.always_strict());
    }

    #[test]
    fn check_options_drives_end_to_end_diagnostics() {
        // Upstream abstractClassUnionInstantiation.ts (sha256
        // 012bd00d5213a672086b74643b36cf3f252b4a7e96b5950d2f8121ae725581c5)
        // baseline errors.txt (sha256 20f79cd3...) expects TS2564 rows for
        // abstract properties; with strict-on plumbing they must surface.
        let program = resolved(
            "abstract class A { a: string; }\nnew A();\n",
            r#"{"strict":true}"#,
        );
        let frontend = compile_program_frontend(&program, FrontendMode::Check);
        let strict_on: Vec<_> = frontend
            .modules()
            .iter()
            .flat_map(|module| module.diagnostics().iter())
            .filter(|diagnostic| diagnostic.code().as_str() == "BAMTS-C028")
            .collect();
        assert_eq!(strict_on.len(), 1, "{strict_on:?}");

        let permissive = resolved(
            "abstract class A { a: string; }\nnew A();\n",
            r#"{"strict":false}"#,
        );
        let frontend = compile_program_frontend(&permissive, FrontendMode::Check);
        let permissive_strict_on: Vec<_> = frontend
            .modules()
            .iter()
            .flat_map(|module| module.diagnostics().iter())
            .filter(|diagnostic| diagnostic.code().as_str() == "BAMTS-C028")
            .collect();
        assert!(permissive_strict_on.is_empty(), "{permissive_strict_on:?}");
        // The same program must report the flag through its checker view.
        assert!(permissive.check_options() == ProgramCheckOptions::standard());
    }
}
