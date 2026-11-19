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
        resolution::{
            ModuleResolutionKind, ResolutionCache, ResolutionHost, ResolutionMode,
            resolve_module_name, resolve_type_reference,
        },
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

/// Which triple-slash reference directive introduced an edge, if any.
///
/// A `Some` value marks an edge collected from a leading
/// `/// <reference ... />` comment rather than from an import or export
/// statement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReferenceDirectiveKind {
    Path,
    Types,
    Lib,
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
    unresolved: bool,
    directive: Option<ReferenceDirectiveKind>,
}
impl ModuleEdge {
    #[must_use]
    pub const fn kind(&self) -> ModuleEdgeKind {
        self.kind
    }

    /// Which triple-slash reference directive introduced this edge, if any.
    #[must_use]
    pub const fn reference_directive(&self) -> Option<ReferenceDirectiveKind> {
        self.directive
    }

    /// Whether a tolerant load found nothing for this specifier.
    #[must_use]
    pub const fn is_unresolved(&self) -> bool {
        self.unresolved
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
    module_kind: Option<crate::emitter::ModuleKind>,
    /// For a Node module mode, the format each module emits as, by module index.
    node_formats: Arc<[crate::emitter::ModuleKind]>,
    no_implicit_any: bool,
    strict_null_checks: bool,
    strict_property_initialization: bool,
    always_strict: bool,
    no_emit_helpers: bool,
    remove_comments: bool,
    source_map: bool,
    inline_source_map: bool,
    inline_sources: bool,
    use_define_for_class_fields: Option<bool>,
    experimental_decorators: bool,
    emit_decorator_metadata: bool,
    import_helpers: Option<bool>,
    es_module_interop: Option<bool>,
    verbatim_module_syntax: bool,
    target: crate::emitter::ScriptTarget,
    libs: crate::checker::intrinsic_environment::LibSet,
    check_js: bool,
    no_unused_locals: bool,
    jsx_custom_factory: bool,
    no_unused_parameters: bool,
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
    pub const fn source_map(&self) -> bool {
        self.source_map
    }

    #[must_use]
    pub const fn inline_source_map(&self) -> bool {
        self.inline_source_map
    }

    #[must_use]
    pub const fn inline_sources(&self) -> bool {
        self.inline_sources
    }

    #[must_use]
    pub const fn experimental_decorators(&self) -> bool {
        self.experimental_decorators
    }

    #[must_use]
    pub const fn emit_decorator_metadata(&self) -> bool {
        self.emit_decorator_metadata
    }

    #[must_use]
    pub const fn import_helpers(&self) -> Option<bool> {
        self.import_helpers
    }

    #[must_use]
    pub const fn es_module_interop(&self) -> Option<bool> {
        self.es_module_interop
    }

    #[must_use]
    pub const fn verbatim_module_syntax(&self) -> bool {
        self.verbatim_module_syntax
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

    /// The module kind the module at `index` emits as, when the options give it
    /// one: CommonJS, the AMD, UMD, and System wrappers, or the per-file format a
    /// Node module mode derives from extension and package type.
    #[must_use]
    pub fn emit_module_kind(&self, index: usize) -> Option<crate::emitter::ModuleKind> {
        use crate::emitter::ModuleKind;
        if self.commonjs {
            return Some(ModuleKind::CommonJs);
        }
        match self.module_kind? {
            ModuleKind::Node => self.node_formats.get(index).copied(),
            kind @ (ModuleKind::Amd | ModuleKind::Umd | ModuleKind::System) => Some(kind),
            _ => None,
        }
    }

    /// Whether `module` is a Node mode, where dynamic `import()` is never lowered.
    #[must_use]
    pub fn is_node_module_mode(&self) -> bool {
        self.module_kind == Some(crate::emitter::ModuleKind::Node)
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
        .with_remove_comments(self.remove_comments)
        .with_script_target(self.target)
        .with_libs(self.libs)
        .with_check_js(self.check_js)
        .with_no_unused_locals(self.no_unused_locals)
        .with_no_unused_parameters(self.no_unused_parameters)
        .with_jsx(self.jsx)
        .with_jsx_custom_factory(self.jsx_custom_factory)
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
    tolerate_unresolved: bool,
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
            tolerate_unresolved: false,
        })
    }

    /// Keeps loading past an import nothing can satisfy, for a run that only
    /// checks, as `tsc` does. The frontend reports each one, so a project sees
    /// all of them at once. A run that will execute must not use this: the
    /// program has to fail before it starts.
    #[must_use]
    pub const fn tolerating_unresolved_imports(mut self) -> Self {
        self.tolerate_unresolved = true;
        self
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
        let module_kind = self.options.module().and_then(crate::emitter::parse_module);
        let node_formats = if module_kind == Some(crate::emitter::ModuleKind::Node) {
            node_module_formats(&state.modules, &self.root, self.fs.as_ref())
        } else {
            Arc::from([])
        };
        Ok(ResolvedProgram {
            root: self.root.clone(),
            roots: Arc::from(root_ids),
            modules: Arc::from(state.modules),
            module_indices,
            commonjs: ambient == ResolutionMode::Require,
            module_kind,
            node_formats,
            no_implicit_any: self.options.no_implicit_any(),
            strict_null_checks: self.options.strict_null_checks(),
            strict_property_initialization: self.options.strict_property_initialization(),
            always_strict: self.options.always_strict(),
            no_emit_helpers: self.options.no_emit_helpers(),
            remove_comments: self.options.remove_comments(),
            source_map: self.options.source_map(),
            inline_source_map: self.options.inline_source_map(),
            inline_sources: self.options.inline_sources(),
            use_define_for_class_fields: self.options.use_define_for_class_fields(),
            experimental_decorators: self.options.experimental_decorators(),
            emit_decorator_metadata: self.options.emit_decorator_metadata(),
            import_helpers: self.options.import_helpers(),
            es_module_interop: self.options.es_module_interop(),
            verbatim_module_syntax: self.options.verbatim_module_syntax(),
            target,
            libs,
            no_unused_parameters: self.options.no_unused_parameters(),
            check_js: self.options.check_js(),
            no_unused_locals: self.options.no_unused_locals(),
            jsx_custom_factory: self.options.jsx_custom_factory(),
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
        if let Some(directive) = edge.directive {
            return self.resolve_directive(importer, edge, directive, cancel);
        }
        if self.tolerate_unresolved {
            return self.resolve_edge_for_check(importer, edge, flavor, cancel);
        }
        if let Some(target) = self.resolve_local(importer, edge, flavor, cancel)? {
            let type_overlay = self.type_overlay(importer, edge, &target, cancel)?;
            return Ok(ResolvedEdge {
                target,
                type_overlay,
                flavor,
            });
        }
        if flavor == ResolutionFlavor::Types
            && !self.uses_classic_resolution()
            && split_package_specifier(&edge.specifier).is_some()
        {
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

    /// Resolves an edge for a run that only checks. A package the runtime
    /// could not use can still type-check, so `tsc`'s own algorithm gets the
    /// last word, and what that cannot find becomes a reported edge.
    fn resolve_edge_for_check(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
        cancel: &CancellationToken,
    ) -> Result<ResolvedEdge, ProgramLoadError> {
        let local = Self::missing_when_invalid(self.resolve_local(importer, edge, flavor, cancel))?;
        if let Some(target) = local {
            let type_overlay =
                Self::missing_when_invalid(self.type_overlay(importer, edge, &target, cancel))?;
            return Ok(ResolvedEdge {
                target,
                type_overlay,
                flavor,
            });
        }
        let target = match self.resolve_as_tsc(importer, edge) {
            Some(path) => ResolvedEdgeTarget::Local(path),
            None => ResolvedEdgeTarget::Unresolved(Arc::clone(&edge.specifier)),
        };
        Ok(ResolvedEdge {
            target,
            type_overlay: None,
            flavor,
        })
    }
    fn resolve_directive(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        directive: ReferenceDirectiveKind,
        cancel: &CancellationToken,
    ) -> Result<ResolvedEdge, ProgramLoadError> {
        let flavor = ResolutionFlavor::Types;
        match directive {
            ReferenceDirectiveKind::Lib => Ok(ResolvedEdge {
                target: ResolvedEdgeTarget::External(Arc::from(format!("lib:{}", edge.specifier))),
                type_overlay: None,
                flavor,
            }),
            ReferenceDirectiveKind::Types => {
                if let Some(path) =
                    self.resolve_type_directive(importer, &edge.specifier, edge.mode)?
                {
                    return Ok(ResolvedEdge {
                        target: ResolvedEdgeTarget::Local(path),
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
            ReferenceDirectiveKind::Path => {
                let rewritten =
                    reference_path_target(&edge.specifier).map(|target| UnresolvedEdge {
                        kind: edge.kind,
                        mode: edge.mode,
                        specifier: target,
                        range: edge.range,
                        directive: edge.directive,
                    });
                let probe = rewritten.as_ref().unwrap_or(edge);
                if let Some(target) = self.resolve_local(importer, probe, flavor, cancel)? {
                    let type_overlay = self.type_overlay(importer, probe, &target, cancel)?;
                    return Ok(ResolvedEdge {
                        target,
                        type_overlay,
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
        }
    }

    fn resolve_type_directive(
        &self,
        importer: &Path,
        specifier: &str,
        mode: ResolutionMode,
    ) -> Result<Option<PathBuf>, ProgramLoadError> {
        let kind = ModuleResolutionKind::from_options(&self.options)
            .unwrap_or(ModuleResolutionKind::Bundler);
        let host = LoaderResolutionHost(self.fs.as_ref());
        let mut cache = ResolutionCache::new();
        match resolve_type_reference(
            &self.root,
            &self.options,
            importer,
            specifier,
            (kind, mode),
            &host,
            &mut cache,
        ) {
            Ok(resolved) => self
                .fs
                .normalize(resolved.path())
                .map(Some)
                .map_err(|error| ProgramLoadError::Read {
                    path: resolved.path().to_path_buf(),
                    source: file_system_io(error),
                }),
            Err(_) => Ok(None),
        }
    }

    /// Reads a package or specifier the runtime rules refused as not found.
    fn missing_when_invalid<T>(
        resolved: Result<Option<T>, ProgramLoadError>,
    ) -> Result<Option<T>, ProgramLoadError> {
        match resolved {
            Err(
                ProgramLoadError::InvalidPackage { .. } | ProgramLoadError::InvalidSpecifier { .. },
            ) => Ok(None),
            resolved => resolved,
        }
    }

    fn resolve_as_tsc(&self, importer: &Path, edge: &UnresolvedEdge) -> Option<PathBuf> {
        let kind = ModuleResolutionKind::from_options(&self.options)
            .unwrap_or(ModuleResolutionKind::Bundler);
        let strategy = (kind, edge.mode);
        let host = LoaderResolutionHost(self.fs.as_ref());
        let mut cache = ResolutionCache::new();
        let specifier = &*edge.specifier;
        let root = &self.root;
        let options = &self.options;
        resolve_type_reference(
            root, options, importer, specifier, strategy, &host, &mut cache,
        )
        .or_else(|_| {
            resolve_module_name(
                root, options, importer, specifier, strategy, &host, &mut cache,
            )
        })
        .ok()
        .and_then(|resolved| self.fs.normalize(resolved.path()).ok())
    }

    /// Whether the options pin `moduleResolution: classic`, the only kind the
    /// loader routes through the traced classic resolver.
    fn uses_classic_resolution(&self) -> bool {
        ModuleResolutionKind::from_options(&self.options) == Ok(ModuleResolutionKind::Classic)
    }

    fn resolve_classic_edge(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
    ) -> Result<Option<ResolvedEdgeTarget>, ProgramLoadError> {
        let strategy = (ModuleResolutionKind::Classic, edge.mode);
        let host = LoaderResolutionHost(self.fs.as_ref());
        let mut cache = ResolutionCache::new();
        let outcome = if flavor == ResolutionFlavor::Types {
            resolve_type_reference(
                &self.root,
                &self.options,
                importer,
                &edge.specifier,
                strategy,
                &host,
                &mut cache,
            )
        } else {
            resolve_module_name(
                &self.root,
                &self.options,
                importer,
                &edge.specifier,
                strategy,
                &host,
                &mut cache,
            )
        };
        let Some(resolved) = outcome.ok() else {
            return Ok(None);
        };
        let path = self
            .fs
            .normalize(resolved.path())
            .map_err(|error| ProgramLoadError::Read {
                path: resolved.path().to_path_buf(),
                source: file_system_io(error),
            })?;
        Ok(Some(ResolvedEdgeTarget::Local(path)))
    }

    fn resolve_local(
        &self,
        importer: &Path,
        edge: &UnresolvedEdge,
        flavor: ResolutionFlavor,
        cancel: &CancellationToken,
    ) -> Result<Option<ResolvedEdgeTarget>, ProgramLoadError> {
        if self.uses_classic_resolution() {
            return self.resolve_classic_edge(importer, edge, flavor);
        }
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
                            directive: edge.directive,
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
    /// Nothing satisfies the specifier, and the load was told to continue.
    Unresolved(Arc<str>),
}

/// The loader's filesystem, as `tsc`'s resolution algorithm reads it.
struct LoaderResolutionHost<'a>(&'a dyn FileSystem);

impl ResolutionHost for LoaderResolutionHost<'_> {
    fn file_exists(&self, path: &Path) -> bool {
        self.0.metadata(path).is_ok() && !self.directory_exists(path)
    }

    fn directory_exists(&self, path: &Path) -> bool {
        self.0.read_dir(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> Option<Arc<str>> {
        self.0.read(path).ok().map(Arc::from)
    }
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
                            unresolved: false,
                            directive: pending.edge.directive,
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
                            directive: None,
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
                            let resolved = match self.loader.resolve_edge(
                                &frame.path,
                                &edge,
                                self.cancel,
                            ) {
                                Ok(resolved) => resolved,
                                Err(error)
                                    if edge.kind == ModuleEdgeKind::DynamicRuntime
                                        && matches!(
                                            error,
                                            ProgramLoadError::UnresolvedModule(_)
                                                | ProgramLoadError::InvalidSpecifier { .. }
                                                | ProgramLoadError::InvalidPackage { .. }
                                                | ProgramLoadError::UnsupportedSource(_)
                                                | ProgramLoadError::Read { .. }
                                                | ProgramLoadError::Source { .. }
                                                | ProgramLoadError::IllFormedModuleSpecifier { .. }
                                                | ProgramLoadError::TraversalRejected { .. }
                                                | ProgramLoadError::JsxPlan { .. }
                                        ) =>
                                {
                                    frame.dependencies.push(ModuleEdge {
                                        kind: edge.kind,
                                        flavor: crate::project::ResolutionFlavor::Runtime,
                                        mode: edge.mode,
                                        specifier: Arc::clone(&edge.specifier),
                                        target: ModuleTarget::External(Arc::clone(&edge.specifier)),
                                        type_target: None,
                                        range: edge.range,
                                        unresolved: true,
                                        directive: edge.directive,
                                    });
                                    continue;
                                }
                                Err(error)
                                    if edge.kind == ModuleEdgeKind::TypeOnly
                                        && edge.directive.is_some()
                                        && matches!(
                                            error,
                                            ProgramLoadError::UnresolvedModule(_)
                                                | ProgramLoadError::InvalidSpecifier { .. }
                                                | ProgramLoadError::InvalidPackage { .. }
                                                | ProgramLoadError::UnsupportedSource(_)
                                                | ProgramLoadError::Read { .. }
                                                | ProgramLoadError::Source { .. }
                                                | ProgramLoadError::IllFormedModuleSpecifier { .. }
                                                | ProgramLoadError::TraversalRejected { .. }
                                                | ProgramLoadError::JsxPlan { .. }
                                        ) =>
                                {
                                    frame.dependencies.push(ModuleEdge {
                                        kind: edge.kind,
                                        flavor: crate::project::ResolutionFlavor::Types,
                                        mode: edge.mode,
                                        specifier: Arc::clone(&edge.specifier),
                                        target: ModuleTarget::External(Arc::clone(&edge.specifier)),
                                        type_target: None,
                                        range: edge.range,
                                        unresolved: true,
                                        directive: edge.directive,
                                    });
                                    continue;
                                }
                                Err(error) => return Err(error),
                            };
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
                                        unresolved: false,
                                        directive: edge.directive,
                                    });
                                }
                                ResolvedEdgeTarget::Unresolved(specifier) => {
                                    frame.dependencies.push(ModuleEdge {
                                        kind: edge.kind,
                                        flavor: resolved.flavor,
                                        mode: edge.mode,
                                        specifier: edge.specifier,
                                        target: ModuleTarget::External(specifier),
                                        type_target: None,
                                        range: edge.range,
                                        unresolved: true,
                                        directive: edge.directive,
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
                        unresolved: false,
                        directive: pending.edge.directive,
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
    directive: Option<ReferenceDirectiveKind>,
}

fn collect_edges(
    source: &SourceFile,
    ambient: ResolutionMode,
) -> Result<Vec<UnresolvedEdge>, TextRange> {
    let mut edges = Vec::new();
    collect_reference_directives(source, ambient, &mut edges);
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
            directive: None,
        });
    }
    Ok(edges)
}

fn collect_reference_directives(
    source: &SourceFile,
    ambient: ResolutionMode,
    edges: &mut Vec<UnresolvedEdge>,
) {
    let boundary = source
        .statements()
        .first()
        .map(|statement| statement.range().start());
    for token in source.tokens() {
        if boundary.is_some_and(|end| token.range().start() >= end) {
            break;
        }
        if token.kind() != TokenKind::LineComment {
            continue;
        }
        let Some(text) = source.token_text(token) else {
            continue;
        };
        parse_reference_directive(source, text, token, ambient, edges);
    }
}

fn parse_reference_directive(
    source: &SourceFile,
    text: &str,
    token: &crate::syntax::Token,
    ambient: ResolutionMode,
    edges: &mut Vec<UnresolvedEdge>,
) {
    let bytes = text.as_bytes();
    if bytes.len() < 3 || &bytes[..3] != b"///" || bytes.get(3) == Some(&b'/') {
        return;
    }
    let tag = b"<reference";
    let mut cursor = 3;
    while cursor + tag.len() <= bytes.len() && &bytes[cursor..cursor + tag.len()] != tag {
        cursor += 1;
    }
    if cursor + tag.len() > bytes.len() {
        return;
    }
    cursor += tag.len();
    loop {
        skip_ascii_whitespace(bytes, &mut cursor);
        if bytes.get(cursor) == Some(&b'/') {
            cursor += 1;
        }
        if bytes.get(cursor) == Some(&b'>') {
            break;
        }
        let Some(attribute) = next_directive_attribute(text, &mut cursor) else {
            return;
        };
        let kind = match attribute.name {
            "path" => ReferenceDirectiveKind::Path,
            "types" => ReferenceDirectiveKind::Types,
            "lib" => ReferenceDirectiveKind::Lib,
            _ => continue,
        };
        edges.push(UnresolvedEdge {
            kind: ModuleEdgeKind::TypeOnly,
            mode: ambient,
            specifier: Arc::from(attribute.value),
            range: directive_value_range(
                source,
                token,
                text,
                attribute.value_start,
                attribute.value_end,
            ),
            directive: Some(kind),
        });
    }
}

struct DirectiveAttribute<'a> {
    name: &'a str,
    value: &'a str,
    value_start: usize,
    value_end: usize,
}

fn skip_ascii_whitespace(bytes: &[u8], cursor: &mut usize) {
    while bytes.get(*cursor).is_some_and(u8::is_ascii_whitespace) {
        *cursor += 1;
    }
}

fn next_directive_attribute<'a>(
    text: &'a str,
    cursor: &mut usize,
) -> Option<DirectiveAttribute<'a>> {
    let bytes = text.as_bytes();
    let name_start = *cursor;
    while bytes
        .get(*cursor)
        .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'-' || *byte == b'_')
    {
        *cursor += 1;
    }
    if *cursor == name_start {
        return None;
    }
    let name = &text[name_start..*cursor];
    skip_ascii_whitespace(bytes, cursor);
    if bytes.get(*cursor) != Some(&b'=') {
        return None;
    }
    *cursor += 1;
    skip_ascii_whitespace(bytes, cursor);
    let quote = match bytes.get(*cursor) {
        Some(b'"') | Some(b'\'') => bytes[*cursor],
        _ => return None,
    };
    *cursor += 1;
    let value_start = *cursor;
    while bytes.get(*cursor).is_some_and(|byte| *byte != quote) {
        *cursor += 1;
    }
    if bytes.get(*cursor) != Some(&quote) {
        return None;
    }
    let value_end = *cursor;
    *cursor += 1;
    Some(DirectiveAttribute {
        name,
        value: &text[value_start..value_end],
        value_start,
        value_end,
    })
}

fn directive_value_range(
    source: &SourceFile,
    token: &crate::syntax::Token,
    text: &str,
    start: usize,
    end: usize,
) -> TextRange {
    let fallback = token.range();
    let base = source.source_text().utf16_to_byte(token.range().start());
    let Ok(base) = base else {
        return fallback;
    };
    let (Some(value_start), Some(value_end)) = (base.checked_add(start), base.checked_add(end))
    else {
        return fallback;
    };
    if value_end > base + text.len() {
        return fallback;
    }
    let source_text = source.source_text();
    let (Ok(range_start), Ok(range_end)) = (
        source_text.byte_to_utf16(value_start),
        source_text.byte_to_utf16(value_end),
    ) else {
        return fallback;
    };
    TextRange::new(range_start, range_end).unwrap_or(fallback)
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
                ClassMember::IndexSignature(_)
                | ClassMember::Missing(_)
                | ClassMember::Semicolon => {}
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
                    if let AssignmentArrayElement::Target(value)
                    | AssignmentArrayElement::Rest(value) = element
                    {
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
        directive: None,
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

/// Rewrites a `/// <reference path>` value to the relative specifier it
/// names. A path without a `./`, `../`, `/`, or `#` lead is relative to
/// the importing file, never a package name. Values that already carry a
/// lead, or that relative resolution rejects outright, return `None`.
fn reference_path_target(specifier: &str) -> Option<Arc<str>> {
    if specifier.starts_with("./")
        || specifier.starts_with("../")
        || specifier.starts_with('/')
        || specifier.starts_with('#')
        || specifier.contains("://")
        || specifier.contains('?')
    {
        return None;
    }
    Some(Arc::from(format!("./{specifier}")))
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

/// The module format a Node module mode emits for each file: the extension
/// decides, then the `type` of the nearest `package.json`, and a file with
/// neither is CommonJS.
fn node_module_formats(
    modules: &[ResolvedModule],
    root: &ProjectRoot,
    fs: &dyn FileSystem,
) -> Arc<[crate::emitter::ModuleKind]> {
    let mut directories = HashMap::new();
    modules
        .iter()
        .map(|module| node_module_format(module.path(), root, fs, &mut directories))
        .collect()
}

fn node_module_format(
    path: &Path,
    root: &ProjectRoot,
    fs: &dyn FileSystem,
    directories: &mut HashMap<PathBuf, crate::emitter::ModuleKind>,
) -> crate::emitter::ModuleKind {
    use crate::emitter::ModuleKind;
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("mts" | "mjs") => return ModuleKind::EsNext,
        Some("cts" | "cjs") => return ModuleKind::CommonJs,
        _ => {}
    }
    path.parent().map_or(ModuleKind::CommonJs, |directory| {
        directory_module_format(directory, root, fs, directories)
    })
}

fn directory_module_format(
    directory: &Path,
    root: &ProjectRoot,
    fs: &dyn FileSystem,
    directories: &mut HashMap<PathBuf, crate::emitter::ModuleKind>,
) -> crate::emitter::ModuleKind {
    use crate::emitter::ModuleKind;
    if let Some(&format) = directories.get(directory) {
        return format;
    }
    let package_path = directory.join("package.json");
    let package = fs
        .read(&package_path)
        .ok()
        .and_then(|text| PackageJson::parse(root, &package_path, &text).ok());
    let format = match package {
        Some(package) if package.package_type() == Some("module") => ModuleKind::EsNext,
        Some(_) => ModuleKind::CommonJs,
        None => directory.parent().map_or(ModuleKind::CommonJs, |parent| {
            directory_module_format(parent, root, fs, directories)
        }),
    };
    directories.insert(directory.to_path_buf(), format);
    format
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

    let mut static_reachable: HashSet<SourceId> = HashSet::new();
    {
        let mut worklist = vec![resolved.entrypoint_id()];
        static_reachable.insert(resolved.entrypoint_id());
        while let Some(id) = worklist.pop() {
            let Some(current) = resolved.module(id) else {
                continue;
            };
            for dep in current.dependencies() {
                if dep.kind() != ModuleEdgeKind::StaticRuntime {
                    continue;
                }
                if let ModuleTarget::Local(target) = dep.target()
                    && static_reachable.insert(*target)
                {
                    worklist.push(*target);
                }
            }
        }
    }
    let mut excluded: HashSet<SourceId> = HashSet::new();
    let mut stubbed: HashSet<SourceId> = HashSet::new();
    let mut synthetic_id = resolved
        .modules()
        .iter()
        .map(|module| module.source_id().get())
        .max()
        .unwrap_or(0)
        .saturating_add(1);
    loop {
        let kept: Vec<&ResolvedModule> = resolved
            .modules()
            .iter()
            .filter(|module| !excluded.contains(&module.source_id()))
            .collect();
        let new_ids: HashMap<SourceId, ModuleId> = kept
            .iter()
            .enumerate()
            .map(|(index, module)| {
                (
                    module.source_id(),
                    ModuleId::new(u32::try_from(index).expect("kept fits u32")),
                )
            })
            .collect();
        let orig_ids: HashMap<SourceId, ModuleId> = resolved
            .modules()
            .iter()
            .enumerate()
            .map(|(index, module)| {
                (
                    module.source_id(),
                    ModuleId::new(u32::try_from(index).expect("resolved fits u32")),
                )
            })
            .collect();
        let mut raw_modules: Vec<RawModule> = Vec::with_capacity(kept.len());
        let mut stub_codes: HashMap<SourceId, bamts_bytecode::Module<bamts_bytecode::Verified>> =
            HashMap::new();
        for module in &kept {
            check_lower_cancel(cancel, module.path(), ProgramLowerPhase::Metadata)?;
            if stubbed.contains(&module.source_id()) {
                let name =
                    normalized_module_name(resolved.root(), module.path()).ok_or_else(|| {
                        program_lower_error(
                            module.path(),
                            ProgramLowerPhase::Metadata,
                            ProgramLowerErrorKind::InvalidModuleName,
                        )
                    })?;
                let stub_raw = RawModule {
                    name: name.clone(),
                    edges: Vec::new(),
                    bindings: Vec::new(),
                    exports: Vec::new(),
                    stars: Vec::new(),
                    jsx_plan: None,
                };
                let stub_source = SourceText::new(
                    "throw new SyntaxError(\"dynamic import target failed to link\");",
                )
                .expect("stub fits budget");
                let stub_arc = Arc::new(stub_source);
                let stub_id = SourceId::new(synthetic_id);
                synthetic_id = synthetic_id.saturating_add(1);
                let scanned = scanner::scan_with_cancel(
                    stub_id,
                    module.script_kind(),
                    Arc::clone(&stub_arc),
                    cancel.clone(),
                )
                .map_err(|error| {
                    let scanner::ScanError::Cancelled(cancelled) = error;
                    program_lower_error(
                        module.path(),
                        ProgramLowerPhase::Module,
                        ProgramLowerErrorKind::Cancelled(cancelled),
                    )
                })?;
                let parsed =
                    parser::parse_with_cancel(scanned, cancel.clone()).map_err(|error| {
                        let parser::ParseError::Cancelled(cancelled) = error;
                        program_lower_error(
                            module.path(),
                            ProgramLowerPhase::Module,
                            ProgramLowerErrorKind::Cancelled(cancelled),
                        )
                    })?;
                let synthetic = parsed.product();
                let strings = linkage_strings(&stub_raw);
                let enum_facts = crate::enum_plan::EnumFacts::unchecked();
                let namespace_facts = crate::namespace_plan::NamespaceFacts::unchecked();
                let code = lower::assemble_program_module(
                    synthetic,
                    LowerOptions {
                        script_entry: false,
                        javascript_compatibility: true,
                    },
                    &strings,
                    None,
                    &enum_facts,
                    &namespace_facts,
                )
                .and_then(|unverified| {
                    unverified.verify().map_err(|error| LowerError {
                        source: synthetic.source_id(),
                        range: synthetic.range(),
                        kind: lower::LowerErrorKind::Verify(error),
                    })
                })
                .map_err(|error| {
                    program_lower_error(
                        module.path(),
                        ProgramLowerPhase::Module,
                        ProgramLowerErrorKind::Lower(error),
                    )
                })?;
                stub_codes.insert(module.source_id(), code);
                raw_modules.push(stub_raw);
                check_lower_cancel(cancel, module.path(), ProgramLowerPhase::Metadata)?;
                continue;
            }
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
            let mut raw = collect_raw_module(
                module,
                output.source_file(),
                output.semantic_model().enum_facts(),
                output.semantic_model().namespace_facts(),
                name,
                &orig_ids,
            )?;
            for edge in &mut raw.edges {
                if let EdgeTarget::Local(orig) = edge.target {
                    let target_source = resolved.modules()[orig.get() as usize].source_id();
                    if excluded.contains(&target_source) {
                        edge.target = EdgeTarget::External;
                        edge.external_identity = Some(edge.specifier.clone());
                    } else if let Some(remapped) = new_ids.get(&target_source) {
                        edge.target = EdgeTarget::Local(*remapped);
                    }
                }
            }
            if runs_as_script(resolved, module, output.source_file(), options) {
                raw.bindings
                    .retain(|binding| !matches!(binding.kind, RawBindingKind::Hoisted));
            }
            raw_modules.push(raw);
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
        let mut module_failures: Vec<(SourceId, ProgramLowerError)> = Vec::new();
        for (index, (kept_module, raw)) in kept.iter().zip(raw_modules.iter()).enumerate() {
            check_lower_cancel(cancel, kept_module.path(), ProgramLowerPhase::Module)?;
            let code = if let Some(stub) = stub_codes.remove(&kept_module.source_id()) {
                stub
            } else {
                let output = frontend
                    .module(kept_module.source_id())
                    .expect("frontend presence checked above");
                let file = output.source_file();
                let strings = linkage_strings(raw);
                match lower::assemble_program_module(
                    file,
                    LowerOptions {
                        script_entry: runs_as_script(resolved, kept_module, file, options),
                        ..options
                    },
                    &strings,
                    raw.jsx_plan.as_ref(),
                    output.semantic_model().enum_facts(),
                    output.semantic_model().namespace_facts(),
                )
                .and_then(|unverified| {
                    unverified.verify().map_err(|error| LowerError {
                        source: file.source_id(),
                        range: file.range(),
                        kind: lower::LowerErrorKind::Verify(error),
                    })
                }) {
                    Ok(code) => code,
                    Err(error) => {
                        module_failures.push((
                            kept_module.source_id(),
                            program_lower_error(
                                kept_module.path(),
                                ProgramLowerPhase::Module,
                                ProgramLowerErrorKind::Lower(error),
                            ),
                        ));
                        continue;
                    }
                }
            };
            check_lower_cancel(cancel, kept_module.path(), ProgramLowerPhase::Module)?;
            linked_modules.push(materialize_program_module(code, raw));
            provenance.push(ExecutableModuleProvenance {
                module: ModuleId::new(u32::try_from(index).expect("kept fits u32")),
                source: kept_module.identity().clone(),
                edges: Arc::from(kept_module.dependencies()),
            });
        }
        if !module_failures.is_empty() {
            if let Some((_, failure)) = module_failures
                .iter()
                .find(|(source, _)| static_reachable.contains(source))
            {
                return Err(failure.clone());
            }
            let failing: Vec<SourceId> =
                module_failures.iter().map(|(source, _)| *source).collect();
            let (_, failure) = module_failures
                .into_iter()
                .next()
                .expect("a non-empty failure list has a first failure");
            let mut quarantine = DynamicQuarantine {
                resolved,
                static_reachable: &static_reachable,
                stubbed: &mut stubbed,
                excluded: &mut excluded,
            };
            if !quarantine.quarantine_all(&failing) {
                return Err(failure);
            }
            continue;
        }
        let entry = new_ids[&resolved.entrypoint_id()];
        check_lower_cancel(
            cancel,
            resolved.entrypoint().path(),
            ProgramLowerPhase::Link,
        )?;
        match BytecodeProgram::link(linked_modules, entry) {
            Ok(wire) => {
                check_lower_cancel(
                    cancel,
                    resolved.entrypoint().path(),
                    ProgramLowerPhase::Link,
                )?;
                return Ok(ExecutableProgram { wire, provenance });
            }
            Err(link_error) => {
                let failing_source = link_error
                    .module
                    .and_then(|mid| kept.get(mid.get() as usize))
                    .map(|module| module.source_id());
                let Some(failing) = failing_source else {
                    let path = link_error
                        .module
                        .and_then(|module| resolved.modules().get(module.get() as usize))
                        .map_or_else(|| resolved.entrypoint().path(), ResolvedModule::path);
                    return Err(program_lower_error(
                        path,
                        ProgramLowerPhase::Link,
                        ProgramLowerErrorKind::Link(link_error),
                    ));
                };
                if static_reachable.contains(&failing) {
                    let path = resolved
                        .module(failing)
                        .map_or_else(|| resolved.entrypoint().path(), ResolvedModule::path);
                    return Err(program_lower_error(
                        path,
                        ProgramLowerPhase::Link,
                        ProgramLowerErrorKind::Link(link_error),
                    ));
                }
                let mut quarantine = DynamicQuarantine {
                    resolved,
                    static_reachable: &static_reachable,
                    stubbed: &mut stubbed,
                    excluded: &mut excluded,
                };
                if !quarantine.quarantine_all(&[failing]) {
                    let path = resolved
                        .module(failing)
                        .map_or_else(|| resolved.entrypoint().path(), ResolvedModule::path);
                    return Err(program_lower_error(
                        path,
                        ProgramLowerPhase::Link,
                        ProgramLowerErrorKind::Link(link_error),
                    ));
                }
                continue;
            }
        }
    }
}

fn live_without(
    resolved: &ResolvedProgram,
    failing: &HashSet<SourceId>,
    excluded: &HashSet<SourceId>,
    stubbed: &HashSet<SourceId>,
) -> HashSet<SourceId> {
    let mut protected = HashSet::new();
    let mut stack = vec![resolved.entrypoint_id()];
    while let Some(current) = stack.pop() {
        if failing.contains(&current) || !protected.insert(current) {
            continue;
        }

        if excluded.contains(&current) || stubbed.contains(&current) {
            continue;
        }
        let Some(node) = resolved.module(current) else {
            continue;
        };
        for dependency in node.dependencies() {
            if let ModuleTarget::Local(target) = dependency.target()
                && !failing.contains(target)
            {
                stack.push(*target);
            }
        }
    }
    protected
}

struct DynamicQuarantine<'a> {
    resolved: &'a ResolvedProgram,
    static_reachable: &'a HashSet<SourceId>,
    stubbed: &'a mut HashSet<SourceId>,
    excluded: &'a mut HashSet<SourceId>,
}

impl DynamicQuarantine<'_> {
    fn quarantine_all(&mut self, failing: &[SourceId]) -> bool {
        let mut progressed = false;
        for source in failing {
            progressed |= self.stubbed.insert(*source);
        }
        let failing: HashSet<SourceId> = failing.iter().copied().collect();
        let protected = live_without(self.resolved, &failing, self.excluded, self.stubbed);
        for source in &failing {
            progressed |= self.exclude_transitive(*source, &protected);
        }
        progressed
    }

    fn exclude_transitive(&mut self, failing: SourceId, protected: &HashSet<SourceId>) -> bool {
        let mut progressed = false;
        let mut stack = vec![failing];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            let Some(node) = self.resolved.module(current) else {
                continue;
            };
            for dependency in node.dependencies() {
                if let ModuleTarget::Local(target) = dependency.target() {
                    progressed |= self.consider(target, failing, protected, &mut stack);
                }
            }
        }
        progressed
    }

    fn consider(
        &mut self,
        target: &SourceId,
        failing: SourceId,
        protected: &HashSet<SourceId>,
        stack: &mut Vec<SourceId>,
    ) -> bool {
        stack.push(*target);
        if *target == failing
            || self.static_reachable.contains(target)
            || protected.contains(target)
            || self.stubbed.contains(target)
        {
            return false;
        }
        self.excluded.insert(*target)
    }
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

/// Whether `module` is the Script the host asked for. A file with module syntax
/// is a module either way, and the host decides whether that is an error.
fn runs_as_script(
    resolved: &ResolvedProgram,
    module: &ResolvedModule,
    file: &SourceFile,
    options: LowerOptions,
) -> bool {
    options.script_entry
        && module.source_id() == resolved.entrypoint().source_id()
        && !crate::early_errors::is_module(file)
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
mod tests;
