//! Module resolution modes for node16 / nodenext / bundler.
//!
//! Builds on the lexical foundation in [`crate::project`]:
//! [`ProjectRoot`] confinement, [`plan_relative_module`] extension substitution,
//! and [`PackageJson`] exports/imports. This module owns the I/O-driven walk,
//! resolution-mode conditions, deterministic trace, and cycle-safe package lookup.
//! It does not introduce a second path, options, or diagnostics model.

use super::resolution_trace::{ResolutionRequest, ResolutionTraceLog};
use crate::project::{
    CompilerOptions, ModuleResolutionError, PackageError, PackageJson, PackageMode, PackageTarget,
    PathError, PathMapping, ProjectRoot, ResolutionConditions, ResolutionFlavor, append_unique,
    append_with_extension, parse_jsonc, plan_relative_module,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Path, PathBuf},
    sync::Arc,
};

/// Supported `compilerOptions.moduleResolution` values for this leaf.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModuleResolutionKind {
    Node16,
    NodeNext,
    Bundler,
    Classic,
}

impl ModuleResolutionKind {
    /// Parses a tsconfig `moduleResolution` string. Matching is case-insensitive
    /// and accepts the forms TypeScript documents (`node16`, `nodenext`, `bundler`,
    /// `classic`).
    pub fn parse(value: &str) -> Result<Self, ResolutionError> {
        match value.trim().to_ascii_lowercase().as_str() {
            "node16" => Ok(Self::Node16),
            "nodenext" => Ok(Self::NodeNext),
            "bundler" => Ok(Self::Bundler),
            "classic" => Ok(Self::Classic),
            _ => Err(ResolutionError::UnsupportedKind {
                value: Arc::from(value),
            }),
        }
    }

    /// Resolves the kind from compiler options, defaulting per the module
    /// format when `moduleResolution` is unset: `amd`, `system`, and `umd`
    /// default to `Classic` (upstream probes the importing file's directory
    /// for bare names under those formats), an unset `module` to `Bundler`,
    /// and everything else to `NodeNext`.
    pub fn from_options(options: &CompilerOptions) -> Result<Self, ResolutionError> {
        match options.module_resolution() {
            Some(value) => Self::parse(value),
            None => Ok(Self::default_for_module(options.module())),
        }
    }

    /// Default kind for an unset `moduleResolution`, keyed off the module
    /// format alone. Matching is case-insensitive and ignores padding.
    /// Oracle (tsc 7.0.2, `--traceResolution` on a scratch project with
    /// neither `module` nor `moduleResolution`): `Module resolution kind is
    /// not specified, using 'Bundler'`.
    fn default_for_module(module: Option<&str>) -> Self {
        let Some(module) = module else {
            return Self::Bundler;
        };
        let classic = matches!(
            module.trim().to_ascii_lowercase().as_str(),
            "amd" | "system" | "umd"
        );
        if classic {
            Self::Classic
        } else {
            Self::NodeNext
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Node16 => "node16",
            Self::NodeNext => "nodenext",
            Self::Bundler => "bundler",
            Self::Classic => "classic",
        }
    }

    /// Whether relative imports may omit an extension (bundler yes; node16/nodenext no
    /// for the *original* specifier, though extension substitution still applies to
    /// `.js` → `.ts` rewrites).
    #[must_use]
    pub const fn allows_extensionless_relative(self) -> bool {
        matches!(self, Self::Bundler | Self::Classic)
    }
    /// Upstream trace spelling used by `traceResolution` output.
    #[must_use]
    pub const fn trace_name(self) -> &'static str {
        match self {
            Self::Node16 => "Node16",
            Self::NodeNext => "NodeNext",
            Self::Bundler => "Bundler",
            Self::Classic => "Classic",
        }
    }
}

/// Per-import `resolution-mode` (`"import"` | `"require"`), also used as the ambient
/// mode derived from the containing module kind.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ResolutionMode {
    Import,
    Require,
}

impl ResolutionMode {
    pub fn parse(value: &str) -> Result<Self, ResolutionError> {
        match value.trim().to_ascii_lowercase().as_str() {
            "import" => Ok(Self::Import),
            "require" => Ok(Self::Require),
            _ => Err(ResolutionError::UnsupportedResolutionMode {
                value: Arc::from(value),
            }),
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Import => "import",
            Self::Require => "require",
        }
    }

    #[must_use]
    pub const fn package_mode(self) -> PackageMode {
        match self {
            Self::Import => PackageMode::Import,
            Self::Require => PackageMode::Require,
        }
    }
}

/// Derives the per-importing-file resolution mode for `node16`/`nodenext`-style
/// lookup: the importer extension decides (`.mts`/`.mjs` import, `.cts`/`.cjs`
/// require), then the `type` field of the nearest `package.json`, defaulting
/// to CJS. The tsconfig `module` option plays no part: a plain `.ts` file with
/// no package scope resolves in CJS mode even under `module: nodenext`.
/// Callers consult this only under those two kinds; under `bundler`/`classic`
/// the edge syntax decides through the ambient mode instead.
pub fn mode_for_importer(
    host: &dyn ResolutionHost,
    root: &ProjectRoot,
    importer: &Path,
) -> ResolutionMode {
    match importer.extension().and_then(|extension| extension.to_str()) {
        Some(extension)
            if extension.eq_ignore_ascii_case("mts")
                || extension.eq_ignore_ascii_case("mjs") =>
        {
            return ResolutionMode::Import;
        }
        Some(extension)
            if extension.eq_ignore_ascii_case("cts")
                || extension.eq_ignore_ascii_case("cjs") =>
        {
            return ResolutionMode::Require;
        }
        _ => {}
    }
    let mut directory = importer.parent();
    while let Some(current) = directory {
        if !current.starts_with(root.path()) {
            break;
        }
        let candidate = current.join("package.json");
        if host.file_exists(&candidate) {
            let is_module = host
                .read_file(&candidate)
                .and_then(|source| PackageJson::parse(root, &candidate, &source).ok())
                .and_then(|package| package.package_type().map(str::to_string))
                .is_some_and(|package_type| package_type.eq_ignore_ascii_case("module"));
            return if is_module {
                ResolutionMode::Import
            } else {
                ResolutionMode::Require
            };
        }
        if current == root.path() {
            break;
        }
        directory = current.parent();
    }
    ResolutionMode::Require
}

/// File-system probe used by the resolver. Implementations must be deterministic:
/// identical queries return identical answers for the life of one resolve call.
pub trait ResolutionHost {
    fn file_exists(&self, path: &Path) -> bool;
    fn directory_exists(&self, path: &Path) -> bool;
    fn read_file(&self, path: &Path) -> Option<Arc<str>>;
}

/// One ordered step of a resolution attempt. Traces are stable across identical
/// inputs so two runs produce byte-identical step sequences.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolutionTraceStep {
    LookingFor {
        specifier: Arc<str>,
        from: PathBuf,
        kind: ModuleResolutionKind,
        mode: ResolutionMode,
    },
    Candidate {
        path: PathBuf,
        exists: bool,
    },
    PathsMatch {
        pattern: Arc<str>,
        target: PathBuf,
    },
    ScopeProbe {
        path: PathBuf,
        exists: bool,
        has_exports: bool,
    },
    LegacyField {
        field: Arc<str>,
        target: Option<(Arc<str>, PathBuf)>,
    },
    StripExtension {
        path: PathBuf,
    },
    Condition {
        name: Arc<str>,
        matched: bool,
    },
    PackageImport {
        specifier: Arc<str>,
        target: Arc<str>,
    },
    NodeModulesWalk {
        directory: PathBuf,
        exists: bool,
        fallback: bool,
    },
    PackageJsonProbe {
        path: PathBuf,
        exists: bool,
    },
    TypesFallback {
        package: Arc<str>,
        path: PathBuf,
    },
    Failed {
        reason: Arc<str>,
    },
    Resolved {
        path: PathBuf,
    },
}

/// Immutable, ordered resolution trace.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolutionTrace {
    steps: Vec<ResolutionTraceStep>,
}

impl ResolutionTrace {
    #[must_use]
    pub fn steps(&self) -> &[ResolutionTraceStep] {
        &self.steps
    }

    fn push(&mut self, step: ResolutionTraceStep) {
        self.steps.push(step);
    }
}

/// Successful module resolution result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    path: PathBuf,
    kind: ModuleResolutionKind,
    mode: ResolutionMode,
    package_json: Option<PathBuf>,
    trace: ResolutionTrace,
}

impl ResolvedModule {
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub const fn kind(&self) -> ModuleResolutionKind {
        self.kind
    }

    #[must_use]
    pub const fn mode(&self) -> ResolutionMode {
        self.mode
    }

    #[must_use]
    pub fn package_json(&self) -> Option<&Path> {
        self.package_json.as_deref()
    }

    #[must_use]
    pub const fn trace(&self) -> &ResolutionTrace {
        &self.trace
    }
}

/// Module resolution failure with an attached deterministic trace.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolutionError {
    UnsupportedKind {
        value: Arc<str>,
    },
    UnsupportedResolutionMode {
        value: Arc<str>,
    },
    EmptySpecifier,
    UrlLikeSpecifier {
        specifier: Arc<str>,
    },
    Path(PathError),
    Module(ModuleResolutionError),
    Package(PackageError),
    NotFound {
        specifier: Arc<str>,
        from: PathBuf,
        trace: ResolutionTrace,
    },
    EscapesRoot {
        path: PathBuf,
        root: PathBuf,
        trace: ResolutionTrace,
    },
    PackageCycle {
        specifier: Arc<str>,
        trace: ResolutionTrace,
    },
}

impl fmt::Display for ResolutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedKind { value } => {
                write!(
                    formatter,
                    "unsupported moduleResolution {value:?}; expected node16, nodenext, or bundler"
                )
            }
            Self::UnsupportedResolutionMode { value } => {
                write!(
                    formatter,
                    "unsupported resolution-mode {value:?}; expected import or require"
                )
            }
            Self::EmptySpecifier => formatter.write_str("module specifier is empty"),
            Self::UrlLikeSpecifier { specifier } => {
                write!(
                    formatter,
                    "URL-like module specifier {specifier:?} is not a project file"
                )
            }
            Self::Path(error) => error.fmt(formatter),
            Self::Module(error) => error.fmt(formatter),
            Self::Package(error) => error.fmt(formatter),
            Self::NotFound {
                specifier, from, ..
            } => write!(
                formatter,
                "cannot resolve {specifier:?} from {}",
                from.display()
            ),
            Self::EscapesRoot { path, root, .. } => write!(
                formatter,
                "resolved path {} escapes project root {}",
                path.display(),
                root.display()
            ),
            Self::PackageCycle { specifier, .. } => {
                write!(
                    formatter,
                    "package import cycle while resolving {specifier:?}"
                )
            }
        }
    }
}

impl std::error::Error for ResolutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Path(error) => Some(error),
            Self::Module(error) => Some(error),
            Self::Package(error) => Some(error),
            _ => None,
        }
    }
}

impl From<PathError> for ResolutionError {
    fn from(error: PathError) -> Self {
        Self::Path(error)
    }
}

impl From<ModuleResolutionError> for ResolutionError {
    fn from(error: ModuleResolutionError) -> Self {
        Self::Module(error)
    }
}

impl From<PackageError> for ResolutionError {
    fn from(error: PackageError) -> Self {
        Self::Package(error)
    }
}

impl ResolutionError {
    #[must_use]
    pub fn trace(&self) -> Option<&ResolutionTrace> {
        match self {
            Self::NotFound { trace, .. }
            | Self::EscapesRoot { trace, .. }
            | Self::PackageCycle { trace, .. } => Some(trace),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct CacheKey {
    containing_directory: PathBuf,
    specifier: Arc<str>,
    kind: ModuleResolutionKind,
    mode: ResolutionMode,
    flavor: ResolutionFlavor,
}

/// Cache keyed by containing directory, specifier, kind, mode, and resolution flavor.
/// Failed lookups are stored so repeated misses stay deterministic and cheap.
#[derive(Clone, Debug, Default)]
pub struct ResolutionCache {
    hits: BTreeMap<CacheKey, Result<ResolvedModule, ResolutionError>>,
}

impl ResolutionCache {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.hits.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.hits.is_empty()
    }
}
/// Host and mutable state used by traced module resolution.
pub struct TraceResolutionServices<'a> {
    pub host: &'a dyn ResolutionHost,
    pub cache: &'a mut ResolutionCache,
    pub log: &'a mut ResolutionTraceLog,
}

type ResolverServices<'host, 'cache, 'stack> = (
    &'host dyn ResolutionHost,
    &'cache mut ResolutionCache,
    &'stack mut BTreeSet<(PathBuf, Arc<str>)>,
);

type PathMappingSelection<'a> = (Arc<str>, &'a [PathBuf], Option<Arc<str>>);
type ScoredPathMapping<'a> = (Arc<str>, &'a [PathBuf], Option<Arc<str>>, usize);

/// Resolves `specifier` as imported from `importer` under `kind` / `mode`.
///
/// Every candidate is confined to `root` after normalization. Package `#imports`
/// that redirect to other bare specifiers are followed with an explicit cycle
/// guard. No ambient `tsc` or host TypeScript process is consulted.
pub fn resolve_module_name(
    root: &ProjectRoot,
    options: &CompilerOptions,
    importer: impl AsRef<Path>,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode),
    host: &dyn ResolutionHost,
    cache: &mut ResolutionCache,
) -> Result<ResolvedModule, ResolutionError> {
    resolve_module_name_inner(
        (root, options),
        importer.as_ref(),
        specifier,
        (strategy.0, strategy.1, ResolutionFlavor::Runtime),
        (host, cache, &mut BTreeSet::new()),
        None,
    )
}

/// Like [`resolve_module_name`] while appending sanitized upstream
/// `traceResolution` lines to `log`. The strategy carries the resolution
/// flavor so the trace narrates candidates in the order actually probed.
pub fn resolve_module_name_with_trace(
    root: &ProjectRoot,
    options: &CompilerOptions,
    importer: impl AsRef<Path>,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: TraceResolutionServices<'_>,
) -> Result<ResolvedModule, ResolutionError> {
    let TraceResolutionServices { host, cache, log } = services;
    resolve_module_name_inner(
        (root, options),
        importer.as_ref(),
        specifier,
        strategy,
        (host, cache, &mut BTreeSet::new()),
        Some(log),
    )
}

/// Like [`resolve_module_name`] but prefers declaration files (`ResolutionFlavor::Types`
/// and `PackageMode::Types` conditions).
pub fn resolve_type_reference(
    root: &ProjectRoot,
    options: &CompilerOptions,
    importer: impl AsRef<Path>,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode),
    host: &dyn ResolutionHost,
    cache: &mut ResolutionCache,
) -> Result<ResolvedModule, ResolutionError> {
    resolve_module_name_inner(
        (root, options),
        importer.as_ref(),
        specifier,
        (strategy.0, strategy.1, ResolutionFlavor::Types),
        (host, cache, &mut BTreeSet::new()),
        None,
    )
}

fn resolve_module_name_inner(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: ResolverServices<'_, '_, '_>,
    log: Option<&mut ResolutionTraceLog>,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let (host, cache, package_stack) = services;
    if specifier.is_empty() {
        return Err(ResolutionError::EmptySpecifier);
    }

    let importer = root.confine(importer)?;
    let containing = importer
        .parent()
        .ok_or_else(|| PathError::PathHasNoParent {
            path: importer.clone(),
        })?
        .to_path_buf();

    let key = CacheKey {
        containing_directory: containing.clone(),
        specifier: Arc::from(specifier),
        kind,
        mode,
        flavor,
    };
    if let Some(cached) = cache.hits.get(&key) {
        let result = cached.clone();
        if let Some(log) = log {
            log.record_module(
                root,
                ResolutionRequest {
                    importer: &importer,
                    specifier,
                    strategy: (kind, mode, flavor),
                },
                options.module_resolution().is_some(),
                true,
                &result,
            );
        }
        return result;
    }

    let mut trace = ResolutionTrace::default();
    trace.push(ResolutionTraceStep::LookingFor {
        specifier: Arc::from(specifier),
        from: importer.clone(),
        kind,
        mode,
    });

    let result = resolve_uncached(
        (root, options),
        &importer,
        &containing,
        specifier,
        (kind, mode, flavor),
        (host, &mut *cache, &mut *package_stack),
        &mut trace,
    );

    let stored = match result {
        Ok(mut resolved) => {
            resolved.trace = trace;
            let path = root.confine(resolved.path()).map_err(|error| match error {
                PathError::PathEscapesRoot { root, path } => ResolutionError::EscapesRoot {
                    path,
                    root,
                    trace: resolved.trace.clone(),
                },
                other => ResolutionError::Path(other),
            })?;
            resolved.path = path;
            resolved.trace.push(ResolutionTraceStep::Resolved {
                path: resolved.path.clone(),
            });
            Ok(resolved)
        }
        Err(ResolutionError::NotFound {
            specifier,
            from,
            trace: mut existing,
        }) => {
            if existing.steps.is_empty() {
                existing = trace;
            }
            existing.push(ResolutionTraceStep::Failed {
                reason: Arc::from(format!("cannot resolve {specifier:?}")),
            });
            Err(ResolutionError::NotFound {
                specifier,
                from,
                trace: existing,
            })
        }
        Err(other) => Err(other),
    };

    if let Some(log) = log {
        log.record_module(
            root,
            ResolutionRequest {
                importer: &importer,
                specifier,
                strategy: (kind, mode, flavor),
            },
            options.module_resolution().is_some(),
            false,
            &stored,
        );
    }
    cache.hits.insert(key, stored.clone());
    stored
}

fn resolve_uncached(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    containing: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: ResolverServices<'_, '_, '_>,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let (host, cache, package_stack) = services;
    if is_url_like(specifier) {
        return Err(ResolutionError::UrlLikeSpecifier {
            specifier: Arc::from(specifier),
        });
    }

    if kind == ModuleResolutionKind::Classic {
        return resolve_classic(
            (root, options),
            importer,
            containing,
            specifier,
            (kind, mode, flavor),
            host,
            trace,
        );
    }

    if specifier.starts_with("./") || specifier.starts_with("../") {
        return resolve_relative(
            (root, options),
            importer,
            specifier,
            (kind, mode, flavor),
            host,
            trace,
        );
    }

    if specifier.starts_with('#') {
        return resolve_hash_import(
            (root, options),
            importer,
            containing,
            specifier,
            (kind, mode, flavor),
            (host, &mut *cache, &mut *package_stack),
            trace,
        );
    }

    if let Some(resolved) = try_paths_mapping(
        (root, options),
        importer,
        specifier,
        (kind, mode, flavor),
        host,
        trace,
    )? {
        return Ok(resolved);
    }

    if let Some(resolved) = try_node_modules(
        (root, options),
        importer,
        containing,
        specifier,
        (kind, mode, flavor),
        (host, &mut *cache, &mut *package_stack),
        trace,
    )? {
        return Ok(resolved);
    }

    if flavor == ResolutionFlavor::Types
        && let Some(resolved) = try_types_package(
            (root, options),
            containing,
            specifier,
            (kind, mode),
            host,
            trace,
        )?
    {
        return Ok(resolved);
    }

    Err(ResolutionError::NotFound {
        specifier: Arc::from(specifier),
        from: importer.to_path_buf(),
        trace: trace.clone(),
    })
}

fn is_url_like(specifier: &str) -> bool {
    specifier.contains("://")
        || specifier.starts_with("node:")
        || specifier.starts_with("data:")
        || specifier.contains('?')
        || specifier.contains('#') && !specifier.starts_with('#')
}

/// Resolves `specifier` under `ModuleResolutionKind::Classic`: relative names probe
/// the importing file's directory, non-relative names probe `paths` mappings first
/// and then walk up the directory chain to the project root. Every level
/// tries `.ts`, `.tsx`, and `.d.ts` (plus `.js` and `.jsx` under `allowJs`). There
/// is no `node_modules` or `@types` lookup and no directory-index probing.
fn resolve_classic(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    containing: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, _) = context;
    if specifier.starts_with("./") || specifier.starts_with("../") {
        return match resolve_classic_from(context, containing, specifier, strategy, host, trace)? {
            Some(found) => Ok(found),
            None => Err(ResolutionError::NotFound {
                specifier: Arc::from(specifier),
                from: importer.to_path_buf(),
                trace: trace.clone(),
            }),
        };
    }
    if let Some(found) = resolve_classic_paths(context, specifier, strategy, host, trace)? {
        return Ok(found);
    }
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            break;
        }
        if let Some(found) =
            resolve_classic_from(context, &directory, specifier, strategy, host, trace)?
        {
            return Ok(found);
        }
        let Some(parent) = directory.parent() else {
            break;
        };
        if parent == directory {
            break;
        }
        directory = parent.to_path_buf();
    }
    if let Some(found) = try_types_package(
        context,
        containing,
        specifier,
        (strategy.0, strategy.1),
        host,
        trace,
    )? {
        return Ok(found);
    }
    Err(ResolutionError::NotFound {
        specifier: Arc::from(specifier),
        from: importer.to_path_buf(),
        trace: trace.clone(),
    })
}

/// Probes `specifier` against one directory; `Ok(None)` means nothing at this
/// level matched, and the caller decides whether another level exists.
fn resolve_classic_from(
    context: (&ProjectRoot, &CompilerOptions),
    directory: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, _options) = context;
    let requested = root.resolve_from(directory, specifier)?;
    probe_classic_location(context, &requested, strategy, host, trace)
}

fn resolve_classic_paths(
    context: (&ProjectRoot, &CompilerOptions),
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let Some((_, targets, capture)) = select_path_mapping(options.paths(), specifier) else {
        return Ok(None);
    };
    for target_pattern in targets {
        let substituted = substitute_star(target_pattern, capture.as_deref());
        let confined = root.confine(substituted)?;
        if let Some(found) = probe_classic_location(context, &confined, strategy, host, trace)? {
            return Ok(Some(found));
        }
    }
    Ok(None)
}

fn probe_classic_location(
    context: (&ProjectRoot, &CompilerOptions),
    location: &Path,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, _flavor) = strategy;
    for candidate in classic_candidates(location, options.allow_js()) {
        let exists = host.file_exists(&candidate);
        trace.push(ResolutionTraceStep::Candidate {
            path: candidate.clone(),
            exists,
        });
        if exists {
            let confined = root.confine(candidate)?;
            return Ok(Some(ResolvedModule {
                path: confined,
                kind,
                mode,
                package_json: None,
                trace: ResolutionTrace::default(),
            }));
        }
    }
    Ok(None)
}

fn classic_candidates(location: &Path, allow_js: bool) -> Vec<PathBuf> {
    let extensions: &[&str] = if allow_js {
        &["ts", "tsx", "d.ts", "js", "jsx"]
    } else {
        &["ts", "tsx", "d.ts"]
    };
    let mut candidates = Vec::new();
    if location.extension().is_some() {
        append_unique(&mut candidates, location.to_path_buf());
    }
    let stem = classic_stem(location).unwrap_or_else(|| location.to_path_buf());
    for extension in extensions {
        append_with_extension(&mut candidates, &stem, extension);
    }
    candidates
}

fn classic_stem(path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let mut stem = name;
    for suffix in [
        ".d.mts", ".d.cts", ".d.ts", ".mts", ".cts", ".tsx", ".mjs", ".cjs", ".ts", ".js", ".jsx",
    ] {
        if let Some(base) = stem.strip_suffix(suffix) {
            stem = base;
            break;
        }
    }
    if stem.is_empty() || stem == name {
        return None;
    }
    Some(path.with_file_name(stem))
}

/// Origin of a relative specifier handed to [`resolve_relative_inner`].
///
/// The extensionless-relative rejection for ESM (`import` under
/// `node16`/`nodenext`) applies only to specifiers the user wrote. Probes the
/// resolver synthesizes from package contents keep probing with extension
/// substitution: a bare root with a manifest keeps the legacy `index` default
/// for ESM importers, and extensionless subpaths keep probing for CJS ones.
/// Manifest-less ESM roots and extensionless ESM subpaths never reach this
/// function; the installed-package fallback rejects them first.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RelativeOrigin {
    UserWritten,
    Synthesized,
}

fn resolve_relative(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    resolve_relative_inner(
        context,
        importer,
        specifier,
        strategy,
        host,
        trace,
        RelativeOrigin::UserWritten,
    )
}

fn resolve_synthesized_relative(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    resolve_relative_inner(
        context,
        importer,
        specifier,
        strategy,
        host,
        trace,
        RelativeOrigin::Synthesized,
    )
}

fn resolve_relative_inner(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
    origin: RelativeOrigin,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, _) = context;
    let (kind, mode, flavor) = strategy;
    if origin == RelativeOrigin::UserWritten
        && mode == ResolutionMode::Import
        && !kind.allows_extensionless_relative()
        && Path::new(specifier).extension().is_none()
    {
        return Err(ResolutionError::NotFound {
            specifier: Arc::from(specifier),
            from: importer.to_path_buf(),
            trace: trace.clone(),
        });
    }
    let plan = plan_relative_module(root, importer, specifier, flavor)?;
    for candidate in plan.candidates() {
        let exists = host.file_exists(candidate);
        trace.push(ResolutionTraceStep::Candidate {
            path: candidate.clone(),
            exists,
        });
        if exists {
            let confined = root.confine(candidate)?;
            return Ok(ResolvedModule {
                path: confined,
                kind,
                mode,
                package_json: None,
                trace: ResolutionTrace::default(),
            });
        }
    }
    Err(ResolutionError::NotFound {
        specifier: Arc::from(specifier),
        from: importer.to_path_buf(),
        trace: trace.clone(),
    })
}

fn try_paths_mapping(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let Some((pattern, targets, capture)) = select_path_mapping(options.paths(), specifier) else {
        return Ok(None);
    };
    // A paths-mapped `.json` specifier is only resolvable when
    // `resolveJsonModule` is enabled. With the flag off the module cannot be
    // found with the current settings (upstream TS2732), so the mapping must
    // not resolve it even when the target file exists.
    if !options.resolve_json_module()
        && Path::new(specifier)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("json"))
    {
        return Ok(None);
    }
    for target_pattern in targets {
        let substituted = substitute_star(target_pattern, capture.as_deref());
        // Targets from PathMapping are already absolute and confined to the project.
        let as_relative = path_as_dot_relative(root, importer, &substituted)?;
        trace.push(ResolutionTraceStep::PathsMatch {
            pattern: Arc::clone(&pattern),
            target: substituted.clone(),
        });
        match resolve_relative(
            (root, options),
            importer,
            &as_relative,
            (kind, mode, flavor),
            host,
            trace,
        ) {
            Ok(resolved) => return Ok(Some(resolved)),
            Err(ResolutionError::NotFound { .. }) => continue,
            Err(other) => return Err(other),
        }
    }
    Ok(None)
}

fn select_path_mapping<'a>(
    mappings: &'a [PathMapping],
    specifier: &str,
) -> Option<PathMappingSelection<'a>> {
    let mut best: Option<ScoredPathMapping<'a>> = None;
    for mapping in mappings {
        let pattern = mapping.pattern();
        if !pattern.contains('*') {
            if pattern == specifier {
                let score = pattern.len();
                if best
                    .as_ref()
                    .is_none_or(|(_, _, _, current)| score > *current)
                {
                    best = Some((Arc::from(pattern), mapping.targets(), None, score));
                }
            }
            continue;
        }
        let (prefix, suffix) = pattern.split_once('*')?;
        let Some(remainder) = specifier.strip_prefix(prefix) else {
            continue;
        };
        let Some(capture) = remainder.strip_suffix(suffix) else {
            continue;
        };
        let score = prefix.len() + suffix.len();
        if best
            .as_ref()
            .is_none_or(|(_, _, _, current)| score > *current)
        {
            best = Some((
                Arc::from(pattern),
                mapping.targets(),
                Some(Arc::from(capture)),
                score,
            ));
        }
    }
    best.map(|(pattern, targets, capture, _)| (pattern, targets, capture))
}

fn substitute_star(target: &Path, capture: Option<&str>) -> PathBuf {
    let Some(capture) = capture else {
        return target.to_path_buf();
    };
    let raw = target.to_string_lossy();
    PathBuf::from(raw.replace('*', capture))
}

fn path_as_dot_relative(
    root: &ProjectRoot,
    importer: &Path,
    absolute: &Path,
) -> Result<String, ResolutionError> {
    let importer_dir = importer
        .parent()
        .ok_or_else(|| PathError::PathHasNoParent {
            path: importer.to_path_buf(),
        })?;
    let absolute = root.confine(absolute)?;
    let relative = pathdiff_relative(importer_dir, &absolute);
    if relative.starts_with("./") || relative.starts_with("../") {
        Ok(relative)
    } else {
        Ok(format!("./{relative}"))
    }
}

fn pathdiff_relative(from_dir: &Path, to: &Path) -> String {
    let from_components: Vec<_> = from_dir.components().collect();
    let to_components: Vec<_> = to.components().collect();
    let mut common = 0;
    for (a, b) in from_components.iter().zip(to_components.iter()) {
        if a == b {
            common += 1;
        } else {
            break;
        }
    }
    let mut parts = Vec::new();
    parts.extend(std::iter::repeat_n("..", from_components.len() - common));
    for component in &to_components[common..] {
        parts.push(component.as_os_str().to_str().unwrap_or(""));
    }
    if parts.is_empty() {
        ".".to_string()
    } else {
        parts.join("/")
    }
}
fn package_has_exports(content: &Option<Arc<str>>) -> bool {
    content.as_ref().is_some_and(|source| {
        parse_jsonc(source)
            .map(|value| {
                value
                    .as_object()
                    .is_some_and(|object| object.get("exports").is_some())
            })
            .unwrap_or(false)
    })
}

fn legacy_field_value(content: &Arc<str>, field: &str) -> Option<Arc<str>> {
    parse_jsonc(content)
        .ok()?
        .as_object()?
        .get(field)?
        .as_str()
        .map(Arc::from)
}

fn probe_legacy_fields(
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
    chain: &[(PathBuf, Option<Arc<str>>)],
) -> Option<PathBuf> {
    let (driver_path, driver_source) = chain.first()?;
    let driver_source = driver_source.as_ref()?;
    let driver_dir = driver_path.parent()?;
    for field in ["typesVersions", "typings", "types"] {
        let value = legacy_field_value(driver_source, field);
        match value {
            None => {
                trace.push(ResolutionTraceStep::LegacyField {
                    field: Arc::from(field),
                    target: None,
                });
            }
            Some(value) => {
                let resolved = driver_dir.join(value.strip_prefix("./").unwrap_or(value.as_ref()));
                trace.push(ResolutionTraceStep::LegacyField {
                    field: Arc::from(field),
                    target: Some((Arc::clone(&value), resolved.clone())),
                });
                if field == "typesVersions" {
                    return None;
                }
                let direct = resolved
                    .extension()
                    .is_some_and(|extension| extension == "ts" || extension == "tsx")
                    || resolved
                        .file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.ends_with(".d.ts"));
                if direct {
                    if let Some(found) = probe_candidate(host, trace, resolved) {
                        return Some(found);
                    }
                } else {
                    trace.push(ResolutionTraceStep::StripExtension {
                        path: resolved.clone(),
                    });
                    let stem = resolved.with_extension("");
                    for extension in ["ts", "tsx", "d.ts"] {
                        let mut name = stem.clone().into_os_string();
                        name.push(".");
                        name.push(extension);
                        if let Some(found) = probe_candidate(host, trace, PathBuf::from(name)) {
                            return Some(found);
                        }
                    }
                }
            }
        }
    }
    None
}

fn probe_candidate(
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
    candidate: PathBuf,
) -> Option<PathBuf> {
    let exists = host.file_exists(&candidate);
    trace.push(ResolutionTraceStep::Candidate {
        path: candidate.clone(),
        exists,
    });
    exists.then_some(candidate)
}

fn confined_hit(
    root: &ProjectRoot,
    trace: &mut ResolutionTrace,
    kind: ModuleResolutionKind,
    mode: ResolutionMode,
    found: &Path,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let path = root.confine(found).map_err(|error| match error {
        PathError::PathEscapesRoot { path, root } => ResolutionError::EscapesRoot {
            path,
            root,
            trace: trace.clone(),
        },
        other => ResolutionError::Path(other),
    })?;
    Ok(Some(ResolvedModule {
        path,
        kind,
        mode,
        package_json: None,
        trace: ResolutionTrace::default(),
    }))
}

fn probe_loose_stems(
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
    stems: &[PathBuf],
    extensions: &[&str],
) -> Option<PathBuf> {
    for root in stems {
        for extension in extensions {
            let mut name = root.clone().into_os_string();
            name.push(".");
            name.push(extension);
            if let Some(found) = probe_candidate(host, trace, PathBuf::from(name)) {
                return Some(found);
            }
        }
    }
    None
}
fn probe_loose_files(
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
    node_modules: &Path,
    package_name: &str,
    subpath: &str,
    extensions: &[&str],
) -> Option<PathBuf> {
    if package_name.starts_with('@') {
        return None;
    }
    if !host.directory_exists(node_modules) {
        return None;
    }
    let mut stem = node_modules.join(package_name);
    if !subpath.is_empty() {
        stem.push(subpath);
    }
    if stem.extension().is_some() {
        return None;
    }
    probe_loose_stems(host, trace, &[stem.clone(), stem.join("index")], extensions)
}

fn try_node_modules(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    containing: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: ResolverServices<'_, '_, '_>,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let (host, cache, package_stack) = services;
    let (package_name, subpath) = split_package_specifier(specifier);
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            break;
        }
        let package_json = directory.join("package.json");
        trace.push(ResolutionTraceStep::PackageJsonProbe {
            path: package_json.clone(),
            exists: host.file_exists(&package_json),
        });
        let Some(parent) = directory.parent() else {
            break;
        };
        if parent == directory {
            break;
        }
        directory = parent.to_path_buf();
    }
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            break;
        }
        let node_modules = directory.join("node_modules");
        trace.push(ResolutionTraceStep::NodeModulesWalk {
            directory: directory.clone(),
            exists: host.directory_exists(&node_modules),
            fallback: false,
        });
        let package_root = directory.join("node_modules").join(&package_name);
        // The package directory itself may be absent while a stem file beside
        // it exists (`node_modules/dep.ts` with no `node_modules/dep/`): tsc
        // probes stems regardless under node16/nodenext (its trace prints the
        // `package.json` miss), so enter whenever the `node_modules`
        // container exists. Bundler keeps the old gate: its loose-file path
        // below already probes stems, and its trace prints no miss line.
        if (host.directory_exists(&package_root)
            || host.file_exists(&package_root.join("package.json"))
            || (kind != ModuleResolutionKind::Bundler
                && host.directory_exists(&node_modules)))
            && let Some(resolved) = resolve_installed_package(
                (root, options),
                importer,
                &package_root,
                &subpath,
                (kind, mode, flavor),
                (host, &mut *cache, &mut *package_stack),
                trace,
            )?
        {
            return Ok(Some(resolved));
        }
        if kind == ModuleResolutionKind::Bundler
            && let Some(found) = probe_loose_files(
                host,
                trace,
                &node_modules,
                &package_name,
                &subpath,
                &["ts", "tsx", "d.ts"],
            )
        {
            return confined_hit(root, trace, kind, mode, &found);
        }
        let Some(parent) = directory.parent() else {
            break;
        };
        if parent == directory {
            break;
        }
        directory = parent.to_path_buf();
    }
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            break;
        }
        let node_modules = directory.join("node_modules");
        trace.push(ResolutionTraceStep::NodeModulesWalk {
            directory: directory.clone(),
            exists: host.directory_exists(&node_modules),
            fallback: true,
        });
        if kind == ModuleResolutionKind::Bundler
            && let Some(found) = probe_loose_files(
                host,
                trace,
                &node_modules,
                &package_name,
                &subpath,
                &["js", "jsx", "json"],
            )
        {
            return confined_hit(root, trace, kind, mode, &found);
        }
        let Some(parent) = directory.parent() else {
            break;
        };
        if parent == directory {
            break;
        }
        directory = parent.to_path_buf();
    }
    Ok(None)
}

fn resolve_installed_package(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    package_root: &Path,
    subpath: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: ResolverServices<'_, '_, '_>,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let (host, _cache, _package_stack) = services;
    let export_subpath = if subpath.is_empty() {
        ".".to_string()
    } else {
        format!("./{subpath}")
    };
    let walk_start = if subpath.is_empty() {
        package_root.to_path_buf()
    } else {
        package_root.join(subpath)
    };
    let mut chain: Vec<(PathBuf, Option<Arc<str>>)> = Vec::new();
    let mut cursor = walk_start.clone();
    loop {
        let confined = match root.confine(cursor.join("package.json")) {
            Ok(path) => path,
            Err(PathError::PathEscapesRoot { path, root }) => {
                if cursor == package_root {
                    return Err(ResolutionError::EscapesRoot {
                        path,
                        root,
                        trace: trace.clone(),
                    });
                }
                break;
            }
            Err(other) => return Err(other.into()),
        };
        let content = host.read_file(&confined);
        chain.push((confined, content));
        if cursor == package_root {
            break;
        }
        match cursor.parent() {
            Some(parent) => cursor = parent.to_path_buf(),
            None => break,
        }
    }
    for (path, content) in &chain {
        trace.push(ResolutionTraceStep::ScopeProbe {
            path: path.clone(),
            exists: content.is_some(),
            has_exports: package_has_exports(content),
        });
    }
    let package_json_path = chain
        .last()
        .map(|(path, _)| path.clone())
        .unwrap_or_else(|| package_root.join("package.json"));
    if let Some(source) = chain.last().and_then(|(_, content)| content.clone()) {
        let package = PackageJson::parse(root, &package_json_path, &source)?;
        let has_exports = package.raw().get("exports").is_some();
        if has_exports {
            let conditions = conditions_for(kind, mode, flavor);
            for name in conditions.values() {
                trace.push(ResolutionTraceStep::Condition {
                    name: Arc::clone(name),
                    matched: true,
                });
            }
        }
        let package_mode = if flavor == ResolutionFlavor::Types {
            PackageMode::Types
        } else {
            mode.package_mode()
        };
        match package.resolve_export(
            root,
            &export_subpath,
            package_mode,
            &conditions_for(kind, mode, flavor),
        ) {
            Ok(target) => {
                return finalize_package_target(
                    (root, options),
                    importer,
                    &target,
                    (kind, mode, flavor),
                    Some(package_json_path),
                    host,
                    trace,
                );
            }
            Err(error @ PackageError::SubpathNotExported { .. })
            | Err(error @ PackageError::TargetBlocked)
                if has_exports =>
            {
                return Err(error.into());
            }
            Err(PackageError::SubpathNotExported { .. })
            | Err(PackageError::NoLegacyEntry)
            | Err(PackageError::TargetBlocked) => {}
            Err(other) => return Err(other.into()),
        }
    }
    let chain_has_exports = chain
        .iter()
        .any(|(_, content)| package_has_exports(content));
    if kind == ModuleResolutionKind::Bundler
        && !chain_has_exports
        && walk_start.extension().is_none()
        && !walk_start.components().any(|component| {
            component
                .as_os_str()
                .as_encoded_bytes()
                .first()
                .is_some_and(|byte| *byte == b'@')
        })
    {
        let mut stems = vec![walk_start.clone()];
        if chain.first().is_some_and(|(_, content)| content.is_none()) {
            stems.push(walk_start.join("index"));
        }
        if let Some(found) = probe_loose_stems(host, trace, &stems, &["ts", "tsx", "d.ts"]) {
            return confined_hit(root, trace, kind, mode, &found);
        }
    }
    if kind == ModuleResolutionKind::Bundler
        && !chain_has_exports
        && chain.first().is_some_and(|(_, content)| content.is_some())
        && let Some(found) = probe_legacy_fields(host, trace, &chain)
    {
        return confined_hit(root, trace, kind, mode, &found);
    }
    // No usable exports/legacy entry: try subpath as a relative file inside the package.
    // In ESM mode (`import` under node16/nodenext) a manifest-less package performs
    // no file probing, and neither does an extensionless subpath: both fail the way
    // an extensionless relative import fails. A bare root with a manifest keeps the
    // legacy `index` default, resolved with extension substitution below.
    let has_manifest = chain.iter().any(|(_, content)| content.is_some());
    if mode == ResolutionMode::Import
        && !kind.allows_extensionless_relative()
        && (!has_manifest || !subpath.is_empty())
    {
        return Ok(None);
    }
    if subpath.is_empty() && mode == ResolutionMode::Require {
        // Oracle (tsc 7.0.2, CJS mode, manifest or not): a bare package probes
        // the package stem before its directory index, in a preferred
        // TypeScript pass first and a JavaScript fallback pass after:
        // `dep.ts, dep.tsx, dep.d.ts, dep/index.ts, dep/index.tsx,
        // dep/index.d.ts`, then `dep.js, dep.jsx, dep/index.js, dep/index.jsx`.
        // `Types` flavor hoists the declaration candidate inside each pass.
        let (preferred, fallback): (&[&str], &[&str]) = match flavor {
            ResolutionFlavor::Types => (&["d.ts", "ts", "tsx"], &["js", "jsx"]),
            ResolutionFlavor::Runtime => (&["ts", "tsx", "d.ts"], &["js", "jsx"]),
        };
        for extensions in [preferred, fallback] {
            for stem in [package_root.to_path_buf(), package_root.join("index")] {
                if let Some(found) = probe_loose_stems(host, trace, &[stem], extensions)
                    && let Some(mut resolved) = confined_hit(root, trace, kind, mode, &found)?
                {
                    resolved.package_json = Some(package_json_path.clone());
                    return Ok(Some(resolved));
                }
            }
        }
        return Ok(None);
    }
    let relative = if subpath.is_empty() {
        "./index".to_string()
    } else {
        format!("./{subpath}")
    };
    let fake_importer = package_root.join("package.json");
    match resolve_synthesized_relative(
        (root, options),
        &fake_importer,
        &relative,
        (kind, mode, flavor),
        host,
        trace,
    ) {
        Ok(mut resolved) => {
            resolved.package_json = Some(package_json_path);
            Ok(Some(resolved))
        }
        Err(ResolutionError::NotFound { .. }) => Ok(None),
        Err(other) => Err(other),
    }
}
fn finalize_package_target(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    target: &Path,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    package_json: Option<PathBuf>,
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let confined = root.confine(target)?;
    let as_relative = path_as_dot_relative(root, importer, &confined)?;
    match resolve_relative(
        (root, options),
        importer,
        &as_relative,
        (kind, mode, flavor),
        host,
        trace,
    ) {
        Ok(mut resolved) => {
            resolved.package_json = package_json;
            Ok(Some(resolved))
        }
        Err(ResolutionError::NotFound { .. }) => {
            // Also try from the target's own directory using its basename.
            let parent = confined.parent().unwrap_or_else(|| Path::new("/"));
            let name = confined
                .file_name()
                .and_then(|value| value.to_str())
                .unwrap_or("index");
            let fake = parent.join("__resolver__.ts");
            match resolve_relative(
                (root, options),
                &fake,
                &format!("./{name}"),
                (kind, mode, flavor),
                host,
                trace,
            ) {
                Ok(mut resolved) => {
                    resolved.package_json = package_json;
                    Ok(Some(resolved))
                }
                Err(ResolutionError::NotFound { .. }) => Ok(None),
                Err(other) => Err(other),
            }
        }
        Err(other) => Err(other),
    }
}

fn resolve_hash_import(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    containing: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    services: ResolverServices<'_, '_, '_>,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    let (host, cache, package_stack) = services;
    let Some(package_json_path) = find_nearest_package_json(root, containing, host) else {
        return Err(ResolutionError::NotFound {
            specifier: Arc::from(specifier),
            from: importer.to_path_buf(),
            trace: trace.clone(),
        });
    };
    let package_json_path = root.confine(package_json_path)?;
    let stack_key = (package_json_path.clone(), Arc::from(specifier));
    if !package_stack.insert(stack_key.clone()) {
        return Err(ResolutionError::PackageCycle {
            specifier: Arc::from(specifier),
            trace: trace.clone(),
        });
    }

    let Some(source) = host.read_file(&package_json_path) else {
        package_stack.remove(&stack_key);
        return Err(ResolutionError::NotFound {
            specifier: Arc::from(specifier),
            from: importer.to_path_buf(),
            trace: trace.clone(),
        });
    };
    let package = PackageJson::parse(root, &package_json_path, &source)?;
    let conditions = conditions_for(kind, mode, flavor);
    let outcome = package.resolve_import(root, specifier, &conditions);
    let result = match outcome {
        Ok(PackageTarget::Path(path)) => finalize_package_target(
            (root, options),
            importer,
            &path,
            (kind, mode, flavor),
            Some(package_json_path.clone()),
            host,
            trace,
        )?
        .ok_or_else(|| ResolutionError::NotFound {
            specifier: Arc::from(specifier),
            from: importer.to_path_buf(),
            trace: trace.clone(),
        }),
        Ok(PackageTarget::External(external)) => {
            trace.push(ResolutionTraceStep::PackageImport {
                specifier: Arc::from(specifier),
                target: Arc::clone(&external),
            });
            resolve_module_name_inner(
                (root, options),
                importer,
                external.as_ref(),
                (kind, mode, flavor),
                (host, &mut *cache, &mut *package_stack),
                None,
            )
        }
        Err(error) => Err(error.into()),
    };
    package_stack.remove(&stack_key);
    result
}

fn find_nearest_package_json(
    root: &ProjectRoot,
    containing: &Path,
    host: &dyn ResolutionHost,
) -> Option<PathBuf> {
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            return None;
        }
        let candidate = directory.join("package.json");
        if host.file_exists(&candidate) {
            return Some(candidate);
        }
        let parent = directory.parent()?;
        if parent == directory {
            return None;
        }
        directory = parent.to_path_buf();
    }
}

/// Resolves a `/// <reference types="name" />` target against the configured
/// `typeRoots`, probing `<typeRoot>/<name>/index.d.ts` and then a
/// `<typeRoot>/<name>/package.json` types entry. Names are used literally;
/// the `@types` scope mangling of the default walk does not apply here.
fn try_type_roots(
    context: (&ProjectRoot, &CompilerOptions),
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    for type_root in options.type_roots() {
        if let Some(resolved) = probe_type_root(
            (root, options),
            type_root,
            specifier,
            strategy,
            host,
            trace,
        )? {
            return Ok(Some(resolved));
        }
    }
    Ok(None)
}

/// Probes one configured type root for a type package.
fn probe_type_root(
    context: (&ProjectRoot, &CompilerOptions),
    type_root: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode) = strategy;
    let flavor = ResolutionFlavor::Types;
    let package_root = type_root.join(specifier);
    let index = package_root.join("index.d.ts");
    trace.push(ResolutionTraceStep::TypesFallback {
        package: Arc::from(specifier),
        path: index.clone(),
    });
    if host.file_exists(&index) {
        let confined = root.confine(&index)?;
        return Ok(Some(ResolvedModule {
            path: confined,
            kind,
            mode,
            package_json: Some(package_root.join("package.json")),
            trace: ResolutionTrace::default(),
        }));
    }
    let package_json = package_root.join("package.json");
    if root.confine(&package_json).is_err() {
        return Ok(None);
    }
    let Some(source) = host.read_file(&package_json) else {
        return Ok(None);
    };
    let package = PackageJson::parse(root, &package_json, &source)?;
    let conditions = conditions_for(kind, mode, flavor);
    let Ok(target) = package.resolve_export(root, ".", PackageMode::Types, &conditions) else {
        return Ok(None);
    };
    finalize_package_target(
        (root, options),
        &package_json,
        &target,
        (kind, mode, flavor),
        Some(package_json.clone()),
        host,
        trace,
    )
}


fn try_types_package(
    context: (&ProjectRoot, &CompilerOptions),
    containing: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<Option<ResolvedModule>, ResolutionError> {
    let (root, options) = context;
    let (kind, mode) = strategy;
    let rooted = if options.type_roots().is_empty() {
        None
    } else {
        try_type_roots((root, options), specifier, (kind, mode), host, trace)?
    };
    if let Some(resolved) = rooted {
        return Ok(Some(resolved));
    }
    let types_name = types_package_name(specifier);
    let mut directory = containing.to_path_buf();
    loop {
        if !directory.starts_with(root.path()) {
            break;
        }
        let package_root = directory.join("node_modules").join(&types_name);
        let index = package_root.join("index.d.ts");
        trace.push(ResolutionTraceStep::TypesFallback {
            package: Arc::from(types_name.as_str()),
            path: index.clone(),
        });
        if host.file_exists(&index) {
            let confined = root.confine(&index)?;
            return Ok(Some(ResolvedModule {
                path: confined,
                kind,
                mode,
                package_json: Some(package_root.join("package.json")),
                trace: ResolutionTrace::default(),
            }));
        }
        let package_json = package_root.join("package.json");
        if let Some(source) = host.read_file(&package_json) {
            let package = PackageJson::parse(root, &package_json, &source)?;
            let conditions = conditions_for(kind, mode, ResolutionFlavor::Types);
            if let Ok(target) = package.resolve_export(root, ".", PackageMode::Types, &conditions) {
                return finalize_package_target(
                    (root, options),
                    &package_json,
                    &target,
                    (kind, mode, ResolutionFlavor::Types),
                    Some(package_json.clone()),
                    host,
                    trace,
                );
            }
        }
        let Some(parent) = directory.parent() else {
            break;
        };
        if parent == directory {
            break;
        }
        directory = parent.to_path_buf();
    }
    Ok(None)
}

fn types_package_name(specifier: &str) -> String {
    let (name, _) = split_package_specifier(specifier);
    if let Some(rest) = name.strip_prefix('@') {
        let (scope, pkg) = rest
            .split_once('/')
            .map_or((rest, rest), |(scope, pkg)| (scope, pkg));
        format!("@types/{scope}__{pkg}")
    } else {
        format!("@types/{name}")
    }
}

fn split_package_specifier(specifier: &str) -> (String, String) {
    if let Some(rest) = specifier.strip_prefix('@') {
        let mut parts = rest.splitn(2, '/');
        let scope = parts.next().unwrap_or("");
        match parts.next() {
            None | Some("") => (format!("@{scope}"), String::new()),
            Some(remainder) => match remainder.split_once('/') {
                None => (format!("@{scope}/{remainder}"), String::new()),
                Some((pkg, subpath)) => (format!("@{scope}/{pkg}"), subpath.to_string()),
            },
        }
    } else {
        match specifier.split_once('/') {
            None => (specifier.to_string(), String::new()),
            Some((name, subpath)) => (name.to_string(), subpath.to_string()),
        }
    }
}

fn conditions_for(
    kind: ModuleResolutionKind,
    mode: ResolutionMode,
    flavor: ResolutionFlavor,
) -> ResolutionConditions {
    if flavor == ResolutionFlavor::Types {
        return ResolutionConditions::for_mode(PackageMode::Types);
    }
    match kind {
        ModuleResolutionKind::Bundler => match mode {
            ResolutionMode::Require => {
                ResolutionConditions::new(["require"]).expect("require is a valid condition")
            }
            ResolutionMode::Import => {
                ResolutionConditions::new(["import"]).expect("import is a valid condition")
            }
        },
        ModuleResolutionKind::Node16 | ModuleResolutionKind::NodeNext => {
            ResolutionConditions::for_mode(mode.package_mode())
        }
        ModuleResolutionKind::Classic => ResolutionConditions::for_mode(mode.package_mode()),
    }
}

#[cfg(test)]
mod tests;
