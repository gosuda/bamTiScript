//! Module resolution modes for node16 / nodenext / bundler.
//!
//! Builds on the lexical foundation in [`crate::project`]:
//! [`ProjectRoot`] confinement, [`plan_relative_module`] extension substitution,
//! and [`PackageJson`] exports/imports. This module owns the I/O-driven walk,
//! resolution-mode conditions, deterministic trace, and cycle-safe package lookup.
//! It does not introduce a second path, options, or diagnostics model.

use super::resolution_trace::ResolutionTraceLog;
use crate::project::{
    CompilerOptions, ModuleResolutionError, PackageError, PackageJson, PackageMode, PackageTarget,
    PathError, PathMapping, ProjectRoot, ResolutionConditions, ResolutionFlavor,
    plan_relative_module,
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
}

impl ModuleResolutionKind {
    /// Parses a tsconfig `moduleResolution` string. Matching is case-insensitive
    /// and accepts the forms TypeScript documents (`node16`, `nodenext`, `bundler`).
    pub fn parse(value: &str) -> Result<Self, ResolutionError> {
        match value.trim().to_ascii_lowercase().as_str() {
            "node16" => Ok(Self::Node16),
            "nodenext" => Ok(Self::NodeNext),
            "bundler" => Ok(Self::Bundler),
            _ => Err(ResolutionError::UnsupportedKind {
                value: Arc::from(value),
            }),
        }
    }

    /// Resolves the kind from compiler options, defaulting to `NodeNext` when unset.
    pub fn from_options(options: &CompilerOptions) -> Result<Self, ResolutionError> {
        match options.module_resolution() {
            Some(value) => Self::parse(value),
            None => Ok(Self::NodeNext),
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Node16 => "node16",
            Self::NodeNext => "nodenext",
            Self::Bundler => "bundler",
        }
    }

    /// Whether relative imports may omit an extension (bundler yes; node16/nodenext no
    /// for the *original* specifier, though extension substitution still applies to
    /// `.js` → `.ts` rewrites).
    #[must_use]
    pub const fn allows_extensionless_relative(self) -> bool {
        matches!(self, Self::Bundler)
    }
    /// Upstream trace spelling used by `traceResolution` output.
    #[must_use]
    pub const fn trace_name(self) -> &'static str {
        match self {
            Self::Node16 => "Node16",
            Self::NodeNext => "NodeNext",
            Self::Bundler => "Bundler",
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
    PackageJson {
        path: PathBuf,
        subpath: Arc<str>,
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
                &importer,
                specifier,
                (kind, mode, flavor),
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
            &importer,
            specifier,
            (kind, mode, flavor),
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

fn resolve_relative(
    context: (&ProjectRoot, &CompilerOptions),
    importer: &Path,
    specifier: &str,
    strategy: (ModuleResolutionKind, ResolutionMode, ResolutionFlavor),
    host: &dyn ResolutionHost,
    trace: &mut ResolutionTrace,
) -> Result<ResolvedModule, ResolutionError> {
    let (root, options) = context;
    let (kind, mode, flavor) = strategy;
    if mode == ResolutionMode::Import
        && !kind.allows_extensionless_relative()
        && Path::new(specifier).extension().is_none()
    {
        return Err(ResolutionError::NotFound {
            specifier: Arc::from(specifier),
            from: importer.to_path_buf(),
            trace: trace.clone(),
        });
    }
    let plan = plan_relative_module(
        root,
        importer,
        specifier,
        flavor,
        options.resolve_json_module(),
    )?;
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
        let node_modules = directory.join("node_modules");
        trace.push(ResolutionTraceStep::NodeModulesWalk {
            directory: directory.clone(),
            exists: host.directory_exists(&node_modules),
            fallback: false,
        });
        let package_root = directory.join("node_modules").join(&package_name);
        if (host.directory_exists(&package_root)
            || host.file_exists(&package_root.join("package.json")))
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
    let package_json_path = package_root.join("package.json");
    let package_json_path = match root.confine(&package_json_path) {
        Ok(path) => path,
        Err(PathError::PathEscapesRoot { path, root }) => {
            return Err(ResolutionError::EscapesRoot {
                path,
                root,
                trace: trace.clone(),
            });
        }
        Err(other) => return Err(other.into()),
    };

    let export_subpath = if subpath.is_empty() {
        ".".to_string()
    } else {
        format!("./{subpath}")
    };
    trace.push(ResolutionTraceStep::PackageJson {
        path: package_json_path.clone(),
        subpath: Arc::from(export_subpath.as_str()),
    });

    let conditions = conditions_for(kind, mode, flavor);
    for name in conditions.values() {
        trace.push(ResolutionTraceStep::Condition {
            name: Arc::clone(name),
            matched: true,
        });
    }

    if let Some(source) = host.read_file(&package_json_path) {
        let package = PackageJson::parse(root, &package_json_path, &source)?;
        let has_exports = package.raw().get("exports").is_some();
        let package_mode = if flavor == ResolutionFlavor::Types {
            PackageMode::Types
        } else {
            mode.package_mode()
        };
        match package.resolve_export(root, &export_subpath, package_mode, &conditions) {
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

    // No usable exports/legacy entry: try subpath as a relative file inside the package.
    let relative = if subpath.is_empty() {
        "./index".to_string()
    } else {
        format!("./{subpath}")
    };
    let fake_importer = package_root.join("package.json");
    match resolve_relative(
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::canonical::slash_text;
    use crate::project::test_paths::abs;
    use crate::project::{JsonObject, JsonValue, PathMapping, ProjectConfig};
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct MemoryHost {
        files: BTreeMap<PathBuf, Arc<str>>,
        directories: BTreeSet<PathBuf>,
    }

    impl MemoryHost {
        fn file(&mut self, path: impl AsRef<Path>, source: &str) {
            let path = path.as_ref().to_path_buf();
            if let Some(parent) = path.parent() {
                self.mark_dirs(parent);
            }
            self.files.insert(path, Arc::from(source));
        }

        fn mark_dirs(&mut self, path: &Path) {
            let mut current = Some(path);
            while let Some(dir) = current {
                self.directories.insert(dir.to_path_buf());
                current = dir.parent();
            }
        }
    }

    impl ResolutionHost for MemoryHost {
        fn file_exists(&self, path: &Path) -> bool {
            self.files.contains_key(path)
        }

        fn directory_exists(&self, path: &Path) -> bool {
            self.directories.contains(path) || self.files.keys().any(|file| file.starts_with(path))
        }

        fn read_file(&self, path: &Path) -> Option<Arc<str>> {
            self.files.get(path).cloned()
        }
    }

    fn root() -> ProjectRoot {
        ProjectRoot::new(abs("/workspace")).expect("absolute root")
    }

    /// How a trace line spells the root of the fixture file system: c: on Windows,
    /// where upstream traces print a lowercase drive, and nothing elsewhere.
    fn trace_drive() -> String {
        slash_text(&abs("/"))
            .trim_end_matches('/')
            .to_ascii_lowercase()
    }

    fn options_with_resolution(module_resolution: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(
                r#"{{"compilerOptions":{{"moduleResolution":"{module_resolution}","resolveJsonModule":true}}}}"#
            ),
        )
        .expect("config");
        config.options().clone()
    }

    fn options_with_paths(paths_json: &str) -> CompilerOptions {
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            &format!(
                r#"{{"compilerOptions":{{"moduleResolution":"bundler","baseUrl":".","paths":{paths_json}}}}}"#
            ),
        )
        .expect("config");
        config.options().clone()
    }

    #[test]
    fn parses_node16_nodenext_bundler_and_resolution_mode() {
        assert_eq!(
            ModuleResolutionKind::parse("Node16").unwrap(),
            ModuleResolutionKind::Node16
        );
        assert_eq!(
            ModuleResolutionKind::parse("nodenext").unwrap(),
            ModuleResolutionKind::NodeNext
        );
        assert_eq!(
            ModuleResolutionKind::parse("BUNDLER").unwrap(),
            ModuleResolutionKind::Bundler
        );
        assert!(ModuleResolutionKind::parse("classic").is_err());
        assert_eq!(
            ResolutionMode::parse("import").unwrap(),
            ResolutionMode::Import
        );
        assert_eq!(
            ResolutionMode::parse("require").unwrap(),
            ResolutionMode::Require
        );
        assert!(ResolutionMode::parse("eval").is_err());
        assert!(ModuleResolutionKind::Bundler.allows_extensionless_relative());
        assert!(!ModuleResolutionKind::Node16.allows_extensionless_relative());
    }

    #[test]
    fn relative_extension_substitution_and_index_fallback() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/util.ts"), "export const n = 1;\n");
        host.file(abs("/workspace/src/nested/index.ts"), "export {};\n");
        let options = options_with_resolution("node16");
        let mut cache = ResolutionCache::new();

        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./util.js",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("util.js → util.ts");
        assert_eq!(resolved.path(), abs("/workspace/src/util.ts").as_path());
        assert!(
            resolved
                .trace()
                .steps()
                .iter()
                .any(|step| matches!(step, ResolutionTraceStep::Candidate { exists: true, .. }))
        );

        let nested = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./nested",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("directory index");
        assert_eq!(
            nested.path(),
            abs("/workspace/src/nested/index.ts").as_path()
        );
    }
    #[test]
    fn nodenext_import_requires_relative_extension_but_require_and_bundler_do_not() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/util.ts"), "export const n = 1;\n");
        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();
        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./util",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(matches!(missing, Err(ResolutionError::NotFound { .. })));
        for strategy in [
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
        ] {
            let resolved = resolve_module_name(
                &root(),
                &options,
                abs("/workspace/src/main.ts"),
                "./util",
                strategy,
                &host,
                &mut cache,
            )
            .expect("extensionless resolution is permitted");
            assert_eq!(resolved.path(), abs("/workspace/src/util.ts").as_path());
        }
    }

    #[test]
    fn paths_longest_prefix_wins_with_star_substitution() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/lib/foo/bar.ts"), "export {};\n");
        let options = options_with_paths(r#"{ "@app/*": ["lib/*"], "@app/foo/*": ["lib/foo/*"] }"#);
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@app/foo/bar",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("paths");
        assert_eq!(resolved.path(), abs("/workspace/lib/foo/bar.ts").as_path());
        assert!(resolved.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::PathsMatch { pattern, .. } if pattern.as_ref() == "@app/foo/*"
        )));
    }

    #[test]
    fn package_exports_honor_resolution_mode_conditions() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/pkg/package.json"),
            r#"{
                "name":"pkg",
                "exports":{
                    ".":{
                        "import":"./esm.js",
                        "require":"./cjs.js"
                    }
                }
            }"#,
        );
        host.file(abs("/workspace/node_modules/pkg/esm.js"), "export {};\n");
        host.file(
            abs("/workspace/node_modules/pkg/cjs.js"),
            "module.exports = {};\n",
        );
        // Provide TS stand-ins so extension substitution can succeed for both modes.
        host.file(abs("/workspace/node_modules/pkg/esm.ts"), "export {};\n");
        host.file(abs("/workspace/node_modules/pkg/cjs.ts"), "export {};\n");

        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();

        let import_hit = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("import condition");
        assert_eq!(
            import_hit.path(),
            abs("/workspace/node_modules/pkg/esm.ts").as_path()
        );

        let require_hit = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("require condition");
        assert_eq!(
            require_hit.path(),
            abs("/workspace/node_modules/pkg/cjs.ts").as_path()
        );
    }
    #[test]
    fn package_exports_block_private_and_null_subpaths() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/pkg/package.json"),
            r#"{"exports":{".":"./index.js","./blocked":null}}"#,
        );
        host.file(abs("/workspace/node_modules/pkg/index.ts"), "export {};\n");
        host.file(
            abs("/workspace/node_modules/pkg/private.ts"),
            "export {};\n",
        );
        host.file(
            abs("/workspace/node_modules/pkg/blocked.ts"),
            "export {};\n",
        );
        let options = options_with_resolution("nodenext");
        for specifier in ["pkg/private", "pkg/blocked"] {
            let error = resolve_module_name(
                &root(),
                &options,
                abs("/workspace/src/main.ts"),
                specifier,
                (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
                &host,
                &mut ResolutionCache::new(),
            )
            .expect_err("exports encapsulation blocks filesystem fallback");
            assert!(matches!(
                error,
                ResolutionError::Package(PackageError::SubpathNotExported { .. })
                    | ResolutionError::Package(PackageError::TargetBlocked)
            ));
        }
    }

    #[test]
    fn package_imports_resolve_and_detect_cycles() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/package.json"),
            r##"{
                "name":"app",
                "imports":{
                    "#internal/*": "./src/*.ts",
                    "#loop": "#loop"
                }
            }"##,
        );
        host.file(abs("/workspace/src/value.ts"), "export const v = 1;\n");
        host.file(abs("/workspace/src/main.ts"), "import '#internal/value';\n");

        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "#internal/value",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("hash import");
        assert_eq!(resolved.path(), abs("/workspace/src/value.ts").as_path());

        let cycle = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "#loop",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect_err("self-import cycle");
        assert!(matches!(cycle, ResolutionError::PackageCycle { .. }));
    }

    #[test]
    fn node_modules_walk_stops_at_project_root_and_confinement_rejects_escape() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/left-pad/package.json"),
            r#"{"name":"left-pad","main":"./index.js"}"#,
        );
        host.file(
            abs("/workspace/node_modules/left-pad/index.ts"),
            "export {};\n",
        );
        host.file(
            abs("/workspace/node_modules/left-pad/index.js"),
            "module.exports = {};\n",
        );

        let options = options_with_resolution("node16");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/packages/app/src/main.ts"),
            "left-pad",
            (ModuleResolutionKind::Node16, ResolutionMode::Require),
            &host,
            &mut cache,
        )
        .expect("upward walk");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/left-pad/index.ts").as_path()
        );
        assert!(
            resolved
                .trace()
                .steps()
                .iter()
                .any(|step| matches!(step, ResolutionTraceStep::NodeModulesWalk { .. }))
        );

        let escape = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "../../outside",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(escape.is_err(), "escaping relative must fail");
    }

    #[test]
    fn types_fallback_mangles_scoped_package_names() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/@types/scope__pkg/index.d.ts"),
            "export {};\n",
        );
        let options = options_with_resolution("nodenext");
        let mut cache = ResolutionCache::new();
        let resolved = resolve_type_reference(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@scope/pkg",
            (ModuleResolutionKind::NodeNext, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("@types scope mangling");
        assert_eq!(
            resolved.path(),
            abs("/workspace/node_modules/@types/scope__pkg/index.d.ts").as_path()
        );
        assert!(resolved.trace().steps().iter().any(|step| matches!(
            step,
            ResolutionTraceStep::TypesFallback { package, .. }
                if package.as_ref() == "@types/scope__pkg"
        )));
    }

    #[test]
    fn cache_returns_identical_results_for_repeated_lookups() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/a.ts"), "export {};\n");
        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let first = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./a",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("first");
        let second = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./a",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("second");
        assert_eq!(first, second);
        assert_eq!(cache.len(), 1);

        let missing = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert!(missing.is_err());
        let missing_again = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        );
        assert_eq!(
            missing.as_ref().err().map(ToString::to_string),
            missing_again.err().map(|e| e.to_string())
        );
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn trace_is_deterministic_across_two_fresh_caches() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/node_modules/demo/package.json"),
            r#"{"name":"demo","exports":{".":{"import":"./lib.js"}}}"#,
        );
        host.file(abs("/workspace/node_modules/demo/lib.ts"), "export {};\n");
        host.file(abs("/workspace/node_modules/demo/lib.js"), "export {};\n");
        let options = options_with_resolution("node16");

        let mut cache_a = ResolutionCache::new();
        let a = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "demo",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache_a,
        )
        .expect("a");
        let mut cache_b = ResolutionCache::new();
        let b = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "demo",
            (ModuleResolutionKind::Node16, ResolutionMode::Import),
            &host,
            &mut cache_b,
        )
        .expect("b");
        assert_eq!(a.trace(), b.trace());
    }

    #[test]
    fn from_options_reads_compiler_module_resolution() {
        let options = options_with_resolution("bundler");
        assert_eq!(
            ModuleResolutionKind::from_options(&options).unwrap(),
            ModuleResolutionKind::Bundler
        );
        // Prove PathMapping surface remains the shared model (no duplicate paths type).
        let _mappings: &[PathMapping] = options.paths();
        let _object_ty: Option<&JsonObject> = None;
        let _value_ty: Option<&JsonValue> = None;
    }
    #[test]
    fn trace_kind_line_marks_unspecified_resolution_kind() {
        let unspecified = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{}}"#,
        )
        .expect("config")
        .options()
        .clone();
        let specified = options_with_resolution("bundler");
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/other.ts"), "export {};\n");
        for (options, expected) in [
            (
                unspecified,
                "Module resolution kind is not specified, using 'Bundler'.",
            ),
            (
                specified,
                "Explicitly specified module resolution kind: 'Bundler'.",
            ),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            resolve_module_name_with_trace(
                &root(),
                &options,
                abs("/workspace/main.ts"),
                "./other",
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("relative resolution");
            assert!(
                log.lines().iter().any(|line| line == expected),
                "missing `{expected}` in {:?}",
                log.lines()
            );
        }
    }
    #[test]
    fn trace_bundler_bare_miss_matches_upstream_walk() {
        let options = options_with_resolution("bundler");
        let host = MemoryHost::default();
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();
        let outcome = resolve_module_name_with_trace(
            &root(),
            &options,
            abs("/workspace/a/b/c/lib.ts"),
            "foo",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Import,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        );
        assert!(outcome.is_err());
        let expected: &[&str] = &[
            "======== Resolving module 'foo' from '/workspace/a/b/c/lib.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in CJS mode with conditions 'import', 'types'.",
            "File '/workspace/a/b/c/package.json' does not exist.",
            "File '/workspace/a/b/package.json' does not exist.",
            "File '/workspace/a/package.json' does not exist.",
            "File '/workspace/package.json' does not exist.",
            "Loading module 'foo' from 'node_modules' folder, target file types: TypeScript, JavaScript, Declaration, JSON.",
            "Searching all ancestor node_modules directories for preferred extensions: TypeScript, Declaration.",
            "Directory '/workspace/a/b/c/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/node_modules' does not exist, skipping all lookups in it.",
            "Searching all ancestor node_modules directories for fallback extensions: JavaScript, JSON.",
            "Directory '/workspace/a/b/c/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/b/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/a/node_modules' does not exist, skipping all lookups in it.",
            "Directory '/workspace/node_modules' does not exist, skipping all lookups in it.",
            "======== Module name 'foo' was not resolved. ========",
        ];
        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/workspace", &format!("'{drive}/workspace")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_log_matches_upstream_bundler_relative_blob() {
        // Lines pinned byte-for-byte to the upstream baseline blob
        // sha256 1170256ebc7a95579edb54bfe7ce1b8c6ffd8ffcf8a219318822605ad58fdda3
        // (tests/baselines/reference/bundlerRelative1(module=bundler).trace.json,
        // indices 12..=31) plus its cache-hit re-resolution template. The mode
        // word follows the per-import ResolutionMode: Import renders ESM.
        let expected: &[&str] = &[
            "======== Resolving module './dir/index' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in ESM mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index.js' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in ESM mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index.js', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File name '/dir/index.js' has a '.js' extension - stripping it.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index.js' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index.ts' from '/main.ts'. ========",
            "Explicitly specified module resolution kind: 'Bundler'.",
            "Resolving in ESM mode with conditions 'import', 'types'.",
            "Loading module as file / folder, candidate module location '/dir/index.ts', target file types: TypeScript, JavaScript, Declaration, JSON.",
            "File name '/dir/index.ts' has a '.ts' extension - stripping it.",
            "File '/dir/index.ts' exists - use it as a name resolution result.",
            "======== Module name './dir/index.ts' was successfully resolved to '/dir/index.ts'. ========",
            "======== Resolving module './dir/index' from '/main.ts'. ========",
            "Resolution for module './dir/index' was found in cache from location '/'.",
            "======== Module name './dir/index' was successfully resolved to '/dir/index.ts'. ========",
        ];

        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/main.ts"), "import {} from './dir/index.js';\n");
        host.file(abs("/dir/index.ts"), "export {};\n");
        let mut cache = ResolutionCache::new();
        let mut log = ResolutionTraceLog::default();

        for specifier in ["./dir/index", "./dir/index.js", "./dir/index.ts"] {
            resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                specifier,
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .unwrap_or_else(|error| panic!("resolve {specifier}: {error}"));
        }
        resolve_module_name_with_trace(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (
                ModuleResolutionKind::Bundler,
                ResolutionMode::Import,
                ResolutionFlavor::Runtime,
            ),
            TraceResolutionServices {
                host: &host,
                cache: &mut cache,
                log: &mut log,
            },
        )
        .expect("cache hit");

        let drive = trace_drive();
        let expected: Vec<String> = expected
            .iter()
            .map(|line| line.replace("'/", &format!("'{drive}/")))
            .collect();
        let produced: Vec<&str> = log.lines().iter().map(String::as_str).collect();
        assert_eq!(produced, expected);
        assert!(log.unsupported().is_empty());
    }
    #[test]
    fn trace_mode_word_follows_resolution_mode() {
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.ts"), "export {};\n");

        for (mode, word) in [
            (ResolutionMode::Import, "ESM"),
            (ResolutionMode::Require, "CJS"),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                "./dir/index.ts",
                (
                    ModuleResolutionKind::Bundler,
                    mode,
                    ResolutionFlavor::Runtime,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("relative resolution");
            let expected = format!(
                "Resolving in {word} mode with conditions '{}', 'types'.",
                mode.as_str()
            );
            assert!(
                log.lines().iter().any(|line| line == &expected),
                "missing `{expected}` in {:?}",
                log.lines()
            );
        }
    }

    #[test]
    fn trace_types_flavor_narrates_declaration_candidates_first() {
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let config = ProjectConfig::parse(
            &fs_root,
            abs("/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.d.ts"), "export {};\n");
        host.file(abs("/dir/index.ts"), "export {};\n");

        for (flavor, chosen, narrated) in [
            (ResolutionFlavor::Runtime, "index.ts", "dir/index.ts"),
            (ResolutionFlavor::Types, "index.d.ts", "dir/index.d.ts"),
        ] {
            let mut cache = ResolutionCache::new();
            let mut log = ResolutionTraceLog::default();
            let resolved = resolve_module_name_with_trace(
                &fs_root,
                &options,
                abs("/main.ts"),
                "./dir/index",
                (
                    ModuleResolutionKind::Bundler,
                    ResolutionMode::Import,
                    flavor,
                ),
                TraceResolutionServices {
                    host: &host,
                    cache: &mut cache,
                    log: &mut log,
                },
            )
            .expect("resolution");
            assert_eq!(resolved.path(), abs(&format!("/dir/{chosen}")).as_path());
            // Narration stops at the first probed candidate, so the single
            // narrated file must be the one the resolver actually chose.
            let narrated_files: Vec<String> = log
                .lines()
                .iter()
                .filter(|line| line.starts_with("File '"))
                .cloned()
                .collect();
            let expected = format!(
                "File '{}/{narrated}' exists - use it as a name resolution result.",
                trace_drive()
            );
            assert_eq!(narrated_files, vec![expected]);
        }
    }

    #[test]
    fn cache_keys_distinguish_runtime_and_types_flavors() {
        let fs_root = ProjectRoot::new(abs("/")).expect("absolute root");
        let mut host = MemoryHost::default();
        host.file(abs("/dir/index.d.ts"), "export {};\n");
        host.file(abs("/dir/index.ts"), "export {};\n");
        let options = options_with_resolution("bundler");
        let mut cache = ResolutionCache::new();
        let runtime = resolve_module_name(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("runtime flavor");
        let types = resolve_type_reference(
            &fs_root,
            &options,
            abs("/main.ts"),
            "./dir/index",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("types flavor");
        assert_eq!(runtime.path(), abs("/dir/index.ts").as_path());
        assert_eq!(types.path(), abs("/dir/index.d.ts").as_path());
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn json_specifier_resolves_the_exact_file_when_resolve_json_module_is_on() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/data.json"), "{\n  \"a\": 1\n}\n");
        // A script module beside the JSON file must not win: a `.json`
        // specifier is planned as an exact file with no extension
        // substitution.
        host.file(abs("/workspace/src/data.ts"), "export const a = 1;\n");
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","resolveJsonModule":true}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./data.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("exact JSON module");
        assert_eq!(resolved.path(), abs("/workspace/src/data.json").as_path());
        assert!(
            resolved.trace().steps().iter().all(|step| !matches!(
                step,
                ResolutionTraceStep::Candidate { path, .. }
                    if path.extension().is_some_and(|ext| ext != "json"),
            )),
            "no non-JSON candidate may be probed"
        );
    }

    #[test]
    fn json_specifier_probes_the_exact_file_even_when_resolve_json_module_is_off() {
        let mut host = MemoryHost::default();
        host.file(abs("/workspace/src/data.json"), "{\n  \"a\": 1\n}\n");
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler"}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        // Upstream resolves a relative exact `.json` import even without
        // `resolveJsonModule` (requireOfJsonFileWithoutResolveJsonModule,
        // importAssertionsDeprecated): the flag only decides whether `.json`
        // joins the *searched* extension list.
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./data.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("exact JSON module resolves without the flag");
        assert_eq!(resolved.path(), abs("/workspace/src/data.json").as_path());

        // A `.json` specifier that names no file fails as a plain cannot-find
        // miss (upstream TS2732) — never as an unsupported-extension
        // rejection.
        let error = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "./missing.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect_err("missing JSON module cannot resolve");
        assert!(matches!(error, ResolutionError::NotFound { .. }));
    }

    #[test]
    fn json_specifier_with_paths_mapping_resolves_through_the_mapping() {
        let mut host = MemoryHost::default();
        host.file(
            abs("/workspace/config/pkg.json"),
            "{\n  \"name\": \"pkg\"\n}\n",
        );
        let config = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","baseUrl":".","paths":{"@config/*":["config/*"]},"resolveJsonModule":true}}"#,
        )
        .expect("config");
        let options = config.options().clone();
        let mut cache = ResolutionCache::new();
        let resolved = resolve_module_name(
            &root(),
            &options,
            abs("/workspace/src/main.ts"),
            "@config/pkg.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut cache,
        )
        .expect("paths-mapped JSON module");
        assert_eq!(resolved.path(), abs("/workspace/config/pkg.json").as_path());

        // The searched routes stay flag-gated: with `resolveJsonModule`
        // disabled a paths-mapped `.json` cannot be found with the current
        // settings (upstream TS2732 on
        // requireOfJsonFileWithoutResolveJsonModuleAndPathMapping), even
        // though the mapped target file exists.
        let without_flag = ProjectConfig::parse(
            &root(),
            abs("/workspace/tsconfig.json"),
            r#"{"compilerOptions":{"moduleResolution":"bundler","baseUrl":".","paths":{"@config/*":["config/*"]}}}"#,
        )
        .expect("config");
        // A fresh cache: the flag-on probe above stored its hit under the
        // same (directory, specifier) key.
        let mut fresh = ResolutionCache::new();
        let error = resolve_module_name(
            &root(),
            without_flag.options(),
            abs("/workspace/src/main.ts"),
            "@config/pkg.json",
            (ModuleResolutionKind::Bundler, ResolutionMode::Import),
            &host,
            &mut fresh,
        )
        .expect_err("flag-off paths JSON cannot resolve");
        assert!(matches!(error, ResolutionError::NotFound { .. }));
    }
}
