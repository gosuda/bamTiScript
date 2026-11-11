//! Incremental language-service state over the compiler's parser and checker products.
//!
//! A document update constructs one immutable [`DocumentSnapshot`]. Every synchronous
//! and asynchronous query borrows that same snapshot; the service never reparses or
//! rechecks inside an individual language operation.

pub mod r#async;
pub mod filesystem;
pub mod language_service;
pub mod sync;
#[cfg(test)]
mod test_support;

use bamts_cancel::CancellationToken;
use std::{
    borrow::Cow,
    collections::BTreeMap,
    fmt, io,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    checker::{
        self, SemanticModel,
        diagnostic_messages::{Args, by_u32},
    },
    diagnostic::{Diagnostic, DiagnosticCode, Recovered},
    lint::{LintProfile, LintTable},
    parser,
    project::{
        CompilerOptions, ProjectConfig, ProjectRoot,
        resolution::{
            ModuleResolutionKind, ResolutionCache, ResolutionHost, ResolutionMode,
            resolve_module_name, resolve_type_reference,
        },
    },
    scanner,
    source::{ScriptKind, SourceId, SourcePositionError, SourceText, TextRange},
    syntax::{
        ExportDeclaration, ExportNamedDeclaration, ExportSpecifierMode, ExternalModuleReference,
        ImportBinding, ImportSpecifierMode, SourceFile, Statement, StringLiteralNode,
    },
};

use filesystem::{FileMetadata, FileSystem, FileSystemError};

pub use language_service::{
    Completion, DiagnosticEntry, DocumentEdit, Location, QuickInfo, QuickInfoKind, RenameEdit,
    RenameResult,
};

/// A public service request failure. Compiler diagnostics remain ordinary query data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ServiceError {
    FileSystem(FileSystemError),
    Source(SourcePositionError),
    DocumentNotOpen(PathBuf),
    DocumentNotFound(PathBuf),
    VersionOutOfOrder {
        path: PathBuf,
        current: u64,
        proposed: u64,
    },
    InvalidPosition {
        path: PathBuf,
        offset: usize,
    },
    InvalidRename(String),
    RenameUnavailable,
    Cancelled,
    Backpressure,
    LockPoisoned,
}

impl fmt::Display for ServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(error) => error.fmt(formatter),
            Self::FileSystem(error) => error.fmt(formatter),
            Self::DocumentNotOpen(path) => {
                write!(formatter, "document is not open: {}", path.display())
            }
            Self::DocumentNotFound(path) => {
                write!(formatter, "document was not found: {}", path.display())
            }
            Self::VersionOutOfOrder {
                path,
                current,
                proposed,
            } => write!(
                formatter,
                "document version must increase for {}: current={current}, proposed={proposed}",
                path.display()
            ),
            Self::InvalidPosition { path, offset } => {
                write!(
                    formatter,
                    "invalid UTF-16 position {offset} in {}",
                    path.display()
                )
            }
            Self::InvalidRename(message) => formatter.write_str(message),
            Self::RenameUnavailable => {
                formatter.write_str("no renameable symbol at the requested position")
            }
            Self::Cancelled => formatter.write_str("service request was cancelled"),
            Self::Backpressure => formatter.write_str("service request queue is full"),
            Self::LockPoisoned => formatter.write_str("service state lock is poisoned"),
        }
    }
}

impl std::error::Error for ServiceError {}

impl From<FileSystemError> for ServiceError {
    fn from(error: FileSystemError) -> Self {
        Self::FileSystem(error)
    }
}

impl From<SourcePositionError> for ServiceError {
    fn from(error: SourcePositionError) -> Self {
        Self::Source(error)
    }
}

/// One immutable compiler/checker product for one version of a source file.
#[derive(Clone)]
pub struct DocumentSnapshot {
    path: PathBuf,
    version: u64,
    open: bool,
    parsed: Arc<Recovered<SourceFile>>,
    semantic: Arc<Recovered<SemanticModel>>,
    diagnostics: Arc<[Diagnostic]>,
    disk_metadata: Option<FileMetadata>,
}

impl DocumentSnapshot {
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }
    #[must_use]
    pub const fn version(&self) -> u64 {
        self.version
    }
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open
    }
    #[must_use]
    pub fn source(&self) -> &SourceFile {
        self.parsed.product()
    }
    #[must_use]
    pub fn semantic(&self) -> &SemanticModel {
        self.semantic.product()
    }
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

/// A coherent, immutable view of every source known to the service.
#[derive(Clone, Default)]
pub struct ServiceSnapshot {
    documents: BTreeMap<PathBuf, Arc<DocumentSnapshot>>,
}

impl ServiceSnapshot {
    #[must_use]
    pub fn document(&self, path: &Path) -> Option<&DocumentSnapshot> {
        self.documents.get(path).map(Arc::as_ref)
    }

    pub fn documents(&self) -> impl Iterator<Item = &DocumentSnapshot> {
        self.documents.values().map(Arc::as_ref)
    }
}

/// Mutable project state. Mutations replace whole document snapshots atomically.
pub struct ServiceState<F: FileSystem> {
    pub(crate) filesystem: F,
    pub(crate) documents: BTreeMap<PathBuf, Arc<DocumentSnapshot>>,
    next_source_id: u32,
    resolution_root: Option<PathBuf>,
    resolution_config: Option<ResolutionConfig>,
}

impl<F: FileSystem> ServiceState<F> {
    #[must_use]
    pub fn new(filesystem: F) -> Self {
        Self {
            filesystem,
            documents: BTreeMap::new(),
            next_source_id: 0,
            resolution_root: None,
            resolution_config: None,
        }
    }

    /// Configures the workspace root used to surface unresolvable relative
    /// imports as `TS2307` diagnostics. Loads `tsconfig.json` under `root`
    /// when present; otherwise falls back to `Bundler` / `Import` defaults.
    pub fn set_resolution_root(&mut self, root: PathBuf) {
        self.resolution_config = load_resolution_config(&self.filesystem, &root);
        self.resolution_root = Some(root);
    }

    pub fn open(
        &mut self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.open_with_cancel(path, text, version, &CancellationToken::new())
    }

    pub fn open_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancel: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        let path = self.filesystem.normalize(path.as_ref())?;
        if let Some(current) = self.documents.get(&path).filter(|document| document.open)
            && version <= current.version
        {
            return Err(ServiceError::VersionOutOfOrder {
                path,
                current: current.version,
                proposed: version,
            });
        }
        let source_id = self.source_id_for(&path);
        let snapshot = Arc::new(build_snapshot_with_cancel(
            path.clone(),
            source_id,
            SnapshotContent {
                text: text.into(),
                version,
                open: true,
                disk_metadata: None,
            },
            cancel,
            self.resolution_config.as_ref(),
            &self.filesystem,
        )?);
        self.commit_new_document(path, snapshot, cancel)
    }

    pub fn update(
        &mut self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.update_with_cancel(path, text, version, &CancellationToken::new())
    }

    pub fn update_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancel: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        let path = self.filesystem.normalize(path.as_ref())?;
        let current = self
            .documents
            .get(&path)
            .filter(|document| document.open)
            .ok_or_else(|| ServiceError::DocumentNotOpen(path.clone()))?;
        if version <= current.version {
            return Err(ServiceError::VersionOutOfOrder {
                path,
                current: current.version,
                proposed: version,
            });
        }
        let source_id = current.source().source_id();
        let snapshot = Arc::new(build_snapshot_with_cancel(
            path.clone(),
            source_id,
            SnapshotContent {
                text: text.into(),
                version,
                open: true,
                disk_metadata: None,
            },
            cancel,
            self.resolution_config.as_ref(),
            &self.filesystem,
        )?);
        self.commit_replacement_document(path, snapshot, cancel)
    }

    pub fn close(&mut self, path: impl AsRef<Path>) -> Result<(), ServiceError> {
        self.close_with_cancel(path, &CancellationToken::new())
    }

    pub fn close_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        cancel: &CancellationToken,
    ) -> Result<(), ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        let path = self.filesystem.normalize(path.as_ref())?;
        let current = self
            .documents
            .get(&path)
            .filter(|document| document.open)
            .ok_or_else(|| ServiceError::DocumentNotOpen(path.clone()))?;
        let source_id = current.source().source_id();
        match self.filesystem.read(&path) {
            Ok(text) => {
                let metadata = self.filesystem.metadata(&path).ok();
                let snapshot = build_snapshot_with_cancel(
                    path.clone(),
                    source_id,
                    SnapshotContent {
                        text: Arc::<str>::from(text),
                        version: 0,
                        open: false,
                        disk_metadata: metadata,
                    },
                    cancel,
                    self.resolution_config.as_ref(),
                    &self.filesystem,
                )?;
                self.commit_replacement_document(path, Arc::new(snapshot), cancel)?;
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                cancel.check().map_err(|_| ServiceError::Cancelled)?;
                self.documents.remove(&path);
            }
            Err(error) => return Err(error.into()),
        }
        Ok(())
    }

    #[must_use]
    pub fn snapshot(&self) -> ServiceSnapshot {
        ServiceSnapshot {
            documents: self.documents.clone(),
        }
    }

    pub(crate) fn ensure_document(
        &mut self,
        path: &Path,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.ensure_document_with_cancel(path, &CancellationToken::new())
    }

    pub(crate) fn ensure_document_with_cancel(
        &mut self,
        path: &Path,
        cancel: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        let path = self.filesystem.normalize(path)?;
        if let Some(document) = self.documents.get(&path).filter(|document| document.open) {
            return Ok(Arc::clone(document));
        }

        let metadata = self.filesystem.metadata(&path).map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                ServiceError::DocumentNotFound(path.clone())
            } else {
                error.into()
            }
        })?;
        if let Some(document) = self.documents.get(&path)
            && document.disk_metadata == Some(metadata)
        {
            return Ok(Arc::clone(document));
        }

        let text = self.filesystem.read(&path)?;
        let source_id = self.source_id_for(&path);
        let snapshot = Arc::new(build_snapshot_with_cancel(
            path.clone(),
            source_id,
            SnapshotContent {
                text: Arc::<str>::from(text),
                version: 0,
                open: false,
                disk_metadata: Some(metadata),
            },
            cancel,
            self.resolution_config.as_ref(),
            &self.filesystem,
        )?);
        self.commit_new_document(path, snapshot, cancel)
    }

    fn commit_new_document(
        &mut self,
        path: PathBuf,
        snapshot: Arc<DocumentSnapshot>,
        cancel: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.commit_source_id(&path);
        self.documents.insert(path, Arc::clone(&snapshot));
        Ok(snapshot)
    }

    fn commit_replacement_document(
        &mut self,
        path: PathBuf,
        snapshot: Arc<DocumentSnapshot>,
        cancel: &CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.documents.insert(path, Arc::clone(&snapshot));
        Ok(snapshot)
    }

    fn source_id_for(&self, path: &Path) -> SourceId {
        self.documents.get(path).map_or_else(
            || SourceId::new(self.next_source_id),
            |document| document.source().source_id(),
        )
    }

    fn commit_source_id(&mut self, path: &Path) {
        if !self.documents.contains_key(path) {
            self.next_source_id = self
                .next_source_id
                .checked_add(1)
                .expect("source id space exhausted");
        }
    }
}

impl<F: FileSystem> ServiceState<F> {
    pub fn completions_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        position: crate::source::Utf16Pos,
        cancel: &CancellationToken,
    ) -> Result<Vec<Completion>, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.completions(path, position)
    }

    pub fn definition_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        position: crate::source::Utf16Pos,
        cancel: &CancellationToken,
    ) -> Result<Option<Location>, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.definition(path, position)
    }

    pub fn references_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        position: crate::source::Utf16Pos,
        cancel: &CancellationToken,
    ) -> Result<Vec<Location>, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.references(path, position)
    }

    pub fn quick_info_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        position: crate::source::Utf16Pos,
        cancel: &CancellationToken,
    ) -> Result<Option<QuickInfo>, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.quick_info(path, position)
    }

    pub fn rename_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        position: crate::source::Utf16Pos,
        new_name: &str,
        cancel: &CancellationToken,
    ) -> Result<RenameResult, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.rename(path, position, new_name)
    }

    pub fn diagnostics_with_cancel(
        &mut self,
        path: impl AsRef<Path>,
        cancel: &CancellationToken,
    ) -> Result<Vec<DiagnosticEntry>, ServiceError> {
        let path = path.as_ref();
        self.ensure_document_with_cancel(path, cancel)?;
        cancel.check().map_err(|_| ServiceError::Cancelled)?;
        self.diagnostics(path)
    }
}
/// The document content a snapshot freezes: the text, its client version,
/// whether the document is open, and the disk metadata a closed document
/// was read under.
struct SnapshotContent {
    text: Arc<str>,
    version: u64,
    open: bool,
    disk_metadata: Option<FileMetadata>,
}

fn build_snapshot_with_cancel<F: FileSystem>(
    path: PathBuf,
    source_id: SourceId,
    content: SnapshotContent,
    cancel: &CancellationToken,
    resolution: Option<&ResolutionConfig>,
    filesystem: &F,
) -> Result<DocumentSnapshot, ServiceError> {
    cancel.check().map_err(|_| ServiceError::Cancelled)?;
    let SnapshotContent {
        text,
        version,
        open,
        disk_metadata,
    } = content;
    let declaration_file = is_declaration_file(&path);
    let source = Arc::new(SourceText::from_arc(text)?.with_declaration_file(declaration_file));
    let scanned = scanner::scan_with_cancel(source_id, script_kind(&path), source, cancel.clone())
        .map_err(|_| ServiceError::Cancelled)?;
    let parsed =
        parser::parse_with_cancel(scanned, cancel.clone()).map_err(|_| ServiceError::Cancelled)?;
    let semantic = checker::check_source_with_lints_with_cancel(
        parsed.product(),
        &LintTable::new(LintProfile::Default),
        cancel.clone(),
    )
    .map_err(|_| ServiceError::Cancelled)?;
    let mut diagnostics = semantic.diagnostics().to_vec();
    if let Some(config) = resolution {
        let host = ServiceResolutionHost { filesystem };
        diagnostics.extend(collect_resolution_diagnostics(
            parsed.product(),
            source_id,
            &path,
            config,
            &host,
        ));
    }
    let diagnostics = Arc::from(diagnostics);
    Ok(DocumentSnapshot {
        path,
        version,
        open,
        parsed: Arc::new(parsed),
        semantic: Arc::new(semantic),
        diagnostics,
        disk_metadata,
    })
}

fn is_declaration_file(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.ends_with(".d.ts") || name.ends_with(".d.mts") || name.ends_with(".d.cts")
}

fn script_kind(path: &Path) -> ScriptKind {
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("js" | "mjs" | "cjs") => ScriptKind::JavaScript,
        Some("jsx") => ScriptKind::JavaScriptReact,
        Some("tsx") => ScriptKind::TypeScriptReact,
        Some("json") => ScriptKind::Json,
        _ => ScriptKind::TypeScript,
    }
}

/// Cached workspace resolution context: the project root, compiler options
/// loaded from `tsconfig.json`, and the derived `(kind, mode)` strategy.
struct ResolutionConfig {
    root: ProjectRoot,
    options: CompilerOptions,
    kind: ModuleResolutionKind,
    mode: ResolutionMode,
}

/// Loads the resolution config for `root`. When `tsconfig.json` is present
/// its `compilerOptions` (including `moduleResolution`) are honored; when
/// absent the strategy falls back to `(Bundler, Import)`.
fn load_resolution_config<F: FileSystem>(filesystem: &F, root: &Path) -> Option<ResolutionConfig> {
    let project_root = ProjectRoot::new(root).ok()?;
    let config_path = root.join("tsconfig.json");
    let (options, kind) = match filesystem.read(&config_path) {
        Ok(source) => {
            let config = ProjectConfig::parse(&project_root, &config_path, &source).ok()?;
            let options = config.options().clone();
            let kind = ModuleResolutionKind::from_options(&options).ok()?;
            (options, kind)
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            let config = ProjectConfig::parse(&project_root, &config_path, "{}").ok()?;
            (config.options().clone(), ModuleResolutionKind::Bundler)
        }
        Err(_) => return None,
    };
    let mode = ambient_resolution_mode(&options);
    Some(ResolutionConfig {
        root: project_root,
        options,
        kind,
        mode,
    })
}

/// Derives the ambient resolution mode from the module format option.
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

/// Adapts the service's [`FileSystem`] to the resolver's [`ResolutionHost`].
struct ServiceResolutionHost<'a, F: FileSystem> {
    filesystem: &'a F,
}

impl<F: FileSystem> ResolutionHost for ServiceResolutionHost<'_, F> {
    fn file_exists(&self, path: &Path) -> bool {
        self.filesystem.metadata(path).is_ok()
    }

    fn directory_exists(&self, path: &Path) -> bool {
        self.filesystem.read_dir(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> Option<Arc<str>> {
        self.filesystem.read(path).ok().map(Arc::<str>::from)
    }
}

/// Walks top-level import/export statements, resolves relative specifiers
/// against the workspace root, and returns `TS2307` diagnostics for each
/// unresolvable module. Bare/package specifiers are skipped.
fn collect_resolution_diagnostics(
    source: &SourceFile,
    source_id: SourceId,
    importer: &Path,
    config: &ResolutionConfig,
    host: &dyn ResolutionHost,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut cache = ResolutionCache::new();
    for statement in source.statements() {
        for edge in literal_edges(source, statement.data()) {
            if !is_relative_specifier(&edge.specifier) {
                continue;
            }
            let resolved = if edge.type_only {
                resolve_type_reference(
                    &config.root,
                    &config.options,
                    importer,
                    &edge.specifier,
                    (config.kind, config.mode),
                    host,
                    &mut cache,
                )
            } else {
                resolve_module_name(
                    &config.root,
                    &config.options,
                    importer,
                    &edge.specifier,
                    (config.kind, config.mode),
                    host,
                    &mut cache,
                )
            };
            if resolved.is_err() {
                let message = by_u32(2307)
                    .and_then(|entry| entry.format(Args::new([edge.specifier.as_str()])).ok())
                    .map(Cow::Owned)
                    .unwrap_or(Cow::Borrowed(
                        "Cannot find module or its corresponding type declarations.",
                    ));
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::new("2307"),
                    source_id,
                    edge.range,
                    message,
                ));
            }
        }
    }
    diagnostics
}

/// One extracted literal import/export edge awaiting resolution.
struct LiteralEdge {
    specifier: String,
    range: TextRange,
    type_only: bool,
}

/// Extracts literal specifier text and range from top-level import/export
/// statements. Non-literal or malformed specifiers yield no edges.
fn literal_edges(source: &SourceFile, statement: &Statement) -> Vec<LiteralEdge> {
    let mut edges = Vec::new();
    match statement {
        Statement::Import(import) => {
            let type_only = import_is_type_only(import);
            push_edge(source, &mut edges, type_only, &import.source);
        }
        Statement::ImportEquals(import) => {
            if let ExternalModuleReference::Require(specifier) = &import.reference {
                push_edge(source, &mut edges, import.is_type_only, specifier);
            }
        }
        Statement::Export(ExportDeclaration::All(export)) => {
            push_edge(source, &mut edges, export.type_only, &export.source);
        }
        Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
            type_only,
            specifiers,
            source: Some(module),
            ..
        })) => {
            let only_types = *type_only
                || (!specifiers.is_empty()
                    && specifiers
                        .iter()
                        .all(|specifier| specifier.data().mode == ExportSpecifierMode::TypeOnly));
            push_edge(source, &mut edges, only_types, module);
        }
        _ => {}
    }
    edges
}

/// Extracts the literal specifier text and range from a string-literal node.
fn push_edge(
    source: &SourceFile,
    edges: &mut Vec<LiteralEdge>,
    type_only: bool,
    literal: &StringLiteralNode,
) {
    let Some(text) = source.token_text(literal.data().token()) else {
        return;
    };
    let Some(value) = crate::program::unquote(text) else {
        return;
    };
    let Ok(specifier) = value.to_utf8_strict() else {
        return;
    };
    edges.push(LiteralEdge {
        specifier,
        range: literal.range(),
        type_only,
    });
}

/// Returns `true` for relative specifiers (`./`, `../`, `/`, `.`, `..`).
fn is_relative_specifier(specifier: &str) -> bool {
    specifier.starts_with("./")
        || specifier.starts_with("../")
        || specifier.starts_with('/')
        || specifier == "."
        || specifier == ".."
}

/// Mirrors `program::import_is_type_only` for service-tier edge classification.
fn import_is_type_only(import: &crate::syntax::ImportDeclaration) -> bool {
    import.type_only || import_clause_is_type_only(import.clause.as_ref())
}

/// Mirrors `program::import_clause_is_type_only` for service-tier use.
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

#[cfg(test)]
mod tests {
    use std::{fs, path::Path, sync::Arc};

    use super::{
        CancellationToken, ServiceError, ServiceState, SnapshotContent, build_snapshot_with_cancel,
    };
    use crate::{service::filesystem::OsFileSystem, source::SourceId};

    fn state() -> (std::path::PathBuf, ServiceState<OsFileSystem>) {
        let root = crate::service::test_support::fresh_dir("bamts-service-state");
        let state = ServiceState::new(OsFileSystem::new(&root).expect("filesystem"));
        (root, state)
    }

    #[test]
    fn updates_replace_snapshots_and_reject_stale_versions() {
        let (root, mut state) = state();
        let first = state
            .open("a.ts", Arc::<str>::from("const a = 1;"), 1)
            .expect("open");
        let frozen = state.snapshot();
        let second = state
            .update("a.ts", Arc::<str>::from("const b = 2;"), 2)
            .expect("update");
        assert_eq!(first.source().source_id(), second.source().source_id());
        assert_eq!(
            frozen
                .documents()
                .next()
                .expect("frozen document")
                .version(),
            1
        );
        assert_eq!(
            state
                .snapshot()
                .documents()
                .next()
                .expect("current document")
                .version(),
            2
        );
        assert!(matches!(
            state.update("a.ts", Arc::<str>::from("const c = 3;"), 2),
            Err(ServiceError::VersionOutOfOrder { .. })
        ));
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn open_snapshot_precedes_disk_until_close() {
        let (root, mut state) = state();
        fs::write(root.join("a.ts"), "const disk = 1;").expect("write disk source");
        state
            .open("a.ts", Arc::<str>::from("const memory = 2;"), 1)
            .expect("open");
        let open = state
            .ensure_document(Path::new("a.ts"))
            .expect("open snapshot");
        assert!(open.source().source_text().as_str().contains("memory"));
        state.close("a.ts").expect("close");
        let closed = state
            .ensure_document(Path::new("a.ts"))
            .expect("disk snapshot");
        assert!(closed.source().source_text().as_str().contains("disk"));
        fs::remove_dir_all(root).expect("remove root");
    }
    #[test]
    fn pre_cancelled_open_does_not_mutate_state() {
        let (root, mut state) = state();
        let cancel = CancellationToken::new();
        cancel.cancel();

        assert!(matches!(
            state.open_with_cancel("a.ts", Arc::<str>::from("const value = 1;"), 1, &cancel,),
            Err(ServiceError::Cancelled)
        ));
        assert_eq!(state.snapshot().documents().count(), 0);
        assert_eq!(state.next_source_id, 0);
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn cancelled_commit_new_document_leaves_state_untouched() {
        let (root, mut state) = state();
        let snapshot = state
            .open("a.ts", Arc::<str>::from("const value = 1;"), 1)
            .expect("open");
        let before = state.snapshot();
        let next_source_id = state.next_source_id;
        let cancel = CancellationToken::new();
        cancel.cancel();

        assert!(matches!(
            state.commit_new_document(root.join("b.ts"), snapshot, &cancel),
            Err(ServiceError::Cancelled)
        ));
        let after = state.snapshot();
        assert_eq!(before.documents.len(), after.documents.len());
        for (path, document) in &before.documents {
            assert!(Arc::ptr_eq(
                document,
                after.documents.get(path).expect("document remains present")
            ));
        }
        assert_eq!(state.next_source_id, next_source_id);
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn cancelled_commit_replacement_document_leaves_state_untouched() {
        let (root, mut state) = state();
        let snapshot = state
            .open("a.ts", Arc::<str>::from("const value = 1;"), 1)
            .expect("open");
        let path = state
            .documents
            .keys()
            .next()
            .expect("open document")
            .clone();
        let before = state.snapshot();
        let next_source_id = state.next_source_id;
        let cancel = CancellationToken::new();
        cancel.cancel();

        assert!(matches!(
            state.commit_replacement_document(path, snapshot, &cancel),
            Err(ServiceError::Cancelled)
        ));
        let after = state.snapshot();
        assert_eq!(before.documents.len(), after.documents.len());
        for (path, document) in &before.documents {
            assert!(Arc::ptr_eq(
                document,
                after.documents.get(path).expect("document remains present")
            ));
        }
        assert_eq!(state.next_source_id, next_source_id);
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn build_snapshot_honors_pre_cancelled_token() {
        let cancel = CancellationToken::new();
        cancel.cancel();

        assert!(matches!(
            build_snapshot_with_cancel(
                std::path::PathBuf::from("a.ts"),
                SourceId::new(0),
                SnapshotContent {
                    text: Arc::<str>::from("const value = 1;"),
                    version: 1,
                    open: true,
                    disk_metadata: None,
                },
                &cancel,
                None,
                &OsFileSystem::new(std::env::temp_dir()).expect("temp filesystem"),
            ),
            Err(ServiceError::Cancelled)
        ));
    }

    fn resolution_state() -> (std::path::PathBuf, ServiceState<OsFileSystem>) {
        let (root, state) = state();
        let mut state = state;
        state.set_resolution_root(root.clone());
        (root, state)
    }

    fn has_2307(snapshot: &super::DocumentSnapshot) -> bool {
        snapshot
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code().as_str() == "2307")
    }

    #[test]
    fn unresolved_relative_import_surfaces_ts2307() {
        let (root, mut state) = resolution_state();
        let snapshot = state
            .open(
                "main.ts",
                Arc::<str>::from("import { x } from \"./missing.js\";\n"),
                1,
            )
            .expect("open");
        assert!(
            has_2307(&snapshot),
            "expected TS2307 for unresolvable ./missing.js, got {:?}",
            snapshot.diagnostics()
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn resolved_relative_import_produces_no_ts2307() {
        let (root, mut state) = resolution_state();
        fs::write(root.join("missing.ts"), "export const x = 1;\n").expect("write dependency");
        let snapshot = state
            .open(
                "main.ts",
                Arc::<str>::from("import { x } from \"./missing.js\";\n"),
                1,
            )
            .expect("open");
        assert!(
            !has_2307(&snapshot),
            "expected no TS2307 when ./missing.ts exists, got {:?}",
            snapshot.diagnostics()
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn no_resolution_root_means_no_ts2307() {
        let (root, mut state) = state();
        let snapshot = state
            .open(
                "main.ts",
                Arc::<str>::from("import { x } from \"./missing.js\";\n"),
                1,
            )
            .expect("open");
        assert!(
            !has_2307(&snapshot),
            "expected no TS2307 without resolution root, got {:?}",
            snapshot.diagnostics()
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn canonical_absolute_importer_surfaces_ts2307() {
        let (root, state) = state();
        let canonical = std::fs::canonicalize(&root).expect("canonical");
        std::fs::write(
            canonical.join("case.ts"),
            "import { x } from \"./missing.js\";\n",
        )
        .expect("seed");
        let mut state = state;
        state.set_resolution_root(canonical.clone());
        let path = canonical.join("case.ts");
        let snapshot = state
            .open(
                &path,
                Arc::<str>::from("import { x } from \"./missing.js\";\n"),
                1,
            )
            .expect("open");
        assert!(
            has_2307(&snapshot),
            "expected TS2307 with a canonical absolute importer, got {:?}",
            snapshot
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>()
        );
        fs::remove_dir_all(root).expect("remove root");
    }

    #[test]
    fn tsconfig_module_resolution_strategy_is_honored() {
        // NodeNext import mode requires explicit relative extensions, while
        // the no-tsconfig Bundler default allows the extensionless form.
        let (root, root_state) = state();
        let canonical = std::fs::canonicalize(&root).expect("canonical");
        fs::write(canonical.join("missing.ts"), "export const x = 1;\n").expect("dependency");
        fs::write(
            canonical.join("tsconfig.json"),
            r#"{"compilerOptions": {"moduleResolution": "nodenext"}}"#,
        )
        .expect("tsconfig");
        let mut nodenext_state = root_state;
        nodenext_state.set_resolution_root(canonical);
        let snapshot = nodenext_state
            .open(
                "main.ts",
                Arc::<str>::from("import { x } from \"./missing\";\n"),
                1,
            )
            .expect("open");
        assert!(
            has_2307(&snapshot),
            "nodenext must reject the extensionless relative import, got {:?}",
            snapshot
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>()
        );

        // The same workspace without a tsconfig uses the Bundler default,
        // where the identical extensionless import resolves.
        let (plain_root, mut plain_state) = state();
        fs::write(plain_root.join("missing.ts"), "export const x = 1;\n").expect("dependency");
        plain_state.set_resolution_root(plain_root.clone());
        let snapshot = plain_state
            .open(
                "main.ts",
                Arc::<str>::from("import { x } from \"./missing\";\n"),
                1,
            )
            .expect("open");
        assert!(
            !has_2307(&snapshot),
            "bundler default must resolve the extensionless relative import, got {:?}",
            snapshot
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>()
        );
        fs::remove_dir_all(root).expect("remove root");
        fs::remove_dir_all(plain_root).expect("remove plain root");
    }
}
