//! Full tsconfig JSONC parsing, option surface validation, project references,
//! and `extends` resolution with cycle and path-escape detection.
//!
//! This module layers on the canonical [`crate::project`] types (`ProjectConfig`,
//! `CompilerOptions`, `ProjectRoot`, `JsonValue`) so it does not introduce a
//! second project graph or options model.

use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::project::{
    CompilerOptions, ConfigError, JsonObject, JsonValue, PathError, ProjectConfig, ProjectRoot,
    parse_jsonc,
};
use crate::source::{SourceId, TextRange, Utf16Pos};
use std::{
    collections::BTreeSet,
    fmt,
    path::{Path, PathBuf},
    sync::Arc,
};

const CODE_JSONC: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-001");
const CODE_ROOT_NOT_OBJECT: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-002");
const CODE_INVALID_FIELD: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-003");
const CODE_PATH_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-004");
const CODE_PATH_NO_PARENT: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-005");
const CODE_EXTENDS_CYCLE: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-006");
const CODE_INVALID_EXTENDS: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-007");
const CODE_MISSING_EXTENDS: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-008");
const CODE_INVALID_REFERENCE: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-009");
const CODE_NESTING_TOO_DEEP: DiagnosticCode = DiagnosticCode::new("BAMTS-TSC-010");

/// A typed tsconfig diagnostic.
///
/// Each variant carries enough context to render an exact [`Diagnostic`] for a
/// given source file, and can be converted from the canonical project errors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TsConfigDiagnostic {
    Jsonc(crate::project::JsoncError),
    RootNotObject,
    InvalidField {
        field: Arc<str>,
        expected: &'static str,
    },
    PathEscape {
        root: PathBuf,
        path: PathBuf,
    },
    PathHasNoParent {
        path: PathBuf,
    },
    ExtendsCycle {
        path: Arc<str>,
    },
    InvalidExtends {
        specifier: Arc<str>,
        reason: &'static str,
    },
    MissingExtends {
        path: PathBuf,
    },
    InvalidReference {
        index: usize,
        reason: &'static str,
    },
    NestingTooDeep,
}

impl TsConfigDiagnostic {
    /// Renders this diagnostic as a compiler [`Diagnostic`] anchored at `source_id`.
    ///
    /// `source` is the original tsconfig text; it is used to turn the byte
    /// offsets from JSONC parse errors into UTF-16 source ranges.
    pub fn to_diagnostic(&self, source_id: SourceId, source: &str) -> Diagnostic {
        let zero = TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO)
            .ok()
            .unwrap_or_else(|| TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).ok().unwrap());

        match self {
            Self::Jsonc(error) => {
                let pos = Utf16Pos::new(utf16_offset(source, error.offset()));
                let range = TextRange::new(pos, pos).ok().unwrap_or(zero);
                Diagnostic::error(CODE_JSONC, source_id, range, "JSONC parse error")
                    .with_note(format!("{error}"))
            }
            Self::RootNotObject => Diagnostic::error(
                CODE_ROOT_NOT_OBJECT,
                source_id,
                zero,
                "tsconfig root must be an object",
            ),
            Self::InvalidField { field, expected } => Diagnostic::error(
                CODE_INVALID_FIELD,
                source_id,
                zero,
                "tsconfig field has an invalid type",
            )
            .with_note(format!("field {field:?} must be {expected}")),
            Self::PathEscape { root, path } => Diagnostic::error(
                CODE_PATH_ESCAPE,
                source_id,
                zero,
                "project path escapes the configured root",
            )
            .with_note(format!(
                "path {} escapes project root {}",
                path.display(),
                root.display()
            )),
            Self::PathHasNoParent { path } => Diagnostic::error(
                CODE_PATH_NO_PARENT,
                source_id,
                zero,
                "tsconfig path has no parent directory",
            )
            .with_note(format!("path: {}", path.display())),
            Self::ExtendsCycle { path } => Diagnostic::error(
                CODE_EXTENDS_CYCLE,
                source_id,
                zero,
                "tsconfig extends cycle detected",
            )
            .with_note(format!("revisited path: {}", path.as_ref())),
            Self::InvalidExtends { specifier, reason } => Diagnostic::error(
                CODE_INVALID_EXTENDS,
                source_id,
                zero,
                "invalid tsconfig extends",
            )
            .with_note(format!("extends {specifier:?}: {reason}")),
            Self::MissingExtends { path } => Diagnostic::error(
                CODE_MISSING_EXTENDS,
                source_id,
                zero,
                "could not load extended tsconfig",
            )
            .with_note(format!("resolved path: {}", path.display())),
            Self::InvalidReference { index, reason } => Diagnostic::error(
                CODE_INVALID_REFERENCE,
                source_id,
                zero,
                "invalid tsconfig project reference",
            )
            .with_note(format!("references[{index}]: {reason}")),
            Self::NestingTooDeep => Diagnostic::error(
                CODE_NESTING_TOO_DEEP,
                source_id,
                zero,
                "tsconfig extends nesting too deep",
            ),
        }
    }
}

impl fmt::Display for TsConfigDiagnostic {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Jsonc(error) => write!(formatter, "{error}"),
            Self::RootNotObject => formatter.write_str("tsconfig root must be an object"),
            Self::InvalidField { field, expected } => {
                write!(formatter, "tsconfig field {field:?} must be {expected}")
            }
            Self::PathEscape { root, path } => write!(
                formatter,
                "path {} escapes project root {}",
                path.display(),
                root.display()
            ),
            Self::PathHasNoParent { path } => {
                write!(formatter, "tsconfig path has no parent: {}", path.display())
            }
            Self::ExtendsCycle { path } => write!(formatter, "tsconfig extends cycle at {path}"),
            Self::InvalidExtends { specifier, reason } => {
                write!(formatter, "invalid extends {specifier:?}: {reason}")
            }
            Self::MissingExtends { path } => {
                write!(
                    formatter,
                    "could not load extended tsconfig: {}",
                    path.display()
                )
            }
            Self::InvalidReference { index, reason } => {
                write!(formatter, "references[{index}]: {reason}")
            }
            Self::NestingTooDeep => formatter.write_str("tsconfig extends nesting too deep"),
        }
    }
}

impl From<ConfigError> for TsConfigDiagnostic {
    fn from(error: ConfigError) -> Self {
        match error {
            ConfigError::Json(e) => Self::Jsonc(e),
            ConfigError::Path(e) => Self::from(e),
            ConfigError::RootMustBeObject => Self::RootNotObject,
            ConfigError::InvalidField { field, expected } => Self::InvalidField { field, expected },
        }
    }
}

impl From<PathError> for TsConfigDiagnostic {
    fn from(error: PathError) -> Self {
        match error {
            PathError::RootIsNotAbsolute { path } => Self::PathEscape {
                root: path.clone(),
                path,
            },
            PathError::PathEscapesRoot { root, path } => Self::PathEscape { root, path },
            PathError::PathHasNoParent { path } => Self::PathHasNoParent { path },
        }
    }
}

/// One or more tsconfig diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TsConfigError(Arc<[TsConfigDiagnostic]>);

impl TsConfigError {
    pub fn new(diagnostics: impl IntoIterator<Item = TsConfigDiagnostic>) -> Self {
        Self(Arc::from(diagnostics.into_iter().collect::<Vec<_>>()))
    }

    pub fn iter(&self) -> std::slice::Iter<'_, TsConfigDiagnostic> {
        self.0.iter()
    }
}

impl fmt::Display for TsConfigError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, diagnostic) in self.0.iter().enumerate() {
            if index > 0 {
                formatter.write_str("; ")?;
            }
            diagnostic.fmt(formatter)?;
        }
        Ok(())
    }
}

impl std::error::Error for TsConfigError {}

impl From<TsConfigDiagnostic> for TsConfigError {
    fn from(diagnostic: TsConfigDiagnostic) -> Self {
        Self::new([diagnostic])
    }
}

impl From<ConfigError> for TsConfigError {
    fn from(error: ConfigError) -> Self {
        Self::from(TsConfigDiagnostic::from(error))
    }
}

impl From<PathError> for TsConfigError {
    fn from(error: PathError) -> Self {
        Self::from(TsConfigDiagnostic::from(error))
    }
}

impl From<crate::project::JsoncError> for TsConfigError {
    fn from(error: crate::project::JsoncError) -> Self {
        Self::from(TsConfigDiagnostic::Jsonc(error))
    }
}

/// One project reference declared by `references` in `tsconfig.json`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectReference {
    original_path: Option<Arc<str>>,
    path: PathBuf,
    prepend: Option<bool>,
    circular: Option<bool>,
}

impl ProjectReference {
    #[must_use]
    pub fn original_path(&self) -> Option<&str> {
        self.original_path.as_deref()
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub const fn prepend(&self) -> Option<bool> {
        self.prepend
    }

    #[must_use]
    pub const fn circular(&self) -> Option<bool> {
        self.circular
    }
}

/// One resolved `extends` link.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedExtends {
    specifier: Arc<str>,
    path: PathBuf,
    source: Arc<str>,
}

impl ResolvedExtends {
    #[must_use]
    pub fn specifier(&self) -> &str {
        &self.specifier
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }
}

/// A parsed and confined tsconfig document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TsConfig {
    config: ProjectConfig,
    references: Arc<[ProjectReference]>,
}

impl TsConfig {
    /// Parses a single tsconfig source into the canonical project view plus
    /// project references.
    ///
    /// `extends` is *not* resolved here; use [`resolve_extends`] for that.
    pub fn parse(
        root: &ProjectRoot,
        config_path: impl AsRef<Path>,
        source: &str,
    ) -> Result<Self, TsConfigError> {
        let value = parse_jsonc(source)?;
        let raw = value
            .as_object()
            .ok_or(TsConfigDiagnostic::RootNotObject)?
            .clone();
        Self::parse_value(root, config_path, raw)
    }

    /// Parses one already-decoded tsconfig object.
    pub fn parse_value(
        root: &ProjectRoot,
        config_path: impl AsRef<Path>,
        raw: JsonObject,
    ) -> Result<Self, TsConfigError> {
        let config = ProjectConfig::parse_value(root, config_path, raw)?;
        let path = config.path().to_path_buf();
        let directory = path
            .parent()
            .ok_or_else(|| TsConfigDiagnostic::PathHasNoParent { path: path.clone() })?;
        let references = parse_references(config.raw(), root, directory)?;
        Ok(Self { config, references })
    }

    #[must_use]
    pub fn config(&self) -> &ProjectConfig {
        &self.config
    }

    #[must_use]
    pub fn references(&self) -> &[ProjectReference] {
        &self.references
    }

    #[must_use]
    pub fn options(&self) -> &CompilerOptions {
        self.config.options()
    }
}

fn parse_references(
    raw: &JsonObject,
    root: &ProjectRoot,
    directory: &Path,
) -> Result<Arc<[ProjectReference]>, TsConfigDiagnostic> {
    let Some(value) = raw.get("references") else {
        return Ok(Arc::from(Vec::<ProjectReference>::new()));
    };
    let entries = value
        .as_array()
        .ok_or(TsConfigDiagnostic::InvalidReference {
            index: 0,
            reason: "references must be an array of objects",
        })?;
    let mut references = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let object = entry
            .as_object()
            .ok_or(TsConfigDiagnostic::InvalidReference {
                index,
                reason: "reference must be an object",
            })?;
        let original = object.get("path").and_then(JsonValue::as_str).ok_or(
            TsConfigDiagnostic::InvalidReference {
                index,
                reason: "references[?].path must be a string",
            },
        )?;
        let path = root
            .resolve_from(directory, original)
            .map_err(TsConfigDiagnostic::from)?;
        let original_path = Some(Arc::from(original));
        let prepend =
            match object.get("prepend") {
                None => None,
                Some(value) => Some(value.as_bool().ok_or(
                    TsConfigDiagnostic::InvalidReference {
                        index,
                        reason: "references[?].prepend must be a boolean",
                    },
                )?),
            };
        let circular =
            match object.get("circular") {
                None => None,
                Some(value) => Some(value.as_bool().ok_or(
                    TsConfigDiagnostic::InvalidReference {
                        index,
                        reason: "references[?].circular must be a boolean",
                    },
                )?),
            };
        references.push(ProjectReference {
            original_path,
            path,
            prepend,
            circular,
        });
    }
    Ok(Arc::from(references))
}

/// Resolves the `extends` chain for one tsconfig source.
///
/// `load` is a pure, caller-supplied I/O function. It should return the source
/// text for an absolute, confined `tsconfig.json` path. Returning `None` for a
/// resolved path produces [`TsConfigDiagnostic::MissingExtends`].
///
/// Relative `extends` (`./base.json`, `../base.json`) and package-style
/// `extends` (`@scope/pkg` or `@scope/pkg/tsconfig.json`) are supported.
/// Cycles and paths that escape `root` are rejected.
pub fn resolve_extends(
    root: &ProjectRoot,
    config_path: impl AsRef<Path>,
    source: &str,
    load: &dyn Fn(&Path) -> Option<Arc<str>>,
    max_depth: usize,
) -> Result<Arc<[ResolvedExtends]>, TsConfigError> {
    let path = root
        .confine(config_path.as_ref())
        .map_err(TsConfigError::from)?;
    let directory = path.parent().ok_or_else(|| {
        TsConfigError::from(TsConfigDiagnostic::PathHasNoParent { path: path.clone() })
    })?;
    let value = parse_jsonc(source).map_err(TsConfigError::from)?;
    let raw = value.as_object().ok_or(TsConfigDiagnostic::RootNotObject)?;
    let mut visited = BTreeSet::<PathBuf>::new();
    let mut chain = Vec::new();
    visited.insert(path.clone());
    resolve_extends_one(
        root,
        directory,
        raw,
        load,
        &mut visited,
        &mut chain,
        max_depth,
    )?;
    Ok(Arc::from(chain))
}

fn resolve_extends_one(
    root: &ProjectRoot,
    current_dir: &Path,
    raw: &JsonObject,
    load: &dyn Fn(&Path) -> Option<Arc<str>>,
    visited: &mut BTreeSet<PathBuf>,
    chain: &mut Vec<ResolvedExtends>,
    remaining: usize,
) -> Result<(), TsConfigError> {
    if remaining == 0 {
        return Err(TsConfigDiagnostic::NestingTooDeep.into());
    }
    let Some(value) = raw.get("extends") else {
        return Ok(());
    };
    let specifiers: Vec<&str> = if let Some(specifier) = value.as_str() {
        vec![specifier]
    } else if let Some(values) = value.as_array() {
        values
            .iter()
            .map(|value| {
                value
                    .as_str()
                    .ok_or_else(|| TsConfigDiagnostic::InvalidExtends {
                        specifier: Arc::from(""),
                        reason: "extends array entries must be strings",
                    })
            })
            .collect::<Result<_, _>>()?
    } else {
        return Err(TsConfigDiagnostic::InvalidExtends {
            specifier: Arc::from(""),
            reason: "extends must be a string or an array of strings",
        }
        .into());
    };

    for specifier in specifiers {
        let (resolved, source) = load_extends(root, current_dir, specifier, load)?;
        if !visited.insert(resolved.clone()) {
            return Err(TsConfigDiagnostic::ExtendsCycle {
                path: Arc::from(resolved.to_string_lossy().as_ref()),
            }
            .into());
        }
        let value = parse_jsonc(&source).map_err(TsConfigError::from)?;
        let raw = value.as_object().ok_or(TsConfigDiagnostic::RootNotObject)?;
        chain.push(ResolvedExtends {
            specifier: Arc::from(specifier),
            path: resolved.clone(),
            source,
        });
        let next_dir = resolved
            .parent()
            .ok_or_else(|| TsConfigDiagnostic::PathHasNoParent {
                path: resolved.clone(),
            })?;
        resolve_extends_one(root, next_dir, raw, load, visited, chain, remaining - 1)?;
        visited.remove(&resolved);
    }
    Ok(())
}

fn load_extends(
    root: &ProjectRoot,
    current_dir: &Path,
    specifier: &str,
    load: &dyn Fn(&Path) -> Option<Arc<str>>,
) -> Result<(PathBuf, Arc<str>), TsConfigError> {
    let package = !specifier.starts_with("./")
        && !specifier.starts_with("../")
        && !Path::new(specifier).is_absolute();
    let mut directory = Some(current_dir);
    let mut first = None;
    while let Some(candidate_dir) = directory {
        let resolved = resolve_extends_specifier(root, candidate_dir, specifier)?;
        first.get_or_insert_with(|| resolved.clone());
        if let Some(source) = load(&resolved) {
            return Ok((resolved, source));
        }
        if !package || candidate_dir == root.path() {
            break;
        }
        directory = candidate_dir
            .parent()
            .filter(|parent| parent.starts_with(root.path()));
    }
    Err(TsConfigDiagnostic::MissingExtends {
        path: first.expect("at least one extends candidate"),
    }
    .into())
}

fn resolve_extends_specifier(
    root: &ProjectRoot,
    directory: &Path,
    specifier: &str,
) -> Result<PathBuf, TsConfigError> {
    let target: Arc<str> = if specifier.starts_with("./") || specifier.starts_with("../") {
        Arc::from(specifier)
    } else {
        Arc::from(package_extends_path(specifier))
    };
    root.resolve_from(directory, target.as_ref())
        .map_err(|e| TsConfigError::from(TsConfigDiagnostic::from(e)))
}

fn package_extends_path(specifier: &str) -> String {
    if specifier.ends_with(".json") {
        format!("node_modules/{specifier}")
    } else if specifier.starts_with('@') && specifier.matches('/').count() == 1 {
        format!("node_modules/{specifier}/tsconfig.json")
    } else if specifier.contains('/') {
        format!("node_modules/{specifier}.json")
    } else {
        format!("node_modules/{specifier}/tsconfig.json")
    }
}

fn utf16_offset(source: &str, byte: usize) -> usize {
    let mut u16_pos = 0;
    for (i, ch) in source.char_indices() {
        if i >= byte {
            break;
        }
        u16_pos += ch.len_utf16();
    }
    u16_pos
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::test_paths::abs;

    fn root() -> ProjectRoot {
        ProjectRoot::new(abs("/workspace")).unwrap()
    }

    #[test]
    fn minimal() {
        let cfg = TsConfig::parse(&root(), "tsconfig.json", "{}").unwrap();
        assert!(cfg.options().target().is_none());
        assert!(cfg.references().is_empty());
    }

    #[test]
    fn jsonc_comments_and_trailing_commas() {
        let source = r#"{
            // a comment
            "compilerOptions": {
                "strict": true,
            },
            /* block */
            "include": ["src"],
        }"#;
        let cfg = TsConfig::parse(&root(), "tsconfig.json", source).unwrap();
        assert!(cfg.options().strict());
        assert_eq!(cfg.config().include().len(), 1);
        assert_eq!(cfg.config().include()[0].as_ref(), "src");
    }

    #[test]
    fn files_include_exclude() {
        let source = r#"{
            "files": ["a.ts"],
            "include": ["src/**/*"],
            "exclude": ["node_modules", "**/*.test.ts"]
        }"#;
        let cfg = TsConfig::parse(&root(), "tsconfig.json", source).unwrap();
        assert_eq!(cfg.config().files().len(), 1);
        assert_eq!(cfg.config().include().len(), 1);
        assert_eq!(cfg.config().exclude().len(), 2);
    }

    #[test]
    fn references_valid() {
        let source = r#"{
            "references": [
                {"path": "packages/foo"},
                {"path": "packages/bar", "prepend": true, "circular": true}
            ]
        }"#;
        let cfg = TsConfig::parse(&root(), "tsconfig.json", source).unwrap();
        assert_eq!(cfg.references().len(), 2);
        assert_eq!(cfg.references()[0].original_path(), Some("packages/foo"));
        assert_eq!(
            cfg.references()[0].path(),
            abs("/workspace/packages/foo").as_path()
        );
        assert_eq!(cfg.references()[1].original_path(), Some("packages/bar"));
        assert_eq!(cfg.references()[1].prepend(), Some(true));
        assert_eq!(cfg.references()[1].circular(), Some(true));
    }

    #[test]
    fn reference_missing_path() {
        let source = r#"{"references": [{}]}"#;
        let err = TsConfig::parse(&root(), "tsconfig.json", source).unwrap_err();
        assert!(err.iter().any(|d| matches!(d, TsConfigDiagnostic::InvalidReference { reason, .. } if *reason == "references[?].path must be a string")));
    }

    #[test]
    fn reference_prepend_not_bool() {
        let source = r#"{"references": [{"path": "packages/foo", "prepend": ["x"]}]}"#;
        let err = TsConfig::parse(&root(), "tsconfig.json", source).unwrap_err();
        assert!(err.iter().any(|d| matches!(d, TsConfigDiagnostic::InvalidReference { reason, .. } if *reason == "references[?].prepend must be a boolean")));
    }

    #[test]
    fn invalid_compiler_options_type() {
        let source = r#"{"compilerOptions": "nope"}"#;
        let err = TsConfig::parse(&root(), "tsconfig.json", source).unwrap_err();
        assert!(err.iter().any(|d| matches!(d, TsConfigDiagnostic::InvalidField { field, .. } if field.as_ref() == "compilerOptions")));
    }

    #[test]
    fn relative_extends() {
        let source = r#"{"extends": "./base.json"}"#;
        let loader = |p: &Path| {
            if p == abs("/workspace/base.json").as_path() {
                Some(Arc::from(r#"{"compilerOptions": {"strict": true}}"#))
            } else {
                None
            }
        };
        let chain = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap();
        assert_eq!(chain.len(), 1);
        assert_eq!(chain[0].path(), abs("/workspace/base.json").as_path());
        assert_eq!(chain[0].specifier(), "./base.json");
    }

    #[test]
    fn package_extends() {
        let source = r#"{"extends": "@tsconfig/strict"}"#;
        let loader = |p: &Path| {
            if p == abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json").as_path() {
                Some(Arc::from(r#"{}"#))
            } else {
                None
            }
        };
        let chain = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap();
        assert_eq!(chain.len(), 1);
        assert_eq!(
            chain[0].path(),
            abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json").as_path()
        );
    }

    #[test]
    fn package_extends_with_subpath() {
        let source = r#"{"extends": "@tsconfig/strict/tsconfig.json"}"#;
        let loader = |p: &Path| {
            if p == abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json").as_path() {
                Some(Arc::from(r#"{}"#))
            } else {
                None
            }
        };
        let chain = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap();
        assert_eq!(chain.len(), 1);
        assert_eq!(
            chain[0].path(),
            abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json").as_path()
        );
    }

    #[test]
    fn extends_arrays_preserve_order_and_walk_ancestor_node_modules() {
        let source = r#"{"extends":["./base.json","@tsconfig/strict"]}"#;
        let loader = |path: &Path| {
            let known = [
                abs("/workspace/packages/app/base.json"),
                abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json"),
            ];
            known
                .iter()
                .any(|candidate| candidate == path)
                .then(|| Arc::from(r#"{}"#))
        };
        let chain = resolve_extends(
            &root(),
            abs("/workspace/packages/app/tsconfig.json"),
            source,
            &loader,
            8,
        )
        .unwrap();
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[0].specifier(), "./base.json");
        assert_eq!(chain[1].specifier(), "@tsconfig/strict");
        assert_eq!(
            chain[1].path(),
            abs("/workspace/node_modules/@tsconfig/strict/tsconfig.json").as_path()
        );
    }

    #[test]
    fn extends_array_rejects_non_string_entries() {
        let error = resolve_extends(
            &root(),
            "tsconfig.json",
            r#"{"extends":["./base.json",1]}"#,
            &|_| Some(Arc::from(r#"{}"#)),
            8,
        )
        .unwrap_err();
        assert!(error.iter().any(|diagnostic| matches!(
            diagnostic,
            TsConfigDiagnostic::InvalidExtends { reason, .. }
                if *reason == "extends array entries must be strings"
        )));
    }
    #[test]
    fn extends_cycle() {
        let source = r#"{"extends": "./a.json"}"#;
        let loader = |p: &Path| {
            if p == abs("/workspace/a.json").as_path() {
                Some(Arc::from(r#"{"extends": "./b.json"}"#))
            } else if p == abs("/workspace/b.json").as_path() {
                Some(Arc::from(r#"{"extends": "./a.json"}"#))
            } else {
                None
            }
        };
        let err = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap_err();
        assert!(
            err.iter()
                .any(|d| matches!(d, TsConfigDiagnostic::ExtendsCycle { .. }))
        );
    }

    #[test]
    fn extends_path_escape() {
        let source = r#"{"extends": "../base.json"}"#;
        let loader = |_p: &Path| Some(Arc::from(r#"{}"#));
        let err = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap_err();
        assert!(
            err.iter()
                .any(|d| matches!(d, TsConfigDiagnostic::PathEscape { .. }))
        );
    }

    #[test]
    fn missing_extends() {
        let source = r#"{"extends": "./missing.json"}"#;
        let loader = |_p: &Path| None;
        let err = resolve_extends(&root(), "tsconfig.json", source, &loader, 8).unwrap_err();
        assert!(
            err.iter()
                .any(|d| matches!(d, TsConfigDiagnostic::MissingExtends { .. }))
        );
    }
}
