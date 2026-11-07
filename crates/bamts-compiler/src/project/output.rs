//! Pure, deterministic source-to-output path planning.
//!
//! This module performs no filesystem access. Paths are normalized lexically and every
//! source, configured directory, and planned artifact is confined to the project root.

use std::{
    collections::BTreeMap,
    ffi::OsStr,
    fmt,
    path::{Component, Path, PathBuf},
};

/// The kind of file produced by one source.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArtifactKind {
    JavaScript,
    Declaration,
    SourceMap,
    DeclarationMap,
}

/// Selects which siblings are included in an output plan.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ArtifactSelection {
    pub javascript: bool,
    pub declaration: bool,
    pub source_map: bool,
    pub declaration_map: bool,
}

/// Inputs to pure output-path planning.
#[derive(Clone, Copy, Debug)]
pub struct PlanRequest<'a> {
    /// Absolute lexical boundary for every input, configured directory, and output.
    pub project_root: &'a Path,
    /// Source paths, absolute or relative to `project_root`.
    pub sources: &'a [PathBuf],
    /// Explicit common source directory. Relative paths are resolved from `project_root`.
    pub root_dir: Option<&'a Path>,
    /// JavaScript output directory. Without it, JavaScript is emitted beside each source.
    pub out_dir: Option<&'a Path>,
    /// Declaration output directory. It falls back to `out_dir`, then the source directory.
    pub declaration_dir: Option<&'a Path>,
    /// Whether `.tsx` preserves JSX as `.jsx`; otherwise it maps to `.js`.
    pub jsx_preserve: bool,
    pub artifacts: ArtifactSelection,
}

/// One source-to-destination assignment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedArtifact {
    pub source: PathBuf,
    pub path: PathBuf,
    pub kind: ArtifactKind,
}

/// A complete output plan, ordered by normalized destination path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OutputPlan {
    pub project_root: PathBuf,
    pub common_source_dir: PathBuf,
    pub artifacts: BTreeMap<PathBuf, PlannedArtifact>,
}

/// A deterministic output-planning failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutputMapError {
    RootNotAbsolute {
        root: PathBuf,
    },
    NoSources,
    OutsideRoot {
        path: PathBuf,
        root: PathBuf,
    },
    RootDirViolation {
        source: PathBuf,
        root_dir: PathBuf,
    },
    MissingFileName {
        path: PathBuf,
    },
    UnsupportedSourceExtension {
        source: PathBuf,
    },
    DuplicateSource {
        source: PathBuf,
    },
    ClobbersInput {
        path: PathBuf,
        source: PathBuf,
    },
    Collision {
        path: PathBuf,
        first_source: PathBuf,
        first_kind: ArtifactKind,
        second_source: PathBuf,
        second_kind: ArtifactKind,
    },
}

impl fmt::Display for OutputMapError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RootNotAbsolute { root } => {
                write!(
                    formatter,
                    "project root must be absolute: {}",
                    root.display()
                )
            }
            Self::NoSources => formatter.write_str("at least one source is required"),
            Self::OutsideRoot { path, root } => write!(
                formatter,
                "path {} escapes project root {}",
                path.display(),
                root.display()
            ),
            Self::RootDirViolation { source, root_dir } => write!(
                formatter,
                "source {} is not under rootDir {}",
                source.display(),
                root_dir.display()
            ),
            Self::MissingFileName { path } => {
                write!(formatter, "path does not name a file: {}", path.display())
            }
            Self::UnsupportedSourceExtension { source } => {
                write!(
                    formatter,
                    "unsupported source extension: {}",
                    source.display()
                )
            }
            Self::DuplicateSource { source } => {
                write!(formatter, "duplicate source: {}", source.display())
            }
            Self::ClobbersInput { path, source } => write!(
                formatter,
                "output {} would overwrite input {}",
                path.display(),
                source.display()
            ),
            Self::Collision {
                path,
                first_source,
                first_kind,
                second_source,
                second_kind,
            } => write!(
                formatter,
                "output collision at {} between {:?} from {} and {:?} from {}",
                path.display(),
                first_kind,
                first_source.display(),
                second_kind,
                second_source.display()
            ),
        }
    }
}

impl std::error::Error for OutputMapError {}

/// Maps one source set to a confined, collision-free, stable output plan.
pub fn map_output_paths(request: PlanRequest<'_>) -> Result<OutputPlan, OutputMapError> {
    let root =
        normalize_lexically(request.project_root).ok_or_else(|| OutputMapError::OutsideRoot {
            path: request.project_root.to_path_buf(),
            root: request.project_root.to_path_buf(),
        })?;
    if !root.is_absolute() {
        return Err(OutputMapError::RootNotAbsolute {
            root: request.project_root.to_path_buf(),
        });
    }
    if request.sources.is_empty() {
        return Err(OutputMapError::NoSources);
    }

    let mut sources = Vec::with_capacity(request.sources.len());
    for source in request.sources {
        sources.push(resolve_confined(&root, source)?);
    }
    sources.sort();
    for pair in sources.windows(2) {
        if pair[0] == pair[1] {
            return Err(OutputMapError::DuplicateSource {
                source: pair[0].clone(),
            });
        }
    }

    let explicit_root_dir = request
        .root_dir
        .map(|path| resolve_confined(&root, path))
        .transpose()?;
    let common_source_dir = match explicit_root_dir {
        Some(root_dir) => {
            if let Some(source) = sources
                .iter()
                .filter(|source| !is_declaration_source(source))
                .find(|source| !source.starts_with(&root_dir))
            {
                return Err(OutputMapError::RootDirViolation {
                    source: source.clone(),
                    root_dir,
                });
            }
            root_dir
        }
        None => derive_common_source_dir(&sources, &root)?,
    };

    let out_dir = request
        .out_dir
        .map(|path| resolve_confined(&root, path))
        .transpose()?;
    let declaration_dir = request
        .declaration_dir
        .map(|path| resolve_confined(&root, path))
        .transpose()?;

    let input_keys: BTreeMap<String, PathBuf> = sources
        .iter()
        .map(|source| (case_key(source), source.clone()))
        .collect();
    let mut destinations: BTreeMap<String, PlannedArtifact> = BTreeMap::new();

    for source in sources
        .iter()
        .filter(|source| !is_declaration_source(source))
    {
        let relative = source.strip_prefix(&common_source_dir).map_err(|_| {
            OutputMapError::RootDirViolation {
                source: source.clone(),
                root_dir: common_source_dir.clone(),
            }
        })?;
        let relative_parent = relative.parent().unwrap_or_else(|| Path::new(""));
        let javascript_name = javascript_file_name(source, request.jsx_preserve)?;
        let javascript = match &out_dir {
            Some(directory) => directory.join(relative_parent).join(javascript_name),
            None => source.with_file_name(javascript_name),
        };
        let javascript = require_confined_output(&root, javascript)?;

        if request.artifacts.javascript {
            insert_artifact(
                &mut destinations,
                &input_keys,
                source,
                javascript.clone(),
                ArtifactKind::JavaScript,
            )?;
            if request.artifacts.source_map {
                insert_artifact(
                    &mut destinations,
                    &input_keys,
                    source,
                    append_suffix(&javascript, ".map")?,
                    ArtifactKind::SourceMap,
                )?;
            }
        }

        if request.artifacts.declaration {
            let declaration_base = match declaration_dir.as_ref().or(out_dir.as_ref()) {
                Some(directory) => {
                    directory
                        .join(relative_parent)
                        .join(javascript.file_name().ok_or_else(|| {
                            OutputMapError::MissingFileName {
                                path: javascript.clone(),
                            }
                        })?)
                }
                None => javascript.clone(),
            };
            let declaration = declaration_path(&declaration_base);
            insert_artifact(
                &mut destinations,
                &input_keys,
                source,
                declaration.clone(),
                ArtifactKind::Declaration,
            )?;
            if request.artifacts.declaration_map {
                insert_artifact(
                    &mut destinations,
                    &input_keys,
                    source,
                    append_suffix(&declaration, ".map")?,
                    ArtifactKind::DeclarationMap,
                )?;
            }
        }
    }

    let artifacts = destinations
        .into_values()
        .map(|artifact| (artifact.path.clone(), artifact))
        .collect();
    Ok(OutputPlan {
        project_root: root,
        common_source_dir,
        artifacts,
    })
}

fn derive_common_source_dir(
    sources: &[PathBuf],
    project_root: &Path,
) -> Result<PathBuf, OutputMapError> {
    let mut runtime_sources = sources
        .iter()
        .filter(|source| !is_declaration_source(source));
    let Some(first) = runtime_sources.next() else {
        return Ok(project_root.to_path_buf());
    };
    let mut common = first
        .parent()
        .ok_or_else(|| OutputMapError::MissingFileName {
            path: first.clone(),
        })?
        .to_path_buf();
    for source in runtime_sources {
        while !source.starts_with(&common) {
            if !common.pop() || !common.starts_with(project_root) {
                return Ok(project_root.to_path_buf());
            }
        }
    }
    Ok(common)
}

fn resolve_confined(root: &Path, path: &Path) -> Result<PathBuf, OutputMapError> {
    let candidate = if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    };
    let normalized =
        normalize_lexically(&candidate).ok_or_else(|| OutputMapError::OutsideRoot {
            path: path.to_path_buf(),
            root: root.to_path_buf(),
        })?;
    if normalized.starts_with(root) {
        Ok(normalized)
    } else {
        Err(OutputMapError::OutsideRoot {
            path: normalized,
            root: root.to_path_buf(),
        })
    }
}

fn require_confined_output(root: &Path, path: PathBuf) -> Result<PathBuf, OutputMapError> {
    let normalized = normalize_lexically(&path).ok_or_else(|| OutputMapError::OutsideRoot {
        path: path.clone(),
        root: root.to_path_buf(),
    })?;
    if normalized.starts_with(root) {
        Ok(normalized)
    } else {
        Err(OutputMapError::OutsideRoot {
            path: normalized,
            root: root.to_path_buf(),
        })
    }
}

fn insert_artifact(
    destinations: &mut BTreeMap<String, PlannedArtifact>,
    inputs: &BTreeMap<String, PathBuf>,
    source: &Path,
    path: PathBuf,
    kind: ArtifactKind,
) -> Result<(), OutputMapError> {
    let key = case_key(&path);
    if let Some(input) = inputs.get(&key) {
        return Err(OutputMapError::ClobbersInput {
            path,
            source: input.clone(),
        });
    }
    if let Some(first) = destinations.get(&key) {
        return Err(OutputMapError::Collision {
            path,
            first_source: first.source.clone(),
            first_kind: first.kind,
            second_source: source.to_path_buf(),
            second_kind: kind,
        });
    }
    destinations.insert(
        key,
        PlannedArtifact {
            source: source.to_path_buf(),
            path,
            kind,
        },
    );
    Ok(())
}

fn javascript_file_name(source: &Path, jsx_preserve: bool) -> Result<PathBuf, OutputMapError> {
    let name = source
        .file_name()
        .ok_or_else(|| OutputMapError::MissingFileName {
            path: source.to_path_buf(),
        })?;
    let extension = source
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase);
    let output_extension = match extension.as_deref() {
        Some("ts") => "js",
        Some("tsx") if jsx_preserve => "jsx",
        Some("tsx") => "js",
        Some("mts" | "mjs") => "mjs",
        Some("cts" | "cjs") => "cjs",
        Some("js") => "js",
        Some("jsx") => "jsx",
        _ => {
            return Err(OutputMapError::UnsupportedSourceExtension {
                source: source.to_path_buf(),
            });
        }
    };
    let mut output = PathBuf::from(name);
    output.set_extension(output_extension);
    Ok(output)
}

fn declaration_path(javascript: &Path) -> PathBuf {
    match javascript
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase)
        .as_deref()
    {
        Some("mjs") => javascript.with_extension("d.mts"),
        Some("cjs") => javascript.with_extension("d.cts"),
        _ => javascript.with_extension("d.ts"),
    }
}

fn append_suffix(path: &Path, suffix: &str) -> Result<PathBuf, OutputMapError> {
    let name = path
        .file_name()
        .ok_or_else(|| OutputMapError::MissingFileName {
            path: path.to_path_buf(),
        })?;
    let mut suffixed = name.to_os_string();
    suffixed.push(suffix);
    Ok(path.with_file_name(suffixed))
}

fn is_declaration_source(path: &Path) -> bool {
    let name = path
        .file_name()
        .and_then(OsStr::to_str)
        .unwrap_or_default()
        .to_ascii_lowercase();
    name.ends_with(".d.ts") || name.ends_with(".d.mts") || name.ends_with(".d.cts")
}

fn case_key(path: &Path) -> String {
    path.to_string_lossy().to_lowercase()
}

pub(super) fn normalize_lexically(path: &Path) -> Option<PathBuf> {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    return None;
                }
            }
            Component::Normal(part) => normalized.push(part),
        }
    }
    Some(normalized)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::test_paths::abs;
    use std::sync::OnceLock;

    fn project_root() -> &'static Path {
        static ROOT: OnceLock<PathBuf> = OnceLock::new();
        ROOT.get_or_init(|| abs("/project")).as_path()
    }

    fn request<'a>(sources: &'a [PathBuf]) -> PlanRequest<'a> {
        PlanRequest {
            project_root: project_root(),
            sources,
            root_dir: None,
            out_dir: Some(Path::new("out")),
            declaration_dir: None,
            jsx_preserve: false,
            artifacts: ArtifactSelection {
                javascript: true,
                declaration: false,
                source_map: false,
                declaration_map: false,
            },
        }
    }

    fn paths(plan: &OutputPlan) -> Vec<(PathBuf, ArtifactKind)> {
        plan.artifacts
            .values()
            .map(|artifact| (artifact.path.clone(), artifact.kind))
            .collect()
    }

    #[test]
    fn rejects_source_outside_explicit_root_dir() {
        let sources = vec![PathBuf::from("src/a.ts"), PathBuf::from("shared/b.ts")];
        let mut request = request(&sources);
        request.root_dir = Some(Path::new("src"));
        assert_eq!(
            map_output_paths(request),
            Err(OutputMapError::RootDirViolation {
                source: abs("/project/shared/b.ts"),
                root_dir: abs("/project/src"),
            })
        );
    }

    #[test]
    fn derives_common_source_directory() {
        let sources = vec![
            PathBuf::from("src/a.ts"),
            PathBuf::from("src/deep/b.ts"),
            PathBuf::from("types/outside.d.ts"),
        ];
        let plan = map_output_paths(request(&sources)).unwrap();
        assert_eq!(plan.common_source_dir, abs("/project/src").as_path());
        assert_eq!(
            paths(&plan),
            vec![
                (abs("/project/out/a.js"), ArtifactKind::JavaScript),
                (abs("/project/out/deep/b.js"), ArtifactKind::JavaScript,),
            ]
        );
    }

    #[test]
    fn maps_mixed_source_extensions() {
        let sources = [
            "a.ts", "b.tsx", "c.mts", "d.cts", "e.js", "f.jsx", "g.mjs", "h.cjs",
        ]
        .into_iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>();
        let plan = map_output_paths(request(&sources)).unwrap();
        let actual = plan
            .artifacts
            .keys()
            .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert_eq!(
            actual,
            [
                "a.js", "b.js", "c.mjs", "d.cjs", "e.js", "f.jsx", "g.mjs", "h.cjs"
            ]
        );

        let mut preserve_request = request(&sources);
        preserve_request.jsx_preserve = true;
        let preserve = map_output_paths(preserve_request).unwrap();
        assert!(
            preserve
                .artifacts
                .contains_key(abs("/project/out/b.jsx").as_path())
        );
    }

    #[test]
    fn plans_declaration_and_map_combinations() {
        let sources = vec![PathBuf::from("src/a.mts")];
        for (selection, expected) in [
            (
                ArtifactSelection {
                    javascript: true,
                    declaration: false,
                    source_map: true,
                    declaration_map: true,
                },
                vec!["a.mjs", "a.mjs.map"],
            ),
            (
                ArtifactSelection {
                    javascript: false,
                    declaration: true,
                    source_map: true,
                    declaration_map: true,
                },
                vec!["a.d.mts", "a.d.mts.map"],
            ),
            (
                ArtifactSelection {
                    javascript: true,
                    declaration: true,
                    source_map: true,
                    declaration_map: true,
                },
                vec!["a.d.mts", "a.d.mts.map", "a.mjs", "a.mjs.map"],
            ),
        ] {
            let mut request = request(&sources);
            request.artifacts = selection;
            let plan = map_output_paths(request).unwrap();
            let actual = plan
                .artifacts
                .keys()
                .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
        }

        let mut routed = request(&sources);
        routed.declaration_dir = Some(Path::new("types"));
        routed.artifacts = ArtifactSelection {
            javascript: true,
            declaration: true,
            source_map: false,
            declaration_map: true,
        };
        let routed = map_output_paths(routed).unwrap();
        assert!(
            routed
                .artifacts
                .contains_key(abs("/project/out/a.mjs").as_path())
        );
        assert!(
            routed
                .artifacts
                .contains_key(abs("/project/types/a.d.mts").as_path())
        );
        assert!(
            routed
                .artifacts
                .contains_key(abs("/project/types/a.d.mts.map").as_path())
        );
    }

    #[test]
    fn detects_canonical_and_case_collisions() {
        let canonical = vec![PathBuf::from("a.ts"), PathBuf::from("a.js")];
        assert!(matches!(
            map_output_paths(request(&canonical)),
            Err(OutputMapError::Collision { .. })
        ));

        let case = vec![PathBuf::from("A.ts"), PathBuf::from("a.ts")];
        assert!(matches!(
            map_output_paths(request(&case)),
            Err(OutputMapError::Collision { .. })
        ));
    }

    #[test]
    fn rejects_output_that_clobbers_an_input() {
        let sources = vec![PathBuf::from("src/a.ts"), PathBuf::from("out/src/a.js")];
        assert_eq!(
            map_output_paths(request(&sources)),
            Err(OutputMapError::ClobbersInput {
                path: abs("/project/out/src/a.js"),
                source: abs("/project/out/src/a.js"),
            })
        );
    }

    #[test]
    fn rejects_source_and_output_traversal() {
        let escaped_source = vec![PathBuf::from("../outside.ts")];
        assert!(matches!(
            map_output_paths(request(&escaped_source)),
            Err(OutputMapError::OutsideRoot { .. })
        ));

        let sources = vec![PathBuf::from("src/a.ts")];
        let mut escaped_output = request(&sources);
        escaped_output.out_dir = Some(Path::new("../outside"));
        assert!(matches!(
            map_output_paths(escaped_output),
            Err(OutputMapError::OutsideRoot { .. })
        ));
    }

    #[test]
    fn input_order_does_not_change_plan_or_error() {
        let forward = vec![PathBuf::from("src/a.ts"), PathBuf::from("src/deep/b.cts")];
        let reverse = vec![PathBuf::from("src/deep/b.cts"), PathBuf::from("src/a.ts")];
        assert_eq!(
            map_output_paths(request(&forward)),
            map_output_paths(request(&reverse))
        );

        let colliding_forward = vec![PathBuf::from("a.ts"), PathBuf::from("a.js")];
        let colliding_reverse = vec![PathBuf::from("a.js"), PathBuf::from("a.ts")];
        assert_eq!(
            map_output_paths(request(&colliding_forward)),
            map_output_paths(request(&colliding_reverse))
        );
    }
}
