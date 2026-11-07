use crate::project::tsconfig::{ProjectReference, TsConfig};
use crate::project::{JsonObject, PathError, ProjectConfig, ProjectRoot};

use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Path, PathBuf},
    sync::Arc,
};

/// A failure while building or validating a project-reference graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReferenceError {
    /// The project config path has no parent directory to resolve relative
    /// reference paths from.
    MissingConfigParent { path: PathBuf },
    /// A reference path resolved outside the project root.
    InvalidPath { source: PathError },
    /// A project-reference graph contains a cycle.
    ///
    /// `sequence` begins and ends with the same project, listing the cycle in
    /// order of the references that form it.
    Cycle { sequence: Vec<PathBuf> },
    /// `composite` is `true` but `declaration` is explicitly `false`.
    CompositeNeedsDeclaration { project: PathBuf },
    /// `composite` is `true` but `incremental` is explicitly `false`.
    CompositeNeedsIncremental { project: PathBuf },
    /// A non-solution project references a project that does not have
    /// `composite` enabled.
    ReferencedNotComposite {
        from: PathBuf,
        to: PathBuf,
        reference: Arc<str>,
    },
    /// A non-solution project references a project that disables emit.
    ReferencedNoEmit {
        from: PathBuf,
        to: PathBuf,
        reference: Arc<str>,
    },
    /// Two projects in the reference graph would write the same build-info
    /// file.
    BuildInfoCollision {
        first: PathBuf,
        second: PathBuf,
        build_info: PathBuf,
    },
}

impl fmt::Display for ReferenceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingConfigParent { path } => {
                write!(
                    formatter,
                    "project config has no parent: {}",
                    path.display()
                )
            }
            Self::InvalidPath { source } => source.fmt(formatter),
            Self::Cycle { sequence } => {
                let joined: Vec<String> =
                    sequence.iter().map(|p| p.display().to_string()).collect();
                write!(
                    formatter,
                    "project references may not form a cycle: {}",
                    joined.join(" -> ")
                )
            }
            Self::CompositeNeedsDeclaration { project } => {
                write!(
                    formatter,
                    "composite project {} may not disable declaration emit",
                    project.display()
                )
            }
            Self::CompositeNeedsIncremental { project } => {
                write!(
                    formatter,
                    "composite project {} may not disable incremental compilation",
                    project.display()
                )
            }
            Self::ReferencedNotComposite {
                from,
                to,
                reference,
            } => {
                write!(
                    formatter,
                    "project {} references {} (\"{reference}\") which is not composite",
                    from.display(),
                    to.display()
                )
            }
            Self::ReferencedNoEmit {
                from,
                to,
                reference,
            } => {
                write!(
                    formatter,
                    "project {} references {} (\"{reference}\") which disables emit",
                    from.display(),
                    to.display()
                )
            }
            Self::BuildInfoCollision {
                first,
                second,
                build_info,
            } => {
                write!(
                    formatter,
                    "projects {} and {} would both write build-info {}",
                    first.display(),
                    second.display(),
                    build_info.display()
                )
            }
        }
    }
}

impl std::error::Error for ReferenceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidPath { source } => Some(source),
            _ => None,
        }
    }
}

impl From<PathError> for ReferenceError {
    fn from(source: PathError) -> Self {
        Self::InvalidPath { source }
    }
}

/// A content-addressed, deterministic 32-byte digest for a `.tsbuildinfo` file.
///
/// The digest is a SHA-256 hash over a canonical sorted encoding of the
/// project's build inputs, not a full content hash of the emitted build-info
/// file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BuildInfoIdentity([u8; 32]);

impl BuildInfoIdentity {
    #[must_use]
    pub const fn value(&self) -> &[u8; 32] {
        &self.0
    }

    /// Renders the 32-byte digest as a 64-character lowercase hexadecimal
    /// string.
    #[must_use]
    pub fn to_hex(&self) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::with_capacity(64);
        for byte in &self.0 {
            out.push(HEX[usize::from(byte >> 4)] as char);
            out.push(HEX[usize::from(byte & 0x0f)] as char);
        }
        out
    }
}

impl fmt::Display for BuildInfoIdentity {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.to_hex())
    }
}

/// One canonical project-reference edge.
///
/// This wraps the `tsconfig::ProjectReference` and canonicalizes the `path`
/// field to an actual `tsconfig.json` config file path, so every downstream
/// consumer (topological order, build engine, identity) works with the same
/// key space as the graph nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceEdge {
    /// Canonical, absolute path to the referenced project's config file.
    path: PathBuf,
    /// The original `path` string written in `references`.
    original_path: Option<Arc<str>>,
    /// The optional `prepend` annotation from the `references` entry.
    prepend: Option<bool>,
    /// The optional `circular` annotation from the `references` entry.
    circular: Option<bool>,
}

impl ReferenceEdge {
    fn from_tsconfig(reference: &ProjectReference) -> Self {
        Self {
            path: resolve_config_file_name(reference.path().to_path_buf()),
            original_path: reference.original_path().map(Arc::from),
            prepend: reference.prepend(),
            circular: reference.circular(),
        }
    }

    /// Canonical, absolute path to the referenced project's config file.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The original `path` string written in `references`, if any.
    #[must_use]
    pub fn original_path(&self) -> Option<&str> {
        self.original_path.as_deref()
    }

    /// The optional `prepend` annotation.
    #[must_use]
    pub const fn prepend(&self) -> Option<bool> {
        self.prepend
    }

    /// The optional `circular` annotation.
    #[must_use]
    pub const fn circular(&self) -> Option<bool> {
        self.circular
    }
}

/// A node in the canonical project-reference graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceNode {
    /// Absolute, normalized path to this project's config file.
    pub path: PathBuf,
    /// Resolved, canonicalized references declared by this project.
    pub references: Arc<[ReferenceEdge]>,
    /// File list entries from the config, sorted for deterministic hashing.
    pub files: Arc<[PathBuf]>,
    /// Include patterns from the config, sorted for deterministic hashing.
    pub include: Arc<[Arc<str>]>,
    /// Exclude patterns from the config.
    pub exclude: Arc<[Arc<str>]>,
    /// `compilerOptions.composite` was explicitly `true`.
    pub composite: bool,
    /// `compilerOptions.incremental` as written in the config, if present.
    pub incremental: Option<bool>,
    /// `compilerOptions.declaration` as written in the config, if present.
    pub declaration: Option<bool>,
    /// `compilerOptions.noEmit` was explicitly `true`.
    pub no_emit: bool,
    /// Canonical absolute path of the `.tsbuildinfo` file, if any.
    pub build_info_path: Option<PathBuf>,
}

impl ReferenceNode {
    /// Whether this project is treated as incremental (explicit `incremental`
    /// or `composite` implied).
    #[must_use]
    pub fn is_incremental(&self) -> bool {
        self.incremental.unwrap_or(false) || self.composite
    }

    /// Whether this project has any declared source files.
    #[must_use]
    pub fn has_sources(&self) -> bool {
        !self.files.is_empty() || !self.include.is_empty()
    }
}

/// A canonical, acyclic (when validated) project-reference graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceGraph {
    nodes: BTreeMap<PathBuf, ReferenceNode>,
}

impl ReferenceGraph {
    /// Builds a project-reference graph from already-parsed `TsConfig` values.
    ///
    /// `root` is used only to resolve the canonical `.tsbuildinfo` path.  The
    /// graph does not perform any file-system reads; it works from the parsed
    /// tsconfig metadata only.
    pub fn from_tsconfigs(
        root: &ProjectRoot,
        configs: &[&TsConfig],
    ) -> Result<Self, ReferenceError> {
        let mut nodes = BTreeMap::new();

        for tsconfig in configs {
            let config = tsconfig.config();
            let path = config.path().to_path_buf();
            let dir = config
                .path()
                .parent()
                .ok_or_else(|| ReferenceError::MissingConfigParent { path: path.clone() })?;

            let mut references: Vec<ReferenceEdge> = tsconfig
                .references()
                .iter()
                .map(ReferenceEdge::from_tsconfig)
                .collect();
            sort_references(&mut references);
            let references: Arc<[ReferenceEdge]> = references.into();

            let compiler = compiler_options_raw(config);
            let composite = raw_bool(compiler, "composite").unwrap_or(false);
            let incremental = raw_bool(compiler, "incremental");
            let declaration = raw_bool(compiler, "declaration");
            let no_emit = raw_bool(compiler, "noEmit").unwrap_or(false);

            let build_info_path =
                compute_build_info_path(root, config, dir, composite, incremental)?;

            let mut files: Vec<PathBuf> = config.files().to_vec();
            files.sort();

            let mut include: Vec<Arc<str>> = config.include().to_vec();
            include.sort();

            let mut exclude: Vec<Arc<str>> = config.exclude().to_vec();
            exclude.sort();

            let node = ReferenceNode {
                path: path.clone(),
                references,
                files: files.into(),
                include: include.into(),
                exclude: exclude.into(),
                composite,
                incremental,
                declaration,
                no_emit,
                build_info_path,
            };

            nodes.insert(path, node);
        }

        Ok(Self { nodes })
    }

    /// Returns the node for a given config path, if it participates in the
    /// graph.
    #[must_use]
    pub fn node(&self, path: &Path) -> Option<&ReferenceNode> {
        self.nodes.get(path)
    }

    /// Returns the project config paths in a deterministic topological order,
    /// dependencies before dependents.  Fails if the graph contains a cycle.
    pub fn topological_order(&self) -> Result<Vec<PathBuf>, ReferenceError> {
        if let Some(cycle) = self.find_cycle() {
            return Err(ReferenceError::Cycle { sequence: cycle });
        }

        let mut in_degree: BTreeMap<PathBuf, usize> =
            self.nodes.keys().map(|p| (p.clone(), 0)).collect();
        let mut dependents: BTreeMap<PathBuf, Vec<PathBuf>> =
            self.nodes.keys().map(|p| (p.clone(), Vec::new())).collect();

        for node in self.nodes.values() {
            *in_degree.get_mut(&node.path).expect("node in graph") = node
                .references
                .iter()
                .filter(|reference| self.nodes.contains_key(reference.path()))
                .count();
            for reference in &*node.references {
                let target = reference.path().to_path_buf();
                if let Some(list) = dependents.get_mut(&target) {
                    list.push(node.path.clone());
                }
            }
        }

        let mut ready: BTreeSet<PathBuf> = in_degree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(path, _)| path.clone())
            .collect();

        let mut order = Vec::with_capacity(self.nodes.len());

        while let Some(current) = take_first(&mut ready) {
            order.push(current.clone());

            if let Some(dependents) = dependents.get(&current) {
                for dependent in dependents {
                    if let Some(degree) = in_degree.get_mut(dependent) {
                        *degree -= 1;
                        if *degree == 0 {
                            ready.insert(dependent.clone());
                        }
                    }
                }
            }
        }

        if order.len() == self.nodes.len() {
            Ok(order)
        } else {
            // A cycle should already have been caught; this branch is defensive.
            let cycle = self.find_cycle().unwrap_or_default();
            Err(ReferenceError::Cycle { sequence: cycle })
        }
    }

    /// Validates the project-reference graph and returns every diagnostic.
    pub fn validate(&self) -> Vec<ReferenceError> {
        let mut diagnostics = Vec::new();

        if let Some(cycle) = self.find_cycle() {
            diagnostics.push(ReferenceError::Cycle { sequence: cycle });
        }

        for node in self.nodes.values() {
            if node.composite {
                if node.declaration == Some(false) {
                    diagnostics.push(ReferenceError::CompositeNeedsDeclaration {
                        project: node.path.clone(),
                    });
                }
                if node.incremental == Some(false) {
                    diagnostics.push(ReferenceError::CompositeNeedsIncremental {
                        project: node.path.clone(),
                    });
                }
            }

            for reference in &*node.references {
                let target = reference.path().to_path_buf();
                if let Some(target_node) = self.nodes.get(&target) {
                    let original: Arc<str> = reference
                        .original_path()
                        .map(Arc::from)
                        .unwrap_or_else(|| Arc::from("?"));

                    if node.has_sources() {
                        if !target_node.composite {
                            diagnostics.push(ReferenceError::ReferencedNotComposite {
                                from: node.path.clone(),
                                to: target.clone(),
                                reference: original.clone(),
                            });
                        }
                        if target_node.no_emit {
                            diagnostics.push(ReferenceError::ReferencedNoEmit {
                                from: node.path.clone(),
                                to: target,
                                reference: original,
                            });
                        }
                    }

                    if let Some(build_info) = &node.build_info_path
                        && target_node.build_info_path.as_deref() == Some(build_info)
                    {
                        diagnostics.push(ReferenceError::BuildInfoCollision {
                            first: node.path.clone(),
                            second: target_node.path.clone(),
                            build_info: build_info.clone(),
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Computes the deterministic `.tsbuildinfo` identity for a project that
    /// participates in the graph.  Returns `None` for projects that are not
    /// incremental and for unknown project paths.
    #[must_use]
    pub fn tsbuildinfo_identity(&self, project: &Path) -> Option<BuildInfoIdentity> {
        let node = self.nodes.get(project)?;
        if !node.is_incremental() {
            return None;
        }

        let mut canonical = Vec::new();

        feed_bytes(&mut canonical, project.to_string_lossy().as_bytes());

        if let Some(build_info) = &node.build_info_path {
            feed_bytes(&mut canonical, build_info.to_string_lossy().as_bytes());
        }

        feed_bytes(&mut canonical, if node.composite { b"1" } else { b"0" });
        feed_bytes(
            &mut canonical,
            if node.is_incremental() { b"1" } else { b"0" },
        );
        feed_bytes(
            &mut canonical,
            if node.declaration.unwrap_or(false) {
                b"1"
            } else {
                b"0"
            },
        );
        feed_bytes(&mut canonical, if node.no_emit { b"1" } else { b"0" });

        for reference in &*node.references {
            feed_bytes(
                &mut canonical,
                reference.path().to_string_lossy().as_bytes(),
            );
        }

        for file in &*node.files {
            feed_bytes(&mut canonical, file.to_string_lossy().as_bytes());
        }

        for include in &*node.include {
            feed_bytes(&mut canonical, include.as_bytes());
        }

        for exclude in &*node.exclude {
            feed_bytes(&mut canonical, exclude.as_bytes());
        }

        let hash = Sha256::digest(&canonical);
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(hash.as_slice());
        Some(BuildInfoIdentity(bytes))
    }

    fn find_cycle(&self) -> Option<Vec<PathBuf>> {
        #[derive(Clone, Copy, Eq, PartialEq)]
        enum Visit {
            White,
            Gray,
            Black,
        }

        let mut state: BTreeMap<PathBuf, Visit> = self
            .nodes
            .keys()
            .map(|p| (p.clone(), Visit::White))
            .collect();
        let mut path: Vec<PathBuf> = Vec::new();
        let mut stack: Vec<(PathBuf, usize)> = Vec::new();

        for start in self.nodes.keys().cloned().collect::<Vec<_>>() {
            if state.get(&start).copied() != Some(Visit::White) {
                continue;
            }
            state.insert(start.clone(), Visit::Gray);
            path.push(start.clone());
            stack.push((start, 0));

            while let Some((current, mut i)) = stack.pop() {
                let current_node = self.nodes.get(&current);
                let references: &[ReferenceEdge] =
                    current_node.map_or(&[], |n| n.references.as_ref());

                loop {
                    if i >= references.len() {
                        state.insert(current.clone(), Visit::Black);
                        if path.last() == Some(&current) {
                            path.pop();
                        }
                        break;
                    }

                    let reference = &references[i];
                    i += 1;
                    let target = reference.path().to_path_buf();

                    match state.get(&target).copied() {
                        Some(Visit::White) => {
                            state.insert(target.clone(), Visit::Gray);
                            path.push(target.clone());
                            stack.push((current, i));
                            stack.push((target, 0));
                            break;
                        }
                        Some(Visit::Gray) => {
                            if let Some(index) = path.iter().position(|p| p == &target) {
                                let mut sequence: Vec<PathBuf> = path[index..].to_vec();
                                sequence.push(target);
                                return Some(sequence);
                            }
                        }
                        Some(Visit::Black) | None => continue,
                    }
                }
            }
        }

        None
    }
}

/// Resolves a project argument to its config file, preserving explicit JSON paths.
pub fn resolve_config_file_name(path: PathBuf) -> PathBuf {
    if is_json_path(&path) {
        path
    } else {
        path.join("tsconfig.json")
    }
}

fn is_json_path(path: &Path) -> bool {
    path.extension()
        .and_then(|e| e.to_str())
        .is_some_and(|e| e.eq_ignore_ascii_case("json"))
}

fn compiler_options_raw(config: &ProjectConfig) -> Option<&JsonObject> {
    config.raw().get("compilerOptions")?.as_object()
}

fn raw_bool(options: Option<&JsonObject>, key: &str) -> Option<bool> {
    options?.get(key)?.as_bool()
}

fn compute_build_info_path(
    root: &ProjectRoot,
    config: &ProjectConfig,
    dir: &Path,
    composite: bool,
    incremental: Option<bool>,
) -> Result<Option<PathBuf>, ReferenceError> {
    let is_incremental = incremental.unwrap_or(false) || composite;
    if !is_incremental {
        return Ok(None);
    }

    let options = compiler_options_raw(config);

    if let Some(tsbuildinfo_file) = options.and_then(|o| o.get("tsBuildInfoFile")) {
        let Some(specified) = tsbuildinfo_file.as_str() else {
            // Non-string tsBuildInfoFile is a tsconfig error elsewhere; here it
            // simply yields no canonical build-info path.
            return Ok(None);
        };
        if specified.is_empty() {
            return Ok(None);
        }
        return Ok(Some(root.resolve_from(dir, specified)?));
    }

    let config_path = config.path();
    let extension_less = config_path.with_extension("");

    if let Some(out_dir) = config.options().out_dir() {
        let out_dir = out_dir.to_path_buf();
        let build_info_stem = if let Some(root_dir) = config.options().root_dir() {
            match extension_less.strip_prefix(root_dir) {
                Ok(relative) => out_dir.join(relative),
                Err(_) => out_dir.join(
                    extension_less
                        .file_stem()
                        .map_or_else(|| "tsbuildinfo".into(), PathBuf::from),
                ),
            }
        } else {
            out_dir.join(
                extension_less
                    .file_stem()
                    .map_or_else(|| "tsbuildinfo".into(), PathBuf::from),
            )
        };
        return Ok(Some(build_info_stem.with_extension("tsbuildinfo")));
    }

    Ok(Some(extension_less.with_extension("tsbuildinfo")))
}

fn sort_references(references: &mut [ReferenceEdge]) {
    references.sort_by(|a, b| a.path().cmp(b.path()));
}

fn take_first(set: &mut BTreeSet<PathBuf>) -> Option<PathBuf> {
    let first = set.iter().next().cloned()?;
    set.remove(&first);
    Some(first)
}

fn feed_bytes(canonical: &mut Vec<u8>, bytes: &[u8]) {
    canonical.extend_from_slice(bytes);
    canonical.push(0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::test_paths::abs;

    fn test_root() -> ProjectRoot {
        ProjectRoot::new(abs("/workspace/test")).expect("absolute test root")
    }

    fn parse(root: &ProjectRoot, path: impl AsRef<Path>, source: &str) -> TsConfig {
        TsConfig::parse(root, path, source).expect("valid test tsconfig")
    }

    #[test]
    fn empty_references_parses_to_empty_node() {
        let root = test_root();
        let config = parse(&root, abs("/workspace/test/app/tsconfig.json"), r#"{}"#);
        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();

        let node = graph.node(config.config().path()).expect("node exists");
        assert!(node.references.is_empty());
        assert!(!node.composite);
        assert!(!node.is_incremental());
    }

    #[test]
    fn single_directory_reference_resolves_to_sibling_tsconfig() {
        let root = test_root();
        let app = parse(
            &root,
            abs("/workspace/test/app/tsconfig.json"),
            r#"{"references": [{"path": "../lib"}]}"#,
        );
        let lib = parse(&root, abs("/workspace/test/lib/tsconfig.json"), r#"{}"#);

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();
        let node = graph.node(app.config().path()).unwrap();

        assert_eq!(node.references.len(), 1);
        assert_eq!(
            node.references[0].path(),
            abs("/workspace/test/lib/tsconfig.json").as_path()
        );
        assert_eq!(node.references[0].original_path().unwrap(), "../lib");
        assert_eq!(node.references[0].circular(), None);
        assert!(is_json_path(node.references[0].path()));
    }

    #[test]
    fn explicit_config_file_reference_preserves_json_path() {
        let root = test_root();
        let app = parse(
            &root,
            abs("/workspace/test/app/tsconfig.json"),
            r#"{"references": [{"path": "../lib/custom.json"}]}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app]).unwrap();
        let node = graph.node(app.config().path()).unwrap();

        assert_eq!(
            node.references[0].path(),
            abs("/workspace/test/lib/custom.json").as_path()
        );
        assert!(is_json_path(node.references[0].path()));
    }

    #[test]
    fn topological_order_puts_dependencies_first() {
        let root = test_root();
        let app = parse(
            &root,
            abs("/workspace/test/app/tsconfig.json"),
            r#"{"references": [{"path": "../lib"}]}"#,
        );
        let lib = parse(&root, abs("/workspace/test/lib/tsconfig.json"), r#"{}"#);

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &lib]).unwrap();
        let order = graph.topological_order().unwrap();

        assert_eq!(
            order,
            vec![
                abs("/workspace/test/lib/tsconfig.json"),
                abs("/workspace/test/app/tsconfig.json"),
            ]
        );
    }

    #[test]
    fn diamond_graph_produces_dependency_first_order() {
        let root = test_root();
        let app = parse(
            &root,
            abs("/workspace/test/app/tsconfig.json"),
            r#"{"references": [{"path": "../left"}, {"path": "../right"}]}"#,
        );
        let left = parse(
            &root,
            abs("/workspace/test/left/tsconfig.json"),
            r#"{"references": [{"path": "../shared"}]}"#,
        );
        let right = parse(
            &root,
            abs("/workspace/test/right/tsconfig.json"),
            r#"{"references": [{"path": "../shared"}]}"#,
        );
        let shared = parse(&root, abs("/workspace/test/shared/tsconfig.json"), r#"{}"#);

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&app, &left, &right, &shared]).unwrap();
        let order = graph.topological_order().unwrap();

        assert_eq!(order[0], abs("/workspace/test/shared/tsconfig.json"));
        assert!(
            order
                .iter()
                .position(|p| p == shared.config().path())
                .unwrap()
                < order
                    .iter()
                    .position(|p| p == left.config().path())
                    .unwrap()
        );
        assert!(
            order
                .iter()
                .position(|p| p == shared.config().path())
                .unwrap()
                < order
                    .iter()
                    .position(|p| p == right.config().path())
                    .unwrap()
        );
        assert!(
            order
                .iter()
                .position(|p| p == left.config().path())
                .unwrap()
                < order.iter().position(|p| p == app.config().path()).unwrap()
        );
        assert!(
            order
                .iter()
                .position(|p| p == right.config().path())
                .unwrap()
                < order.iter().position(|p| p == app.config().path()).unwrap()
        );
    }

    #[test]
    fn cycle_is_reported_in_topological_order() {
        let root = test_root();
        let a = parse(
            &root,
            abs("/workspace/test/a/tsconfig.json"),
            r#"{"references": [{"path": "../b"}]}"#,
        );
        let b = parse(
            &root,
            abs("/workspace/test/b/tsconfig.json"),
            r#"{"references": [{"path": "../a"}]}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&a, &b]).unwrap();
        let err = graph.topological_order().unwrap_err();

        assert!(matches!(err, ReferenceError::Cycle { .. }));
        if let ReferenceError::Cycle { sequence } = err {
            assert_eq!(sequence.first(), sequence.last());
            assert!(sequence.len() >= 3);
        }
    }

    #[test]
    fn composite_requires_declaration_and_incremental() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{"compilerOptions": {"composite": true, "declaration": false, "incremental": false}}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let errors = graph.validate();

        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ReferenceError::CompositeNeedsDeclaration { .. }))
        );
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ReferenceError::CompositeNeedsIncremental { .. }))
        );
    }

    #[test]
    fn non_composite_referenced_project_is_diagnosed() {
        let root = test_root();
        let parent = parse(
            &root,
            abs("/workspace/test/parent/tsconfig.json"),
            r#"{
                "files": ["a.ts"],
                "references": [{"path": "../child"}]
            }"#,
        );
        let child = parse(&root, abs("/workspace/test/child/tsconfig.json"), r#"{}"#);

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&parent, &child]).unwrap();
        let errors = graph.validate();

        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ReferenceError::ReferencedNotComposite { .. }))
        );
    }

    #[test]
    fn no_emit_referenced_project_is_diagnosed() {
        let root = test_root();
        let parent = parse(
            &root,
            abs("/workspace/test/parent/tsconfig.json"),
            r#"{
                "files": ["a.ts"],
                "compilerOptions": {"composite": true, "declaration": true},
                "references": [{"path": "../child"}]
            }"#,
        );
        let child = parse(
            &root,
            abs("/workspace/test/child/tsconfig.json"),
            r#"{"compilerOptions": {"composite": true, "noEmit": true}}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&parent, &child]).unwrap();
        let errors = graph.validate();

        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ReferenceError::ReferencedNoEmit { .. }))
        );
    }

    #[test]
    fn default_build_info_path_uses_config_name() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{"compilerOptions": {"incremental": true}}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let node = graph.node(config.config().path()).unwrap();

        assert_eq!(
            node.build_info_path.as_deref(),
            Some(abs("/workspace/test/p/tsconfig.tsbuildinfo").as_path())
        );
    }

    #[test]
    fn build_info_path_respects_out_dir_and_root_dir() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/src/p/tsconfig.json"),
            r#"{
                "compilerOptions": {
                    "composite": true,
                    "declaration": true,
                    "outDir": "../../out",
                    "rootDir": "../../src"
                }
            }"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let node = graph.node(config.config().path()).unwrap();

        assert_eq!(
            node.build_info_path.as_deref(),
            Some(abs("/workspace/test/out/p/tsconfig.tsbuildinfo").as_path())
        );
    }

    #[test]
    fn tsbuild_info_path_from_explicit_file() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{
                "compilerOptions": {
                    "incremental": true,
                    "tsBuildInfoFile": "../cache/info.json"
                }
            }"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let node = graph.node(config.config().path()).unwrap();

        assert_eq!(
            node.build_info_path.as_deref(),
            Some(abs("/workspace/test/cache/info.json").as_path())
        );
    }

    #[test]
    fn build_info_collision_is_diagnosed() {
        let root = test_root();
        let parent = parse(
            &root,
            abs("/workspace/test/parent/tsconfig.json"),
            r#"{
                "files": ["a.ts"],
                "compilerOptions": {"composite": true, "declaration": true, "outDir": "../out"},
                "references": [{"path": "../child"}]
            }"#,
        );
        let child = parse(
            &root,
            abs("/workspace/test/child/tsconfig.json"),
            r#"{
                "compilerOptions": {"composite": true, "declaration": true, "outDir": "../out"}
            }"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&parent, &child]).unwrap();
        let errors = graph.validate();

        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ReferenceError::BuildInfoCollision { .. }))
        );
    }

    #[test]
    fn tsbuildinfo_identity_is_stable_and_switches_with_inputs() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{
                "files": ["a.ts"],
                "compilerOptions": {"incremental": true}
            }"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let first = graph.tsbuildinfo_identity(config.config().path());

        assert!(first.is_some());

        let second = graph.tsbuildinfo_identity(config.config().path());
        assert_eq!(first, second);

        let different = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{
                "files": ["a.ts", "b.ts"],
                "compilerOptions": {"incremental": true}
            }"#,
        );
        let graph2 = ReferenceGraph::from_tsconfigs(&root, &[&different]).unwrap();
        assert_ne!(
            first,
            graph2.tsbuildinfo_identity(different.config().path())
        );
    }

    #[test]
    fn tsbuildinfo_identity_renders_as_full_hex() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{"compilerOptions": {"incremental": true}}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let identity = graph.tsbuildinfo_identity(config.config().path()).unwrap();

        assert_eq!(identity.value().len(), 32);
        assert_eq!(identity.to_hex().len(), 64);
        assert!(identity.to_hex().chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn non_incremental_project_has_no_build_info_identity() {
        let root = test_root();
        let config = parse(&root, abs("/workspace/test/p/tsconfig.json"), r#"{}"#);

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        assert!(graph.tsbuildinfo_identity(config.config().path()).is_none());
    }

    #[test]
    fn circular_annotation_is_preserved() {
        let root = test_root();
        let config = parse(
            &root,
            abs("/workspace/test/p/tsconfig.json"),
            r#"{"references": [{"path": "../lib", "circular": true}]}"#,
        );

        let graph = ReferenceGraph::from_tsconfigs(&root, &[&config]).unwrap();
        let node = graph.node(config.config().path()).unwrap();

        assert_eq!(node.references[0].circular(), Some(true));
    }
}
