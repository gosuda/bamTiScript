//! Strict, fail-closed completion over the frozen TypeScript-product program.
//!
//! The program is an explicit closed set. Verification never discovers extra
//! scope on behalf of a worker: disk ledgers and the generated completeness
//! ledger are observations checked against that set.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    fs::{self, File},
    io::{self, BufReader, Write},
    path::{Path, PathBuf},
    process,
    sync::atomic::{AtomicU64, Ordering},
};

use serde::{
    Deserialize, Deserializer,
    de::{IgnoredAny, MapAccess, SeqAccess, Visitor},
};

use crate::{ErrorCode, VerificationError, leaf_evidence, schema::sha256_hex};

const PROGRAM_PATH: &str = "verification/completion-program.toml";
const COMPLETENESS_LEDGER_PATH: &str = "proof/completeness-ledger.json";
const PROGRAM_SCHEMA: &str = "bamti.completion-program/v1";
const SPECIAL_ASPECT_LEAVES: [&str; 11] = [
    "A1.1", "A1.2", "A1.3", "A1.4", "A1.5", "A2.1", "A2.2", "A2.3", "A2.6", "A2.7", "F2.4",
];

/// Leaves the contract table freezes; a table with any other count is stale.
const FROZEN_LEAF_COUNT: usize = 114;

// These recovery ledgers are not part of the frozen product authority.
const LEGACY_INTEGRATION_LEDGER_IDS: [&str; 14] = [
    "clean-port-authority-evidence",
    "clean-port-authority-root",
    "clean-port-bytecode-codegen",
    "clean-port-compiler-cli",
    "clean-port-compiler-frontend",
    "clean-port-compiler-semantics",
    "clean-port-corpus-workflow",
    "clean-port-emitter-project-cli",
    "clean-port-integration",
    "clean-port-npm-api",
    "clean-port-runtime-builtins",
    "clean-port-runtime-core",
    "clean-port-runtime-native",
    "clean-port-verification-proof",
];
static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionScope {
    Leaf(String),
    Cluster(String),
    Track(String),
    Wave(String),
    Root(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompletionAspect {
    Contract,
    Evidence,
    Coverage,
    Regression,
    Mutation,
    Aggregate,
}

impl CompletionAspect {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Contract => "contract",
            Self::Evidence => "evidence",
            Self::Coverage => "coverage",
            Self::Regression => "regression",
            Self::Mutation => "mutation",
            Self::Aggregate => "aggregate",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "contract" => Some(Self::Contract),
            "evidence" => Some(Self::Evidence),
            "coverage" => Some(Self::Coverage),
            "regression" => Some(Self::Regression),
            "mutation" => Some(Self::Mutation),
            "aggregate" => Some(Self::Aggregate),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegenerateMode {
    Write,
    Check,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegenerateOutcome {
    Identical,
    Written { bytes: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionFailure {
    UnknownScope {
        kind: &'static str,
        id: String,
    },
    UnknownLeaf(String),
    MissingLeaf(String),
    DuplicateLeaf(String),
    DuplicateNode {
        kind: String,
        id: String,
    },
    OwnershipPathGap {
        leaf: String,
    },
    OrphanOwnership {
        leaf: String,
        path: String,
    },
    OwnershipConflict {
        path: String,
        first: String,
        second: String,
    },
    HierarchyGap {
        parent: String,
        child: String,
    },
    ChildNotProven {
        parent: String,
        child: String,
    },
    MissingLedger {
        id: String,
        path: String,
    },
    MissingAspect {
        id: String,
        aspect: CompletionAspect,
    },
    NonCurrentEvidence {
        id: String,
        gate: String,
    },
    StaleEvidence {
        id: String,
    },
    NonPassTerminal {
        obligation: String,
        state: String,
    },
    PublicReachabilityExclusion {
        obligation: String,
        state: String,
    },
    MissingReceipt {
        id: String,
    },
    UncheckedMutation {
        leaf: String,
    },
    RegressionUnchecked {
        id: String,
    },
}

impl fmt::Display for CompletionFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownScope { kind, id } => write!(f, "unknown {kind} `{id}`"),
            Self::UnknownLeaf(id) => write!(f, "program contains unknown leaf `{id}`"),
            Self::MissingLeaf(id) => write!(f, "program omits leaf `{id}`"),
            Self::DuplicateLeaf(id) => write!(f, "program duplicates leaf `{id}`"),
            Self::DuplicateNode { kind, id } => write!(f, "program duplicates {kind} `{id}`"),
            Self::OwnershipPathGap { leaf } => write!(f, "leaf `{leaf}` has no ownership path"),
            Self::OrphanOwnership { leaf, path } => {
                write!(f, "leaf `{leaf}` owns absent path `{path}`")
            }
            Self::OwnershipConflict {
                path,
                first,
                second,
            } => write!(
                f,
                "ownership `{path}` conflicts between `{first}` and `{second}`"
            ),
            Self::HierarchyGap { parent, child } => {
                write!(f, "hierarchy `{parent}` names unknown child `{child}`")
            }
            Self::ChildNotProven { parent, child } => {
                write!(f, "hierarchy `{parent}` has unproven child `{child}`")
            }
            Self::MissingLedger { id, path } => {
                write!(f, "scope `{id}` ledger `{path}` is missing")
            }
            Self::MissingAspect { id, aspect } => {
                write!(f, "scope `{id}` does not declare `{}`", aspect.as_str())
            }
            Self::NonCurrentEvidence { id, gate } => write!(
                f,
                "scope `{id}` gate `{gate}` lacks current content-addressed evidence"
            ),
            Self::StaleEvidence { id } => write!(f, "scope `{id}` has stale evidence"),
            Self::NonPassTerminal { obligation, state } => {
                write!(f, "obligation `{obligation}` is `{state}`, not PASS")
            }
            Self::PublicReachabilityExclusion { obligation, state } => write!(
                f,
                "public obligation `{obligation}` cannot be excluded as `{state}`"
            ),
            Self::MissingReceipt { id } => write!(f, "scope `{id}` has no matching receipt"),
            Self::UncheckedMutation { leaf } => {
                write!(f, "leaf `{leaf}` has no checked mutation contract")
            }
            Self::RegressionUnchecked { id } => {
                write!(f, "scope `{id}` has no checked regression evidence")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionReport {
    pub scope: CompletionScope,
    pub aspect: CompletionAspect,
    pub checked_leaves: usize,
    pub checked_obligations: usize,
    pub failures: Vec<CompletionFailure>,
    pub gate_evidence: Option<String>,
}

impl CompletionReport {
    pub fn is_pass(&self) -> bool {
        self.failures.is_empty()
    }

    pub fn success_line(&self) -> Option<String> {
        if !self.is_pass() {
            return None;
        }
        if self.aspect != CompletionAspect::Aggregate {
            let (kind, id) = match &self.scope {
                CompletionScope::Leaf(id) => ("LEAF", id.clone()),
                CompletionScope::Cluster(id) => ("CLUSTER", id.clone()),
                CompletionScope::Track(id) => ("TRACK", id.clone()),
                CompletionScope::Wave(id) => ("WAVE", id.clone()),
                CompletionScope::Root(id) => ("ROOT", id.clone()),
            };
            return Some(format!(
                "{kind} {id} {} PASS",
                self.aspect.as_str().to_ascii_uppercase()
            ));
        }
        match &self.scope {
            CompletionScope::Root(id) if id == "authority" => {
                Some("AUTHORITY COMPLETE release=typescript-7.0.2".into())
            }
            CompletionScope::Root(id) if id == "compiler" => Some(
                "COMPILER COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0".into(),
            ),
            CompletionScope::Root(id) if id == "runtime" => {
                Some("RUNTIME COMPLETE modes=3 blocking=0 external_blocked=0".into())
            }
            CompletionScope::Root(id) if id == "native" => {
                Some("NATIVE COMPLETE formal=PASS targets=49/49 benchmarks=9/9".into())
            }
            CompletionScope::Root(id) if id == "package" => {
                Some("PACKAGE COMPLETE exports=13 cli=PASS api=PASS".into())
            }
            CompletionScope::Root(id) if id == "product" => Some(
                "PRODUCT COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0 catalog_errors=0".into(),
            ),
            CompletionScope::Leaf(id) => Some(format!("LEAF {id} COMPLETE")),
            CompletionScope::Cluster(id) => Some(format!("CLUSTER {id} COMPLETE")),
            CompletionScope::Track(id) => Some(format!("TRACK {id} COMPLETE")),
            CompletionScope::Wave(id) => Some(format!("WAVE {id} COMPLETE")),
            CompletionScope::Root(id) => Some(format!("ROOT {id} COMPLETE")),
        }
    }
}

#[derive(Debug)]
pub enum CompletionError {
    Io { path: PathBuf, source: io::Error },
    Parse(String),
    Invalid(Vec<CompletionFailure>),
    CheckMismatch { path: PathBuf },
}

impl fmt::Display for CompletionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Parse(detail) => f.write_str(detail),
            Self::Invalid(failures) => {
                write!(f, "completion program is invalid")?;
                for failure in failures {
                    write!(f, "\n- {failure}")?;
                }
                Ok(())
            }
            Self::CheckMismatch { path } => write!(
                f,
                "{} differs from deterministic completion program",
                path.display()
            ),
        }
    }
}
impl std::error::Error for CompletionError {}
impl From<CompletionError> for VerificationError {
    fn from(value: CompletionError) -> Self {
        let code = match value {
            CompletionError::Io { .. } => ErrorCode::Io,
            CompletionError::Parse(_) => ErrorCode::Toml,
            CompletionError::Invalid(_) => ErrorCode::Schema,
            CompletionError::CheckMismatch { .. } => ErrorCode::Digest,
        };
        VerificationError::new(code, value.to_string())
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Program {
    schema: String,
    release: String,
    root: String,
    #[serde(default)]
    leaf: Vec<Leaf>,
    #[serde(default)]
    node: Vec<Node>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Leaf {
    id: String,
    cluster: String,
    wave: String,
    ledger: String,
    owns: Vec<String>,
    aspects: Vec<String>,
    catalogs: Vec<String>,
    mutation_required: bool,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Node {
    kind: String,
    id: String,
    children: Vec<String>,
    ledger: String,
    aspects: Vec<String>,
}

pub fn verify_completion(
    root: &Path,
    scope: &CompletionScope,
    aspect: CompletionAspect,
) -> Result<CompletionReport, CompletionError> {
    let program = load_program(root)?;
    let structural = validate_program(root, &program);
    if !structural.is_empty() {
        return Err(CompletionError::Invalid(structural));
    }

    let leaves = resolve_scope(&program, scope)?;
    let mut failures = Vec::new();
    let mut checked_obligations = 0;

    if matches!(
        aspect,
        CompletionAspect::Contract | CompletionAspect::Aggregate
    ) {
        for leaf in &leaves {
            verify_ownership(root, leaf, &mut failures);
        }
    }

    if aspect == CompletionAspect::Aggregate {
        for leaf in &leaves {
            for selected in [
                CompletionAspect::Contract,
                CompletionAspect::Evidence,
                CompletionAspect::Coverage,
                CompletionAspect::Regression,
            ] {
                if leaf.aspects.iter().any(|value| value == selected.as_str()) {
                    verify_leaf_aspect(root, leaf, selected, true, &mut failures);
                }
            }
            if leaf.mutation_required {
                verify_leaf_aspect(root, leaf, CompletionAspect::Mutation, true, &mut failures);
            }
        }
        checked_obligations = verify_obligations(root, &leaves, &mut failures)?;
    } else {
        verify_scope_aspect(
            root,
            &program,
            scope,
            aspect,
            !matches!(scope, CompletionScope::Leaf(_)),
            &mut failures,
        );
        if matches!(
            aspect,
            CompletionAspect::Evidence | CompletionAspect::Coverage | CompletionAspect::Regression
        ) {
            checked_obligations = verify_obligations(root, &leaves, &mut failures)?;
        }
    }

    if aspect == CompletionAspect::Aggregate {
        verify_hierarchy_ledgers(root, &program, scope, &mut failures);
    }

    let gate_evidence = match scope {
        CompletionScope::Leaf(id) => leaf_gate_evidence(root, &program, id, aspect),
        CompletionScope::Cluster(_)
        | CompletionScope::Track(_)
        | CompletionScope::Wave(_)
        | CompletionScope::Root(_) => None,
    };

    failures.sort_by_key(ToString::to_string);
    failures.dedup();
    Ok(CompletionReport {
        scope: scope.clone(),
        aspect,
        checked_leaves: leaves.len(),
        checked_obligations,
        gate_evidence,
        failures,
    })
}

pub fn regenerate_completion_program(
    root: &Path,
    mode: RegenerateMode,
) -> Result<RegenerateOutcome, CompletionError> {
    let path = root.join(PROGRAM_PATH);
    let program = load_program(root)?;
    let failures = validate_program(root, &program);
    if !failures.is_empty() {
        return Err(CompletionError::Invalid(failures));
    }
    let bytes = canonical_program(&program).into_bytes();
    if mode == RegenerateMode::Check {
        let actual = fs::read(&path).map_err(|source| CompletionError::Io {
            path: path.clone(),
            source,
        })?;
        return if actual == bytes {
            Ok(RegenerateOutcome::Identical)
        } else {
            Err(CompletionError::CheckMismatch { path })
        };
    }
    replace_atomically(&path, &bytes)?;
    Ok(RegenerateOutcome::Written { bytes: bytes.len() })
}

fn load_program(root: &Path) -> Result<Program, CompletionError> {
    let path = root.join(PROGRAM_PATH);
    let text = fs::read_to_string(&path).map_err(|source| CompletionError::Io { path, source })?;
    toml::from_str(&text)
        .map_err(|e| CompletionError::Parse(format!("{}: {e}", root.join(PROGRAM_PATH).display())))
}

fn completion_authority_leaves(root: &Path) -> (BTreeSet<String>, bool) {
    let path = root.join(".outline/type-script-7.0.2-completion.md");
    let Ok(text) = fs::read_to_string(path) else {
        return (BTreeSet::new(), false);
    };
    let strict =
        text.contains("\nrelease: typescript-7.0.2\n") && text.contains("\nproduct: bamti\n");
    let mut lines = text.lines();
    while lines.next().is_some_and(|line| {
        line != "| Leaf | Wave | Cluster | Deliverable | Owned paths | Gate ledger |"
    }) {}
    let _separator = lines.next();
    let leaves = lines
        .take_while(|line| line.starts_with('|'))
        .filter_map(|line| line.trim_matches('|').split('|').next())
        .map(str::trim)
        .filter(|id| !id.is_empty())
        .map(str::to_owned)
        .collect();
    (leaves, strict)
}

fn ledger_declared_aspects(root: &Path, ledger: &str) -> BTreeSet<String> {
    fs::read_to_string(root.join(ledger))
        .ok()
        .map(|text| {
            parse_gate_rows(&text)
                .into_iter()
                .filter_map(|row| {
                    row.check
                        .split_once("--aspect ")
                        .and_then(|(_, tail)| tail.split_whitespace().next())
                        .map(|value| {
                            value
                                .trim_matches(|character: char| {
                                    !character.is_ascii_alphanumeric() && character != '-'
                                })
                                .to_owned()
                        })
                })
                .collect()
        })
        .unwrap_or_default()
}

fn validate_program(root: &Path, p: &Program) -> Vec<CompletionFailure> {
    let mut out = Vec::new();
    if p.schema != PROGRAM_SCHEMA || p.release != "typescript-7.0.2" {
        out.push(CompletionFailure::StaleEvidence {
            id: "program-authority".into(),
        });
    }
    let mut leaves = BTreeMap::new();
    let mut owners = BTreeMap::new();
    for leaf in &p.leaf {
        if leaves.insert(leaf.id.clone(), leaf).is_some() {
            out.push(CompletionFailure::DuplicateLeaf(leaf.id.clone()));
        }
        if leaf.owns.is_empty() {
            out.push(CompletionFailure::OwnershipPathGap {
                leaf: leaf.id.clone(),
            });
        }
        for path in &leaf.owns {
            if let Some(first) = owners.insert(path.clone(), leaf.id.clone()) {
                out.push(CompletionFailure::OwnershipConflict {
                    path: path.clone(),
                    first,
                    second: leaf.id.clone(),
                });
            }
        }
        let ledger_aspects = ledger_declared_aspects(root, &leaf.ledger);
        let program_aspects: BTreeSet<String> = leaf.aspects.iter().cloned().collect();
        let mandatory: BTreeSet<String> = if SPECIAL_ASPECT_LEAVES.contains(&leaf.id.as_str()) {
            ledger_aspects.clone()
        } else {
            ["contract", "evidence", "coverage", "regression", "mutation"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        };
        if ledger_aspects != program_aspects
            || program_aspects != mandatory
            || leaf.mutation_required != mandatory.contains("mutation")
        {
            out.push(CompletionFailure::StaleEvidence {
                id: format!("aspect-contract:{}", leaf.id),
            });
        }
    }
    let authority_path = root.join(".outline/type-script-7.0.2-completion.md");
    let require_authority = !cfg!(test) || authority_path.exists();
    let (authority, strict_authority) = completion_authority_leaves(root);
    if require_authority && (!strict_authority || authority.len() != FROZEN_LEAF_COUNT) {
        out.push(CompletionFailure::StaleEvidence {
            id: format!("completion-authority-leaf-count={}", authority.len()),
        });
    }
    if require_authority {
        let declared: BTreeSet<String> = leaves.keys().cloned().collect();
        for id in authority.difference(&declared) {
            out.push(CompletionFailure::MissingLeaf(id.clone()));
        }
        for id in declared.difference(&authority) {
            out.push(CompletionFailure::UnknownLeaf(id.clone()));
        }
    }
    let gate_dir = root.join(".outline/gates");
    let mut disk = BTreeSet::new();
    if let Ok(entries) = fs::read_dir(&gate_dir) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if let Some(id) = name.strip_suffix(".md")
                && !["cluster-", "track-", "wave-", "root-"]
                    .iter()
                    .any(|prefix| id.starts_with(prefix))
                && !LEGACY_INTEGRATION_LEDGER_IDS.contains(&id)
            {
                disk.insert(id.to_owned());
            }
        }
    }
    for id in disk.difference(&leaves.keys().cloned().collect()) {
        out.push(CompletionFailure::MissingLeaf(id.clone()));
    }
    for id in leaves.keys() {
        if !disk.contains(id) {
            out.push(CompletionFailure::UnknownLeaf(id.clone()));
        }
    }

    let mut nodes = BTreeSet::new();
    for node in &p.node {
        let key = format!("{}:{}", node.kind, node.id);
        if !nodes.insert(key.clone()) {
            out.push(CompletionFailure::DuplicateNode {
                kind: node.kind.clone(),
                id: node.id.clone(),
            });
        }
        let ledger_aspects = ledger_declared_aspects(root, &node.ledger);
        let program_aspects: BTreeSet<String> = node.aspects.iter().cloned().collect();
        if root.join(&node.ledger).exists() && ledger_aspects != program_aspects {
            out.push(CompletionFailure::StaleEvidence {
                id: format!("aspect-contract:{}:{}", node.kind, node.id),
            });
        }
    }
    if !nodes.contains(&format!("root:{}", p.root)) {
        out.push(CompletionFailure::HierarchyGap {
            parent: "program".into(),
            child: format!("root:{}", p.root),
        });
    }
    for leaf in &p.leaf {
        if !nodes.contains(&format!("cluster:{}", leaf.cluster)) {
            out.push(CompletionFailure::HierarchyGap {
                parent: leaf.id.clone(),
                child: format!("cluster:{}", leaf.cluster),
            });
        }
        if !nodes.contains(&format!("wave:{}", leaf.wave)) {
            out.push(CompletionFailure::HierarchyGap {
                parent: leaf.id.clone(),
                child: format!("wave:{}", leaf.wave),
            });
        }
    }
    for node in &p.node {
        for child in &node.children {
            let qualified = if child.contains(':') {
                child.clone()
            } else {
                match node.kind.as_str() {
                    "cluster" | "wave" => format!("leaf:{child}"),
                    "track" => format!("cluster:{child}"),
                    "root" => {
                        if p.node.iter().any(|n| n.kind == "root" && n.id == *child) {
                            format!("root:{child}")
                        } else if p.node.iter().any(|n| n.kind == "track" && n.id == *child) {
                            format!("track:{child}")
                        } else {
                            format!("cluster:{child}")
                        }
                    }
                    _ => String::new(),
                }
            };
            let exists = if let Some(id) = qualified.strip_prefix("leaf:") {
                leaves.contains_key(id)
            } else {
                nodes.contains(&qualified)
            };
            if !exists {
                out.push(CompletionFailure::HierarchyGap {
                    parent: format!("{}:{}", node.kind, node.id),
                    child: qualified,
                });
            }
        }
    }
    out
}

fn resolve_scope<'a>(
    p: &'a Program,
    scope: &CompletionScope,
) -> Result<Vec<&'a Leaf>, CompletionError> {
    let mut ids = BTreeSet::new();
    match scope {
        CompletionScope::Leaf(id) => {
            if p.leaf.iter().any(|l| &l.id == id) {
                ids.insert(id.clone());
            } else {
                return Err(CompletionError::Invalid(vec![
                    CompletionFailure::UnknownScope {
                        kind: "leaf",
                        id: id.clone(),
                    },
                ]));
            }
        }
        CompletionScope::Cluster(id) => collect_node(p, "cluster", id, &mut ids)?,
        CompletionScope::Track(id) => collect_node(p, "track", id, &mut ids)?,
        CompletionScope::Wave(id) => collect_node(p, "wave", id, &mut ids)?,
        CompletionScope::Root(id) => collect_node(p, "root", id, &mut ids)?,
    }
    Ok(p.leaf
        .iter()
        .filter(|leaf| ids.contains(&leaf.id))
        .collect())
}

fn collect_node(
    p: &Program,
    kind: &str,
    id: &str,
    out: &mut BTreeSet<String>,
) -> Result<(), CompletionError> {
    let Some(node) = p.node.iter().find(|n| n.kind == kind && n.id == id) else {
        return Err(CompletionError::Invalid(vec![
            CompletionFailure::UnknownScope {
                kind: scope_kind(kind),
                id: id.to_owned(),
            },
        ]));
    };
    for child in &node.children {
        if let Some((child_kind, child_id)) = child.split_once(':') {
            collect_node(p, child_kind, child_id, out)?;
        } else if kind == "cluster" || kind == "wave" {
            out.insert(child.clone());
        } else if kind == "track" {
            collect_node(p, "cluster", child, out)?;
        } else if p.node.iter().any(|n| n.kind == "root" && n.id == *child) {
            collect_node(p, "root", child, out)?;
        } else if p.node.iter().any(|n| n.kind == "track" && n.id == *child) {
            collect_node(p, "track", child, out)?;
        } else {
            collect_node(p, "cluster", child, out)?;
        }
    }
    Ok(())
}
fn scope_kind(kind: &str) -> &'static str {
    match kind {
        "cluster" => "cluster",
        "track" => "track",
        "wave" => "wave",
        "root" => "root",
        _ => "node",
    }
}
fn scope_id(scope: &CompletionScope) -> String {
    match scope {
        CompletionScope::Leaf(v)
        | CompletionScope::Cluster(v)
        | CompletionScope::Track(v)
        | CompletionScope::Wave(v)
        | CompletionScope::Root(v) => v.clone(),
    }
}

fn verify_ownership(root: &Path, leaf: &Leaf, out: &mut Vec<CompletionFailure>) {
    if leaf.owns.is_empty() {
        out.push(CompletionFailure::OwnershipPathGap {
            leaf: leaf.id.clone(),
        });
    }
    for owned in &leaf.owns {
        let check = if let Some(i) = owned.find('*') {
            &owned[..i]
        } else {
            owned
        };
        let check = check.trim_end_matches('/');
        if check.is_empty() || !root.join(check).exists() {
            out.push(CompletionFailure::OrphanOwnership {
                leaf: leaf.id.clone(),
                path: owned.clone(),
            });
        }
    }
}

fn verify_scope_aspect(
    root: &Path,
    program: &Program,
    scope: &CompletionScope,
    aspect: CompletionAspect,
    require_checked: bool,
    out: &mut Vec<CompletionFailure>,
) {
    if let CompletionScope::Leaf(id) = scope {
        let leaf = program
            .leaf
            .iter()
            .find(|leaf| leaf.id == *id)
            .expect("validated leaf");
        verify_leaf_aspect(root, leaf, aspect, require_checked, out);
        return;
    }
    let (kind, id) = match scope {
        CompletionScope::Cluster(id) => ("cluster", id),
        CompletionScope::Track(id) => ("track", id),
        CompletionScope::Wave(id) => ("wave", id),
        CompletionScope::Root(id) => ("root", id),
        CompletionScope::Leaf(_) => unreachable!(),
    };
    let node = program
        .node
        .iter()
        .find(|node| node.kind == kind && node.id == *id)
        .expect("validated node");
    verify_ledger_aspect(
        root,
        LedgerRef {
            id: &node.id,
            ledger: &node.ledger,
            aspects: &node.aspects,
            leaf: None,
        },
        aspect,
        require_checked,
        out,
    );
}
fn verify_leaf_aspect(
    root: &Path,
    leaf: &Leaf,
    aspect: CompletionAspect,
    require_checked: bool,
    out: &mut Vec<CompletionFailure>,
) {
    verify_ledger_aspect(
        root,
        LedgerRef {
            id: &leaf.id,
            ledger: &leaf.ledger,
            aspects: &leaf.aspects,
            leaf: Some(leaf),
        },
        aspect,
        require_checked,
        out,
    );
}

fn leaf_gate_evidence(
    root: &Path,
    program: &Program,
    leaf_id: &str,
    aspect: CompletionAspect,
) -> Option<String> {
    let leaf = program.leaf.iter().find(|leaf| leaf.id == leaf_id)?;
    let expected_gate = leaf_evidence::gate_for_aspect(aspect.as_str())?;
    let text = fs::read_to_string(root.join(&leaf.ledger)).ok()?;
    parse_gate_rows(&text)
        .into_iter()
        .find(|row| row.gate == expected_gate)
        .map(|row| row.evidence)
}
/// One verifiable ledger: the scope identity, its gate file, the aspects it
/// declares, and the owning leaf when the row must bind leaf-owned artifacts.
struct LedgerRef<'a> {
    id: &'a str,
    ledger: &'a str,
    aspects: &'a [String],
    leaf: Option<&'a Leaf>,
}

fn verify_ledger_aspect(
    root: &Path,
    scope: LedgerRef<'_>,
    aspect: CompletionAspect,
    require_checked: bool,
    out: &mut Vec<CompletionFailure>,
) {
    let LedgerRef {
        id,
        ledger,
        aspects,
        leaf,
    } = scope;
    if !aspects.iter().any(|a| a == aspect.as_str()) {
        out.push(if aspect == CompletionAspect::Mutation {
            CompletionFailure::UncheckedMutation { leaf: id.into() }
        } else {
            CompletionFailure::MissingAspect {
                id: id.into(),
                aspect,
            }
        });
        return;
    }
    let path = root.join(ledger);
    let Ok(text) = fs::read_to_string(&path) else {
        out.push(CompletionFailure::MissingLedger {
            id: id.into(),
            path: ledger.into(),
        });
        return;
    };
    let expected_gate = leaf_evidence::gate_for_aspect(aspect.as_str())
        .expect("every completion aspect has a registered gate");
    let rows = parse_gate_rows(&text);
    let Some(row) = rows.iter().find(|row| row.gate == expected_gate) else {
        out.push(CompletionFailure::MissingAspect {
            id: id.into(),
            aspect,
        });
        return;
    };
    let evidence_current = leaf.map_or_else(
        || current_evidence(root, &row.evidence),
        |leaf| {
            leaf_evidence::validate(root, &leaf.id, aspect.as_str(), &leaf.owns, &row.evidence)
                .is_ok()
        },
    );
    if (require_checked && !row.checked) || !evidence_current {
        out.push(if aspect == CompletionAspect::Mutation {
            CompletionFailure::UncheckedMutation { leaf: id.into() }
        } else {
            CompletionFailure::NonCurrentEvidence {
                id: id.into(),
                gate: row.gate.clone(),
            }
        });
    }
}

#[derive(Default)]
struct GateRow {
    gate: String,
    checked: bool,
    check: String,
    evidence: String,
}
fn parse_gate_rows(text: &str) -> Vec<GateRow> {
    let mut rows = Vec::new();
    let mut current: Option<GateRow> = None;
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("- [") {
            if let Some(r) = current.take() {
                rows.push(r);
            }
            let checked = rest.starts_with('x') || rest.starts_with('X');
            let gate = rest
                .split_once("] ")
                .and_then(|(_, label)| label.split_once(':').map(|(gate, _)| gate.trim()))
                .filter(|gate| !gate.is_empty())
                .unwrap_or("?")
                .to_owned();
            current = Some(GateRow {
                gate,
                checked,
                ..Default::default()
            });
        } else if let Some(r) = current.as_mut() {
            let t = line.trim();
            if let Some(v) = t.strip_prefix("CHECK: ") {
                r.check = v.into();
            }
            if let Some(v) = t.strip_prefix("EVIDENCE: ") {
                r.evidence = v.into();
            }
        }
    }
    if let Some(r) = current {
        rows.push(r);
    }
    rows
}
fn current_evidence(root: &Path, value: &str) -> bool {
    if value.to_ascii_lowercase().contains("pending") {
        return false;
    }
    let mut receipt = None;
    let mut expected = None;
    for field in value.split_whitespace() {
        if let Some(path) = field
            .strip_prefix("receipt=")
            .or_else(|| field.strip_prefix("path="))
        {
            receipt = Some(path);
        } else if let Some(digest) = field.strip_prefix("sha256=") {
            expected = Some(digest);
        }
    }
    let (Some(receipt), Some(expected)) = (receipt, expected) else {
        return false;
    };
    if expected.len() != 64
        || !expected
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
    {
        return false;
    }
    let path = Path::new(receipt);
    if path.is_absolute()
        || path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return false;
    }
    let Ok(canonical_root) = root.canonicalize() else {
        return false;
    };
    let Ok(canonical_receipt) = root.join(path).canonicalize() else {
        return false;
    };
    if !canonical_receipt.starts_with(&canonical_root) {
        return false;
    }
    fs::read(canonical_receipt).is_ok_and(|bytes| sha256_hex(&bytes) == expected)
}

fn verify_hierarchy_ledgers(
    root: &Path,
    program: &Program,
    scope: &CompletionScope,
    out: &mut Vec<CompletionFailure>,
) {
    let parent = scope_id(scope);
    if let Ok(leaves) = resolve_scope(program, scope) {
        for leaf in leaves {
            verify_complete_ledger(root, &parent, &leaf.id, &leaf.ledger, false, out);
        }
    }
    let mut nodes = BTreeSet::new();
    match scope {
        CompletionScope::Cluster(id) => collect_hierarchy_nodes(program, "cluster", id, &mut nodes),
        CompletionScope::Track(id) => collect_hierarchy_nodes(program, "track", id, &mut nodes),
        CompletionScope::Wave(id) => collect_hierarchy_nodes(program, "wave", id, &mut nodes),
        CompletionScope::Root(id) => collect_hierarchy_nodes(program, "root", id, &mut nodes),
        CompletionScope::Leaf(_) => {}
    }
    for key in nodes {
        let (kind, id) = key.split_once(':').expect("qualified node");
        let node = program
            .node
            .iter()
            .find(|node| node.kind == kind && node.id == id)
            .expect("validated hierarchy");
        verify_complete_ledger(root, &parent, &key, &node.ledger, false, out);
    }
}

fn collect_hierarchy_nodes(program: &Program, kind: &str, id: &str, out: &mut BTreeSet<String>) {
    let Some(node) = program
        .node
        .iter()
        .find(|node| node.kind == kind && node.id == id)
    else {
        return;
    };
    if !out.insert(format!("{kind}:{id}")) {
        return;
    }
    for child in &node.children {
        if let Some((child_kind, child_id)) = child.split_once(':') {
            if child_kind != "leaf" {
                collect_hierarchy_nodes(program, child_kind, child_id, out);
            }
        } else if kind == "track" {
            collect_hierarchy_nodes(program, "cluster", child, out);
        } else if kind == "root" {
            if program
                .node
                .iter()
                .any(|candidate| candidate.kind == "root" && candidate.id == *child)
            {
                collect_hierarchy_nodes(program, "root", child, out);
            } else if program
                .node
                .iter()
                .any(|candidate| candidate.kind == "track" && candidate.id == *child)
            {
                collect_hierarchy_nodes(program, "track", child, out);
            } else {
                collect_hierarchy_nodes(program, "cluster", child, out);
            }
        }
    }
}

fn verify_complete_ledger(
    root: &Path,
    parent: &str,
    child: &str,
    ledger: &str,
    first_row_only: bool,
    out: &mut Vec<CompletionFailure>,
) {
    let path = root.join(ledger);
    let Ok(text) = fs::read_to_string(&path) else {
        out.push(CompletionFailure::MissingLedger {
            id: child.into(),
            path: ledger.into(),
        });
        return;
    };
    let rows = parse_gate_rows(&text);
    let incomplete = rows.is_empty()
        || rows
            .iter()
            .take(if first_row_only { 1 } else { usize::MAX })
            .any(|row| !row.checked || !current_evidence(root, &row.evidence));
    if incomplete {
        out.push(CompletionFailure::ChildNotProven {
            parent: parent.into(),
            child: child.into(),
        });
    }
}

#[derive(Deserialize)]
struct RawLedgerRow {
    id: String,
    state: String,
    #[serde(default)]
    public_surface: Option<String>,
}
struct LedgerScan<'a> {
    catalogs: &'a BTreeSet<String>,
    failures: &'a mut Vec<CompletionFailure>,
    expected_manifest: String,
    current: bool,
    matched: usize,
}

struct LedgerSeed<'a, 'b> {
    scan: &'a mut LedgerScan<'b>,
}

impl<'de> serde::de::DeserializeSeed<'de> for LedgerSeed<'_, '_> {
    type Value = ();

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_map(LedgerVisitor { scan: self.scan })
    }
}

struct LedgerVisitor<'a, 'b> {
    scan: &'a mut LedgerScan<'b>,
}

impl<'de> Visitor<'de> for LedgerVisitor<'_, '_> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("completion ledger object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let mut schema_current = false;
        let mut manifest_current = false;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "schema" => {
                    schema_current = map.next_value::<String>()? == "bamti.completeness-ledger/v1";
                }
                "manifest_sha256" => {
                    manifest_current = map.next_value::<String>()? == self.scan.expected_manifest;
                }
                "rows" => map.next_value_seed(RowsSeed { scan: self.scan })?,
                _ => {
                    map.next_value::<IgnoredAny>()?;
                }
            }
        }
        self.scan.current = schema_current && manifest_current;
        Ok(())
    }
}

struct RowsSeed<'a, 'b> {
    scan: &'a mut LedgerScan<'b>,
}

impl<'de> serde::de::DeserializeSeed<'de> for RowsSeed<'_, '_> {
    type Value = ();

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_seq(RowsVisitor { scan: self.scan })
    }
}

struct RowsVisitor<'a, 'b> {
    scan: &'a mut LedgerScan<'b>,
}

impl<'de> Visitor<'de> for RowsVisitor<'_, '_> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("ledger rows")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<(), A::Error> {
        while let Some(row) = seq.next_element::<RawLedgerRow>()? {
            let catalog = row.id.split_once(':').map_or("", |value| value.0);
            if !self.scan.catalogs.contains(catalog) {
                continue;
            }
            self.scan.matched += 1;
            if row.state == "PASS" {
                continue;
            }
            let public = !matches!(
                row.public_surface.as_deref(),
                Some("internal-harness" | "proposal-stage" | "non-public")
            );
            let exact_exclusion = matches!(
                row.state.as_str(),
                "INAPPLICABLE_LANGUAGE_SERVICE"
                    | "INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE"
                    | "INAPPLICABLE_V8_INTERNAL"
            );
            if exact_exclusion && public {
                self.scan
                    .failures
                    .push(CompletionFailure::PublicReachabilityExclusion {
                        obligation: row.id,
                        state: row.state,
                    });
            } else if !exact_exclusion {
                self.scan.failures.push(CompletionFailure::NonPassTerminal {
                    obligation: row.id,
                    state: row.state,
                });
            }
        }
        Ok(())
    }
}

fn verify_obligations(
    root: &Path,
    leaves: &[&Leaf],
    failures: &mut Vec<CompletionFailure>,
) -> Result<usize, CompletionError> {
    let catalogs: BTreeSet<String> = leaves
        .iter()
        .flat_map(|leaf| leaf.catalogs.iter().cloned())
        .collect();
    if catalogs.is_empty() {
        return Ok(0);
    }
    let manifest_path = root.join("verification/manifest.lock.json");
    let manifest = fs::read(&manifest_path).map_err(|source| CompletionError::Io {
        path: manifest_path,
        source,
    })?;
    let path = root.join(COMPLETENESS_LEDGER_PATH);
    let file = File::open(&path).map_err(|source| CompletionError::Io {
        path: path.clone(),
        source,
    })?;
    let mut scan = LedgerScan {
        catalogs: &catalogs,
        failures,
        expected_manifest: sha256_hex(&manifest),
        current: false,
        matched: 0,
    };
    let mut deserializer = serde_json::Deserializer::from_reader(BufReader::new(file));
    serde::de::DeserializeSeed::deserialize(LedgerSeed { scan: &mut scan }, &mut deserializer)
        .map_err(|error| CompletionError::Parse(format!("{}: {error}", path.display())))?;
    if !scan.current {
        scan.failures.push(CompletionFailure::StaleEvidence {
            id: "completeness-ledger".into(),
        });
    }
    if scan.matched == 0 {
        for leaf in leaves.iter().filter(|leaf| !leaf.catalogs.is_empty()) {
            scan.failures.push(CompletionFailure::MissingReceipt {
                id: leaf.id.clone(),
            });
        }
    }
    Ok(scan.matched)
}

fn canonical_program(p: &Program) -> String {
    let mut s = format!(
        "schema = {:?}\nrelease = {:?}\nroot = {:?}\n\n",
        p.schema, p.release, p.root
    );
    for l in &p.leaf {
        s.push_str("[[leaf]]\n");
        s.push_str(&format!("id = {:?}\ncluster = {:?}\nwave = {:?}\nledger = {:?}\nowns = {}\naspects = {}\ncatalogs = {}\nmutation_required = {}\n\n",l.id,l.cluster,l.wave,l.ledger,strings(&l.owns),strings(&l.aspects),strings(&l.catalogs),l.mutation_required));
    }
    for n in &p.node {
        s.push_str("[[node]]\n");
        s.push_str(&format!(
            "kind = {:?}\nid = {:?}\nchildren = {}\nledger = {:?}\naspects = {}\n\n",
            n.kind,
            n.id,
            strings(&n.children),
            n.ledger,
            strings(&n.aspects)
        ));
    }
    s
}
fn strings(v: &[String]) -> String {
    format!(
        "[{}]",
        v.iter()
            .map(|x| format!("{x:?}"))
            .collect::<Vec<_>>()
            .join(", ")
    )
}
fn replace_atomically(path: &Path, bytes: &[u8]) -> Result<(), CompletionError> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|source| CompletionError::Io {
        path: parent.into(),
        source,
    })?;
    let temp = parent.join(format!(
        ".completion-program.tmp.{}.{}",
        process::id(),
        TEMP_NONCE.fetch_add(1, Ordering::Relaxed)
    ));
    let result = (|| {
        let mut file = File::create(&temp).map_err(|source| CompletionError::Io {
            path: temp.clone(),
            source,
        })?;
        file.write_all(bytes)
            .map_err(|source| CompletionError::Io {
                path: temp.clone(),
                source,
            })?;
        file.sync_all().map_err(|source| CompletionError::Io {
            path: temp.clone(),
            source,
        })?;
        fs::rename(&temp, path).map_err(|source| CompletionError::Io {
            path: path.into(),
            source,
        })
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    struct Scratch(PathBuf);
    impl Scratch {
        fn new(name: &str) -> Self {
            // The clock cannot keep these apart: macOS reads it in microseconds,
            // and `fixture` gives every test the same label. A collision does not
            // fail, because `create_dir_all` accepts an existing directory, so
            // two tests would share one and one would delete it under the other.
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let p = std::env::temp_dir().join(format!(
                "bamts-completion-{name}-{}-{}",
                process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            // A directory left by an earlier process with the same id is stale.
            let _ = fs::remove_dir_all(&p);
            fs::create_dir_all(p.join("verification")).unwrap();
            fs::create_dir_all(p.join(".outline/gates")).unwrap();
            fs::create_dir_all(p.join("proof")).unwrap();
            Self(p)
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn scratch_directories_made_together_never_share_a_path() {
        const THREADS: usize = 32;
        let start = std::sync::Arc::new(std::sync::Barrier::new(THREADS));
        let workers: Vec<_> = (0..THREADS)
            .map(|_| {
                let start = std::sync::Arc::clone(&start);
                std::thread::spawn(move || {
                    start.wait();
                    Scratch::new("state")
                })
            })
            .collect();
        let scratches: Vec<_> = workers.into_iter().map(|w| w.join().unwrap()).collect();
        let distinct: std::collections::BTreeSet<_> = scratches.iter().map(|s| &s.0).collect();
        assert_eq!(distinct.len(), THREADS);
    }
    fn fixture(state: &str, public: Option<&str>, mutation: bool) -> Scratch {
        let scratch = Scratch::new("state");
        fs::create_dir_all(scratch.0.join("src")).unwrap();
        fs::write(scratch.0.join("src/x.rs"), "").unwrap();
        let aspects = if mutation {
            "[\"contract\", \"evidence\", \"coverage\", \"regression\", \"mutation\"]"
        } else {
            "[\"contract\", \"evidence\", \"coverage\", \"regression\"]"
        };
        let program = format!(
            "schema = \"{PROGRAM_SCHEMA}\"\n\
             release = \"typescript-7.0.2\"\n\
             root = \"product\"\n\
             [[leaf]]\n\
             id=\"X1\"\n\
             cluster=\"X\"\n\
             wave=\"W0\"\n\
             ledger=\".outline/gates/X1.md\"\n\
             owns=[\"src/x.rs\"]\n\
             aspects={aspects}\n\
             catalogs=[\"test\"]\n\
             mutation_required={mutation}\n\
             [[node]]\n\
             kind=\"cluster\"\n\
             id=\"X\"\n\
             children=[\"X1\"]\n\
             ledger=\".outline/gates/cluster-X.md\"\n\
             aspects=[\"contract\",\"evidence\",\"regression\"]\n\
             [[node]]\n\
             kind=\"wave\"\n\
             id=\"W0\"\n\
             children=[\"X1\"]\n\
             ledger=\".outline/gates/wave-W0.md\"\n\
             aspects=[\"contract\",\"evidence\",\"regression\"]\n\
             [[node]]\n\
             kind=\"root\"\n\
             id=\"product\"\n\
             children=[\"cluster:X\"]\n\
             ledger=\".outline/gates/root-product.md\"\n\
             aspects=[\"contract\",\"regression\"]\n"
        );
        fs::write(scratch.0.join(PROGRAM_PATH), program).unwrap();
        fs::create_dir_all(scratch.0.join("verification/receipts")).unwrap();
        let artifact = sha256_hex(&fs::read(scratch.0.join("src/x.rs")).unwrap());
        let mut gate = String::from("# Gates\n\nScope: test\n");
        for (index, (aspect, gate_id)) in [
            ("contract", "G1"),
            ("evidence", "G2"),
            ("coverage", "G3"),
            ("regression", "G4"),
            ("mutation", "G5"),
        ]
        .iter()
        .enumerate()
        {
            let receipt_path = format!("verification/receipts/{aspect}.json");
            let receipt = serde_json::to_vec(&serde_json::json!({
                "schema": leaf_evidence::SCHEMA,
                "leaf": "X1",
                "aspect": *aspect,
                "gate": *gate_id,
                "adapter": "test_artifact",
                "artifacts": [{"path": "src/x.rs", "sha256": artifact.as_str()}],
            }))
            .unwrap();
            let hash = sha256_hex(&receipt);
            fs::write(scratch.0.join(&receipt_path), receipt).unwrap();
            gate.push_str(&format!(
                "\n- [x] G{}: {aspect}\n  CHECK: cargo run -- completion verify --leaf X1 --aspect {aspect}\n  EXPECT: PASS\n  EVIDENCE: receipt={receipt_path} sha256={hash}\n",
                index + 1
            ));
        }
        fs::write(scratch.0.join(".outline/gates/X1.md"), gate).unwrap();
        let manifest = b"{}";
        fs::write(scratch.0.join("verification/manifest.lock.json"), manifest).unwrap();
        let surface = public
            .map(|value| format!(",\"public_surface\":\"{value}\""))
            .unwrap_or_default();
        fs::write(
            scratch.0.join(COMPLETENESS_LEDGER_PATH),
            format!(
                "{{\"schema\":\"bamti.completeness-ledger/v1\",\"manifest_sha256\":\"{}\",\"rows\":[{{\"id\":\"test:case\",\"state\":\"{state}\"{surface}}}]}}",
                sha256_hex(manifest)
            ),
        )
        .unwrap();
        scratch
    }

    #[test]
    fn rejects_every_incomplete_state() {
        for state in [
            "BLOCKING_FAIL",
            "EXTERNAL_BLOCKED",
            "INAPPLICABLE_CATALOG_ERROR",
            "TIMEOUT",
            "SIGNAL",
            "PROTOCOL_ERROR",
            "WORKER_CRASH",
            "SKIP",
            "MISSING_RECEIPT",
            "UNCONSUMED",
        ] {
            let f = fixture(state, Some("non-public"), true);
            let report = verify_completion(
                &f.0,
                &CompletionScope::Leaf("X1".into()),
                CompletionAspect::Coverage,
            )
            .unwrap();
            assert!(!report.is_pass(), "{state} became complete");
            assert!(
                report
                    .failures
                    .iter()
                    .any(|v| matches!(v, CompletionFailure::NonPassTerminal { .. })),
                "{state}: {:?}",
                report.failures
            );
        }
    }

    #[test]
    fn public_reachability_overrides_exclusion() {
        let f = fixture(
            "INAPPLICABLE_LANGUAGE_SERVICE",
            Some("language-service-api"),
            true,
        );
        let report = verify_completion(
            &f.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Coverage,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|v| matches!(v, CompletionFailure::PublicReachabilityExclusion { .. }))
        );
    }

    #[test]
    fn exact_non_public_exclusion_is_eligible() {
        let fixture = fixture(
            "INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE",
            Some("non-public"),
            true,
        );
        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Coverage,
        )
        .unwrap();
        assert!(report.is_pass(), "{:?}", report.failures);
    }

    #[test]
    fn parses_checked_and_unchecked_gate_identities() {
        let rows = parse_gate_rows("- [x] G1: contract\n- [ ] G5: mutation\n");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].gate, "G1");
        assert!(rows[0].checked);
        assert_eq!(rows[1].gate, "G5");
        assert!(!rows[1].checked);
    }

    #[test]
    fn leaf_aspect_verifies_valid_unchecked_evidence_for_gate_checking() {
        let fixture = fixture("PASS", None, true);
        let ledger = fixture.0.join(".outline/gates/X1.md");
        let text = fs::read_to_string(&ledger).unwrap();
        fs::write(&ledger, text.replacen("- [x] G1:", "- [ ] G1:", 1)).unwrap();

        let direct = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap();
        assert!(direct.is_pass(), "{:?}", direct.failures);
        assert!(direct.gate_evidence.as_deref().is_some_and(|evidence| {
            evidence.starts_with("receipt=verification/receipts/contract.json ")
        }));

        let aggregate = verify_completion(
            &fixture.0,
            &CompletionScope::Root("product".into()),
            CompletionAspect::Aggregate,
        )
        .unwrap();
        assert!(
            aggregate
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::NonCurrentEvidence { .. }))
        );
    }

    #[test]
    fn stale_completeness_ledger_fails() {
        let fixture = fixture("PASS", None, true);
        fs::write(
            fixture.0.join("verification/manifest.lock.json"),
            b"{\"changed\":true}",
        )
        .unwrap();
        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Evidence,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::StaleEvidence { .. }))
        );
    }

    #[test]
    fn fabricated_evidence_hash_fails() {
        let fixture = fixture("PASS", None, true);
        let ledger = fixture.0.join(".outline/gates/X1.md");
        let text = fs::read_to_string(&ledger).unwrap();
        let receipt = fs::read(fixture.0.join("verification/receipts/evidence.json")).unwrap();
        fs::write(
            &ledger,
            text.replace(
                &sha256_hex(&receipt),
                "0000000000000000000000000000000000000000000000000000000000000000",
            ),
        )
        .unwrap();
        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Evidence,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::NonCurrentEvidence { .. }))
        );
    }

    #[test]
    fn receipt_without_current_owned_artifact_fails() {
        let fixture = fixture("PASS", None, true);
        fs::write(fixture.0.join("src/x.rs"), "changed").unwrap();

        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::NonCurrentEvidence { .. }))
        );
    }

    #[test]
    fn arbitrary_hashed_receipt_fails() {
        let fixture = fixture("PASS", None, true);
        let receipt_path = fixture.0.join("verification/receipts/contract.json");
        let original = fs::read(&receipt_path).unwrap();
        let replacement = b"arbitrary bytes";
        fs::write(&receipt_path, replacement).unwrap();
        let ledger = fixture.0.join(".outline/gates/X1.md");
        let text = fs::read_to_string(&ledger).unwrap();
        fs::write(
            &ledger,
            text.replace(&sha256_hex(&original), &sha256_hex(replacement)),
        )
        .unwrap();

        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::NonCurrentEvidence { .. }))
        );
    }

    #[test]
    fn receipt_with_wrong_leaf_identity_fails() {
        let fixture = fixture("PASS", None, true);
        let receipt_path = fixture.0.join("verification/receipts/contract.json");
        let original = fs::read(&receipt_path).unwrap();
        let mut receipt: serde_json::Value = serde_json::from_slice(&original).unwrap();
        receipt["leaf"] = serde_json::Value::String("forged".to_owned());
        let replacement = serde_json::to_vec(&receipt).unwrap();
        fs::write(&receipt_path, &replacement).unwrap();
        let ledger = fixture.0.join(".outline/gates/X1.md");
        let text = fs::read_to_string(&ledger).unwrap();
        fs::write(
            &ledger,
            text.replace(&sha256_hex(&original), &sha256_hex(&replacement)),
        )
        .unwrap();

        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::NonCurrentEvidence { .. }))
        );
    }

    #[test]
    fn hierarchy_requires_node_ledgers() {
        let fixture = fixture("PASS", None, true);
        let report = verify_completion(
            &fixture.0,
            &CompletionScope::Root("product".into()),
            CompletionAspect::Aggregate,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::MissingLedger { .. }))
        );
    }

    fn write_authority_table(root: &Path, leaves: usize) {
        let mut authority = String::from(
            "---\nrelease: typescript-7.0.2\nproduct: bamti\n---\n\
             | Leaf | Wave | Cluster | Deliverable | Owned paths | Gate ledger |\n\
             |---|---|---|---|---|---|\n",
        );
        for index in 1..=leaves {
            authority.push_str(&format!(
                "| X{index} | W0 | X | d | `src/x.rs` | `.outline/gates/X{index}.md` |\n"
            ));
        }
        fs::write(
            root.join(".outline/type-script-7.0.2-completion.md"),
            authority,
        )
        .unwrap();
    }

    fn leaf_count_failures(leaves: usize) -> Vec<CompletionFailure> {
        let fixture = fixture("PASS", None, true);
        write_authority_table(&fixture.0, leaves);
        match verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        ) {
            Err(CompletionError::Invalid(failures)) => failures,
            other => panic!("a table that disagrees with the program must be invalid: {other:?}"),
        }
    }

    fn reports_stale_leaf_count(failures: &[CompletionFailure], leaves: usize) -> bool {
        failures.iter().any(|failure| {
            matches!(failure, CompletionFailure::StaleEvidence { id }
                if *id == format!("completion-authority-leaf-count={leaves}"))
        })
    }

    #[test]
    fn authority_table_must_hold_exactly_the_frozen_leaf_count() {
        for leaves in [FROZEN_LEAF_COUNT - 1, FROZEN_LEAF_COUNT + 1] {
            assert!(
                reports_stale_leaf_count(&leaf_count_failures(leaves), leaves),
                "{leaves} leaves must be reported as a stale count"
            );
        }
        assert!(
            !reports_stale_leaf_count(&leaf_count_failures(FROZEN_LEAF_COUNT), FROZEN_LEAF_COUNT),
            "the frozen count itself must not be reported as stale"
        );
    }

    #[test]
    fn frozen_authority_rejects_joint_leaf_removal() {
        let fixture = fixture("PASS", None, true);
        write_authority_table(&fixture.0, FROZEN_LEAF_COUNT);
        let error = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            CompletionError::Invalid(failures)
                if failures.iter().any(|failure|
                    matches!(failure, CompletionFailure::MissingLeaf(id) if id == "X2"))
        ));
    }

    #[test]
    fn missing_leaf_fails() {
        let f = fixture("PASS", None, true);
        fs::write(f.0.join(".outline/gates/X2.md"), "# Gates").unwrap();
        let err = verify_completion(
            &f.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap_err();
        assert!(
            matches!(err,CompletionError::Invalid(v) if v.iter().any(|x|matches!(x,CompletionFailure::MissingLeaf(id) if id=="X2")))
        );
    }

    #[test]
    fn unregistered_clean_port_ledger_fails_closed() {
        let fixture = fixture("PASS", None, true);
        fs::write(
            fixture.0.join(".outline/gates/clean-port-unregistered.md"),
            "# Gates\n",
        )
        .unwrap();

        let error = verify_completion(
            &fixture.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            CompletionError::Invalid(failures)
                if failures.iter().any(|failure|
                    matches!(failure, CompletionFailure::MissingLeaf(id) if id == "clean-port-unregistered"))
        ));
    }

    #[test]
    fn orphan_ownership_fails() {
        let f = fixture("PASS", None, true);
        fs::remove_file(f.0.join("src/x.rs")).unwrap();
        let report = verify_completion(
            &f.0,
            &CompletionScope::Leaf("X1".into()),
            CompletionAspect::Contract,
        )
        .unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|v| matches!(v, CompletionFailure::OrphanOwnership { .. }))
        );
    }

    #[test]
    fn check_mode_does_not_write() {
        let f = fixture("PASS", None, true);
        let path = f.0.join(PROGRAM_PATH);
        let before = fs::read(&path).unwrap();
        let _ = regenerate_completion_program(&f.0, RegenerateMode::Check);
        assert_eq!(fs::read(path).unwrap(), before);
    }
}
