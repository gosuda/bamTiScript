//! Strict, fail-closed completion over the frozen TypeScript-product program.
//!
//! The program is an explicit closed set. Verification never discovers extra
//! scope on behalf of a worker: the generated completeness ledger is an
//! observation checked against that set.

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

use crate::{ErrorCode, VerificationError, rebuild::LEDGER_SCHEMA, schema::sha256_hex};

const PROGRAM_PATH: &str = "verification/completion-program.toml";
const COMPLETENESS_LEDGER_PATH: &str = "proof/completeness-ledger.json";
const PROGRAM_SCHEMA: &str = "bamti.completion-program/v2";
static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompletionScope {
    Leaf(String),
    Cluster(String),
    Root(String),
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
}

impl fmt::Display for CompletionFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownScope { kind, id } => write!(f, "unknown {kind} `{id}`"),
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
            Self::StaleEvidence { id } => write!(f, "scope `{id}` has stale evidence"),
            Self::NonPassTerminal { obligation, state } => {
                write!(f, "obligation `{obligation}` is `{state}`, not PASS")
            }
            Self::PublicReachabilityExclusion { obligation, state } => write!(
                f,
                "public obligation `{obligation}` cannot be excluded as `{state}`"
            ),
            Self::MissingReceipt { id } => write!(f, "scope `{id}` has no matching receipt"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionReport {
    pub scope: CompletionScope,
    pub checked_leaves: usize,
    pub checked_obligations: usize,
    pub failures: Vec<CompletionFailure>,
}

impl CompletionReport {
    pub fn is_pass(&self) -> bool {
        self.failures.is_empty()
    }

    pub fn success_line(&self) -> Option<String> {
        if !self.is_pass() {
            return None;
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
                Some("NATIVE COMPLETE formal=PASS".into())
            }
            CompletionScope::Root(id) if id == "package" => {
                Some("PACKAGE COMPLETE exports=13 cli=PASS api=PASS".into())
            }
            CompletionScope::Root(id) if id == "product" => Some(
                "PRODUCT COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0 catalog_errors=0".into(),
            ),
            CompletionScope::Leaf(id) => Some(format!("LEAF {id} COMPLETE")),
            CompletionScope::Cluster(id) => Some(format!("CLUSTER {id} COMPLETE")),
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
    owns: Vec<String>,
    catalogs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct Node {
    kind: String,
    id: String,
    children: Vec<String>,
}

pub fn verify_completion(
    root: &Path,
    scope: &CompletionScope,
) -> Result<CompletionReport, CompletionError> {
    let program = load_program(root)?;
    let structural = validate_program(&program);
    if !structural.is_empty() {
        return Err(CompletionError::Invalid(structural));
    }

    let leaves = resolve_scope(&program, scope)?;
    let mut failures = Vec::new();
    for leaf in &leaves {
        verify_ownership(root, leaf, &mut failures);
    }
    let checked_obligations = verify_obligations(root, &leaves, &mut failures)?;

    failures.sort_by_key(ToString::to_string);
    failures.dedup();
    Ok(CompletionReport {
        scope: scope.clone(),
        checked_leaves: leaves.len(),
        checked_obligations,
        failures,
    })
}

pub fn regenerate_completion_program(
    root: &Path,
    mode: RegenerateMode,
) -> Result<RegenerateOutcome, CompletionError> {
    let path = root.join(PROGRAM_PATH);
    let program = load_program(root)?;
    let failures = validate_program(&program);
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

fn validate_program(p: &Program) -> Vec<CompletionFailure> {
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
    }
    for node in &p.node {
        for child in &node.children {
            let qualified = if child.contains(':') {
                child.clone()
            } else if node.kind.as_str() == "cluster" {
                format!("leaf:{child}")
            } else {
                String::new()
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
        } else if kind == "cluster" {
            out.insert(child.clone());
        } else {
            return Err(CompletionError::Invalid(vec![
                CompletionFailure::HierarchyGap {
                    parent: format!("{kind}:{id}"),
                    child: child.clone(),
                },
            ]));
        }
    }
    Ok(())
}
fn scope_kind(kind: &str) -> &'static str {
    match kind {
        "cluster" => "cluster",
        "root" => "root",
        _ => "node",
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
                    schema_current = map.next_value::<String>()? == LEDGER_SCHEMA;
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
        s.push_str(&format!(
            "id = {:?}\ncluster = {:?}\nowns = {}\ncatalogs = {}\n\n",
            l.id,
            l.cluster,
            strings(&l.owns),
            strings(&l.catalogs)
        ));
    }
    for n in &p.node {
        s.push_str("[[node]]\n");
        s.push_str(&format!(
            "kind = {:?}\nid = {:?}\nchildren = {}\n\n",
            n.kind,
            n.id,
            strings(&n.children)
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
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let p = std::env::temp_dir().join(format!(
                "bamts-completion-{name}-{}-{}",
                process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let _ = fs::remove_dir_all(&p);
            fs::create_dir_all(p.join("verification")).unwrap();
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
    fn fixture(state: &str, public: Option<&str>) -> Scratch {
        let scratch = Scratch::new("state");
        fs::create_dir_all(scratch.0.join("src")).unwrap();
        fs::write(scratch.0.join("src/x.rs"), "").unwrap();
        let program = format!(
            "schema = \"{PROGRAM_SCHEMA}\"\n\
             release = \"typescript-7.0.2\"\n\
             root = \"product\"\n\
             [[leaf]]\n\
             id = \"X1\"\n\
             cluster = \"X\"\n\
             owns = [\"src/x.rs\"]\n\
             catalogs = [\"test\"]\n\
             [[node]]\n\
             kind = \"cluster\"\n\
             id = \"X\"\n\
             children = [\"X1\"]\n\
             [[node]]\n\
             kind = \"root\"\n\
             id = \"product\"\n\
             children = [\"cluster:X\"]\n"
        );
        fs::write(scratch.0.join(PROGRAM_PATH), program).unwrap();
        let manifest = b"{}";
        fs::write(scratch.0.join("verification/manifest.lock.json"), manifest).unwrap();
        let surface = public
            .map(|value| format!(",\"public_surface\":\"{value}\""))
            .unwrap_or_default();
        fs::write(
            scratch.0.join(COMPLETENESS_LEDGER_PATH),
            format!(
                "{{\"schema\":\"bamti.completeness-ledger/v2\",\"manifest_sha256\":\"{}\",\"rows\":[{{\"id\":\"test:case\",\"state\":\"{state}\"{surface}}}]}}",
                sha256_hex(manifest)
            ),
        )
        .unwrap();
        scratch
    }

    fn program_text(scratch: &Scratch) -> String {
        fs::read_to_string(scratch.0.join(PROGRAM_PATH)).unwrap()
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
            let f = fixture(state, Some("non-public"));
            let report = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap();
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
        );
        let report = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|v| matches!(v, CompletionFailure::PublicReachabilityExclusion { .. }))
        );
    }

    #[test]
    fn exact_non_public_exclusion_is_eligible() {
        let fixture = fixture("INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE", Some("non-public"));
        let report = verify_completion(&fixture.0, &CompletionScope::Leaf("X1".into())).unwrap();
        assert!(report.is_pass(), "{:?}", report.failures);
    }

    #[test]
    fn stale_completeness_ledger_fails() {
        let fixture = fixture("PASS", None);
        fs::write(
            fixture.0.join("verification/manifest.lock.json"),
            b"{\"changed\":true}",
        )
        .unwrap();
        let report = verify_completion(&fixture.0, &CompletionScope::Leaf("X1".into())).unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|failure| matches!(failure, CompletionFailure::StaleEvidence { .. }))
        );
    }

    #[test]
    fn orphan_ownership_fails() {
        let f = fixture("PASS", None);
        fs::remove_file(f.0.join("src/x.rs")).unwrap();
        let report = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|v| matches!(v, CompletionFailure::OrphanOwnership { .. }))
        );
    }

    #[test]
    fn duplicate_leaf_fails() {
        let f = fixture("PASS", None);
        let mut text = program_text(&f);
        text.push_str(
            "[[leaf]]\nid = \"X1\"\ncluster = \"X\"\nowns = [\"src/dup.rs\"]\ncatalogs = []\n\n",
        );
        fs::write(f.0.join(PROGRAM_PATH), text).unwrap();
        let error = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap_err();
        assert!(
            matches!(error, CompletionError::Invalid(v) if v.iter().any(|x| matches!(x, CompletionFailure::DuplicateLeaf(id) if id == "X1")))
        );
    }

    #[test]
    fn ownership_conflict_fails() {
        let f = fixture("PASS", None);
        let mut text = program_text(&f);
        text.push_str(
            "[[leaf]]\nid = \"X2\"\ncluster = \"X\"\nowns = [\"src/x.rs\"]\ncatalogs = []\n\n",
        );
        fs::write(f.0.join(PROGRAM_PATH), text).unwrap();
        let error = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap_err();
        assert!(
            matches!(error, CompletionError::Invalid(v) if v.iter().any(|x| matches!(x, CompletionFailure::OwnershipConflict { .. })))
        );
    }

    #[test]
    fn hierarchy_gap_fails() {
        let f = fixture("PASS", None);
        let text = program_text(&f).replace("cluster = \"X\"\nowns", "cluster = \"Missing\"\nowns");
        fs::write(f.0.join(PROGRAM_PATH), text).unwrap();
        let error = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap_err();
        assert!(
            matches!(error, CompletionError::Invalid(v) if v.iter().any(|x| matches!(x, CompletionFailure::HierarchyGap { .. })))
        );
    }

    #[test]
    fn unknown_scope_fails() {
        let f = fixture("PASS", None);
        let error = verify_completion(&f.0, &CompletionScope::Leaf("Nope".into())).unwrap_err();
        assert!(
            matches!(error, CompletionError::Invalid(v) if v.iter().any(|x| matches!(x, CompletionFailure::UnknownScope { .. })))
        );
        let error = verify_completion(&f.0, &CompletionScope::Cluster("Nope".into())).unwrap_err();
        assert!(
            matches!(error, CompletionError::Invalid(v) if v.iter().any(|x| matches!(x, CompletionFailure::UnknownScope { .. })))
        );
    }

    #[test]
    fn missing_receipt_fails() {
        let f = fixture("PASS", None);
        let manifest = fs::read(f.0.join("verification/manifest.lock.json")).unwrap();
        fs::write(
            f.0.join(COMPLETENESS_LEDGER_PATH),
            format!(
                "{{\"schema\":\"bamti.completeness-ledger/v2\",\"manifest_sha256\":\"{}\",\"rows\":[]}}",
                sha256_hex(&manifest)
            ),
        )
        .unwrap();
        let report = verify_completion(&f.0, &CompletionScope::Leaf("X1".into())).unwrap();
        assert!(
            report
                .failures
                .iter()
                .any(|v| matches!(v, CompletionFailure::MissingReceipt { .. }))
        );
    }

    #[test]
    fn check_mode_does_not_write() {
        let f = fixture("PASS", None);
        let path = f.0.join(PROGRAM_PATH);
        let before = fs::read(&path).unwrap();
        let _ = regenerate_completion_program(&f.0, RegenerateMode::Check);
        assert_eq!(fs::read(path).unwrap(), before);
    }

    #[test]
    fn check_mismatch_fails() {
        let f = fixture("PASS", None);
        let path = f.0.join(PROGRAM_PATH);
        let mut text = fs::read_to_string(&path).unwrap();
        text.push_str("# drift\n");
        fs::write(&path, text).unwrap();
        assert!(matches!(
            regenerate_completion_program(&f.0, RegenerateMode::Check),
            Err(CompletionError::CheckMismatch { .. })
        ));
    }
}
