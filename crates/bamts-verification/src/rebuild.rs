//! Deterministic evidence-derived completeness-ledger rebuild.
//!
//! The ledger is a projection of exactly three inputs: the canonical manifest,
//! the current receipts, and exact policy prose for non-PASS rows.  Nothing
//! else may influence a row, and no row may be minted without a receipt that
//! binds the run.
//!
//! `PASS` is admitted only when a receipt carries the exact obligation key and
//! every observable the manifest identity declares, with a digest for each.  A
//! forged row, a row for an unknown obligation, a duplicated receipt, a stale
//! run binding, or a missing receipt is a rejection, and a rejection never
//! publishes.
//!
//! One ledger row is one manifest identifier.  A receipt names it by lane key,
//! and an identifier is proven in every mode its catalog declares: `test262`
//! needs the interpreter, JIT, and AOT to agree, so its row settles only when
//! all three have reported the same state.
//!
//! Memory is one receipt row, one ledger row, and bounded per-obligation
//! outcome state.  The ledger document is never materialized as a value tree.
//! Publication streams into a sibling temporary file and renames it only after
//! every late check has passed, so a malformed input, a write failure, or an
//! interruption leaves the previous publication byte-for-byte intact.  Check
//! mode compares digests and never touches the destination.

use std::{
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
    fmt,
    fs::{self, File},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    process,
    sync::atomic::{AtomicU64, Ordering},
};

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::{
    ErrorCode, Result, VerificationError,
    catalog::{extract_test262_cells, extract_typescript_cells},
    classification::{ClassificationState, NonPassState, load_classifications},
    evidence::{EvidenceReader, EvidenceRow, RunBinding, TerminalState},
    schema::{
        MANIFEST_PATH, VerificationManifest, load_sources, parse_json, read_bytes, sha256_hex,
        validate_manifest,
    },
    shard::{ExecutionMode, ObligationKey},
    suite::completion::{current_run_bindings, logical_obligation, required_modes},
};

/// Canonical published ledger, relative to the repository root.
pub const LEDGER_PATH: &str = "proof/completeness-ledger.json";
/// Legacy canonical receipt-set directory.
pub const RECEIPTS_DIR: &str = "verification/receipts";
/// Exact, non-recursive receipt-set owners. A rebuild consumes exactly one
/// populated directory; combining roots would mix independent workflow runs.
/// The same list defines the generated-run-output boundary shared by receipt
/// discovery and the candidate-source projection, so the two can never drift
/// apart.
pub(crate) const RECEIPT_SET_DIRS: [&str; 5] = [
    RECEIPTS_DIR,
    "verification/evidence/pr-merged",
    "verification/evidence/nightly-merged",
    "verification/evidence/release",
    "verification/evidence/typescript-7.0.2",
];

/// Whether one canonical repository-relative Git path is a generated run
/// output rather than candidate source.
///
/// The generated-output boundary is byte-exact and closed:
///
/// 1. exactly `proof/completeness-ledger.json`;
/// 2. immediate children with the case-sensitive `.jsonl` suffix of exactly
///    the directories in [`RECEIPT_SET_DIRS`].
///
/// `path` is the raw Git path as Git enumerates it (no filesystem
/// canonicalization, no symlink resolution, no Unicode rewriting): matching
/// is `&[u8]` equality so non-UTF-8 paths can never decode into an allowed
/// name. Prefix lookalikes stay source: a nested file
/// (`<owner>/sub/a.jsonl`), a sibling directory (`release-extra/a.jsonl`),
/// a different suffix (`.json`, `.jsonl.tmp`, `foo.jsonl.rs`), and a
/// different case (`.JSONL`) all return `false`. Nothing outside this
/// allowlist is ever exempt — toolchain JSON, the locked manifest,
/// classification, source locks, formal material, `.gitignore`, Cargo files,
/// and raw shards remain candidate source.
///
/// This predicate answers the path question only. Every caller must also
/// enforce the file kind: the committed-tree projection excludes an allowed
/// path only when it is a regular blob (mode `100644`/`100755`), and the
/// dirty gate permits an allowed path only when the worktree entry is a
/// regular file. A symlink, submodule, or directory standing at an allowed
/// path is therefore never exempt — it stays bound in candidate identity and
/// cannot hide source.
pub(crate) fn is_generated_run_output(path: &[u8]) -> bool {
    if path == LEDGER_PATH.as_bytes() {
        return true;
    }
    for dir in RECEIPT_SET_DIRS {
        if let Some(name) = path
            .strip_prefix(dir.as_bytes())
            .and_then(|suffix| suffix.strip_prefix(b"/"))
            && !name.contains(&b'/')
            && name.ends_with(b".jsonl")
        {
            return true;
        }
    }
    false
}

/// Schema tag the G0 ledger verifier requires.
pub const LEDGER_SCHEMA: &str = "bamti.completeness-ledger/v2";

/// Closed ledger state vocabulary, in canonical declaration order.
pub const LEDGER_STATES: [&str; 7] = [
    "PASS",
    "BLOCKING_FAIL",
    "INAPPLICABLE_LANGUAGE_SERVICE",
    "INAPPLICABLE_OUT_OF_SCOPE_HOST_FEATURE",
    "INAPPLICABLE_V8_INTERNAL",
    "INAPPLICABLE_CATALOG_ERROR",
    "EXTERNAL_BLOCKED",
];

/// GitHub refuses a blob at or above 100 MiB; the published ledger must stay
/// below it without splitting or weakening closure.
pub const MAX_LEDGER_BYTES: u64 = 100 * 1024 * 1024;

/// A single row far larger than any legitimate identity indicates a corrupt
/// projection rather than a large catalog.
const MAX_ROW_BYTES: usize = 4096;

static TEMP_NONCE: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
thread_local! {
    static FAIL_PUBLICATION_AFTER_TEMP_CREATE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Replace the published ledger or compare against it without mutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RebuildMode {
    Write,
    Check,
}

impl RebuildMode {
    #[must_use]
    pub const fn writes(self) -> bool {
        matches!(self, Self::Write)
    }
}

/// Exact prose a non-PASS ledger row must carry.  Policy owns these strings;
/// the rebuild never invents them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerProse {
    pub citation: String,
    pub owner: String,
    pub reason: String,
    pub matcher: String,
}

impl LedgerProse {
    fn validate(&self, row_id: &str) -> Result<()> {
        for (field, value) in [
            ("citation", &self.citation),
            ("owner", &self.owner),
            ("reason", &self.reason),
            ("matcher", &self.matcher),
        ] {
            if value.trim().is_empty() {
                return Err(VerificationError::new(
                    ErrorCode::Transition,
                    format!("non-PASS row `{row_id}` has empty `{field}`"),
                ));
            }
        }
        Ok(())
    }
}

/// Why one obligation cannot be projected into a green ledger row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RejectionReason {
    /// No receipt recorded this obligation in a mode its catalog requires.
    MissingReceipt { mode: ExecutionMode },
    /// A receipt named an obligation the manifest does not declare.
    UnknownObligation,
    /// Two receipts recorded the same obligation and run coordinates.
    DuplicateReceipt,
    /// The modes of one obligation reported different states.
    ModeDisagreement { states: String },
    /// A PASS row did not declare exactly the identity's observables.
    ObservableMismatch { expected: String, actual: String },
    /// A receipt declared an observable without a digest.
    MissingObservableDigest { observable: String },
    /// A receipt's run binding disagrees with the expected binding.
    StaleBinding { field: String },
    /// A receipt's catalog is absent from the canonical manifest.
    UnknownCatalog { catalog: String },
    /// Rows within one evidence document name different catalogs.
    ReceiptCatalogMismatch { expected: String, actual: String },
    /// An empty receipt has no row catalog with which to select a binding.
    UnscopedReceipt,
    /// A receipt state disagrees with the exact classification policy.
    ClassificationMismatch { expected: String, actual: String },
    /// A non-PASS state that cannot appear in a complete ledger.
    BlockingState { state: TerminalState },
    /// A non-PASS state was recorded without exact policy prose.
    MissingPolicyProse { state: TerminalState },
}

impl fmt::Display for RejectionReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingReceipt { mode } => {
                write!(
                    formatter,
                    "no {} receipt recorded this obligation",
                    mode.as_str()
                )
            }
            Self::UnknownObligation => {
                formatter.write_str("receipt names an obligation the manifest does not declare")
            }
            Self::DuplicateReceipt => formatter.write_str("duplicate receipt for one obligation"),
            Self::ModeDisagreement { states } => {
                write!(formatter, "modes disagree on this obligation: {states}")
            }
            Self::ObservableMismatch { expected, actual } => write!(
                formatter,
                "PASS declares observables `{actual}` instead of `{expected}`"
            ),
            Self::MissingObservableDigest { observable } => {
                write!(
                    formatter,
                    "observable `{observable}` has no artifact digest"
                )
            }
            Self::StaleBinding { field } => {
                write!(formatter, "run binding field `{field}` is stale")
            }
            Self::UnknownCatalog { catalog } => {
                write!(formatter, "receipt names unknown catalog `{catalog}`")
            }
            Self::ReceiptCatalogMismatch { expected, actual } => write!(
                formatter,
                "receipt mixes catalog `{actual}` into document for `{expected}`"
            ),
            Self::UnscopedReceipt => {
                formatter.write_str("empty receipt cannot select a catalog binding")
            }
            Self::ClassificationMismatch { expected, actual } => write!(
                formatter,
                "receipt state `{actual}` disagrees with classification `{expected}`"
            ),
            Self::BlockingState { state } => {
                write!(formatter, "state `{}` is not complete", state.as_str())
            }
            Self::MissingPolicyProse { state } => write!(
                formatter,
                "state `{}` has no exact policy record",
                state.as_str()
            ),
        }
    }
}

/// One rejected obligation.  A rebuild with any rejection publishes nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RebuildRejection {
    pub row_id: String,
    pub reason: RejectionReason,
}

impl fmt::Display for RebuildRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.row_id, self.reason)
    }
}

/// Outcome of one rebuild.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RebuildReport {
    pub mode: RebuildMode,
    pub ledger_path: PathBuf,
    /// Obligations the manifest declares.
    pub obligations: usize,
    /// Receipt rows consumed from the supplied documents.
    pub receipts_consumed: usize,
    /// SHA-256 of the projected ledger bytes.
    pub ledger_digest: String,
    /// Byte length of the projected ledger.
    pub bytes: u64,
    /// Whether the projection differs from the published ledger.
    pub changed: bool,
    /// Peak number of ledger rows held in memory at once.
    pub max_live_rows: usize,
    pub rejections: Vec<RebuildRejection>,
}

impl RebuildReport {
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.rejections.is_empty()
    }
}

/// One declared obligation and the observables its identity requires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationSlot {
    catalog: String,
    identifier: String,
    modes: Vec<ExecutionMode>,
    platform: String,
    observables: BTreeSet<String>,
    classification: Option<ClassificationState>,
}

/// Canonical obligation universe, ordered by ledger row id.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObligationIndex {
    slots: BTreeMap<String, ObligationSlot>,
    /// The row each lane cell proves.  Mode and platform are not part of a cell:
    /// they are checked against the slot, so a wrong one reads as stale.
    rows: BTreeMap<String, String>,
}

/// A lane cell as one string.  Key tokens cannot contain NUL, so this is injective.
fn lane_cell(key: &ObligationKey) -> String {
    format!("{}\0{}\0{}", key.catalog(), key.case(), key.configuration())
}

impl ObligationIndex {
    /// Builds the index from manifest row ids of the form `catalog:identifier`.
    pub fn from_row_ids(row_ids: &BTreeSet<String>) -> Result<Self> {
        let platform = bamts_platform::host_triple();
        let mut slots = BTreeMap::new();
        let mut rows = BTreeMap::new();
        for row_id in row_ids {
            let (catalog, identifier) = row_id.split_once(':').ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::Schema,
                    format!("manifest row `{row_id}` is not `catalog:identifier`"),
                )
            })?;
            if catalog.is_empty() || identifier.is_empty() {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("manifest row `{row_id}` has an empty component"),
                ));
            }
            let modes = required_modes(catalog)?;
            let obligation = logical_obligation(catalog, identifier, modes[0], &platform)?;
            if rows
                .insert(lane_cell(&obligation.key), row_id.clone())
                .is_some()
            {
                return Err(VerificationError::new(
                    ErrorCode::SetMismatch,
                    format!("manifest row `{row_id}` shares a lane key with another row"),
                ));
            }
            slots.insert(
                row_id.clone(),
                ObligationSlot {
                    catalog: catalog.to_owned(),
                    identifier: identifier.to_owned(),
                    modes,
                    platform: platform.clone(),
                    observables: obligation.observables,
                    classification: None,
                },
            );
        }
        Ok(Self { slots, rows })
    }

    /// The manifest row a receipt key proves, if it proves one.
    fn resolve(&self, key: &ObligationKey) -> Option<(&str, &ObligationSlot)> {
        let row_id = self.rows.get(&lane_cell(key))?;
        Some((row_id, self.slots.get(row_id)?))
    }

    fn attach_classifications(
        &mut self,
        classifications: BTreeMap<String, ClassificationState>,
    ) -> Result<()> {
        const CLASSIFIED_CATALOGS: [&str; 4] = [
            "typescript-7.0.2",
            "typescript-6.0.2",
            "typescript-5.9.3",
            "test262",
        ];
        for (identifier, state) in classifications {
            let catalog = identifier.split('/').next().ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::Schema,
                    format!("classification `{identifier}` has no catalog authority"),
                )
            })?;
            let row_id = format!("{catalog}:{identifier}");
            let slot = self.slots.get_mut(&row_id).ok_or_else(|| {
                VerificationError::new(
                    ErrorCode::SetMismatch,
                    format!("classification names unknown manifest obligation `{row_id}`"),
                )
            })?;
            slot.classification = Some(state);
        }
        if let Some((row_id, _)) = self.slots.iter().find(|(_, slot)| {
            CLASSIFIED_CATALOGS.contains(&slot.catalog.as_str()) && slot.classification.is_none()
        }) {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                format!("manifest obligation `{row_id}` has no exact classification"),
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    #[must_use]
    pub fn catalogs(&self) -> BTreeSet<String> {
        self.slots
            .values()
            .map(|slot| slot.catalog.clone())
            .collect()
    }
}

/// Rebuilds the ledger from the manifest and the supplied receipts.
pub fn rebuild_ledger(
    root: &Path,
    receipts: &[PathBuf],
    mode: RebuildMode,
) -> Result<RebuildReport> {
    let (index, manifest_sha256) = load_projection_inputs(root)?;
    let bindings = current_run_bindings(root, &index.catalogs())?;
    rebuild_projection(
        root,
        &index,
        &manifest_sha256,
        receipts,
        mode,
        &bindings,
        &BTreeMap::new(),
    )
}

/// Rebuilds with exact policy prose for non-PASS rows.
pub fn rebuild_ledger_with_policies(
    root: &Path,
    receipts: &[PathBuf],
    mode: RebuildMode,
    prose: &BTreeMap<String, LedgerProse>,
) -> Result<RebuildReport> {
    let (index, manifest_sha256) = load_projection_inputs(root)?;
    let bindings = current_run_bindings(root, &index.catalogs())?;
    rebuild_projection(
        root,
        &index,
        &manifest_sha256,
        receipts,
        mode,
        &bindings,
        prose,
    )
}

/// Discovers one current canonical receipt set and rebuilds or checks the
/// ledger. This is the entry point behind `completion regenerate [--check]`.
pub fn regenerate_completion(root: &Path, mode: RebuildMode) -> Result<RebuildReport> {
    let receipts = discover_receipts(root)?;
    rebuild_ledger(root, &receipts, mode)
}

/// Sorted immediate `*.jsonl` receipts from exactly one canonical owner.
pub fn discover_receipts(root: &Path) -> Result<Vec<PathBuf>> {
    let mut populated = Vec::new();
    for relative in RECEIPT_SET_DIRS {
        let directory = root.join(relative);
        let names = receipt_names(&directory)?;
        if !names.is_empty() {
            populated.push((directory, names));
        }
    }

    match populated.as_slice() {
        [] => Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "no canonical receipt set found; expected exactly one populated directory among {}",
                RECEIPT_SET_DIRS.join(", ")
            ),
        )),
        [(directory, names)] => Ok(names.iter().map(|name| directory.join(name)).collect()),
        owners => Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "multiple canonical receipt sets are populated: {}",
                owners
                    .iter()
                    .map(|(directory, _)| directory.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        )),
    }
}

fn receipt_names(directory: &Path) -> Result<BTreeSet<String>> {
    if !directory.exists() {
        return Ok(BTreeSet::new());
    }
    if !directory.is_dir() {
        return Err(VerificationError::new(
            ErrorCode::Io,
            format!("{} is not a receipts directory", directory.display()),
        ));
    }

    let mut names = BTreeSet::new();
    for entry in fs::read_dir(directory).map_err(|error| io_path(directory, error))? {
        let entry = entry.map_err(|error| io_path(directory, error))?;
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| io_path(&path, error))?;
        let name = entry.file_name().into_string().map_err(|_| {
            VerificationError::new(
                ErrorCode::Schema,
                format!("{} contains a non-UTF-8 receipt name", directory.display()),
            )
        })?;
        if !file_type.is_file() || !name.ends_with(".jsonl") {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                format!(
                    "{} contains unexpected receipt entry `{name}`",
                    directory.display()
                ),
            ));
        }
        names.insert(name);
    }
    Ok(names)
}

fn load_projection_inputs(root: &Path) -> Result<(ObligationIndex, String)> {
    let (sources, source_ledger_sha256) = load_sources(root)?;
    let manifest_path = root.join(MANIFEST_PATH);
    let manifest_bytes = read_bytes(&manifest_path)?;
    let manifest_sha256 = sha256_hex(&manifest_bytes);
    let manifest: VerificationManifest = parse_json(&manifest_path, &manifest_bytes)?;
    let row_ids = validate_manifest(&manifest, &manifest_path, &source_ledger_sha256, &sources)?;
    let mut index = ObligationIndex::from_row_ids(&row_ids)?;

    let mut universes = BTreeMap::new();
    for (catalog, relative_root) in [
        (
            "typescript-7.0.2",
            "target/authority/typescript-7.0.2-tests",
        ),
        (
            "typescript-6.0.2",
            "target/authority/typescript-6.0.2-tests",
        ),
        (
            "typescript-5.9.3",
            "target/authority/typescript-5.9.3-tests",
        ),
    ] {
        universes.insert(
            catalog.to_owned(),
            extract_typescript_cells(&root.join(relative_root), catalog)?,
        );
    }
    universes.insert(
        "test262".to_owned(),
        extract_test262_cells(&root.join("target/authority/test262"), "test262")?,
    );
    index.attach_classifications(load_classifications(root, &universes)?)?;

    Ok((index, manifest_sha256))
}

/// One obligation's recorded outcome. Bounded: a state plus one rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Outcome {
    state: TerminalState,
    rejection: Option<RejectionReason>,
}

/// Every mode one obligation has reported in, including any it should not have.
type ModeOutcomes = BTreeMap<ExecutionMode, Outcome>;

/// The state one row publishes.  It needs every required mode to have reported,
/// nothing rejected, and all modes in agreement.
fn settled_state(slot: &ObligationSlot, recorded: &ModeOutcomes) -> Option<TerminalState> {
    let complete = slot.modes.iter().all(|mode| recorded.contains_key(mode));
    if !complete || recorded.values().any(|outcome| outcome.rejection.is_some()) {
        return None;
    }
    let mut states = recorded.values().map(|outcome| outcome.state);
    let first = states.next()?;
    states.all(|state| state == first).then_some(first)
}

pub(crate) fn rebuild_projection(
    root: &Path,
    index: &ObligationIndex,
    manifest_sha256: &str,
    receipts: &[PathBuf],
    mode: RebuildMode,
    expected_bindings: &BTreeMap<String, RunBinding>,
    prose: &BTreeMap<String, LedgerProse>,
) -> Result<RebuildReport> {
    if index.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "cannot project a ledger for an empty obligation universe",
        ));
    }
    if receipts.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "ledger rebuild requires at least one receipt",
        ));
    }

    let ledger_path = root.join(LEDGER_PATH);
    let mut outcomes: BTreeMap<String, ModeOutcomes> = BTreeMap::new();
    let mut rejections: Vec<RebuildRejection> = Vec::new();
    let mut receipts_consumed = 0usize;
    let catalogs = index.catalogs();
    if expected_bindings.keys().ne(catalogs.iter()) {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "expected run bindings do not exactly cover the manifest catalogs",
        ));
    }

    for receipt in receipts {
        let mut reader = EvidenceReader::open(receipt)?;
        let header_binding = reader.header().binding().clone();
        let Some(first_row) = reader.next_row()? else {
            reader.finish()?;
            rejections.push(RebuildRejection {
                row_id: receipt_label(receipt),
                reason: RejectionReason::UnscopedReceipt,
            });
            continue;
        };
        let document_catalog = first_row.key().catalog().to_owned();
        let expected_binding = expected_bindings.get(&document_catalog);
        let mut document_admitted = true;
        match expected_binding {
            None => {
                document_admitted = false;
                rejections.push(RebuildRejection {
                    row_id: receipt_label(receipt),
                    reason: RejectionReason::UnknownCatalog {
                        catalog: document_catalog.clone(),
                    },
                });
            }
            Some(expected) => {
                if let Some(field) = expected.first_mismatch_field(&header_binding) {
                    document_admitted = false;
                    rejections.push(RebuildRejection {
                        row_id: receipt_label(receipt),
                        reason: RejectionReason::StaleBinding {
                            field: field.to_owned(),
                        },
                    });
                }
            }
        }

        let mut row = Some(first_row);
        while let Some(current) = row {
            receipts_consumed += 1;
            if current.key().catalog() != document_catalog {
                rejections.push(RebuildRejection {
                    row_id: row_id_for(current.key()),
                    reason: RejectionReason::ReceiptCatalogMismatch {
                        expected: document_catalog.clone(),
                        actual: current.key().catalog().to_owned(),
                    },
                });
            } else if document_admitted {
                record_outcome(index, &mut outcomes, &mut rejections, &current);
            }
            row = reader.next_row()?;
        }
        reader.finish()?;
    }

    for (row_id, slot) in &index.slots {
        let recorded = outcomes.entry(row_id.clone()).or_default();
        let before = rejections.len();
        let mut reject = |reason: RejectionReason| {
            rejections.push(RebuildRejection {
                row_id: row_id.clone(),
                reason,
            });
        };
        for mode in &slot.modes {
            if !recorded.contains_key(mode) {
                reject(RejectionReason::MissingReceipt { mode: *mode });
            }
        }
        for outcome in recorded.values_mut() {
            if !outcome.state.is_pass()
                && outcome.rejection.is_none()
                && !prose.contains_key(row_id)
            {
                outcome.rejection = Some(RejectionReason::MissingPolicyProse {
                    state: outcome.state,
                });
            }
            if let Some(reason) = &outcome.rejection {
                reject(reason.clone());
            }
        }
        if rejections.len() == before && settled_state(slot, recorded).is_none() {
            let states: Vec<String> = recorded
                .iter()
                .map(|(mode, outcome)| format!("{}={}", mode.as_str(), outcome.state.as_str()))
                .collect();
            rejections.push(RebuildRejection {
                row_id: row_id.clone(),
                reason: RejectionReason::ModeDisagreement {
                    states: states.join(","),
                },
            });
        }
    }

    let projection = Projection {
        index,
        outcomes: &outcomes,
        prose,
        manifest_sha256,
    };

    // Late validation runs before anything is published: a rejection, an
    // oversized artifact, or a malformed row leaves the previous ledger intact.
    if !rejections.is_empty() {
        let measured = projection.measure()?;
        let changed = measured.digest_differs(&ledger_path);
        return Ok(RebuildReport {
            mode,
            ledger_path,
            obligations: index.len(),
            receipts_consumed,
            ledger_digest: measured.digest,
            bytes: measured.bytes,
            changed,
            max_live_rows: measured.max_live_rows,
            rejections,
        });
    }

    let measured = projection.measure()?;
    let changed = measured.digest_differs(&ledger_path);
    if mode.writes() && changed {
        projection.publish(&ledger_path, &measured)?;
    }

    Ok(RebuildReport {
        mode,
        ledger_path,
        obligations: index.len(),
        receipts_consumed,
        ledger_digest: measured.digest,
        bytes: measured.bytes,
        changed,
        max_live_rows: measured.max_live_rows,
        rejections: Vec::new(),
    })
}

fn record_outcome(
    index: &ObligationIndex,
    outcomes: &mut BTreeMap<String, ModeOutcomes>,
    rejections: &mut Vec<RebuildRejection>,
    row: &EvidenceRow,
) {
    let Some((row_id, slot)) = index.resolve(row.key()) else {
        rejections.push(RebuildRejection {
            row_id: row_id_for(row.key()),
            reason: RejectionReason::UnknownObligation,
        });
        return;
    };
    let reason = admit(
        slot,
        row.key(),
        row.state(),
        row.observables(),
        row.artifacts(),
    );
    let recorded = outcomes.entry(row_id.to_owned()).or_default();
    match recorded.entry(row.key().mode()) {
        Entry::Vacant(slot) => {
            slot.insert(Outcome {
                state: row.state(),
                rejection: reason,
            });
        }
        Entry::Occupied(mut existing) => {
            existing.insert(Outcome {
                state: row.state(),
                rejection: Some(RejectionReason::DuplicateReceipt),
            });
        }
    }
}

fn admit(
    slot: &ObligationSlot,
    key: &ObligationKey,
    state: TerminalState,
    observables: &BTreeSet<String>,
    artifacts: &BTreeMap<String, String>,
) -> Option<RejectionReason> {
    for (field, matches) in [
        ("execution_mode", slot.modes.contains(&key.mode())),
        ("platform", key.platform() == slot.platform),
    ] {
        if !matches {
            return Some(RejectionReason::StaleBinding {
                field: field.to_owned(),
            });
        }
    }
    if let Some(expected) = slot.classification
        && !classification_matches(expected, state)
    {
        return Some(RejectionReason::ClassificationMismatch {
            expected: format!("{expected:?}"),
            actual: state.as_str().to_owned(),
        });
    }
    if state.is_pass() {
        if observables != &slot.observables {
            return Some(RejectionReason::ObservableMismatch {
                expected: render_set(&slot.observables),
                actual: render_set(observables),
            });
        }
        for observable in observables {
            if !artifacts.contains_key(observable) {
                return Some(RejectionReason::MissingObservableDigest {
                    observable: observable.clone(),
                });
            }
        }
        return None;
    }

    match state {
        TerminalState::Pass => None,
        TerminalState::InapplicableLanguageService
        | TerminalState::InapplicableOutOfScopeHostFeature
        | TerminalState::InapplicableV8Internal
        | TerminalState::ExternalBlocked => None,
        TerminalState::BlockingFail
        | TerminalState::InapplicableCatalogError
        | TerminalState::Timeout
        | TerminalState::Signal
        | TerminalState::ProtocolError
        | TerminalState::WorkerCrash => Some(RejectionReason::BlockingState { state }),
    }
}

fn classification_matches(expected: ClassificationState, actual: TerminalState) -> bool {
    matches!(
        (expected, actual),
        (ClassificationState::Pass, TerminalState::Pass)
            | (
                ClassificationState::NonPass(NonPassState::BlockingFail),
                TerminalState::BlockingFail
            )
            | (
                ClassificationState::NonPass(NonPassState::InapplicableLanguageService),
                TerminalState::InapplicableLanguageService
            )
            | (
                ClassificationState::NonPass(NonPassState::InapplicableOutOfScopeHostFeature),
                TerminalState::InapplicableOutOfScopeHostFeature
            )
            | (
                ClassificationState::NonPass(NonPassState::InapplicableV8Internal),
                TerminalState::InapplicableV8Internal
            )
            | (
                ClassificationState::NonPass(NonPassState::InapplicableCatalogError),
                TerminalState::InapplicableCatalogError
            )
            | (
                ClassificationState::NonPass(NonPassState::ExternalBlocked),
                TerminalState::ExternalBlocked
            )
    )
}

/// Maps a terminal state onto the closed ledger vocabulary.  States outside the
/// vocabulary never reach a published row.
fn ledger_state(state: TerminalState) -> Option<&'static str> {
    let rendered = state.as_str();
    LEDGER_STATES
        .iter()
        .find(|allowed| **allowed == rendered)
        .copied()
}

fn render_set(values: &BTreeSet<String>) -> String {
    values
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(",")
}

fn row_id_for(key: &ObligationKey) -> String {
    format!("{}:{}", key.catalog(), key.case())
}

fn receipt_label(receipt: &Path) -> String {
    receipt.display().to_string()
}

/// One published row. Prose exists only on non-PASS rows and the case is the
/// tail of `id`, so a PASS row is these three fields: at the manifest's full size
/// that keeps the ledger about half the size of writing every field.
#[derive(Serialize)]
struct LedgerRowOut<'a> {
    catalog: &'a str,
    #[serde(skip_serializing_if = "str::is_empty")]
    citation: &'a str,
    id: &'a str,
    #[serde(skip_serializing_if = "str::is_empty")]
    matcher: &'a str,
    #[serde(skip_serializing_if = "str::is_empty")]
    owner: &'a str,
    #[serde(skip_serializing_if = "str::is_empty")]
    reason: &'a str,
    state: &'a str,
}

struct Projection<'a> {
    index: &'a ObligationIndex,
    outcomes: &'a BTreeMap<String, ModeOutcomes>,
    prose: &'a BTreeMap<String, LedgerProse>,
    manifest_sha256: &'a str,
}

struct Measured {
    digest: String,
    bytes: u64,
    max_live_rows: usize,
}

impl Measured {
    fn digest_differs(&self, ledger_path: &Path) -> bool {
        match file_digest(ledger_path) {
            Ok(Some(existing)) => existing != self.digest,
            Ok(None) | Err(_) => true,
        }
    }
}

impl Projection<'_> {
    /// Streams the projection into a sink, returning its digest and length.
    fn measure(&self) -> Result<Measured> {
        let mut writer = HashingWriter::new(io::sink());
        let max_live_rows = self.stream(&mut writer)?;
        Ok(Measured {
            digest: format!("{:x}", writer.hasher.finalize()),
            bytes: writer.bytes,
            max_live_rows,
        })
    }

    /// Publishes atomically: stream to a sibling temporary file, verify the
    /// bytes match the measured projection, then rename.
    fn publish(&self, ledger_path: &Path, measured: &Measured) -> Result<()> {
        let parent = ledger_path.parent().ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{} has no parent directory", ledger_path.display()),
            )
        })?;
        fs::create_dir_all(parent).map_err(|error| io_path(parent, error))?;
        let temporary = sibling_temp(ledger_path);
        let guard = TempGuard {
            path: temporary.clone(),
        };

        let file = File::create(&temporary).map_err(|error| io_path(&temporary, error))?;
        #[cfg(test)]
        if FAIL_PUBLICATION_AFTER_TEMP_CREATE.with(|fail| fail.replace(false)) {
            return Err(VerificationError::new(
                ErrorCode::Io,
                "injected ledger write failure after temporary-file creation",
            ));
        }
        let mut writer = HashingWriter::new(BufWriter::new(file));
        self.stream(&mut writer)?;
        let digest = format!("{:x}", writer.hasher.clone().finalize());
        let bytes = writer.bytes;
        let mut inner = writer
            .inner
            .into_inner()
            .map_err(|error| io_path(&temporary, error.into_error()))?;
        inner.flush().map_err(|error| io_path(&temporary, error))?;
        inner
            .sync_all()
            .map_err(|error| io_path(&temporary, error))?;
        drop(inner);

        if digest != measured.digest || bytes != measured.bytes {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                format!(
                    "{}: projection is not reproducible between measure and publish",
                    ledger_path.display()
                ),
            ));
        }

        fs::rename(&temporary, ledger_path).map_err(|error| io_path(ledger_path, error))?;
        guard.disarm();
        Ok(())
    }

    /// Writes the whole document one row at a time.  Returns the peak number of
    /// rows held at once, which the streaming contract pins at one.
    fn stream<W: Write>(&self, writer: &mut HashingWriter<W>) -> Result<usize> {
        let mut max_live_rows = 0usize;
        writer.write_str("{\"schema\":\"")?;
        writer.write_str(LEDGER_SCHEMA)?;
        writer.write_str("\",\"manifest_sha256\":\"")?;
        writer.write_str(self.manifest_sha256)?;
        writer.write_str("\",\"states\":[")?;
        for (position, state) in LEDGER_STATES.iter().enumerate() {
            if position > 0 {
                writer.write_str(",")?;
            }
            writer.write_str("\"")?;
            writer.write_str(state)?;
            writer.write_str("\"")?;
        }
        writer.write_str("],\"rows\":[")?;

        let mut first = true;
        for (row_id, slot) in &self.index.slots {
            let Some(settled) = self
                .outcomes
                .get(row_id)
                .and_then(|recorded| settled_state(slot, recorded))
            else {
                continue;
            };
            let Some(state) = ledger_state(settled) else {
                continue;
            };
            let empty = LedgerProse {
                citation: String::new(),
                owner: String::new(),
                reason: String::new(),
                matcher: String::new(),
            };
            let prose = if settled.is_pass() {
                &empty
            } else {
                let prose = self.prose.get(row_id).ok_or_else(|| {
                    VerificationError::new(
                        ErrorCode::Transition,
                        format!("non-PASS row `{row_id}` has no exact policy record"),
                    )
                })?;
                prose.validate(row_id)?;
                prose
            };

            // One row is live at a time: encoded, written, and dropped.
            let row = LedgerRowOut {
                catalog: &slot.catalog,
                citation: &prose.citation,
                id: row_id,
                matcher: &prose.matcher,
                owner: &prose.owner,
                reason: &prose.reason,
                state,
            };
            max_live_rows = max_live_rows.max(1);
            let encoded = serde_json::to_vec(&row).map_err(|error| {
                VerificationError::new(
                    ErrorCode::Json,
                    format!("cannot encode ledger row `{row_id}`: {error}"),
                )
            })?;
            if encoded.len() > MAX_ROW_BYTES {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!(
                        "ledger row `{row_id}` is {} bytes, above the {MAX_ROW_BYTES}-byte row bound",
                        encoded.len()
                    ),
                ));
            }
            if !first {
                writer.write_str(",")?;
            }
            first = false;
            writer.write_all_checked(&encoded)?;
        }

        writer.write_str("]}\n")?;
        if writer.bytes >= MAX_LEDGER_BYTES {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "projected ledger is {} bytes, at or above the {MAX_LEDGER_BYTES}-byte publication bound",
                    writer.bytes
                ),
            ));
        }
        Ok(max_live_rows)
    }
}

struct HashingWriter<W> {
    inner: W,
    hasher: Sha256,
    bytes: u64,
}

impl<W: Write> HashingWriter<W> {
    fn new(inner: W) -> Self {
        Self {
            inner,
            hasher: Sha256::new(),
            bytes: 0,
        }
    }

    fn write_str(&mut self, value: &str) -> Result<()> {
        self.write_all_checked(value.as_bytes())
    }

    fn write_all_checked(&mut self, bytes: &[u8]) -> Result<()> {
        self.inner.write_all(bytes).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("cannot write ledger: {error}"))
        })?;
        self.hasher.update(bytes);
        self.bytes += bytes.len() as u64;
        Ok(())
    }
}

struct TempGuard {
    path: PathBuf,
}

impl TempGuard {
    fn disarm(self) {
        std::mem::forget(self);
    }
}

impl Drop for TempGuard {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn sibling_temp(destination: &Path) -> PathBuf {
    let nonce = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
    let name = destination.file_name().map_or_else(
        || "ledger".to_owned(),
        |name| name.to_string_lossy().into_owned(),
    );
    destination.with_file_name(format!(".{name}.rebuild.{}.{nonce}.tmp", process::id()))
}

fn file_digest(path: &Path) -> Result<Option<String>> {
    let file = match File::open(path) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(io_path(path, error)),
    };
    let mut reader = BufReader::new(file);
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = reader
            .read(&mut buffer)
            .map_err(|error| io_path(path, error))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(Some(format!("{:x}", hasher.finalize())))
}

fn io_path(path: &Path, error: io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        evidence::{PublishMode, ToolchainPin, WorkingDirectoryPolicy, publish_evidence},
        shard::{ExecutionMode, ShardIdentity, ShardSpec},
        suite::completion::{SuiteRunner, logical_obligation, materialize_obligations},
    };

    const DIGEST: &str = "a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90";
    const OTHER: &str = "0f1e2d3c4b5a69788796a5b4c3d2e1f00f1e2d3c4b5a69788796a5b4c3d2e1f0";
    const CATALOG: &str = "typescript-7.0.2";
    fn platform() -> String {
        bamts_platform::host_triple()
    }
    fn scratch(name: &str) -> PathBuf {
        let nonce = TEMP_NONCE.fetch_add(1, Ordering::Relaxed);
        let root =
            std::env::temp_dir().join(format!("bamts-rebuild-{name}-{}-{nonce}", process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("proof")).expect("scratch root");
        root
    }

    fn identity(index: usize, observable: &str) -> String {
        format!("{CATALOG}/compiler/tests/cases/compiler/case-{index:04}.ts#default#{observable}")
    }

    fn index_of(identities: &[String]) -> ObligationIndex {
        let row_ids: BTreeSet<String> = identities
            .iter()
            .map(|identity| format!("{CATALOG}:{identity}"))
            .collect();
        ObligationIndex::from_row_ids(&row_ids).expect("index")
    }

    /// The key a lane really writes, so a fixture cannot drift from a receipt.
    fn lane_key(catalog: &str, identity: &str, mode: ExecutionMode) -> ObligationKey {
        logical_obligation(catalog, identity, mode, &platform())
            .expect("logical obligation")
            .key
    }

    fn key_for(identity: &str) -> ObligationKey {
        lane_key(CATALOG, identity, ExecutionMode::Aot)
    }
    fn toolchain_pin() -> ToolchainPin {
        ToolchainPin::new("rustc-1.97.1", DIGEST).expect("toolchain pin")
    }

    fn binding() -> RunBinding {
        RunBinding::new(DIGEST, DIGEST, DIGEST, DIGEST, toolchain_pin()).expect("binding")
    }

    fn expected_bindings() -> BTreeMap<String, RunBinding> {
        BTreeMap::from([(CATALOG.to_owned(), binding())])
    }

    const CATALOG_A: &str = "typescript-a";
    const CATALOG_B: &str = "typescript-b";
    const THIRD: &str = "1111111111111111111111111111111111111111111111111111111111111111";

    fn catalog_identity(catalog: &str, index: usize) -> String {
        format!("{catalog}/case-{index:04}.ts#default#diagnostics")
    }

    fn multi_index(entries: &[(&str, &str)]) -> ObligationIndex {
        let row_ids = entries
            .iter()
            .map(|(catalog, identity)| format!("{catalog}:{identity}"))
            .collect();
        ObligationIndex::from_row_ids(&row_ids).expect("multi-catalog index")
    }

    fn pass_row_for_catalog(catalog: &str, identity: &str) -> EvidenceRow {
        EvidenceRow::new(
            lane_key(catalog, identity, ExecutionMode::Aot),
            vec!["bamts".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["diagnostics".to_owned()]),
            BTreeMap::from([("diagnostics".to_owned(), DIGEST.to_owned())]),
            TerminalState::Pass,
            1,
            "receipt",
        )
        .expect("catalog row")
    }

    fn run_binding(authority: &str, tree: &str) -> RunBinding {
        RunBinding::new(authority, tree, DIGEST, DIGEST, toolchain_pin()).expect("run binding")
    }

    fn two_catalog_fixture() -> (
        ObligationIndex,
        String,
        String,
        BTreeMap<String, RunBinding>,
    ) {
        let first = catalog_identity(CATALOG_A, 0);
        let second = catalog_identity(CATALOG_B, 1);
        let index = multi_index(&[(CATALOG_A, &first), (CATALOG_B, &second)]);
        let expected = BTreeMap::from([
            (CATALOG_A.to_owned(), run_binding(DIGEST, DIGEST)),
            (CATALOG_B.to_owned(), run_binding(OTHER, DIGEST)),
        ]);
        (index, first, second, expected)
    }

    fn project_with_bindings(
        root: &Path,
        index: &ObligationIndex,
        receipts: &[PathBuf],
        expected: &BTreeMap<String, RunBinding>,
        mode: RebuildMode,
    ) -> Result<RebuildReport> {
        rebuild_projection(
            root,
            index,
            DIGEST,
            receipts,
            mode,
            expected,
            &BTreeMap::new(),
        )
    }

    fn pass_row(identity: &str, observable: &str) -> EvidenceRow {
        row_with(identity, TerminalState::Pass, &[observable], &[observable])
    }

    fn row_with(
        identity: &str,
        state: TerminalState,
        observables: &[&str],
        artifacts: &[&str],
    ) -> EvidenceRow {
        let observables: BTreeSet<String> =
            observables.iter().map(|name| (*name).to_owned()).collect();
        let artifacts: BTreeMap<String, String> = artifacts
            .iter()
            .map(|name| ((*name).to_owned(), DIGEST.to_owned()))
            .collect();
        EvidenceRow::new(
            key_for(identity),
            vec!["bamts".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            observables,
            artifacts,
            state,
            1,
            "receipt",
        )
        .expect("evidence row")
    }

    fn write_receipt(path: &Path, rows: &[EvidenceRow], binding: RunBinding) {
        let mut keys: Vec<ObligationKey> = rows.iter().map(|row| row.key().clone()).collect();
        keys.sort();
        let shard = ShardIdentity::plan(ShardSpec::unsharded(), &keys).expect("plan");
        let header = crate::evidence::EvidenceHeader::new(
            shard,
            binding,
            crate::evidence::ExecutionBinding::local_for_tests(),
        )
        .expect("header");
        publish_evidence(path, header, rows, PublishMode::Replace).expect("publish receipt");
    }

    fn project(
        root: &Path,
        index: &ObligationIndex,
        receipts: &[PathBuf],
        mode: RebuildMode,
    ) -> Result<RebuildReport> {
        rebuild_projection(
            root,
            index,
            DIGEST,
            receipts,
            mode,
            &expected_bindings(),
            &BTreeMap::new(),
        )
    }

    #[test]
    fn rebuild_is_deterministic() {
        let root = scratch("deterministic");
        let identities: Vec<String> = (0..6).map(|index| identity(index, "diagnostics")).collect();
        let index = index_of(&identities);
        let first = root.join("first.jsonl");
        let second = root.join("second.jsonl");
        write_receipt(
            &first,
            &identities[..3]
                .iter()
                .map(|identity| pass_row(identity, "diagnostics"))
                .collect::<Vec<_>>(),
            binding(),
        );
        write_receipt(
            &second,
            &identities[3..]
                .iter()
                .map(|identity| pass_row(identity, "diagnostics"))
                .collect::<Vec<_>>(),
            binding(),
        );

        let forward = project(
            &root,
            &index,
            &[first.clone(), second.clone()],
            RebuildMode::Write,
        )
        .expect("forward rebuild");
        assert!(forward.is_clean(), "{:?}", forward.rejections);
        let bytes = fs::read(&forward.ledger_path).expect("published ledger");

        // Receipt order must not influence the projection.
        let reversed =
            project(&root, &index, &[second, first], RebuildMode::Write).expect("reversed rebuild");
        assert!(reversed.is_clean(), "{:?}", reversed.rejections);
        assert_eq!(forward.ledger_digest, reversed.ledger_digest);
        assert_eq!(bytes, fs::read(&reversed.ledger_path).expect("republished"));
        assert!(!reversed.changed, "an identical projection is not a change");
        assert_eq!(forward.obligations, 6);
        assert_eq!(forward.receipts_consumed, 6);
        assert_eq!(sha256_hex(&bytes), forward.ledger_digest);
        let document: serde_json::Value =
            serde_json::from_slice(&bytes).expect("canonical ledger JSON");
        let ids: Vec<&str> = document["rows"]
            .as_array()
            .expect("rows")
            .iter()
            .map(|row| row["id"].as_str().expect("row id"))
            .collect();
        assert!(
            ids.windows(2).all(|pair| pair[0] < pair[1]),
            "ledger rows must be in strict canonical key order"
        );

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn rejects_unproven_pass() {
        let root = scratch("unproven");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));

        // A PASS for an obligation the manifest never declared.
        let forged = root.join("forged.jsonl");
        write_receipt(
            &forged,
            &[pass_row(&identity(9, "diagnostics"), "diagnostics")],
            binding(),
        );
        let report = project(&root, &index, &[forged], RebuildMode::Write).expect("forged");
        assert!(
            report
                .rejections
                .iter()
                .any(|rejection| { rejection.reason == RejectionReason::UnknownObligation }),
            "{:?}",
            report.rejections
        );
        assert!(
            report.rejections.iter().any(|rejection| rejection.reason
                == RejectionReason::MissingReceipt {
                    mode: ExecutionMode::Aot
                }),
            "the declared obligation is still unproven"
        );

        // A PASS whose observable set is not the identity's declared observable.
        let wrong = root.join("wrong-observable.jsonl");
        write_receipt(&wrong, &[pass_row(&declared, "javascript")], binding());
        let report =
            project(&root, &index, &[wrong], RebuildMode::Write).expect("wrong observable");
        assert!(
            report.rejections.iter().any(|rejection| matches!(
                rejection.reason,
                RejectionReason::ObservableMismatch { .. }
            )),
            "{:?}",
            report.rejections
        );

        // A PASS that declares the observable but records no digest for it is
        // refused by the receipt schema itself, so it can never be projected.
        let missing = EvidenceRow::new(
            key_for(&declared),
            vec!["bamts".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["diagnostics".to_owned()]),
            BTreeMap::new(),
            TerminalState::Pass,
            1,
            "receipt",
        );
        assert!(missing.is_err(), "a PASS without its artifact is not a row");

        // Exact classification policy also owns whether PASS is admissible.
        let mut classified_index = index_of(std::slice::from_ref(&declared));
        classified_index
            .attach_classifications(BTreeMap::from([(
                declared.clone(),
                ClassificationState::NonPass(NonPassState::ExternalBlocked),
            )]))
            .expect("classification");
        let classified = root.join("classified.jsonl");
        write_receipt(
            &classified,
            &[pass_row(&declared, "diagnostics")],
            binding(),
        );
        let report = project(&root, &classified_index, &[classified], RebuildMode::Write)
            .expect("classified PASS");
        assert!(
            report.rejections.iter().any(|rejection| matches!(
                rejection.reason,
                RejectionReason::ClassificationMismatch { .. }
            )),
            "{:?}",
            report.rejections
        );

        // Nothing was published by any rejected rebuild.
        assert!(!root.join(LEDGER_PATH).exists());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn rejects_stale_receipt() {
        let root = scratch("stale");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let receipt = root.join("stale.jsonl");

        // A binding whose authority digest is not the repository's.
        write_receipt(
            &receipt,
            &[pass_row(&declared, "diagnostics")],
            RunBinding::new(OTHER, DIGEST, DIGEST, DIGEST, toolchain_pin())
                .expect("stale authority"),
        );
        let report = project(
            &root,
            &index,
            std::slice::from_ref(&receipt),
            RebuildMode::Write,
        )
        .expect("stale authority");
        assert!(
            report.rejections.iter().any(|rejection| rejection.reason
                == RejectionReason::StaleBinding {
                    field: "authority_digest".to_owned()
                }),
            "{:?}",
            report.rejections
        );

        // Every remaining binding field is pinned exactly.
        for (field, stale) in [
            (
                "candidate_tree_digest",
                RunBinding::new(DIGEST, OTHER, DIGEST, DIGEST, toolchain_pin()).expect("tree"),
            ),
            (
                "candidate_binary_digest",
                RunBinding::new(DIGEST, DIGEST, OTHER, DIGEST, toolchain_pin()).expect("binary"),
            ),
            (
                "harness_digest",
                RunBinding::new(DIGEST, DIGEST, DIGEST, OTHER, toolchain_pin()).expect("harness"),
            ),
        ] {
            write_receipt(&receipt, &[pass_row(&declared, "diagnostics")], stale);
            let report = rebuild_projection(
                &root,
                &index,
                DIGEST,
                std::slice::from_ref(&receipt),
                RebuildMode::Write,
                &expected_bindings(),
                &BTreeMap::new(),
            )
            .expect("pinned binding");
            assert!(
                report.rejections.iter().any(|rejection| rejection.reason
                    == RejectionReason::StaleBinding {
                        field: field.to_owned()
                    }),
                "{field} must be detected: {:?}",
                report.rejections
            );
        }

        // A stale shard from an earlier run cannot be mixed with a current one.
        let current = root.join("current.jsonl");
        let earlier = root.join("earlier.jsonl");
        let second = identity(1, "diagnostics");
        let index = index_of(&[declared.clone(), second.clone()]);
        write_receipt(&current, &[pass_row(&declared, "diagnostics")], binding());
        write_receipt(
            &earlier,
            &[pass_row(&second, "diagnostics")],
            RunBinding::new(DIGEST, OTHER, OTHER, OTHER, toolchain_pin()).expect("earlier run"),
        );
        let report =
            project(&root, &index, &[current, earlier], RebuildMode::Write).expect("mixed runs");
        assert!(
            report
                .rejections
                .iter()
                .any(|rejection| matches!(rejection.reason, RejectionReason::StaleBinding { .. })),
            "{:?}",
            report.rejections
        );

        // Mode, platform, and normalization are bound by the obligation key and
        // the canonical environment: a receipt naming another mode or platform
        // projects to no declared obligation.
        for (field, key) in [
            (
                "execution_mode",
                lane_key(CATALOG, &declared, ExecutionMode::Jit),
            ),
            (
                "platform",
                logical_obligation(
                    CATALOG,
                    &declared,
                    ExecutionMode::Aot,
                    &format!("{}-foreign", platform()),
                )
                .expect("platform")
                .key,
            ),
        ] {
            let index = index_of(std::slice::from_ref(&declared));
            let row = EvidenceRow::new(
                key,
                vec!["bamts".to_owned()],
                WorkingDirectoryPolicy::RepositoryRoot,
                BTreeSet::from(["diagnostics".to_owned()]),
                BTreeMap::from([("diagnostics".to_owned(), DIGEST.to_owned())]),
                TerminalState::Pass,
                1,
                "receipt",
            )
            .expect("row");
            let path = root.join("coordinate.jsonl");
            write_receipt(&path, &[row], binding());
            let report = project(&root, &index, &[path], RebuildMode::Write).expect("coordinate");
            // The obligation key carries mode and platform, so a divergent run
            // coordinate cannot satisfy the declared obligation.
            assert!(
                report.rejections.iter().any(|rejection| rejection.reason
                    == RejectionReason::StaleBinding {
                        field: field.to_owned()
                    }),
                "{field}: {:?}",
                report.rejections
            );
        }

        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn accepts_distinct_current_authorities_per_catalog() {
        let root = scratch("two-catalog-accept");
        let (index, first, second, expected) = two_catalog_fixture();
        assert_ne!(
            expected[CATALOG_A].authority_digest(),
            expected[CATALOG_B].authority_digest()
        );
        assert!(expected[CATALOG_A].same_run_as(&expected[CATALOG_B]));

        let first_receipt = root.join("a.jsonl");
        let second_receipt = root.join("b.jsonl");
        write_receipt(
            &first_receipt,
            &[pass_row_for_catalog(CATALOG_A, &first)],
            expected[CATALOG_A].clone(),
        );
        write_receipt(
            &second_receipt,
            &[pass_row_for_catalog(CATALOG_B, &second)],
            expected[CATALOG_B].clone(),
        );
        let forward = project_with_bindings(
            &root,
            &index,
            &[first_receipt.clone(), second_receipt.clone()],
            &expected,
            RebuildMode::Write,
        )
        .expect("forward");
        assert!(forward.is_clean(), "{:?}", forward.rejections);
        let forward_bytes = fs::read(&forward.ledger_path).expect("forward ledger");

        let reverse = project_with_bindings(
            &root,
            &index,
            &[second_receipt, first_receipt],
            &expected,
            RebuildMode::Write,
        )
        .expect("reverse");
        assert!(reverse.is_clean(), "{:?}", reverse.rejections);
        assert_eq!(reverse.ledger_digest, forward.ledger_digest);
        assert_eq!(
            fs::read(&reverse.ledger_path).expect("reverse ledger"),
            forward_bytes
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_authority_swapped_between_catalogs() {
        let root = scratch("authority-swapped");
        let (index, first, second, expected) = two_catalog_fixture();
        let first_receipt = root.join("a.jsonl");
        let second_receipt = root.join("b.jsonl");
        write_receipt(
            &first_receipt,
            &[pass_row_for_catalog(CATALOG_A, &first)],
            expected[CATALOG_B].clone(),
        );
        write_receipt(
            &second_receipt,
            &[pass_row_for_catalog(CATALOG_B, &second)],
            expected[CATALOG_A].clone(),
        );
        let report = project_with_bindings(
            &root,
            &index,
            &[first_receipt, second_receipt],
            &expected,
            RebuildMode::Write,
        )
        .expect("rejection report");
        assert_eq!(
            report
                .rejections
                .iter()
                .filter(|rejection| rejection.reason
                    == RejectionReason::StaleBinding {
                        field: "authority_digest".to_owned()
                    })
                .count(),
            2
        );
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_one_stale_catalog_authority() {
        let root = scratch("one-stale-authority");
        let (index, first, second, expected) = two_catalog_fixture();
        let first_receipt = root.join("a.jsonl");
        let second_receipt = root.join("b.jsonl");
        write_receipt(
            &first_receipt,
            &[pass_row_for_catalog(CATALOG_A, &first)],
            expected[CATALOG_A].clone(),
        );
        write_receipt(
            &second_receipt,
            &[pass_row_for_catalog(CATALOG_B, &second)],
            run_binding(THIRD, DIGEST),
        );
        let report = project_with_bindings(
            &root,
            &index,
            &[first_receipt, second_receipt],
            &expected,
            RebuildMode::Write,
        )
        .expect("rejection report");
        assert!(report.rejections.iter().any(|rejection| {
            rejection.reason
                == RejectionReason::StaleBinding {
                    field: "authority_digest".to_owned(),
                }
        }));
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_shared_stale_global_run() {
        let root = scratch("shared-stale-global");
        let (index, first, second, expected) = two_catalog_fixture();
        let first_receipt = root.join("a.jsonl");
        let second_receipt = root.join("b.jsonl");
        write_receipt(
            &first_receipt,
            &[pass_row_for_catalog(CATALOG_A, &first)],
            run_binding(DIGEST, OTHER),
        );
        write_receipt(
            &second_receipt,
            &[pass_row_for_catalog(CATALOG_B, &second)],
            run_binding(OTHER, OTHER),
        );
        let report = project_with_bindings(
            &root,
            &index,
            &[first_receipt, second_receipt],
            &expected,
            RebuildMode::Write,
        )
        .expect("rejection report");
        assert_eq!(
            report
                .rejections
                .iter()
                .filter(|rejection| rejection.reason
                    == RejectionReason::StaleBinding {
                        field: "candidate_tree_digest".to_owned()
                    })
                .count(),
            2
        );
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_mixed_run_across_catalogs() {
        let root = scratch("mixed-global-run");
        let (index, first, second, expected) = two_catalog_fixture();
        let first_receipt = root.join("a.jsonl");
        let second_receipt = root.join("b.jsonl");
        write_receipt(
            &first_receipt,
            &[pass_row_for_catalog(CATALOG_A, &first)],
            expected[CATALOG_A].clone(),
        );
        write_receipt(
            &second_receipt,
            &[pass_row_for_catalog(CATALOG_B, &second)],
            run_binding(OTHER, OTHER),
        );
        let report = project_with_bindings(
            &root,
            &index,
            &[first_receipt, second_receipt],
            &expected,
            RebuildMode::Write,
        )
        .expect("rejection report");
        assert!(report.rejections.iter().any(|rejection| {
            rejection.reason
                == RejectionReason::StaleBinding {
                    field: "candidate_tree_digest".to_owned(),
                }
        }));
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_mixed_catalog_rows_in_one_receipt() {
        let root = scratch("mixed-catalog-document");
        let (index, first, second, expected) = two_catalog_fixture();
        let receipt = root.join("mixed.jsonl");
        write_receipt(
            &receipt,
            &[
                pass_row_for_catalog(CATALOG_A, &first),
                pass_row_for_catalog(CATALOG_B, &second),
            ],
            expected[CATALOG_A].clone(),
        );
        let report =
            project_with_bindings(&root, &index, &[receipt], &expected, RebuildMode::Write)
                .expect("rejection report");
        assert!(report.rejections.iter().any(|rejection| matches!(
            rejection.reason,
            RejectionReason::ReceiptCatalogMismatch { .. }
        )));
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rejects_unknown_catalog_before_binding_admission() {
        let root = scratch("unknown-catalog");
        let identity = catalog_identity(CATALOG_A, 0);
        let index = multi_index(&[(CATALOG_A, &identity)]);
        let expected = BTreeMap::from([(CATALOG_A.to_owned(), run_binding(DIGEST, DIGEST))]);
        let foreign_catalog = "catalog-foreign";
        let foreign_identity = catalog_identity(foreign_catalog, 0);
        let receipt = root.join("foreign.jsonl");
        write_receipt(
            &receipt,
            &[pass_row_for_catalog(foreign_catalog, &foreign_identity)],
            run_binding(OTHER, OTHER),
        );
        let report =
            project_with_bindings(&root, &index, &[receipt], &expected, RebuildMode::Write)
                .expect("rejection report");
        assert!(report.rejections.iter().any(|rejection| {
            rejection.reason
                == RejectionReason::UnknownCatalog {
                    catalog: foreign_catalog.to_owned(),
                }
        }));
        assert!(
            !report
                .rejections
                .iter()
                .any(|rejection| matches!(rejection.reason, RejectionReason::StaleBinding { .. }))
        );
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn streams_large_ledger() {
        let root = scratch("large");
        // Representative deterministic mix: one deep configured conformance
        // identity followed by two ordinary compiler identities.
        let identities: Vec<String> = (0..2_000)
            .map(|index| {
                if index % 3 == 0 {
                    format!(
                        "{CATALOG}/conformance/tests/cases/conformance/es2020/modules/nested/deeply/\
                         case-{index:06}.ts#module=commonjs,target=es5,strict=true,declaration=true#diagnostics"
                    )
                } else {
                    identity(index, "diagnostics")
                }
            })
            .collect();
        let row_ids: BTreeSet<String> = identities
            .iter()
            .map(|identity| format!("{CATALOG}:{identity}"))
            .collect();
        let index = ObligationIndex::from_row_ids(&row_ids).expect("index");

        let rows: Vec<EvidenceRow> = identities
            .iter()
            .map(|identity| {
                EvidenceRow::new(
                    key_for(identity),
                    vec!["bamts".to_owned()],
                    WorkingDirectoryPolicy::RepositoryRoot,
                    BTreeSet::from(["diagnostics".to_owned()]),
                    BTreeMap::from([("diagnostics".to_owned(), DIGEST.to_owned())]),
                    TerminalState::Pass,
                    1,
                    "receipt",
                )
                .expect("row")
            })
            .collect();
        let mut sorted = rows;
        sorted.sort_by(|left, right| left.key().cmp(right.key()));

        let receipt = root.join("large.jsonl");
        write_receipt(&receipt, &sorted, binding());

        let report = project(&root, &index, &[receipt], RebuildMode::Write).expect("large rebuild");
        assert!(report.is_clean(), "{:?}", report.rejections);
        assert_eq!(report.obligations, 2_000);

        // Bounded memory: exactly one ledger row is live at any time.
        assert_eq!(report.max_live_rows, 1);

        // Compact encoding: no per-row pretty-printing reaches the artifact.
        let bytes = fs::read(&report.ledger_path).expect("published");
        let text = String::from_utf8(bytes).expect("utf8");
        assert!(!text.contains("\n  "), "rows must not be pretty-printed");
        assert_eq!(text.matches("\"state\":\"PASS\"").count(), 2_000);

        let _ = fs::remove_dir_all(&root);
    }

    const TEST262_CASE: &str = "test262/test262/test/built-ins/Array/case.js#default#runtime";

    fn test262_index() -> ObligationIndex {
        multi_index(&[("test262", TEST262_CASE)])
    }

    fn test262_row(mode: ExecutionMode, state: TerminalState) -> EvidenceRow {
        let pass = state == TerminalState::Pass;
        EvidenceRow::new(
            lane_key("test262", TEST262_CASE, mode),
            vec!["bamts".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["runtime".to_owned()]),
            if pass {
                BTreeMap::from([("runtime".to_owned(), DIGEST.to_owned())])
            } else {
                BTreeMap::new()
            },
            state,
            1,
            "receipt",
        )
        .expect("test262 row")
    }

    /// One receipt per row, the way one lane writes one receipt per mode.
    fn test262_receipts(root: &Path, rows: Vec<EvidenceRow>) -> Vec<PathBuf> {
        rows.into_iter()
            .enumerate()
            .map(|(position, row)| {
                let path = root.join(format!("test262-{position}.jsonl"));
                write_receipt(&path, &[row], binding());
                path
            })
            .collect()
    }

    fn project_test262(root: &Path, receipts: &[PathBuf]) -> RebuildReport {
        let expected = BTreeMap::from([("test262".to_owned(), binding())]);
        project_with_bindings(
            root,
            &test262_index(),
            receipts,
            &expected,
            RebuildMode::Write,
        )
        .expect("test262 projection")
    }

    #[test]
    fn a_compiler_receipt_row_is_admitted() {
        let root = scratch("compiler-row");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let lanes = materialize_obligations(
            CATALOG,
            std::slice::from_ref(&declared),
            SuiteRunner::Compiler,
            &platform(),
        )
        .expect("lane keys");
        assert_eq!(lanes[0].key, key_for(&declared));

        let receipt = root.join("compiler.jsonl");
        write_receipt(&receipt, &[pass_row(&declared, "diagnostics")], binding());
        let report = project(&root, &index, &[receipt], RebuildMode::Write).expect("rebuild");
        assert!(report.is_clean(), "{:?}", report.rejections);
        let ledger: serde_json::Value =
            serde_json::from_slice(&fs::read(&report.ledger_path).expect("ledger")).expect("json");
        assert_eq!(
            ledger["rows"][0],
            serde_json::json!({
                "catalog": CATALOG,
                "id": format!("{CATALOG}:{declared}"),
                "state": "PASS",
            }),
            "a PASS row carries nothing the id does not already say"
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_non_pass_row_keeps_its_policy_prose() {
        let root = scratch("non-pass-row");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let receipt = root.join("blocked.jsonl");
        write_receipt(
            &receipt,
            &[row_with(
                &declared,
                TerminalState::ExternalBlocked,
                &["diagnostics"],
                &[],
            )],
            binding(),
        );
        let row_id = format!("{CATALOG}:{declared}");
        let prose = BTreeMap::from([(
            row_id.clone(),
            LedgerProse {
                citation: "citation".to_owned(),
                owner: "owner".to_owned(),
                reason: "reason".to_owned(),
                matcher: "matcher".to_owned(),
            },
        )]);
        let report = rebuild_projection(
            &root,
            &index,
            DIGEST,
            &[receipt],
            RebuildMode::Write,
            &expected_bindings(),
            &prose,
        )
        .expect("rebuild");
        assert!(report.is_clean(), "{:?}", report.rejections);
        let ledger: serde_json::Value =
            serde_json::from_slice(&fs::read(&report.ledger_path).expect("ledger")).expect("json");
        assert_eq!(
            ledger["rows"][0],
            serde_json::json!({
                "catalog": CATALOG,
                "citation": "citation",
                "id": row_id,
                "matcher": "matcher",
                "owner": "owner",
                "reason": "reason",
                "state": "EXTERNAL_BLOCKED",
            })
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_test262_case_is_complete_only_in_all_three_modes() {
        let root = scratch("three-modes");
        let partial = test262_receipts(
            &root,
            vec![
                test262_row(ExecutionMode::Interpreter, TerminalState::Pass),
                test262_row(ExecutionMode::Jit, TerminalState::Pass),
            ],
        );
        let report = project_test262(&root, &partial);
        assert_eq!(
            report.rejections,
            [RebuildRejection {
                row_id: format!("test262:{TEST262_CASE}"),
                reason: RejectionReason::MissingReceipt {
                    mode: ExecutionMode::Aot
                },
            }]
        );
        assert!(
            !root.join(LEDGER_PATH).exists(),
            "a JIT row without an AOT row leaves the case incomplete"
        );

        let all = test262_receipts(
            &root,
            ExecutionMode::ALL
                .into_iter()
                .map(|mode| test262_row(mode, TerminalState::Pass))
                .collect(),
        );
        let report = project_test262(&root, &all);
        assert!(report.is_clean(), "{:?}", report.rejections);
        assert_eq!(report.receipts_consumed, 3);
        let ledger: serde_json::Value =
            serde_json::from_slice(&fs::read(&report.ledger_path).expect("ledger")).expect("json");
        assert_eq!(ledger["rows"].as_array().expect("rows").len(), 1);
        assert_eq!(ledger["rows"][0]["state"], "PASS");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_row_settles_only_when_every_required_mode_has_reported() {
        let index = test262_index();
        let slot = index.slots.values().next().expect("one slot");
        let pass = Outcome {
            state: TerminalState::Pass,
            rejection: None,
        };
        let mut recorded = ModeOutcomes::new();
        for mode in ExecutionMode::ALL {
            assert_eq!(settled_state(slot, &recorded), None);
            recorded.insert(mode, pass.clone());
        }
        assert_eq!(settled_state(slot, &recorded), Some(TerminalState::Pass));

        recorded.insert(
            ExecutionMode::Jit,
            Outcome {
                state: TerminalState::Pass,
                rejection: Some(RejectionReason::DuplicateReceipt),
            },
        );
        assert_eq!(settled_state(slot, &recorded), None);
    }

    #[test]
    fn one_failing_mode_keeps_a_test262_case_out_of_the_ledger() {
        let root = scratch("one-mode-fails");
        let receipts = test262_receipts(
            &root,
            vec![
                test262_row(ExecutionMode::Interpreter, TerminalState::Pass),
                test262_row(ExecutionMode::Jit, TerminalState::Pass),
                test262_row(ExecutionMode::Aot, TerminalState::BlockingFail),
            ],
        );
        let report = project_test262(&root, &receipts);
        assert_eq!(report.rejections.len(), 1, "{:?}", report.rejections);
        assert!(matches!(
            report.rejections[0].reason,
            RejectionReason::BlockingState { .. }
        ));
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn modes_that_disagree_do_not_settle_a_row() {
        let root = scratch("disagreement");
        let receipts = test262_receipts(
            &root,
            vec![
                test262_row(ExecutionMode::Interpreter, TerminalState::Pass),
                test262_row(ExecutionMode::Jit, TerminalState::Pass),
                test262_row(
                    ExecutionMode::Aot,
                    TerminalState::InapplicableOutOfScopeHostFeature,
                ),
            ],
        );
        let row_id = format!("test262:{TEST262_CASE}");
        let prose = BTreeMap::from([(
            row_id.clone(),
            LedgerProse {
                citation: "citation".to_owned(),
                owner: "owner".to_owned(),
                reason: "reason".to_owned(),
                matcher: "matcher".to_owned(),
            },
        )]);
        let report = rebuild_projection(
            &root,
            &test262_index(),
            DIGEST,
            &receipts,
            RebuildMode::Write,
            &BTreeMap::from([("test262".to_owned(), binding())]),
            &prose,
        )
        .expect("disagreement");
        assert_eq!(report.rejections.len(), 1, "{:?}", report.rejections);
        assert_eq!(report.rejections[0].row_id, row_id);
        assert!(matches!(
            report.rejections[0].reason,
            RejectionReason::ModeDisagreement { .. }
        ));
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_mode_is_a_duplicate_only_of_itself() {
        let root = scratch("mode-duplicate");
        let receipts = test262_receipts(
            &root,
            vec![
                test262_row(ExecutionMode::Interpreter, TerminalState::Pass),
                test262_row(ExecutionMode::Interpreter, TerminalState::Pass),
                test262_row(ExecutionMode::Jit, TerminalState::Pass),
                test262_row(ExecutionMode::Aot, TerminalState::Pass),
            ],
        );
        let report = project_test262(&root, &receipts);
        assert_eq!(report.rejections.len(), 1, "{:?}", report.rejections);
        assert_eq!(
            report.rejections[0].reason,
            RejectionReason::DuplicateReceipt
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn a_receipt_in_a_mode_the_catalog_does_not_run_cannot_hide_in_a_complete_row() {
        let root = scratch("extra-mode");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let proper = root.join("proper.jsonl");
        write_receipt(&proper, &[pass_row(&declared, "diagnostics")], binding());
        let extra = root.join("extra.jsonl");
        let row = EvidenceRow::new(
            lane_key(CATALOG, &declared, ExecutionMode::Jit),
            vec!["bamts".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            BTreeSet::from(["diagnostics".to_owned()]),
            BTreeMap::from([("diagnostics".to_owned(), DIGEST.to_owned())]),
            TerminalState::Pass,
            1,
            "receipt",
        )
        .expect("row");
        write_receipt(&extra, &[row], binding());
        let report = project(&root, &index, &[proper, extra], RebuildMode::Write).expect("rebuild");
        assert_eq!(
            report
                .rejections
                .iter()
                .map(|r| &r.reason)
                .collect::<Vec<_>>(),
            [&RejectionReason::StaleBinding {
                field: "execution_mode".to_owned()
            }]
        );
        assert!(!root.join(LEDGER_PATH).exists());
        let _ = fs::remove_dir_all(&root);
    }

    /// The obligation universe of the committed manifest.
    fn committed_index() -> ObligationIndex {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let path = root.join(MANIFEST_PATH);
        let bytes = read_bytes(&path).expect("manifest");
        let manifest: VerificationManifest = parse_json(&path, &bytes).expect("manifest json");
        let row_ids: BTreeSet<String> = manifest
            .catalogs
            .iter()
            .flat_map(|catalog| {
                catalog
                    .identifiers
                    .iter()
                    .map(|identifier| format!("{}:{identifier}", catalog.id))
            })
            .collect();
        let index = ObligationIndex::from_row_ids(&row_ids).expect("every identifier has a key");
        assert_eq!(index.len(), row_ids.len());
        index
    }

    #[test]
    fn a_full_ledger_of_the_committed_manifest_stays_under_ninety_megabytes() {
        const TARGET_BYTES: u64 = 90_000_000;
        let index = committed_index();
        let outcomes: BTreeMap<String, ModeOutcomes> = index
            .slots
            .iter()
            .map(|(row_id, slot)| {
                let recorded = slot.modes.iter().map(|mode| {
                    let outcome = Outcome {
                        state: TerminalState::Pass,
                        rejection: None,
                    };
                    (*mode, outcome)
                });
                (row_id.clone(), recorded.collect())
            })
            .collect();
        let prose = BTreeMap::new();
        let measured = Projection {
            index: &index,
            outcomes: &outcomes,
            prose: &prose,
            manifest_sha256: DIGEST,
        }
        .measure()
        .expect("full ledger");
        assert!(
            measured.bytes < TARGET_BYTES,
            "a full ledger is {} bytes",
            measured.bytes
        );
        assert_eq!(measured.max_live_rows, 1);
    }

    #[test]
    fn every_manifest_identifier_is_reached_from_its_own_lane_key() {
        let index = committed_index();
        for (row_id, slot) in &index.slots {
            for mode in &slot.modes {
                let obligation =
                    logical_obligation(&slot.catalog, &slot.identifier, *mode, &platform())
                        .expect("lane key");
                let (reached, _) = index.resolve(&obligation.key).expect("key resolves");
                assert_eq!(reached, row_id);
            }
        }
    }

    #[test]
    fn publication_is_atomic() {
        let root = scratch("atomic");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let ledger = root.join(LEDGER_PATH);

        let receipt = root.join("good.jsonl");
        write_receipt(&receipt, &[pass_row(&declared, "diagnostics")], binding());
        let clean = project(
            &root,
            &index,
            std::slice::from_ref(&receipt),
            RebuildMode::Write,
        )
        .expect("clean");
        assert!(clean.is_clean(), "{:?}", clean.rejections);
        let published = fs::read(&ledger).expect("published");

        // Check mode never mutates the destination, even when it differs.
        let wider = index_of(&[declared.clone(), identity(1, "diagnostics")]);
        let checked = project(
            &root,
            &wider,
            std::slice::from_ref(&receipt),
            RebuildMode::Check,
        )
        .expect("check mode");
        assert!(!checked.is_clean(), "the wider universe is not covered");
        assert_eq!(fs::read(&ledger).expect("unchanged"), published);

        let clean_check = project(
            &root,
            &index,
            std::slice::from_ref(&receipt),
            RebuildMode::Check,
        )
        .expect("clean check");
        assert!(clean_check.is_clean());
        assert!(!clean_check.changed);
        assert_eq!(fs::read(&ledger).expect("unchanged"), published);

        // A rejected rebuild leaves the previous publication byte-for-byte.
        let rejected = project(
            &root,
            &wider,
            std::slice::from_ref(&receipt),
            RebuildMode::Write,
        )
        .expect("rejected rebuild");
        assert!(!rejected.is_clean());
        assert_eq!(fs::read(&ledger).expect("preserved"), published);

        // A malformed late input aborts before publication.
        let truncated = root.join("truncated.jsonl");
        let text = fs::read_to_string(&receipt).expect("receipt text");
        let head = text.lines().next().expect("header line");
        fs::write(&truncated, format!("{head}\n")).expect("truncate");
        let error = project(&root, &index, &[truncated], RebuildMode::Write)
            .expect_err("a truncated receipt cannot publish");
        assert_eq!(error.code(), ErrorCode::Schema);
        assert_eq!(fs::read(&ledger).expect("preserved"), published);

        // An I/O failure after temporary-file creation but before rename
        // preserves the old publication and exercises the drop guard.
        FAIL_PUBLICATION_AFTER_TEMP_CREATE.with(|fail| fail.set(true));
        let error = rebuild_projection(
            &root,
            &index,
            OTHER,
            std::slice::from_ref(&receipt),
            RebuildMode::Write,
            &expected_bindings(),
            &BTreeMap::new(),
        )
        .expect_err("injected publication failure");
        assert_eq!(error.code(), ErrorCode::Io);
        assert_eq!(fs::read(&ledger).expect("preserved"), published);

        // No temporary file survives any of those paths.
        let leftovers: Vec<PathBuf> = fs::read_dir(root.join("proof"))
            .expect("proof dir")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.contains(".rebuild."))
            })
            .collect();
        assert!(leftovers.is_empty(), "{leftovers:?}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn rejects_duplicate_or_unknown_row() {
        let root = scratch("duplicate");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));

        // Two receipts must not both claim the same obligation and coordinates.
        let first = root.join("first.jsonl");
        let second = root.join("second.jsonl");
        write_receipt(&first, &[pass_row(&declared, "diagnostics")], binding());
        write_receipt(&second, &[pass_row(&declared, "diagnostics")], binding());
        let report =
            project(&root, &index, &[first, second], RebuildMode::Write).expect("duplicate");
        assert!(
            report
                .rejections
                .iter()
                .any(|rejection| matches!(rejection.reason, RejectionReason::DuplicateReceipt)),
            "a second claim is a forgery surface: {:?}",
            report.rejections
        );
        assert!(!report.is_clean());
        assert!(!root.join(LEDGER_PATH).exists());

        // A receipt naming an obligation the manifest never declared is unknown.
        let unknown = root.join("unknown.jsonl");
        write_receipt(
            &unknown,
            &[pass_row(&identity(7, "diagnostics"), "diagnostics")],
            binding(),
        );
        let report = project(&root, &index, &[unknown], RebuildMode::Write).expect("unknown");
        assert!(
            report
                .rejections
                .iter()
                .any(|rejection| rejection.reason == RejectionReason::UnknownObligation),
            "{:?}",
            report.rejections
        );
        assert!(!root.join(LEDGER_PATH).exists());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn check_mode_does_not_mutate() {
        let root = scratch("check");
        let declared = identity(0, "diagnostics");
        let index = index_of(std::slice::from_ref(&declared));
        let ledger = root.join(LEDGER_PATH);

        let receipt = root.join("good.jsonl");
        write_receipt(&receipt, &[pass_row(&declared, "diagnostics")], binding());
        let written = project(
            &root,
            &index,
            std::slice::from_ref(&receipt),
            RebuildMode::Write,
        )
        .expect("write");
        assert!(written.is_clean(), "{:?}", written.rejections);
        let published = fs::read(&ledger).expect("published");

        // A clean check reports no change and writes nothing.
        let checked = project(
            &root,
            &index,
            std::slice::from_ref(&receipt),
            RebuildMode::Check,
        )
        .expect("check");
        assert!(checked.is_clean());
        assert!(!checked.changed);
        assert_eq!(fs::read(&ledger).expect("unchanged"), published);

        // A drifted on-disk ledger is detected but never healed in check mode.
        fs::write(&ledger, b"corrupted").expect("corrupt");
        let drifted =
            project(&root, &index, &[receipt], RebuildMode::Check).expect("drifted check");
        assert!(drifted.is_clean(), "the projection itself is clean");
        assert!(
            drifted.changed,
            "the drifted ledger differs from the projection"
        );
        assert_eq!(fs::read(&ledger).expect("still drifted"), b"corrupted");

        // No temporary publication artifact was left behind by either check.
        let temps: Vec<PathBuf> = fs::read_dir(root.join("proof"))
            .expect("proof dir")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.contains(".rebuild."))
            })
            .collect();
        assert!(temps.is_empty(), "{temps:?}");

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn discovers_canonical_merged_receipts() {
        let root = scratch("discover");
        let nightly = root.join("verification/evidence/nightly-merged");
        fs::create_dir_all(&nightly).expect("nightly merged");
        let later = nightly.join("z-test262-interpreter-linux.jsonl");
        let earlier = nightly.join("a-typescript-interpreter-linux.jsonl");
        fs::write(&later, b"later").expect("later receipt");
        fs::write(&earlier, b"earlier").expect("earlier receipt");

        // Raw shards are deliberately nested below a non-owner and must not be
        // discovered or conflict with the merged canonical set.
        let raw = root.join("verification/evidence/nightly/test262/interpreter/linux");
        fs::create_dir_all(&raw).expect("raw shards");
        let raw_receipt = raw.join("0.jsonl");
        fs::write(&raw_receipt, b"raw").expect("raw receipt");

        let receipts = discover_receipts(&root).expect("discover nightly merged");
        assert_eq!(receipts, vec![earlier.clone(), later.clone()]);
        assert_eq!(fs::read(&earlier).expect("earlier unchanged"), b"earlier");
        assert_eq!(fs::read(&later).expect("later unchanged"), b"later");
        assert_eq!(fs::read(&raw_receipt).expect("raw unchanged"), b"raw");

        // Two populated owners are ambiguous; discovery never concatenates or
        // silently chooses one run over another.
        let pr = root.join("verification/evidence/pr-merged");
        fs::create_dir_all(&pr).expect("pr merged");
        let pr_receipt = pr.join("test262-interpreter-linux.jsonl");
        fs::write(&pr_receipt, b"pr").expect("pr receipt");
        let error = discover_receipts(&root).expect_err("ambiguous owners");
        assert_eq!(error.code(), ErrorCode::SetMismatch);
        assert_eq!(fs::read(&pr_receipt).expect("pr unchanged"), b"pr");

        let _ = fs::remove_dir_all(&root);
    }

    /// The generated-output allowlist is byte-exact and closed: the ledger
    /// path matches only itself, each canonical owner directory admits only
    /// its own immediate `.jsonl` children, and nested paths, sibling
    /// directories, wrong suffixes, and case variants are all candidate
    /// source. This is the shared predicate `suite/completion.rs` relies on
    /// for both the committed-tree projection and the dirty gate, so its
    /// contract is pinned here independent of any real Git repository.
    #[test]
    fn is_generated_run_output_matches_exact_allowlist_only() {
        assert!(is_generated_run_output(b"proof/completeness-ledger.json"));
        assert!(!is_generated_run_output(
            b"proof/completeness-ledger.json.bak"
        ));
        assert!(!is_generated_run_output(b"proof/completeness-ledger"));
        assert!(!is_generated_run_output(b"Proof/completeness-ledger.json"));
        assert!(!is_generated_run_output(b"proof/completeness_ledger.json"));

        for dir in RECEIPT_SET_DIRS {
            let direct = format!("{dir}/a.jsonl");
            assert!(
                is_generated_run_output(direct.as_bytes()),
                "{direct} must be accepted"
            );

            let nested = format!("{dir}/sub/a.jsonl");
            assert!(
                !is_generated_run_output(nested.as_bytes()),
                "{nested} must be rejected"
            );

            let sibling = format!("{dir}-extra/a.jsonl");
            assert!(
                !is_generated_run_output(sibling.as_bytes()),
                "{sibling} must be rejected"
            );

            let wrong_suffix = format!("{dir}/a.json");
            assert!(
                !is_generated_run_output(wrong_suffix.as_bytes()),
                "{wrong_suffix} must be rejected"
            );

            let tmp_suffix = format!("{dir}/a.jsonl.tmp");
            assert!(
                !is_generated_run_output(tmp_suffix.as_bytes()),
                "{tmp_suffix} must be rejected"
            );

            let embedded_suffix = format!("{dir}/foo.jsonl.rs");
            assert!(
                !is_generated_run_output(embedded_suffix.as_bytes()),
                "{embedded_suffix} must be rejected"
            );

            let wrong_case = format!("{dir}/a.JSONL");
            assert!(
                !is_generated_run_output(wrong_case.as_bytes()),
                "{wrong_case} must be rejected"
            );
        }
    }
}
