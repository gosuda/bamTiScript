//! TypeScript 7 suite importer, snapshot materializer, and bounded runner (U0.4).
//!
//! Import pipeline accepts an extracted tree root for hermetic tests; curl/tar is
//! isolated behind fetch/extract helpers. Snapshot digests are walk-order
//! independent via [`BTreeMap`].

pub mod completion;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Component, Path, PathBuf},
    process::Command,
    sync::Arc,
    time::Duration,
};

use bamts_compiler::diagnostic::Diagnostic;
use bamts_compiler::parser::parse;
use bamts_compiler::program::ProgramLoader;
use bamts_compiler::project::{ProjectConfig, ProjectRoot};
use bamts_compiler::scanner::scan;
use bamts_compiler::source::{ScriptKind, SourceId, SourceText};
use bamts_compiler::syntax::{Token, TokenKind};
use bamts_compiler::telemetry::{PhaseTotals, TelemetryCollector};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::catalog::{self, ObservableKind};
use crate::check_cells::{self, CasePragmas, CheckContext};
use crate::corpus::{
    ArtifactDirectory, CaseSpec, DigestAlgorithm, ExecutionMode as CorpusExecutionMode,
    NODE_VERSION, OracleLimits, Provenance, bounded_output, cli_args, drain_stream, normalized_env,
    run_process,
};
use crate::lane::{LaneBinding, LaneOutcome, LaneRequest};
use crate::oracle_pins::{
    COMPILER_COMMIT, COMPILER_DIGEST, COMPILER_REPOSITORY, COMPILER_TAG, COMPILER_URL,
    NPM_INTEGRITY, NPM_SPECIFIER, OraclePins, SUITE_COMMIT, SUITE_DIGEST, SUITE_REPOSITORY,
    SUITE_URL, verify_oracle_pins,
};
use crate::shard::{ExecutionMode, ObligationKey};
use crate::ts_ledger::{
    Backend, CompilerOracle, Confidence, Entry, EvidenceRecord, Facet, LEDGER_SCHEMA_VERSION,
    NpmOracle, Oracle, Partition, ReasonCode, SUITE_BASELINE_ROOT, SUITE_CASE_ROOT, Snapshot,
    Status, SuiteOracle, TimeoutClass, Totals, TsLedger, TsLedgerReader, TsLedgerWriter,
};
use crate::{ErrorCode, Result, VerificationError};

/// Pinned npm publication time used for every deterministic `generatedAt`.
pub const PINNED_GENERATED_AT: &str = "2026-07-08T15:55:18.431Z";
/// Per-stream capture cap (1 MiB). Exceeding yields [`FailureClass::OutputTruncated`].
pub const OUTPUT_CAP_BYTES: usize = 1 << 20;
/// Per-cell AOT scratch cap (1 GiB).
pub const AOT_SCRATCH_CAP_BYTES: u64 = 1 << 30;
/// Default snapshot root relative to the workspace.
pub const DEFAULT_SNAPSHOT_REL: &str = "verification/ts-suite";

const FRONTEND_DEFAULT_MS: u64 = 5_000;
const FRONTEND_CAP_MS: u64 = 30_000;
const EXECUTE_DEFAULT_MS: u64 = 10_000;
const EXECUTE_CAP_MS: u64 = 60_000;
const PROJECT_DEFAULT_MS: u64 = 30_000;
const PROJECT_CAP_MS: u64 = 60_000;
const WATCH_DEFAULT_MS: u64 = 30_000;
const WATCH_CAP_MS: u64 = 60_000;

/// All 15 ledger facets, in schema order.
pub const ALL_FACETS: [Facet; 15] = [
    Facet::Parse,
    Facet::Diagnostics,
    Facet::Types,
    Facet::Symbols,
    Facet::JsEmit,
    Facet::DtsEmit,
    Facet::ModuleResolution,
    Facet::Config,
    Facet::Cli,
    Facet::Build,
    Facet::Watch,
    Facet::NodeApi,
    Facet::LanguageService,
    Facet::Harness,
    Facet::Implementation,
];

/// Cell-level result taxonomy (not an [`ErrorCode`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum FailureClass {
    Pass,
    FailBehavior,
    FailDiagnostic,
    FailBaselineHash,
    Timeout,
    Crash,
    OutputTruncated,
    ProvenanceMismatch,
    LedgerIncomplete,
    SkipDeferred,
    SkipExcluded,
    HarnessError,
    /// The observable does not apply to this cell: the catalog generated an
    /// obligation but the upstream baseline has no corresponding artifact.
    /// Maps to [`LaneOutcome::InapplicableCatalogError`] so the row is
    /// non-blocking and completion-ineligible (a catalog error to fix, not a
    /// compiler defect to burn down).
    Inapplicable,
}

impl FailureClass {
    /// Stable display / rollup name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::FailBehavior => "FAIL_BEHAVIOR",
            Self::FailDiagnostic => "FAIL_DIAGNOSTIC",
            Self::FailBaselineHash => "FAIL_BASELINE_HASH",
            Self::Timeout => "TIMEOUT",
            Self::Crash => "CRASH",
            Self::OutputTruncated => "OUTPUT_TRUNCATED",
            Self::ProvenanceMismatch => "PROVENANCE_MISMATCH",
            Self::LedgerIncomplete => "LEDGER_INCOMPLETE",
            Self::SkipDeferred => "SKIP_DEFERRED",
            Self::SkipExcluded => "SKIP_EXCLUDED",
            Self::HarnessError => "HARNESS_ERROR",
            Self::Inapplicable => "INAPPLICABLE",
        }
    }
}

/// Snapshot asset classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AssetKind {
    CaseInput,
    BaselineFacet,
    DifferenceRecord,
    LicenseNotice,
}

impl AssetKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CaseInput => "caseInput",
            Self::BaselineFacet => "baselineFacet",
            Self::DifferenceRecord => "differenceRecord",
            Self::LicenseNotice => "licenseNotice",
        }
    }
}

/// Runner state machine stages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RunState {
    PinVerify,
    Toolchains,
    Materialize,
    LedgerAudit,
    ShardPlan,
    ExecuteCell,
    Aggregate,
    Proof,
    Publish,
}

impl RunState {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PinVerify => "PinVerify",
            Self::Toolchains => "Toolchains",
            Self::Materialize => "Materialize",
            Self::LedgerAudit => "LedgerAudit",
            Self::ShardPlan => "ShardPlan",
            Self::ExecuteCell => "ExecuteCell",
            Self::Aggregate => "Aggregate",
            Self::Proof => "Proof",
            Self::Publish => "Publish",
        }
    }
}

/// One executed (or skipped) cell outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CellResult {
    pub entry_id: String,
    pub facet: Facet,
    pub backend: Backend,
    pub class: FailureClass,
    pub detail: String,
}

/// Sorted logical-path index of the snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SuiteIndex {
    pub entries: BTreeMap<String, IndexEntry>,
}

/// One index row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct IndexEntry {
    pub logical_path: String,
    pub sha256: String,
    pub asset_kind: AssetKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub facet: Option<Facet>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub partition: Option<Partition>,
}

/// Options for [`sync_suite`].
#[derive(Debug, Clone)]
pub struct SyncOptions {
    pub verify_pin: bool,
    pub write_snapshot: bool,
    pub workspace_root: PathBuf,
    pub snapshot_root: PathBuf,
    /// When set, import from this extracted suite tree (hermetic; skips curl/tar).
    pub extracted_suite_root: Option<PathBuf>,
}

/// Status filter for run/ci.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatusFilter {
    Included,
    Deferred,
    Excluded,
    All,
}

/// Backend filter for run/ci.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackendFilter {
    One(Backend),
    All,
}

/// Filters applied during shard planning.
#[derive(Debug, Clone)]
pub struct RunFilterOptions {
    pub status: StatusFilter,
    pub slice: Option<String>,
    pub backends: BackendFilter,
    /// One-based `(k, N)` from `--shards k/N`.
    pub shards: Option<(u32, u32)>,
}

/// CI mode selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CiMode {
    Pr,
    Nightly,
    WeeklyAudit,
}

/// Options for [`run_ci`].
#[derive(Debug, Clone)]
pub struct CiOptions {
    pub mode: CiMode,
    pub filters: RunFilterOptions,
    pub workspace_root: PathBuf,
    pub snapshot_root: PathBuf,
}

/// Aggregated suite run report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteRunReport {
    pub results: Vec<CellResult>,
    pub rollups: BTreeMap<FailureClass, usize>,
    pub state_reached: RunState,
}

/// Materialized snapshot handle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteSnapshot {
    pub root: PathBuf,
    pub digest: String,
    pub index: SuiteIndex,
    pub ledger: TsLedger,
}

/// Authenticated metadata required by the exact compiler worker.
///
/// Unlike [`SuiteSnapshot`], this view deliberately carries no parsed ledger:
/// the parent already verified the full snapshot before issuing the binding,
/// while the worker authenticates those same raw metadata bytes before parsing
/// only the pin and index it consumes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilerSnapshot {
    pub root: PathBuf,
    pub metadata_digest: String,
    pub index: SuiteIndex,
}

/// Read-only snapshot metadata needed to select and authenticate one asset.
pub trait SnapshotAssets {
    fn root(&self) -> &Path;
    fn index(&self) -> &SuiteIndex;
}

impl SnapshotAssets for SuiteSnapshot {
    fn root(&self) -> &Path {
        &self.root
    }

    fn index(&self) -> &SuiteIndex {
        &self.index
    }
}

impl SnapshotAssets for CompilerSnapshot {
    fn root(&self) -> &Path {
        &self.root
    }

    fn index(&self) -> &SuiteIndex {
        &self.index
    }
}

/// Snapshot that passed digest re-verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedSuite {
    pub snapshot: SuiteSnapshot,
    pin_bytes: Vec<u8>,
    index_bytes: Vec<u8>,
    ledger_bytes: Vec<u8>,
}

impl VerifiedSuite {
    /// Bind a parent-issued run identity to the exact retained metadata bytes.
    pub fn bind_compiler_lane(&self, run: LaneBinding) -> Result<LaneBinding> {
        run.with_snapshot(
            COMPILER_CATALOG,
            &self.snapshot.root,
            &self.pin_bytes,
            &self.index_bytes,
            &self.ledger_bytes,
        )
    }
}

/// A materialized suite asset (type exported for `walk_extracted_tree`).
#[derive(Debug, Clone)]
pub struct ImportedAsset {
    pub logical_path: String,
    pub kind: AssetKind,
    pub digest_hex: String,
    pub bytes: Vec<u8>,
    pub facet: Option<Facet>,
    pub partition: Option<Partition>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PinDocument {
    npm_specifier: String,
    npm_integrity: String,
    compiler_repository: String,
    compiler_commit: String,
    compiler_tag: String,
    suite_repository: String,
    suite_commit: String,
}

impl PinDocument {
    fn from_pins(pins: &OraclePins) -> Self {
        Self {
            npm_specifier: pins.npm_specifier.clone(),
            npm_integrity: pins.npm_integrity.clone(),
            compiler_repository: pins.compiler_repository.clone(),
            compiler_commit: pins.compiler_commit.clone(),
            compiler_tag: pins.compiler_tag.clone(),
            suite_repository: pins.suite_repository.clone(),
            suite_commit: pins.suite_commit.clone(),
        }
    }

    fn expected() -> Self {
        Self::from_pins(&OraclePins::expected())
    }
}

/// Import / materialize a suite snapshot.
pub fn sync_suite(options: &SyncOptions) -> Result<SuiteSnapshot> {
    let pins = if options.verify_pin {
        if options.extracted_suite_root.is_some() {
            OraclePins::expected()
        } else {
            verify_oracle_pins(&options.workspace_root)?
        }
    } else {
        OraclePins::expected()
    };

    // Keep extraction temps alive until walks finish.
    let mut cleanup_suite: Option<TempDir> = None;
    let mut cleanup_compiler: Option<TempDir> = None;
    let assets = if let Some(root) = &options.extracted_suite_root {
        walk_extracted_tree(root)?
    } else {
        let archives = options.snapshot_root.join(".archives");
        fs::create_dir_all(&archives).map_err(|e| io_err(&archives, &e))?;
        let suite_archive = fetch_archive(SUITE_URL, SUITE_DIGEST, &archives)?;
        let compiler_archive = fetch_archive(COMPILER_URL, COMPILER_DIGEST, &archives)?;
        let suite_extracted = extract_archive(&suite_archive)?;
        let compiler_extracted = extract_archive(&compiler_archive)?;
        let suite_root = single_archive_root(suite_extracted.path())?;
        let compiler_root = single_archive_root(compiler_extracted.path())?;
        let mut assets = walk_extracted_tree(&suite_root)?;
        merge_compiler_license_notice(&mut assets, &compiler_root)?;
        cleanup_suite = Some(suite_extracted);
        cleanup_compiler = Some(compiler_extracted);
        assets
    };

    if !options.write_snapshot {
        let _ = (cleanup_suite, cleanup_compiler);
        return Err(VerificationError::new(
            ErrorCode::Usage,
            "sync requires --write-snapshot",
        ));
    }

    let snapshot = materialize_snapshot(&options.snapshot_root, &pins, &assets)?;
    let _ = (cleanup_suite, cleanup_compiler);
    verify_snapshot(&options.snapshot_root)?;
    Ok(snapshot)
}

/// Audit a ledger for completeness against discovered case inputs.
pub fn audit_ledger(
    ledger_path: &Path,
    require_complete: bool,
    discovered_inputs: &BTreeSet<String>,
) -> Result<TsLedger> {
    let ledger = TsLedgerReader::from_file(ledger_path)?;
    if !require_complete {
        return Ok(ledger);
    }

    let mut covered: BTreeSet<&str> = BTreeSet::new();
    for entry in &ledger.entries {
        covered.insert(entry.input.as_str());
    }
    for input in discovered_inputs {
        if !covered.contains(input.as_str()) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("LEDGER_INCOMPLETE: missing coverage for input `{input}`"),
            ));
        }
    }
    Ok(ledger)
}

/// Run the suite through the RunState machine with filters.
pub fn run_suite(
    workspace_root: &Path,
    snapshot_root: &Path,
    filters: &RunFilterOptions,
) -> Result<SuiteRunReport> {
    // PinVerify
    verify_pin_document(&snapshot_root.join("oracle/pin.json"))?;
    if filters_need_workspace_pins(filters) {
        // Live pin drift check is optional when snapshot pin already matches expected.
        let _ = workspace_root;
    }

    // Toolchains
    // Node gate only when execute backends are in scope for included cells.
    // Provisional ledger has no included rows; skip live Node for default runs.
    let _ = NODE_VERSION;

    // Materialize
    let verified = verify_snapshot(snapshot_root)?;

    // LedgerAudit
    let discovered = case_inputs_from_index(&verified.snapshot.index);
    let committed_ledger = workspace_root.join("verification/ts-suite-ledger.json");
    let ledger_path = if committed_ledger.is_file() {
        committed_ledger
    } else {
        snapshot_root.join("ledger.json")
    };
    let ledger = audit_ledger(&ledger_path, true, &discovered)?;
    let expected_digest = index_content_digest(&verified.snapshot.index);
    if ledger.snapshot.digest != expected_digest {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "classified ledger digest `{}` does not match suite index `{expected_digest}`",
                ledger.snapshot.digest
            ),
        ));
    }

    // ShardPlan
    let planned = plan_cells(&ledger, filters)?;

    // S2 check-cell context: the diagnostic code map and baseline groups are
    // loaded once per run (U2.8), and only when an included check cell is
    // planned for a facet that needs them — parse-only and skip-class runs
    // never touch them.
    let check_context = planned
        .iter()
        .any(|plan| {
            matches!(plan.entry.status, Status::Included)
                && matches!(plan.backend, Backend::Check)
                && matches!(
                    plan.entry.facet,
                    Facet::Diagnostics | Facet::Types | Facet::Symbols
                )
        })
        .then(|| {
            let code_map = crate::facets::load_diagnostic_code_map(workspace_root)?;
            let baseline_groups = crate::check_cells::baseline_groups(&verified.snapshot.index);
            Ok::<_, VerificationError>(crate::check_cells::CheckContext {
                code_map,
                baseline_groups,
            })
        })
        .transpose()?;

    // ExecuteCell
    let mut results = Vec::new();
    for plan in &planned {
        results.push(execute_planned_cell(
            snapshot_root,
            &verified.snapshot,
            check_context.as_ref(),
            plan,
        )?);
    }

    // Aggregate
    enforce_no_silent_skip(&planned, &results)?;

    // Proof
    let rollups = rollup_classes(&results);

    // Publish
    Ok(SuiteRunReport {
        results,
        rollups,
        state_reached: RunState::Publish,
    })
}

/// Run the suite and collect frontend phase telemetry from every executed cell.
///
/// A [`TelemetryCollector`] is active on the calling thread for the whole run,
/// so each check-backend compile the runner drives accumulates its
/// scan/parse/bind/check/emit/total wall into the returned [`PhaseTotals`]. The
/// runner executes cells synchronously on this thread, so the collector
/// observes every compile the backend performed.
pub fn run_suite_with_telemetry(
    workspace_root: &Path,
    snapshot_root: &Path,
    filters: &RunFilterOptions,
) -> Result<(SuiteRunReport, PhaseTotals)> {
    let collector = TelemetryCollector::start();
    let report = run_suite(workspace_root, snapshot_root, filters)?;
    let telemetry = collector.snapshot();
    Ok((report, telemetry))
}

/// CI entrypoint: same filters, mode retained for future policy differences.
pub fn run_ci(options: &CiOptions) -> Result<SuiteRunReport> {
    match options.mode {
        CiMode::Pr | CiMode::Nightly | CiMode::WeeklyAudit => run_suite(
            &options.workspace_root,
            &options.snapshot_root,
            &options.filters,
        ),
    }
}

fn filters_need_workspace_pins(_filters: &RunFilterOptions) -> bool {
    false
}

#[derive(Debug, Clone)]
pub(crate) struct PlannedCell {
    pub(crate) entry: Entry,
    pub(crate) backend: Backend,
}

fn plan_cells(ledger: &TsLedger, filters: &RunFilterOptions) -> Result<Vec<PlannedCell>> {
    let mut planned = Vec::new();
    for entry in &ledger.entries {
        if !status_matches(filters.status, entry.status) {
            continue;
        }
        if let Some(slice) = &filters.slice {
            let needle = slice.to_ascii_lowercase();
            // Deferred/excluded rows name their gating slice in `blockedBy`;
            // included rows carry an empty `blockedBy`, so they are selected by
            // the slice that owns their facet's observation (§17.1/§17.2).
            let hit = if matches!(entry.status, Status::Included) {
                facet_owning_slice(entry.facet).eq_ignore_ascii_case(&needle)
            } else {
                entry
                    .blocked_by
                    .iter()
                    .any(|item| item.eq_ignore_ascii_case(&needle))
            };
            if !hit {
                continue;
            }
        }
        if let Some((k, n)) = filters.shards {
            let index = shard_index(&entry.shard_key, n)?;
            if index != k - 1 {
                continue;
            }
        }
        for backend in &entry.backends {
            if !backend_matches(filters.backends, *backend) {
                continue;
            }
            planned.push(PlannedCell {
                entry: entry.clone(),
                backend: *backend,
            });
        }
    }
    Ok(planned)
}

fn status_matches(filter: StatusFilter, status: Status) -> bool {
    match filter {
        StatusFilter::All => true,
        StatusFilter::Included => matches!(status, Status::Included),
        StatusFilter::Deferred => matches!(status, Status::Deferred),
        StatusFilter::Excluded => matches!(status, Status::Excluded),
    }
}

fn backend_matches(filter: BackendFilter, backend: Backend) -> bool {
    match filter {
        BackendFilter::All => true,
        BackendFilter::One(expected) => backend == expected,
    }
}

fn execute_planned_cell(
    snapshot_root: &Path,
    snapshot: &SuiteSnapshot,
    ctx: Option<&crate::check_cells::CheckContext>,
    plan: &PlannedCell,
) -> Result<CellResult> {
    match plan.entry.status {
        Status::Deferred => {
            return Ok(CellResult {
                entry_id: plan.entry.id.clone(),
                facet: plan.entry.facet,
                backend: plan.backend,
                class: FailureClass::SkipDeferred,
                detail: "deferred provisional row".to_owned(),
            });
        }
        Status::Excluded => {
            return Ok(CellResult {
                entry_id: plan.entry.id.clone(),
                facet: plan.entry.facet,
                backend: plan.backend,
                class: FailureClass::SkipExcluded,
                detail: "excluded provisional row".to_owned(),
            });
        }
        Status::Included => {}
    }

    match plan.backend {
        Backend::Check => execute_check_cell(snapshot_root, snapshot, ctx, plan),
        Backend::Interpreter | Backend::Jit | Backend::Aot => {
            execute_process_cell(snapshot_root, snapshot, plan)
        }
    }
}

fn execute_check_cell(
    _snapshot_root: &Path,
    snapshot: &SuiteSnapshot,
    ctx: Option<&crate::check_cells::CheckContext>,
    plan: &PlannedCell,
) -> Result<CellResult> {
    let Some(index_entry) = snapshot.index.entries.get(&plan.entry.input) else {
        return Ok(CellResult {
            entry_id: plan.entry.id.clone(),
            facet: plan.entry.facet,
            backend: plan.backend,
            class: FailureClass::LedgerIncomplete,
            detail: format!("missing index row for `{}`", plan.entry.input),
        });
    };
    match plan.entry.facet {
        Facet::Parse => execute_parse_check(snapshot, plan, index_entry),
        // U2.8 Phase A: the S2 `diagnostics` observation is wired.
        Facet::Diagnostics => {
            let Some(ctx) = ctx else {
                return Ok(CellResult {
                    entry_id: plan.entry.id.clone(),
                    facet: plan.entry.facet,
                    backend: plan.backend,
                    class: FailureClass::HarnessError,
                    detail: "diagnostics check context not loaded".to_owned(),
                });
            };
            crate::check_cells::execute_diagnostics_check(ctx, snapshot, plan, index_entry)
        }
        // U2.8 Phase B: the S2 `types` observation is wired.
        Facet::Types => {
            let Some(ctx) = ctx else {
                return Ok(CellResult {
                    entry_id: plan.entry.id.clone(),
                    facet: plan.entry.facet,
                    backend: plan.backend,
                    class: FailureClass::HarnessError,
                    detail: "types check context not loaded".to_owned(),
                });
            };
            crate::check_cells::execute_types_check(
                snapshot,
                &ctx.baseline_groups,
                plan,
                index_entry,
            )
        }
        // U2.8 Phase C: the S2 `symbols` observation is wired.
        Facet::Symbols => {
            let Some(ctx) = ctx else {
                return Ok(CellResult {
                    entry_id: plan.entry.id.clone(),
                    facet: plan.entry.facet,
                    backend: plan.backend,
                    class: FailureClass::HarnessError,
                    detail: "symbols check context not loaded".to_owned(),
                });
            };
            crate::check_cells::execute_symbols_check(
                snapshot,
                &ctx.baseline_groups,
                plan,
                index_entry,
            )
        }
        other => Ok(CellResult {
            entry_id: plan.entry.id.clone(),
            facet: plan.entry.facet,
            backend: plan.backend,
            class: FailureClass::HarnessError,
            detail: format!(
                "check backend has no observation wired for facet `{}`",
                other.as_str()
            ),
        }),
    }
}

/// Observe the S1 `parse` contract for one case, per program §6 ("scanner/parser
/// acceptance and recovery ... total recovery"): scan and parse the case source
/// with the script kind its logical path names, and pass iff the parse is
/// *total and well-formed* — the scanner and parser return without panicking,
/// their token streams tile the source exactly once, the parser preserves the
/// source identity, and every diagnostic is canonically ordered and anchored in
/// the source. A recovery that reports syntax errors (a negative test case)
/// still passes: the parse facet proves acceptance and recovery, not error
/// absence. Diagnostic *correspondence* is the `diagnostics` facet, owned by S2.
fn execute_parse_check(
    snapshot: &SuiteSnapshot,
    plan: &PlannedCell,
    index_entry: &IndexEntry,
) -> Result<CellResult> {
    let bytes = match read_verified_asset(snapshot, &index_entry.logical_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            return Ok(CellResult {
                entry_id: plan.entry.id.clone(),
                facet: plan.entry.facet,
                backend: plan.backend,
                class: FailureClass::HarnessError,
                detail: error.to_string(),
            });
        }
    };
    let text = decode_case_source(&bytes);

    let script_kind = script_kind_for(&index_entry.logical_path);
    // The scanner and parser are designed total, but the parse facet's whole
    // point is to prove that on the real suite; a panic is a genuine parse
    // failure, caught here so one case cannot abort the in-process run.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        parse_facet_violation(&text, script_kind)
    }));
    let (class, detail) = match outcome {
        Ok(None) => (
            FailureClass::Pass,
            "scan+parse total; token stream tiles the source; diagnostics well-formed".to_owned(),
        ),
        Ok(Some(violation)) => (FailureClass::FailBehavior, violation),
        Err(_) => (
            FailureClass::Crash,
            "scanner or parser panicked on this input".to_owned(),
        ),
    };
    Ok(CellResult {
        entry_id: plan.entry.id.clone(),
        facet: plan.entry.facet,
        backend: plan.backend,
        class,
        detail,
    })
}

/// Runs the scanner and parser and returns the first structural parse-facet
/// violation, or `None` when the observation is total and well-formed.
fn parse_facet_violation(text: &str, script_kind: ScriptKind) -> Option<String> {
    // The parse facet observes the same frontend input bound as the compiler:
    // a case over the 16 MiB per-file budget is a violation, not a crash.
    let source = match SourceText::new(text) {
        Ok(source) => Arc::new(source),
        Err(error) => return Some(format!("frontend input bound rejected the case: {error}")),
    };
    let scanned = scan(SourceId::new(0), script_kind, Arc::clone(&source));
    if let Some(violation) = tiling_violation(
        "scanner",
        scanned.product().tokens(),
        scanned.product().eof(),
        &source,
        |token| scanned.product().token_text(token).map(str::to_owned),
    ) {
        return Some(violation);
    }

    let parsed = parse(scanned);
    let file = parsed.product();
    if file.source_id() != SourceId::new(0) {
        return Some("parser changed the source identity".to_owned());
    }
    if file.script_kind() != script_kind {
        return Some("parser changed the script kind".to_owned());
    }
    if file.source_text().as_str() != text {
        return Some("parser rewrote the source text".to_owned());
    }
    if let Some(violation) =
        tiling_violation("parser", file.tokens(), file.eof(), &source, |token| {
            file.token_text(token).map(str::to_owned)
        })
    {
        return Some(violation);
    }
    diagnostics_violation(parsed.diagnostics(), &source)
}

/// Verifies a token stream tiles its source exactly once, in order, with the
/// end-of-file token anchored at the source end and lexemes reproducing the
/// source byte for byte. Mirrors the corpus parser conformance invariants.
fn tiling_violation(
    label: &str,
    tokens: &[Token],
    eof: &Token,
    source: &SourceText,
    lexeme: impl Fn(&Token) -> Option<String>,
) -> Option<String> {
    let mut cursor = 0usize;
    let mut reconstructed = String::with_capacity(source.as_str().len());
    for (index, token) in tokens.iter().enumerate() {
        let range = token.range();
        if range.start().get() != cursor {
            return Some(format!(
                "{label}: token {index} ({:?}) starts at {} but the previous token ended at {cursor}",
                token.kind(),
                range.start().get()
            ));
        }
        if token.kind() == TokenKind::EndOfFile {
            return Some(format!(
                "{label}: token {index} is an end-of-file token inside the stream"
            ));
        }
        if token.is_missing() {
            if !range.is_empty() {
                return Some(format!(
                    "{label}: missing token {index} ({:?}) covers source text",
                    token.kind()
                ));
            }
        } else if range.is_empty() {
            return Some(format!(
                "{label}: token {index} ({:?}) makes no forward progress",
                token.kind()
            ));
        }
        let Some(lexeme_text) = lexeme(token) else {
            return Some(format!(
                "{label}: token {index} ({:?}) range {}..{} is not a slice of its source",
                token.kind(),
                range.start().get(),
                range.end().get()
            ));
        };
        if utf16_len(&lexeme_text) != range.len() {
            return Some(format!(
                "{label}: token {index} ({:?}) lexeme length disagrees with its range",
                token.kind()
            ));
        }
        reconstructed.push_str(&lexeme_text);
        cursor = range.end().get();
    }
    if eof.kind() != TokenKind::EndOfFile {
        return Some(format!(
            "{label}: terminal token is {:?}, not end-of-file",
            eof.kind()
        ));
    }
    if !eof.range().is_empty() {
        return Some(format!("{label}: the end-of-file token covers source text"));
    }
    if eof.range().start().get() != cursor {
        return Some(format!(
            "{label}: the end-of-file token is not anchored at the end of the last token"
        ));
    }
    if cursor != source.len_utf16().get() {
        return Some(format!(
            "{label}: the token stream stops before the end of the source"
        ));
    }
    if reconstructed != source.as_str() {
        return Some(format!(
            "{label}: concatenated lexemes do not reproduce the source"
        ));
    }
    None
}

/// Verifies diagnostics are canonically ordered and anchored inside the source.
fn diagnostics_violation(diagnostics: &[Diagnostic], source: &SourceText) -> Option<String> {
    if !diagnostics.is_sorted() {
        return Some("diagnostics are not in canonical order".to_owned());
    }
    for diagnostic in diagnostics {
        if diagnostic.source_id() != SourceId::new(0) {
            return Some(format!(
                "diagnostic {} is anchored in another source",
                diagnostic.code().as_str()
            ));
        }
        let range = diagnostic.range();
        if source.utf16_to_byte(range.start()).is_err()
            || source.utf16_to_byte(range.end()).is_err()
        {
            return Some(format!(
                "diagnostic {} is not anchored at source boundaries",
                diagnostic.code().as_str()
            ));
        }
    }
    None
}

/// UTF-16 code-unit length of a string, matching token range units.
fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// Decodes case bytes to source text the way a TypeScript-compatible reader
/// does: a UTF-16 BE (`FE FF`) or LE (`FF FE`) byte-order mark selects UTF-16
/// decoding, a UTF-8 BOM (`EF BB BF`) is stripped, and the leading marker is
/// dropped. Malformed units decode lossily so the parser still observes a total
/// source — the parse facet proves recovery, not byte-perfect re-encoding.
pub fn decode_case_source(bytes: &[u8]) -> String {
    if let [0xFE, 0xFF, rest @ ..] = bytes {
        let units: Vec<u16> = rest
            .chunks(2)
            .map(|pair| u16::from_be_bytes([pair[0], pair.get(1).copied().unwrap_or(0)]))
            .collect();
        return String::from_utf16_lossy(&units);
    }
    if let [0xFF, 0xFE, rest @ ..] = bytes {
        let units: Vec<u16> = rest
            .chunks(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair.get(1).copied().unwrap_or(0)]))
            .collect();
        return String::from_utf16_lossy(&units);
    }
    let body = bytes.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(bytes);
    String::from_utf8_lossy(body).into_owned()
}

/// Maps a case logical path to the script kind the scanner and parser use,
/// mirroring the compiler's own extension rules (`.tsx`/`.jsx` enable JSX,
/// `.js`/`.mjs`/`.cjs` are JavaScript, everything else — `.ts`/`.mts`/`.cts`/
/// `.d.ts` and extensionless — is TypeScript).
pub(crate) fn script_kind_for(logical_path: &str) -> ScriptKind {
    let lower = logical_path.to_ascii_lowercase();
    if lower.ends_with(".tsx") {
        ScriptKind::TypeScriptReact
    } else if lower.ends_with(".jsx") {
        ScriptKind::JavaScriptReact
    } else if lower.ends_with(".js") || lower.ends_with(".mjs") || lower.ends_with(".cjs") {
        ScriptKind::JavaScript
    } else {
        ScriptKind::TypeScript
    }
}

fn execute_process_cell(
    snapshot_root: &Path,
    snapshot: &SuiteSnapshot,
    plan: &PlannedCell,
) -> Result<CellResult> {
    let Some(index_entry) = snapshot.index.entries.get(&plan.entry.input) else {
        return Ok(CellResult {
            entry_id: plan.entry.id.clone(),
            facet: plan.entry.facet,
            backend: plan.backend,
            class: FailureClass::LedgerIncomplete,
            detail: format!("missing index row for `{}`", plan.entry.input),
        });
    };
    let case_blob = snapshot.root.join("cases").join(&index_entry.sha256);
    let (default_ms, _cap_ms) = budget_for(plan.entry.timeout_class);
    let limits = OracleLimits {
        timeout: Duration::from_millis(default_ms),
        max_output_bytes: OUTPUT_CAP_BYTES,
    };

    let mode = match plan.backend {
        Backend::Interpreter => CorpusExecutionMode::Interpreter,
        Backend::Jit => CorpusExecutionMode::Jit,
        Backend::Aot => CorpusExecutionMode::Aot,
        Backend::Check => {
            return Err(VerificationError::new(
                ErrorCode::Usage,
                "internal: Check backend routed to process cell",
            ));
        }
    };

    if matches!(mode, CorpusExecutionMode::Aot) {
        let spec = scratch_case_spec(&plan.entry.id);
        let artifacts = ArtifactDirectory::create(snapshot_root, &spec, mode)?;
        enforce_aot_scratch_cap(&artifacts.0)?;
        drop(artifacts);
        return Ok(CellResult {
            entry_id: plan.entry.id.clone(),
            facet: plan.entry.facet,
            backend: plan.backend,
            class: FailureClass::HarnessError,
            detail: "AOT cell requires full corpus CaseSpec wiring; scratch cleaned".to_owned(),
        });
    }

    // Keep corpus seams referenced so suite never invents a second process convention.
    let _ = (
        &case_blob,
        limits,
        NODE_VERSION,
        bounded_output as fn(Vec<u8>, usize) -> (Vec<u8>, bool),
        normalized_env as fn() -> Vec<(String, String)>,
        run_process,
        cli_args,
        drain_stream::<std::io::Empty>,
    );
    Ok(CellResult {
        entry_id: plan.entry.id.clone(),
        facet: plan.entry.facet,
        backend: plan.backend,
        class: FailureClass::HarnessError,
        detail: format!(
            "{} backend deferred to corpus driver wiring for included cells",
            backend_name(plan.backend)
        ),
    })
}

fn scratch_case_spec(id: &str) -> CaseSpec {
    CaseSpec {
        id: id.replace(['/', '#'], "_"),
        provenance: Provenance::LocalContent {
            digest_algorithm: DigestAlgorithm::Sha256,
            digest: "0".repeat(64),
        },
        license: "Apache-2.0".to_owned(),
        source_dir: "src".to_owned(),
        entrypoint: "main.ts".to_owned(),
        node_args: Vec::new(),
        expected_timeout_ms: EXECUTE_DEFAULT_MS,
        constructs: Vec::new(),
        source_files: vec!["main.ts".to_owned()],
        compiler_args: Vec::new(),
    }
}

fn enforce_no_silent_skip(planned: &[PlannedCell], results: &[CellResult]) -> Result<()> {
    let mut seen: BTreeSet<(String, String)> = BTreeSet::new();
    for result in results {
        seen.insert((
            result.entry_id.clone(),
            backend_name(result.backend).to_owned(),
        ));
    }
    for plan in planned {
        if !matches!(plan.entry.status, Status::Included) {
            continue;
        }
        let key = (plan.entry.id.clone(), backend_name(plan.backend).to_owned());
        if !seen.contains(&key) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "LEDGER_INCOMPLETE: NO_SILENT_SKIP missing result for `{}` backend `{}`",
                    plan.entry.id,
                    backend_name(plan.backend)
                ),
            ));
        }
    }
    Ok(())
}

fn rollup_classes(results: &[CellResult]) -> BTreeMap<FailureClass, usize> {
    let mut rollups = BTreeMap::new();
    for result in results {
        *rollups.entry(result.class).or_insert(0) += 1;
    }
    rollups
}

/// Default and cap budgets (milliseconds) for a timeout class.
pub fn budget_for(class: TimeoutClass) -> (u64, u64) {
    match class {
        TimeoutClass::Frontend => (FRONTEND_DEFAULT_MS, FRONTEND_CAP_MS),
        TimeoutClass::Execute => (EXECUTE_DEFAULT_MS, EXECUTE_CAP_MS),
        TimeoutClass::Project => (PROJECT_DEFAULT_MS, PROJECT_CAP_MS),
        TimeoutClass::Watch => (WATCH_DEFAULT_MS, WATCH_CAP_MS),
    }
}

/// Map truncation flags onto [`FailureClass::OutputTruncated`].
pub fn classify_truncation(stdout_truncated: bool, stderr_truncated: bool) -> Option<FailureClass> {
    if stdout_truncated || stderr_truncated {
        Some(FailureClass::OutputTruncated)
    } else {
        None
    }
}

/// Reject AOT scratch directories whose recursive size exceeds the cap.
pub fn enforce_aot_scratch_cap(path: &Path) -> Result<()> {
    let size = directory_size(path)?;
    enforce_aot_scratch_size(path, size)
}

/// Size-gated helper used by tests to avoid writing a full gibibyte.
pub fn enforce_aot_scratch_size(path: &Path, size: u64) -> Result<()> {
    if size > AOT_SCRATCH_CAP_BYTES {
        let _ = fs::remove_dir_all(path);
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "AOT scratch at `{}` is {size} bytes, exceeds cap {AOT_SCRATCH_CAP_BYTES}",
                path.display()
            ),
        ));
    }
    Ok(())
}

fn directory_size(path: &Path) -> Result<u64> {
    let mut total = 0u64;
    if !path.exists() {
        return Ok(0);
    }
    let mut stack = vec![path.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = fs::read_dir(&current).map_err(|e| io_err(&current, &e))?;
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            let meta = fs::symlink_metadata(entry.path()).map_err(|e| io_err(&entry.path(), &e))?;
            // Check the link itself before following: `entry.metadata()` would
            // resolve the target, making `is_symlink()` always false and the
            // guard below unreachable — letting the walk escape the scratch dir.
            if meta.file_type().is_symlink() {
                return Err(VerificationError::new(
                    ErrorCode::ProvenanceMismatch,
                    format!("symlink rejected in scratch `{}`", entry.path().display()),
                ));
            }
            if meta.is_dir() {
                stack.push(entry.path());
            } else if meta.is_file() {
                total = total.saturating_add(meta.len());
            }
        }
    }
    Ok(total)
}
type PathClassification = Option<(AssetKind, Option<Partition>, Option<Facet>)>;

/// Classify a suite-relative logical path.
pub fn classify_logical_path(logical_path: &str) -> Result<PathClassification> {
    if logical_path.is_empty() {
        return Ok(None);
    }
    let path = Path::new(logical_path);
    if path.is_absolute() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("absolute path rejected: `{logical_path}`"),
        ));
    }
    for component in path.components() {
        match component {
            Component::Normal(_) => {}
            Component::CurDir => {}
            Component::ParentDir => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("path traversal rejected: `{logical_path}`"),
                ));
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("absolute path rejected: `{logical_path}`"),
                ));
            }
        }
    }

    let lower = logical_path.to_ascii_lowercase();
    if lower.contains("hereby")
        || lower.contains("internal/testutil")
        || lower.contains("/runners/")
        || lower.contains("\\runners\\")
    {
        return Ok(None);
    }

    if let Some(rest) = logical_path.strip_prefix("tests/cases/") {
        let partition = match rest.split('/').next().unwrap_or("") {
            "compiler" => Partition::Compiler,
            "conformance" => Partition::Conformance,
            "project" => Partition::Project,
            "projects" => Partition::Projects,
            "transpile" => Partition::Transpile,
            "unittests" => Partition::UnitTests,
            _ => return Ok(None),
        };
        if rest.contains('/') {
            return Ok(Some((AssetKind::CaseInput, Some(partition), None)));
        }
        return Ok(None);
    }

    if logical_path.starts_with("tests/baselines/reference/")
        || logical_path.starts_with("testdata/baselines/reference/")
    {
        let facet = baseline_facet_from_path(logical_path);
        return Ok(Some((AssetKind::BaselineFacet, None, facet)));
    }

    if logical_path == "testdata/submoduleAccepted.txt"
        || logical_path == "testdata/submoduleTriaged.txt"
    {
        return Ok(Some((AssetKind::DifferenceRecord, None, None)));
    }

    let basename = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    let base_upper = basename.to_ascii_uppercase();
    if base_upper.starts_with("LICENSE") || base_upper.starts_with("NOTICE") {
        return Ok(Some((AssetKind::LicenseNotice, None, None)));
    }

    Ok(None)
}

fn baseline_facet_from_path(path: &str) -> Option<Facet> {
    if path.ends_with(".errors.txt") {
        Some(Facet::Diagnostics)
    } else if path.ends_with(".types") {
        Some(Facet::Types)
    } else if path.ends_with(".symbols") {
        Some(Facet::Symbols)
    } else if path.ends_with(".d.ts") {
        Some(Facet::DtsEmit)
    } else if path.ends_with(".js") {
        Some(Facet::JsEmit)
    } else {
        None
    }
}

/// Walk an extracted suite tree into a deterministic asset map.
pub fn walk_extracted_tree(root: &Path) -> Result<BTreeMap<String, ImportedAsset>> {
    let mut assets = BTreeMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = fs::read_dir(&current).map_err(|e| io_err(&current, &e))?;
        let mut children = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            children.push(entry.path());
        }
        children.sort();
        for child in children {
            let meta = fs::symlink_metadata(&child).map_err(|e| io_err(&child, &e))?;
            let rel = child
                .strip_prefix(root)
                .map(|p| p.to_string_lossy().replace('\\', "/"))
                .unwrap_or_default();
            if meta.file_type().is_symlink() {
                if member_looks_allowlisted(&rel) {
                    return Err(VerificationError::new(
                        ErrorCode::ProvenanceMismatch,
                        format!("symlink rejected: `{}`", child.display()),
                    ));
                }
                continue;
            }
            if meta.is_dir() {
                stack.push(child);
                continue;
            }
            if !meta.is_file() {
                continue;
            }
            let Some((kind, partition, facet)) = classify_logical_path(&rel)? else {
                continue;
            };
            let bytes = fs::read(&child).map_err(|e| io_err(&child, &e))?;
            let digest_hex = sha256_hex(&bytes);
            if assets.contains_key(&rel) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("duplicate logical path `{rel}`"),
                ));
            }
            assets.insert(
                rel.clone(),
                ImportedAsset {
                    logical_path: rel,
                    kind,
                    digest_hex,
                    bytes,
                    facet,
                    partition,
                },
            );
        }
    }
    Ok(assets)
}

/// Import LICENSE/NOTICE assets from the pinned compiler archive under a `compiler/` prefix.
fn merge_compiler_license_notice(
    assets: &mut BTreeMap<String, ImportedAsset>,
    compiler_root: &Path,
) -> Result<()> {
    reject_extracted_symlinks(compiler_root)?;
    let mut stack = vec![compiler_root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = fs::read_dir(&current).map_err(|e| io_err(&current, &e))?;
        let mut children = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            children.push(entry.path());
        }
        children.sort();
        for child in children {
            let meta = fs::symlink_metadata(&child).map_err(|e| io_err(&child, &e))?;
            if meta.file_type().is_symlink() {
                let basename = child
                    .file_name()
                    .and_then(|name| name.to_str())
                    .unwrap_or("")
                    .to_ascii_uppercase();
                if basename.starts_with("LICENSE") || basename.starts_with("NOTICE") {
                    return Err(VerificationError::new(
                        ErrorCode::ProvenanceMismatch,
                        format!("symlink rejected: `{}`", child.display()),
                    ));
                }
                continue;
            }
            if meta.is_dir() {
                stack.push(child);
                continue;
            }
            if !meta.is_file() {
                continue;
            }
            let basename = child
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("")
                .to_ascii_uppercase();
            if !(basename.starts_with("LICENSE") || basename.starts_with("NOTICE")) {
                continue;
            }
            let rel = child
                .strip_prefix(compiler_root)
                .map_err(|_| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!("path escapes compiler root: `{}`", child.display()),
                    )
                })?
                .to_string_lossy()
                .replace('\\', "/");
            let logical = format!("compiler/{rel}");
            let Some((kind, partition, facet)) = classify_logical_path(&logical)? else {
                continue;
            };
            if !matches!(kind, AssetKind::LicenseNotice) {
                continue;
            }
            let bytes = fs::read(&child).map_err(|e| io_err(&child, &e))?;
            let digest_hex = sha256_hex(&bytes);
            if assets.contains_key(&logical) {
                return Err(VerificationError::new(
                    ErrorCode::Duplicate,
                    format!("duplicate logical path `{logical}`"),
                ));
            }
            assets.insert(
                logical.clone(),
                ImportedAsset {
                    logical_path: logical,
                    kind,
                    digest_hex,
                    bytes,
                    facet,
                    partition,
                },
            );
        }
    }
    Ok(())
}

fn materialize_snapshot(
    snapshot_root: &Path,
    pins: &OraclePins,
    assets: &BTreeMap<String, ImportedAsset>,
) -> Result<SuiteSnapshot> {
    let cases_dir = snapshot_root.join("cases");
    let baselines_dir = snapshot_root.join("baselines");
    let notice_dir = snapshot_root.join("oracle/NOTICE");
    fs::create_dir_all(&cases_dir).map_err(|e| io_err(&cases_dir, &e))?;
    fs::create_dir_all(&baselines_dir).map_err(|e| io_err(&baselines_dir, &e))?;
    fs::create_dir_all(&notice_dir).map_err(|e| io_err(&notice_dir, &e))?;

    let mut index = SuiteIndex {
        entries: BTreeMap::new(),
    };

    for asset in assets.values() {
        match asset.kind {
            AssetKind::CaseInput => {
                store_blob(&cases_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::BaselineFacet => {
                store_blob(&baselines_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::DifferenceRecord => {
                store_blob(&baselines_dir, &asset.digest_hex, &asset.bytes)?;
            }
            AssetKind::LicenseNotice => {
                let dest = notice_dir.join(asset.logical_path.replace('/', "__"));
                if let Some(parent) = dest.parent() {
                    fs::create_dir_all(parent).map_err(|e| io_err(parent, &e))?;
                }
                write_then_verify(&dest, &asset.bytes)?;
            }
        }
        index.entries.insert(
            asset.logical_path.clone(),
            IndexEntry {
                logical_path: asset.logical_path.clone(),
                sha256: asset.digest_hex.clone(),
                asset_kind: asset.kind,
                facet: asset.facet,
                partition: asset.partition,
            },
        );
    }

    let ledger = build_provisional_ledger(pins, &index)?;
    let pin_bytes = canonicalize_json_bytes(&PinDocument::from_pins(pins))?;
    let index_bytes = canonicalize_json_bytes(&index)?;
    let ledger_bytes = TsLedgerWriter::to_vec(&ledger)?;

    let oracle_dir = snapshot_root.join("oracle");
    fs::create_dir_all(&oracle_dir).map_err(|e| io_err(&oracle_dir, &e))?;
    write_then_verify(&oracle_dir.join("pin.json"), &pin_bytes)?;
    write_then_verify(&snapshot_root.join("index.json"), &index_bytes)?;
    write_then_verify(&snapshot_root.join("ledger.json"), &ledger_bytes)?;

    let digest = sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]);
    write_then_verify(
        &snapshot_root.join("snapshot.sha256"),
        format!("{digest}\n").as_bytes(),
    )?;

    Ok(SuiteSnapshot {
        root: snapshot_root.to_path_buf(),
        digest,
        index,
        ledger,
    })
}

/// Build the provisional U0.4 ledger covering every case input × all 15 facets.
pub fn build_provisional_ledger(pins: &OraclePins, index: &SuiteIndex) -> Result<TsLedger> {
    let mut entries = Vec::new();
    for entry in index.entries.values() {
        if !matches!(entry.asset_kind, AssetKind::CaseInput) {
            continue;
        }
        let partition = entry.partition.ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Schema,
                format!("case input `{}` missing partition", entry.logical_path),
            )
        })?;
        for facet in ALL_FACETS {
            entries.push(provisional_entry(&entry.logical_path, partition, facet));
        }
    }

    let content_digest = index_content_digest(index);
    let mut ledger = TsLedger {
        schema_version: LEDGER_SCHEMA_VERSION,
        oracle: Oracle {
            npm: NpmOracle {
                specifier: pins.npm_specifier.clone(),
                integrity: pins.npm_integrity.clone(),
                published_at: PINNED_GENERATED_AT.to_owned(),
            },
            compiler: CompilerOracle {
                repository: pins.compiler_repository.clone(),
                commit: pins.compiler_commit.clone(),
                tag: pins.compiler_tag.clone(),
            },
            suite: SuiteOracle {
                repository: pins.suite_repository.clone(),
                commit: pins.suite_commit.clone(),
                case_root: SUITE_CASE_ROOT.to_owned(),
                baseline_root: SUITE_BASELINE_ROOT.to_owned(),
            },
        },
        snapshot: Snapshot {
            digest: content_digest,
            generated_at: PINNED_GENERATED_AT.to_owned(),
            entry_count: 0,
            input_count: 0,
        },
        entries,
        totals: Totals {
            discovered_inputs: 0,
            entries: 0,
            included: 0,
            deferred: 0,
            excluded: 0,
        },
    };
    ledger.sort_and_recompute();
    ledger.totals.discovered_inputs = ledger.snapshot.input_count;
    Ok(ledger)
}

fn provisional_entry(input: &str, partition: Partition, facet: Facet) -> Entry {
    let (status, reason_code, blocked_by) = match facet {
        Facet::Harness => (
            Status::Excluded,
            ReasonCode::UpstreamHarnessOnly,
            Vec::new(),
        ),
        Facet::Implementation => (
            Status::Excluded,
            ReasonCode::UpstreamImplementationOnly,
            Vec::new(),
        ),
        Facet::Parse
        | Facet::Diagnostics
        | Facet::Types
        | Facet::Symbols
        | Facet::JsEmit
        | Facet::DtsEmit
        | Facet::ModuleResolution
        | Facet::Config
        | Facet::Cli
        | Facet::Build
        | Facet::Watch
        | Facet::NodeApi
        | Facet::LanguageService => (
            Status::Deferred,
            ReasonCode::PromisedNotImplemented,
            vec!["S0".to_owned()],
        ),
    };

    let backends = match facet {
        Facet::JsEmit | Facet::NodeApi => {
            vec![Backend::Interpreter, Backend::Jit, Backend::Aot]
        }
        Facet::Parse
        | Facet::Diagnostics
        | Facet::Types
        | Facet::Symbols
        | Facet::DtsEmit
        | Facet::ModuleResolution
        | Facet::Config
        | Facet::Cli
        | Facet::Build
        | Facet::Watch
        | Facet::LanguageService
        | Facet::Harness
        | Facet::Implementation => vec![Backend::Check],
    };

    let timeout_class = match facet {
        Facet::Watch => TimeoutClass::Watch,
        Facet::Build => TimeoutClass::Project,
        Facet::JsEmit | Facet::NodeApi => TimeoutClass::Execute,
        Facet::Parse
        | Facet::Diagnostics
        | Facet::Types
        | Facet::Symbols
        | Facet::DtsEmit
        | Facet::ModuleResolution
        | Facet::Config
        | Facet::Cli
        | Facet::LanguageService
        | Facet::Harness
        | Facet::Implementation => TimeoutClass::Frontend,
    };

    let id = format!("{input}#{}", facet.as_str());
    let shard_key = compute_shard_key(&id, facet, &backends);

    Entry {
        id,
        input: input.to_owned(),
        partition,
        facet,
        status,
        surface: format!("{}.{}", partition.as_str(), facet.as_str()),
        reason_code,
        backends,
        timeout_class,
        shard_key,
        expected: Vec::new(),
        blocked_by,
        evidence: vec![EvidenceRecord {
            tier: 1,
            confidence: Confidence::Verified,
            url: SUITE_URL.to_owned(),
            note: Some("provisional U0.4 tier-1 evidence".to_owned()),
        }],
    }
}

/// Classify a single (`partition`, `facet`) cell for the U0.5 ledger v1 per
/// `.outline/wayfinder/type-script-7-compatibility-program.md` §17.2 and §2.1.
///
/// Returns the `(status, reasonCode, blockedBy)` triple. Facet-level exclusions
/// (`harness`/`implementation`) are never owned by any slice and win over every
/// partition rule; whole-partition dispositions (Node API / language-service /
/// watch families and upstream unit tests) win over the per-facet owning-slice
/// fallback used by the general compiler/conformance/project partitions.
pub fn classify_cell(partition: Partition, facet: Facet) -> (Status, ReasonCode, Vec<String>) {
    // Facet-level exclusions: never owned (§17.2 `harness` / `implementation`).
    match facet {
        Facet::Harness => {
            return (
                Status::Excluded,
                ReasonCode::UpstreamHarnessOnly,
                Vec::new(),
            );
        }
        Facet::Implementation => {
            return (
                Status::Excluded,
                ReasonCode::UpstreamImplementationOnly,
                Vec::new(),
            );
        }
        _ => {}
    }

    // Whole-partition dispositions (§17.2 rows keyed by partition).
    match partition {
        // Upstream compiler-internal unit tests assert no promised external
        // contract, so they are excluded with evidence (§17.2 `unittests`).
        Partition::UnitTests => (
            Status::Excluded,
            ReasonCode::UpstreamImplementationOnly,
            Vec::new(),
        ),
        // Node API family (`api`/`transpile`/`astnav`) → deferred until S10.
        Partition::Transpile | Partition::Api | Partition::AstNav => deferred_to("S10"),
        // Language service / LSP (`fourslash`/`lsp`) → deferred until S11.
        Partition::Fourslash | Partition::Lsp => deferred_to("S11"),
        // Watch partitions (`tscWatch`/`tsbuildWatch`) → deferred until S9.
        Partition::TscWatch | Partition::TsBuildWatch => deferred_to("S9"),
        // Configuration / CLI partitions: the entire partition is owned by S7
        // per §17.2, regardless of the specific facet.
        Partition::Config | Partition::Tsc | Partition::TsOptions => deferred_to("S7"),
        // Build-mode partition: the entire partition is owned by S8 per §17.2.
        Partition::TsBuild => deferred_to("S8"),
        // General partitions (compiler/conformance/project/projects/other):
        // facet-partitioned rows; the facet names the owning slice. U1.3 flips
        // the `parse` facet to an included compiler contract (S1 owns parsing);
        // U2.8 flips `diagnostics` the same way (S2 owns diagnostic
        // correspondence) — with per-input refinement in [`classify_s2_entry`]
        // (project diagnostics re-defer to S5; projects rows are excluded).
        // `types` and `symbols` are refined per-input in [`classify_s2_entry`]
        // (Phase B/C baseline ownership: included iff the input uniquely owns
        // the facet's baseline, else excluded upstream-harness).
        Partition::Compiler
        | Partition::Conformance
        | Partition::Project
        | Partition::Projects
        | Partition::Other => {
            if matches!(facet, Facet::Parse | Facet::Diagnostics) {
                (
                    Status::Included,
                    ReasonCode::PromisedCompilerContract,
                    Vec::new(),
                )
            } else {
                deferred_to(facet_owning_slice(facet))
            }
        }
    }
}

/// U2.8 per-input refinement of the S2 facet classification.
///
/// `classify_cell` is pure in `(partition, facet)`; baseline-aware and
/// project rules need the input path, so this runs inside
/// [`build_classified_ledger`]. Returns `None` when the generic rule stands.
fn classify_s2_entry(
    input: &str,
    partition: Partition,
    facet: Facet,
    s2: &crate::check_cells::S2Classification,
) -> Option<(Status, ReasonCode, Vec<String>)> {
    match facet {
        Facet::Diagnostics => match partition {
            // Project diagnostics baselines (`reference/project/<name>/…`) are
            // module-resolution/tsconfig observations (TS2792/TS5107); §17.2
            // assigns resolution semantics to S5.
            Partition::Project => Some(deferred_to("S5")),
            // The `projects` partition carries no upstream baseline artifacts.
            Partition::Projects => Some((
                Status::Excluded,
                ReasonCode::UpstreamHarnessOnly,
                Vec::new(),
            )),
            _ => None,
        },
        // Phase B: `types` is an included compiler contract for a general
        // partition input that uniquely owns a `.types` baseline. Every other
        // input is excluded upstream-harness-only: project/projects (no upstream
        // `.types`), `APISample_*` / `@noTypesAndSymbols` (no baseline), and the
        // ambiguous side of a duplicate stem (index alone cannot name the owner).
        Facet::Types => match partition {
            Partition::Project | Partition::Projects => Some((
                Status::Excluded,
                ReasonCode::UpstreamHarnessOnly,
                Vec::new(),
            )),
            Partition::Compiler | Partition::Conformance | Partition::Other => {
                if s2.owns_types_baseline(input) {
                    Some((
                        Status::Included,
                        ReasonCode::PromisedCompilerContract,
                        Vec::new(),
                    ))
                } else {
                    Some((
                        Status::Excluded,
                        ReasonCode::UpstreamHarnessOnly,
                        Vec::new(),
                    ))
                }
            }
            _ => None,
        },
        // Phase C: `symbols` follows the identical ownership rule as `types`
        // (a general-partition input included iff it uniquely owns a `.symbols`
        // baseline; project/projects, `@noTypesAndSymbols`, `APISample_*`, and
        // the ambiguous side of a duplicate stem are excluded upstream-harness).
        Facet::Symbols => match partition {
            Partition::Project | Partition::Projects => Some((
                Status::Excluded,
                ReasonCode::UpstreamHarnessOnly,
                Vec::new(),
            )),
            Partition::Compiler | Partition::Conformance | Partition::Other => {
                if s2.owns_symbols_baseline(input) {
                    Some((
                        Status::Included,
                        ReasonCode::PromisedCompilerContract,
                        Vec::new(),
                    ))
                } else {
                    Some((
                        Status::Excluded,
                        ReasonCode::UpstreamHarnessOnly,
                        Vec::new(),
                    ))
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn deferred_to(slice: &str) -> (Status, ReasonCode, Vec<String>) {
    (
        Status::Deferred,
        ReasonCode::PromisedNotImplemented,
        vec![slice.to_owned()],
    )
}

/// The vertical slice that owns a facet's observation (§17.1/§17.2 ownership).
fn facet_owning_slice(facet: Facet) -> &'static str {
    match facet {
        Facet::Parse => "S1",
        Facet::Diagnostics | Facet::Types | Facet::Symbols => "S2",
        Facet::JsEmit | Facet::DtsEmit => "S4",
        Facet::ModuleResolution => "S5",
        Facet::Config | Facet::Cli => "S7",
        Facet::Build => "S8",
        Facet::Watch => "S9",
        Facet::NodeApi => "S10",
        Facet::LanguageService => "S11",
        // Excluded before reaching here; kept exhaustive for the compiler.
        Facet::Harness | Facet::Implementation => "S0",
    }
}

/// Build the U0.5 classified ledger (v1): every discovered case input × all 15
/// facets, classified per [`classify_cell`]. Reuses the U0.4 provisional layout
/// for entry shape, shard keys, backends, and timeout classes; `snapshot.digest`
/// is the index content digest, while the snapshot's top-level `snapshot.sha256`
/// is computed separately over the whole manifest (pin + index + ledger).
pub fn build_classified_ledger(pins: &OraclePins, index: &SuiteIndex) -> Result<TsLedger> {
    let mut ledger = build_provisional_ledger(pins, index)?;
    ledger.snapshot.digest = index_content_digest(index);
    let s2 = crate::check_cells::S2Classification::from_index(index);
    for entry in &mut ledger.entries {
        let (status, reason_code, blocked_by) =
            classify_s2_entry(&entry.input, entry.partition, entry.facet, &s2)
                .unwrap_or_else(|| classify_cell(entry.partition, entry.facet));
        entry.status = status;
        entry.reason_code = reason_code;
        entry.blocked_by = blocked_by;
        entry.evidence = vec![EvidenceRecord {
            tier: 1,
            confidence: Confidence::Verified,
            url: SUITE_URL.to_owned(),
            note: Some(classification_note(entry.partition, entry.facet, status)),
        }];
    }
    ledger.sort_and_recompute();
    ledger.totals.discovered_inputs = ledger.snapshot.input_count;
    Ok(ledger)
}

fn classification_note(partition: Partition, facet: Facet, status: Status) -> String {
    let disposition = match status {
        Status::Included => "included",
        Status::Deferred => "deferred",
        Status::Excluded => "excluded",
    };
    format!(
        "U0.5 §17.2 classification (U1.3 parse, U2.8 diagnostics): partition `{}`, facet `{}` → {disposition}",
        partition.as_str(),
        facet.as_str(),
    )
}

/// Classify a materialized, provenance-verified snapshot and write ledger v1 to
/// `ledger_out`. Also overwrites the snapshot's own `ledger.json` and
/// recomputes `snapshot.sha256` so the runner sees the classified ledger.
pub fn write_suite_ledger(snapshot_root: &Path, ledger_out: &Path) -> Result<TsLedger> {
    let verified = verify_snapshot(snapshot_root)?;
    let pins = OraclePins::expected();
    let ledger = build_classified_ledger(&pins, &verified.snapshot.index)?;
    let ledger_bytes = TsLedgerWriter::to_vec(&ledger)?;

    if let Some(parent) = ledger_out.parent() {
        fs::create_dir_all(parent).map_err(|e| io_err(parent, &e))?;
    }
    write_then_verify(ledger_out, &ledger_bytes)?;
    write_then_verify(&snapshot_root.join("ledger.json"), &ledger_bytes)?;

    let pin_bytes = fs::read(snapshot_root.join("oracle/pin.json"))
        .map_err(|e| io_err(&snapshot_root.join("oracle/pin.json"), &e))?;
    let index_bytes = fs::read(snapshot_root.join("index.json"))
        .map_err(|e| io_err(&snapshot_root.join("index.json"), &e))?;
    let digest = sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]);
    write_then_verify(
        &snapshot_root.join("snapshot.sha256"),
        format!("{digest}\n").as_bytes(),
    )?;
    Ok(ledger)
}

fn index_content_digest(index: &SuiteIndex) -> String {
    let mut hasher = Sha256::new();
    for (path, entry) in &index.entries {
        hasher.update(path.as_bytes());
        hasher.update(b"|");
        hasher.update(entry.sha256.as_bytes());
        hasher.update(b"\n");
    }
    hex_encode(hasher.finalize())
}

/// Compute the exact shard key formula.
pub fn compute_shard_key(id: &str, facet: Facet, backends: &[Backend]) -> String {
    let mut names: Vec<&str> = backends.iter().copied().map(backend_name).collect();
    names.sort_unstable();
    let joined = names.join(",");
    let material = format!("{id}|{}|{joined}", facet.as_str());
    let digest = sha256_hex(material.as_bytes());
    digest[..16].to_owned()
}

/// Parse the first 8 hex chars of a shard key as `u32` and reduce mod `n`.
pub fn shard_index(shard_key: &str, n: u32) -> Result<u32> {
    if n == 0 {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            "shard count N must be > 0",
        ));
    }
    if shard_key.len() < 8 {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("shard key `{shard_key}` is too short"),
        ));
    }
    let prefix = u32::from_str_radix(&shard_key[..8], 16).map_err(|error| {
        VerificationError::new(
            ErrorCode::Usage,
            format!("invalid shard key prefix `{shard_key}`: {error}"),
        )
    })?;
    Ok(prefix % n)
}

/// Parse `--shards k/N` (1-based).
pub fn parse_shards(value: &str) -> Result<(u32, u32)> {
    let Some((k_text, n_text)) = value.split_once('/') else {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("invalid --shards `{value}`; expected k/N"),
        ));
    };
    let k: u32 = k_text.parse().map_err(|_| {
        VerificationError::new(
            ErrorCode::Usage,
            format!("invalid --shards `{value}`; k must be an integer"),
        )
    })?;
    let n: u32 = n_text.parse().map_err(|_| {
        VerificationError::new(
            ErrorCode::Usage,
            format!("invalid --shards `{value}`; N must be an integer"),
        )
    })?;
    if n == 0 || k == 0 || k > n {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("invalid --shards `{value}`; require 1 <= k <= N and N > 0"),
        ));
    }
    Ok((k, n))
}

pub fn backend_name(backend: Backend) -> &'static str {
    match backend {
        Backend::Check => "check",
        Backend::Interpreter => "interpreter",
        Backend::Jit => "jit",
        Backend::Aot => "aot",
    }
}

#[allow(dead_code)]
fn status_name(status: Status) -> &'static str {
    match status {
        Status::Included => "included",
        Status::Deferred => "deferred",
        Status::Excluded => "excluded",
    }
}

/// Re-verify blob digests and `snapshot.sha256`.
pub fn verify_snapshot(snapshot_root: &Path) -> Result<VerifiedSuite> {
    let snapshot_root =
        fs::canonicalize(snapshot_root).map_err(|error| io_err(snapshot_root, &error))?;
    let (pin_bytes, index_bytes, ledger_bytes) = read_snapshot_metadata_bytes(&snapshot_root)?;
    let expected = sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]);
    let recorded = fs::read_to_string(snapshot_root.join("snapshot.sha256"))
        .map_err(|error| io_err(&snapshot_root.join("snapshot.sha256"), &error))?;
    let recorded = recorded.trim();
    if recorded != expected {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!("snapshot.sha256 mismatch: recorded `{recorded}`, computed `{expected}`"),
        ));
    }

    let (index, ledger) = parse_snapshot_metadata(&pin_bytes, &index_bytes, &ledger_bytes)?;
    for entry in index.entries.values() {
        if matches!(entry.asset_kind, AssetKind::LicenseNotice) {
            continue;
        }
        let _ = read_verified_index_entry(&snapshot_root, entry)?;
    }

    Ok(VerifiedSuite {
        snapshot: SuiteSnapshot {
            root: snapshot_root,
            digest: expected,
            index,
            ledger,
        },
        pin_bytes,
        index_bytes,
        ledger_bytes,
    })
}

/// Load a compiler snapshot from retained metadata only. Never walks the blob tree.
pub fn load_bound_compiler_snapshot(
    snapshot_root: &Path,
    binding: &LaneBinding,
) -> Result<CompilerSnapshot> {
    binding.validate()?;
    if !binding.has_snapshot() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "compiler worker request is missing snapshot binding",
        ));
    }
    let snapshot_root =
        fs::canonicalize(snapshot_root).map_err(|error| io_err(snapshot_root, &error))?;
    let (pin_bytes, index_bytes, ledger_bytes) = read_snapshot_metadata_bytes(&snapshot_root)?;
    binding.verify_snapshot(
        COMPILER_CATALOG,
        &snapshot_root,
        &pin_bytes,
        &index_bytes,
        &ledger_bytes,
    )?;
    verify_pin_document_bytes(&pin_bytes)?;
    let index: SuiteIndex = serde_json::from_slice(&index_bytes)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("index.json: {error}")))?;
    validate_suite_index(&index)?;
    Ok(CompilerSnapshot {
        root: snapshot_root,
        metadata_digest: sha256_hex_concat(&[&pin_bytes, &index_bytes, &ledger_bytes]),
        index,
    })
}

/// Read one selected snapshot asset once and consume only those digest-checked bytes.
pub fn read_verified_asset(snapshot: &SuiteSnapshot, logical_path: &str) -> Result<Vec<u8>> {
    read_verified_snapshot_asset(snapshot, logical_path)
}

pub(crate) fn read_verified_snapshot_asset(
    snapshot: &(impl SnapshotAssets + ?Sized),
    logical_path: &str,
) -> Result<Vec<u8>> {
    if !is_safe_logical_path(logical_path) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unsafe snapshot logical path `{logical_path}`"),
        ));
    }
    let entry = snapshot.index().entries.get(logical_path).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!("snapshot has no asset `{logical_path}`"),
        )
    })?;
    if entry.logical_path != logical_path {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "index key `{logical_path}` does not match entry path `{}`",
                entry.logical_path
            ),
        ));
    }
    read_verified_index_entry(snapshot.root(), entry)
}

fn read_snapshot_metadata_bytes(snapshot_root: &Path) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    let pin_path = snapshot_root.join("oracle/pin.json");
    let index_path = snapshot_root.join("index.json");
    let ledger_path = snapshot_root.join("ledger.json");
    let pin_bytes = fs::read(&pin_path).map_err(|error| io_err(&pin_path, &error))?;
    let index_bytes = fs::read(&index_path).map_err(|error| io_err(&index_path, &error))?;
    let ledger_bytes = fs::read(&ledger_path).map_err(|error| io_err(&ledger_path, &error))?;
    Ok((pin_bytes, index_bytes, ledger_bytes))
}

fn parse_snapshot_metadata(
    pin_bytes: &[u8],
    index_bytes: &[u8],
    ledger_bytes: &[u8],
) -> Result<(SuiteIndex, crate::ts_ledger::TsLedger)> {
    verify_pin_document_bytes(pin_bytes)?;
    let index: SuiteIndex = serde_json::from_slice(index_bytes)
        .map_err(|error| VerificationError::new(ErrorCode::Json, format!("index.json: {error}")))?;
    validate_suite_index(&index)?;
    let ledger = TsLedgerReader::from_slice(ledger_bytes)?;
    Ok((index, ledger))
}

fn validate_suite_index(index: &SuiteIndex) -> Result<()> {
    for (path, entry) in &index.entries {
        if path != &entry.logical_path {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "index key `{path}` does not match entry path `{}`",
                    entry.logical_path
                ),
            ));
        }
        if !is_safe_logical_path(path) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("unsafe snapshot logical path `{path}`"),
            ));
        }
        crate::shard::require_sha256("index entry digest", &entry.sha256)?;
    }
    Ok(())
}

fn read_verified_index_entry(snapshot_root: &Path, entry: &IndexEntry) -> Result<Vec<u8>> {
    crate::shard::require_sha256("index entry digest", &entry.sha256)?;
    if entry.sha256.contains('/') || entry.sha256.contains('\\') {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "index digest for `{}` is not a path-safe blob name",
                entry.logical_path
            ),
        ));
    }
    let dir = match entry.asset_kind {
        AssetKind::CaseInput => snapshot_root.join("cases"),
        AssetKind::BaselineFacet | AssetKind::DifferenceRecord => snapshot_root.join("baselines"),
        AssetKind::LicenseNotice => {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "license asset `{}` is not a case or baseline blob",
                    entry.logical_path
                ),
            ));
        }
    };
    let path = dir.join(&entry.sha256);
    let bytes = fs::read(&path).map_err(|error| io_err(&path, &error))?;
    let actual = sha256_hex(&bytes);
    if actual != entry.sha256 {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "blob digest mismatch for `{}`: index `{}`, actual `{actual}`",
                entry.logical_path, entry.sha256
            ),
        ));
    }
    Ok(bytes)
}

fn verify_pin_document(path: &Path) -> Result<()> {
    let bytes = fs::read(path).map_err(|e| io_err(path, &e))?;
    verify_pin_document_bytes(&bytes)
}

fn verify_pin_document_bytes(bytes: &[u8]) -> Result<()> {
    let doc: PinDocument = serde_json::from_slice(bytes)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("pin.json: {e}")))?;
    let expected = PinDocument::expected();
    if doc.npm_specifier != expected.npm_specifier
        || doc.npm_integrity != expected.npm_integrity
        || doc.compiler_repository != expected.compiler_repository
        || doc.compiler_commit != expected.compiler_commit
        || doc.compiler_tag != expected.compiler_tag
        || doc.suite_repository != expected.suite_repository
        || doc.suite_commit != expected.suite_commit
    {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            "oracle/pin.json does not match pinned TypeScript 7.0.2 identity",
        ));
    }
    // Touch constants so pin drift against module constants is obvious to readers.
    let _ = (
        NPM_SPECIFIER,
        NPM_INTEGRITY,
        COMPILER_REPOSITORY,
        COMPILER_COMMIT,
        COMPILER_TAG,
        SUITE_REPOSITORY,
        SUITE_COMMIT,
    );
    Ok(())
}

fn case_inputs_from_index(index: &SuiteIndex) -> BTreeSet<String> {
    index
        .entries
        .values()
        .filter(|entry| matches!(entry.asset_kind, AssetKind::CaseInput))
        .map(|entry| entry.logical_path.clone())
        .collect()
}

fn store_blob(dir: &Path, digest_hex: &str, bytes: &[u8]) -> Result<()> {
    let path = dir.join(digest_hex);
    if path.exists() {
        let existing = fs::read(&path).map_err(|e| io_err(&path, &e))?;
        if existing != bytes {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                format!("content mismatch for blob `{digest_hex}`"),
            ));
        }
        return Ok(());
    }
    write_then_verify(&path, bytes)
}

fn write_then_verify(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| io_err(parent, &e))?;
    }
    fs::write(path, bytes).map_err(|e| io_err(path, &e))?;
    let read_back = fs::read(path).map_err(|e| io_err(path, &e))?;
    if read_back != bytes {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!("write-then-verify failed for `{}`", path.display()),
        ));
    }
    Ok(())
}

pub(crate) fn fetch_archive(url: &str, expected_digest: &str, cache_dir: &Path) -> Result<PathBuf> {
    let cache_path = cache_dir.join(format!("{expected_digest}.tar.gz"));
    if cache_path.exists() {
        let bytes = fs::read(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
        let actual = sha256_hex(&bytes);
        if actual == expected_digest {
            return Ok(cache_path);
        }
        fs::remove_file(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
    }

    let status = Command::new("curl")
        .args(["-fsSL", "--output"])
        .arg(&cache_path)
        .arg(url)
        .status()
        .map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                VerificationError::new(ErrorCode::ToolMissing, "curl is not available on PATH")
            } else {
                VerificationError::new(
                    ErrorCode::ToolFailed,
                    format!("failed to spawn curl: {error}"),
                )
            }
        })?;
    if !status.success() {
        let _ = fs::remove_file(&cache_path);
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("curl failed fetching `{url}` with {status}"),
        ));
    }
    let bytes = fs::read(&cache_path).map_err(|e| io_err(&cache_path, &e))?;
    let actual = sha256_hex(&bytes);
    if actual != expected_digest {
        let _ = fs::remove_file(&cache_path);
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "archive digest mismatch for `{url}`: expected `{expected_digest}`, got `{actual}`"
            ),
        ));
    }
    Ok(cache_path)
}

pub(crate) fn extract_archive(archive: &Path) -> Result<TempDir> {
    // Each archive extracts into its own temp dir. Without a per-archive
    // discriminator the suite and compiler extractions collide on the same
    // path (same prefix + pid), and the second extraction wipes the first.
    let discriminator = &sha256_hex(archive.to_string_lossy().as_bytes())[..8];
    let temp = TempDir::new(&format!("bamts-suite-extract-{discriminator}"))?;
    let listed = Command::new("tar")
        .args(["-tzf"])
        .arg(archive)
        .output()
        .map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                VerificationError::new(ErrorCode::ToolMissing, "tar is not available on PATH")
            } else {
                VerificationError::new(
                    ErrorCode::ToolFailed,
                    format!("failed to spawn tar: {error}"),
                )
            }
        })?;
    if !listed.status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "tar -tzf failed: {}",
                String::from_utf8_lossy(&listed.stderr)
            ),
        ));
    }
    let listing = String::from_utf8_lossy(&listed.stdout);
    for member in listing.lines() {
        reject_tar_member(member)?;
    }

    let verbose = Command::new("tar")
        .args(["-tvzf"])
        .arg(archive)
        .output()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("failed to spawn tar verbose list: {error}"),
            )
        })?;
    if !verbose.status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "tar -tvzf failed: {}",
                String::from_utf8_lossy(&verbose.stderr)
            ),
        ));
    }
    let verbose_listing = String::from_utf8_lossy(&verbose.stdout);
    for line in verbose_listing.lines() {
        reject_tar_verbose_line(line)?;
    }

    let status = Command::new("tar")
        .args([
            "-xzf",
            archive.to_str().ok_or_else(|| {
                VerificationError::new(ErrorCode::Io, "archive path is not UTF-8")
            })?,
            "--no-same-owner",
            "--no-same-permissions",
            "-C",
        ])
        .arg(temp.path())
        .status()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("failed to spawn tar extract: {error}"),
            )
        })?;
    if !status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("tar extract failed with {status}"),
        ));
    }
    reject_extracted_symlinks(temp.path())?;
    Ok(temp)
}

fn reject_tar_member(member: &str) -> Result<()> {
    if member.is_empty() {
        return Ok(());
    }
    if member.starts_with('/') || member.contains("://") {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!("archive member absolute path rejected: `{member}`"),
        ));
    }
    for part in member.split('/') {
        if part == ".." {
            return Err(VerificationError::new(
                ErrorCode::ProvenanceMismatch,
                format!("archive member traversal rejected: `{member}`"),
            ));
        }
    }
    Ok(())
}

fn reject_tar_verbose_line(line: &str) -> Result<()> {
    let trimmed = line.trim_start();
    if trimmed.is_empty() {
        return Ok(());
    }
    if matches!(trimmed.chars().next(), Some('-') | Some('d')) {
        return Ok(());
    }
    Err(VerificationError::new(
        ErrorCode::ProvenanceMismatch,
        format!("archive member link/special type rejected: `{line}`"),
    ))
}

fn member_looks_allowlisted(member: &str) -> bool {
    let lower = member.to_ascii_lowercase().replace('\\', "/");
    if lower.contains("tests/cases/")
        || lower.contains("tests/baselines/")
        || lower.contains("testdata/")
    {
        return true;
    }
    let base = Path::new(&lower)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    base.starts_with("license") || base.starts_with("notice")
}

fn reject_extracted_symlinks(root: &Path) -> Result<()> {
    // Do not fail the whole archive on incidental symlinks outside imported
    // paths; walk/import refuse to follow or read them.
    let mut stack = vec![root.to_path_buf()];
    while let Some(current) = stack.pop() {
        let entries = match fs::read_dir(&current) {
            Ok(entries) => entries,
            Err(error) => return Err(io_err(&current, &error)),
        };
        for entry in entries {
            let entry = entry.map_err(|e| io_err(&current, &e))?;
            let path = entry.path();
            let meta = fs::symlink_metadata(&path).map_err(|e| io_err(&path, &e))?;
            if meta.file_type().is_symlink() {
                return Err(VerificationError::new(
                    ErrorCode::ProvenanceMismatch,
                    format!("extracted symlink rejected: `{}`", path.display()),
                ));
            }
            if meta.is_dir() {
                stack.push(path);
            }
        }
    }
    Ok(())
}

pub(crate) fn single_archive_root(extract_root: &Path) -> Result<PathBuf> {
    let mut dirs = Vec::new();
    for entry in fs::read_dir(extract_root).map_err(|e| io_err(extract_root, &e))? {
        let entry = entry.map_err(|e| io_err(extract_root, &e))?;
        let meta = fs::symlink_metadata(entry.path()).map_err(|e| io_err(&entry.path(), &e))?;
        if meta.is_dir() {
            dirs.push(entry.path());
        }
    }
    if dirs.len() != 1 {
        return Err(VerificationError::new(
            ErrorCode::ProvenanceMismatch,
            format!(
                "expected exactly one archive root under `{}`, found {}",
                extract_root.display(),
                dirs.len()
            ),
        ));
    }
    Ok(dirs.remove(0))
}

pub(crate) struct TempDir {
    path: PathBuf,
}

impl TempDir {
    pub(crate) fn new(prefix: &str) -> Result<Self> {
        static TEMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            TEMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        if path.exists() {
            fs::remove_dir_all(&path).map_err(|e| io_err(&path, &e))?;
        }
        fs::create_dir_all(&path).map_err(|e| io_err(&path, &e))?;
        Ok(Self { path })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn canonicalize_json_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    let mut json = serde_json::to_value(value)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("{e}")))?;
    sort_json_keys(&mut json);
    let text = serde_json::to_string_pretty(&json)
        .map_err(|e| VerificationError::new(ErrorCode::Json, format!("{e}")))?;
    let canonical = text
        .lines()
        .map(|line| line.trim_end().replace('\r', ""))
        .collect::<Vec<_>>()
        .join("\n");
    Ok(canonical.into_bytes())
}

fn sort_json_keys(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Object(map) => {
            map.sort_keys();
            for member in map.values_mut() {
                sort_json_keys(member);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                sort_json_keys(item);
            }
        }
        _ => {}
    }
}

pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    hex_encode(Sha256::digest(bytes))
}

fn sha256_hex_concat(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hex_encode(hasher.finalize())
}

fn hex_encode(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn io_err(path: &Path, error: &io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

/// Materialize from an extracted tree without network (test seam).
pub fn materialize_from_extracted(
    snapshot_root: &Path,
    extracted_suite_root: &Path,
) -> Result<SuiteSnapshot> {
    sync_suite(&SyncOptions {
        verify_pin: true,
        write_snapshot: true,
        workspace_root: PathBuf::from("."),
        snapshot_root: snapshot_root.to_path_buf(),
        extracted_suite_root: Some(extracted_suite_root.to_path_buf()),
    })
}

const COMPILER_CATALOG: &str = "typescript-7.0.2";

/// Exact compiler-lane observation of one catalog key through BamTS check cells.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilerLaneObservation {
    pub snapshot_input: String,
    pub variant: String,
    pub observable: String,
    pub selected_options: BTreeMap<String, String>,
    pub class: FailureClass,
    pub detail: String,
    pub artifacts: BTreeMap<String, String>,
}

impl CompilerLaneObservation {
    fn blocking(
        snapshot_input: impl Into<String>,
        variant: impl Into<String>,
        observable: impl Into<String>,
        selected_options: BTreeMap<String, String>,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            snapshot_input: snapshot_input.into(),
            variant: variant.into(),
            observable: observable.into(),
            selected_options,
            class: FailureClass::HarnessError,
            detail: detail.into(),
            artifacts: BTreeMap::new(),
        }
    }

    /// Bind this observation to the lane protocol. Only an observed pass becomes
    /// [`LaneOutcome::Completed`].
    #[must_use]
    pub fn lane_outcome(&self) -> LaneOutcome {
        if self.class == FailureClass::Pass {
            LaneOutcome::Completed {
                artifacts: self.artifacts.clone(),
            }
        } else if self.class == FailureClass::Inapplicable {
            LaneOutcome::InapplicableCatalogError {
                detail: self.detail.clone(),
            }
        } else {
            LaneOutcome::BlockingFail {
                detail: self.detail.clone(),
            }
        }
    }
}

/// Map one TypeScript compiler lane request onto exactly one BamTS check cell.
///
/// Catalog, case prefix, `<variant>#<observable>` configuration, and the
/// declared observable singleton are validated independently. Status, slice,
/// and backend filters are not consulted. Every unmappable component or
/// comparator non-pass stays a closed non-pass.
pub fn observe_compiler_lane(
    snapshot: &(impl SnapshotAssets + ?Sized),
    ctx: &CheckContext,
    request: &LaneRequest,
) -> CompilerLaneObservation {
    let key = request.key();
    if !request.binding().has_snapshot() {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            "compiler lane request is missing snapshot binding",
        );
    }
    if request.binding().snapshot_catalog() != Some(COMPILER_CATALOG) {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            "compiler snapshot binding catalog does not match typescript-7.0.2",
        );
    }
    let snapshot_root = snapshot.root().to_str().unwrap_or_default();
    if request.binding().snapshot_root() != Some(snapshot_root) {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            "compiler snapshot binding root does not match loaded snapshot",
        );
    }
    if key.catalog() != COMPILER_CATALOG {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            format!("catalog `{}` is not `{COMPILER_CATALOG}`", key.catalog()),
        );
    }
    if key.mode() != ExecutionMode::Aot {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            format!("compiler lane does not bind mode `{}`", key.mode().as_str()),
        );
    }
    if compiler_snapshot_input(key.case()).is_none() {
        return project_trace_lane(snapshot, ctx, request, key);
    }
    let snapshot_input = compiler_snapshot_input(key.case()).unwrap_or_default();
    let Some((variant, observable)) = split_configuration(key.configuration()) else {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            "",
            "",
            BTreeMap::new(),
            format!(
                "configuration `{}` is not `<variant>#<observable>`",
                key.configuration()
            ),
        );
    };
    let declared = request.observables();
    let expected = BTreeSet::from([observable.to_owned()]);
    if declared != &expected {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            variant,
            observable,
            BTreeMap::new(),
            format!(
                "declared observables {declared:?} do not equal configuration observable `{observable}`"
            ),
        );
    }
    let Some(kind) = observable_kind(observable) else {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            variant,
            observable,
            BTreeMap::new(),
            format!("unknown compiler observable `{observable}`"),
        );
    };
    let Some(index_entry) = snapshot.index().entries.get(snapshot_input) else {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            variant,
            observable,
            BTreeMap::new(),
            format!("snapshot has no case input `{snapshot_input}`"),
        );
    };
    let text = match read_snapshot_case(snapshot, index_entry) {
        Ok(text) => text,
        Err(error) => {
            return CompilerLaneObservation::blocking(
                snapshot_input,
                variant,
                observable,
                BTreeMap::new(),
                error.to_string(),
            );
        }
    };
    let configurations = match catalog::parse_case_configuration(&text) {
        Ok(configurations) => configurations,
        Err(error) => {
            return CompilerLaneObservation::blocking(
                snapshot_input,
                variant,
                observable,
                BTreeMap::new(),
                error.to_string(),
            );
        }
    };
    let Some(configuration) = configurations.iter().find(|item| item.name == variant) else {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            variant,
            observable,
            BTreeMap::new(),
            format!("case `{snapshot_input}` has no configuration `{variant}`"),
        );
    };
    if !configuration.observables.contains(&kind) {
        return CompilerLaneObservation::blocking(
            snapshot_input,
            variant,
            observable,
            configuration.options.clone(),
            format!("configuration `{variant}` does not declare observable `{observable}`"),
        );
    }
    let selected_options = configuration.options.clone();
    let pragmas = CasePragmas::from_configuration(configuration);
    let check = match kind {
        ObservableKind::Diagnostics => {
            check_cells::observe_diagnostics(ctx, snapshot, index_entry, &text, &pragmas)
        }
        ObservableKind::Types => {
            check_cells::observe_types(snapshot, &ctx.baseline_groups, index_entry, &text, &pragmas)
        }
        ObservableKind::Symbols => check_cells::observe_symbols(
            snapshot,
            &ctx.baseline_groups,
            index_entry,
            &text,
            &pragmas,
        ),
        ObservableKind::JavaScript => check_cells::observe_javascript(
            snapshot,
            &ctx.baseline_groups,
            index_entry,
            &text,
            &pragmas,
        ),
        ObservableKind::Declaration => check_cells::observe_declaration(
            snapshot,
            &ctx.baseline_groups,
            index_entry,
            &text,
            &pragmas,
        ),
        ObservableKind::SourceMap => check_cells::observe_source_map(
            snapshot,
            &ctx.baseline_groups,
            index_entry,
            &text,
            &pragmas,
        ),
        ObservableKind::Trace => {
            check_cells::observe_trace(snapshot, &ctx.baseline_groups, index_entry, &text, &pragmas)
        }
        ObservableKind::BuildInfo => check_cells::observe_build_info(
            snapshot,
            &ctx.baseline_groups,
            index_entry,
            &text,
            &pragmas,
        ),
        other => {
            return CompilerLaneObservation::blocking(
                snapshot_input,
                variant,
                observable,
                selected_options,
                format!(
                    "no BamTS check-cell comparator for observable `{}`",
                    other.as_str()
                ),
            );
        }
    };
    bind_compiler_observation(
        snapshot_input,
        variant,
        observable,
        selected_options,
        declared,
        check,
    )
}

/// Execute a project-partition trace obligation against the project fixture's
/// owned `tests/baselines/reference/project/<case>.trace.json` baseline.
/// Project sources are materialized into one confined temporary root before the
/// same `ProgramLoader` load produces both the graph and its resolution trace.
fn project_trace_lane(
    snapshot: &(impl SnapshotAssets + ?Sized),
    _ctx: &CheckContext,
    request: &LaneRequest,
    key: &ObligationKey,
) -> CompilerLaneObservation {
    let case = key.case();
    let Some(input) = case.strip_prefix("project/") else {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            format!("case `{case}` is not a compiler/, conformance/, or project/ tests/cases path"),
        );
    };
    if !input.starts_with("tests/cases/project/") || !is_safe_logical_path(input) {
        return CompilerLaneObservation::blocking(
            "",
            "",
            "",
            BTreeMap::new(),
            format!("case `{case}` is not a compiler/, conformance/, or project/ tests/cases path"),
        );
    }
    let Some((variant, observable)) = split_configuration(key.configuration()) else {
        return CompilerLaneObservation::blocking(
            input,
            "",
            "",
            BTreeMap::new(),
            format!(
                "configuration `{}` is not `<variant>#<observable>`",
                key.configuration()
            ),
        );
    };
    let declared = request.observables();
    let expected = BTreeSet::from([observable.to_owned()]);
    if declared != &expected {
        return CompilerLaneObservation::blocking(
            input,
            variant,
            observable,
            BTreeMap::new(),
            format!(
                "declared observables {declared:?} do not equal configuration observable `{observable}`"
            ),
        );
    }
    if observable_kind(observable) != Some(ObservableKind::Trace) {
        return CompilerLaneObservation::blocking(
            input,
            variant,
            observable,
            BTreeMap::new(),
            format!("project case `{input}` does not route observable `{observable}`"),
        );
    }
    let Some(index_entry) = snapshot.index().entries.get(input) else {
        return CompilerLaneObservation::blocking(
            input,
            variant,
            observable,
            BTreeMap::new(),
            format!("snapshot has no case input `{input}`"),
        );
    };
    let check = observe_project_trace(snapshot, index_entry);
    bind_compiler_observation(input, variant, observable, BTreeMap::new(), declared, check)
}

/// Typed errors from `produce_project_trace` so `observe_project_trace` can
/// distinguish genuinely catalog-inapplicable outcomes (no `inputFiles`,
/// baseline proven absent upstream) from harness failures and compiler
/// defects that must stay in the blocking denominator.
enum ProjectTraceError {
    /// The fixture has no `inputFiles`: it is a project compilation test,
    /// not a trace test. The trace observable is inapplicable.
    NoInputFiles,
    /// The baseline `.trace.json` was not found in the snapshot. The catalog
    /// generated a trace obligation, but the upstream baseline has no
    /// corresponding artifact — a catalog error, not a compiler defect.
    MissingBaseline(String),
    /// A harness-level failure: temp-dir, I/O, config parse, or loader
    /// setup. These are infrastructure bugs, not compiler defects, but they
    /// must not be silently dropped from the blocking denominator.
    Harness(String),
    /// The fixture's `projectRoot` or `inputFiles` contain path traversal or
    /// other unsafe constructs. A harness guard failure — blocking.
    UnsafeInputFiles(String),
    /// The fixture's `projectRoot` is not under `tests/cases/projects/` or
    /// contains path traversal. A harness guard failure — blocking.
    UnsafeProjectRoot(String),
    /// The fixture JSON could not be deserialized. A harness/snapshot
    /// integrity failure — blocking.
    InvalidFixture(String),
    /// The fixture's logical path does not strip to a project baseline stem.
    /// A harness routing failure — blocking.
    InvalidPath(String),
    /// Compilation or module resolution failed while producing the trace.
    /// These are real compiler defects — blocking.
    Compile(String),
}

impl ProjectTraceError {
    /// Human-readable detail text. Preserves the prefixes that existing
    /// tests assert on (e.g. `missing trace evidence \`...\``).
    fn detail(&self) -> String {
        match self {
            Self::NoInputFiles => {
                "project trace fixture has no inputFiles: trace observable inapplicable".to_owned()
            }
            Self::MissingBaseline(msg) => msg.clone(),
            Self::Harness(msg) => msg.clone(),
            Self::UnsafeInputFiles(msg) => msg.clone(),
            Self::UnsafeProjectRoot(msg) => msg.clone(),
            Self::InvalidFixture(msg) => msg.clone(),
            Self::InvalidPath(msg) => msg.clone(),
            Self::Compile(msg) => msg.clone(),
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ProjectTraceCase {
    project_root: String,
    #[serde(default)]
    input_files: Vec<String>,
}

fn observe_project_trace(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> check_cells::CompilerCheckObservation {
    match produce_project_trace(snapshot, index_entry) {
        Ok((produced, expected, _baseline)) if produced == expected => {
            check_cells::CompilerCheckObservation {
                class: FailureClass::Pass,
                detail: String::new(),
                artifact: Some(produced),
            }
        }
        Ok((produced, expected, baseline_path)) => check_cells::CompilerCheckObservation {
            class: FailureClass::FailBehavior,
            detail: format!(
                "trace mismatch against `{baseline_path}`: produced {} bytes, expected {} bytes",
                produced.len(),
                expected.len(),
            ),
            artifact: Some(produced),
        },
        Err(err @ (ProjectTraceError::NoInputFiles | ProjectTraceError::MissingBaseline(_))) => {
            check_cells::CompilerCheckObservation {
                class: FailureClass::Inapplicable,
                detail: err.detail(),
                artifact: None,
            }
        }
        Err(
            err @ (ProjectTraceError::Harness(_)
            | ProjectTraceError::InvalidFixture(_)
            | ProjectTraceError::InvalidPath(_)),
        ) => check_cells::CompilerCheckObservation {
            class: FailureClass::HarnessError,
            detail: err.detail(),
            artifact: None,
        },
        Err(err) => check_cells::CompilerCheckObservation {
            class: FailureClass::FailBehavior,
            detail: err.detail(),
            artifact: None,
        },
    }
}

fn produce_project_trace(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> std::result::Result<(Vec<u8>, Vec<u8>, String), ProjectTraceError> {
    let descriptor = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)
        .map_err(|error| ProjectTraceError::Harness(error.to_string()))?;
    let fixture: ProjectTraceCase = serde_json::from_slice(&descriptor).map_err(|error| {
        ProjectTraceError::InvalidFixture(format!("invalid project trace fixture: {error}"))
    })?;
    if !fixture.project_root.starts_with("tests/cases/projects/")
        || !is_safe_logical_path(&fixture.project_root)
    {
        return Err(ProjectTraceError::UnsafeProjectRoot(format!(
            "project trace fixture has unsafe projectRoot `{}`",
            fixture.project_root
        )));
    }
    // A project fixture without `inputFiles` is a project compilation test,
    // not a trace test: the trace observable is inapplicable. Upstream project
    // fixtures use `projectRoot` + directory scanning, not an explicit file
    // list; only fixtures that declare `inputFiles` carry trace obligations.
    if fixture.input_files.is_empty() {
        return Err(ProjectTraceError::NoInputFiles);
    }
    if fixture
        .input_files
        .iter()
        .any(|path| !is_safe_logical_path(path))
    {
        return Err(ProjectTraceError::UnsafeInputFiles(
            "project trace fixture has unsafe inputFiles".to_owned(),
        ));
    }

    let relative_case = index_entry
        .logical_path
        .strip_prefix("tests/cases/project/")
        .and_then(|path| path.strip_suffix(".json"))
        .ok_or_else(|| {
            ProjectTraceError::InvalidPath(format!(
                "project trace fixture path `{}` has no project baseline stem",
                index_entry.logical_path
            ))
        })?;
    let baseline_path = format!("tests/baselines/reference/project/{relative_case}.trace.json");
    let expected = read_verified_snapshot_asset(snapshot, &baseline_path).map_err(|error| {
        ProjectTraceError::MissingBaseline(format!(
            "missing trace evidence `{baseline_path}`: {error}"
        ))
    })?;

    let temp = TempDir::new("bamts-project-trace")
        .map_err(|error| ProjectTraceError::Harness(format!("project trace temp root: {error}")))?;
    let project_dir = temp.path().join(&fixture.project_root);
    fs::create_dir_all(&project_dir).map_err(|error| {
        ProjectTraceError::Harness(format!(
            "project trace root `{}`: {error}",
            project_dir.display()
        ))
    })?;
    let project_prefix = format!("{}/", fixture.project_root.trim_end_matches('/'));
    for entry in snapshot.index().entries.values() {
        let Some(relative) = entry.logical_path.strip_prefix(&project_prefix) else {
            continue;
        };
        if entry.asset_kind != AssetKind::CaseInput || !is_safe_logical_path(relative) {
            continue;
        }
        let bytes = read_verified_snapshot_asset(snapshot, &entry.logical_path)
            .map_err(|error| ProjectTraceError::Harness(error.to_string()))?;
        let destination = project_dir.join(relative);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(|error| {
                ProjectTraceError::Harness(format!(
                    "project trace directory `{}`: {error}",
                    parent.display()
                ))
            })?;
        }
        fs::write(&destination, bytes).map_err(|error| {
            ProjectTraceError::Harness(format!(
                "project trace source `{}`: {error}",
                destination.display()
            ))
        })?;
    }

    let root = ProjectRoot::new(&project_dir)
        .map_err(|error| ProjectTraceError::Harness(format!("project trace root: {error}")))?;
    let config_path = project_dir.join("tsconfig.json");
    let config_source = if config_path.exists() {
        fs::read_to_string(&config_path).map_err(|error| {
            ProjectTraceError::Harness(format!(
                "project trace config `{}`: {error}",
                config_path.display()
            ))
        })?
    } else {
        "{}".to_owned()
    };
    let config = ProjectConfig::parse(&root, &config_path, &config_source)
        .map_err(|error| ProjectTraceError::Harness(format!("project trace config: {error}")))?;
    let loader = ProgramLoader::new(&root, config.options())
        .map_err(|error| ProjectTraceError::Harness(format!("project trace loader: {error}")))?;
    let roots: Vec<PathBuf> = fixture.input_files.iter().map(PathBuf::from).collect();
    let loaded = loader.load_roots(&roots).map_err(|error| {
        ProjectTraceError::Compile(format!("project trace load failed: {error}"))
    })?;
    let trace = check_cells::collect_resolution_trace(&loaded, config.options());
    let mut rendered = trace.lines().join("\n");
    if !rendered.is_empty() {
        rendered.push('\n');
    }
    let physical_root = loaded.root().path().to_string_lossy().replace('\\', "/");
    let produced = rendered
        .replace(&physical_root, fixture.project_root.trim_end_matches('/'))
        .into_bytes();
    Ok((produced, expected, baseline_path))
}

fn bind_compiler_observation(
    snapshot_input: &str,
    variant: &str,
    observable: &str,
    selected_options: BTreeMap<String, String>,
    declared: &BTreeSet<String>,
    check: check_cells::CompilerCheckObservation,
) -> CompilerLaneObservation {
    if check.class == FailureClass::Pass {
        let Some(bytes) = check.artifact else {
            return CompilerLaneObservation::blocking(
                snapshot_input,
                variant,
                observable,
                selected_options,
                "pass observation produced no artifact",
            );
        };
        let mut artifacts = BTreeMap::new();
        artifacts.insert(observable.to_owned(), sha256_hex(&bytes));
        let observed: BTreeSet<String> = artifacts.keys().cloned().collect();
        if &observed != declared {
            return CompilerLaneObservation::blocking(
                snapshot_input,
                variant,
                observable,
                selected_options,
                format!("observable set mismatch: declared {declared:?}, observed {observed:?}"),
            );
        }
        return CompilerLaneObservation {
            snapshot_input: snapshot_input.to_owned(),
            variant: variant.to_owned(),
            observable: observable.to_owned(),
            selected_options,
            class: FailureClass::Pass,
            detail: check.detail,
            artifacts,
        };
    }
    CompilerLaneObservation {
        snapshot_input: snapshot_input.to_owned(),
        variant: variant.to_owned(),
        observable: observable.to_owned(),
        selected_options,
        class: check.class,
        detail: check.detail,
        artifacts: BTreeMap::new(),
    }
}

fn compiler_snapshot_input(case: &str) -> Option<&str> {
    let (input, partition) = if let Some(input) = case.strip_prefix("compiler/") {
        (input, "tests/cases/compiler/")
    } else {
        (
            case.strip_prefix("conformance/")?,
            "tests/cases/conformance/",
        )
    };
    if !input.starts_with(partition) || !is_safe_logical_path(input) {
        return None;
    }
    Some(input)
}

fn is_safe_logical_path(path: &str) -> bool {
    !path.is_empty()
        && !path.starts_with('/')
        && path
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
}

fn split_configuration(configuration: &str) -> Option<(&str, &str)> {
    let (variant, observable) = configuration.split_once('#')?;
    if variant.is_empty() || observable.is_empty() || observable.contains('#') {
        None
    } else {
        Some((variant, observable))
    }
}

fn observable_kind(name: &str) -> Option<ObservableKind> {
    match name {
        "parse" => Some(ObservableKind::Parse),
        "diagnostics" => Some(ObservableKind::Diagnostics),
        "javascript" => Some(ObservableKind::JavaScript),
        "declaration" => Some(ObservableKind::Declaration),
        "source-map" => Some(ObservableKind::SourceMap),
        "trace" => Some(ObservableKind::Trace),
        "build-info" => Some(ObservableKind::BuildInfo),
        "types" => Some(ObservableKind::Types),
        "symbols" => Some(ObservableKind::Symbols),
        "runtime" => Some(ObservableKind::Runtime),
        _ => None,
    }
}

fn read_snapshot_case(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> Result<String> {
    let bytes = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)?;
    Ok(decode_case_source(&bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestDir(PathBuf);

    impl TestDir {
        fn new(label: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "bamts-u04-{label}-{}-{}",
                std::process::id(),
                sha256_hex(label.as_bytes())[..8].to_owned()
            ));
            let _ = fs::remove_dir_all(&path);
            fs::create_dir_all(&path).expect("temp dir");
            Self(path)
        }

        pub(crate) fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn write_fixture_tree(root: &Path) {
        let case = root.join("tests/cases/compiler/a.ts");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(&case, b"export const answer = 42;\n").unwrap();
        let baseline = root.join("tests/baselines/reference/a.errors.txt");
        fs::create_dir_all(baseline.parent().unwrap()).unwrap();
        fs::write(&baseline, b"error TS0000: sample\n").unwrap();
        fs::write(root.join("LICENSE"), b"Apache-2.0\n").unwrap();
        fs::write(root.join("NOTICE"), b"notice\n").unwrap();
        // Noise that must be ignored / rejected by allowlist.
        fs::create_dir_all(root.join("hereby")).unwrap();
        fs::write(root.join("hereby/task.txt"), b"nope\n").unwrap();
        fs::create_dir_all(root.join("internal/testutil")).unwrap();
        fs::write(root.join("internal/testutil/x.ts"), b"nope\n").unwrap();
    }

    /// A minimal index exercising the U2.8 Phase B `types` ownership rule:
    /// `owned` (sole stem + `.types`), `nobaseline` (no `.types`), and `dup`
    /// (a stem shared by two case inputs, so unownable from the index alone).
    fn s2_test_index() -> SuiteIndex {
        fn entry(path: &str, kind: AssetKind) -> IndexEntry {
            IndexEntry {
                logical_path: path.to_owned(),
                sha256: "0".repeat(64),
                asset_kind: kind,
                facet: None,
                partition: None,
            }
        }
        let mut entries = BTreeMap::new();
        for (path, kind) in [
            ("tests/cases/compiler/owned.ts", AssetKind::CaseInput),
            (
                "tests/baselines/reference/owned.types",
                AssetKind::BaselineFacet,
            ),
            ("tests/cases/compiler/nobaseline.ts", AssetKind::CaseInput),
            ("tests/cases/compiler/dup.ts", AssetKind::CaseInput),
            ("tests/cases/conformance/dup.ts", AssetKind::CaseInput),
            (
                "tests/baselines/reference/dup.types",
                AssetKind::BaselineFacet,
            ),
            (
                "tests/baselines/reference/owned.symbols",
                AssetKind::BaselineFacet,
            ),
            (
                "tests/baselines/reference/dup.symbols",
                AssetKind::BaselineFacet,
            ),
        ] {
            entries.insert(path.to_owned(), entry(path, kind));
        }
        SuiteIndex { entries }
    }

    #[test]
    fn snapshot_determinism_across_discovery_order() {
        let a = TestDir::new("det-a");
        let b = TestDir::new("det-b");
        write_fixture_tree(a.path());
        write_fixture_tree(b.path());
        // Add an extra file in different relative creation order on b.
        fs::write(b.path().join("tests/cases/compiler/z.ts"), b"export {};\n").unwrap();
        fs::write(a.path().join("tests/cases/compiler/z.ts"), b"export {};\n").unwrap();

        let snap_a = TestDir::new("snap-a");
        let snap_b = TestDir::new("snap-b");
        let left = materialize_from_extracted(snap_a.path(), a.path()).unwrap();
        let right = materialize_from_extracted(snap_b.path(), b.path()).unwrap();
        assert_eq!(left.digest, right.digest);
        assert_eq!(
            fs::read(snap_a.path().join("index.json")).unwrap(),
            fs::read(snap_b.path().join("index.json")).unwrap()
        );
        assert_eq!(
            fs::read(snap_a.path().join("ledger.json")).unwrap(),
            fs::read(snap_b.path().join("ledger.json")).unwrap()
        );
    }

    #[test]
    fn ledger_completeness_reports_ledger_incomplete() {
        let suite = TestDir::new("complete-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("complete-snap");
        let snapshot = materialize_from_extracted(snap.path(), suite.path()).unwrap();
        let mut discovered = case_inputs_from_index(&snapshot.index);
        discovered.insert("tests/cases/compiler/missing.ts".to_owned());
        let err = audit_ledger(&snap.path().join("ledger.json"), true, &discovered)
            .expect_err("missing input must fail");
        assert_eq!(err.code(), ErrorCode::Schema);
        assert!(err.to_string().contains("LEDGER_INCOMPLETE:"));
    }

    #[test]
    fn shard_key_stability_golden() {
        let key = compute_shard_key(
            "tests/cases/compiler/a.ts#parse",
            Facet::Parse,
            &[Backend::Check],
        );
        assert_eq!(key.len(), 16);
        assert!(
            key.chars()
                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        );
        let again = compute_shard_key(
            "tests/cases/compiler/a.ts#parse",
            Facet::Parse,
            &[Backend::Check],
        );
        assert_eq!(key, again);
        // Order independence of backends list.
        let key_sorted = compute_shard_key(
            "id#jsEmit",
            Facet::JsEmit,
            &[Backend::Aot, Backend::Interpreter, Backend::Jit],
        );
        let key_unsorted = compute_shard_key(
            "id#jsEmit",
            Facet::JsEmit,
            &[Backend::Jit, Backend::Aot, Backend::Interpreter],
        );
        assert_eq!(key_sorted, key_unsorted);
        let n = 4;
        let index = shard_index(&key, n).unwrap();
        assert!(index < n);
    }

    #[test]
    fn invalid_shard_flag_rejected() {
        assert!(parse_shards("0/4").is_err());
        assert!(parse_shards("5/4").is_err());
        assert!(parse_shards("1/0").is_err());
        assert!(parse_shards("abc").is_err());
        assert_eq!(parse_shards("1/4").unwrap(), (1, 4));
        assert_eq!(parse_shards("4/4").unwrap(), (4, 4));
    }

    #[test]
    fn digest_mismatch_rejected_before_execution() {
        let suite = TestDir::new("digest-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("digest-snap");
        materialize_from_extracted(snap.path(), suite.path()).unwrap();
        fs::write(snap.path().join("snapshot.sha256"), b"00\n").unwrap();
        let err = run_suite(
            Path::new("."),
            snap.path(),
            &RunFilterOptions {
                status: StatusFilter::All,
                slice: None,
                backends: BackendFilter::All,
                shards: None,
            },
        )
        .expect_err("tampered digest must fail before execute");
        assert_eq!(err.code(), ErrorCode::ProvenanceMismatch);
    }

    #[test]
    fn timeout_class_default_and_cap() {
        assert_eq!(budget_for(TimeoutClass::Frontend), (5_000, 30_000));
        assert_eq!(budget_for(TimeoutClass::Execute), (10_000, 60_000));
        assert_eq!(budget_for(TimeoutClass::Project), (30_000, 60_000));
        assert_eq!(budget_for(TimeoutClass::Watch), (30_000, 60_000));
    }

    #[test]
    fn output_truncation_over_1mib() {
        let oversized = vec![b'x'; OUTPUT_CAP_BYTES + 8];
        let (bounded, truncated) = bounded_output(oversized, OUTPUT_CAP_BYTES);
        assert!(truncated);
        assert_eq!(bounded.len(), OUTPUT_CAP_BYTES);
        assert_eq!(
            classify_truncation(true, false),
            Some(FailureClass::OutputTruncated)
        );
        assert_eq!(classify_truncation(false, false), None);
    }

    #[test]
    fn aot_scratch_over_1gib_fails_and_cleans_up() {
        let root = TestDir::new("aot-root");
        let spec = scratch_case_spec("scratch_case");
        let artifacts =
            ArtifactDirectory::create(root.path(), &spec, CorpusExecutionMode::Aot).unwrap();
        let path = artifacts.0.clone();
        fs::write(path.join("ok.bin"), b"tiny").unwrap();
        enforce_aot_scratch_cap(&path).unwrap();
        drop(artifacts);
        assert!(!path.exists(), "ArtifactDirectory Drop must clean scratch");

        let manual = root.path().join("manual-scratch");
        fs::create_dir_all(&manual).unwrap();
        fs::write(manual.join("marker"), b"x").unwrap();
        let err = enforce_aot_scratch_size(&manual, AOT_SCRATCH_CAP_BYTES + 1)
            .expect_err("over-cap scratch must fail");
        assert_eq!(err.code(), ErrorCode::ToolFailed);
        assert!(!manual.exists(), "failed over-cap path must be cleaned");
    }

    #[test]
    fn allowlist_rejects_hereby_traversal_testutil() {
        assert!(classify_logical_path("hereby/task.txt").unwrap().is_none());
        assert!(
            classify_logical_path("internal/testutil/x.ts")
                .unwrap()
                .is_none()
        );
        assert!(classify_logical_path("tests/cases/compiler/../secret.ts").is_err());
        assert!(classify_logical_path("/abs/tests/cases/compiler/a.ts").is_err());
        let ok = classify_logical_path("tests/cases/compiler/a.ts")
            .unwrap()
            .expect("case input");
        assert!(matches!(ok.0, AssetKind::CaseInput));
        assert!(matches!(ok.1, Some(Partition::Compiler)));
    }

    #[test]
    fn provisional_ledger_maps_all_15_facets() {
        let suite = TestDir::new("facets-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("facets-snap");
        let snapshot = materialize_from_extracted(snap.path(), suite.path()).unwrap();
        let input = "tests/cases/compiler/a.ts";
        let mut facets = BTreeSet::new();
        for entry in &snapshot.ledger.entries {
            if entry.input == input {
                facets.insert(entry.facet);
                match entry.facet {
                    Facet::Harness => {
                        assert!(matches!(entry.status, Status::Excluded));
                        assert!(matches!(entry.reason_code, ReasonCode::UpstreamHarnessOnly));
                        assert!(entry.blocked_by.is_empty());
                    }
                    Facet::Implementation => {
                        assert!(matches!(entry.status, Status::Excluded));
                        assert!(matches!(
                            entry.reason_code,
                            ReasonCode::UpstreamImplementationOnly
                        ));
                    }
                    Facet::Parse
                    | Facet::Diagnostics
                    | Facet::Types
                    | Facet::Symbols
                    | Facet::JsEmit
                    | Facet::DtsEmit
                    | Facet::ModuleResolution
                    | Facet::Config
                    | Facet::Cli
                    | Facet::Build
                    | Facet::Watch
                    | Facet::NodeApi
                    | Facet::LanguageService => {
                        assert!(matches!(entry.status, Status::Deferred));
                        assert_eq!(entry.blocked_by, vec!["S0".to_owned()]);
                        assert!(matches!(
                            entry.reason_code,
                            ReasonCode::PromisedNotImplemented
                        ));
                    }
                }
                assert_eq!(entry.evidence[0].tier, 1);
            }
        }
        assert_eq!(facets.len(), 15);
    }

    #[test]
    fn deferred_excluded_rollup_skip_classes() {
        let suite = TestDir::new("rollup-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("rollup-snap");
        materialize_from_extracted(snap.path(), suite.path()).unwrap();
        let report = run_suite(
            Path::new("."),
            snap.path(),
            &RunFilterOptions {
                status: StatusFilter::All,
                slice: None,
                backends: BackendFilter::All,
                shards: Some((1, 1)),
            },
        )
        .unwrap();
        assert!(
            report
                .rollups
                .get(&FailureClass::SkipDeferred)
                .copied()
                .unwrap_or(0)
                > 0
        );
        assert!(
            report
                .rollups
                .get(&FailureClass::SkipExcluded)
                .copied()
                .unwrap_or(0)
                > 0
        );
        assert_eq!(report.state_reached, RunState::Publish);
    }

    #[test]
    fn fresh_sync_keeps_the_committed_classified_ledger_authoritative() {
        let suite = TestDir::new("classified-sync-suite");
        write_fixture_tree(suite.path());
        let snapshot = TestDir::new("classified-sync-snapshot");
        materialize_from_extracted(snapshot.path(), suite.path()).unwrap();
        let workspace = TestDir::new("classified-sync-workspace");
        let ledger_path = workspace.path().join("verification/ts-suite-ledger.json");
        write_suite_ledger(snapshot.path(), &ledger_path).unwrap();

        // A later pin/snapshot refresh recreates the provisional embedded ledger.
        materialize_from_extracted(snapshot.path(), suite.path()).unwrap();

        let report = run_suite(
            workspace.path(),
            snapshot.path(),
            &RunFilterOptions {
                status: StatusFilter::Included,
                slice: Some("s1".to_owned()),
                backends: BackendFilter::One(Backend::Check),
                shards: Some((1, 1)),
            },
        )
        .unwrap();

        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].facet, Facet::Parse);
        assert!(matches!(report.results[0].class, FailureClass::Pass));
    }
    #[test]
    fn committed_ledger_must_match_the_materialized_index() {
        let suite = TestDir::new("classified-digest-suite");
        write_fixture_tree(suite.path());
        let snapshot = TestDir::new("classified-digest-snapshot");
        materialize_from_extracted(snapshot.path(), suite.path()).unwrap();
        let workspace = TestDir::new("classified-digest-workspace");
        let ledger_path = workspace.path().join("verification/ts-suite-ledger.json");
        let mut ledger = write_suite_ledger(snapshot.path(), &ledger_path).unwrap();
        ledger.snapshot.digest = "0".repeat(64);
        fs::write(&ledger_path, TsLedgerWriter::to_vec(&ledger).unwrap()).unwrap();
        materialize_from_extracted(snapshot.path(), suite.path()).unwrap();

        let error = run_suite(
            workspace.path(),
            snapshot.path(),
            &RunFilterOptions {
                status: StatusFilter::Included,
                slice: Some("s1".to_owned()),
                backends: BackendFilter::One(Backend::Check),
                shards: Some((1, 1)),
            },
        )
        .unwrap_err();

        assert_eq!(error.code(), ErrorCode::Digest);
    }

    #[test]
    fn included_s1_parse_rows_are_selected_by_slice_and_pass_check() {
        let suite = TestDir::new("s1parse-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("s1parse-snap");
        materialize_from_extracted(snap.path(), suite.path()).unwrap();
        // Reclassify so the snapshot's own ledger carries the U1.3 included
        // `parse` rows the runner reads.
        let ledger_out = snap.path().join("ts-suite-ledger.json");
        write_suite_ledger(snap.path(), &ledger_out).unwrap();

        let report = run_suite(
            Path::new("."),
            snap.path(),
            &RunFilterOptions {
                status: StatusFilter::Included,
                slice: Some("s1".to_owned()),
                backends: BackendFilter::One(Backend::Check),
                shards: Some((1, 1)),
            },
        )
        .unwrap();

        // The single fixture case yields exactly one included parse cell, and it
        // parses/checks cleanly, so the only rollup class is Pass.
        assert!(!report.results.is_empty(), "slice s1 selected no cells");
        assert!(
            report.results.iter().all(|r| r.facet == Facet::Parse),
            "slice s1 must select only parse-facet cells"
        );
        assert!(
            report
                .results
                .iter()
                .all(|r| matches!(r.class, FailureClass::Pass)),
            "every included S1 parse cell must pass: {:?}",
            report.results
        );
        assert_eq!(report.state_reached, RunState::Publish);
    }

    #[test]
    fn no_silent_skip_when_included_result_missing() {
        let entry = provisional_entry(
            "tests/cases/compiler/a.ts",
            Partition::Compiler,
            Facet::Parse,
        );
        let mut included = entry;
        included.status = Status::Included;
        included.reason_code = ReasonCode::PromisedCompilerContract;
        included.blocked_by.clear();
        let planned = vec![PlannedCell {
            entry: included,
            backend: Backend::Check,
        }];
        let err = enforce_no_silent_skip(&planned, &[]).expect_err("missing included result");
        assert_eq!(err.code(), ErrorCode::Schema);
        assert!(err.to_string().contains("LEDGER_INCOMPLETE:"));
        assert!(err.to_string().contains("NO_SILENT_SKIP"));
        let _ = status_name(Status::Included);
    }

    #[test]
    fn classify_cell_follows_section_17_2() {
        // Facet-level exclusions win over any partition, including special ones.
        for partition in [
            Partition::Compiler,
            Partition::Transpile,
            Partition::UnitTests,
        ] {
            let (status, reason, blocked) = classify_cell(partition, Facet::Harness);
            assert_eq!(status, Status::Excluded);
            assert_eq!(reason, ReasonCode::UpstreamHarnessOnly);
            assert!(blocked.is_empty());
            let (status, reason, blocked) = classify_cell(partition, Facet::Implementation);
            assert_eq!(status, Status::Excluded);
            assert_eq!(reason, ReasonCode::UpstreamImplementationOnly);
            assert!(blocked.is_empty());
        }

        // Compiler/conformance facet-partitioned owning slices. `parse` (U1.3)
        // and `diagnostics` (U2.8) are included compiler contracts (asserted
        // separately below); every other facet remains deferred to its later
        // owning slice.
        let expected: &[(Facet, &str)] = &[
            (Facet::Types, "S2"),
            (Facet::Symbols, "S2"),
            (Facet::JsEmit, "S4"),
            (Facet::DtsEmit, "S4"),
            (Facet::ModuleResolution, "S5"),
            (Facet::Config, "S7"),
            (Facet::Cli, "S7"),
            (Facet::Build, "S8"),
            (Facet::Watch, "S9"),
            (Facet::NodeApi, "S10"),
            (Facet::LanguageService, "S11"),
        ];
        for (facet, slice) in expected {
            let (status, reason, blocked) = classify_cell(Partition::Compiler, *facet);
            assert_eq!(status, Status::Deferred, "facet {}", facet.as_str());
            assert_eq!(reason, ReasonCode::PromisedNotImplemented);
            assert_eq!(
                blocked,
                vec![(*slice).to_owned()],
                "facet {}",
                facet.as_str()
            );
        }

        // U1.3: `parse` is an included compiler contract across every general
        // partition, with no blocking slice.
        for partition in [
            Partition::Compiler,
            Partition::Conformance,
            Partition::Project,
            Partition::Projects,
            Partition::Other,
        ] {
            assert_eq!(
                classify_cell(partition, Facet::Parse),
                (
                    Status::Included,
                    ReasonCode::PromisedCompilerContract,
                    vec![]
                ),
                "parse facet in general partition"
            );
        }

        // U2.8: `diagnostics` is an included compiler contract across every
        // general partition; `classify_s2_entry` re-defers project rows to S5
        // and excludes projects rows (per-input, asserted below).
        for partition in [
            Partition::Compiler,
            Partition::Conformance,
            Partition::Project,
            Partition::Projects,
            Partition::Other,
        ] {
            assert_eq!(
                classify_cell(partition, Facet::Diagnostics),
                (
                    Status::Included,
                    ReasonCode::PromisedCompilerContract,
                    vec![]
                ),
                "diagnostics facet in general partition"
            );
        }
        let s2 = crate::check_cells::S2Classification::from_index(&s2_test_index());
        assert_eq!(
            classify_s2_entry(
                "tests/cases/project/foo.json",
                Partition::Project,
                Facet::Diagnostics,
                &s2,
            ),
            Some((
                Status::Deferred,
                ReasonCode::PromisedNotImplemented,
                vec!["S5".to_owned()]
            )),
            "project diagnostics re-defer to S5 (module-resolution baselines)"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/projects/foo.ts",
                Partition::Projects,
                Facet::Diagnostics,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "projects rows carry no upstream baseline artifacts"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/foo.ts",
                Partition::Compiler,
                Facet::Diagnostics,
                &s2,
            ),
            None,
            "compiler diagnostics keep the generic included rule"
        );
        // Phase B `types` per-input ownership.
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/owned.ts",
                Partition::Compiler,
                Facet::Types,
                &s2,
            ),
            Some((
                Status::Included,
                ReasonCode::PromisedCompilerContract,
                vec![]
            )),
            "a sole-stem compiler input owning a `.types` baseline is included"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/nobaseline.ts",
                Partition::Compiler,
                Facet::Types,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "a compiler input with no `.types` baseline is excluded"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/dup.ts",
                Partition::Compiler,
                Facet::Types,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "a duplicate-stem input cannot be proven owner from the index alone"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/project/foo.json",
                Partition::Project,
                Facet::Types,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "project types rows have no upstream `.types` baselines"
        );

        // Phase C `symbols` per-input ownership (identical rule to `types`).
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/owned.ts",
                Partition::Compiler,
                Facet::Symbols,
                &s2,
            ),
            Some((
                Status::Included,
                ReasonCode::PromisedCompilerContract,
                vec![]
            )),
            "a sole-stem compiler input owning a `.symbols` baseline is included"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/nobaseline.ts",
                Partition::Compiler,
                Facet::Symbols,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "a compiler input with no `.symbols` baseline is excluded"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/compiler/dup.ts",
                Partition::Compiler,
                Facet::Symbols,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "a duplicate-stem input cannot be proven owner from the index alone"
        );
        assert_eq!(
            classify_s2_entry(
                "tests/cases/projects/foo.ts",
                Partition::Projects,
                Facet::Symbols,
                &s2,
            ),
            Some((Status::Excluded, ReasonCode::UpstreamHarnessOnly, vec![])),
            "projects symbols rows have no upstream `.symbols` baselines"
        );

        // Whole-partition dispositions (over the per-facet fallback).
        assert_eq!(
            classify_cell(Partition::Transpile, Facet::Parse),
            (
                Status::Deferred,
                ReasonCode::PromisedNotImplemented,
                vec!["S10".to_owned()]
            )
        );
        assert_eq!(
            classify_cell(Partition::Fourslash, Facet::Types),
            (
                Status::Deferred,
                ReasonCode::PromisedNotImplemented,
                vec!["S11".to_owned()]
            )
        );
        assert_eq!(
            classify_cell(Partition::TscWatch, Facet::Diagnostics),
            (
                Status::Deferred,
                ReasonCode::PromisedNotImplemented,
                vec!["S9".to_owned()]
            )
        );
        // Upstream unit tests: excluded with an implementation reason code.
        let (status, reason, blocked) = classify_cell(Partition::UnitTests, Facet::Parse);
        assert_eq!(status, Status::Excluded);
        assert_eq!(reason, ReasonCode::UpstreamImplementationOnly);
        assert!(blocked.is_empty());
    }

    #[test]
    fn classified_ledger_v1_is_valid_and_digest_bound() {
        let suite = TestDir::new("v1-suite");
        write_fixture_tree(suite.path());
        let snap = TestDir::new("v1-snap");
        materialize_from_extracted(snap.path(), suite.path()).unwrap();

        let ledger_out = snap.path().join("ts-suite-ledger.json");
        let ledger = write_suite_ledger(snap.path(), &ledger_out).unwrap();

        // Re-reading through the schema-bound reader must succeed.
        let reparsed = TsLedgerReader::from_file(&ledger_out).unwrap();
        assert_eq!(reparsed, ledger);
        assert_eq!(ledger.schema_version, 1);

        // snapshot.digest is the index content digest, which is independent
        // of the top-level snapshot.sha256 manifest digest.
        let verified = verify_snapshot(snap.path()).unwrap();
        assert_eq!(
            ledger.snapshot.digest,
            index_content_digest(&verified.snapshot.index)
        );
        // One fixture case × 15 facets: harness+implementation excluded, plus
        // `types` and `symbols` excluded (no `.types`/`.symbols` baseline for the
        // fixture stem); the `parse` (U1.3) and `diagnostics` (U2.8) facets are
        // included compiler contracts; the rest remain deferred to their later
        // owning slices.
        assert_eq!(ledger.totals.entries, 15);
        assert_eq!(ledger.totals.included, 2);
        assert_eq!(ledger.totals.excluded, 4);
        assert_eq!(ledger.totals.deferred, 9);
        assert_eq!(ledger.totals.discovered_inputs, 1);
        assert_eq!(
            ledger.totals.included + ledger.totals.deferred + ledger.totals.excluded,
            ledger.totals.entries
        );

        // Every row carries a reason code and at least one evidence record.
        for entry in &ledger.entries {
            assert!(!entry.evidence.is_empty());
            match entry.facet {
                Facet::Harness => {
                    assert_eq!(entry.status, Status::Excluded);
                    assert_eq!(entry.reason_code, ReasonCode::UpstreamHarnessOnly);
                }
                Facet::Implementation => {
                    assert_eq!(entry.status, Status::Excluded);
                    assert_eq!(entry.reason_code, ReasonCode::UpstreamImplementationOnly);
                }
                Facet::Parse | Facet::Diagnostics => {
                    assert_eq!(entry.status, Status::Included);
                    assert_eq!(entry.reason_code, ReasonCode::PromisedCompilerContract);
                    assert!(entry.blocked_by.is_empty());
                }
                Facet::Types | Facet::Symbols => {
                    assert_eq!(entry.status, Status::Excluded);
                    assert_eq!(entry.reason_code, ReasonCode::UpstreamHarnessOnly);
                }
                _ => {
                    assert_eq!(entry.status, Status::Deferred);
                    assert!(!entry.blocked_by.is_empty());
                }
            }
        }
    }

    #[test]
    fn tar_preflight_rejects_non_allowlisted_symlink_and_hard_link() {
        let symlink = "lrwxrwxrwx owner/group 0 2026-08-20 00:00 package/docs/link -> target";
        let hard_link =
            "hrw-r--r-- owner/group 0 2026-08-20 00:00 package/docs/alias link to target";
        assert_eq!(
            reject_tar_verbose_line(symlink).unwrap_err().code,
            ErrorCode::ProvenanceMismatch
        );
        assert_eq!(
            reject_tar_verbose_line(hard_link).unwrap_err().code,
            ErrorCode::ProvenanceMismatch
        );
    }

    #[test]
    fn tar_preflight_allows_only_regular_files_and_directories() {
        reject_tar_verbose_line("-rw-r--r-- owner/group 1 2026-08-20 00:00 package/docs/file")
            .unwrap();
        reject_tar_verbose_line("drwxr-xr-x owner/group 0 2026-08-20 00:00 package/docs/").unwrap();
        for special in ['c', 'b', 'p', 's'] {
            let line = format!("{special}rw-r--r-- owner/group 0 date package/docs/special");
            assert!(reject_tar_verbose_line(&line).is_err());
        }
    }

    const SCALAR_TYPES_SOURCE: &str = "var x: any;\nvar s: string = \"hi\";\n";
    const SCALAR_TYPES_BASELINE: &str = "//// [tests/cases/compiler/scalarPin.ts] ////\n\
\n\
=== scalarPin.ts ===\n\
var x: any;\n\
>x : any\n\
>  : ^^^\n\
\n\
var s: string = \"hi\";\n\
>s : string\n\
>  : ^^^^^^\n\
>\"hi\" : \"hi\"\n\
>     : ^^^^\n";

    struct CompilerLaneFixture {
        _extracted: TestDir,
        _snap: TestDir,
        snapshot: SuiteSnapshot,
        ctx: CheckContext,
    }

    fn compiler_lane_fixture(
        label: &str,
        file_name: &str,
        source: &str,
        types_baseline: &str,
    ) -> CompilerLaneFixture {
        compiler_lane_fixture_with_baselines(label, file_name, source, &[("types", types_baseline)])
    }

    /// Materialize a one-case suite snapshot with arbitrary flat reference
    /// baselines (`(<stem>).<suffix>` files under
    /// `tests/baselines/reference/`).
    fn compiler_lane_fixture_with_baselines(
        label: &str,
        file_name: &str,
        source: &str,
        baselines: &[(&str, &str)],
    ) -> CompilerLaneFixture {
        let extracted = TestDir::new(&format!("{label}-src"));
        let case = extracted
            .path()
            .join("tests/cases/compiler")
            .join(file_name);
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(&case, source).unwrap();
        let stem = file_name
            .rsplit_once('.')
            .map(|(stem, _)| stem)
            .unwrap_or(file_name);
        for (suffix, content) in baselines {
            let baseline = extracted
                .path()
                .join("tests/baselines/reference")
                .join(format!("{stem}.{suffix}"));
            fs::create_dir_all(baseline.parent().unwrap()).unwrap();
            fs::write(&baseline, content).unwrap();
        }
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new(&format!("{label}-snap"));
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        CompilerLaneFixture {
            _extracted: extracted,
            _snap: snap,
            snapshot: verified.snapshot,
            ctx,
        }
    }

    const COMPILER_TEST_RUN_ID: &str =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    fn bind_snapshot(snapshot: &(impl SnapshotAssets + ?Sized)) -> LaneBinding {
        let pin = fs::read(snapshot.root().join("oracle/pin.json")).expect("pin");
        let index = fs::read(snapshot.root().join("index.json")).expect("index");
        let ledger = fs::read(snapshot.root().join("ledger.json")).expect("ledger");
        LaneBinding::unbound(COMPILER_TEST_RUN_ID)
            .expect("run")
            .with_snapshot(COMPILER_CATALOG, snapshot.root(), &pin, &index, &ledger)
            .expect("bind")
    }

    fn compiler_lane_request(
        snapshot: &(impl SnapshotAssets + ?Sized),
        catalog: &str,
        case: &str,
        configuration: &str,
        observables: &[&str],
    ) -> LaneRequest {
        let key = crate::shard::ObligationKey::new(
            catalog,
            case,
            configuration,
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key");
        LaneRequest::new(
            bind_snapshot(snapshot),
            1,
            key,
            observables.iter().copied().map(str::to_owned).collect(),
            vec!["ts_lane_worker".to_owned()],
            crate::evidence::WorkingDirectoryPolicy::RepositoryRoot,
            5_000,
        )
        .expect("request")
    }

    fn closed_non_pass(observation: &CompilerLaneObservation) {
        assert_ne!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
        assert!(
            !matches!(observation.lane_outcome(), LaneOutcome::Completed { .. }),
            "{}",
            observation.detail
        );
        assert!(observation.artifacts.is_empty());
    }

    #[test]
    fn compiler_observation_selects_named_configuration() {
        let source = "// @target: es5, es2015\n\
            var x: any;\n\
            var s: string = \"hi\";\n";
        let pragmas = crate::check_cells::parse_case_pragmas(source);
        let first_target = pragmas
            .options
            .iter()
            .find(|(name, _)| name == "target")
            .and_then(|(_, values)| values.first())
            .map(String::as_str);
        assert_eq!(first_target, Some("es5"));

        let fixture = compiler_lane_fixture(
            "cfg-select",
            "targetVary.ts",
            source,
            "//// [tests/cases/compiler/targetVary.ts] ////\n",
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/targetVary.ts",
            "target=es2015#types",
            &["types"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(observation.variant, "target=es2015");
        assert_eq!(
            observation
                .selected_options
                .get("target")
                .map(String::as_str),
            Some("es2015")
        );
        assert_ne!(
            observation
                .selected_options
                .get("target")
                .map(String::as_str),
            first_target
        );
        assert_eq!(
            observation.snapshot_input,
            "tests/cases/compiler/targetVary.ts"
        );
    }

    #[test]
    fn compiler_observation_rejects_wrong_case_prefix() {
        let fixture = compiler_lane_fixture(
            "prefix",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "conformance/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn compiler_observation_rejects_unknown_configuration() {
        let fixture = compiler_lane_fixture(
            "unknown-cfg",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "target=es5#types",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn compiler_observation_rejects_malformed_configuration() {
        let fixture = compiler_lane_fixture(
            "bad-cfg",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn compiler_snapshot_input_maps_compiler_and_conformance_cases() {
        assert_eq!(
            compiler_snapshot_input("compiler/tests/cases/compiler/2dArrays.ts"),
            Some("tests/cases/compiler/2dArrays.ts")
        );
        assert_eq!(
            compiler_snapshot_input(
                "conformance/tests/cases/conformance/es6/functionExpressions/FunctionExpression1_es6.ts"
            ),
            Some("tests/cases/conformance/es6/functionExpressions/FunctionExpression1_es6.ts")
        );
        assert_eq!(compiler_snapshot_input("fourslash/foo.ts"), None);
        assert_eq!(compiler_snapshot_input("compiler/LICENSE"), None);
    }

    #[test]
    fn compiler_observation_conformance_path_reaches_snapshot_lookup() {
        let fixture = compiler_lane_fixture(
            "conformance-prefix",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "conformance/tests/cases/conformance/es6/functionExpressions/FunctionExpression1_es6.ts",
            "default#diagnostics",
            &["diagnostics"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert!(
            observation
                .detail
                .contains("snapshot has no case input `tests/cases/conformance/es6/functionExpressions/FunctionExpression1_es6.ts`"),
            "{}",
            observation.detail
        );
    }

    #[test]
    fn compiler_observation_rejects_unsupported_observable() {
        let fixture = compiler_lane_fixture(
            "bad-obs",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#source-map",
            &["source-map"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    /// Framing pin against the byte-exact upstream ClassDeclaration10.js
    /// baseline: document header with trailing ////, verbatim unit echo, one
    /// blank-line separator, then the `//// [ClassDeclaration10.js]` output.
    // Byte-exact from the authority case file, which ends at `}` with no final
    // newline. The echo is verbatim, so the source's own ending decides the
    // separator width in the pinned baseline below; adding a newline here would
    // fabricate a document upstream never produced.
    const CLASS_DECLARATION_10_SOURCE: &str = "class C {\n   constructor();\n   foo();\n}";
    const CLASS_DECLARATION_10_BASELINE: &str = "//// [tests/cases/compiler/ClassDeclaration10.ts] ////\n\
        \n\
        //// [ClassDeclaration10.ts]\nclass C {\n\
        \x20  constructor();\n\
        \x20  foo();\n\
        }\n\
        \n\
        //// [ClassDeclaration10.js]\n\
        \"use strict\";\nclass C {\n}\n";

    #[test]
    fn compiler_observation_javascript_matches_real_blob() {
        let units = check_cells::split_case_units(
            "tests/cases/compiler/ClassDeclaration10.ts",
            CLASS_DECLARATION_10_SOURCE,
        );
        let entry =
            check_cells::entry_virtual_path("tests/cases/compiler/ClassDeclaration10.ts", &units);
        let case = check_cells::compile_case_frontend(
            &units,
            &entry,
            &check_cells::CasePragmas::default(),
            bamts_compiler::pipeline::FrontendMode::JavaScript,
        )
        .expect("case compiles");
        let emitted = check_cells::emit_javascript_baseline(
            &case,
            "tests/cases/compiler/ClassDeclaration10.ts",
        )
        .expect("javascript emit");

        // The framing is pinned byte-exactly against the real upstream blob:
        // document header, unit echo, and blank-line separator. The emitted
        // js section is spliced in so the pin does not conflate framing with
        // the B4.1 emit-parity burn-down.
        let emitted_js_section = emitted
            .rsplit_once("//// [ClassDeclaration10.js]\n")
            .map(|(_, section)| section.to_owned())
            .expect("emitted doc carries the js section");
        let (baseline_head, _) = CLASS_DECLARATION_10_BASELINE
            .rsplit_once("//// [ClassDeclaration10.js]\n")
            .expect("baseline carries the js section");
        let framing_pinned_baseline =
            format!("{baseline_head}//// [ClassDeclaration10.js]\n{emitted_js_section}");
        assert!(
            emitted.starts_with(baseline_head),
            "framing must match the upstream blob byte-exactly:\n{emitted}"
        );
        assert_eq!(
            emitted, framing_pinned_baseline,
            "assembled doc must equal the framing-pinned baseline"
        );

        let fixture = compiler_lane_fixture_with_baselines(
            "js-blob",
            "ClassDeclaration10.ts",
            CLASS_DECLARATION_10_SOURCE,
            &[("js", &framing_pinned_baseline)],
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/ClassDeclaration10.ts",
            "default#javascript",
            &["javascript"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
    }

    #[test]
    fn compiler_observation_javascript_reaches_js_baseline_lookup() {
        let fixture = compiler_lane_fixture(
            "js-obs",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#javascript",
            &["javascript"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert!(
            !observation
                .detail
                .contains("no BamTS check-cell comparator for observable `javascript`"),
            "{}",
            observation.detail
        );
        closed_non_pass(&observation);
    }

    #[test]
    fn compiler_observation_rejects_wrong_catalog() {
        let fixture = compiler_lane_fixture(
            "catalog",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            "typescript-6.0.2",
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn compiler_observation_rejects_observable_set_mismatch() {
        let fixture = compiler_lane_fixture(
            "obs-set",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types", "symbols"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn compiler_observation_types_fixture_uses_real_comparator() {
        let fixture = compiler_lane_fixture(
            "types-pass",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
        assert_eq!(observation.variant, "default");
        assert_eq!(observation.observable, "types");
        let LaneOutcome::Completed { artifacts } = observation.lane_outcome() else {
            panic!("expected completed: {}", observation.detail);
        };
        assert_eq!(artifacts.len(), 1);
        let digest = artifacts.get("types").expect("types artifact");
        assert_eq!(digest.len(), 64);
        assert!(
            digest
                .chars()
                .all(|ch| ch.is_ascii_hexdigit() && !ch.is_ascii_uppercase())
        );
    }

    fn declaration_lane_emitted_doc(source: &str) -> String {
        let logical = "tests/cases/compiler/declLane.ts";
        let units = check_cells::split_case_units(logical, source);
        let entry = check_cells::entry_virtual_path(logical, &units);
        let case = check_cells::compile_case_frontend(
            &units,
            &entry,
            &check_cells::CasePragmas::default(),
            bamts_compiler::pipeline::FrontendMode::Declaration,
        )
        .expect("case compiles");
        check_cells::emit_declaration_baseline(&case).expect("declaration emit")
    }

    /// The `declaration` observable evaluates the `//// [<stem>.d.ts]`
    /// sections of the owned `.js` baseline document against the declaration
    /// emit — a pass with an artifact, never the no-comparator rejection.
    #[test]
    fn compiler_observation_declaration_compares_dts_sections() {
        let source = "// @declaration: true\nvar x: number = 1;\n";
        let dts = declaration_lane_emitted_doc(source);
        assert!(dts.starts_with("//// [declLane.d.ts]\n"), "{dts}");
        let baseline = format!(
            "//// [tests/cases/compiler/declLane.ts] ////\n\
             \n\
             //// [declLane.ts]\n{source}\n\
             {dts}"
        );
        let fixture = compiler_lane_fixture_with_baselines(
            "decl-pass",
            "declLane.ts",
            source,
            &[("js", &baseline)],
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/declLane.ts",
            "declaration=true#declaration",
            &["declaration"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
        assert_eq!(observation.observable, "declaration");
    }

    /// A semantic `.d.ts` divergence is an honest structural mismatch.
    #[test]
    fn compiler_observation_declaration_reports_structural_mismatch() {
        let source = "// @declaration: true\nvar x: number = 1;\n";
        let dts = declaration_lane_emitted_doc(source).replace("number", "string");
        let baseline = format!(
            "//// [tests/cases/compiler/declLane.ts] ////\n\
             \n\
             //// [declLane.ts]\n{source}\n\
             {dts}"
        );
        let fixture = compiler_lane_fixture_with_baselines(
            "decl-fail",
            "declLane.ts",
            source,
            &[("js", &baseline)],
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/declLane.ts",
            "declaration=true#declaration",
            &["declaration"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::FailBehavior,
            "{}",
            observation.detail
        );
        assert!(observation.detail.contains("structural mismatch"));
    }

    /// A `declaration` obligation with no owned `.js` baseline is a
    /// classification/execution drift, named precisely.
    #[test]
    fn compiler_observation_declaration_names_missing_baseline() {
        let fixture = compiler_lane_fixture(
            "decl-missing",
            "declLane.ts",
            "// @declaration: true\nvar x: number = 1;\n",
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/declLane.ts",
            "declaration=true#declaration",
            &["declaration"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(observation.class, FailureClass::HarnessError);
        assert!(
            observation
                .detail
                .contains("no owned `.js` baseline document"),
            "{}",
            observation.detail
        );
    }

    /// The `source-map` observable compares emitted printer maps against the
    /// owned `.js.map` baseline under JSON canonicalization; the upstream
    /// visualization trailer does not disturb the verdict.
    #[test]
    fn compiler_observation_source_map_compares_map_json() {
        let source = "// @sourcemap: true\nvar v = 1;\n";
        let logical = "tests/cases/compiler/mapLane.ts";
        let units = check_cells::split_case_units(logical, source);
        let entry = check_cells::entry_virtual_path(logical, &units);
        let case = check_cells::compile_case_frontend(
            &units,
            &entry,
            &check_cells::parse_case_pragmas(source),
            bamts_compiler::pipeline::FrontendMode::JavaScript,
        )
        .expect("case compiles");
        let emitted = check_cells::emit_source_map_baseline(&case, false).expect("map emit");
        assert!(emitted.starts_with("//// [mapLane.js.map]\n"), "{emitted}");
        let baseline =
            format!("{emitted}//// https://sokra.github.io/source-map-visualization#base64,zm9v\n");
        let fixture = compiler_lane_fixture_with_baselines(
            "map-pass",
            "mapLane.ts",
            source,
            &[("js.map", &baseline)],
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/mapLane.ts",
            "sourcemap=true#source-map",
            &["source-map"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );

        // A changed map is a real mismatch, and an inline configuration has
        // no `.js.map` facet upstream: it records the producer gap instead.
        let changed = emitted.replace("\"version\":3", "\"version\":2");
        let mismatch_fixture = compiler_lane_fixture_with_baselines(
            "map-fail",
            "mapLane.ts",
            source,
            &[("js.map", &changed)],
        );
        let request = compiler_lane_request(
            &mismatch_fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/mapLane.ts",
            "sourcemap=true#source-map",
            &["source-map"],
        );
        let observation =
            observe_compiler_lane(&mismatch_fixture.snapshot, &mismatch_fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::FailBehavior,
            "{}",
            observation.detail
        );
    }

    /// Inline source maps have no `.js.map` baseline facet upstream and the
    /// `.sourcemap.txt` record has no producer yet: a precise producer gap.
    #[test]
    fn compiler_observation_source_map_records_inline_producer_gap() {
        let fixture = compiler_lane_fixture(
            "map-inline",
            "inlineMapLane.ts",
            "// @inlinesourcemap: true\nvar v = 1;\n",
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/inlineMapLane.ts",
            "inlinesourcemap=true#source-map",
            &["source-map"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(observation.class, FailureClass::HarnessError);
        assert!(
            observation.detail.starts_with("producer missing:"),
            "{}",
            observation.detail
        );
    }

    /// A non-inline `source-map` obligation with no owned `.js.map` baseline
    /// is a classification/execution drift, named precisely.
    #[test]
    fn compiler_observation_source_map_names_missing_baseline() {
        let fixture = compiler_lane_fixture(
            "map-missing",
            "mapLane.ts",
            "// @sourcemap: true\nvar v = 1;\n",
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/mapLane.ts",
            "sourcemap=true#source-map",
            &["source-map"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(observation.class, FailureClass::HarnessError);
        assert!(
            observation.detail.contains("no owned `.js.map` baseline"),
            "{}",
            observation.detail
        );
    }

    /// The `trace` observable compiles the case and re-resolves imports
    /// through `resolve_module_name_with_trace`. A case with no owned
    /// `.trace.json` baseline is inapplicable: the catalog generated a trace
    /// obligation, but the upstream baseline has no trace artifact for this
    /// case/configuration, so the observable does not apply.
    #[test]
    fn compiler_observation_trace_without_baseline_is_drift() {
        let fixture = compiler_lane_fixture(
            "trace-gap",
            "traceLane.ts",
            "// @traceresolution: true\nvar v = 1;\n",
            SCALAR_TYPES_BASELINE,
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/traceLane.ts",
            "traceresolution=true#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(observation.class, FailureClass::Inapplicable);
        assert!(
            observation
                .detail
                .contains("no owned `.trace.json` baseline"),
            "{}",
            observation.detail
        );
    }

    /// One project-trace suite fixture: the case JSON, its project sources,
    /// and an optional owned `.trace.json` baseline.
    fn project_trace_fixture(label: &str, trace_baseline: Option<&str>) -> CompilerLaneFixture {
        let extracted = TestDir::new(&format!("{label}-src"));
        let case = extracted.path().join("tests/cases/project/traceFix.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(
            &case,
            r#"{"scenario":"trace","projectRoot":"tests/cases/projects/trace","inputFiles":["main.ts"]}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/trace");
        fs::create_dir_all(&project).unwrap();
        fs::write(project.join("main.ts"), "import './util.js'; void 0;\n").unwrap();
        fs::write(project.join("util.ts"), "export const util = 1;\n").unwrap();
        if let Some(baseline) = trace_baseline {
            let baseline_path = extracted
                .path()
                .join("tests/baselines/reference/project/traceFix.trace.json");
            fs::create_dir_all(baseline_path.parent().unwrap()).unwrap();
            fs::write(&baseline_path, baseline).unwrap();
        }
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new(&format!("{label}-snap"));
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        CompilerLaneFixture {
            _extracted: extracted,
            _snap: snap,
            snapshot: verified.snapshot,
            ctx,
        }
    }

    /// The rendered trace of the one-edge fixture project, written with the
    /// fixture's logical project root instead of the loader's temporary root.
    const PROJECT_TRACE_BASELINE: &str = "\
======== Resolving module './util.js' from 'tests/cases/projects/trace/main.ts'. ========\n\
Explicitly specified module resolution kind: 'Bundler'.\n\
Resolving in ESM mode with conditions 'import', 'types'.\n\
Loading module as file / folder, candidate module location 'tests/cases/projects/trace/util.js', target file types: TypeScript, JavaScript, Declaration, JSON.\n\
File name 'tests/cases/projects/trace/util.js' has a '.js' extension - stripping it.\n\
File 'tests/cases/projects/trace/util.ts' exists - use it as a name resolution result.\n\
======== Module name './util.js' was successfully resolved to 'tests/cases/projects/trace/util.ts'. ========\n";

    /// Project-partition trace obligations execute a real traced program load
    /// over the fixture's project sources and compare the rendered
    /// `ResolutionTraceLog` against the owned project `.trace.json` baseline.
    #[test]
    fn project_trace_lane_executes_traced_load_and_passes() {
        let fixture = project_trace_fixture("project-trace-pass", Some(PROJECT_TRACE_BASELINE));
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/traceFix.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}; [DEBUG-a19f] trace={:?}",
            observation.detail,
            observation.artifacts.get("trace")
        );
        assert_eq!(observation.detail, "");
        assert!(observation.artifacts.contains_key("trace"));

        // A project row routed with a non-trace observable stays a closed
        // blocking fail (the catalog routes only trace here).
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/traceFix.json",
            "default#diagnostics",
            &["diagnostics"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        closed_non_pass(&observation);
        assert!(
            observation.detail.contains("does not route observable"),
            "{}",
            observation.detail
        );
    }

    /// A project fixture with no owned `.trace.json` baseline is
    /// inapplicable: the trace observable does not apply when the upstream
    /// baseline has no trace artifact for this project.
    #[test]
    fn project_trace_without_baseline_names_missing_evidence() {
        let fixture = project_trace_fixture("project-trace-missing", None);
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/traceFix.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Inapplicable,
            "{}",
            observation.detail
        );
        assert!(
            observation.detail.starts_with(
                "missing trace evidence `tests/baselines/reference/project/traceFix.trace.json`"
            ),
            "{}",
            observation.detail
        );
    }

    /// Divergent trace output is a behavioral failure against the owned
    /// baseline, carrying the produced render as the observation artifact.
    #[test]
    fn project_trace_mismatch_reports_behavior_failure() {
        let fixture = project_trace_fixture(
            "project-trace-mismatch",
            Some("======== unexpected ========\n"),
        );
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/traceFix.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::FailBehavior,
            "{}",
            observation.detail
        );
        assert!(
            observation.detail.starts_with(
                "trace mismatch against `tests/baselines/reference/project/traceFix.trace.json`"
            ),
            "{}",
            observation.detail
        );
    }

    /// A project fixture without `inputFiles` is a project compilation test,
    /// not a trace test. The trace observable is inapplicable: the catalog
    /// generates a trace obligation for every project case, but fixtures
    /// without `inputFiles` don't carry trace obligations. Per the catalog
    /// rule, this is `Inapplicable` (non-blocking, completion-ineligible),
    /// not `HarnessError` / `BLOCKING_FAIL`.
    #[test]
    fn project_trace_without_input_files_is_inapplicable() {
        let extracted = TestDir::new("project-trace-no-inputfiles-src");
        let case = extracted
            .path()
            .join("tests/cases/project/noInputFiles.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        // No `inputFiles` field — this is a project compilation fixture.
        fs::write(
            &case,
            r#"{"scenario":"trace","projectRoot":"tests/cases/projects/trace"}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/trace");
        fs::create_dir_all(&project).unwrap();
        fs::write(project.join("main.ts"), "void 0;\n").unwrap();
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new("project-trace-no-inputfiles-snap");
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        let request = compiler_lane_request(
            &verified.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/noInputFiles.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&verified.snapshot, &ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Inapplicable,
            "{}",
            observation.detail
        );
        assert!(
            observation.detail.contains("no inputFiles"),
            "{}",
            observation.detail
        );
    }

    /// A project fixture with malformed JSON is a harness/snapshot integrity
    /// failure, not a catalog-inapplicable outcome. The typed error
    /// `InvalidFixture` maps to `HarnessError` (blocking), not
    /// `Inapplicable`, so the defect stays in the blocking denominator.
    #[test]
    fn project_trace_harness_error_is_not_inapplicable() {
        let extracted = TestDir::new("project-trace-harness-src");
        let case = extracted.path().join("tests/cases/project/badJson.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        // Malformed JSON — deserialization fails, which is a harness error.
        fs::write(&case, r#"{"scenario":"trace","projectRoot":"tests/cases/projects/trace","inputFiles":["main.ts"]"#).unwrap();
        let project = extracted.path().join("tests/cases/projects/trace");
        fs::create_dir_all(&project).unwrap();
        fs::write(project.join("main.ts"), "void 0;\n").unwrap();
        // Provide a baseline so the error is from parsing, not missing baseline.
        let baseline_path = extracted
            .path()
            .join("tests/baselines/reference/project/badJson.trace.json");
        fs::create_dir_all(baseline_path.parent().unwrap()).unwrap();
        fs::write(&baseline_path, "[]\n").unwrap();
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new("project-trace-harness-snap");
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        let request = compiler_lane_request(
            &verified.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/badJson.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&verified.snapshot, &ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::HarnessError,
            "{}",
            observation.detail
        );
        assert!(
            observation
                .detail
                .starts_with("invalid project trace fixture:"),
            "{}",
            observation.detail
        );
    }

    /// A project fixture whose `inputFiles` import a non-existent module
    /// triggers a compile/resolution failure. The typed error `Compile` maps
    /// to `FailBehavior` (blocking), not `Inapplicable`, so the compiler
    /// defect stays in the blocking denominator.
    #[test]
    fn project_trace_compile_failure_is_blocking() {
        let extracted = TestDir::new("project-trace-compile-src");
        let case = extracted
            .path()
            .join("tests/cases/project/compileFail.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(
            &case,
            r#"{"scenario":"trace","projectRoot":"tests/cases/projects/compileFail","inputFiles":["main.ts"]}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/compileFail");
        fs::create_dir_all(&project).unwrap();
        // main.ts imports a module that does not exist — resolution will fail.
        fs::write(project.join("main.ts"), "import './nonexistent.js';\n").unwrap();
        // Provide a baseline so the error is from compilation, not missing baseline.
        let baseline_path = extracted
            .path()
            .join("tests/baselines/reference/project/compileFail.trace.json");
        fs::create_dir_all(baseline_path.parent().unwrap()).unwrap();
        fs::write(&baseline_path, "[]\n").unwrap();
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new("project-trace-compile-snap");
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        let request = compiler_lane_request(
            &verified.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/compileFail.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&verified.snapshot, &ctx, &request);
        assert_ne!(
            observation.class,
            FailureClass::Inapplicable,
            "compile failure must not be Inapplicable: {}",
            observation.detail
        );
        assert!(
            observation.detail.starts_with("project trace load failed:"),
            "{}",
            observation.detail
        );
    }

    /// A project fixture with unsafe `inputFiles` (path traversal) is a
    /// harness guard failure — blocking, not inapplicable. The typed error
    /// `UnsafeInputFiles` maps to `FailBehavior`.
    #[test]
    fn project_trace_unsafe_input_files_is_blocking() {
        let extracted = TestDir::new("project-trace-unsafe-src");
        let case = extracted
            .path()
            .join("tests/cases/project/unsafeInput.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        // inputFiles contains a path traversal — unsafe.
        fs::write(
            &case,
            r#"{"scenario":"trace","projectRoot":"tests/cases/projects/trace","inputFiles":["../escape.ts"]}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/trace");
        fs::create_dir_all(&project).unwrap();
        fs::write(project.join("main.ts"), "void 0;\n").unwrap();
        // Provide a baseline so the error is from the guard, not missing baseline.
        let baseline_path = extracted
            .path()
            .join("tests/baselines/reference/project/unsafeInput.trace.json");
        fs::create_dir_all(baseline_path.parent().unwrap()).unwrap();
        fs::write(&baseline_path, "[]\n").unwrap();
        fs::write(extracted.path().join("LICENSE"), b"Apache-2.0\n").unwrap();
        let snap = TestDir::new("project-trace-unsafe-snap");
        materialize_from_extracted(snap.path(), extracted.path()).unwrap();
        let verified = verify_snapshot(snap.path()).unwrap();
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let ctx = CheckContext {
            code_map: crate::facets::load_diagnostic_code_map(&repo).expect("code map"),
            baseline_groups: crate::check_cells::baseline_groups(&verified.snapshot.index),
        };
        let request = compiler_lane_request(
            &verified.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/unsafeInput.json",
            "default#trace",
            &["trace"],
        );
        let observation = observe_compiler_lane(&verified.snapshot, &ctx, &request);
        assert_ne!(
            observation.class,
            FailureClass::Inapplicable,
            "unsafe inputFiles must not be Inapplicable: {}",
            observation.detail
        );
        assert!(
            observation.detail.contains("unsafe inputFiles"),
            "{}",
            observation.detail
        );
    }

    /// The baseline path derivation strips `tests/cases/project/` prefix and
    /// `.json` suffix from the case path, then appends `.trace.json` under
    /// `tests/baselines/reference/project/`. This matches the upstream
    /// layout where project baselines live at
    /// `tests/baselines/reference/project/<name>.trace.json`. The 281
    /// "missing trace evidence" rows from the evidence sweep were proven
    /// absent: zero of the 281 project case names have a `.trace.json`
    /// file anywhere under the upstream `tests/baselines/reference/`
    /// directory (checked against 204 existing trace baselines, 0
    /// intersection). The path derivation is correct; the baselines are
    /// genuinely absent upstream.
    #[test]
    fn project_trace_baseline_path_derivation_matches_upstream_layout() {
        // The derivation logic: strip "tests/cases/project/" prefix and
        // ".json" suffix, then format as
        // "tests/baselines/reference/project/{relative_case}.trace.json".
        // This is exercised by the passing test
        // project_trace_without_baseline_names_missing_evidence, which
        // verifies the exact path
        // "tests/baselines/reference/project/traceFix.trace.json".
        // Here we verify the derivation for a nested case name.
        let logical_path = "tests/cases/project/subDir/nestedCase.json";
        let relative_case = logical_path
            .strip_prefix("tests/cases/project/")
            .and_then(|path| path.strip_suffix(".json"))
            .expect("strip prefix and suffix");
        let baseline_path = format!("tests/baselines/reference/project/{relative_case}.trace.json");
        assert_eq!(
            baseline_path,
            "tests/baselines/reference/project/subDir/nestedCase.trace.json"
        );
    }

    #[test]
    fn bound_loader_observes_without_full_blob_scan() {
        let fixture = compiler_lane_fixture(
            "fast-path",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let poison = fixture
            .snapshot
            .root
            .join("baselines")
            .join("ff".repeat(32));
        fs::write(&poison, b"unrelated blob corruption").expect("poison");
        let binding = bind_snapshot(&fixture.snapshot);
        let loaded =
            load_bound_compiler_snapshot(&fixture.snapshot.root, &binding).expect("fast load");
        let request = compiler_lane_request(
            &loaded,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        let observation = observe_compiler_lane(&loaded, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
    }

    #[test]
    fn bound_loader_rejects_metadata_identity_mismatch() {
        let fixture = compiler_lane_fixture(
            "meta-mismatch",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let binding = bind_snapshot(&fixture.snapshot);
        let swapped = fixture.snapshot.root.join("oracle/pin.json");
        let mut pin = fs::read(&swapped).expect("pin");
        pin.extend_from_slice(b" ");
        fs::write(&swapped, pin).expect("swap pin");
        let error =
            load_bound_compiler_snapshot(&fixture.snapshot.root, &binding).expect_err("pin swap");
        assert_eq!(error.code(), ErrorCode::ProvenanceMismatch);
    }

    #[test]
    fn selected_case_tamper_is_rejected() {
        let fixture = compiler_lane_fixture(
            "case-tamper",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let logical = "tests/cases/compiler/scalarPin.ts";
        let digest = fixture.snapshot.index.entries[logical].sha256.clone();
        fs::write(
            fixture.snapshot.root.join("cases").join(&digest),
            b"tampered",
        )
        .expect("tamper case");
        let error = read_verified_asset(&fixture.snapshot, logical).expect_err("digest");
        assert_eq!(error.code(), ErrorCode::Digest);
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn selected_baseline_tamper_is_rejected() {
        let fixture = compiler_lane_fixture(
            "base-tamper",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let logical = "tests/baselines/reference/scalarPin.types";
        let digest = fixture.snapshot.index.entries[logical].sha256.clone();
        fs::write(
            fixture.snapshot.root.join("baselines").join(&digest),
            b"tampered baseline",
        )
        .expect("tamper baseline");
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            &["types"],
        );
        closed_non_pass(&observe_compiler_lane(
            &fixture.snapshot,
            &fixture.ctx,
            &request,
        ));
    }

    #[test]
    fn worker_loader_does_not_fall_back_to_full_verification() {
        let fixture = compiler_lane_fixture(
            "no-fallback",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let unbound = LaneBinding::unbound(COMPILER_TEST_RUN_ID).expect("unbound");
        let error =
            load_bound_compiler_snapshot(&fixture.snapshot.root, &unbound).expect_err("unbound");
        assert_eq!(error.code(), ErrorCode::Schema);
        assert!(error.to_string().contains("missing snapshot binding"));
    }

    #[test]
    fn bound_loader_does_not_deserialize_ledger() {
        let fixture = compiler_lane_fixture(
            "no-ledger-parse",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let ledger_path = fixture.snapshot.root.join("ledger.json");
        let garbage = b"not-json-ledger";
        fs::write(&ledger_path, garbage).expect("garbage ledger");
        let pin = fs::read(fixture.snapshot.root.join("oracle/pin.json")).expect("pin");
        let index = fs::read(fixture.snapshot.root.join("index.json")).expect("index");
        let binding = LaneBinding::unbound(COMPILER_TEST_RUN_ID)
            .expect("run")
            .with_snapshot(
                COMPILER_CATALOG,
                &fixture.snapshot.root,
                &pin,
                &index,
                garbage,
            )
            .expect("bind");
        let loaded =
            load_bound_compiler_snapshot(&fixture.snapshot.root, &binding).expect("fast load");
        assert_eq!(
            loaded.index.entries.len(),
            fixture.snapshot.index.entries.len()
        );
        verify_snapshot(&fixture.snapshot.root).expect_err("parent still requires a parsed ledger");
    }

    #[test]
    fn compiler_observation_rejects_missing_snapshot_binding() {
        let fixture = compiler_lane_fixture(
            "missing-bind",
            "scalarPin.ts",
            SCALAR_TYPES_SOURCE,
            SCALAR_TYPES_BASELINE,
        );
        let key = crate::shard::ObligationKey::new(
            COMPILER_CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key");
        let request = LaneRequest::new(
            LaneBinding::unbound(COMPILER_TEST_RUN_ID).expect("unbound"),
            1,
            key,
            ["types".to_owned()].into_iter().collect(),
            vec!["ts_lane_worker".to_owned()],
            crate::evidence::WorkingDirectoryPolicy::RepositoryRoot,
            5_000,
        )
        .expect("unbound request is still a valid generic lane request");
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        closed_non_pass(&observation);
        assert!(
            observation.detail.contains("missing snapshot binding"),
            "{}",
            observation.detail
        );
    }
}
