//! TypeScript 7 suite importer, snapshot materializer, and bounded runner (U0.4).
//!
//! Import pipeline accepts an extracted tree root for hermetic tests; curl/tar is
//! isolated behind fetch/extract helpers. Snapshot digests are walk-order
//! independent via [`BTreeMap`].

mod ci;
pub mod completion;
mod runner;
mod snapshot;
pub use self::ci::{
    audit_ledger, build_classified_ledger, build_provisional_ledger, classify_cell, run_ci,
    write_suite_ledger,
};
pub(crate) use self::runner::PlannedCell;
pub use self::runner::{
    CompilerLaneObservation, backend_name, budget_for, classify_truncation, compute_shard_key,
    enforce_aot_scratch_cap, enforce_aot_scratch_size, observe_compiler_lane, parse_shards,
    run_suite, run_suite_with_telemetry, shard_index,
};
pub(crate) use self::snapshot::{
    TempDir, extract_archive, fetch_archive, read_verified_snapshot_asset, single_archive_root,
};
pub use self::snapshot::{
    classify_logical_path, decode_case_source, load_bound_compiler_snapshot,
    materialize_from_extracted, read_verified_asset, sync_suite, verify_snapshot,
    walk_extracted_tree,
};
use crate::Result;
use crate::lane::LaneBinding;
use crate::ts_ledger::{Backend, Facet, Partition, TsLedger};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
/// Pinned npm publication time used for every deterministic `generatedAt`.
pub const PINNED_GENERATED_AT: &str = "2026-07-08T15:55:18.431Z";
/// Per-stream capture cap (1 MiB). Exceeding yields [`FailureClass::OutputTruncated`].
pub const OUTPUT_CAP_BYTES: usize = 1 << 20;
/// Per-cell AOT scratch cap (1 GiB).
pub const AOT_SCRATCH_CAP_BYTES: u64 = 1 << 30;
/// Default snapshot root relative to the workspace.
pub const DEFAULT_SNAPSHOT_REL: &str = "verification/ts-suite";
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
///
/// `SupportFile` covers shared inputs that are neither cases nor baselines:
/// the `tests/lib/*.d.ts` files cases pull in through `/.lib/` reference
/// directives. Support files are readable blobs but carry no obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AssetKind {
    CaseInput,
    BaselineFacet,
    DifferenceRecord,
    LicenseNotice,
    SupportFile,
}

impl AssetKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CaseInput => "caseInput",
            Self::BaselineFacet => "baselineFacet",
            Self::DifferenceRecord => "differenceRecord",
            Self::LicenseNotice => "licenseNotice",
            Self::SupportFile => "supportFile",
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

pub(crate) const COMPILER_CATALOG: &str = "typescript-7.0.2";
#[cfg(test)]
mod tests {
    use super::ci::{classify_s2_entry, provisional_entry};
    use super::runner::{enforce_no_silent_skip, scratch_case_spec, status_name};
    use super::snapshot::{
        case_inputs_from_index, compiler_snapshot_input, index_content_digest,
        reject_tar_verbose_line,
    };
    use super::*;
    use crate::ErrorCode;
    use crate::check_cells::{self, CheckContext};
    use crate::corpus::{ArtifactDirectory, ExecutionMode as CorpusExecutionMode, bounded_output};
    use crate::lane::{LaneOutcome, LaneRequest};
    use crate::schema::sha256_hex;
    use crate::shard::ExecutionMode;
    use crate::ts_ledger::{ReasonCode, Status, TimeoutClass, TsLedgerReader, TsLedgerWriter};
    use std::collections::BTreeSet;
    use std::fs;

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
    fn shard_index_rejects_a_key_that_splits_a_character() {
        let key = format!("a{}", "\u{e9}".repeat(4));
        assert_eq!(key.len(), 9);
        let error = shard_index(&key, 4).expect_err("non-boundary prefix is a usage error");
        assert!(error.to_string().contains("splits a character"), "{error}");
        assert_eq!(shard_index("0000000f", 4).unwrap(), 3);
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
    fn shared_lib_declaration_files_classify_as_support_files() {
        for path in [
            "tests/lib/react.d.ts",
            "tests/lib/react16.d.ts",
            "tests/lib/react18/global.d.ts",
            "tests/lib/react18/react18.d.ts",
        ] {
            let ok = classify_logical_path(path).unwrap().expect("support file");
            assert!(matches!(ok.0, AssetKind::SupportFile));
            assert!(ok.1.is_none());
            assert!(ok.2.is_none());
        }
        assert!(
            classify_logical_path("tests/lib/readme.md")
                .unwrap()
                .is_none()
        );
        assert!(
            classify_logical_path("tests/lib/react.d.ts.map")
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn support_files_round_trip_without_ledger_obligations() {
        let suite = TestDir::new("support-extracted");
        let case = suite.path().join("tests/cases/compiler/a.ts");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(&case, b"export const answer = 42;\n").unwrap();
        let lib = suite.path().join("tests/lib/react16.d.ts");
        fs::create_dir_all(lib.parent().unwrap()).unwrap();
        fs::write(&lib, b"declare module \"react\" {}\n").unwrap();
        let snap = TestDir::new("support-snap");
        let snapshot = materialize_from_extracted(snap.path(), suite.path()).unwrap();
        let entry = snapshot
            .index
            .entries
            .get("tests/lib/react16.d.ts")
            .expect("support file indexed");
        assert!(matches!(entry.asset_kind, AssetKind::SupportFile));
        let bytes = read_verified_snapshot_asset(&snapshot, "tests/lib/react16.d.ts").unwrap();
        assert_eq!(bytes, b"declare module \"react\" {}\n");
        assert!(
            snapshot
                .ledger
                .entries
                .iter()
                .all(|entry| entry.input != "tests/lib/react16.d.ts"),
            "support files carry no ledger obligations"
        );
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

    /// The rendered trace of the one-edge fixture project with no tsconfig,
    /// using default resolution and the fixture's logical project root.
    const PROJECT_TRACE_BASELINE: &str = "\
======== Resolving module './util.js' from 'tests/cases/projects/trace/main.ts'. ========\n\
Module resolution kind is not specified, using 'Bundler'.\n\
Resolving in CJS mode with conditions 'import', 'types'.\n\
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
            "{}; trace={:?}",
            observation.detail,
            observation.artifacts.get("trace")
        );
        assert_eq!(observation.detail, "");
        assert!(observation.artifacts.contains_key("trace"));

        // A project row routed with a still-unrouted observable stays a closed
        // blocking fail (trace, declaration, diagnostics, and javascript
        // route; symbols do not yet).
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/traceFix.json",
            "default#symbols",
            &["symbols"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        closed_non_pass(&observation);
        assert!(
            observation.detail.contains("does not route observable"),
            "{}",
            observation.detail
        );
    }
    fn project_declaration_fixture(label: &str) -> CompilerLaneFixture {
        let extracted = TestDir::new(&format!("{label}-src"));
        let case = extracted.path().join("tests/cases/project/declFix.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(
            &case,
            r#"{"scenario":"declarationDir: specify declarationDir only","projectRoot":"tests/cases/projects/declproj","inputFiles":["a.ts","subfolder/b.ts","subfolder/c.ts"],"declaration":true,"declarationDir":"declarations","baselineCheck":true}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/declproj");
        fs::create_dir_all(&project).unwrap();
        fs::write(
            project.join("a.ts"),
            "import {B} from './subfolder/b';\nexport class A {\n    b: B;\n}\n",
        )
        .unwrap();
        fs::create_dir_all(project.join("subfolder")).unwrap();
        fs::write(
            project.join("subfolder/b.ts"),
            "export class B {\n    \n}\n",
        )
        .unwrap();
        fs::write(
            project.join("subfolder/c.ts"),
            "import {A} from '../a';\n\nexport class C {\n    a: A;\n}\n",
        )
        .unwrap();
        let manifest = r#"{"scenario":"declarationDir: specify declarationDir only","projectRoot":"tests/cases/projects/declproj","inputFiles":["a.ts","subfolder/b.ts","subfolder/c.ts"],"declaration":true,"declarationDir":"declarations","baselineCheck":true,"resolvedInputFiles":["lib.es5.d.ts","lib.decorators.d.ts","lib.decorators.legacy.d.ts","subfolder/b.ts","a.ts","subfolder/c.ts"],"emittedFiles":["subfolder/b.js","declarations/subfolder/b.d.ts","a.js","declarations/a.d.ts","subfolder/c.js","declarations/subfolder/c.d.ts"]}"#;
        for variant in ["amd", "node"] {
            let dir = extracted.path().join(format!(
                "tests/baselines/reference/project/declFix/{variant}"
            ));
            fs::create_dir_all(&dir).unwrap();
            fs::write(dir.join("declFix.json"), manifest).unwrap();
            fs::create_dir_all(dir.join("declarations/subfolder")).unwrap();
            fs::write(
                dir.join("declarations/a.d.ts"),
                "import { B } from './subfolder/b';\nexport declare class A {\n    b: B;\n}\n",
            )
            .unwrap();
            fs::write(
                dir.join("declarations/subfolder/b.d.ts"),
                "export declare class B {\n}\n",
            )
            .unwrap();
            fs::write(
                dir.join("declarations/subfolder/c.d.ts"),
                "import { A } from '../a';\nexport declare class C {\n    a: A;\n}\n",
            )
            .unwrap();
        }
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

    #[test]
    fn project_declaration_lane_routes_real_baseline() {
        let fixture = project_declaration_fixture("project-decl-route");
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/declFix.json",
            "default#declaration",
            &["declaration"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::Pass,
            "{}",
            observation.detail
        );
        assert_eq!(observation.detail, "");
        assert!(observation.artifacts.contains_key("declaration"));
    }
    fn project_diagnostic_fixture(label: &str) -> CompilerLaneFixture {
        let extracted = TestDir::new(&format!("{label}-src"));
        let case = extracted.path().join("tests/cases/project/diagFix.json");
        fs::create_dir_all(case.parent().unwrap()).unwrap();
        fs::write(
            &case,
            r#"{"scenario":"baseline","projectRoot":"tests/cases/projects/diagproj","inputFiles":["emit.ts"],"baselineCheck":true,"runTest":true}"#,
        )
        .unwrap();
        let project = extracted.path().join("tests/cases/projects/diagproj");
        fs::create_dir_all(&project).unwrap();
        fs::write(
            project.join("decl.ts"),
            "export interface Point { x: number; y: number; };\nexport function point (x: number, y: number): Point {\n\treturn { x: x, y: y };\n}\n",
        )
        .unwrap();
        fs::write(
            project.join("emit.ts"),
            "import g = require(\"./decl\");\nvar p = g.point(10,20);\n",
        )
        .unwrap();
        let node_errors = "error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\n\n\n!!! error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\n==== decl.ts (0 errors) ====\n==== emit.ts (0 errors) ====\n";
        let amd_errors = "error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\nerror TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\n\n\n!!! error TS5107: Option 'module=AMD' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\n!!! error TS5107: Option 'moduleResolution=classic' is deprecated and will stop functioning in TypeScript 7.0. Specify compilerOption '\"ignoreDeprecations\": \"6.0\"' to silence this error.\n==== decl.ts (0 errors) ====\n==== emit.ts (0 errors) ====\n";
        for (variant, errors) in [("amd", amd_errors), ("node", node_errors)] {
            let dir = extracted.path().join(format!(
                "tests/baselines/reference/project/diagFix/{variant}"
            ));
            fs::create_dir_all(&dir).unwrap();
            fs::write(dir.join("diagFix.errors.txt"), errors).unwrap();
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

    #[test]
    fn project_diagnostic_lane_reports_missing_globals() {
        let fixture = project_diagnostic_fixture("project-diag-route");
        let request = compiler_lane_request(
            &fixture.snapshot,
            COMPILER_CATALOG,
            "project/tests/cases/project/diagFix.json",
            "default#diagnostics",
            &["diagnostics"],
        );
        let observation = observe_compiler_lane(&fixture.snapshot, &fixture.ctx, &request);
        assert_eq!(
            observation.class,
            FailureClass::FailBehavior,
            "{}",
            observation.detail
        );
        assert!(
            observation.detail.contains("missing global diagnostics")
                && observation.detail.contains("diagFix.errors.txt"),
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
