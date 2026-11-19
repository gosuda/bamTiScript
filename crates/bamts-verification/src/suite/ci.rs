use std::{collections::BTreeSet, fs, path::Path};
use super::runner::{compute_shard_key, run_suite};
use super::snapshot::{
    index_content_digest, io_err, sha256_hex_concat, verify_snapshot, write_then_verify,
};
use super::{
    ALL_FACETS, AssetKind, CiMode, CiOptions, PINNED_GENERATED_AT, RunFilterOptions, SuiteIndex,
    SuiteRunReport,
};
use crate::oracle_pins::{OraclePins, SUITE_URL};
use crate::ts_ledger::{
    Backend, CompilerOracle, Confidence, Entry, EvidenceRecord, Facet, LEDGER_SCHEMA_VERSION,
    NpmOracle, Oracle, Partition, ReasonCode, SUITE_BASELINE_ROOT, SUITE_CASE_ROOT, Snapshot,
    Status, SuiteOracle, TimeoutClass, Totals, TsLedger, TsLedgerReader, TsLedgerWriter,
};
use crate::{ErrorCode, Result, VerificationError};

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

/// CI entrypoint: same filters, mode retained for future policy differences.
pub fn run_ci(options: &CiOptions) -> Result<SuiteRunReport> {
    match options.mode {
        CiMode::Pr | CiMode::Nightly => run_suite(
            &options.workspace_root,
            &options.snapshot_root,
            &options.filters,
        ),
    }
}

pub(super) fn filters_need_workspace_pins(_filters: &RunFilterOptions) -> bool {
    false
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

pub(super) fn provisional_entry(input: &str, partition: Partition, facet: Facet) -> Entry {
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
pub(super) fn classify_s2_entry(
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
pub(super) fn facet_owning_slice(facet: Facet) -> &'static str {
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
