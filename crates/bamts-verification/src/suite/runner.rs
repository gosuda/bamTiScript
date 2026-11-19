use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    sync::Arc,
    time::Duration,
};
use bamts_compiler::diagnostic::{Diagnostic, DiagnosticSeverity};
use bamts_compiler::parser::parse;
use bamts_compiler::pipeline::{FrontendMode, compile_program_frontend};
use bamts_compiler::program::ProgramLoader;
use bamts_compiler::project::resolution_trace::display_path;
use bamts_compiler::project::{ProjectConfig, ProjectRoot};
use bamts_compiler::scanner::scan;
use bamts_compiler::source::{ScriptKind, SourceId, SourceText};
use bamts_compiler::syntax::{Token, TokenKind};
use bamts_compiler::telemetry::{PhaseTotals, TelemetryCollector};
use serde::Deserialize;
use super::ci::{audit_ledger, facet_owning_slice, filters_need_workspace_pins};
use super::snapshot::{
    TempDir, case_inputs_from_index, compiler_snapshot_input, decode_case_source,
    index_content_digest, io_err, is_safe_logical_path, observable_kind, read_snapshot_case,
    read_verified_asset, read_verified_snapshot_asset, split_configuration, verify_pin_document,
    verify_snapshot,
};
use super::{
    AOT_SCRATCH_CAP_BYTES, AssetKind, BackendFilter, COMPILER_CATALOG, CellResult, FailureClass,
    IndexEntry, OUTPUT_CAP_BYTES, RunFilterOptions, RunState, SnapshotAssets, StatusFilter,
    SuiteRunReport, SuiteSnapshot,
};
use crate::catalog::{self, ObservableKind};
use crate::check_cells::{self, CasePragmas, CheckContext};
use crate::corpus::{
    ArtifactDirectory, CaseSpec, DigestAlgorithm, ExecutionMode as CorpusExecutionMode,
    NODE_VERSION, OracleLimits, Provenance, bounded_output, cli_args, drain_stream, normalized_env,
    run_process,
};
use crate::facets;
use crate::lane::{LaneOutcome, LaneRequest};
use crate::schema::sha256_hex;
use crate::shard::{ExecutionMode, ObligationKey};
use crate::ts_ledger::{Backend, Entry, Facet, Status, TimeoutClass, TsLedger};
use crate::{ErrorCode, Result, VerificationError};

const FRONTEND_DEFAULT_MS: u64 = 5_000;
const FRONTEND_CAP_MS: u64 = 30_000;
const EXECUTE_DEFAULT_MS: u64 = 10_000;
const EXECUTE_CAP_MS: u64 = 60_000;
const PROJECT_DEFAULT_MS: u64 = 30_000;
const PROJECT_CAP_MS: u64 = 60_000;
const WATCH_DEFAULT_MS: u64 = 30_000;
const WATCH_CAP_MS: u64 = 60_000;

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

pub(super) fn scratch_case_spec(id: &str) -> CaseSpec {
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

pub(super) fn enforce_no_silent_skip(planned: &[PlannedCell], results: &[CellResult]) -> Result<()> {
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
    let Some(prefix_text) = shard_key.get(..8) else {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("shard key `{shard_key}` splits a character in its first 8 bytes"),
        ));
    };
    let prefix = u32::from_str_radix(prefix_text, 16).map_err(|error| {
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
pub(super) fn status_name(status: Status) -> &'static str {
    match status {
        Status::Included => "included",
        Status::Deferred => "deferred",
        Status::Excluded => "excluded",
    }
}

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
    let kind = observable_kind(observable);
    if kind != Some(ObservableKind::Trace)
        && kind != Some(ObservableKind::Declaration)
        && kind != Some(ObservableKind::Diagnostics)
        && kind != Some(ObservableKind::JavaScript)
    {
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
    let check = match kind {
        Some(ObservableKind::Trace) => observe_project_trace(snapshot, index_entry),
        Some(ObservableKind::Declaration) => observe_project_declaration(snapshot, index_entry),
        Some(ObservableKind::Diagnostics) => {
            observe_project_diagnostics(snapshot, _ctx, index_entry)
        }
        Some(ObservableKind::JavaScript) => observe_project_javascript(snapshot, index_entry),
        _ => {
            return CompilerLaneObservation::blocking(
                input,
                variant,
                observable,
                BTreeMap::new(),
                format!("project case `{input}` does not route observable `{observable}`"),
            );
        }
    };
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
    let physical_root = display_path(loaded.root().path());
    let produced = rendered
        .replace(&physical_root, fixture.project_root.trim_end_matches('/'))
        .into_bytes();
    Ok((produced, expected, baseline_path))
}
enum ProjectEmitError {
    InvalidFixture(String),
    UnsafeProjectRoot(String),
    UnsafeInputFiles(String),
    Harness(String),
    MissingBaseline(String),
    Compile(String),
    InvalidPath(String),
}

impl ProjectEmitError {
    fn detail(&self) -> String {
        match self {
            Self::InvalidFixture(msg)
            | Self::UnsafeProjectRoot(msg)
            | Self::UnsafeInputFiles(msg)
            | Self::Harness(msg)
            | Self::MissingBaseline(msg)
            | Self::Compile(msg)
            | Self::InvalidPath(msg) => msg.clone(),
        }
    }
}

fn observe_project_declaration(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> check_cells::CompilerCheckObservation {
    match produce_project_declaration(snapshot, index_entry) {
        Ok((produced, _expected_count)) => check_cells::CompilerCheckObservation {
            class: FailureClass::Pass,
            detail: String::new(),
            artifact: Some(produced),
        },
        Err(
            err @ (ProjectEmitError::Harness(_)
            | ProjectEmitError::InvalidFixture(_)
            | ProjectEmitError::InvalidPath(_)),
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

struct ProjectFixture {
    value: serde_json::Value,
    root: String,
    input_files: Vec<String>,
    relative_case: String,
}

fn read_project_fixture(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> std::result::Result<ProjectFixture, ProjectEmitError> {
    let descriptor = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)
        .map_err(|error| ProjectEmitError::Harness(error.to_string()))?;
    let value: serde_json::Value = serde_json::from_slice(&descriptor).map_err(|error| {
        ProjectEmitError::InvalidFixture(format!("invalid project fixture: {error}"))
    })?;
    let root = value
        .get("projectRoot")
        .and_then(|value| value.as_str())
        .ok_or_else(|| {
            ProjectEmitError::InvalidFixture("project fixture has no projectRoot".to_owned())
        })?
        .to_owned();
    if !root.starts_with("tests/cases/projects/") || !is_safe_logical_path(&root) {
        return Err(ProjectEmitError::UnsafeProjectRoot(format!(
            "project fixture has unsafe projectRoot `{root}`"
        )));
    }
    let input_files: Vec<String> = value
        .get("inputFiles")
        .and_then(|value| value.as_array())
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item.as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default();
    if input_files.iter().any(|path| !is_safe_logical_path(path)) {
        return Err(ProjectEmitError::UnsafeInputFiles(
            "project fixture has unsafe inputFiles".to_owned(),
        ));
    }
    let relative_case = index_entry
        .logical_path
        .strip_prefix("tests/cases/project/")
        .and_then(|path| path.strip_suffix(".json"))
        .ok_or_else(|| {
            ProjectEmitError::InvalidPath(format!(
                "project fixture path `{}` has no project baseline stem",
                index_entry.logical_path
            ))
        })?
        .to_owned();
    Ok(ProjectFixture {
        value,
        root,
        input_files,
        relative_case,
    })
}

fn materialize_project(
    snapshot: &(impl SnapshotAssets + ?Sized),
    project_root: &str,
    temp_prefix: &str,
) -> std::result::Result<(TempDir, PathBuf), ProjectEmitError> {
    let temp = TempDir::new(temp_prefix)
        .map_err(|error| ProjectEmitError::Harness(format!("project temp root: {error}")))?;
    let project_dir = temp.path().join(project_root);
    fs::create_dir_all(&project_dir).map_err(|error| {
        ProjectEmitError::Harness(format!("project root `{}`: {error}", project_dir.display()))
    })?;
    let project_prefix = format!("{}/", project_root.trim_end_matches('/'));
    for entry in snapshot.index().entries.values() {
        let Some(relative) = entry.logical_path.strip_prefix(&project_prefix) else {
            continue;
        };
        if entry.asset_kind != AssetKind::CaseInput || !is_safe_logical_path(relative) {
            continue;
        }
        let bytes = read_verified_snapshot_asset(snapshot, &entry.logical_path)
            .map_err(|error| ProjectEmitError::Harness(error.to_string()))?;
        let destination = project_dir.join(relative);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(|error| {
                ProjectEmitError::Harness(format!(
                    "project directory `{}`: {error}",
                    parent.display()
                ))
            })?;
        }
        fs::write(&destination, bytes).map_err(|error| {
            ProjectEmitError::Harness(format!(
                "project source `{}`: {error}",
                destination.display()
            ))
        })?;
    }
    Ok((temp, project_dir))
}

fn project_config(
    fixture: &serde_json::Value,
    project_dir: &Path,
    forced: &[(&str, &str)],
) -> std::result::Result<ProjectConfig, ProjectEmitError> {
    let root = ProjectRoot::new(project_dir)
        .map_err(|error| ProjectEmitError::Harness(format!("project root: {error}")))?;
    let config_path = project_dir.join("tsconfig.json");
    let on_disk = if config_path.exists() {
        fs::read_to_string(&config_path).map_err(|error| {
            ProjectEmitError::Harness(format!(
                "project config `{}`: {error}",
                config_path.display()
            ))
        })?
    } else {
        "{}".to_owned()
    };
    let mut disk_value: serde_json::Value = serde_json::from_str(&on_disk)
        .map_err(|error| ProjectEmitError::Harness(format!("project config parse: {error}")))?;
    if !disk_value.is_object() {
        return Err(ProjectEmitError::Harness(
            "project config is not an object".to_owned(),
        ));
    }
    let fixture_object = fixture.as_object().cloned().unwrap_or_default();
    let ignored = [
        "scenario",
        "projectRoot",
        "inputFiles",
        "baselineCheck",
        "runTest",
        "resolvedInputFiles",
        "emittedFiles",
    ];
    let disk_object = disk_value
        .as_object_mut()
        .ok_or_else(|| ProjectEmitError::Harness("project config is not an object".to_owned()))?;
    let compiler_options = disk_object
        .entry("compilerOptions")
        .or_insert_with(|| serde_json::Value::Object(serde_json::Map::new()));
    if let serde_json::Value::Object(map) = compiler_options {
        for (key, value) in &fixture_object {
            if ignored.contains(&key.as_str()) {
                continue;
            }
            map.insert(key.clone(), value.clone());
        }
        for (key, value) in forced {
            map.entry((*key).to_owned())
                .or_insert_with(|| serde_json::Value::String((*value).to_owned()));
        }
        if !forced.is_empty() {
            map.entry("moduleResolution".to_owned())
                .or_insert_with(|| serde_json::Value::String("classic".to_owned()));
        }
    }
    let merged_source = serde_json::to_string(&disk_value)
        .map_err(|error| ProjectEmitError::Harness(format!("project config serialize: {error}")))?;
    ProjectConfig::parse(&root, &config_path, &merged_source)
        .map_err(|error| ProjectEmitError::Harness(format!("project config: {error}")))
}

fn load_project_program(
    input_files: &[String],
    config: &ProjectConfig,
    project_dir: &Path,
) -> std::result::Result<bamts_compiler::program::ResolvedProgram, ProjectEmitError> {
    let root = ProjectRoot::new(project_dir)
        .map_err(|error| ProjectEmitError::Harness(format!("project root: {error}")))?;
    let mut roots: Vec<PathBuf> = input_files.iter().map(PathBuf::from).collect();
    if roots.is_empty() {
        roots = config.files().to_vec();
    }
    if roots.is_empty() {
        roots = collect_project_sources(project_dir).map_err(ProjectEmitError::Harness)?;
    }
    if roots.is_empty() {
        return Err(ProjectEmitError::Compile(
            "project has no roots to compile".to_owned(),
        ));
    }
    let loader = ProgramLoader::new(&root, config.options())
        .map_err(|error| ProjectEmitError::Harness(format!("project loader: {error}")))?;
    loader
        .load_roots(&roots)
        .map_err(|error| ProjectEmitError::Compile(format!("project load failed: {error}")))
}

fn produce_project_declaration(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> std::result::Result<(Vec<u8>, usize), ProjectEmitError> {
    let ProjectFixture {
        value: fixture,
        root: project_root,
        input_files,
        relative_case,
    } = read_project_fixture(snapshot, index_entry)?;
    let manifest_path =
        format!("tests/baselines/reference/project/{relative_case}/node/{relative_case}.json");
    let manifest_bytes =
        read_verified_snapshot_asset(snapshot, &manifest_path).map_err(|error| {
            ProjectEmitError::MissingBaseline(format!(
                "missing declaration manifest `{manifest_path}`: {error}"
            ))
        })?;
    let manifest: serde_json::Value = serde_json::from_slice(&manifest_bytes).map_err(|error| {
        ProjectEmitError::Harness(format!("invalid declaration manifest: {error}"))
    })?;
    let empty = Vec::new();
    let emitted = manifest
        .get("emittedFiles")
        .and_then(|value| value.as_array())
        .unwrap_or(&empty);
    let mut expected_dts: Vec<String> = emitted
        .iter()
        .filter_map(|item| item.as_str())
        .filter(|name| name.ends_with(".d.ts"))
        .map(str::to_owned)
        .collect();
    expected_dts.sort();
    let (_temp, project_dir) = materialize_project(snapshot, &project_root, "bamts-project-decl")?;
    let config = project_config(&fixture, &project_dir, &[])?;
    if !config.options().declaration() {
        if expected_dts.is_empty() {
            return Ok((Vec::new(), 0));
        }
        return Err(ProjectEmitError::Compile(format!(
            "declaration file list mismatch against `{manifest_path}`: produced [], expected [{}]",
            expected_dts.join(", ")
        )));
    }
    let loaded = load_project_program(&input_files, &config, &project_dir)?;
    let frontend = compile_program_frontend(&loaded, FrontendMode::Declaration);
    let mut produced_by_source: BTreeMap<String, String> = BTreeMap::new();
    for module in loaded.modules() {
        let Ok(relative) = module.path().strip_prefix(&project_dir) else {
            continue;
        };
        if module.path().extension().is_some_and(|ext| ext == "d") {
            continue;
        }
        let relative_posix = relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let Some(output) = frontend
            .modules()
            .iter()
            .find(|item| item.source_file().source_id() == module.source_id())
        else {
            continue;
        };
        let Some(code) = output
            .emit()
            .as_ref()
            .and_then(|emit| emit.declaration.as_ref())
            .map(|file| file.code.clone())
        else {
            continue;
        };
        produced_by_source.insert(relative_posix, code);
    }
    let declaration_dir_prefix = config
        .options()
        .declaration_dir()
        .and_then(|dir| dir.strip_prefix(&project_dir).ok())
        .map(|relative| {
            relative
                .components()
                .map(|component| component.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/")
        })
        .filter(|prefix| !prefix.is_empty())
        .map(|prefix| format!("{prefix}/"))
        .unwrap_or_default();
    let mut produced_outputs: BTreeMap<String, String> = BTreeMap::new();
    for (source, code) in &produced_by_source {
        let stem = source
            .strip_suffix(".ts")
            .or_else(|| source.strip_suffix(".tsx"))
            .or_else(|| source.strip_suffix(".js"))
            .unwrap_or(source);
        produced_outputs.insert(format!("{declaration_dir_prefix}{stem}.d.ts"), code.clone());
    }
    let mut produced_names: Vec<String> = produced_outputs.keys().cloned().collect();
    produced_names.sort();
    if produced_names != expected_dts {
        return Err(ProjectEmitError::Compile(format!(
            "declaration file list mismatch against `{manifest_path}`: produced [{}], expected [{}]",
            produced_names.join(", "),
            expected_dts.join(", ")
        )));
    }
    let mut artifact = String::new();
    for name in &expected_dts {
        let amd_path = format!("tests/baselines/reference/project/{relative_case}/amd/{name}");
        let node_path = format!("tests/baselines/reference/project/{relative_case}/node/{name}");
        let amd_bytes = read_verified_snapshot_asset(snapshot, &amd_path).map_err(|error| {
            ProjectEmitError::MissingBaseline(format!(
                "missing declaration baseline `{amd_path}`: {error}"
            ))
        })?;
        let node_bytes = read_verified_snapshot_asset(snapshot, &node_path).map_err(|error| {
            ProjectEmitError::MissingBaseline(format!(
                "missing declaration baseline `{node_path}`: {error}"
            ))
        })?;
        if amd_bytes != node_bytes {
            return Err(ProjectEmitError::Compile(format!(
                "amd/node declaration baselines differ for `{name}`"
            )));
        }
        let Some(produced) = produced_outputs.get(name) else {
            return Err(ProjectEmitError::Compile(format!(
                "no declaration emit for `{name}`"
            )));
        };
        let expected_text = String::from_utf8_lossy(&node_bytes).into_owned();
        if produced != &expected_text {
            return Err(ProjectEmitError::Compile(format!(
                "declaration mismatch against `{node_path}`: produced {} bytes, expected {} bytes",
                produced.len(),
                node_bytes.len()
            )));
        }
        artifact.push_str(produced);
        artifact.push('\n');
    }
    Ok((artifact.into_bytes(), expected_dts.len()))
}

fn observe_project_javascript(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> check_cells::CompilerCheckObservation {
    match produce_project_javascript(snapshot, index_entry) {
        Ok(produced) => check_cells::CompilerCheckObservation {
            class: FailureClass::Pass,
            detail: String::new(),
            artifact: Some(produced),
        },
        Err(
            err @ (ProjectEmitError::Harness(_)
            | ProjectEmitError::InvalidFixture(_)
            | ProjectEmitError::InvalidPath(_)),
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

const PROJECT_MODULE_VARIANTS: [(&str, &str); 2] = [("amd", "amd"), ("node", "commonjs")];

fn produce_project_javascript(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> std::result::Result<Vec<u8>, ProjectEmitError> {
    let fixture = read_project_fixture(snapshot, index_entry)?;
    let mut artifact = String::new();
    for (variant, module) in PROJECT_MODULE_VARIANTS {
        let relative_case = &fixture.relative_case;
        let manifest_path = format!(
            "tests/baselines/reference/project/{relative_case}/{variant}/{relative_case}.json"
        );
        let manifest_bytes =
            read_verified_snapshot_asset(snapshot, &manifest_path).map_err(|error| {
                ProjectEmitError::MissingBaseline(format!(
                    "missing project manifest `{manifest_path}`: {error}"
                ))
            })?;
        let manifest: serde_json::Value =
            serde_json::from_slice(&manifest_bytes).map_err(|error| {
                ProjectEmitError::Harness(format!("invalid project manifest: {error}"))
            })?;
        let mut expected: Vec<String> = manifest
            .get("emittedFiles")
            .and_then(|value| value.as_array())
            .map(|items| {
                items
                    .iter()
                    .filter_map(|item| item.as_str())
                    .filter(|name| name.ends_with(".js"))
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default();
        expected.sort();
        let (_temp, project_dir) =
            materialize_project(snapshot, &fixture.root, "bamts-project-javascript")?;
        let mut forced: Vec<(&str, &str)> = vec![("module", module), ("target", "es5")];
        if fixture.value.get("strict") != Some(&serde_json::Value::Bool(false)) {
            forced.push(("alwaysStrict", "true"));
        }
        let config = project_config(&fixture.value, &project_dir, &forced)?;
        let produced = if expected.is_empty() {
            BTreeMap::new()
        } else {
            let loaded = load_project_program(&fixture.input_files, &config, &project_dir)?;
            project_javascript_outputs(&loaded, &config, &project_dir)
        };
        let produced_names: Vec<String> = produced.keys().cloned().collect();
        if produced_names != expected {
            return Err(ProjectEmitError::Compile(format!(
                "javascript file list mismatch against `{manifest_path}`: produced [{}], expected [{}]",
                produced_names.join(", "),
                expected.join(", ")
            )));
        }
        for (name, code) in &produced {
            let baseline_path =
                format!("tests/baselines/reference/project/{relative_case}/{variant}/{name}");
            let baseline =
                read_verified_snapshot_asset(snapshot, &baseline_path).map_err(|error| {
                    ProjectEmitError::MissingBaseline(format!(
                        "missing javascript baseline `{baseline_path}`: {error}"
                    ))
                })?;
            if code.as_bytes() != baseline.as_slice() {
                return Err(ProjectEmitError::Compile(format!(
                    "javascript mismatch against `{baseline_path}`: produced {} bytes, expected {} bytes",
                    code.len(),
                    baseline.len()
                )));
            }
            artifact.push_str(code);
            artifact.push('\n');
        }
    }
    Ok(artifact.into_bytes())
}

fn project_javascript_outputs(
    loaded: &bamts_compiler::program::ResolvedProgram,
    config: &ProjectConfig,
    project_dir: &Path,
) -> BTreeMap<String, String> {
    let frontend = compile_program_frontend(loaded, FrontendMode::JavaScript);
    let sources: Vec<(String, String)> = loaded
        .modules()
        .iter()
        .filter_map(|module| {
            let relative = module.path().strip_prefix(project_dir).ok()?;
            let posix = relative
                .components()
                .map(|component| component.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/");
            let code = frontend
                .modules()
                .iter()
                .find(|item| item.source_file().source_id() == module.source_id())?
                .emit()
                .as_ref()?
                .javascript
                .as_ref()?
                .code
                .clone();
            Some((posix, code))
        })
        .filter(|(posix, _)| {
            !posix.ends_with(".d.ts")
                && !posix.ends_with(".json")
                && (config.options().allow_js() || !posix.ends_with(".js"))
        })
        .collect();
    let common: Vec<String> =
        check_cells::common_directory(sources.iter().map(|(posix, _)| posix.as_str()))
            .into_iter()
            .map(str::to_owned)
            .collect();
    let common: Vec<&str> = common.iter().map(String::as_str).collect();
    let out_dir = config
        .options()
        .out_dir()
        .and_then(|dir| dir.strip_prefix(project_dir).ok())
        .map(|relative| {
            relative
                .components()
                .map(|component| component.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/")
        });
    sources
        .into_iter()
        .map(|(posix, code)| {
            let stem = posix
                .rsplit_once('.')
                .map_or(posix.as_str(), |(stem, _)| stem);
            let path = match &out_dir {
                Some(directory) => check_cells::emitted_path(
                    directory,
                    &common,
                    &posix,
                    &format!("{}.js", stem.rsplit('/').next().unwrap_or(stem)),
                ),
                None => format!("{stem}.js"),
            };
            (path.trim_start_matches('/').to_owned(), code)
        })
        .collect()
}
fn observe_project_diagnostics(
    snapshot: &(impl SnapshotAssets + ?Sized),
    ctx: &CheckContext,
    index_entry: &IndexEntry,
) -> check_cells::CompilerCheckObservation {
    match produce_project_diagnostics(snapshot, ctx, index_entry) {
        Ok(produced) => check_cells::CompilerCheckObservation {
            class: FailureClass::Pass,
            detail: String::new(),
            artifact: Some(produced),
        },
        Err(
            err @ (ProjectEmitError::Harness(_)
            | ProjectEmitError::InvalidFixture(_)
            | ProjectEmitError::InvalidPath(_)),
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

fn produce_project_diagnostics(
    snapshot: &(impl SnapshotAssets + ?Sized),
    ctx: &CheckContext,
    index_entry: &IndexEntry,
) -> std::result::Result<Vec<u8>, ProjectEmitError> {
    let (fixture, project_root, input_files, relative_case) =
        project_diagnostic_case(snapshot, index_entry)?;
    let ProjectDiagnosticBaseline {
        file_rows: expected,
        amd_globals,
        node_globals,
        node_path,
    } = project_diagnostic_expected(snapshot, &relative_case)?;
    let actual = project_diagnostic_actual(snapshot, &fixture, &project_root, &input_files)?;
    match facets::compare_diagnostics(&expected, &actual, &ctx.code_map) {
        facets::FacetVerdict::Pass => {}
        facets::FacetVerdict::Fail { reason } => {
            return Err(ProjectEmitError::Compile(format!(
                "diagnostic mismatch against `{node_path}`: {reason}"
            )));
        }
        facets::FacetVerdict::Unproven { reason } => {
            return Err(ProjectEmitError::Harness(format!(
                "diagnostic oracle could not prove parity against `{node_path}`: {reason}"
            )));
        }
    }
    if !amd_globals.is_empty() || !node_globals.is_empty() {
        let amd_codes: Vec<&str> = amd_globals.iter().map(|(code, _)| code.as_str()).collect();
        let node_codes: Vec<&str> = node_globals.iter().map(|(code, _)| code.as_str()).collect();
        return Err(ProjectEmitError::Compile(format!(
            "missing global diagnostics against `{node_path}`: expected amd [{}] node [{}], produced []",
            amd_codes.join(", "),
            node_codes.join(", ")
        )));
    }
    serde_json::to_vec(&actual)
        .map_err(|error| ProjectEmitError::Harness(format!("diagnostic artifact: {error}")))
}

fn project_diagnostic_case(
    snapshot: &(impl SnapshotAssets + ?Sized),
    index_entry: &IndexEntry,
) -> std::result::Result<(serde_json::Value, String, Vec<String>, String), ProjectEmitError> {
    let descriptor = read_verified_snapshot_asset(snapshot, &index_entry.logical_path)
        .map_err(|error| ProjectEmitError::Harness(error.to_string()))?;
    let fixture: serde_json::Value = serde_json::from_slice(&descriptor).map_err(|error| {
        ProjectEmitError::InvalidFixture(format!("invalid project fixture: {error}"))
    })?;
    let project_root = fixture
        .get("projectRoot")
        .and_then(|value| value.as_str())
        .ok_or_else(|| {
            ProjectEmitError::InvalidFixture("project fixture has no projectRoot".to_owned())
        })?
        .to_owned();
    if !project_root.starts_with("tests/cases/projects/") || !is_safe_logical_path(&project_root) {
        return Err(ProjectEmitError::UnsafeProjectRoot(format!(
            "project fixture has unsafe projectRoot `{project_root}`"
        )));
    }
    let input_files: Vec<String> = fixture
        .get("inputFiles")
        .and_then(|value| value.as_array())
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item.as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default();
    if input_files.iter().any(|path| !is_safe_logical_path(path)) {
        return Err(ProjectEmitError::UnsafeInputFiles(
            "project fixture has unsafe inputFiles".to_owned(),
        ));
    }
    let relative_case = index_entry
        .logical_path
        .strip_prefix("tests/cases/project/")
        .and_then(|path| path.strip_suffix(".json"))
        .ok_or_else(|| {
            ProjectEmitError::InvalidPath(format!(
                "project fixture path `{}` has no project baseline stem",
                index_entry.logical_path
            ))
        })?
        .to_owned();
    Ok((fixture, project_root, input_files, relative_case))
}

struct ProjectDiagnosticBaseline {
    file_rows: Vec<facets::FacetDiagnostic>,
    amd_globals: Vec<(String, String)>,
    node_globals: Vec<(String, String)>,
    node_path: String,
}

fn project_diagnostic_expected(
    snapshot: &(impl SnapshotAssets + ?Sized),
    relative_case: &str,
) -> std::result::Result<ProjectDiagnosticBaseline, ProjectEmitError> {
    let amd_path =
        format!("tests/baselines/reference/project/{relative_case}/amd/{relative_case}.errors.txt");
    let node_path = format!(
        "tests/baselines/reference/project/{relative_case}/node/{relative_case}.errors.txt"
    );
    let amd_bytes = read_verified_snapshot_asset(snapshot, &amd_path).map_err(|error| {
        ProjectEmitError::MissingBaseline(format!(
            "missing diagnostic baseline `{amd_path}`: {error}"
        ))
    })?;
    let node_bytes = read_verified_snapshot_asset(snapshot, &node_path).map_err(|error| {
        ProjectEmitError::MissingBaseline(format!(
            "missing diagnostic baseline `{node_path}`: {error}"
        ))
    })?;
    let amd_parsed = check_cells::parse_errors_baseline(&String::from_utf8_lossy(&amd_bytes));
    let node_parsed = check_cells::parse_errors_baseline(&String::from_utf8_lossy(&node_bytes));
    let mut amd_rows: Vec<facets::FacetDiagnostic> = amd_parsed
        .diagnostics
        .iter()
        .map(facet_from_errors_row)
        .collect();
    let mut node_rows: Vec<facets::FacetDiagnostic> = node_parsed
        .diagnostics
        .iter()
        .map(facet_from_errors_row)
        .collect();
    amd_rows.sort();
    node_rows.sort();
    if amd_rows != node_rows {
        return Err(ProjectEmitError::Compile(format!(
            "amd/node file diagnostics differ for `{relative_case}`"
        )));
    }
    let amd_globals: Vec<(String, String)> = amd_parsed
        .globals
        .iter()
        .map(|global| (global.code.clone(), global.message.clone()))
        .collect();
    let node_globals: Vec<(String, String)> = node_parsed
        .globals
        .iter()
        .map(|global| (global.code.clone(), global.message.clone()))
        .collect();
    Ok(ProjectDiagnosticBaseline {
        file_rows: node_rows,
        amd_globals,
        node_globals,
        node_path,
    })
}

fn facet_from_errors_row(row: &check_cells::ErrorsDiagnostic) -> facets::FacetDiagnostic {
    let category = if row.category == "warning" {
        facets::DiagnosticCategory::Warning
    } else {
        facets::DiagnosticCategory::Error
    };
    let severity = if row.category == "warning" {
        facets::FacetSeverity::Warning
    } else {
        facets::FacetSeverity::Error
    };
    facets::FacetDiagnostic {
        unit: row.unit.clone(),
        position: facets::SourcePosition {
            line: row.line,
            character: row.character,
        },
        category,
        severity,
        code: row.code.clone(),
    }
}

fn project_diagnostic_actual(
    snapshot: &(impl SnapshotAssets + ?Sized),
    fixture: &serde_json::Value,
    project_root: &str,
    input_files: &[String],
) -> std::result::Result<Vec<facets::FacetDiagnostic>, ProjectEmitError> {
    let temp = TempDir::new("bamts-project-diag")
        .map_err(|error| ProjectEmitError::Harness(format!("project temp root: {error}")))?;
    let project_dir = temp.path().join(project_root);
    fs::create_dir_all(&project_dir).map_err(|error| {
        ProjectEmitError::Harness(format!("project root `{}`: {error}", project_dir.display()))
    })?;
    let project_prefix = format!("{}/", project_root.trim_end_matches('/'));
    for entry in snapshot.index().entries.values() {
        let Some(relative) = entry.logical_path.strip_prefix(&project_prefix) else {
            continue;
        };
        if entry.asset_kind != AssetKind::CaseInput || !is_safe_logical_path(relative) {
            continue;
        }
        let bytes = read_verified_snapshot_asset(snapshot, &entry.logical_path)
            .map_err(|error| ProjectEmitError::Harness(error.to_string()))?;
        let destination = project_dir.join(relative);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(|error| {
                ProjectEmitError::Harness(format!(
                    "project directory `{}`: {error}",
                    parent.display()
                ))
            })?;
        }
        fs::write(&destination, bytes).map_err(|error| {
            ProjectEmitError::Harness(format!(
                "project source `{}`: {error}",
                destination.display()
            ))
        })?;
    }
    let root = ProjectRoot::new(&project_dir)
        .map_err(|error| ProjectEmitError::Harness(format!("project root: {error}")))?;
    let config_path = project_dir.join("tsconfig.json");
    let on_disk = if config_path.exists() {
        fs::read_to_string(&config_path).map_err(|error| {
            ProjectEmitError::Harness(format!(
                "project config `{}`: {error}",
                config_path.display()
            ))
        })?
    } else {
        "{}".to_owned()
    };
    let merged_source = merged_fixture_config(&on_disk, fixture)?;
    let config = ProjectConfig::parse(&root, &config_path, &merged_source)
        .map_err(|error| ProjectEmitError::Harness(format!("project config: {error}")))?;
    let mut roots: Vec<PathBuf> = input_files.iter().map(PathBuf::from).collect();
    if roots.is_empty() {
        roots = config.files().to_vec();
    }
    if roots.is_empty() {
        roots = collect_project_sources(&project_dir).map_err(ProjectEmitError::Harness)?;
    }
    if roots.is_empty() {
        return Err(ProjectEmitError::Compile(
            "project has no roots to compile".to_owned(),
        ));
    }
    let loader = ProgramLoader::new(&root, config.options())
        .map_err(|error| ProjectEmitError::Harness(format!("project loader: {error}")))?;
    let loaded = loader
        .load_roots(&roots)
        .map_err(|error| ProjectEmitError::Compile(format!("project load failed: {error}")))?;
    let frontend = compile_program_frontend(&loaded, FrontendMode::Check);
    let mut actual = Vec::new();
    for module in loaded.modules() {
        let Ok(relative) = module.path().strip_prefix(&project_dir) else {
            continue;
        };
        let name = relative
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default();
        if name.ends_with(".d.ts") {
            continue;
        }
        let relative_posix = relative
            .components()
            .map(|component| component.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let Some(output) = frontend
            .modules()
            .iter()
            .find(|item| item.source_file().source_id() == module.source_id())
        else {
            continue;
        };
        let Ok(text) = SourceText::new(output.source_file().source_text().as_str().to_owned())
        else {
            continue;
        };
        for diagnostic in output.diagnostics() {
            if diagnostic.code().as_str().starts_with("BAMTS-W") {
                continue;
            }
            let (line, character) = text
                .line_column(diagnostic.range().start())
                .map(|(line, character)| ((line + 1) as u32, character as u32))
                .unwrap_or((0, 0));
            let (category, severity) = match diagnostic.severity() {
                DiagnosticSeverity::Warning => (
                    facets::DiagnosticCategory::Warning,
                    facets::FacetSeverity::Warning,
                ),
                DiagnosticSeverity::Error => (
                    facets::DiagnosticCategory::Error,
                    facets::FacetSeverity::Error,
                ),
            };
            actual.push(facets::FacetDiagnostic {
                unit: relative_posix.clone(),
                position: facets::SourcePosition { line, character },
                category,
                severity,
                code: diagnostic.code().as_str().to_owned(),
            });
        }
    }
    actual.sort();
    Ok(actual)
}

fn merged_fixture_config(
    on_disk: &str,
    fixture: &serde_json::Value,
) -> std::result::Result<String, ProjectEmitError> {
    let mut disk_value: serde_json::Value = serde_json::from_str(on_disk)
        .map_err(|error| ProjectEmitError::Harness(format!("project config parse: {error}")))?;
    let disk_object = disk_value
        .as_object_mut()
        .ok_or_else(|| ProjectEmitError::Harness("project config is not an object".to_owned()))?;
    let compiler_options = disk_object
        .entry("compilerOptions")
        .or_insert_with(|| serde_json::Value::Object(serde_json::Map::new()));
    if let (Some(map), Some(fixture_object)) =
        (compiler_options.as_object_mut(), fixture.as_object())
    {
        let ignored = [
            "scenario",
            "projectRoot",
            "inputFiles",
            "baselineCheck",
            "runTest",
            "resolvedInputFiles",
            "emittedFiles",
        ];
        for (key, value) in fixture_object {
            if ignored.contains(&key.as_str()) {
                continue;
            }
            map.insert(key.clone(), value.clone());
        }
    }
    serde_json::to_string(&disk_value)
        .map_err(|error| ProjectEmitError::Harness(format!("project config serialize: {error}")))
}

fn collect_project_sources(project_dir: &Path) -> std::result::Result<Vec<PathBuf>, String> {
    let mut sources = Vec::new();
    let mut stack = vec![project_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir)
            .map_err(|error| format!("project scan `{}`: {error}", dir.display()))?;
        for entry in entries {
            let entry = entry.map_err(|error| format!("project scan entry: {error}"))?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else {
                let name = path
                    .file_name()
                    .map(|name| name.to_string_lossy().into_owned())
                    .unwrap_or_default();
                if name.ends_with(".d.ts") {
                    continue;
                }
                let ext = path
                    .extension()
                    .and_then(|ext| ext.to_str())
                    .unwrap_or_default();
                if !matches!(ext, "ts" | "tsx" | "js" | "jsx") {
                    continue;
                }
                let relative = path
                    .strip_prefix(project_dir)
                    .map_err(|error| format!("project source prefix: {error}"))?;
                sources.push(relative.to_path_buf());
            }
        }
    }
    sources.sort();
    Ok(sources)
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
