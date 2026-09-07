//! Suite run/merge engine behind `suite run` and `suite merge`.
//!
//! A run loads the current locked manifest, converts every logical
//! identifier of the selected catalog into an exact obligation key plus its
//! declared observable, strides the canonical catalog by the requested
//! shard, executes each selected obligation through the real repository
//! path behind [`LaneExecutor`], and streams one strict receipt.  Only the
//! parent lane ([`derive_row`]) can record `PASS`; this module never
//! decides or reclassifies a case.  Blocking per-case outcomes are recorded
//! and the loop continues.
//!
//! A merge discovers JSONL shard documents below a receipts root, rejects
//! wrong catalog/runner/platform, absent/duplicate/stale rows, mixed run
//! bindings, and foreign shard matrices, then delegates the bounded k-way
//! merge to [`crate::evidence::merge_shards`].
//!
//! Runner bindings between the parsed key mode and the workflow-declared
//! runner follow the matrix the four workflows declare:
//! TypeScript→compiler, test262→interpreter|jit|aot, formal-quint→quint,
//! formal-lean→lean, formal-redex→redex, target-cells→aot, and
//! benchmarks→perf.  Runners that do not name a runtime mode bind
//! [`ExecutionMode::Aot`]: their obligations execute the AOT candidate
//! substrate, so every (catalog, mode) pair recovers exactly one runner.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::BufWriter,
    path::{Path, PathBuf},
    sync::LazyLock,
    time::{Duration, Instant},
};

use serde::Deserialize;
use sha2::{Digest, Sha256};

use crate::{
    ErrorCode, Result, VerificationError,
    catalog::{self, CatalogCell},
    classification::{self, ClassificationState, NonPassState},
    evidence::{
        EvidenceHeader, EvidenceReader, EvidenceRow, EvidenceWriter, ExecutionBinding, PublishMode,
        RunBinding, TerminalState, ToolchainPin, WorkingDirectoryPolicy, merge_shards,
    },
    lane::{
        LaneBinding, LaneExecutor, LaneOutcome, LaneProcessResult, LaneRequest, LaneResponse,
        ProcessExecutor, ProcessObservation, derive_row,
    },
    schema,
    shard::{ObligationKey, ShardIdentity, ShardSpec, validate_catalog},
    suite::{DEFAULT_SNAPSHOT_REL, verify_snapshot},
    toolchain_schema::load_target_cells,
};

/// Per-obligation wall-clock bound handed to the lane.
const CASE_TIMEOUT_MS: u64 = 30_000;
/// Manifest schema tag produced by `catalog regenerate`.
const MANIFEST_SCHEMA: &str = "bamti.verification-manifest/v1";
const PROBE_OUTPUT_BYTES: usize = 1 << 16;

/// CLIs and workers take this API verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteRunRequest {
    pub catalog: String,
    pub shard: ShardSpec,
    pub receipt: PathBuf,
    pub runner: String,
    pub platform: String,
    pub execution: ExecutionBinding,
}

/// Inputs for a deterministic receipt merge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteMergeRequest {
    pub catalog: String,
    pub receipts: PathBuf,
    pub out: PathBuf,
    pub publish: PublishMode,
}

/// Counted outcome of a run or a merge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteReport {
    pub catalog: String,
    pub runner: String,
    pub platform: String,
    pub obligations: usize,
    pub rows: usize,
    pub states: BTreeMap<String, usize>,
    pub obligation_set_digest: String,
    pub out: PathBuf,
    /// Run shard, or the unsharded identity a merge published.
    pub shard: ShardSpec,
    /// Shard documents consumed (0 for a run).
    pub documents: usize,
}

/// Closed runner set declared by the workflows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SuiteRunner {
    Compiler,
    Interpreter,
    Jit,
    Aot,
    Quint,
    Lean,
    Redex,
    Perf,
}

impl SuiteRunner {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::Interpreter => "interpreter",
            Self::Jit => "jit",
            Self::Aot => "aot",
            Self::Quint => "quint",
            Self::Lean => "lean",
            Self::Redex => "redex",
            Self::Perf => "perf",
        }
    }

    /// Key mode this runner binds.  Non-runtime runners execute the AOT
    /// candidate substrate and therefore bind `ExecutionMode::Aot`.
    #[must_use]
    pub const fn execution_mode(self) -> crate::shard::ExecutionMode {
        match self {
            Self::Interpreter => crate::shard::ExecutionMode::Interpreter,
            Self::Jit => crate::shard::ExecutionMode::Jit,
            Self::Compiler | Self::Aot | Self::Quint | Self::Lean | Self::Redex | Self::Perf => {
                crate::shard::ExecutionMode::Aot
            }
        }
    }
}

/// Workflow-declared runner allowlist for one catalog.
fn allowed_runners(catalog: &str) -> Result<&'static [SuiteRunner]> {
    if catalog.starts_with("typescript-") {
        return Ok(&[SuiteRunner::Compiler]);
    }
    match catalog {
        "test262" => Ok(&[SuiteRunner::Interpreter, SuiteRunner::Jit, SuiteRunner::Aot]),
        "formal-quint" => Ok(&[SuiteRunner::Quint]),
        "formal-lean" => Ok(&[SuiteRunner::Lean]),
        "formal-redex" => Ok(&[SuiteRunner::Redex]),
        "target-cells" => Ok(&[SuiteRunner::Aot]),
        "benchmarks" => Ok(&[SuiteRunner::Perf]),
        _ => Err(VerificationError::new(
            ErrorCode::Usage,
            format!("unknown catalog `{catalog}` for suite selection"),
        )),
    }
}

/// Resolves the requested runner against the workflow-declared mapping.
///
/// An empty runner selects the catalog's sole declared runner; catalogs
/// with several declared runners require an explicit `BAMTS_MODE`.
pub fn resolve_runner(catalog: &str, runner: &str) -> Result<SuiteRunner> {
    // Reject names outside the locked manifest's catalogue before aliases.
    if !schema::CATALOG_NAMES.contains(&catalog) {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("unknown catalog `{catalog}`"),
        ));
    }
    let allowed = allowed_runners(catalog)?;
    if runner.is_empty() {
        return match allowed {
            [sole] => Ok(*sole),
            _ => Err(VerificationError::new(
                ErrorCode::Usage,
                format!(
                    "catalog `{catalog}` declares runners [{}]; `BAMTS_MODE` must choose one",
                    allowed
                        .iter()
                        .map(|entry| entry.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            )),
        };
    }
    allowed
        .iter()
        .find(|entry| entry.as_str() == runner)
        .copied()
        .ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "runner `{runner}` is not workflow-declared for catalog `{catalog}` (allowed: [{}])",
                    allowed
                        .iter()
                        .map(|entry| entry.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            )
        })
}

/// Recovers the runner a receipt row's key mode binds for `catalog`.
///
/// Returns `None` when the pair is not workflow-declared; merges reject it.
fn runner_for_mode(catalog: &str, mode: crate::shard::ExecutionMode) -> Option<SuiteRunner> {
    let allowed = allowed_runners(catalog).ok()?;
    use crate::shard::ExecutionMode as Mode;
    let runner = match mode {
        Mode::Interpreter => SuiteRunner::Interpreter,
        Mode::Jit => SuiteRunner::Jit,
        Mode::Aot => {
            if catalog.starts_with("typescript-") {
                SuiteRunner::Compiler
            } else {
                match catalog {
                    "test262" => SuiteRunner::Aot,
                    "formal-quint" => SuiteRunner::Quint,
                    "formal-lean" => SuiteRunner::Lean,
                    "formal-redex" => SuiteRunner::Redex,
                    "target-cells" => SuiteRunner::Aot,
                    "benchmarks" => SuiteRunner::Perf,
                    _ => return None,
                }
            }
        }
    };
    allowed.contains(&runner).then_some(runner)
}

/// Platform token used when `BAMTS_PLATFORM` is unset: the host triple in
/// the form the receipts already record.
#[must_use]
pub fn default_platform() -> String {
    let arch = std::env::consts::ARCH;
    match std::env::consts::OS {
        "linux" => format!("{arch}-unknown-linux-gnu"),
        "macos" => format!("{arch}-apple-darwin"),
        "windows" => format!("{arch}-pc-windows-msvc"),
        os => format!("{arch}-unknown-{os}"),
    }
}

/// Selected catalog plus the digests that name the current manifest image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CatalogManifest {
    pub catalog: String,
    pub identifiers: Vec<String>,
    pub manifest_path: PathBuf,
    pub manifest_sha256: String,
    pub source_ledger_sha256: String,
    pub identifiers_sha256: String,
}

/// Loads the locked manifest and proves the selected catalog's identity:
/// schema tag, sources-ledger pin, identifier count, digest, order.
pub fn load_catalog_manifest(root: &Path, catalog: &str) -> Result<CatalogManifest> {
    if !schema::CATALOG_NAMES.contains(&catalog) {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!("unknown catalog `{catalog}`"),
        ));
    }
    let manifest_path = root.join(schema::MANIFEST_PATH);
    let bytes = schema::read_bytes(&manifest_path)?;
    let manifest_sha256 = schema::sha256_hex(&bytes);
    schema::reject_duplicate_json_keys(&manifest_path, &bytes)?;
    let manifest: schema::VerificationManifest = schema::parse_json(&manifest_path, &bytes)?;
    if manifest.schema != MANIFEST_SCHEMA {
        return Err(schema::schema_error(
            &manifest_path,
            format!(
                "expected schema `{MANIFEST_SCHEMA}`, found `{}`",
                manifest.schema
            ),
        ));
    }
    let sources_bytes = schema::read_bytes(&root.join(schema::SOURCES_PATH))?;
    let source_ledger_sha256 = schema::sha256_hex(&sources_bytes);
    if manifest.source_ledger_sha256 != source_ledger_sha256 {
        return Err(schema::schema_error(
            &manifest_path,
            "manifest source ledger digest does not match the current sources pin",
        ));
    }
    let selected = manifest
        .catalogs
        .iter()
        .find(|entry| entry.id == catalog)
        .ok_or_else(|| {
            schema::schema_error(
                &manifest_path,
                format!("manifest has no catalog `{catalog}`"),
            )
        })?;
    if selected.identifier_count != selected.identifiers.len() {
        return Err(schema::schema_error(
            &manifest_path,
            format!(
                "catalog `{catalog}` declares {} identifiers but carries {}",
                selected.identifier_count,
                selected.identifiers.len()
            ),
        ));
    }
    let identifiers_sha256 = schema::identifiers_sha256(&selected.identifiers);
    if selected.identifiers_sha256 != identifiers_sha256 {
        return Err(schema::schema_error(
            &manifest_path,
            format!("catalog `{catalog}` identifier digest does not match its list"),
        ));
    }
    for pair in selected.identifiers.windows(2) {
        if pair[0] >= pair[1] {
            return Err(schema::schema_error(
                &manifest_path,
                format!("catalog `{catalog}` identifiers are not strictly increasing"),
            ));
        }
    }
    Ok(CatalogManifest {
        catalog: catalog.to_owned(),
        identifiers: selected.identifiers.clone(),
        manifest_path,
        manifest_sha256,
        source_ledger_sha256,
        identifiers_sha256,
    })
}

/// One exact obligation: canonical lane key plus its declared observables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogicalObligation {
    pub key: ObligationKey,
    pub observables: BTreeSet<String>,
}

/// Converts every logical identifier of the catalog into an exact
/// obligation key and declared observable set, in canonical sorted order.
///
/// TypeScript/test262 identifiers are `authority/runner/case#config#observable`;
/// formal and target identifiers are `locator::name`; benchmark identifiers
/// are the plain rule name.  Keys are built injectively: the observable is
/// folded into the configuration token so one case can carry several
/// observables without colliding.
pub fn materialize_obligations(
    catalog: &str,
    identifiers: &[String],
    runner: SuiteRunner,
    platform: &str,
) -> Result<Vec<LogicalObligation>> {
    if platform.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "obligation platform must be nonempty",
        ));
    }
    let mode = runner.execution_mode();
    let mut obligations = Vec::with_capacity(identifiers.len());
    let authority_prefix = format!("{catalog}/");
    for identifier in identifiers {
        let (case, configuration, observables) = parse_logical_identifier(catalog, identifier)?;
        // TS/test262 cases are `runner/path` tokens after the authority
        // prefix; every other family keeps its own identity segments.
        let key = ObligationKey::new(
            catalog,
            case.strip_prefix(authority_prefix.as_str())
                .map(str::to_owned)
                .unwrap_or(case.clone()),
            configuration,
            mode,
            platform,
        )?;
        let _ = authority_prefix;
        obligations.push(LogicalObligation { key, observables });
    }
    obligations.sort_by(|left, right| left.key.cmp(&right.key));
    validate_catalog(
        &obligations
            .iter()
            .map(|entry| entry.key.clone())
            .collect::<Vec<_>>(),
    )?;
    Ok(obligations)
}

/// Splits one logical identifier into〈case, configuration, observables〉.
///
/// The returned `case` still carries the authority prefix for TS/test262
/// identifiers so callers can make the strip decision themselves.
fn parse_logical_identifier(
    catalog: &str,
    identifier: &str,
) -> Result<(String, String, BTreeSet<String>)> {
    let reject = || {
        VerificationError::new(
            ErrorCode::Schema,
            format!("catalog `{catalog}` has a malformed logical identifier `{identifier}`"),
        )
    };
    if catalog.starts_with("typescript-") || catalog == "test262" {
        let parts: Vec<&str> = identifier.split('#').collect();
        let [case, configuration, observable] = parts.as_slice() else {
            return Err(reject());
        };
        if case.is_empty() || configuration.is_empty() || observable.is_empty() {
            return Err(reject());
        }
        let authority_prefix = format!("{catalog}/");
        if !case.starts_with(&authority_prefix) {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "logical identifier `{identifier}` does not name the `{catalog}` authority"
                ),
            ));
        }
        return Ok((
            (*case).to_owned(),
            format!("{configuration}#{observable}"),
            BTreeSet::from([(*observable).to_owned()]),
        ));
    }
    if identifier.contains("::") {
        let segments: Vec<&str> = identifier.split("::").collect();
        let [locator, name] = segments.as_slice() else {
            return Err(reject());
        };
        if locator.is_empty() || name.is_empty() {
            return Err(reject());
        }
        return Ok((
            (*locator).to_owned(),
            (*name).to_owned(),
            BTreeSet::from([(*name).to_owned()]),
        ));
    }
    if identifier.is_empty() {
        return Err(reject());
    }
    Ok((
        identifier.to_owned(),
        "default".to_owned(),
        BTreeSet::from([identifier.to_owned()]),
    ))
}

fn load_obligation_classifications(
    root: &Path,
    catalog_name: &str,
    identifiers: &[String],
    obligations: &[LogicalObligation],
) -> Result<BTreeMap<ObligationKey, ClassificationState>> {
    let policy = root
        .join(schema::CLASSIFICATION_DIR)
        .join(format!("{catalog_name}.toml"));
    if !policy.exists() {
        return Ok(BTreeMap::new());
    }
    let cells: Vec<CatalogCell> = match catalog_name {
        "test262" => catalog::extract_test262_cells(
            &root.join("target").join("authority").join("test262"),
            catalog_name,
        )?,
        _ => {
            return Err(VerificationError::new(
                ErrorCode::ToolMissing,
                format!(
                    "{}: classification policy exists but no exact catalog-cell loader is registered",
                    policy.display()
                ),
            ));
        }
    };
    let extracted: Vec<String> = cells.iter().map(CatalogCell::rendered_identity).collect();
    if extracted != identifiers {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "classification universe for `{catalog_name}` does not match the locked manifest"
            ),
        ));
    }
    let mut universes = BTreeMap::new();
    universes.insert(catalog_name.to_owned(), cells);
    let states = classification::load_classifications(root, &universes)?;
    if obligations.len() != identifiers.len() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "logical obligations do not cover the classification universe",
        ));
    }
    identifiers
        .iter()
        .zip(obligations)
        .map(|(identifier, obligation)| {
            states
                .get(identifier)
                .copied()
                .map(|state| (obligation.key.clone(), state))
                .ok_or_else(|| {
                    VerificationError::new(
                        ErrorCode::SetMismatch,
                        format!("classification state is missing for `{identifier}`"),
                    )
                })
        })
        .collect()
}

/// Executor backing: an internal adapter, an injected lane worker, or a typed
/// unavailable adapter. An unavailable adapter is evidence, not a suite abort.
enum SuiteAdapter {
    TargetCells(BTreeMap<String, crate::toolchain_schema::TargetCellRecord>),
    External(ProcessExecutor),
    Missing(String),
}

/// The environment variable naming one runner's out-of-process lane worker.
fn lane_adapter_variable(runner: SuiteRunner) -> String {
    format!(
        "BAMTS_SUITE_{}_ADAPTER",
        runner.as_str().to_ascii_uppercase().replace('-', "_")
    )
}

/// Resolves one runner's configured lane worker. The single resolution rule
/// shared by capture and by binding computation: two copies could drift, and
/// a receipt would then content-address a binary the verifier never resolved.
/// A relative path resolves against `root`; a path naming no file is unset.
fn lane_program(root: &Path, runner: SuiteRunner) -> Option<PathBuf> {
    let configured =
        std::env::var_os(lane_adapter_variable(runner)).filter(|value| !value.is_empty())?;
    let program = PathBuf::from(configured);
    let program = if program.is_absolute() {
        program
    } else {
        root.join(program)
    };
    program.is_file().then_some(program)
}

impl SuiteAdapter {
    fn build(root: &Path, catalog: &str, runner: SuiteRunner) -> Result<Self> {
        if runner == SuiteRunner::Aot && catalog == "target-cells" {
            return Ok(Self::TargetCells(load_target_cells(root)?));
        }

        let variable = lane_adapter_variable(runner);
        let Some(configured) = std::env::var_os(&variable).filter(|value| !value.is_empty()) else {
            return Ok(Self::Missing(format!(
                "runner `{}` has no registered adapter; set `{variable}` to an explicit lane-worker executable",
                runner.as_str()
            )));
        };
        let Some(program) = lane_program(root, runner) else {
            let attempted = PathBuf::from(configured);
            let attempted = if attempted.is_absolute() {
                attempted
            } else {
                root.join(attempted)
            };
            return Ok(Self::Missing(format!(
                "runner `{}` adapter `{}` is not a file",
                runner.as_str(),
                attempted.display()
            )));
        };
        Ok(Self::External(
            ProcessExecutor::new(program, Vec::new(), root, root.join("target/suite-lanes"))
                .with_max_output_bytes(PROBE_OUTPUT_BYTES),
        ))
    }

    /// Executes one obligation through an internal path. Result is a worker
    /// outcome; the parent — never this function — derives PASS from it.
    fn evaluate(&self, request: &LaneRequest) -> Result<LaneOutcome> {
        match self {
            Self::TargetCells(cells) => {
                let record = cells.get(request.key().case()).ok_or_else(|| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!(
                            "no target-cell record for `{}` obligation `{}`",
                            request.key().case(),
                            request.key()
                        ),
                    )
                })?;
                let obligation = record
                    .obligations()
                    .get(request.key().configuration())
                    .ok_or_else(|| {
                        VerificationError::new(
                            ErrorCode::Schema,
                            format!(
                                "target cell `{}` has no `{}` obligation evidence",
                                request.key().case(),
                                request.key().configuration()
                            ),
                        )
                    })?;
                Ok(match obligation.status() {
                    TerminalState::Pass => LaneOutcome::Completed {
                        artifacts: request
                            .observables()
                            .iter()
                            .map(|observable| {
                                (
                                    observable.clone(),
                                    schema::sha256_hex(obligation.evidence().as_bytes()),
                                )
                            })
                            .collect(),
                    },
                    TerminalState::BlockingFail => LaneOutcome::BlockingFail {
                        detail: format!(
                            "{}; missing artifact `{}`",
                            obligation.reason(),
                            obligation.missing_artifact()
                        ),
                    },
                    TerminalState::ExternalBlocked => LaneOutcome::ExternalBlocked {
                        detail: format!(
                            "{}; host must supply `{}`",
                            obligation.reason(),
                            obligation.missing_artifact()
                        ),
                    },
                    TerminalState::InapplicableOutOfScopeHostFeature => {
                        LaneOutcome::InapplicableOutOfScopeHostFeature {
                            detail: obligation.reason().to_owned(),
                        }
                    }
                    other => LaneOutcome::BlockingFail {
                        detail: format!(
                            "target-cell obligation `{}` records non-lane terminal state `{}`",
                            request.key().configuration(),
                            other.as_str()
                        ),
                    },
                })
            }
            Self::Missing(detail) => Ok(LaneOutcome::BlockingFail {
                detail: detail.clone(),
            }),
            Self::External(_) => Err(VerificationError::new(
                ErrorCode::Schema,
                "external lane adapter reached the internal evaluator",
            )),
        }
    }
}

/// Parent-side lane driver over suite adapters and locked classifications.
struct SuiteExecutor {
    adapter: SuiteAdapter,
    classifications: BTreeMap<ObligationKey, ClassificationState>,
}

impl LaneExecutor for SuiteExecutor {
    fn run(&mut self, request: &LaneRequest) -> Result<LaneProcessResult> {
        if let Some(outcome) = fourslash_lane_outcome(request.key()) {
            return lane_result(request, outcome, Instant::now());
        }
        if let Some(ClassificationState::NonPass(state)) = self.classifications.get(request.key()) {
            return lane_result(
                request,
                classified_outcome(*state, request.key()),
                Instant::now(),
            );
        }
        if let SuiteAdapter::External(executor) = &mut self.adapter {
            return executor.run(request);
        }
        let started = Instant::now();
        let outcome = self.adapter.evaluate(request)?;
        lane_result(request, outcome, started)
    }
}

/// The `typescript-7.0.2` manifest carries `fourslash/…` language-service
/// authority obligations, and no classification policy exists for that
/// catalog (`verification/classification/` holds only `test262.toml`), so the
/// executor routes them itself: the internal fourslash DSL is an exact
/// completion-contract exclusion and must surface as
/// `INAPPLICABLE_LANGUAGE_SERVICE`, never as a malformed-path blocking error
/// from the compiler lane.
fn fourslash_lane_outcome(key: &ObligationKey) -> Option<LaneOutcome> {
    key.case().starts_with("fourslash/").then(|| {
        LaneOutcome::InapplicableLanguageService {
            detail: format!(
                "fourslash language-service authority case `{}` routed out of the compiler lane (internal fourslash DSL is an exact exclusion)",
                key.case()
            ),
        }
    })
}

fn lane_result(
    request: &LaneRequest,
    outcome: LaneOutcome,
    started: Instant,
) -> Result<LaneProcessResult> {
    let response = LaneResponse::new(
        request.binding().clone(),
        request.request_id(),
        request.key().clone(),
        outcome,
    )?;
    let body = serde_json::to_vec(&response).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!(
                "cannot encode lane response for `{}`: {error}",
                request.key()
            ),
        )
    })?;
    Ok(LaneProcessResult {
        observation: ProcessObservation::Exited { code: 0 },
        response_body: Some(body),
        duration_ms: started.elapsed().as_millis() as u64,
        detail: String::new(),
    })
}

fn classified_outcome(state: NonPassState, key: &ObligationKey) -> LaneOutcome {
    let detail = format!("locked classification for `{key}`");
    match state {
        NonPassState::BlockingFail => LaneOutcome::BlockingFail { detail },
        NonPassState::InapplicableLanguageService => {
            LaneOutcome::InapplicableLanguageService { detail }
        }
        NonPassState::InapplicableOutOfScopeHostFeature => {
            LaneOutcome::InapplicableOutOfScopeHostFeature { detail }
        }
        NonPassState::InapplicableV8Internal => LaneOutcome::InapplicableV8Internal { detail },
        NonPassState::InapplicableCatalogError => LaneOutcome::InapplicableCatalogError { detail },
        NonPassState::ExternalBlocked => LaneOutcome::ExternalBlocked { detail },
    }
}

/// Runs one catalog shard and publishes a strict current receipt.
///
/// Abort error (manifest, adapter, digests, writer) leaves no receipt
/// behind; per-obligation blocking outcomes never abort the loop.
pub fn run_suite(root: &Path, request: &SuiteRunRequest) -> Result<SuiteReport> {
    let runner = resolve_runner(&request.catalog, &request.runner)?;
    let platform = if request.platform.is_empty() {
        default_platform()
    } else {
        request.platform.clone()
    };
    if platform.trim() != platform || platform.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            "suite platform must be a nonempty canonical token",
        ));
    }
    let catalog = load_catalog_manifest(root, &request.catalog)?;
    let obligations =
        materialize_obligations(&request.catalog, &catalog.identifiers, runner, &platform)?;
    let classifications = load_obligation_classifications(
        root,
        &request.catalog,
        &catalog.identifiers,
        &obligations,
    )?;
    let adapter = SuiteAdapter::build(root, &request.catalog, runner)?;
    let keys: Vec<ObligationKey> = obligations.iter().map(|entry| entry.key.clone()).collect();
    let shard = ShardIdentity::plan(request.shard, &keys)?;
    let binding = current_run_binding(root, &request.catalog)?;
    let header = EvidenceHeader::new(shard.clone(), binding, request.execution.clone())?;
    let members: Vec<usize> = request.shard.member_indices(keys.len()).collect();
    let lane_binding = {
        let run = LaneBinding::fresh()?;
        if runner == SuiteRunner::Compiler {
            let verified = verify_snapshot(&root.join(DEFAULT_SNAPSHOT_REL))?;
            verified.bind_compiler_lane(run)?
        } else {
            run
        }
    };

    let executor = SuiteExecutor {
        adapter,
        classifications,
    };
    let temp = temp_sibling(&request.receipt);
    if let Some(parent) = request
        .receipt
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| io_path(parent, error))?;
    }
    let mut states: BTreeMap<String, usize> = BTreeMap::new();
    let outcome = (|| {
        let file = File::create(&temp).map_err(|error| io_path(&temp, error))?;
        let mut writer = EvidenceWriter::new(BufWriter::new(file), header)?;
        let mut executor = executor;
        for (ordinal, index) in members.iter().enumerate() {
            let obligation = &obligations[*index];
            let lane_request = LaneRequest::new(
                lane_binding.clone(),
                (ordinal + 1) as u64,
                obligation.key.clone(),
                obligation.observables.clone(),
                vec![
                    "bamts-verification::suite::worker".to_owned(),
                    obligation.key.to_string(),
                ],
                WorkingDirectoryPolicy::RepositoryRoot,
                CASE_TIMEOUT_MS,
            )?;
            let process = match executor.run(&lane_request) {
                Ok(process) => process,
                Err(error) => LaneProcessResult {
                    observation: ProcessObservation::Exited { code: 1 },
                    response_body: None,
                    duration_ms: 0,
                    detail: error.to_string(),
                },
            };
            // PASS exists only inside `derive_row`; the suite cannot mint it.
            let row = derive_row(&lane_request, process)?;
            *states.entry(row.state().as_str().to_owned()).or_default() += 1;
            writer.write_row(&row)?;
        }
        writer.finish()?;
        File::open(&temp)
            .map_err(|error| io_path(&temp, error))?
            .sync_all()
            .map_err(|error| io_path(&temp, error))
    })();
    match outcome {
        Ok(()) => {
            fs::rename(&temp, &request.receipt)
                .map_err(|error| io_path(&request.receipt, error))?;
            Ok(SuiteReport {
                catalog: request.catalog.clone(),
                runner: runner.as_str().to_owned(),
                platform: platform.clone(),
                obligations: keys.len(),
                rows: members.len(),
                states,
                obligation_set_digest: shard.obligation_set_digest().to_owned(),
                out: request.receipt.clone(),
                shard: request.shard,
                documents: 0,
            })
        }
        Err(error) => {
            let _ = fs::remove_file(&temp);
            Err(error)
        }
    }
}

/// Merges every shard document below `receipts_root` for the catalog.
///
/// Discovery is bounded and rejects wrong catalog, mixed runner/platform,
/// stale or wrong shard identities, mixed run bindings, and empty receipts.
/// The ordered interleave is delegated to [`merge_shards`], which keeps one
/// live row per shard and rejects missing/extra/duplicate rows.
pub fn merge_suite(root: &Path, request: &SuiteMergeRequest) -> Result<SuiteReport> {
    let catalog = request.catalog.as_str();
    let receipts_root = request.receipts.as_path();
    let out = request.out.as_path();
    let mode = request.publish;
    let _ = allowed_runners(catalog)?;
    let mut paths = Vec::new();
    discover_jsonl(receipts_root, &mut paths)?;
    paths.sort();
    if paths.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Io,
            format!(
                "{}: no `.jsonl` receipts found below the receipts root",
                receipts_root.display()
            ),
        ));
    }

    struct ShardProbe {
        path: PathBuf,
        header: EvidenceHeader,
        first_row: EvidenceRow,
    }

    let mut probes: Vec<ShardProbe> = Vec::new();
    for path in &paths {
        let mut reader = EvidenceReader::open(path)?;
        let Some(first_row) = reader.next_row()? else {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("{}: receipt carries no obligation rows", path.display()),
            ));
        };
        let header = reader.header().clone();
        let _footer = reader.finish()?;
        if first_row.key().catalog() != catalog {
            // A workflow may pass the shared receipts root; only complete,
            // internally valid documents for other catalogs are ignored.
            continue;
        }
        probes.push(ShardProbe {
            path: path.clone(),
            header,
            first_row,
        });
    }
    if probes.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "{}: no receipts for catalog `{catalog}`",
                receipts_root.display()
            ),
        ));
    }

    let modes: BTreeSet<crate::shard::ExecutionMode> = probes
        .iter()
        .map(|probe| probe.first_row.key().mode())
        .collect();
    let platforms: BTreeSet<String> = probes
        .iter()
        .map(|probe| probe.first_row.key().platform().to_owned())
        .collect();
    if modes.len() != 1 || platforms.len() != 1 {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "receipts for catalog `{catalog}` mix runner modes or platforms ({modes:?}, {platforms:?})"
            ),
        ));
    }
    let mode_value = *modes.iter().next().expect("nonempty mode set");
    let platform = platforms.iter().next().expect("nonempty platform set");
    let runner = runner_for_mode(catalog, mode_value).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Schema,
            format!(
                "receipts bind runner mode `{mode_value:?}` for catalog `{catalog}`, which no workflow declares"
            ),
        )
    })?;

    let binding = probes[0].header.binding().clone();
    for probe in &probes[1..] {
        if binding != *probe.header.binding() {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                format!(
                    "{}: run binding differs from sibling shard receipts (mixed authority, candidate, or harness digests)",
                    probe.path.display()
                ),
            ));
        }
    }

    let manifest = load_catalog_manifest(root, catalog)?;
    let obligations = materialize_obligations(catalog, &manifest.identifiers, runner, platform)?;
    let _classifications =
        load_obligation_classifications(root, catalog, &manifest.identifiers, &obligations)?;
    let current_binding = current_run_binding(root, catalog)?;
    if binding != current_binding {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            "shard receipts are stale for the current authority, candidate, or harness binding",
        ));
    }
    let keys: Vec<ObligationKey> = obligations.iter().map(|entry| entry.key.clone()).collect();
    let mut shard_count = None;
    let mut shard_indices = BTreeSet::new();
    for probe in &probes {
        let spec = probe.header.shard().spec();
        match shard_count {
            None => shard_count = Some(spec.count()),
            Some(count) if count != spec.count() => {
                return Err(VerificationError::new(
                    ErrorCode::SetMismatch,
                    "shard receipts do not share one matrix count",
                ));
            }
            Some(_) => {}
        }
        if !shard_indices.insert(spec.index()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate shard index {}", spec.index()),
            ));
        }
        let expected = ShardIdentity::plan(spec, &keys)?;
        if expected != *probe.header.shard() {
            return Err(VerificationError::new(
                ErrorCode::SetMismatch,
                format!(
                    "{}: shard identity is stale or foreign to the current catalog `{catalog}`",
                    probe.path.display()
                ),
            ));
        }
    }
    let count = shard_count.expect("nonempty probes have a count");
    if probes.len() != count as usize || shard_indices.len() != count as usize {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            "merge requires every shard index exactly once",
        ));
    }

    let shard_paths: Vec<PathBuf> = probes.iter().map(|probe| probe.path.clone()).collect();
    merge_shards(&shard_paths, &keys, out, mode)?;

    // Bounded closure proof: the published image streams again and its
    // footer must account for exactly the canonical catalog.
    let mut reader = EvidenceReader::open(out)?;
    let mut states: BTreeMap<String, usize> = BTreeMap::new();
    while let Some(row) = reader.next_row()? {
        *states.entry(row.state().as_str().to_owned()).or_default() += 1;
    }
    let footer = reader.finish()?;
    if footer.row_count() != keys.len() {
        return Err(VerificationError::new(
            ErrorCode::SetMismatch,
            format!(
                "merged receipt records {} rows for a catalog of {}",
                footer.row_count(),
                keys.len()
            ),
        ));
    }
    Ok(SuiteReport {
        catalog: catalog.to_owned(),
        runner: runner.as_str().to_owned(),
        platform: platform.clone(),
        obligations: keys.len(),
        rows: footer.row_count(),
        states,
        obligation_set_digest: crate::shard::digest_obligation_set(keys.iter()),
        out: out.to_path_buf(),
        shard: ShardSpec::unsharded(),
        documents: shard_paths.len(),
    })
}

/// Authority directories under `target/authority` that this catalog reads.
fn authority_dirs(catalog: &str) -> &'static [&'static str] {
    match catalog {
        "typescript-7.0.2" => &["typescript-7.0.2", "typescript-7.0.2-tests"],
        "typescript-6.0.2" => &["typescript-6.0.2-tests"],
        "typescript-5.9.3" => &["typescript-5.9.3-tests"],
        "test262" => &["test262"],
        _ => &[],
    }
}

#[derive(Debug, Deserialize)]
struct SourceMarker {
    name: String,
    tree_digest: String,
}

/// Binds the locked authority materialization and classification policy.
fn authority_digest(root: &Path, catalog: &str) -> Result<String> {
    let dirs = authority_dirs(catalog);
    let mut records: Vec<(String, String)> = Vec::with_capacity(dirs.len());
    for dir in dirs {
        let marker_path = root
            .join("target")
            .join("authority")
            .join(dir)
            .join(".bamti-source.json");
        let bytes = schema::read_bytes(&marker_path).map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolMissing,
                format!(
                    "authority `{dir}` is not materialized under target/authority ({error}); run `source fetch {dir} --dest target/authority/{dir}` first"
                ),
            )
        })?;
        let marker: SourceMarker = serde_json::from_slice(&bytes).map_err(|error| {
            VerificationError::new(
                ErrorCode::Json,
                format!("{}: invalid source marker: {error}", marker_path.display()),
            )
        })?;
        records.push((marker.name, marker.tree_digest));
    }
    records.sort();
    let mut hasher = Sha256::new();
    for (name, tree_digest) in records {
        hasher.update(name.as_bytes());
        hasher.update([0]);
        hasher.update(tree_digest.as_bytes());
        hasher.update([0x0a]);
    }
    let policy = root
        .join(schema::CLASSIFICATION_DIR)
        .join(format!("{catalog}.toml"));
    hasher.update(b"classification\x00");
    if policy.exists() {
        hasher.update(file_sha256(&policy)?.as_bytes());
    } else {
        hasher.update(schema::sha256_hex(b"").as_bytes());
    }
    hasher.update([0x0a]);
    Ok(schema::sha256_hex(&hasher.finalize()))
}

/// SHA-256 of one file, streamed in 64 KiB chunks.
fn file_sha256(path: &Path) -> Result<String> {
    use std::io::BufReader;
    let file = File::open(path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })?;
    let mut reader = BufReader::with_capacity(64 * 1024, file);
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 64 * 1024];
    loop {
        let read = std::io::Read::read(&mut reader, &mut buffer).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(schema::sha256_hex(&hasher.finalize()))
}

/// Bounded runtime for host-identity probes.
const PROBE_TIMEOUT: Duration = Duration::from_secs(10);

/// Candidate tree identity for a committed tree: a versioned projection of
/// committed source, not the raw tree hash.
///
/// The digest is `sha256("bamti-candidate-source/v1\0" + stream)`. The stream
/// is the deterministic, byte-sorted sequence of every committed Git tree
/// entry of the resolved `HEAD` tree except exact generated run outputs:
/// `proof/completeness-ledger.json` and the immediate regular-file `.jsonl`
/// children of the canonical receipt-set directories declared by
/// [`crate::rebuild::RECEIPT_SET_DIRS`]. Each retained entry contributes its
/// mode, object type, object ID, and exact path bytes, so executable bits,
/// symlink targets, submodules, and path names stay bound; parent tree IDs
/// are never hashed, so a receipt-only landing commit that only rewrites
/// generated leaves leaves this digest unchanged.
///
/// Generated outputs are excluded only as regular blob files. A symlink or
/// submodule standing at an output path is retained and therefore cannot use
/// that location to hide source; nested files, sibling directories, and
/// suffix or case lookalikes were never outputs to begin with.
///
/// A v2 receipt is only valid for a clean committed tree. The dirty gate
/// mirrors the identical path policy over
/// `git status --porcelain=v1 -z --untracked-files=all`: modification,
/// staging, deletion, addition, type change, conflict, and untracked entries
/// at source paths are refused, a rename or copy crossing the source/output
/// boundary is refused on either end, an unmerged record is refused even at
/// an output name, and an untracked entry at an output path is permitted only
/// as a regular file. Deletion or modification of a generated output never
/// dirties the tree. Truncated or malformed Git output is refused; no digest
/// is ever produced from partial records. Git runs through the pinned
/// process boundary, so a user's global gitconfig — especially
/// `core.excludesfile` — cannot silently hide untracked content.
///
/// The capture is an atomic snapshot of one committed tree. The git probes
/// are separate processes, so after the gate completes `HEAD` is resolved a
/// second time and a capture that observed `HEAD` move between resolution
/// and completion is refused, never digested: the dirty gate and the hashed
/// enumeration always describe the same commit.
/// Two captures of the same committed tree always produce the same digest.
/// The namespace version makes receipts captured by the former full-tree
/// algorithm (`git-tree\0` prefix) permanently stale at merge/admission; old
/// receipts require genuine reruns and must never be rewritten to fit.
fn candidate_tree_digest(root: &Path) -> Result<String> {
    let tree = resolve_head_tree(root)?;
    candidate_tree_digest_against(root, &tree)
}

/// Projects one committed tree, already resolved from `HEAD`, through the
/// dirty gate and the digest, and refuses unless `HEAD` still resolves to
/// that same tree once the gate completes. Split from
/// [`candidate_tree_digest`] so tests can replay a capture whose tree was
/// displaced mid-flight.
fn candidate_tree_digest_against(root: &Path, tree: &str) -> Result<String> {
    let status = git_probe(
        root,
        &[
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--ignore-submodules=none",
        ],
    )?;
    let listing = git_probe_bounded(
        root,
        &["ls-tree", "-r", "-z", "--full-tree", tree],
        TREE_PROBE_OUTPUT_BYTES,
    )?;
    let records = parse_tree_records(&listing)?;
    refuse_dirty_source(root, &status, &records)?;
    let settled = resolve_head_tree(root)?;
    if settled != tree {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!(
                "the candidate snapshot is not coherent; `HEAD` moved from tree {tree} to {settled} during the capture"
            ),
        ));
    }
    let mut hasher = Sha256::new();
    hasher.update(CANDIDATE_SOURCE_NAMESPACE);
    hasher.update(b"\x00");
    hasher.update(committed_source_stream(&records));
    Ok(schema::sha256_hex(&hasher.finalize()))
}

/// Domain separator of the committed-source projection algorithm. A change
/// to the exclusion policy or to the stream encoding must bump the version.
const CANDIDATE_SOURCE_NAMESPACE: &[u8] = b"bamti-candidate-source/v1";

/// Bounded window for the recursive committed-tree enumeration. The 64-KiB
/// probe window would silently truncate the `ls-tree` listing of any
/// real-world repository, and a truncated enumeration must never feed the
/// digest, so the tree probe uses an explicitly justified larger window:
/// a full recursive listing of a large monorepo stays in the low megabytes,
/// and the boundary still fails closed through `stdout_truncated`.
const TREE_PROBE_OUTPUT_BYTES: usize = 64 << 20;

/// Runs `git` through the bounded corpus process boundary with the default
/// 64-KiB probe window.
fn git_probe(root: &Path, args: &[&str]) -> Result<Vec<u8>> {
    git_probe_bounded(root, args, PROBE_OUTPUT_BYTES)
}

/// Runs `git` through the bounded corpus process boundary, pinned
/// environment included, and refuses any output that outgrew its window: a
/// truncated prefix is a non-answer, never a digest input.
fn git_probe_bounded(root: &Path, args: &[&str], max_output_bytes: usize) -> Result<Vec<u8>> {
    use crate::oracles::{self, ProcessBoundary};
    let invocation = oracles::ProcessInvocation {
        program: PathBuf::from("git"),
        argv: args.iter().map(|arg| (*arg).into()).collect(),
        cwd: root.to_path_buf(),
        environment: oracles::pinned_environment(),
        limits: crate::corpus::OracleLimits {
            timeout: PROBE_TIMEOUT,
            max_output_bytes,
        },
    };
    let outcome = oracles::CorpusProcessBoundary
        .invoke(&invocation)
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("git probe `git {}` failed: {error}", args.join(" ")),
            )
        })?;
    if outcome.stdout_truncated {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "git probe `git {}` output exceeded the bounded {max_output_bytes}-byte window",
                args.join(" ")
            ),
        ));
    }
    if outcome.exit_code != Some(0) {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!(
                "git probe `git {}` exited {:?}",
                args.join(" "),
                outcome.exit_code
            ),
        ));
    }
    Ok(outcome.stdout)
}

/// Resolves `HEAD` once to its committed tree ID. An unborn `HEAD`, a
/// malformed object ID, or a failed resolution is a refusal, never an empty
/// projection.
fn resolve_head_tree(root: &Path) -> Result<String> {
    let tree_bytes = git_probe(root, &["rev-parse", "HEAD^{tree}"])?;
    let tree = String::from_utf8_lossy(&tree_bytes).trim().to_owned();
    if !matches!(tree.len(), 40 | 64)
        || !tree
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err(VerificationError::new(
            ErrorCode::Digest,
            format!("git reported a malformed tree digest `{tree}`"),
        ));
    }
    Ok(tree)
}

/// One committed Git tree entry as `git ls-tree -r -z` enumerates it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TreeRecord {
    mode: String,
    kind: String,
    object: String,
    path: Vec<u8>,
}

/// Parses the raw `-z` listing. `mode SP kind SP object TAB path NUL` per
/// record; paths are raw bytes and may contain any byte except NUL. Every
/// deviation — a missing tab, an unknown mode or kind, a malformed object ID,
/// an unterminated record — is a refusal, so a truncated or corrupted
/// listing can never contribute a partial projection.
fn parse_tree_records(listing: &[u8]) -> Result<Vec<TreeRecord>> {
    let malformed = |detail: String| {
        VerificationError::new(
            ErrorCode::ToolFailed,
            format!("git ls-tree enumeration is malformed: {detail}"),
        )
    };
    let mut records = Vec::new();
    let mut rest = listing;
    while !rest.is_empty() {
        let Some(tab) = rest.iter().position(|byte| *byte == b'\t') else {
            return Err(malformed("record has no path separator".to_owned()));
        };
        let meta = std::str::from_utf8(&rest[..tab])
            .map_err(|_| malformed("record metadata is not UTF-8".to_owned()))?;
        let mut fields = meta.split(' ');
        let (mode, kind, object) =
            match (fields.next(), fields.next(), fields.next(), fields.next()) {
                (Some(mode), Some(kind), Some(object), None) => (mode, kind, object),
                _ => {
                    return Err(malformed(format!(
                        "record metadata `{meta}` is not three fields"
                    )));
                }
            };
        if !matches!(
            (mode, kind),
            ("100644" | "100755" | "120000", "blob") | ("160000", "commit")
        ) {
            return Err(malformed(format!("invalid mode/type pair `{mode} {kind}`")));
        }
        if !matches!(object.len(), 40 | 64)
            || !object
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
        {
            return Err(malformed(format!("record object `{object}` is malformed")));
        }
        let path_bytes = &rest[tab + 1..];
        let Some(nul) = path_bytes.iter().position(|byte| *byte == b'\0') else {
            return Err(malformed("record path is not NUL-terminated".to_owned()));
        };
        if nul == 0 {
            return Err(malformed("record path is empty".to_owned()));
        }
        records.push(TreeRecord {
            mode: mode.to_owned(),
            kind: kind.to_owned(),
            object: object.to_owned(),
            path: path_bytes[..nul].to_vec(),
        });
        rest = &path_bytes[nul + 1..];
    }
    Ok(records)
}

/// Encodes the deterministic committed-source stream: every record except
/// exact generated run outputs, sorted by exact path bytes (then mode and
/// object for a total order), each contributing
/// `mode SP kind SP object TAB path NUL`. Exclusion applies only to regular
/// blobs; a symlink or submodule at an output path stays in the stream.
fn committed_source_stream(records: &[TreeRecord]) -> Vec<u8> {
    let mut retained: Vec<&TreeRecord> = records
        .iter()
        .filter(|record| {
            !(record.kind == "blob"
                && matches!(record.mode.as_str(), "100644" | "100755")
                && crate::rebuild::is_generated_run_output(&record.path))
        })
        .collect();
    retained.sort_by(|left, right| {
        (&left.path, &left.mode, &left.object).cmp(&(&right.path, &right.mode, &right.object))
    });
    let mut stream = Vec::new();
    for record in retained {
        stream.extend_from_slice(record.mode.as_bytes());
        stream.push(b' ');
        stream.extend_from_slice(record.kind.as_bytes());
        stream.push(b' ');
        stream.extend_from_slice(record.object.as_bytes());
        stream.push(b'\t');
        stream.extend_from_slice(&record.path);
        stream.push(b'\0');
    }
    stream
}

/// One `git status --porcelain=v1 -z` record: the XY state pair plus one
/// raw path (and the original path of a rename or copy).
#[derive(Debug, Clone, PartialEq, Eq)]
struct StatusRecord {
    index_state: u8,
    worktree_state: u8,
    path: Vec<u8>,
    orig_path: Option<Vec<u8>>,
}

impl StatusRecord {
    /// The closed unmerged vocabulary. `DD` (both deleted) and `AA`
    /// (both added) carry no `U`, so they are matched explicitly.
    fn is_unmerged(&self) -> bool {
        matches!(
            (self.index_state, self.worktree_state),
            (b'D', b'D') | (b'A', b'A')
        ) || self.index_state == b'U'
            || self.worktree_state == b'U'
    }

    /// Whether the record takes the path out of the worktree, in which case
    /// no worktree file kind can be observed.
    fn removes_from_worktree(&self) -> bool {
        self.index_state == b'D' || self.worktree_state == b'D'
    }
}

/// Parses the raw `-z` status: `XY SP path NUL` per record, and rename/copy
/// records carry the original path as one further NUL-delimited field. Any
/// deviation — a short record, a missing state separator, an empty path, a
/// record that is not NUL-terminated — is a refusal.
fn parse_status_records(status: &[u8]) -> Result<Vec<StatusRecord>> {
    let malformed = |detail: String| {
        VerificationError::new(
            ErrorCode::ToolFailed,
            format!("git status enumeration is malformed: {detail}"),
        )
    };
    let mut records = Vec::new();
    let mut rest = status;
    while !rest.is_empty() {
        if rest.len() < 4 || rest[2] != b' ' {
            return Err(malformed("record is shorter than `XY SP path`".to_owned()));
        }
        let (index_state, worktree_state) = (rest[0], rest[1]);
        if !matches!(
            index_state,
            b' ' | b'M' | b'T' | b'A' | b'D' | b'R' | b'C' | b'U' | b'?'
        ) || !matches!(
            worktree_state,
            b' ' | b'M' | b'T' | b'A' | b'D' | b'R' | b'C' | b'U' | b'?'
        ) || ((index_state == b'?') != (worktree_state == b'?'))
            || (index_state == b' ' && worktree_state == b' ')
        {
            return Err(malformed("invalid status state pair".to_owned()));
        }
        let path_bytes = &rest[3..];
        let Some(nul) = path_bytes.iter().position(|byte| *byte == b'\0') else {
            return Err(malformed("record path is not NUL-terminated".to_owned()));
        };
        let path = path_bytes[..nul].to_vec();
        rest = &path_bytes[nul + 1..];
        let orig_path =
            if matches!(index_state, b'R' | b'C') || matches!(worktree_state, b'R' | b'C') {
                let Some(nul) = rest.iter().position(|byte| *byte == b'\0') else {
                    return Err(malformed("rename record has no original path".to_owned()));
                };
                let orig_path = rest[..nul].to_vec();
                rest = &rest[nul + 1..];
                if orig_path.is_empty() {
                    return Err(malformed(
                        "rename record has an empty original path".to_owned(),
                    ));
                }
                Some(orig_path)
            } else {
                None
            };
        if path.is_empty() {
            return Err(malformed("record path is empty".to_owned()));
        }
        records.push(StatusRecord {
            index_state,
            worktree_state,
            path,
            orig_path,
        });
    }
    Ok(records)
}

/// Addresses one raw Git path against the repository root. On Unix the bytes
/// pass through exactly.
#[cfg(unix)]
fn worktree_path(root: &Path, path: &[u8]) -> Result<PathBuf> {
    use std::os::unix::ffi::OsStrExt;
    Ok(root.join(std::ffi::OsStr::from_bytes(path)))
}

#[cfg(not(unix))]
fn worktree_path(root: &Path, path: &[u8]) -> Result<PathBuf> {
    let text = std::str::from_utf8(path).map_err(|_| {
        VerificationError::new(
            ErrorCode::Schema,
            "non-UTF-8 Git path cannot be addressed on this platform",
        )
    })?;
    Ok(root.join(text))
}

/// Whether the worktree entry at one raw Git path is a regular file. Symlink
/// metadata is used so a symlink standing at an output path is never
/// mistaken for the generated file it names.
fn worktree_file_is_regular(root: &Path, path: &[u8]) -> Result<bool> {
    let addressed = worktree_path(root, path)?;
    Ok(fs::symlink_metadata(&addressed).is_ok_and(|meta| meta.is_file()))
}

fn dirty_source(detail: String) -> VerificationError {
    VerificationError::new(
        ErrorCode::Schema,
        format!("candidate tree is dirty; a v2 receipt requires a clean committed tree: {detail}"),
    )
}

/// The dirty gate. Mirrors the exact generated-output policy of the
/// committed-source projection: every status record must name only generated
/// run outputs, unmerged records are refused even at output names, a rename
/// or copy is refused when either end leaves the output boundary, and an
/// untracked or modified output is tolerated only while the worktree entry
/// is a regular file. Existing HEAD and index entries must also be regular:
/// deleting or replacing a source-bound symlink is still a source change.
fn refuse_dirty_source(root: &Path, status: &[u8], committed: &[TreeRecord]) -> Result<()> {
    let changes = parse_status_records(status)?;
    if changes.is_empty() {
        return Ok(());
    }
    let index = git_probe_bounded(
        root,
        &["ls-files", "--stage", "-z"],
        TREE_PROBE_OUTPUT_BYTES,
    )?;
    let mut index_modes = BTreeMap::new();
    for entry in index
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
    {
        let Some((metadata, path)) = entry
            .iter()
            .position(|byte| *byte == b'\t')
            .map(|tab| entry.split_at(tab))
        else {
            return Err(dirty_source("malformed index enumeration".to_owned()));
        };
        let fields: Vec<_> = metadata.split(|byte| *byte == b' ').collect();
        if fields.len() != 3 || fields.last().copied() != Some(b"0".as_slice()) {
            return Err(dirty_source("unmerged or malformed index".to_owned()));
        }
        let mode = fields.first().copied().unwrap_or_default();
        index_modes.insert(path.strip_prefix(b"\t").unwrap_or_default(), mode);
    }
    if !index.is_empty() && !index.ends_with(b"\0") {
        return Err(dirty_source("truncated index enumeration".to_owned()));
    }
    let committed_modes: BTreeMap<_, _> = committed
        .iter()
        .map(|entry| (entry.path.as_slice(), entry.mode.as_bytes()))
        .collect();
    for record in changes {
        if record.is_unmerged() {
            return Err(dirty_source(format!(
                "unmerged index record at `{}`",
                String::from_utf8_lossy(&record.path)
            )));
        }
        let mut paths: Vec<&[u8]> = vec![&record.path];
        if let Some(orig_path) = &record.orig_path {
            paths.push(orig_path);
        }
        for path in paths {
            if !crate::rebuild::is_generated_run_output(path) {
                return Err(dirty_source(format!(
                    "`{}` is candidate source, not a generated run output",
                    String::from_utf8_lossy(path)
                )));
            }
            for modes in [&committed_modes, &index_modes] {
                if modes
                    .get(path)
                    .is_some_and(|mode| !matches!(*mode, b"100644" | b"100755"))
                {
                    return Err(dirty_source(
                        "generated path has a source-bound file kind".to_owned(),
                    ));
                }
            }
        }
        // Even a staged deletion may have been recreated in the worktree.
        // A recreated symlink or directory must not inherit the deletion exemption.
        if (!record.removes_from_worktree()
            || worktree_path(root, &record.path)?
                .symlink_metadata()
                .is_ok())
            && !worktree_file_is_regular(root, &record.path)?
        {
            return Err(dirty_source(format!(
                "`{}` stands at a generated output path but is not a regular file",
                String::from_utf8_lossy(&record.path)
            )));
        }
    }
    Ok(())
}

/// Toolchain pin: the `rustc` version string and the SHA-256 of
/// `rust-toolchain.toml` at the repository root.
fn toolchain_pin(root: &Path) -> Result<ToolchainPin> {
    let rustc_version = rustc_version_string()?;
    let toml_path = root.join("rust-toolchain.toml");
    let toml_digest = file_sha256(&toml_path)?;
    ToolchainPin::new(rustc_version, toml_digest)
}

/// Returns the `rustc --version` output as a trimmed string with spaces
/// replaced by hyphens, so it is a valid token for [`ToolchainPin`].
fn rustc_version_string() -> Result<String> {
    let output = std::process::Command::new("rustc")
        .arg("--version")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .map_err(|error| {
            VerificationError::new(
                ErrorCode::ToolFailed,
                format!("rustc --version probe failed: {error}"),
            )
        })?;
    if !output.status.success() {
        return Err(VerificationError::new(
            ErrorCode::ToolFailed,
            format!("rustc --version exited {}", output.status),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .trim()
        .replace(' ', "-"))
}

/// Cached harness binary path and SHA-256 digest.  The executing binary
/// does not change during one process lifetime, so the expensive
/// `file_sha256` of a potentially multi-hundred-MB test binary is computed
/// at most once per process and reused by every `current_run_binding` call.
static HARNESS_EXE: LazyLock<Result<(PathBuf, String), VerificationError>> = LazyLock::new(|| {
    let exe = std::env::current_exe().map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("cannot resolve the harness binary: {error}"),
        )
    })?;
    let digest = file_sha256(&exe)?;
    Ok((exe, digest))
});

/// Returns the harness binary path and its SHA-256 digest, computing and
/// caching them on the first call.
fn harness_exe_digest() -> Result<&'static (PathBuf, String)> {
    HARNESS_EXE.as_ref().map_err(VerificationError::clone)
}

#[derive(Debug)]
struct RunSnapshot {
    candidate_tree_digest: String,
    /// Path of the harness binary (`std::env::current_exe`), kept so
    /// `binding_from_snapshot` can skip re-hashing when the candidate
    /// binary is the harness itself.
    harness_path: PathBuf,
    harness_digest: String,
}

fn current_run_snapshot(root: &Path) -> Result<RunSnapshot> {
    let candidate_tree_digest = candidate_tree_digest(root)?;
    let (harness_path, harness_digest) = harness_exe_digest()?;
    Ok(RunSnapshot {
        candidate_tree_digest,
        harness_path: harness_path.clone(),
        harness_digest: harness_digest.clone(),
    })
}

/// The binary that executes one catalog's obligations. An in-process runner
/// executes inside this harness, so the harness names itself. An
/// out-of-process runner executes inside its lane worker, and the receipt has
/// to content-address that worker: hashing the harness instead would name a
/// binary that did no measuring, so a changed worker under an unchanged
/// harness would leave stale receipts verifying.
///
/// A catalog whose runners resolve to different workers has no single
/// executing binary, so this refuses rather than silently choosing one. A
/// catalog with no declared runners can name no worker, so the harness stands;
/// an unrecognized catalog is rejected downstream, where the receipt is read.
fn candidate_binary(root: &Path, catalog: &str) -> Result<PathBuf> {
    let programs: BTreeSet<PathBuf> = allowed_runners(catalog)
        .unwrap_or(&[])
        .iter()
        .filter_map(|runner| lane_program(root, *runner))
        .collect();
    select_candidate_binary(catalog, programs)
}

/// Chooses the one executing binary from a catalog's resolved lane workers.
/// Separated from environment lookup so the rule itself is directly testable.
fn select_candidate_binary(catalog: &str, programs: BTreeSet<PathBuf>) -> Result<PathBuf> {
    let mut programs = programs.into_iter();
    let Some(program) = programs.next() else {
        let (exe, _) = harness_exe_digest()?;
        return Ok(exe.clone());
    };
    if let Some(second) = programs.next() {
        return Err(VerificationError::new(
            ErrorCode::Usage,
            format!(
                "catalog `{catalog}` resolves two lane workers, `{}` and `{}`, so no single binary executes it",
                program.display(),
                second.display()
            ),
        ));
    }
    Ok(program)
}

fn binding_from_snapshot(root: &Path, catalog: &str, snapshot: &RunSnapshot) -> Result<RunBinding> {
    let candidate = candidate_binary(root, catalog)?;
    // When the candidate binary is the harness itself (the in-process
    // runner case), reuse the already-computed digest instead of hashing
    // the same multi-hundred-MB file a second time.
    let candidate_digest = if candidate == snapshot.harness_path {
        snapshot.harness_digest.clone()
    } else {
        file_sha256(&candidate)?
    };
    RunBinding::new(
        authority_digest(root, catalog)?,
        snapshot.candidate_tree_digest.clone(),
        candidate_digest,
        snapshot.harness_digest.clone(),
        toolchain_pin(root)?,
    )
}

/// The four digests + normalized environment the header binds.
pub fn current_run_binding(root: &Path, catalog: &str) -> Result<RunBinding> {
    binding_from_snapshot(root, catalog, &current_run_snapshot(root)?)
}

/// Current bindings for every catalog, sharing one exact run snapshot.
pub fn current_run_bindings(
    root: &Path,
    catalogs: &BTreeSet<String>,
) -> Result<BTreeMap<String, RunBinding>> {
    let snapshot = current_run_snapshot(root)?;
    catalogs
        .iter()
        .map(|catalog| {
            binding_from_snapshot(root, catalog, &snapshot)
                .map(|binding| (catalog.clone(), binding))
        })
        .collect()
}

/// Destination-sibling temp path used before the atomic rename.
fn temp_sibling(dest: &Path) -> PathBuf {
    let mut name = dest
        .file_name()
        .map(|name| name.to_os_string())
        .unwrap_or_else(|| "receipt".into());
    name.push(format!(".tmp-{}", std::process::id()));
    dest.with_file_name(name)
}

fn io_path(path: &Path, error: std::io::Error) -> VerificationError {
    VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
}

/// Collects `.jsonl` files below `root`, recursively, deterministic order.
fn discover_jsonl(root: &Path, found: &mut Vec<PathBuf>) -> Result<()> {
    let entries = fs::read_dir(root).map_err(|error| io_path(root, error))?;
    let mut entries = entries
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(|error| io_path(root, error))?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| io_path(&path, error))?;
        if file_type.is_dir() {
            discover_jsonl(&path, found)?;
        } else if file_type.is_file()
            && path
                .extension()
                .is_some_and(|extension| extension == "jsonl")
        {
            found.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ExecutionMode;

    struct Scratch {
        root: PathBuf,
    }

    impl Scratch {
        fn new(label: &str) -> Self {
            static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let root = std::env::temp_dir().join(format!(
                "bamts-suite-test-{}-{label}-{}",
                std::process::id(),
                COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
            fs::create_dir_all(&root).expect("scratch root");
            Self { root }
        }

        fn write(&self, relative: &str, bytes: &[u8]) -> PathBuf {
            let path = self.root.join(relative);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("scratch parent");
            }
            fs::write(&path, bytes).expect("scratch write");
            path
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn hex(byte: u8) -> String {
        std::iter::repeat_n(char::from_digit(byte as u32, 16).expect("hex digit"), 64).collect()
    }

    fn manifest_bytes(
        identifiers: &[&str],
        source_ledger: &str,
        identifiers_sha256: &str,
    ) -> Vec<u8> {
        let mut sorted: Vec<String> = identifiers
            .iter()
            .map(|entry| (*entry).to_owned())
            .collect();
        sorted.sort();
        let list = sorted
            .iter()
            .map(|entry| format!("\"{entry}\""))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "{{\"schema\": \"{MANIFEST_SCHEMA}\", \"source_ledger_sha256\": \"{source_ledger}\", \
             \"catalogs\": [{{\"extractor\": {{}}, \"id\": \"benchmarks\", \
             \"identifier_count\": {}, \"identifiers\": [{}], \
             \"identifiers_sha256\": \"{}\", \
             \"source\": {{\"pin\": \"p\", \"url\": \"u\", \"digest_algorithm\": \"sha256\", \
             \"digest\": \"{}\"}}}}]}}",
            sorted.len(),
            list,
            identifiers_sha256,
            hex(3)
        )
        .into_bytes()
    }

    fn manifest_root(label: &str, identifiers: &[&str]) -> (Scratch, Vec<String>) {
        let scratch = Scratch::new(label);
        let sources = b"[[source]]\n";
        let source_ledger = schema::sha256_hex(sources);
        let mut sorted: Vec<String> = identifiers
            .iter()
            .map(|entry| (*entry).to_owned())
            .collect();
        sorted.sort();
        let digest = schema::identifiers_sha256(&sorted);
        scratch.write("vendor/sources.toml", sources);
        scratch.write(
            "verification/manifest.lock.json",
            &manifest_bytes(identifiers, &source_ledger, &digest),
        );
        scratch.write(
            "rust-toolchain.toml",
            b"[toolchain]\nchannel = \"1.97.1\"\n",
        );
        scratch.write(
            ".gitignore",
            b"receipts/\npartial/\nstale/\nextra/\nwrong-mode/\ntwo/\nduplicate/\n*.jsonl\nout*.jsonl\n",
        );
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        run_git(&["init", "-q"]);
        run_git(&["add", "."]);
        run_git(&[
            "-c",
            "user.name=bamts-suite-test",
            "-c",
            "user.email=suite@example.invalid",
            "commit",
            "-qm",
            "fixture",
        ]);
        (scratch, sorted)
    }

    #[test]
    fn current_run_bindings_scope_authority_but_share_run_identity() {
        let (scratch, _) = manifest_root("binding-map", &["jit.a"]);
        scratch.write(
            "verification/classification/catalog-a.toml",
            b"catalog = \"a\"\n",
        );
        scratch.write(
            "verification/classification/catalog-b.toml",
            b"catalog = \"b\"\n",
        );
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        run_git(&["add", "."]);
        run_git(&[
            "-c",
            "user.name=bamts-suite-test",
            "-c",
            "user.email=suite@example.invalid",
            "commit",
            "-qm",
            "classification fixtures",
        ]);
        let catalogs = BTreeSet::from(["catalog-b".to_owned(), "catalog-a".to_owned()]);

        let bindings = current_run_bindings(&scratch.root, &catalogs).expect("bindings");
        assert_eq!(
            bindings.keys().map(String::as_str).collect::<Vec<_>>(),
            ["catalog-a", "catalog-b"]
        );
        let first = &bindings["catalog-a"];
        let second = &bindings["catalog-b"];
        assert_ne!(first.authority_digest(), second.authority_digest());
        assert!(first.same_run_as(second));
    }

    /// A receipt has to content-address the binary that measured it. Hashing
    /// the harness for both digests -- the prior behavior -- meant a lane
    /// worker could change under an unchanged harness while stale receipts
    /// kept verifying. `RunSnapshot` now carries no candidate field at all,
    /// so that reuse is unrepresentable; these cover the selection rule.
    #[test]
    fn an_external_lane_worker_names_itself_as_the_candidate_binary() {
        let worker = PathBuf::from("/nonexistent/lane-worker");
        let chosen = select_candidate_binary("formal-redex", BTreeSet::from([worker.clone()]))
            .expect("one worker selects");
        assert_eq!(chosen, worker);

        let harness = select_candidate_binary("benchmarks", BTreeSet::new())
            .expect("no worker falls back to the harness");
        assert_eq!(
            harness,
            std::env::current_exe().expect("current exe"),
            "a catalog with no lane worker runs in process, so the harness names itself"
        );
        assert_ne!(chosen, harness);
    }

    #[test]
    fn a_catalog_resolving_two_lane_workers_is_refused() {
        let error = select_candidate_binary(
            "test262",
            BTreeSet::from([PathBuf::from("/one"), PathBuf::from("/two")]),
        )
        .expect_err("two workers cannot both have measured one catalog");
        assert_eq!(error.code(), ErrorCode::Usage);
        assert!(
            error.to_string().contains("no single binary executes it"),
            "unexpected message: {error}"
        );
    }

    /// The adapter variable name is part of the operator contract: it appears
    /// in workflow environments, the release gate, and the typed message a
    /// missing adapter records into a receipt. Renaming a runner silently
    /// renames the variable, so pin both spellings a workflow relies on.
    #[test]
    fn each_runner_names_its_own_adapter_variable() {
        assert_eq!(
            lane_adapter_variable(SuiteRunner::Compiler),
            "BAMTS_SUITE_COMPILER_ADAPTER"
        );
        assert_eq!(
            lane_adapter_variable(SuiteRunner::Redex),
            "BAMTS_SUITE_REDEX_ADAPTER"
        );
        assert_eq!(
            lane_adapter_variable(SuiteRunner::Interpreter),
            "BAMTS_SUITE_INTERPRETER_ADAPTER"
        );
    }

    #[test]
    fn tracked_deletions_bind_status_and_path_without_file_bytes() {
        for (label, staged, expected_status) in [
            ("worktree-deletion", false, b" D tracked.txt\0"),
            ("index-deletion", true, b"D  tracked.txt\0"),
        ] {
            let (scratch, _) = manifest_root(label, &["jit.a"]);
            let tracked = scratch.write("tracked.txt", b"tracked bytes");
            let run_git = |args: &[&str]| {
                let status = std::process::Command::new("git")
                    .args(args)
                    .current_dir(&scratch.root)
                    .status()
                    .expect("run git");
                assert!(status.success(), "git {args:?}");
            };
            run_git(&["add", "tracked.txt"]);
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                "tracked deletion fixture",
            ]);
            let _ = candidate_tree_digest(&scratch.root).expect("clean candidate digest");

            if staged {
                run_git(&["rm", "-q", "tracked.txt"]);
            } else {
                fs::remove_file(&tracked).expect("delete tracked file");
            }
            assert!(!tracked.exists(), "deleted path must have no bytes to hash");
            let status = git_probe(
                &scratch.root,
                &["status", "--porcelain=v1", "-z", "--untracked-files=all"],
            )
            .expect("deletion status");
            assert_eq!(status, expected_status.as_slice());

            let error =
                candidate_tree_digest(&scratch.root).expect_err("dirty tree must be rejected");
            assert_eq!(error.code(), ErrorCode::Schema);
        }
    }

    #[test]
    fn embedded_git_directory_contributes_status_without_file_bytes() {
        let (scratch, _) = manifest_root("embedded-git", &["jit.a"]);
        let _ = candidate_tree_digest(&scratch.root).expect("clean candidate digest");
        let embedded = scratch.root.join(".references/bun");
        fs::create_dir_all(&embedded).expect("create embedded repository");
        let status = std::process::Command::new("git")
            .args(["init", "-q"])
            .current_dir(&embedded)
            .status()
            .expect("initialize embedded repository");
        assert!(status.success());

        let status = git_probe(
            &scratch.root,
            &["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        )
        .expect("embedded repository status");
        assert!(String::from_utf8_lossy(&status).contains(".references/bun/"));

        let error = candidate_tree_digest(&scratch.root)
            .expect_err("dirty tree with embedded git must be rejected");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    #[test]
    fn manifest_identity_parsing_is_strict() {
        let (scratch, sorted) = manifest_root("identity", &["jit.c", "jit.a", "jit.b"]);
        let loaded = load_catalog_manifest(&scratch.root, "benchmarks").expect("loads");
        assert_eq!(loaded.catalog, "benchmarks");
        assert_eq!(loaded.identifiers, sorted);
        assert_eq!(
            loaded.identifiers_sha256,
            schema::identifiers_sha256(&sorted)
        );
        assert_eq!(loaded.manifest_sha256.len(), 64);

        // Sources-ledger drift is rejected as stale, not parsed over.
        scratch.write("vendor/sources.toml", b"[[source]]\n# drift\n");
        let error = load_catalog_manifest(&scratch.root, "benchmarks")
            .expect_err("stale sources ledger must fail");
        assert_eq!(error.code(), ErrorCode::Schema);

        let (mutated, _) = manifest_root("identity-dup", &["jit.a", "jit.b"]);
        let bytes = fs::read(mutated.root.join(schema::MANIFEST_PATH)).expect("read");
        let text = String::from_utf8(bytes)
            .expect("utf8")
            .replacen("\"jit.b\"", "\"jit.a\"", 1);
        // Duplicate JSON keys are caught by the structural check; the
        // duplicate identifier itself is caught by the digest.
        assert!(text.contains("\"jit.a\", \"jit.a\""));
        fs::write(mutated.root.join(schema::MANIFEST_PATH), text).expect("write");
        assert!(load_catalog_manifest(&mutated.root, "benchmarks").is_err());

        let (bad_tag, _) = manifest_root("identity-tag", &["jit.a"]);
        let bytes = fs::read(bad_tag.root.join(schema::MANIFEST_PATH)).expect("read");
        let text = String::from_utf8(bytes)
            .expect("utf8")
            .replace(MANIFEST_SCHEMA, "bamti.other/v9");
        fs::write(bad_tag.root.join(schema::MANIFEST_PATH), text).expect("write");
        assert!(load_catalog_manifest(&bad_tag.root, "benchmarks").is_err());
    }

    #[test]
    fn runner_allowlist_accepts_declared_and_rejects_mismatch() {
        let declared = [
            ("typescript-7.0.2", "compiler", SuiteRunner::Compiler),
            ("typescript-6.0.2", "compiler", SuiteRunner::Compiler),
            ("test262", "interpreter", SuiteRunner::Interpreter),
            ("test262", "jit", SuiteRunner::Jit),
            ("test262", "aot", SuiteRunner::Aot),
            ("formal-quint", "quint", SuiteRunner::Quint),
            ("formal-lean", "lean", SuiteRunner::Lean),
            ("formal-redex", "redex", SuiteRunner::Redex),
            ("target-cells", "aot", SuiteRunner::Aot),
            ("benchmarks", "perf", SuiteRunner::Perf),
        ];
        for (catalog, runner, expected) in declared {
            assert_eq!(
                resolve_runner(catalog, runner).expect("declared"),
                expected,
                "{catalog}/{runner}"
            );
        }
        for (catalog, runner) in [
            ("typescript-7.0.2", "aot"),
            ("typescript-7.0.2", "interpreter"),
            ("test262", "compiler"),
            ("test262", "perf"),
            ("formal-quint", "lean"),
            ("formal-lean", "quint"),
            ("formal-redex", "compiler"),
            ("target-cells", "perf"),
            ("benchmarks", "aot"),
        ] {
            let error = resolve_runner(catalog, runner).expect_err("undeclared runner must fail");
            assert_eq!(error.code(), ErrorCode::Schema, "{catalog}/{runner}");
            let text = error.to_string();
            assert!(text.contains(catalog) && text.contains(runner), "{text}");
        }
        assert_eq!(
            resolve_runner("benchmarks", "").expect("sole runner"),
            SuiteRunner::Perf
        );
        assert!(resolve_runner("test262", "").is_err());
        assert_eq!(
            resolve_runner("node-24", "compiler")
                .expect_err("foreign catalog")
                .code(),
            ErrorCode::Usage
        );
        assert_eq!(
            resolve_runner("benchmarks", "Perf")
                .expect_err("case mismatch")
                .code(),
            ErrorCode::Schema
        );
    }

    #[test]
    fn shard_membership_partitions_the_canonical_catalog() {
        let identifiers = [
            "jit.a", "jit.b", "jit.c", "jit.d", "jit.e", "jit.f", "jit.g",
        ];
        let obligations = materialize_obligations(
            "benchmarks",
            &identifiers
                .iter()
                .map(|entry| (*entry).to_owned())
                .collect::<Vec<_>>(),
            SuiteRunner::Perf,
            "ubuntu-latest",
        )
        .expect("obligations");
        assert_eq!(obligations.len(), 7);
        for count in [1usize, 2, 3, 5, 7] {
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            for index in 0..count {
                let spec = ShardSpec::new(index as u32, count as u32).expect("spec");
                for member in spec.member_indices(obligations.len()) {
                    assert!(spec.owns(member));
                    assert!(seen.insert(member), "shards must be disjoint");
                }
            }
            assert_eq!(seen.len(), obligations.len(), "shards must cover");
        }
        let keys: Vec<ObligationKey> = obligations.into_iter().map(|entry| entry.key).collect();
        let head = ShardIdentity::plan(ShardSpec::new(0, 3).expect("spec"), &keys).expect("plan");
        let tail = ShardIdentity::plan(ShardSpec::new(2, 3).expect("spec"), &keys).expect("plan");
        assert_eq!(head.catalog_digest(), tail.catalog_digest());
        assert_ne!(head.obligation_set_digest(), tail.obligation_set_digest());
        assert_eq!(
            head.expected_count() + tail.expected_count() + 3,
            keys.len() + 1
        );
    }

    #[test]
    fn suite_never_mints_pass_without_exact_observables() {
        fn key(case: &str) -> ObligationKey {
            ObligationKey::new(
                "benchmarks",
                case,
                "default",
                ExecutionMode::Aot,
                "ubuntu-latest",
            )
            .expect("key")
        }
        let declared = BTreeSet::from(["jit.a".to_owned()]);
        let binding = LaneBinding::unbound(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        )
        .expect("binding");
        let request = LaneRequest::new(
            binding.clone(),
            7,
            key("jit.a"),
            declared,
            vec!["bamts-verification::suite::worker".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            CASE_TIMEOUT_MS,
        )
        .expect("request");
        let response_completed = |artifacts: BTreeMap<String, String>, request_id: u64| {
            serde_json::to_vec(
                &LaneResponse::new(
                    binding.clone(),
                    request_id,
                    key("jit.a"),
                    LaneOutcome::Completed { artifacts },
                )
                .expect("response"),
            )
            .expect("encode")
        };
        // Claimed completion with the exact declared artifact set, correct
        // binding, request_id, and key: only the parent derivation may turn this into PASS.
        let exact = BTreeMap::from([("jit.a".to_owned(), hex(9))]);
        let row = derive_row(
            &request,
            LaneProcessResult {
                observation: ProcessObservation::Exited { code: 0 },
                response_body: Some(response_completed(exact.clone(), 7)),
                duration_ms: 1,
                detail: String::new(),
            },
        )
        .expect("derive");
        assert_eq!(row.state(), TerminalState::Pass);
        // Same claim with a wrong request_id, a wrong observable, or an extra
        // artifact is protocol evidence, never PASS.
        let mut extra = exact.clone();
        extra.insert("stderr".to_owned(), hex(4));
        for body in [
            response_completed(exact.clone(), 8),
            response_completed(BTreeMap::from([("other".to_owned(), hex(9))]), 7),
            response_completed(extra, 7),
        ] {
            let row = derive_row(
                &request,
                LaneProcessResult {
                    observation: ProcessObservation::Exited { code: 0 },
                    response_body: Some(body),
                    duration_ms: 1,
                    detail: String::new(),
                },
            )
            .expect("derive");
            assert_eq!(row.state(), TerminalState::ProtocolError);
            assert!(!row.state().is_pass());
        }
    }

    fn binding_for_tests(path: &Path) -> RunBinding {
        let repository = path
            .ancestors()
            .find(|candidate| candidate.join(".git").is_dir())
            .expect("fixture git repository");
        current_run_binding(repository, "benchmarks").expect("current binding")
    }

    fn write_shard(root: &Path, name: &str, keys: &[ObligationKey], spec: ShardSpec) -> PathBuf {
        let obligations: Vec<EvidenceRow> = spec
            .member_indices(keys.len())
            .map(|index| {
                let key = &keys[index];
                EvidenceRow::new(
                    key.clone(),
                    vec!["bamts-verification::suite::worker".to_owned()],
                    WorkingDirectoryPolicy::RepositoryRoot,
                    BTreeSet::from([key.configuration().to_owned()]),
                    BTreeMap::new(),
                    TerminalState::BlockingFail,
                    1,
                    "synthetic blocking outcome",
                )
                .expect("row")
            })
            .collect();
        let header = EvidenceHeader::new(
            ShardIdentity::plan(spec, keys).expect("plan"),
            binding_for_tests(root),
            ExecutionBinding::local_for_tests(),
        )
        .expect("header");
        let path = root.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("shard parent");
        }
        let file = File::create(&path).expect("shard file");
        let mut writer = EvidenceWriter::new(file, header).expect("writer");
        for row in &obligations {
            writer.write_row(row).expect("write");
        }
        writer.finish().expect("finish");
        path
    }

    fn merge_for_tests(
        root: &Path,
        catalog: &str,
        receipts: &Path,
        out: &Path,
        publish: PublishMode,
    ) -> Result<SuiteReport> {
        merge_suite(
            root,
            &SuiteMergeRequest {
                catalog: catalog.to_owned(),
                receipts: receipts.to_path_buf(),
                out: out.to_path_buf(),
                publish,
            },
        )
    }

    #[test]
    fn merge_closure_rejects_missing_extra_and_stale_rows() {
        let (scratch, sorted) = manifest_root(
            "merge",
            &["jit.a", "jit.b", "jit.c", "jit.d", "jit.e", "jit.f"],
        );
        let root = scratch.root.clone();
        let obligations =
            materialize_obligations("benchmarks", &sorted, SuiteRunner::Perf, "ubuntu-latest")
                .expect("obligations");
        let keys: Vec<ObligationKey> = obligations.into_iter().map(|entry| entry.key).collect();
        let receipts = root.join("receipts");
        for index in 0..3u32 {
            write_shard(
                &receipts,
                &format!("shard-{index}.jsonl"),
                &keys,
                ShardSpec::new(index, 3).expect("spec"),
            );
        }
        let out = root.join("merged.jsonl");
        let report = merge_for_tests(&root, "benchmarks", &receipts, &out, PublishMode::Replace)
            .expect("complete merge");
        assert_eq!(report.rows, keys.len());
        assert_eq!(report.documents, 3);
        assert_eq!(report.platform, "ubuntu-latest");
        assert_eq!(report.runner, "perf");
        assert_eq!(report.states.get("BLOCKING_FAIL"), Some(&keys.len()));
        assert_eq!(
            report.obligation_set_digest,
            crate::shard::digest_obligation_set(keys.iter())
        );

        // A missing shard aborts the merge.
        let partial = root.join("partial");
        fs::create_dir_all(&partial).expect("partial dir");
        for index in 0..2u32 {
            write_shard(
                &partial,
                &format!("shard-{index}.jsonl"),
                &keys,
                ShardSpec::new(index, 3).expect("spec"),
            );
        }
        assert!(
            merge_for_tests(
                &root,
                "benchmarks",
                &partial,
                &root.join("out.jsonl"),
                PublishMode::Replace
            )
            .is_err(),
            "missing shard must be rejected"
        );

        // A stale run binding (other authority digest) aborts the merge.
        let stale = root.join("stale");
        fs::create_dir_all(&stale).expect("stale dir");
        for index in 0..3u32 {
            {
                // Resolve shard rows with a divergent binding.
                let obligations: Vec<EvidenceRow> = ShardSpec::new(index, 3)
                    .expect("spec")
                    .member_indices(keys.len())
                    .map(|case| {
                        EvidenceRow::new(
                            keys[case].clone(),
                            vec![],
                            WorkingDirectoryPolicy::RepositoryRoot,
                            BTreeSet::from([keys[case].configuration().to_owned()]),
                            BTreeMap::new(),
                            TerminalState::BlockingFail,
                            1,
                            "synthetic blocking outcome",
                        )
                        .expect("row")
                    })
                    .collect();
                let binding = if index == 2 {
                    RunBinding::new(
                        hex(9),
                        hex(2),
                        hex(3),
                        hex(4),
                        ToolchainPin::new("rustc-1.97.1", hex(5)).expect("toolchain pin"),
                    )
                    .expect("binding")
                } else {
                    binding_for_tests(&root)
                };
                let header = EvidenceHeader::new(
                    ShardIdentity::plan(ShardSpec::new(index, 3).expect("spec"), &keys)
                        .expect("plan"),
                    binding,
                    ExecutionBinding::local_for_tests(),
                )
                .expect("header");
                let file =
                    File::create(stale.join(format!("shard-{index}.jsonl"))).expect("shard file");
                let mut writer = EvidenceWriter::new(file, header).expect("writer");
                for row in &obligations {
                    writer.write_row(row).expect("write");
                }
                writer.finish().expect("finish");
            };
        }
        let error = merge_for_tests(
            &root,
            "benchmarks",
            &stale,
            &root.join("out2.jsonl"),
            PublishMode::Replace,
        )
        .expect_err("mixed authority binding must fail");
        assert_eq!(error.code(), ErrorCode::Digest);

        // An extra, foreign obligation row breaks closure.
        let extra = root.join("extra");
        fs::create_dir_all(&extra).expect("extra dir");
        for index in 0..3u32 {
            write_shard(
                &extra,
                &format!("shard-{index}.jsonl"),
                &keys,
                ShardSpec::new(index, 3).expect("spec"),
            );
        }
        let foreign = ObligationKey::new(
            "benchmarks",
            "aaa.foreign",
            "default",
            ExecutionMode::Aot,
            "ubuntu-latest",
        )
        .expect("foreign key");
        let mut foreign_keys = keys.clone();
        foreign_keys[0] = foreign;
        write_shard(
            &extra,
            "shard-0.jsonl",
            &foreign_keys,
            ShardSpec::new(0, 3).expect("spec"),
        );
        assert!(
            merge_for_tests(
                &root,
                "benchmarks",
                &extra,
                &root.join("out3.jsonl"),
                PublishMode::Replace
            )
            .is_err(),
            "extra row must be rejected"
        );

        // A runner mode no workflow declares is rejected before merging.
        let wrong_mode = root.join("wrong-mode");
        fs::create_dir_all(&wrong_mode).expect("dir");
        let wrong_keys: Vec<ObligationKey> = sorted
            .iter()
            .map(|identifier| {
                ObligationKey::new(
                    "benchmarks",
                    identifier,
                    "default",
                    ExecutionMode::Jit,
                    "ubuntu-latest",
                )
                .expect("key")
            })
            .collect();
        let header = EvidenceHeader::new(
            ShardIdentity::plan(ShardSpec::new(0, 1).expect("spec"), &wrong_keys).expect("plan"),
            binding_for_tests(&root),
            ExecutionBinding::local_for_tests(),
        )
        .expect("header");
        let file = File::create(wrong_mode.join("only.jsonl")).expect("file");
        let mut writer = EvidenceWriter::new(file, header).expect("writer");
        for key in &wrong_keys {
            writer
                .write_row(
                    &EvidenceRow::new(
                        key.clone(),
                        vec![],
                        WorkingDirectoryPolicy::RepositoryRoot,
                        BTreeSet::from(["default".to_owned()]),
                        BTreeMap::new(),
                        TerminalState::BlockingFail,
                        1,
                        "wrong runner mode",
                    )
                    .expect("row"),
                )
                .expect("write");
        }
        writer.finish().expect("finish");
        assert_eq!(
            merge_for_tests(
                &root,
                "benchmarks",
                &wrong_mode,
                &root.join("out4.jsonl"),
                PublishMode::Replace
            )
            .expect_err("undeclared runner mode must fail")
            .code(),
            ErrorCode::Schema
        );
    }

    #[test]
    fn two_half_merge_is_deterministic_and_failure_preserves_output() {
        let (scratch, sorted) = manifest_root("two-half", &["jit.a", "jit.b", "jit.c", "jit.d"]);
        let root = scratch.root.clone();
        let obligations =
            materialize_obligations("benchmarks", &sorted, SuiteRunner::Perf, "ubuntu-latest")
                .expect("obligations");
        let keys: Vec<ObligationKey> = obligations.into_iter().map(|entry| entry.key).collect();
        let receipts = root.join("two");
        for index in 0..2 {
            write_shard(
                &receipts,
                &format!("shard-{index}.jsonl"),
                &keys,
                ShardSpec::new(index, 2).expect("spec"),
            );
        }
        let out = root.join("two-halves.jsonl");
        let report = merge_for_tests(&root, "benchmarks", &receipts, &out, PublishMode::Replace)
            .expect("two-half closure");
        assert_eq!(report.documents, 2);
        assert_eq!(report.rows, keys.len());
        let canonical = fs::read(&out).expect("canonical output");
        merge_for_tests(&root, "benchmarks", &receipts, &out, PublishMode::Replace)
            .expect("deterministic replacement");
        assert_eq!(fs::read(&out).expect("replacement"), canonical);

        let duplicate = root.join("duplicate");
        fs::create_dir_all(&duplicate).expect("duplicate root");
        let shard0 = fs::read_to_string(receipts.join("shard-0.jsonl")).expect("shard 0");
        let mut lines: Vec<&str> = shard0.lines().collect();
        lines.insert(2, lines[1]);
        fs::write(
            duplicate.join("shard-0.jsonl"),
            format!("{}\n", lines.join("\n")),
        )
        .expect("tampered duplicate row");
        fs::copy(
            receipts.join("shard-1.jsonl"),
            duplicate.join("shard-1.jsonl"),
        )
        .expect("shard 1");
        assert!(
            merge_for_tests(&root, "benchmarks", &duplicate, &out, PublishMode::Replace).is_err(),
            "duplicate row must be rejected"
        );
        assert_eq!(
            fs::read(&out).expect("preserved output"),
            canonical,
            "failed merge must not mutate the published output"
        );
    }

    #[test]
    fn missing_adapter_records_typed_blocking_rows_and_continues() {
        assert!(
            std::env::var_os("BAMTS_SUITE_PERF_ADAPTER").is_none(),
            "test requires no injected perf adapter"
        );
        let (scratch, _) = manifest_root("closed", &["jit.a", "jit.b"]);
        let receipt = scratch.root.join("receipt.jsonl");
        let report = run_suite(
            &scratch.root,
            &SuiteRunRequest {
                catalog: "benchmarks".to_owned(),
                shard: ShardSpec::unsharded(),
                receipt: receipt.clone(),
                runner: "perf".to_owned(),
                platform: "ubuntu-latest".to_owned(),
                execution: ExecutionBinding::local_for_tests(),
            },
        )
        .expect("missing adapter is blocking evidence, not an abort");
        assert_eq!(report.rows, 2);
        assert_eq!(report.states.get("BLOCKING_FAIL"), Some(&2));

        let mut reader = EvidenceReader::open(&receipt).expect("receipt");
        let mut rows = 0;
        while let Some(row) = reader.next_row().expect("row") {
            assert_eq!(row.state(), TerminalState::BlockingFail);
            rows += 1;
        }
        assert_eq!(reader.finish().expect("footer").row_count(), rows);
        assert_eq!(rows, 2);
    }

    /// `fourslash/…` obligations are language-service authority cases: the
    /// executor routes them to `INAPPLICABLE_LANGUAGE_SERVICE` before any lane
    /// adapter runs, while compiler/conformance cases stay routable.
    #[test]
    fn fourslash_cases_route_to_language_service_inapplicable() {
        let fourslash = ObligationKey::new(
            "typescript-7.0.2",
            "fourslash/tests/cases/fourslash/completionListInTypeAtPosition.ts",
            "default#parse",
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key");
        let outcome = fourslash_lane_outcome(&fourslash).expect("fourslash routing");
        assert_eq!(
            outcome,
            LaneOutcome::InapplicableLanguageService {
                detail: format!(
                    "fourslash language-service authority case `{}` routed out of the compiler lane (internal fourslash DSL is an exact exclusion)",
                    fourslash.case()
                ),
            }
        );

        let compiler = ObligationKey::new(
            "typescript-7.0.2",
            "compiler/tests/cases/compiler/2dArrays.ts",
            "default#parse",
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key");
        assert!(fourslash_lane_outcome(&compiler).is_none());
    }

    /// Landing a generated receipt through every lifecycle phase — untracked,
    /// staged, committed, modified, deleted, and re-added — never perturbs the
    /// projected candidate-source digest. Only the receipt changes; the
    /// candidate identity it is bound to must not.
    #[test]
    fn receipt_landing_transaction_is_tree_invariant() {
        let (scratch, _) = manifest_root("landing-invariance", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        // The shared fixture's `.gitignore` hides `*.jsonl` so unrelated tests
        // can scatter scratch receipts; this test needs the real project
        // policy, which ignores only build output, so a fresh receipt is
        // genuinely untracked and visible to `git status`.
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");

        let baseline = candidate_tree_digest(&scratch.root).expect("clean baseline digest");

        // Untracked.
        let receipt = scratch.write("verification/receipts/a.jsonl", b"receipt-v1");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("untracked output digest"),
            baseline,
            "an untracked generated output must not perturb the projection"
        );

        // Staged.
        run_git(&["add", "verification/receipts/a.jsonl"]);
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("staged output digest"),
            baseline,
            "a staged generated output must not perturb the projection"
        );

        // Committed.
        commit("land receipt");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("committed output digest"),
            baseline,
            "a committed generated output must not perturb the projection"
        );

        // Modified, untracked.
        fs::write(&receipt, b"receipt-v2").expect("rewrite receipt");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("modified output digest"),
            baseline,
            "an untracked modification to a generated output must not perturb the projection"
        );

        // Deleted, untracked.
        fs::remove_file(&receipt).expect("delete receipt");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("deleted output digest"),
            baseline,
            "an untracked deletion of a generated output must not perturb the projection"
        );

        // Deletion committed.
        run_git(&["add", "-A"]);
        commit("remove receipt");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("committed deletion digest"),
            baseline,
            "committing the removal of a generated output must not perturb the projection"
        );

        // Re-added as output only, committed.
        scratch.write("verification/receipts/a.jsonl", b"receipt-v3");
        run_git(&["add", "-A"]);
        commit("re-land receipt");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("re-landed output digest"),
            baseline,
            "re-landing a generated output must not perturb the projection"
        );
    }

    /// A source file staged in the index — never committed — dirties the tree
    /// and is refused; a v2 receipt requires a clean committed tree.
    #[test]
    fn staged_source_file_is_rejected_by_dirty_gate() {
        let (scratch, _) = manifest_root("staged-source", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        candidate_tree_digest(&scratch.root).expect("clean baseline");

        scratch.write("src/feature.ts", b"// new source");
        run_git(&["add", "src/feature.ts"]);
        let error =
            candidate_tree_digest(&scratch.root).expect_err("staged source must be refused");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    /// A new source file that is merely untracked — never staged — dirties the
    /// tree exactly the same way a staged one does.
    #[test]
    fn untracked_source_file_is_rejected_by_dirty_gate() {
        let (scratch, _) = manifest_root("untracked-source", &["jit.a"]);
        candidate_tree_digest(&scratch.root).expect("clean baseline");

        scratch.write("src/feature.ts", b"// untracked source");
        let error =
            candidate_tree_digest(&scratch.root).expect_err("untracked source must be refused");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    /// A real, committed source change permanently moves the candidate
    /// identity, so a binding captured beforehand is provably stale afterward:
    /// `first_mismatch_field` names exactly `candidate_tree_digest`, with
    /// every other bound field — authority, harness, binary, toolchain —
    /// unchanged.
    #[test]
    fn committed_source_change_produces_stale_binding() {
        let (scratch, _) = manifest_root("committed-source", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        let stale_binding =
            current_run_binding(&scratch.root, "catalog-a").expect("binding before change");

        scratch.write("src/feature.ts", b"// source changed");
        run_git(&["add", "src/feature.ts"]);
        commit("source change");

        let fresh_binding =
            current_run_binding(&scratch.root, "catalog-a").expect("binding after change");
        assert_eq!(
            stale_binding.first_mismatch_field(&fresh_binding),
            Some("candidate_tree_digest"),
            "a receipt captured before the source change must be rejected as stale"
        );
    }

    /// The capture must be an atomic snapshot of one committed tree: if
    /// `HEAD` moves while the dirty gate and enumeration run, the torn read
    /// must be refused, never digested. Replaying a capture against a tree
    /// that a later commit displaced is that torn read, made deterministic.
    #[test]
    fn head_move_during_capture_is_refused() {
        let (scratch, _) = manifest_root("moved-head", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        let stale_tree = resolve_head_tree(&scratch.root).expect("resolve committed tree");

        scratch.write("src/feature.ts", b"// source");
        run_git(&["add", "src/feature.ts"]);
        commit("head moves mid-capture");

        let error = candidate_tree_digest_against(&scratch.root, &stale_tree)
            .expect_err("a capture overtaken by a commit must be refused");
        assert_eq!(error.code(), ErrorCode::Digest);

        let fresh_tree = resolve_head_tree(&scratch.root).expect("resolve moved tree");
        candidate_tree_digest_against(&scratch.root, &fresh_tree)
            .expect("a capture over one stable tree succeeds");
    }

    /// A rename whose original path is candidate source is refused even though
    /// its destination lands at an eligible output path: the projection reads
    /// both sides of a rename record, and cannot let a source edit disguise
    /// itself as a generated output by walking through one.
    #[test]
    fn rename_source_to_output_path_is_rejected() {
        let (scratch, _) = manifest_root("rename-source-to-output", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");
        scratch.write("src/feature.ts", b"// source");
        run_git(&["add", "src/feature.ts"]);
        commit("add source");
        candidate_tree_digest(&scratch.root).expect("clean before rename");

        // `git mv` never creates the destination directory itself.
        fs::create_dir_all(scratch.root.join("verification/receipts"))
            .expect("create destination directory");
        run_git(&[
            "mv",
            "src/feature.ts",
            "verification/receipts/feature.jsonl",
        ]);
        let error = candidate_tree_digest(&scratch.root)
            .expect_err("a rename from source to an output-eligible path must be refused");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    /// A rename whose destination is candidate source is refused even though
    /// its original path was a generated output: an output cannot walk itself
    /// out of the exclusion set and start masquerading as source either.
    #[test]
    fn rename_output_to_source_path_is_rejected() {
        let (scratch, _) = manifest_root("rename-output-to-source", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");
        scratch.write("verification/receipts/feature.jsonl", b"{}");
        run_git(&["add", "verification/receipts/feature.jsonl"]);
        commit("add output");
        candidate_tree_digest(&scratch.root).expect("clean before rename");

        // `git mv` never creates the destination directory itself.
        fs::create_dir_all(scratch.root.join("src")).expect("create destination directory");
        run_git(&[
            "mv",
            "verification/receipts/feature.jsonl",
            "src/feature.txt",
        ]);
        let error = candidate_tree_digest(&scratch.root)
            .expect_err("a rename from an output-eligible path to source must be refused");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    /// A staged rename between two output-eligible paths stays on the exempt
    /// side of the boundary on both ends, so it must not dirty the tree. This
    /// is the contrasting case to the two tests above: only a boundary
    /// crossing is refused, not every rename record that touches an output.
    #[test]
    fn rename_within_output_set_is_invariant() {
        let (scratch, _) = manifest_root("rename-within-output", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");
        scratch.write("verification/receipts/old.jsonl", b"{}");
        run_git(&["add", "verification/receipts/old.jsonl"]);
        commit("add output");
        let baseline = candidate_tree_digest(&scratch.root).expect("clean baseline");

        run_git(&[
            "mv",
            "verification/receipts/old.jsonl",
            "verification/receipts/new.jsonl",
        ]);
        let digest = candidate_tree_digest(&scratch.root)
            .expect("a rename between two output-eligible paths must not dirty the tree");
        assert_eq!(
            digest, baseline,
            "renaming within the output set must not perturb the projection"
        );
    }

    /// A symlink standing at an eligible output path is source-kind, not a
    /// generated output: uncommitted, it fails the regular-file worktree
    /// check; committed, it stays retained in the projection stream instead of
    /// being excluded, so it cannot use its path to hide from candidate
    /// identity.
    #[test]
    #[cfg(unix)]
    fn symlink_at_output_path_is_retained_as_source() {
        let (scratch, _) = manifest_root("symlink-output", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");
        let baseline = candidate_tree_digest(&scratch.root).expect("clean baseline");

        // `symlink` does not create the directory its link path names, unlike
        // `Scratch::write`, so the receipt-set parent must exist first.
        fs::create_dir_all(scratch.root.join("verification/receipts"))
            .expect("create output directory");

        std::os::unix::fs::symlink(
            "/tmp",
            scratch.root.join("verification/receipts/link.jsonl"),
        )
        .expect("create symlink");

        // Uncommitted: an untracked symlink at an eligible output path is
        // refused — it is not a regular file, so the untracked-output
        // exemption does not apply.
        let error = candidate_tree_digest(&scratch.root)
            .expect_err("an untracked symlink at an output path must be refused");
        assert_eq!(error.code(), ErrorCode::Schema);

        run_git(&["add", "verification/receipts/link.jsonl"]);
        commit("land symlink");

        // Committed: the symlink is retained in the projection stream, not
        // excluded, so the digest changes even though its path matches the
        // output allowlist.
        let after = candidate_tree_digest(&scratch.root)
            .expect("a clean commit containing a symlink must still project");
        assert_ne!(
            after, baseline,
            "a symlink at an output path must remain bound in candidate identity"
        );
    }

    /// The mirror case of the symlink test: an executable-mode regular file is
    /// still a regular file, so it stays exempt at an eligible output path
    /// exactly like a non-executable one.
    #[test]
    #[cfg(unix)]
    fn executable_bit_generated_output_remains_exempt() {
        let (scratch, _) = manifest_root("executable-output", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");
        let baseline = candidate_tree_digest(&scratch.root).expect("clean baseline");

        let output = scratch.write("verification/receipts/tool.jsonl", b"{}");
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&output).expect("stat output").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&output, perms).expect("chmod +x");
        run_git(&["add", "verification/receipts/tool.jsonl"]);
        commit("land executable output");

        let after = candidate_tree_digest(&scratch.root)
            .expect("an executable generated output must still project cleanly");
        assert_eq!(
            after, baseline,
            "an executable-mode generated output is still a regular file and stays exempt"
        );
    }

    /// Spaces, a leading dash, and other unusual-but-valid path bytes must
    /// neither break the `ls-tree`/`status` parsers nor confuse exact-path
    /// matching: an odd-byte output stays exempt, an odd-byte source stays
    /// bound, and neither is ever conflated with the other.
    #[test]
    fn unusual_path_bytes_are_handled_exactly() {
        let (scratch, _) = manifest_root("odd-path-bytes", &["jit.a"]);
        let run_git = |args: &[&str]| {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.root)
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        let commit = |message: &str| {
            run_git(&[
                "-c",
                "user.name=bamts-suite-test",
                "-c",
                "user.email=suite@example.invalid",
                "commit",
                "-qm",
                message,
            ]);
        };
        scratch.write(".gitignore", b"/target/\n");
        run_git(&["add", "-A"]);
        commit("realistic gitignore");

        scratch.write("-weird source name.txt", b"v1");
        scratch.write("verification/receipts/name with space.jsonl", b"{}");
        run_git(&["add", "-A"]);
        commit("odd path bytes");
        let baseline = candidate_tree_digest(&scratch.root)
            .expect("odd path bytes must not break the ls-tree/status parsers");

        // Modifying the odd-byte OUTPUT path, untracked, must remain exempt.
        fs::write(
            scratch
                .root
                .join("verification/receipts/name with space.jsonl"),
            b"{}\n",
        )
        .expect("mutate output");
        assert_eq!(
            candidate_tree_digest(&scratch.root).expect("modified odd-path output digest"),
            baseline,
            "an odd-byte generated-output path must still be recognized by exact matching"
        );
        run_git(&[
            "checkout",
            "--",
            "verification/receipts/name with space.jsonl",
        ]);

        // Modifying the odd-byte SOURCE path, staged only, must still dirty
        // the tree.
        fs::write(scratch.root.join("-weird source name.txt"), b"v2").expect("mutate source");
        run_git(&["add", "--", "-weird source name.txt"]);
        let error = candidate_tree_digest(&scratch.root)
            .expect_err("an odd-byte source path must still be recognized as candidate source");
        assert_eq!(error.code(), ErrorCode::Schema);
    }

    /// A binding computed under the retired full-tree algorithm — the
    /// `sha256("git-tree\0" + HEAD^{tree})` digest the projection replaced —
    /// is permanently stale against the current namespaced projection, even
    /// though nothing else about the run changed: authority, candidate
    /// binary, harness, and toolchain all still match. The version bump in
    /// `CANDIDATE_SOURCE_NAMESPACE` is exactly what a legacy receipt cannot
    /// satisfy, and `first_mismatch_field` must name the one field that
    /// carries that version, `candidate_tree_digest`, and nothing else.
    #[test]
    fn domain_version_change_rejects_legacy_namespace_digest() {
        let (scratch, _) = manifest_root("legacy-namespace", &["jit.a"]);

        let mut snapshot = current_run_snapshot(&scratch.root).expect("current snapshot");
        let real_binding =
            binding_from_snapshot(&scratch.root, "catalog-a", &snapshot).expect("real binding");

        let tree_bytes = git_probe(&scratch.root, &["rev-parse", "HEAD^{tree}"])
            .expect("resolve committed tree");
        let tree = String::from_utf8_lossy(&tree_bytes).trim().to_owned();
        let legacy_digest = schema::sha256_hex(format!("git-tree\0{tree}").as_bytes());
        assert_ne!(
            legacy_digest, snapshot.candidate_tree_digest,
            "the legacy full-tree digest must differ from the current projection"
        );

        snapshot.candidate_tree_digest = legacy_digest;
        let legacy_binding = binding_from_snapshot(&scratch.root, "catalog-a", &snapshot)
            .expect("legacy-namespace binding");

        assert_eq!(
            legacy_binding.first_mismatch_field(&real_binding),
            Some("candidate_tree_digest"),
            "a receipt captured under the retired full-tree algorithm must be rejected as stale"
        );
    }
}
