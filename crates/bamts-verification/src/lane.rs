//! Lane request/response protocol and parent-only PASS derivation.
//!
//! Workers never mint `PASS`.  They return a completed observation or a closed
//! non-pass outcome.  The parent records `PASS` only when the run binding,
//! key (case, mode, platform), and observable set match exactly.  Timeout,
//! signal, protocol error, and worker crash become blocking receipts, and the
//! lane continues with later cases.  Process execution reuses the corpus
//! normalized environment, bounded pipe drain, process-group timeout, and
//! whole-group termination.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::{OracleLimits, normalized_env, run_process},
    evidence::{EvidenceRow, TerminalState, WorkingDirectoryPolicy},
    shard::{ObligationKey, require_token},
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Environment variable naming the worker request JSON path.
pub const LANE_WORKER_REQUEST: &str = "BAMTS_LANE_WORKER_REQUEST";

/// Version of the compiler snapshot handoff binding.
pub const COMPILER_SNAPSHOT_BINDING_VERSION: u32 = 1;

const DEFAULT_MAX_OUTPUT_BYTES: usize = 1 << 20;
const RUN_ID_BYTES: usize = 32;
const SNAPSHOT_BINDING_DOMAIN: &[u8] = b"bamts.compiler-lane.snapshot-binding\0v1";

/// Per-suite identity carried by every request and mirrored by every response.
///
/// Snapshot fields are all absent for lanes without snapshot assets and all
/// present for compiler lanes. The metadata digest is domain-separated and
/// length-prefixes the catalog, canonical root, and exact retained metadata
/// bytes so no concatenation ambiguity or `snapshot.sha256` substitution can
/// authenticate a worker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaneBinding {
    version: u32,
    run_id: String,
    snapshot_catalog: Option<String>,
    snapshot_root: Option<String>,
    snapshot_metadata_sha256: Option<String>,
}

impl LaneBinding {
    /// Generate an unpredictable identity for one suite invocation.
    pub fn fresh() -> Result<Self> {
        let mut entropy = [0_u8; RUN_ID_BYTES];
        getrandom::fill(&mut entropy).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("cannot obtain lane run-id entropy: {error}"),
            )
        })?;
        Self::unbound(hex_encode(&entropy))
    }

    /// Construct a deterministic unbound value, primarily for protocol tests.
    pub fn unbound(run_id: impl Into<String>) -> Result<Self> {
        let binding = Self {
            version: COMPILER_SNAPSHOT_BINDING_VERSION,
            run_id: run_id.into(),
            snapshot_catalog: None,
            snapshot_root: None,
            snapshot_metadata_sha256: None,
        };
        binding.validate()?;
        Ok(binding)
    }

    /// Bind this run to one exact compiler snapshot metadata image.
    pub fn with_snapshot(
        self,
        catalog: &str,
        canonical_root: &Path,
        pin_bytes: &[u8],
        index_bytes: &[u8],
        ledger_bytes: &[u8],
    ) -> Result<Self> {
        self.validate()?;
        if self.has_snapshot() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "lane binding already has snapshot identity",
            ));
        }
        require_token("snapshot catalog", catalog)?;
        if !canonical_root.is_absolute() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "snapshot root `{}` is not canonical absolute path",
                    canonical_root.display()
                ),
            ));
        }
        let root = canonical_root.to_str().ok_or_else(|| {
            VerificationError::new(ErrorCode::Schema, "snapshot root is not UTF-8")
        })?;
        let metadata_digest =
            snapshot_metadata_digest(catalog, root, pin_bytes, index_bytes, ledger_bytes)?;
        let binding = Self {
            version: self.version,
            run_id: self.run_id,
            snapshot_catalog: Some(catalog.to_owned()),
            snapshot_root: Some(root.to_owned()),
            snapshot_metadata_sha256: Some(metadata_digest),
        };
        binding.validate()?;
        Ok(binding)
    }

    /// Validate shape and protocol version after any untrusted decode.
    pub fn validate(&self) -> Result<()> {
        if self.version != COMPILER_SNAPSHOT_BINDING_VERSION {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!(
                    "lane binding version {} is not supported version {COMPILER_SNAPSHOT_BINDING_VERSION}",
                    self.version
                ),
            ));
        }
        require_lower_hex("lane run_id", &self.run_id, RUN_ID_BYTES * 2)?;
        match (
            self.snapshot_catalog.as_deref(),
            self.snapshot_root.as_deref(),
            self.snapshot_metadata_sha256.as_deref(),
        ) {
            (None, None, None) => Ok(()),
            (Some(catalog), Some(root), Some(digest)) => {
                require_token("snapshot catalog", catalog)?;
                if !Path::new(root).is_absolute() {
                    return Err(VerificationError::new(
                        ErrorCode::Schema,
                        format!("snapshot root `{root}` is not absolute"),
                    ));
                }
                require_lower_hex("snapshot metadata digest", digest, 64)
            }
            _ => Err(VerificationError::new(
                ErrorCode::Schema,
                "lane snapshot binding fields must be either all present or all absent",
            )),
        }
    }

    /// Exact-match retained worker metadata against the parent-issued binding.
    pub fn verify_snapshot(
        &self,
        catalog: &str,
        canonical_root: &Path,
        pin_bytes: &[u8],
        index_bytes: &[u8],
        ledger_bytes: &[u8],
    ) -> Result<()> {
        self.validate()?;
        let expected = Self::unbound(self.run_id.clone())?.with_snapshot(
            catalog,
            canonical_root,
            pin_bytes,
            index_bytes,
            ledger_bytes,
        )?;
        if self != &expected {
            return Err(VerificationError::new(
                ErrorCode::ProvenanceMismatch,
                "compiler snapshot binding does not match retained metadata",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn run_id(&self) -> &str {
        &self.run_id
    }

    #[must_use]
    pub fn has_snapshot(&self) -> bool {
        self.snapshot_metadata_sha256.is_some()
    }

    #[must_use]
    pub fn snapshot_catalog(&self) -> Option<&str> {
        self.snapshot_catalog.as_deref()
    }

    #[must_use]
    pub fn snapshot_root(&self) -> Option<&str> {
        self.snapshot_root.as_deref()
    }
}

fn snapshot_metadata_digest(
    catalog: &str,
    root: &str,
    pin_bytes: &[u8],
    index_bytes: &[u8],
    ledger_bytes: &[u8],
) -> Result<String> {
    let mut hasher = Sha256::new();
    hasher.update(SNAPSHOT_BINDING_DOMAIN);
    for part in [
        catalog.as_bytes(),
        root.as_bytes(),
        pin_bytes,
        index_bytes,
        ledger_bytes,
    ] {
        let length = u64::try_from(part.len()).map_err(|_| {
            VerificationError::new(ErrorCode::Schema, "snapshot binding field is too large")
        })?;
        hasher.update(length.to_be_bytes());
        hasher.update(part);
    }
    Ok(hex_encode(&hasher.finalize()))
}

fn require_lower_hex(label: &str, value: &str, length: usize) -> Result<()> {
    if value.len() != length
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("{label} must be exactly {length} lowercase hexadecimal characters"),
        ));
    }
    Ok(())
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

/// Parent-issued work item. The binding, request ID, and key are compared
/// exactly on return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaneRequest {
    binding: LaneBinding,
    request_id: u64,
    key: ObligationKey,
    observables: BTreeSet<String>,
    argv: Vec<String>,
    working_directory: WorkingDirectoryPolicy,
    timeout_ms: u64,
}

impl LaneRequest {
    pub fn new(
        binding: LaneBinding,
        request_id: u64,
        key: ObligationKey,
        observables: BTreeSet<String>,
        argv: Vec<String>,
        working_directory: WorkingDirectoryPolicy,
        timeout_ms: u64,
    ) -> Result<Self> {
        let request = Self {
            binding,
            request_id,
            key,
            observables,
            argv,
            working_directory,
            timeout_ms,
        };
        request.validate()?;
        Ok(request)
    }

    /// Validate the complete request after decoding an untrusted request file.
    pub fn validate(&self) -> Result<()> {
        self.binding.validate()?;
        if self.request_id == 0 {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "lane request_id must be positive",
            ));
        }
        self.key.validate()?;
        if self.observables.is_empty() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("lane request `{}` declares no observables", self.key),
            ));
        }
        for observable in &self.observables {
            require_token("observable", observable)?;
        }
        if self.timeout_ms == 0 {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "lane request timeout_ms must be positive",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn binding(&self) -> &LaneBinding {
        &self.binding
    }

    #[must_use]
    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    #[must_use]
    pub fn key(&self) -> &ObligationKey {
        &self.key
    }

    #[must_use]
    pub fn observables(&self) -> &BTreeSet<String> {
        &self.observables
    }

    #[must_use]
    pub fn timeout_ms(&self) -> u64 {
        self.timeout_ms
    }
}

/// Worker-reported outcome.  There is no `pass` variant.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum LaneOutcome {
    Completed {
        artifacts: BTreeMap<String, String>,
    },
    BlockingFail {
        detail: String,
    },
    /// The worker observed a deadline expiration before the obligation
    /// completed.  Mapped to [`TerminalState::Timeout`]; the receipt schema
    /// is unchanged because `Timeout` already exists as a terminal state.
    Timeout {
        detail: String,
    },
    InapplicableLanguageService {
        detail: String,
    },
    InapplicableOutOfScopeHostFeature {
        detail: String,
    },
    InapplicableV8Internal {
        detail: String,
    },
    InapplicableCatalogError {
        detail: String,
    },
    ExternalBlocked {
        detail: String,
    },
}

/// Worker response bound to the exact request binding, request ID, and key.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaneResponse {
    binding: LaneBinding,
    request_id: u64,
    key: ObligationKey,
    outcome: LaneOutcome,
}

impl LaneResponse {
    pub fn new(
        binding: LaneBinding,
        request_id: u64,
        key: ObligationKey,
        outcome: LaneOutcome,
    ) -> Result<Self> {
        let response = Self {
            binding,
            request_id,
            key,
            outcome,
        };
        response.validate()?;
        Ok(response)
    }

    /// Validate the complete response after decoding an untrusted response file.
    pub fn validate(&self) -> Result<()> {
        self.binding.validate()?;
        if self.request_id == 0 {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "lane response request_id must be positive",
            ));
        }
        self.key.validate()
    }

    #[must_use]
    pub fn binding(&self) -> &LaneBinding {
        &self.binding
    }

    #[must_use]
    pub fn request_id(&self) -> u64 {
        self.request_id
    }

    #[must_use]
    pub fn key(&self) -> &ObligationKey {
        &self.key
    }

    #[must_use]
    pub fn outcome(&self) -> &LaneOutcome {
        &self.outcome
    }
}

/// What the parent observed about the worker process itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcessObservation {
    Exited { code: i32 },
    TimedOut,
    Signaled { number: i32 },
}

/// Raw executor result.  `response_body` is untrusted until the parent parses it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneProcessResult {
    pub observation: ProcessObservation,
    pub response_body: Option<Vec<u8>>,
    pub duration_ms: u64,
    pub detail: String,
}

/// Executor seam used by the parent lane runner.
pub trait LaneExecutor {
    fn run(&mut self, request: &LaneRequest) -> Result<LaneProcessResult>;
}

/// Spawns a worker process using corpus process mechanics.
#[derive(Debug, Clone)]
pub struct ProcessExecutor {
    program: PathBuf,
    args: Vec<OsString>,
    cwd: PathBuf,
    work_dir: PathBuf,
    max_output_bytes: usize,
}

impl ProcessExecutor {
    pub fn new(
        program: impl Into<PathBuf>,
        args: Vec<OsString>,
        cwd: impl Into<PathBuf>,
        work_dir: impl Into<PathBuf>,
    ) -> Self {
        Self {
            program: program.into(),
            args,
            cwd: cwd.into(),
            work_dir: work_dir.into(),
            max_output_bytes: DEFAULT_MAX_OUTPUT_BYTES,
        }
    }

    pub fn with_max_output_bytes(mut self, cap: usize) -> Self {
        self.max_output_bytes = cap;
        self
    }
}

impl LaneExecutor for ProcessExecutor {
    fn run(&mut self, request: &LaneRequest) -> Result<LaneProcessResult> {
        request.validate()?;
        fs::create_dir_all(&self.work_dir).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: {error}", self.work_dir.display()),
            )
        })?;
        let request_path = self.work_dir.join(format!(
            "lane-{}-{}.json",
            request.binding().run_id(),
            request.request_id()
        ));
        let response_path = request_path.with_extension("response.json");
        if response_path.try_exists().map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: {error}", response_path.display()),
            )
        })? {
            return Err(VerificationError::new(
                ErrorCode::Replay,
                format!(
                    "refusing retained lane response `{}`",
                    response_path.display()
                ),
            ));
        }
        let encoded = serde_json::to_vec(request).map_err(|error| {
            VerificationError::new(ErrorCode::Json, format!("encode lane request: {error}"))
        })?;
        let mut request_file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&request_path)
            .map_err(|error| {
                VerificationError::new(
                    ErrorCode::Io,
                    format!("{}: {error}", request_path.display()),
                )
            })?;
        request_file.write_all(&encoded).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: {error}", request_path.display()),
            )
        })?;
        request_file.sync_all().map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: {error}", request_path.display()),
            )
        })?;

        let mut environment = normalized_env();
        if let Ok(path) = std::env::var("PATH") {
            environment.push(("PATH".to_owned(), path));
        }
        environment.push((
            LANE_WORKER_REQUEST.to_owned(),
            request_path.to_string_lossy().into_owned(),
        ));
        let limits = OracleLimits {
            timeout: Duration::from_millis(request.timeout_ms()),
            max_output_bytes: self.max_output_bytes,
        };
        let started = Instant::now();
        let outcome = run_process(
            "lane worker",
            &self.program,
            &self.cwd,
            &environment,
            &self.args,
            &limits,
        )?;
        let response_body = fs::read(&response_path).ok();
        let observation = if outcome.timed_out {
            ProcessObservation::TimedOut
        } else if let Some(number) = outcome.signal {
            ProcessObservation::Signaled { number }
        } else {
            ProcessObservation::Exited {
                code: outcome.exit_code.unwrap_or(1),
            }
        };
        Ok(LaneProcessResult {
            observation,
            response_body,
            duration_ms: u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX),
            detail: String::from_utf8_lossy(&outcome.stderr).into_owned(),
        })
    }
}

/// Runs every request, recording blocking evidence on failure and continuing.
pub fn run_lane<E: LaneExecutor>(
    executor: &mut E,
    requests: &[LaneRequest],
) -> Result<Vec<EvidenceRow>> {
    let mut rows = Vec::with_capacity(requests.len());
    for request in requests {
        let process = match executor.run(request) {
            Ok(process) => process,
            Err(error) => LaneProcessResult {
                observation: ProcessObservation::Exited { code: 1 },
                response_body: None,
                duration_ms: 0,
                detail: error.to_string(),
            },
        };
        rows.push(derive_row(request, process)?);
    }
    Ok(rows)
}

/// Parent-only derivation: workers cannot mint PASS.
pub fn derive_row(request: &LaneRequest, process: LaneProcessResult) -> Result<EvidenceRow> {
    let (state, artifacts, detail) = match process.observation {
        ProcessObservation::TimedOut => (
            TerminalState::Timeout,
            BTreeMap::new(),
            ignore_pass_attempt(process.response_body.as_deref(), "timeout"),
        ),
        ProcessObservation::Signaled { number } => (
            TerminalState::Signal,
            BTreeMap::new(),
            format!("worker signaled ({number}); {}", process.detail),
        ),
        ProcessObservation::Exited { code } if code != 0 => (
            TerminalState::WorkerCrash,
            BTreeMap::new(),
            format!("worker exited {code}; {}", process.detail),
        ),
        ProcessObservation::Exited { code: _ } => {
            match parse_response(process.response_body.as_deref()) {
                Err(detail) => (TerminalState::ProtocolError, BTreeMap::new(), detail),
                Ok(response) => derive_from_response(request, response),
            }
        }
    };
    EvidenceRow::new(
        request.key().clone(),
        request.argv.clone(),
        request.working_directory,
        request.observables().clone(),
        artifacts,
        state,
        process.duration_ms,
        detail,
    )
}

fn parse_response(body: Option<&[u8]>) -> std::result::Result<LaneResponse, String> {
    let Some(bytes) = body else {
        return Err("worker produced no response".to_owned());
    };
    let response = serde_json::from_slice::<LaneResponse>(bytes)
        .map_err(|error| format!("worker response is not a valid lane response: {error}"))?;
    response
        .validate()
        .map_err(|error| format!("worker response failed validation: {error}"))?;
    Ok(response)
}

fn derive_from_response(
    request: &LaneRequest,
    response: LaneResponse,
) -> (TerminalState, BTreeMap<String, String>, String) {
    if response.binding() != request.binding() {
        return (
            TerminalState::ProtocolError,
            BTreeMap::new(),
            "response lane binding does not match request".to_owned(),
        );
    }
    if response.request_id() != request.request_id() {
        return (
            TerminalState::ProtocolError,
            BTreeMap::new(),
            format!(
                "response request_id {} does not match request {}",
                response.request_id(),
                request.request_id()
            ),
        );
    }
    if response.key() != request.key() {
        return (
            TerminalState::ProtocolError,
            BTreeMap::new(),
            format!(
                "response key `{}` does not match request `{}`",
                response.key(),
                request.key()
            ),
        );
    }
    match response.outcome {
        LaneOutcome::Completed { artifacts } => {
            let declared = request.observables();
            let observed: BTreeSet<String> = artifacts.keys().cloned().collect();
            if &observed != declared {
                return (
                    TerminalState::ProtocolError,
                    BTreeMap::new(),
                    format!(
                        "observable set mismatch for `{}`: declared {declared:?}, observed {observed:?}",
                        request.key()
                    ),
                );
            }
            (TerminalState::Pass, artifacts, String::new())
        }
        LaneOutcome::BlockingFail { detail } => {
            (TerminalState::BlockingFail, BTreeMap::new(), detail)
        }
        LaneOutcome::Timeout { detail } => (TerminalState::Timeout, BTreeMap::new(), detail),
        LaneOutcome::InapplicableLanguageService { detail } => (
            TerminalState::InapplicableLanguageService,
            BTreeMap::new(),
            detail,
        ),
        LaneOutcome::InapplicableOutOfScopeHostFeature { detail } => (
            TerminalState::InapplicableOutOfScopeHostFeature,
            BTreeMap::new(),
            detail,
        ),
        LaneOutcome::InapplicableV8Internal { detail } => (
            TerminalState::InapplicableV8Internal,
            BTreeMap::new(),
            detail,
        ),
        LaneOutcome::InapplicableCatalogError { detail } => (
            TerminalState::InapplicableCatalogError,
            BTreeMap::new(),
            detail,
        ),
        LaneOutcome::ExternalBlocked { detail } => {
            (TerminalState::ExternalBlocked, BTreeMap::new(), detail)
        }
    }
}

fn ignore_pass_attempt(body: Option<&[u8]>, cause: &str) -> String {
    match parse_response(body) {
        Ok(response) if matches!(response.outcome(), LaneOutcome::Completed { .. }) => {
            format!("{cause}: ignoring completed/PASS attempt from a failed worker")
        }
        _ => cause.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ExecutionMode;
    use std::collections::BTreeMap;

    const TEST_RUN_ID: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const OTHER_RUN_ID: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    struct ScriptedExecutor {
        results: Vec<LaneProcessResult>,
        index: usize,
    }

    impl ScriptedExecutor {
        fn new(results: Vec<LaneProcessResult>) -> Self {
            Self { results, index: 0 }
        }
    }

    impl LaneExecutor for ScriptedExecutor {
        fn run(&mut self, _request: &LaneRequest) -> Result<LaneProcessResult> {
            let result = self.results.get(self.index).cloned().ok_or_else(|| {
                VerificationError::new(ErrorCode::Schema, "scripted executor exhausted")
            })?;
            self.index += 1;
            Ok(result)
        }
    }

    fn test_binding() -> LaneBinding {
        LaneBinding::unbound(TEST_RUN_ID).expect("binding")
    }

    fn key(mode: ExecutionMode, platform: &str, case: &str) -> ObligationKey {
        ObligationKey::new("typescript-7.0.2", case, "default", mode, platform).expect("key")
    }

    fn request(request_id: u64, key: ObligationKey) -> LaneRequest {
        LaneRequest::new(
            test_binding(),
            request_id,
            key,
            BTreeSet::from(["stdout".to_owned()]),
            vec!["lane".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            1_000,
        )
        .expect("request")
    }

    fn completed_body(
        binding: LaneBinding,
        request_id: u64,
        key: &ObligationKey,
        artifacts: BTreeMap<String, String>,
    ) -> Vec<u8> {
        let response = LaneResponse::new(
            binding,
            request_id,
            key.clone(),
            LaneOutcome::Completed { artifacts },
        )
        .expect("response");
        serde_json::to_vec(&response).expect("encode")
    }

    fn stdout_ok() -> BTreeMap<String, String> {
        BTreeMap::from([(
            "stdout".to_owned(),
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_owned(),
        )])
    }

    fn success(request_id: u64, key: &ObligationKey) -> LaneProcessResult {
        LaneProcessResult {
            observation: ProcessObservation::Exited { code: 0 },
            response_body: Some(completed_body(test_binding(), request_id, key, stdout_ok())),
            duration_ms: 3,
            detail: String::new(),
        }
    }

    #[test]
    fn parent_derives_pass_from_exact_response() {
        let good_key = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-0001",
        );
        let request = request(7, good_key.clone());
        let row = derive_row(&request, success(7, &good_key)).expect("derive");
        assert_eq!(row.state(), TerminalState::Pass);
        assert_eq!(row.key(), &good_key);
        assert_eq!(row.artifacts().len(), 1);

        let mismatches = [
            ("request_id", success(8, &good_key)),
            (
                "case",
                success(
                    7,
                    &key(
                        ExecutionMode::Interpreter,
                        "x86_64-unknown-linux-gnu",
                        "case-9999",
                    ),
                ),
            ),
            (
                "mode",
                success(
                    7,
                    &key(ExecutionMode::Jit, "x86_64-unknown-linux-gnu", "case-0001"),
                ),
            ),
            (
                "platform",
                success(
                    7,
                    &key(
                        ExecutionMode::Interpreter,
                        "aarch64-unknown-linux-gnu",
                        "case-0001",
                    ),
                ),
            ),
        ];
        for (name, process) in mismatches {
            let row = derive_row(&request, process).expect(name);
            assert_eq!(row.state(), TerminalState::ProtocolError, "{name}");
            assert_ne!(row.state(), TerminalState::Pass, "{name}");
        }

        let mut extras = stdout_ok();
        extras.insert(
            "stderr".to_owned(),
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_owned(),
        );
        let wrong_obs = LaneProcessResult {
            observation: ProcessObservation::Exited { code: 0 },
            response_body: Some(completed_body(test_binding(), 7, &good_key, extras)),
            duration_ms: 3,
            detail: String::new(),
        };
        let row = derive_row(&request, wrong_obs).expect("observables");
        assert_eq!(row.state(), TerminalState::ProtocolError);
    }

    #[test]
    fn parent_rejects_run_and_snapshot_replay() {
        let good_key = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-0001",
        );
        let catalog = "typescript-7.0.2";
        let root = PathBuf::from("/canonical/ts-suite");
        let pin = b"pin";
        let index = b"index";
        let ledger = b"ledger";
        let bound = test_binding()
            .with_snapshot(catalog, &root, pin, index, ledger)
            .expect("bound");
        let request = LaneRequest::new(
            bound.clone(),
            1,
            good_key.clone(),
            BTreeSet::from(["stdout".to_owned()]),
            vec!["lane".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            1_000,
        )
        .expect("request");

        let wrong_run = LaneBinding::unbound(OTHER_RUN_ID)
            .expect("other run")
            .with_snapshot(catalog, &root, pin, index, ledger)
            .expect("other bound");
        let replay_run = LaneProcessResult {
            observation: ProcessObservation::Exited { code: 0 },
            response_body: Some(completed_body(wrong_run, 1, &good_key, stdout_ok())),
            duration_ms: 3,
            detail: String::new(),
        };
        let row = derive_row(&request, replay_run).expect("run replay");
        assert_eq!(row.state(), TerminalState::ProtocolError);
        assert_ne!(row.state(), TerminalState::Pass);

        let swapped = test_binding()
            .with_snapshot(catalog, &root, b"other-pin", index, ledger)
            .expect("swapped metadata");
        let replay_snapshot = LaneProcessResult {
            observation: ProcessObservation::Exited { code: 0 },
            response_body: Some(completed_body(swapped, 1, &good_key, stdout_ok())),
            duration_ms: 3,
            detail: String::new(),
        };
        let row = derive_row(&request, replay_snapshot).expect("snapshot replay");
        assert_eq!(row.state(), TerminalState::ProtocolError);
        assert_ne!(row.state(), TerminalState::Pass);
    }

    #[test]
    fn snapshot_binding_matches_retained_bytes_not_sha256_alone() {
        let root = PathBuf::from("/canonical/ts-suite");
        let bound = test_binding()
            .with_snapshot("typescript-7.0.2", &root, b"pin", b"index", b"ledger")
            .expect("bound");
        bound
            .verify_snapshot("typescript-7.0.2", &root, b"pin", b"index", b"ledger")
            .expect("identity");
        let error = bound
            .verify_snapshot("typescript-7.0.2", &root, b"pin-swap", b"index", b"ledger")
            .expect_err("metadata swap");
        assert_eq!(error.code(), ErrorCode::ProvenanceMismatch);
        let relative = bound
            .clone()
            .with_snapshot(
                "typescript-7.0.2",
                Path::new("verification/ts-suite"),
                b"pin",
                b"index",
                b"ledger",
            )
            .expect_err("relative root");
        assert_eq!(relative.code(), ErrorCode::Schema);
    }

    #[test]
    fn records_failure_and_continues() {
        let keys: Vec<ObligationKey> = (1..=5)
            .map(|index| {
                key(
                    ExecutionMode::Interpreter,
                    "x86_64-unknown-linux-gnu",
                    &format!("case-{index:04}"),
                )
            })
            .collect();
        let requests: Vec<LaneRequest> = keys
            .iter()
            .enumerate()
            .map(|(index, item)| request((index as u64) + 1, item.clone()))
            .collect();
        let timeout = LaneProcessResult {
            observation: ProcessObservation::TimedOut,
            response_body: Some(completed_body(test_binding(), 1, &keys[0], stdout_ok())),
            duration_ms: 200,
            detail: "timeout".to_owned(),
        };
        let signaled = LaneProcessResult {
            observation: ProcessObservation::Signaled { number: 9 },
            response_body: None,
            duration_ms: 1,
            detail: "killed".to_owned(),
        };
        let protocol = LaneProcessResult {
            observation: ProcessObservation::Exited { code: 0 },
            response_body: None,
            duration_ms: 1,
            detail: String::new(),
        };
        let crash = LaneProcessResult {
            observation: ProcessObservation::Exited { code: 1 },
            response_body: None,
            duration_ms: 1,
            detail: "boom".to_owned(),
        };
        let mut executor = ScriptedExecutor::new(vec![
            timeout,
            signaled,
            protocol,
            crash,
            success(5, &keys[4]),
        ]);
        let rows = run_lane(&mut executor, &requests).expect("lane");
        assert_eq!(rows.len(), 5);
        assert_eq!(rows[0].state(), TerminalState::Timeout);
        assert_eq!(rows[1].state(), TerminalState::Signal);
        assert_eq!(rows[2].state(), TerminalState::ProtocolError);
        assert_eq!(rows[3].state(), TerminalState::WorkerCrash);
        assert_eq!(rows[4].state(), TerminalState::Pass);
        assert!(
            rows.iter()
                .take(4)
                .all(|row| row.state() != TerminalState::Pass)
        );
    }

    #[test]
    fn process_executor_reuses_corpus_timeout() {
        let scratch = std::env::temp_dir().join(format!(
            "bamts-lane-timeout-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(&scratch).expect("scratch");
        let mut executor =
            ProcessExecutor::new("/bin/sleep", vec![OsString::from("2")], "/", &scratch)
                .with_max_output_bytes(64);
        let item = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-sleep",
        );
        let request = LaneRequest::new(
            test_binding(),
            1,
            item,
            BTreeSet::from(["stdout".to_owned()]),
            vec!["sleep".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            200,
        )
        .expect("short timeout");
        let result = executor.run(&request).expect("run");
        let request_path = scratch.join(format!("lane-{TEST_RUN_ID}-1.json"));
        assert!(request_path.is_file(), "{}", request_path.display());
        let _ = fs::remove_dir_all(&scratch);
        assert!(matches!(result.observation, ProcessObservation::TimedOut));
    }

    #[test]
    fn process_executor_records_elapsed_completion_time() {
        let scratch = std::env::temp_dir().join(format!(
            "bamts-lane-duration-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(&scratch).expect("scratch");
        let mut executor = ProcessExecutor::new("/usr/bin/true", Vec::new(), "/", &scratch)
            .with_max_output_bytes(64);
        let request = request(
            1,
            key(
                ExecutionMode::Interpreter,
                "x86_64-unknown-linux-gnu",
                "case-duration",
            ),
        );
        let result = executor.run(&request).expect("run");
        let _ = fs::remove_dir_all(&scratch);
        assert!(matches!(
            result.observation,
            ProcessObservation::Exited { code: 0 }
        ));
        assert!(result.duration_ms < request.timeout_ms());
    }

    #[test]
    fn process_executor_refuses_retained_response() {
        let scratch = std::env::temp_dir().join(format!(
            "bamts-lane-replay-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(&scratch).expect("scratch");
        let retained = scratch.join(format!("lane-{TEST_RUN_ID}-1.response.json"));
        fs::write(&retained, b"stale").expect("retained response");
        let mut executor = ProcessExecutor::new("/usr/bin/true", Vec::new(), "/", &scratch)
            .with_max_output_bytes(64);
        let item = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-replay",
        );
        let request = request(1, item);
        let error = executor.run(&request).expect_err("retained response");
        let _ = fs::remove_dir_all(&scratch);
        assert_eq!(error.code(), ErrorCode::Replay);
    }

    #[test]
    fn fresh_bindings_are_unpredictable() {
        let first = LaneBinding::fresh().expect("first");
        let second = LaneBinding::fresh().expect("second");
        assert_ne!(first.run_id(), second.run_id());
        assert_eq!(first.run_id().len(), 64);
        assert!(!first.has_snapshot());
    }
}
