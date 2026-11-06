//! Lane request/response protocol and parent-only PASS derivation.
//!
//! Workers never mint `PASS`.  They return a completed observation or a closed
//! non-pass outcome.  The parent records `PASS` only when the run binding,
//! key (case, mode, platform), and observable set match exactly.  Timeout,
//! signal, protocol error, and worker crash become blocking receipts, and the
//! lane continues with later cases.  Process execution reuses the corpus
//! normalized environment, bounded pipe drain, process-group timeout, and
//! whole-group termination.  [`ProcessExecutor`] starts one worker per
//! request; [`ServingExecutor`] keeps one worker for many requests and records
//! a worker that exits or misses a deadline the way [`ProcessExecutor`] does.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::{BufRead, BufReader, ErrorKind, Read, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{
        Arc, Mutex, PoisonError,
        mpsc::{self, Receiver, RecvTimeoutError},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::{
        OracleLimits, forward_host_runtime_env, normalized_env, pipe_error, run_process,
        spawn_error, terminate_process_group, termination_signal, thread_error, wait_error,
    },
    evidence::{EvidenceRow, TerminalState, WorkingDirectoryPolicy},
    shard::{ObligationKey, require_token},
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Environment variable naming the worker request JSON path.
pub const LANE_WORKER_REQUEST: &str = "BAMTS_LANE_WORKER_REQUEST";

/// Environment variable that asks a lane worker to answer one request path per
/// line of standard input, instead of the one request in [`LANE_WORKER_REQUEST`].
pub const LANE_WORKER_SERVE: &str = "BAMTS_LANE_WORKER_SERVE";

/// The first line a serving worker prints, before it reads any request.
pub const LANE_WORKER_READY: &str = "bamts-lane-worker ready 1";

/// What a serving worker prints, followed by a space and the request ID, once
/// it has written the response to that request.
pub const LANE_WORKER_DONE: &str = "bamts-lane-worker done";

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
    /// The same request for another key, keeping its run binding and identity.
    pub fn with_key(&self, key: ObligationKey) -> Result<Self> {
        Self::new(
            self.binding.clone(),
            self.request_id,
            key,
            self.observables.clone(),
            self.argv.clone(),
            self.working_directory,
            self.timeout_ms,
        )
    }

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
    /// Completed, with the result measured on another cell. Derives the same
    /// row as [`Self::Completed`], and the row records `source`.
    Reused {
        artifacts: BTreeMap<String, String>,
        source: String,
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
    Exited {
        code: i32,
    },
    TimedOut,
    Signaled {
        number: i32,
    },
    /// A serving worker said that it wrote the response, and keeps running.
    Answered,
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

/// Writes `request` where its worker reads it, and returns the request and the
/// response paths. A response that an earlier run left behind is refused.
fn write_request_file(work_dir: &Path, request: &LaneRequest) -> Result<(PathBuf, PathBuf)> {
    request.validate()?;
    fs::create_dir_all(work_dir).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", work_dir.display()))
    })?;
    let request_path = work_dir.join(format!(
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
    Ok((request_path, response_path))
}

/// The environment of every lane worker: the normalized corpus environment and `PATH`.
fn worker_environment() -> Vec<(String, String)> {
    let mut environment = normalized_env();
    if let Ok(path) = std::env::var("PATH") {
        environment.push(("PATH".to_owned(), path));
    }
    environment
}

impl LaneExecutor for ProcessExecutor {
    fn run(&mut self, request: &LaneRequest) -> Result<LaneProcessResult> {
        let (request_path, response_path) = write_request_file(&self.work_dir, request)?;
        let mut environment = worker_environment();
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

const SERVING_LABEL: &str = "serving lane worker";

/// How long a serving worker may take to exit after its input closes.
const SERVING_STOP_GRACE: Duration = Duration::from_secs(5);

/// How often a serving worker that is stopping is asked whether it has exited.
const SERVING_STOP_POLL: Duration = Duration::from_millis(5);

/// How much of one output line of a serving worker the parent keeps. The protocol
/// lines are far shorter, and the rest of the output is read only to be skipped.
const SERVING_LINE_BYTES: usize = 4096;

/// Reads one line into `line`, of which at most [`SERVING_LINE_BYTES`] are kept, so
/// a worker that prints without a line end cannot grow the memory of the parent.
/// Returns `false` when the output has ended or cannot be read.
fn read_bounded_line(reader: &mut impl BufRead, line: &mut Vec<u8>) -> bool {
    line.clear();
    loop {
        let available = match reader.fill_buf() {
            Ok(available) => available,
            Err(error) if error.kind() == ErrorKind::Interrupted => continue,
            Err(_) => return false,
        };
        if available.is_empty() {
            return !line.is_empty();
        }
        let end = available.iter().position(|byte| *byte == b'\n');
        let text = &available[..end.unwrap_or(available.len())];
        let room = SERVING_LINE_BYTES.saturating_sub(line.len());
        line.extend_from_slice(&text[..text.len().min(room)]);
        let read = end.map_or(available.len(), |end| end + 1);
        reader.consume(read);
        if end.is_some() {
            return true;
        }
    }
}

/// Sends every request to one long-lived worker that serves requests (see
/// [`LANE_WORKER_SERVE`]). The worker starts with the first request, and each
/// request has its own deadline. A worker that exits, or misses a deadline and
/// is terminated, gives its request the observation that [`ProcessExecutor`]
/// gives such a worker, and the next request starts a new worker. Environment,
/// process group, and termination are those of [`ProcessExecutor`].
#[derive(Debug)]
pub struct ServingExecutor {
    program: PathBuf,
    args: Vec<OsString>,
    cwd: PathBuf,
    work_dir: PathBuf,
    max_output_bytes: usize,
    worker: Option<ServingWorker>,
    workers_started: u64,
}

impl ServingExecutor {
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
            worker: None,
            workers_started: 0,
        }
    }

    /// Bounds the standard error kept for one request.
    pub fn with_max_output_bytes(mut self, cap: usize) -> Self {
        self.max_output_bytes = cap;
        self
    }

    /// How many worker processes this executor has started.
    #[must_use]
    pub fn workers_started(&self) -> u64 {
        self.workers_started
    }

    fn start_worker(&mut self) -> Result<ServingWorker> {
        let mut command = Command::new(&self.program);
        command.env_clear();
        for (key, value) in worker_environment() {
            command.env(key, value);
        }
        command.env(LANE_WORKER_SERVE, "1");
        forward_host_runtime_env(&mut command);
        command
            .current_dir(&self.cwd)
            .args(&self.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        let mut child = command
            .spawn()
            .map_err(|error| spawn_error(SERVING_LABEL, &self.program, &error))?;
        self.workers_started += 1;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| pipe_error(SERVING_LABEL, "stdin"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| pipe_error(SERVING_LABEL, "stdout"))?;
        let stderr = child
            .stderr
            .take()
            .ok_or_else(|| pipe_error(SERVING_LABEL, "stderr"))?;
        let (sender, lines) = mpsc::channel();
        let line_reader = thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            let mut line = Vec::new();
            while read_bounded_line(&mut reader, &mut line) {
                let text = String::from_utf8_lossy(&line).trim_end().to_owned();
                if sender.send(text).is_err() {
                    break;
                }
            }
        });
        let captured = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&captured);
        let cap = self.max_output_bytes;
        let stderr_reader = thread::spawn(move || {
            let mut stderr = stderr;
            let mut chunk = [0_u8; 8192];
            loop {
                match stderr.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(read) => {
                        let mut kept = sink.lock().unwrap_or_else(PoisonError::into_inner);
                        let room = cap.saturating_sub(kept.len());
                        kept.extend_from_slice(&chunk[..read.min(room)]);
                    }
                    Err(error) if error.kind() == ErrorKind::Interrupted => {}
                    Err(_) => break,
                }
            }
        });
        Ok(ServingWorker {
            child,
            stdin,
            lines,
            stderr: captured,
            readers: [line_reader, stderr_reader],
        })
    }

    /// Drops the idle worker if it exited after its last request, for example
    /// because something outside killed it. Under [`ProcessExecutor`] each request
    /// has a new process, so the next request starts a new worker rather than
    /// being blamed for an exit that happened while no request was running.
    fn retire_exited_worker(&mut self) -> Result<()> {
        let Some(mut worker) = self.worker.take() else {
            return Ok(());
        };
        match worker.child.try_wait() {
            Ok(None) => {
                self.worker = Some(worker);
                Ok(())
            }
            Ok(Some(_)) => {
                worker.stop();
                Ok(())
            }
            Err(error) => {
                worker.stop();
                Err(wait_error(SERVING_LABEL, error))
            }
        }
    }
}

impl LaneExecutor for ServingExecutor {
    fn run(&mut self, request: &LaneRequest) -> Result<LaneProcessResult> {
        let (request_path, response_path) = write_request_file(&self.work_dir, request)?;
        self.retire_exited_worker()?;
        let started = Instant::now();
        let deadline = started + Duration::from_millis(request.timeout_ms());
        let mut worker = match self.worker.take() {
            Some(worker) => worker,
            None => {
                let worker = self.start_worker()?;
                match worker.await_line(|line| line == LANE_WORKER_READY, deadline) {
                    Heard::Line => worker,
                    heard => return worker.finish(heard, deadline, &response_path, started),
                }
            }
        };
        worker.clear_stderr();
        let sent = writeln!(worker.stdin, "{}", request_path.to_string_lossy())
            .and_then(|()| worker.stdin.flush());
        let heard = if sent.is_err() {
            Heard::Ended
        } else {
            let done = format!("{LANE_WORKER_DONE} {}", request.request_id());
            worker.await_line(|line| line == done, deadline)
        };
        if heard != Heard::Line {
            return worker.finish(heard, deadline, &response_path, started);
        }
        let result = LaneProcessResult {
            observation: ProcessObservation::Answered,
            response_body: fs::read(&response_path).ok(),
            duration_ms: elapsed_ms(started),
            detail: worker.stderr_text(),
        };
        self.worker = Some(worker);
        Ok(result)
    }
}

impl Drop for ServingExecutor {
    fn drop(&mut self) {
        if let Some(worker) = self.worker.take() {
            worker.stop();
        }
    }
}

/// What a serving worker did while the parent waited for one line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Heard {
    /// It printed the line.
    Line,
    /// Its output ended, because it exited or closed it.
    Ended,
    /// The deadline passed first.
    Late,
}

/// One running serving worker and the threads that read its output.
#[derive(Debug)]
struct ServingWorker {
    child: Child,
    stdin: ChildStdin,
    lines: Receiver<String>,
    stderr: Arc<Mutex<Vec<u8>>>,
    readers: [JoinHandle<()>; 2],
}

impl ServingWorker {
    /// Waits for a line that `expected` accepts. Other lines are output of the
    /// work itself, which a one-request worker also prints and nobody reads.
    fn await_line(&self, expected: impl Fn(&str) -> bool, deadline: Instant) -> Heard {
        loop {
            let left = deadline.saturating_duration_since(Instant::now());
            match self.lines.recv_timeout(left) {
                Ok(line) if expected(&line) => return Heard::Line,
                Ok(_) => {}
                Err(RecvTimeoutError::Timeout) => return Heard::Late,
                Err(RecvTimeoutError::Disconnected) => return Heard::Ended,
            }
        }
    }

    fn clear_stderr(&self) {
        self.stderr
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }

    fn stderr_text(&self) -> String {
        String::from_utf8_lossy(&self.stderr.lock().unwrap_or_else(PoisonError::into_inner))
            .into_owned()
    }

    /// Ends a worker that exited or missed the deadline, and records its request
    /// the way [`ProcessExecutor`] records a worker that did the same.
    fn finish(
        mut self,
        heard: Heard,
        deadline: Instant,
        response_path: &Path,
        started: Instant,
    ) -> Result<LaneProcessResult> {
        let mut timed_out = heard == Heard::Late;
        // A worker whose output ended is exiting, and it has to exit by the deadline.
        while !timed_out
            && self
                .child
                .try_wait()
                .map_err(|error| wait_error(SERVING_LABEL, error))?
                .is_none()
        {
            if Instant::now() >= deadline {
                timed_out = true;
            } else {
                thread::sleep(SERVING_STOP_POLL);
            }
        }
        let termination_error = if timed_out {
            terminate_process_group(&mut self.child, SERVING_LABEL).err()
        } else {
            None
        };
        let status = self
            .child
            .wait()
            .map_err(|error| wait_error(SERVING_LABEL, error))?;
        drop(self.stdin);
        let [line_reader, stderr_reader] = self.readers;
        line_reader
            .join()
            .map_err(|_| thread_error(SERVING_LABEL, "stdout"))?;
        stderr_reader
            .join()
            .map_err(|_| thread_error(SERVING_LABEL, "stderr"))?;
        if let Some(error) = termination_error {
            return Err(error);
        }
        let observation = if timed_out {
            ProcessObservation::TimedOut
        } else if let Some(number) = termination_signal(&status) {
            ProcessObservation::Signaled { number }
        } else {
            ProcessObservation::Exited {
                code: status.code().unwrap_or(1),
            }
        };
        let detail =
            String::from_utf8_lossy(&self.stderr.lock().unwrap_or_else(PoisonError::into_inner))
                .into_owned();
        Ok(LaneProcessResult {
            observation,
            response_body: fs::read(response_path).ok(),
            duration_ms: elapsed_ms(started),
            detail,
        })
    }

    /// Closes the worker's input, so it ends its loop and exits. A worker that
    /// does not exit within [`SERVING_STOP_GRACE`] is terminated.
    fn stop(mut self) {
        drop(self.stdin);
        let deadline = Instant::now() + SERVING_STOP_GRACE;
        loop {
            match self.child.try_wait() {
                Ok(Some(_)) => break,
                Ok(None) if Instant::now() < deadline => thread::sleep(SERVING_STOP_POLL),
                _ => {
                    let _ = terminate_process_group(&mut self.child, SERVING_LABEL);
                    let _ = self.child.wait();
                    break;
                }
            }
        }
        for reader in self.readers {
            let _ = reader.join();
        }
    }
}

fn elapsed_ms(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
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
        ProcessObservation::Exited { code: _ } | ProcessObservation::Answered => {
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

fn derive_pass(
    request: &LaneRequest,
    artifacts: BTreeMap<String, String>,
    detail: String,
) -> (TerminalState, BTreeMap<String, String>, String) {
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
    (TerminalState::Pass, artifacts, detail)
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
        LaneOutcome::Completed { artifacts } => derive_pass(request, artifacts, String::new()),
        LaneOutcome::Reused { artifacts, source } => {
            derive_pass(request, artifacts, format!("reused {source}"))
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
        Ok(response)
            if matches!(
                response.outcome(),
                LaneOutcome::Completed { .. } | LaneOutcome::Reused { .. }
            ) =>
        {
            format!("{cause}: ignoring completed/PASS attempt from a failed worker")
        }
        _ => cause.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ExecutionMode;
    use crate::test_programs::windows_system_program;
    use std::collections::BTreeMap;

    const TEST_RUN_ID: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const OTHER_RUN_ID: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    /// A fixture path written the Unix way, on the drive Windows needs to call it absolute.
    fn abs(unix: &str) -> PathBuf {
        if cfg!(windows) {
            PathBuf::from(format!("C:{}", unix.replace('/', "\\")))
        } else {
            PathBuf::from(unix)
        }
    }

    /// A worker that outlives a 200 ms timeout: `sleep 2` on Unix, and on Windows
    /// `ping` with three echoes, which are one second apart.
    fn sleeping_worker() -> (PathBuf, Vec<OsString>) {
        if cfg!(windows) {
            let ping = windows_system_program("PING.EXE");
            let args = ["-n", "3", "127.0.0.1"].map(OsString::from).to_vec();
            (ping, args)
        } else {
            (PathBuf::from("/bin/sleep"), vec![OsString::from("2")])
        }
    }

    /// A worker that exits with status 0 at once.
    fn instant_worker() -> (PathBuf, Vec<OsString>) {
        if cfg!(windows) {
            let args = ["/C", "exit", "0"].map(OsString::from).to_vec();
            (windows_system_program("cmd.exe"), args)
        } else {
            (PathBuf::from("/usr/bin/true"), Vec::new())
        }
    }

    /// A serving worker that says it is ready and then runs `then`, a shell
    /// command that is the same in `cmd.exe` and `sh`.
    fn ready_worker(then: &str) -> (PathBuf, Vec<OsString>) {
        if cfg!(windows) {
            let script = format!("echo {LANE_WORKER_READY}&{then}");
            let args = vec![OsString::from("/C"), OsString::from(script)];
            (windows_system_program("cmd.exe"), args)
        } else {
            let script = format!("echo '{LANE_WORKER_READY}'; {then}");
            let args = vec![OsString::from("-c"), OsString::from(script)];
            (PathBuf::from("/bin/sh"), args)
        }
    }

    fn scratch_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "bamts-lane-{label}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(&dir).expect("scratch");
        dir
    }

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

    fn reused(
        observation: ProcessObservation,
        key: &ObligationKey,
        artifacts: BTreeMap<String, String>,
    ) -> LaneProcessResult {
        let outcome = LaneOutcome::Reused {
            artifacts,
            source: "a twin cell".to_owned(),
        };
        let response =
            LaneResponse::new(test_binding(), 7, key.clone(), outcome).expect("response");
        LaneProcessResult {
            observation,
            response_body: Some(serde_json::to_vec(&response).expect("encode")),
            duration_ms: 3,
            detail: String::new(),
        }
    }

    #[test]
    fn a_reused_result_passes_and_its_row_names_the_source() {
        let good_key = key(ExecutionMode::Aot, "x86_64-unknown-linux-gnu", "case-0001");
        let request = request(7, good_key.clone());
        let exited = ProcessObservation::Exited { code: 0 };

        let row =
            derive_row(&request, reused(exited.clone(), &good_key, stdout_ok())).expect("derive");
        assert_eq!(row.state(), TerminalState::Pass);
        assert_eq!(row.detail(), "reused a twin cell");

        let row = derive_row(&request, reused(exited, &good_key, BTreeMap::new())).expect("derive");
        assert_eq!(
            row.state(),
            TerminalState::ProtocolError,
            "observables still bind"
        );

        let late = reused(ProcessObservation::TimedOut, &good_key, stdout_ok());
        let row = derive_row(&request, late).expect("derive");
        assert_eq!(
            row.state(),
            TerminalState::Timeout,
            "a late pass is not a pass"
        );
        assert!(row.detail().contains("ignoring"), "{}", row.detail());
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
        let root = abs("/canonical/ts-suite");
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
        let root = abs("/canonical/ts-suite");
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
        let (program, args) = sleeping_worker();
        let mut executor =
            ProcessExecutor::new(program, args, abs("/"), &scratch).with_max_output_bytes(64);
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
        let (program, args) = instant_worker();
        let mut executor =
            ProcessExecutor::new(program, args, abs("/"), &scratch).with_max_output_bytes(64);
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
        let (program, args) = instant_worker();
        let mut executor =
            ProcessExecutor::new(program, args, abs("/"), &scratch).with_max_output_bytes(64);
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
    fn a_long_line_of_a_serving_worker_is_cut_and_the_next_line_is_kept() {
        let long = "x".repeat(SERVING_LINE_BYTES * 3);
        let output = format!("{long}\n{LANE_WORKER_DONE} 1\r\nlast");
        let mut reader = BufReader::with_capacity(16, output.as_bytes());
        let mut line = Vec::new();

        assert!(read_bounded_line(&mut reader, &mut line));
        assert_eq!(line.len(), SERVING_LINE_BYTES);
        assert!(read_bounded_line(&mut reader, &mut line));
        assert_eq!(
            String::from_utf8_lossy(&line).trim_end(),
            format!("{LANE_WORKER_DONE} 1")
        );
        // Output that ends without a line end is still a line.
        assert!(read_bounded_line(&mut reader, &mut line));
        assert_eq!(line, b"last");
        assert!(!read_bounded_line(&mut reader, &mut line));
    }

    #[test]
    fn a_serving_worker_that_exits_is_recorded_like_an_exiting_worker_and_replaced() {
        let scratch = scratch_dir("serving-exit");
        let (program, args) = ready_worker("exit 3");
        let mut executor =
            ServingExecutor::new(program, args, &scratch, &scratch).with_max_output_bytes(64);
        let mode = ExecutionMode::Interpreter;
        let platform = "x86_64-unknown-linux-gnu";
        let first = executor
            .run(&request(1, key(mode, platform, "case-first")))
            .expect("first");
        let second = executor
            .run(&request(2, key(mode, platform, "case-second")))
            .expect("second");
        let started = executor.workers_started();
        drop(executor);
        let _ = fs::remove_dir_all(&scratch);
        assert_eq!(first.observation, ProcessObservation::Exited { code: 3 });
        assert_eq!(second.observation, ProcessObservation::Exited { code: 3 });
        assert_eq!(started, 2, "each request after an exit starts a new worker");
        let row = derive_row(&request(1, key(mode, platform, "case-first")), first).expect("row");
        assert_eq!(row.state(), TerminalState::WorkerCrash);
    }

    #[test]
    fn a_serving_worker_that_exited_while_idle_is_replaced_and_not_blamed() {
        let scratch = scratch_dir("serving-idle-exit");
        // A worker that said it was ready and then exited with 9 while it had no
        // request, as one that something outside kills between two requests.
        let (program, args) = ready_worker("exit 9");
        let mut other = ServingExecutor::new(program, args, &scratch, &scratch);
        let mut idle = other.start_worker().expect("worker");
        let ready = idle.await_line(
            |line| line == LANE_WORKER_READY,
            Instant::now() + Duration::from_secs(10),
        );
        assert_eq!(ready, Heard::Line);
        idle.child.wait().expect("the idle worker exits");
        let (program, args) = ready_worker("exit 3");
        let mut executor = ServingExecutor::new(program, args, &scratch, &scratch);
        executor.worker = Some(idle);
        let item = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-after-idle-exit",
        );
        let result = executor.run(&request(1, item)).expect("run");
        let started = executor.workers_started();
        drop(executor);
        drop(other);
        let _ = fs::remove_dir_all(&scratch);
        assert_eq!(
            result.observation,
            ProcessObservation::Exited { code: 3 },
            "the request runs on a new worker, not the one that exited with 9"
        );
        assert_eq!(started, 1);
    }

    #[test]
    fn a_serving_worker_that_misses_the_deadline_is_terminated_and_times_out() {
        let scratch = scratch_dir("serving-timeout");
        let (program, args) = ready_worker(if cfg!(windows) {
            "ping -n 3 127.0.0.1>NUL"
        } else {
            "sleep 2"
        });
        let mut executor =
            ServingExecutor::new(program, args, &scratch, &scratch).with_max_output_bytes(64);
        let request = LaneRequest::new(
            test_binding(),
            1,
            key(
                ExecutionMode::Interpreter,
                "x86_64-unknown-linux-gnu",
                "case-silent",
            ),
            BTreeSet::from(["stdout".to_owned()]),
            vec!["lane".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            200,
        )
        .expect("short timeout");
        let result = executor.run(&request).expect("run");
        drop(executor);
        let _ = fs::remove_dir_all(&scratch);
        assert_eq!(result.observation, ProcessObservation::TimedOut);
        let row = derive_row(&request, result).expect("row");
        assert_eq!(row.state(), TerminalState::Timeout);
    }

    #[test]
    fn a_serving_executor_refuses_a_retained_response() {
        let scratch = scratch_dir("serving-replay");
        let retained = scratch.join(format!("lane-{TEST_RUN_ID}-1.response.json"));
        fs::write(&retained, b"stale").expect("retained response");
        let (program, args) = ready_worker("exit 0");
        let mut executor = ServingExecutor::new(program, args, &scratch, &scratch);
        let item = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-replay",
        );
        let error = executor
            .run(&request(1, item))
            .expect_err("retained response");
        let started = executor.workers_started();
        drop(executor);
        let _ = fs::remove_dir_all(&scratch);
        assert_eq!(error.code(), ErrorCode::Replay);
        assert_eq!(started, 0, "a refused request starts no worker");
    }

    #[test]
    fn an_answered_request_derives_its_row_from_the_response() {
        let item = key(
            ExecutionMode::Interpreter,
            "x86_64-unknown-linux-gnu",
            "case-answered",
        );
        let answered = LaneProcessResult {
            observation: ProcessObservation::Answered,
            ..success(1, &item)
        };
        let row = derive_row(&request(1, item.clone()), answered).expect("row");
        let exited = derive_row(&request(1, item.clone()), success(1, &item)).expect("row");
        assert_eq!(row.state(), TerminalState::Pass);
        assert_eq!(row, exited);
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
