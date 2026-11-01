//! One-shot GitHub Actions JIT runner provisioning for the trusted BH1 host.

use std::{
    env,
    ffi::OsStr,
    fmt,
    fs::{self, File, OpenOptions, Permissions},
    io::{self, Read, Write},
    os::unix::{
        fs::{MetadataExt, OpenOptionsExt, PermissionsExt},
        io::AsRawFd,
        process::CommandExt,
    },
    path::{Component, Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    str::FromStr,
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, Instant},
};

use serde::Deserialize;
use sha2::{Digest, Sha256};

const API_VERSION: &str = "2026-03-10";
const ACCEPT: &str = "Accept: application/vnd.github+json";
const RUNNER_VERSION: &str = "2.336.0";
const RUNNER_FILENAME: &str = "actions-runner-linux-x64-2.336.0.tar.gz";
const RUNNER_URL: &str = "https://github.com/actions/runner/releases/download/v2.336.0/actions-runner-linux-x64-2.336.0.tar.gz";
const RUNNER_SHA256: &str = "04cf0be1aff4c3ec3554466c39124ca250e3effd8873bb7e8d68535aa9505d5d";
const MAX_API_BYTES: usize = 8 * 1024 * 1024;
const MAX_DOWNLOAD_BYTES: usize = 512 * 1024 * 1024;
#[cfg(any(target_os = "linux", test))]
const MAX_JIT_BYTES: usize = 1024 * 1024;
const WORKFLOW_PATH: &str = ".github/workflows/ci.yml";
const PERF_JOB: &str = "perf-bh1";
const ASSIGNMENT_TIMEOUT: Duration = Duration::from_secs(10 * 60);
const COMPLETION_TIMEOUT: Duration = Duration::from_secs(130 * 60);
const CHILD_EXIT_TIMEOUT: Duration = Duration::from_secs(5 * 60);
const DISAPPEAR_TIMEOUT: Duration = Duration::from_secs(60);
const ASSIGNMENT_POLL: Duration = Duration::from_secs(5);
const COMPLETION_POLL: Duration = Duration::from_secs(15);
static INTERRUPTED: AtomicBool = AtomicBool::new(false);

pub type Result<T, E = JitError> = std::result::Result<T, E>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JitErrorCode {
    Usage,
    Precondition,
    Validation,
    Race,
    Provision,
    RunnerFailed,
    Cleanup,
    Interrupted,
}

impl JitErrorCode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Usage => "JIT_USAGE",
            Self::Precondition => "JIT_PRECONDITION",
            Self::Validation => "JIT_VALIDATION",
            Self::Race => "JIT_RACE",
            Self::Provision => "JIT_PROVISION",
            Self::RunnerFailed => "JIT_RUNNER_FAILED",
            Self::Cleanup => "JIT_CLEANUP",
            Self::Interrupted => "JIT_INTERRUPTED",
        }
    }

    pub const fn exit_code(self) -> i32 {
        match self {
            Self::Usage => 2,
            Self::Precondition => 3,
            Self::Validation => 4,
            Self::Race => 5,
            Self::Provision => 6,
            Self::RunnerFailed => 7,
            Self::Cleanup => 8,
            Self::Interrupted => 130,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitError {
    pub code: JitErrorCode,
    detail: String,
}

impl JitError {
    pub fn new(code: JitErrorCode, detail: impl Into<String>) -> Self {
        Self {
            code,
            detail: detail.into(),
        }
    }

    pub fn usage(detail: impl Into<String>) -> Self {
        Self::new(JitErrorCode::Usage, detail)
    }
}

impl fmt::Display for JitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code.as_str(), self.detail)
    }
}

impl std::error::Error for JitError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RepoName {
    owner: String,
    name: String,
}

impl RepoName {
    pub fn owner(&self) -> &str {
        &self.owner
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    fn full_name(&self) -> String {
        format!("{}/{}", self.owner, self.name)
    }
    fn api(&self, suffix: &str) -> String {
        format!("repos/{}/{}/{}", self.owner, self.name, suffix)
    }
}

impl FromStr for RepoName {
    type Err = JitError;

    fn from_str(value: &str) -> Result<Self> {
        let (owner, name) = value
            .split_once('/')
            .ok_or_else(|| JitError::usage("--repo must be owner/name"))?;
        if name.contains('/') || !valid_repo_part(owner) || !valid_repo_part(name) {
            return Err(JitError::usage(
                "--repo must contain two non-empty GitHub name components",
            ));
        }
        Ok(Self {
            owner: owner.to_owned(),
            name: name.to_owned(),
        })
    }
}

fn valid_repo_part(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PullRequestNumber(pub u64);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunId(pub u64);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attempt(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunnerGroupId(pub u64);

macro_rules! positive_number {
    ($type:ty, $name:literal) => {
        impl FromStr for $type {
            type Err = JitError;
            fn from_str(value: &str) -> Result<Self> {
                let number = value
                    .parse()
                    .map_err(|_| JitError::usage(concat!($name, " must be a positive integer")))?;
                if number == 0 {
                    return Err(JitError::usage(concat!(
                        $name,
                        " must be a positive integer"
                    )));
                }
                Ok(Self(number))
            }
        }
    };
}
positive_number!(PullRequestNumber, "--pr");
positive_number!(RunId, "--run");
positive_number!(Attempt, "--attempt");
positive_number!(RunnerGroupId, "--runner-group-id");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeadSha(String);

impl HeadSha {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl FromStr for HeadSha {
    type Err = JitError;
    fn from_str(value: &str) -> Result<Self> {
        if value.len() != 40
            || !value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(JitError::usage(
                "--head-sha must be exactly 40 lowercase hexadecimal characters",
            ));
        }
        Ok(Self(value.to_owned()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvisionArgs {
    pub repo: RepoName,
    pub pull_request: PullRequestNumber,
    pub run_id: RunId,
    pub attempt: Attempt,
    pub head_sha: HeadSha,
    pub runner_group_id: RunnerGroupId,
    pub runner_parent: Option<PathBuf>,
}

impl ProvisionArgs {
    pub fn runner_name(&self) -> String {
        format!("bh1-jit-{}-{}", self.run_id.0, self.attempt.0)
    }
    pub fn labels(&self) -> JitLabels {
        JitLabels::new(self.run_id, self.attempt)
    }
}

#[derive(Debug)]
struct ProvisionLock {
    _file: File,
}

impl ProvisionLock {
    fn acquire() -> Result<Self> {
        let path = lock_directory()?.join("provision.lock");
        let file = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .mode(0o600)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
            .open(&path)
            .map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!("cannot open provision lock {}: {error}", path.display()),
                )
            })?;
        let metadata = file.metadata().map_err(|error| {
            JitError::new(
                JitErrorCode::Precondition,
                format!("cannot inspect provision lock {}: {error}", path.display()),
            )
        })?;
        let effective_uid = effective_uid();
        if !metadata.is_file() || metadata.uid() != effective_uid || metadata.mode() & 0o077 != 0 {
            return Err(JitError::new(
                JitErrorCode::Precondition,
                "provision lock must be an owner-only regular file",
            ));
        }

        #[allow(unsafe_code)]
        let result = unsafe {
            // SAFETY: `file` owns a valid descriptor for this call, and `flock`
            // does not retain the pointer or descriptor after returning.
            libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB)
        };
        if result != 0 {
            let error = io::Error::last_os_error();
            let code = if error.raw_os_error() == Some(libc::EWOULDBLOCK) {
                JitErrorCode::Race
            } else {
                JitErrorCode::Precondition
            };
            return Err(JitError::new(
                code,
                format!("cannot acquire provision lock {}: {error}", path.display()),
            ));
        }
        Ok(Self { _file: file })
    }
}

fn lock_directory() -> Result<PathBuf> {
    let directory = match env::var_os("XDG_RUNTIME_DIR") {
        Some(value) if !value.is_empty() => PathBuf::from(value).join("bamts-bh1-jit"),
        _ => env::temp_dir().join(format!("bamts-bh1-jit-{}", effective_uid())),
    };
    if !directory.is_absolute() {
        return Err(JitError::new(
            JitErrorCode::Precondition,
            "JIT lock directory must be absolute",
        ));
    }
    match fs::create_dir(&directory) {
        Ok(()) => {
            fs::set_permissions(&directory, Permissions::from_mode(0o700)).map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!(
                        "cannot secure provision lock directory {}: {error}",
                        directory.display()
                    ),
                )
            })?
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => {
            return Err(JitError::new(
                JitErrorCode::Precondition,
                format!(
                    "cannot create provision lock directory {}: {error}",
                    directory.display()
                ),
            ));
        }
    }
    let metadata = fs::symlink_metadata(&directory).map_err(|error| {
        JitError::new(
            JitErrorCode::Precondition,
            format!(
                "cannot inspect provision lock directory {}: {error}",
                directory.display()
            ),
        )
    })?;
    if !metadata.is_dir()
        || metadata.file_type().is_symlink()
        || metadata.uid() != effective_uid()
        || metadata.mode() & 0o077 != 0
    {
        return Err(JitError::new(
            JitErrorCode::Precondition,
            "provision lock directory must be an owner-only real directory",
        ));
    }
    Ok(directory)
}

fn effective_uid() -> u32 {
    #[allow(unsafe_code)]
    unsafe {
        // SAFETY: `geteuid` takes no arguments and has no memory-safety
        // preconditions.
        libc::geteuid()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitLabels([String; 5]);

impl JitLabels {
    pub fn new(run_id: RunId, attempt: Attempt) -> Self {
        Self([
            "self-hosted".into(),
            "linux".into(),
            "x64".into(),
            "bh1".into(),
            format!("bh1-perf-{}-{}", run_id.0, attempt.0),
        ])
    }
    pub fn as_slice(&self) -> &[String] {
        &self.0
    }
    pub fn matches(&self, observed: &[String]) -> bool {
        observed.len() == self.0.len()
            && self
                .0
                .iter()
                .all(|expected| observed.iter().any(|label| label == expected))
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct RunObservation {
    event: String,
    name: String,
    path: String,
    pull_requests: Vec<RunPullRequest>,
    run_attempt: u32,
    head_sha: String,
    status: String,
    conclusion: Option<String>,
    head_repository: RepositoryObservation,
    repository: RepositoryObservation,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
struct RunPullRequest {
    number: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct RepositoryObservation {
    full_name: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PullRequestObservation {
    head: PullRequestHead,
    base: PullRequestBase,
    state: String,
}

#[derive(Debug, Clone, Deserialize)]
struct PullRequestHead {
    sha: String,
    repo: RepositoryObservation,
}
#[derive(Debug, Clone, Deserialize)]
struct PullRequestBase {
    repo: RepositoryObservation,
}

#[derive(Debug, Clone, Deserialize)]
pub struct JobObservation {
    id: u64,
    name: String,
    status: String,
    conclusion: Option<String>,
    runner_id: Option<u64>,
    runner_name: Option<String>,
    labels: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct JobsObservation {
    jobs: Vec<JobObservation>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
enum JobsResponse {
    One(JobsObservation),
    Pages(Vec<JobsObservation>),
}

#[derive(Debug, Clone, Deserialize)]
pub struct RunnerDownload {
    os: String,
    architecture: String,
    filename: String,
    download_url: String,
    sha256_checksum: String,
}

#[derive(Debug, Deserialize)]
struct MintResponse {
    runner: MintedRunner,
    encoded_jit_config: JitSecret,
}

#[derive(Debug, Clone, Deserialize)]
struct MintedRunner {
    id: u64,
    name: String,
}

#[derive(Clone, Deserialize)]
struct JitSecret(String);

impl JitSecret {
    fn expose(&self) -> &str {
        &self.0
    }
}
impl fmt::Debug for JitSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("REDACTED")
    }
}
impl fmt::Display for JitSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("REDACTED")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvisionOutcome {
    pub job_id: u64,
    pub conclusion: String,
    pub runner_id: u64,
}

pub fn validate_run_json(bytes: &[u8], args: &ProvisionArgs, race: bool) -> Result<RunObservation> {
    let observation: RunObservation = parse_json(bytes, "workflow run")?;
    let failure = |detail| {
        JitError::new(
            if race {
                JitErrorCode::Race
            } else {
                JitErrorCode::Validation
            },
            detail,
        )
    };
    if observation.event != "pull_request" {
        return Err(failure(format!(
            "workflow event must be pull_request, observed {}",
            observation.event
        )));
    }
    if observation.name != "CI" {
        return Err(failure(
            "workflow name does not match the authorized workflow".to_owned(),
        ));
    }
    if observation.path != WORKFLOW_PATH {
        return Err(failure(
            "workflow path does not match the authorized workflow".to_owned(),
        ));
    }
    if observation.pull_requests.as_slice()
        != [RunPullRequest {
            number: args.pull_request.0,
        }]
    {
        return Err(failure(
            "workflow run is not associated with exactly the requested pull request".to_owned(),
        ));
    }
    if observation.run_attempt != args.attempt.0 {
        return Err(failure(format!(
            "run attempt changed: expected {}, observed {}",
            args.attempt.0, observation.run_attempt
        )));
    }
    if observation.head_sha != args.head_sha.as_str() {
        return Err(failure(
            "workflow head SHA does not match --head-sha".to_owned(),
        ));
    }
    let expected = args.repo.full_name();
    if observation.head_repository.full_name != expected
        || observation.repository.full_name != expected
    {
        return Err(failure(
            "workflow run is not from the same repository".to_owned(),
        ));
    }
    Ok(observation)
}

pub fn validate_pull_request_json(
    bytes: &[u8],
    args: &ProvisionArgs,
    race: bool,
) -> Result<PullRequestObservation> {
    let observation: PullRequestObservation = parse_json(bytes, "pull request")?;
    let code = if race {
        JitErrorCode::Race
    } else {
        JitErrorCode::Validation
    };
    let expected = args.repo.full_name();
    if observation.state != "open" {
        return Err(JitError::new(
            code,
            format!("pull request is {}, not open", observation.state),
        ));
    }
    if observation.head.sha != args.head_sha.as_str() {
        return Err(JitError::new(
            code,
            "pull request head SHA does not match --head-sha",
        ));
    }
    if observation.head.repo.full_name != expected || observation.base.repo.full_name != expected {
        return Err(JitError::new(code, "pull request is not same-repository"));
    }
    Ok(observation)
}

pub fn select_perf_job_json(
    bytes: &[u8],
    args: &ProvisionArgs,
    require_queued: bool,
    race: bool,
) -> Result<JobObservation> {
    let response: JobsResponse = parse_json(bytes, "workflow jobs")?;
    let jobs: Vec<JobObservation> = match response {
        JobsResponse::One(page) => page.jobs,
        JobsResponse::Pages(pages) => pages.into_iter().flat_map(|page| page.jobs).collect(),
    };
    let mut matches = jobs
        .into_iter()
        .filter(|job| job.name == "Performance (BH1)");
    let job = matches.next().ok_or_else(|| {
        JitError::new(
            if race {
                JitErrorCode::Race
            } else {
                JitErrorCode::Validation
            },
            "expected exactly one Performance (BH1) job, found none",
        )
    })?;
    if matches.next().is_some() {
        return Err(JitError::new(
            if race {
                JitErrorCode::Race
            } else {
                JitErrorCode::Validation
            },
            "expected exactly one Performance (BH1) job, found multiple",
        ));
    }
    if !args.labels().matches(&job.labels) {
        return Err(JitError::new(
            if race {
                JitErrorCode::Race
            } else {
                JitErrorCode::Validation
            },
            "Performance (BH1) labels do not exactly match this run attempt",
        ));
    }
    if require_queued
        && (job.status != "queued"
            || job.conclusion.is_some()
            || job.runner_id.is_some()
            || job.runner_name.is_some())
    {
        return Err(JitError::new(
            if race {
                JitErrorCode::Race
            } else {
                JitErrorCode::Validation
            },
            "Performance (BH1) is not queued and unassigned",
        ));
    }
    Ok(job)
}

pub fn select_download_json(bytes: &[u8]) -> Result<RunnerDownload> {
    let downloads: Vec<RunnerDownload> = parse_json(bytes, "runner downloads")?;
    let mut candidates = downloads
        .into_iter()
        .filter(|download| download.os == "linux" && download.architecture == "x64");
    let download = candidates.next().ok_or_else(|| {
        JitError::new(
            JitErrorCode::Provision,
            "runner downloads contain no linux/x64 artifact",
        )
    })?;
    if candidates.next().is_some() {
        return Err(JitError::new(
            JitErrorCode::Provision,
            "runner downloads contain multiple linux/x64 artifacts",
        ));
    }
    if download.filename != RUNNER_FILENAME
        || download.download_url != RUNNER_URL
        || !download.sha256_checksum.eq_ignore_ascii_case(RUNNER_SHA256)
    {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!("GitHub runner download does not match pinned v{RUNNER_VERSION} artifact"),
        ));
    }
    Ok(download)
}

fn parse_json<T: for<'de> Deserialize<'de>>(bytes: &[u8], subject: &str) -> Result<T> {
    if bytes.len() > MAX_API_BYTES {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!("{subject} response exceeds {} bytes", MAX_API_BYTES),
        ));
    }
    serde_json::from_slice(bytes).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("invalid {subject} response: {error}"),
        )
    })
}

pub fn provision(args: &ProvisionArgs) -> Result<ProvisionOutcome> {
    let _lock = ProvisionLock::acquire()?;
    preflight_tools()?;
    let initial_run = get_run(args, false)?;
    reject_terminal_run(&initial_run, JitErrorCode::Validation)?;
    get_pull_request(args, false)?;
    let initial_job = get_job(args, true, false)?;
    let download = get_runner_download(args)?;
    let root = RootGuard::create(args)?;
    root.prepare_layout()?;
    let runner_root = root.runner_path();
    download_and_extract(&download, &runner_root)?;
    bootstrap_rustup(&runner_root)?;
    write_control_files(args, &root.control_path())?;

    let current_run = get_run(args, true)?;
    reject_terminal_run(&current_run, JitErrorCode::Race)?;
    get_pull_request(args, true)?;
    let current_job = get_job(args, true, true)?;
    if current_job.id != initial_job.id {
        return Err(JitError::new(
            JitErrorCode::Race,
            "Performance (BH1) job identity changed during revalidation",
        ));
    }

    install_signal_handlers()?;
    let minted = mint_runner(args)?;
    if minted.runner.name != args.runner_name() {
        return post_mint_without_child(
            args,
            root,
            minted.runner,
            JitError::new(
                JitErrorCode::Provision,
                "GitHub minted an unexpected runner name",
            ),
        );
    }

    let mut child = match launch_runner(&root, &minted.encoded_jit_config) {
        Ok(child) => child,
        Err(error) => return post_mint_without_child(args, root, minted.runner, error),
    };
    let lifecycle = run_minted_lifecycle(args, initial_job.id, &minted.runner, &mut child);
    finish_post_mint(args, root, minted.runner, Some(child), lifecycle)
}

fn reject_terminal_run(run: &RunObservation, code: JitErrorCode) -> Result<()> {
    if run.status == "completed" || run.conclusion.is_some() {
        return Err(JitError::new(code, "workflow run is already terminal"));
    }
    Ok(())
}

fn get_run(args: &ProvisionArgs, race: bool) -> Result<RunObservation> {
    let bytes = gh_api(
        &args.repo.api(&format!("actions/runs/{}", args.run_id.0)),
        "GET",
        &[],
    )?;
    validate_run_json(&bytes, args, race)
}

fn get_pull_request(args: &ProvisionArgs, race: bool) -> Result<PullRequestObservation> {
    let bytes = gh_api(
        &args.repo.api(&format!("pulls/{}", args.pull_request.0)),
        "GET",
        &[],
    )?;
    validate_pull_request_json(&bytes, args, race)
}

fn get_job(args: &ProvisionArgs, require_queued: bool, race: bool) -> Result<JobObservation> {
    let path = args.repo.api(&format!(
        "actions/runs/{}/attempts/{}/jobs?per_page=100",
        args.run_id.0, args.attempt.0
    ));
    let bytes = gh_api(&path, "GET", &[("--paginate", ""), ("--slurp", "")])?;
    select_perf_job_json(&bytes, args, require_queued, race)
}

fn get_runner_download(args: &ProvisionArgs) -> Result<RunnerDownload> {
    let bytes = gh_api(&args.repo.api("actions/runners/downloads"), "GET", &[])?;
    select_download_json(&bytes)
}

fn mint_runner(args: &ProvisionArgs) -> Result<MintResponse> {
    let name = args.runner_name();
    ensure_runner_name_absent(args, &name)?;

    let group = args.runner_group_id.0.to_string();
    let mut fields = vec![
        ("-f", format!("name={name}")),
        ("-F", format!("runner_group_id={group}")),
        ("-f", "work_folder=_work".to_owned()),
    ];
    for label in args.labels().as_slice() {
        fields.push(("-f", format!("labels[]={label}")));
    }
    let refs: Vec<(&str, &str)> = fields
        .iter()
        .map(|(flag, value)| (*flag, value.as_str()))
        .collect();
    let bytes = match gh_api_post(&args.repo.api("actions/runners/generate-jitconfig"), &refs) {
        Ok(bytes) => bytes,
        Err(error) => return Err(cleanup_unconsumed_mint(args, &name, error)),
    };
    let response: MintResponse = match parse_json(&bytes, "JIT configuration") {
        Ok(response) => response,
        Err(error) => return Err(cleanup_unconsumed_mint(args, &name, error)),
    };
    if response.runner.id == 0
        || response.runner.name.is_empty()
        || response.encoded_jit_config.0.is_empty()
    {
        return Err(cleanup_unconsumed_mint(
            args,
            &name,
            JitError::new(
                JitErrorCode::Provision,
                "JIT configuration response is incomplete",
            ),
        ));
    }
    Ok(response)
}

fn gh_api_post(path: &str, fields: &[(&str, &str)]) -> Result<Vec<u8>> {
    let mut command = Command::new("gh");
    command.args([
        "api",
        path,
        "--method",
        "POST",
        "-H",
        ACCEPT,
        "-H",
        &format!("X-GitHub-Api-Version: {API_VERSION}"),
        "--include",
    ]);
    command.env("GH_HTTP_TIMEOUT", "30");
    for (flag, value) in fields {
        command.arg(*flag).arg(*value);
    }
    let output = bounded_output(&mut command, MAX_API_BYTES, "gh api POST")?;
    let (status, body) = split_included_response(&output.stdout)?;
    if !output.status.success() || status != 201 {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!(
                "JIT configuration POST returned HTTP {status}: {}",
                bounded_text(&output.stderr)
            ),
        ));
    }
    Ok(body.to_vec())
}

fn split_included_response(bytes: &[u8]) -> Result<(u16, &[u8])> {
    let separator = bytes
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .map(|index| (index, 4))
        .or_else(|| {
            bytes
                .windows(2)
                .position(|window| window == b"\n\n")
                .map(|index| (index, 2))
        })
        .ok_or_else(|| {
            JitError::new(
                JitErrorCode::Provision,
                "gh api response omitted HTTP headers",
            )
        })?;
    let headers = String::from_utf8_lossy(&bytes[..separator.0]);
    let status = headers
        .lines()
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| {
            JitError::new(
                JitErrorCode::Provision,
                "gh api response omitted HTTP status",
            )
        })?;
    Ok((status, &bytes[separator.0 + separator.1..]))
}

fn gh_api(path: &str, method: &str, fields: &[(&str, &str)]) -> Result<Vec<u8>> {
    let mut command = Command::new("gh");
    command.args([
        "api",
        path,
        "--method",
        method,
        "-H",
        ACCEPT,
        "-H",
        &format!("X-GitHub-Api-Version: {API_VERSION}"),
    ]);
    command.env("GH_HTTP_TIMEOUT", "30");
    for (flag, value) in fields {
        command.arg(flag);
        if !value.is_empty() {
            command.arg(value);
        }
    }
    let output = bounded_output(&mut command, MAX_API_BYTES, "gh api")?;
    if !output.status.success() {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!(
                "gh api failed with status {}: {}",
                output.status,
                bounded_text(&output.stderr)
            ),
        ));
    }
    Ok(output.stdout)
}

struct BoundedOutput {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn bounded_output(command: &mut Command, limit: usize, subject: &str) -> Result<BoundedOutput> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Precondition,
                format!("cannot start {subject}: {error}"),
            )
        })?;
    let stdout = child.stdout.take().ok_or_else(|| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot capture {subject} stdout"),
        )
    })?;
    let stderr = child.stderr.take().ok_or_else(|| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot capture {subject} stderr"),
        )
    })?;
    let stdout_thread = thread::spawn(move || read_bounded(stdout, limit));
    let stderr_thread = thread::spawn(move || read_bounded(stderr, limit));
    let status = child.wait().map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot wait for {subject}: {error}"),
        )
    })?;
    let stdout = stdout_thread
        .join()
        .map_err(|_| {
            JitError::new(
                JitErrorCode::Provision,
                format!("{subject} stdout reader failed"),
            )
        })?
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot read {subject} stdout: {error}"),
            )
        })?;
    let stderr = stderr_thread
        .join()
        .map_err(|_| {
            JitError::new(
                JitErrorCode::Provision,
                format!("{subject} stderr reader failed"),
            )
        })?
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot read {subject} stderr: {error}"),
            )
        })?;
    Ok(BoundedOutput {
        status,
        stdout,
        stderr,
    })
}

fn read_bounded(mut reader: impl Read, limit: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader
        .by_ref()
        .take(limit as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "subprocess output exceeded bound",
        ));
    }
    Ok(bytes)
}

fn bounded_text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(&bytes[..bytes.len().min(4096)]).replace(['\r', '\n'], " ")
}

fn preflight_tools() -> Result<()> {
    for (tool, version_arg) in [
        ("gh", "--version"),
        ("curl", "--version"),
        ("tar", "--version"),
        ("numactl", "--version"),
        ("bwrap", "--version"),
        ("rustup", "--version"),
    ] {
        let status = Command::new(tool)
            .arg(version_arg)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!("required tool {tool} is unavailable: {error}"),
                )
            })?;
        if !status.success() {
            return Err(JitError::new(
                JitErrorCode::Precondition,
                format!("required tool {tool} failed its version check"),
            ));
        }
    }
    let auth = bounded_output(
        Command::new("gh")
            .args(["auth", "status", "--active"])
            .stdout(Stdio::piped()),
        MAX_API_BYTES,
        "gh auth status",
    )?;
    if !auth.status.success() {
        return Err(JitError::new(
            JitErrorCode::Precondition,
            "gh is not authenticated to an active host",
        ));
    }
    Ok(())
}

struct RootGuard {
    path: PathBuf,
}

impl RootGuard {
    fn create(args: &ProvisionArgs) -> Result<Self> {
        let parent = match &args.runner_parent {
            Some(parent) => parent.clone(),
            None => {
                let base = env::var_os("XDG_STATE_HOME")
                    .map(PathBuf::from)
                    .or_else(|| {
                        env::var_os("HOME").map(|home| PathBuf::from(home).join(".local/state"))
                    })
                    .ok_or_else(|| {
                        JitError::new(
                            JitErrorCode::Precondition,
                            "HOME or XDG_STATE_HOME is required",
                        )
                    })?;
                base.join("bamts-bh1-jit")
            }
        };
        fs::create_dir_all(&parent).map_err(|error| {
            JitError::new(
                JitErrorCode::Precondition,
                format!("cannot create runner parent {}: {error}", parent.display()),
            )
        })?;
        reject_symlink_components(&parent)?;
        let path = parent.join(format!("run-{}-{}", args.run_id.0, args.attempt.0));
        fs::create_dir(&path).map_err(|error| {
            JitError::new(
                JitErrorCode::Precondition,
                format!("runner root {} must be fresh: {error}", path.display()),
            )
        })?;
        fs::set_permissions(&path, Permissions::from_mode(0o700)).map_err(|error| {
            JitError::new(
                JitErrorCode::Precondition,
                format!("cannot secure runner root: {error}"),
            )
        })?;
        Ok(Self { path })
    }

    fn runner_path(&self) -> PathBuf {
        self.path.join("runner")
    }

    fn control_path(&self) -> PathBuf {
        self.path.join("control")
    }

    fn prepare_layout(&self) -> Result<()> {
        for path in [self.runner_path(), self.control_path()] {
            fs::create_dir(&path).map_err(|error| {
                JitError::new(
                    JitErrorCode::Provision,
                    format!("cannot create isolated runner layout: {error}"),
                )
            })?;
            fs::set_permissions(&path, Permissions::from_mode(0o700)).map_err(|error| {
                JitError::new(
                    JitErrorCode::Provision,
                    format!("cannot secure isolated runner layout: {error}"),
                )
            })?;
        }
        Ok(())
    }

    fn remove(self) -> Result<()> {
        fs::remove_dir_all(&self.path).map_err(|error| {
            JitError::new(
                JitErrorCode::Cleanup,
                format!("cannot remove runner root {}: {error}", self.path.display()),
            )
        })?;
        if self.path.exists() {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                "runner root still exists after cleanup",
            ));
        }
        Ok(())
    }
}

impl Drop for RootGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn reject_symlink_components(path: &Path) -> Result<()> {
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        env::current_dir()
            .map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!("cannot read cwd: {error}"),
                )
            })?
            .join(path)
    };
    let mut current = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::RootDir => current.push(Path::new("/")),
            Component::Normal(part) => current.push(part),
            Component::CurDir => continue,
            Component::ParentDir | Component::Prefix(_) => {
                return Err(JitError::new(
                    JitErrorCode::Precondition,
                    "runner parent must be a normalized Unix path",
                ));
            }
        }
        if fs::symlink_metadata(&current)
            .map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!("cannot inspect {}: {error}", current.display()),
                )
            })?
            .file_type()
            .is_symlink()
        {
            return Err(JitError::new(
                JitErrorCode::Precondition,
                format!(
                    "runner parent contains symlink component {}",
                    current.display()
                ),
            ));
        }
    }
    Ok(())
}

fn download_and_extract(download: &RunnerDownload, root: &Path) -> Result<()> {
    let mut command = Command::new("curl");
    command.args([
        "--fail",
        "--location",
        "--silent",
        "--show-error",
        "--proto",
        "=https",
        "--tlsv1.2",
        "--connect-timeout",
        "30",
        "--max-time",
        "600",
        &download.download_url,
    ]);
    let output = bounded_output(&mut command, MAX_DOWNLOAD_BYTES, "curl runner download")?;
    if !output.status.success() {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!(
                "runner download failed with status {}: {}",
                output.status,
                bounded_text(&output.stderr)
            ),
        ));
    }
    let actual = format!("{:x}", Sha256::digest(&output.stdout));
    if actual != RUNNER_SHA256 || !actual.eq_ignore_ascii_case(&download.sha256_checksum) {
        return Err(JitError::new(
            JitErrorCode::Provision,
            "runner archive SHA-256 mismatch",
        ));
    }
    let archive = root.join(RUNNER_FILENAME);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&archive)
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot create runner archive: {error}"),
            )
        })?;
    file.write_all(&output.stdout)
        .and_then(|()| file.sync_all())
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot write runner archive: {error}"),
            )
        })?;
    drop(file);
    let status = Command::new("tar")
        .args([
            OsStr::new("-xzf"),
            archive.as_os_str(),
            OsStr::new("-C"),
            root.as_os_str(),
            OsStr::new("--no-same-owner"),
            OsStr::new("--no-same-permissions"),
        ])
        .status()
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot start tar: {error}"),
            )
        })?;
    fs::remove_file(&archive).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot remove runner archive: {error}"),
        )
    })?;
    if !status.success() {
        return Err(JitError::new(
            JitErrorCode::Provision,
            format!("tar failed with status {status}"),
        ));
    }
    for relative in ["run.sh", "bin/Runner.Listener"] {
        let metadata = fs::metadata(root.join(relative)).map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("runner archive lacks {relative}: {error}"),
            )
        })?;
        if !metadata.is_file() {
            return Err(JitError::new(
                JitErrorCode::Provision,
                format!("runner archive entry {relative} is not a file"),
            ));
        }
    }
    Ok(())
}

fn bootstrap_rustup(root: &Path) -> Result<()> {
    let source = resolve_executable("rustup")?;
    let bin = root.join("home/.cargo/bin");
    fs::create_dir_all(&bin).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot create runner cargo bin: {error}"),
        )
    })?;
    let rustup = bin.join("rustup");
    fs::copy(source, &rustup).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot copy rustup: {error}"),
        )
    })?;
    fs::set_permissions(&rustup, Permissions::from_mode(0o700)).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot secure rustup: {error}"),
        )
    })?;
    for proxy in [
        "cargo",
        "rustc",
        "rustdoc",
        "rustfmt",
        "clippy-driver",
        "cargo-clippy",
        "rust-gdb",
        "rust-lldb",
    ] {
        std::os::unix::fs::symlink("rustup", bin.join(proxy)).map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot create rustup proxy {proxy}: {error}"),
            )
        })?;
    }
    Ok(())
}

fn resolve_executable(name: &str) -> Result<PathBuf> {
    let path = env::var_os("PATH")
        .ok_or_else(|| JitError::new(JitErrorCode::Precondition, "PATH is unset"))?;
    for directory in env::split_paths(&path) {
        let candidate = directory.join(name);
        if candidate.is_file()
            && candidate
                .metadata()
                .map(|metadata| metadata.permissions().mode() & 0o111 != 0)
                .unwrap_or(false)
        {
            return fs::canonicalize(&candidate).map_err(|error| {
                JitError::new(
                    JitErrorCode::Precondition,
                    format!("cannot resolve {}: {error}", candidate.display()),
                )
            });
        }
    }
    Err(JitError::new(
        JitErrorCode::Precondition,
        format!("{name} is not executable on PATH"),
    ))
}

fn launch_runner(root: &RootGuard, secret: &JitSecret) -> Result<Child> {
    let numactl = resolve_executable("numactl")?;
    let bwrap = resolve_executable("bwrap")?;
    let mut command = Command::new(numactl);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C.UTF-8")
        .env("LC_ALL", "C.UTF-8")
        .args(["--physcpubind=0-19", "--membind=0"])
        .arg(bwrap)
        .args([
            "--die-with-parent",
            "--unshare-pid",
            "--unshare-ipc",
            "--unshare-uts",
            "--unshare-cgroup",
            "--clearenv",
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--tmpfs",
            "/run",
        ]);
    for system_path in ["/usr", "/bin", "/lib", "/lib64", "/etc", "/sys"] {
        if Path::new(system_path).exists() {
            command.args(["--ro-bind", system_path, system_path]);
        }
    }
    command
        .arg("--bind")
        .arg(root.runner_path())
        .arg("/runner")
        .arg("--ro-bind")
        .arg(root.control_path())
        .arg("/control")
        .args([
            "--chdir",
            "/runner",
            "--setenv",
            "HOME",
            "/runner/home",
            "--setenv",
            "PATH",
            "/runner/home/.cargo/bin:/usr/local/bin:/usr/bin:/bin",
            "--setenv",
            "LANG",
            "C.UTF-8",
            "--setenv",
            "LC_ALL",
            "C.UTF-8",
            "--setenv",
            "NO_COLOR",
            "1",
            "--setenv",
            "ACTIONS_RUNNER_HOOK_JOB_STARTED",
            "/control/job-started",
            "--",
            "/control/bh1_jit",
            "__launch-jit-from-stdin",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    command.process_group(0);
    let mut child = command.spawn().map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot launch sandboxed runner: {error}"),
        )
    })?;
    let write_result = child
        .stdin
        .take()
        .ok_or_else(|| io::Error::other("missing launcher input"))
        .and_then(|mut input| input.write_all(secret.expose().as_bytes()));
    if write_result.is_err() {
        let mut detail = "cannot deliver internal launcher input".to_owned();
        if let Err(error) = terminate_process_group(&mut child) {
            detail.push_str(&format!("; child-terminate: {}", error.detail));
        }
        if let Err(error) = wait_child(&mut child, CHILD_EXIT_TIMEOUT) {
            detail.push_str(&format!("; child-wait: {}", error.detail));
        }
        return Err(JitError::new(JitErrorCode::Provision, detail));
    }
    Ok(child)
}

fn run_minted_lifecycle(
    args: &ProvisionArgs,
    job_id: u64,
    minted: &MintedRunner,
    child: &mut Child,
) -> Result<ProvisionOutcome> {
    let assignment_deadline = Instant::now() + ASSIGNMENT_TIMEOUT;
    loop {
        check_interrupted()?;
        reject_terminal_run(&get_run(args, true)?, JitErrorCode::Race)?;
        let job = get_job(args, false, true)?;
        if job.id != job_id {
            return Err(JitError::new(
                JitErrorCode::Race,
                "Performance (BH1) job identity changed",
            ));
        }
        match (job.runner_id, job.runner_name.as_deref()) {
            (Some(id), Some(name)) if id == minted.id && name == minted.name => break,
            (None, None) if job.status == "queued" => {}
            (Some(_), Some(_)) => {
                return Err(JitError::new(
                    JitErrorCode::Race,
                    "Performance (BH1) was assigned to a different runner",
                ));
            }
            _ => {
                return Err(JitError::new(
                    JitErrorCode::Race,
                    "Performance (BH1) has inconsistent assignment state",
                ));
            }
        }
        if let Some(status) = child.try_wait().map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot observe runner process: {error}"),
            )
        })? {
            return Err(JitError::new(
                JitErrorCode::RunnerFailed,
                format!("runner exited before assignment with status {status}"),
            ));
        }
        if Instant::now() >= assignment_deadline {
            return Err(JitError::new(
                JitErrorCode::Provision,
                "timed out waiting for runner assignment",
            ));
        }
        thread::sleep(ASSIGNMENT_POLL);
    }

    let completion_deadline = Instant::now() + COMPLETION_TIMEOUT;
    loop {
        check_interrupted()?;
        let run = get_run(args, true)?;
        let job = get_job(args, false, true)?;
        if job.id != job_id
            || job.runner_id != Some(minted.id)
            || job.runner_name.as_deref() != Some(minted.name.as_str())
        {
            return Err(JitError::new(
                JitErrorCode::Race,
                "Performance (BH1) assignment changed after claim",
            ));
        }
        if job.status == "completed" {
            let conclusion = job.conclusion.ok_or_else(|| {
                JitError::new(
                    JitErrorCode::RunnerFailed,
                    "completed Performance (BH1) job lacks conclusion",
                )
            })?;
            if conclusion != "success" {
                return Err(JitError::new(
                    JitErrorCode::RunnerFailed,
                    format!("Performance (BH1) concluded {conclusion}"),
                ));
            }
            if run.status != "completed" && run.conclusion.is_some() {
                return Err(JitError::new(
                    JitErrorCode::Race,
                    "workflow run has inconsistent terminal state",
                ));
            }
            return Ok(ProvisionOutcome {
                job_id,
                conclusion,
                runner_id: minted.id,
            });
        }
        if let Some(status) = child.try_wait().map_err(|error| {
            JitError::new(
                JitErrorCode::RunnerFailed,
                format!("cannot observe runner process: {error}"),
            )
        })? {
            return Err(JitError::new(
                JitErrorCode::RunnerFailed,
                format!("runner exited before job completion with status {status}"),
            ));
        }
        if Instant::now() >= completion_deadline {
            return Err(JitError::new(
                JitErrorCode::RunnerFailed,
                "timed out waiting for Performance (BH1) completion",
            ));
        }
        thread::sleep(COMPLETION_POLL);
    }
}

fn post_mint_without_child(
    args: &ProvisionArgs,
    root: RootGuard,
    minted: MintedRunner,
    error: JitError,
) -> Result<ProvisionOutcome> {
    finish_post_mint(args, root, minted, None, Err(error))
}

fn finish_post_mint(
    args: &ProvisionArgs,
    root: RootGuard,
    minted: MintedRunner,
    mut child: Option<Child>,
    lifecycle: Result<ProvisionOutcome>,
) -> Result<ProvisionOutcome> {
    let mut failures = Vec::new();
    if let Some(process) = child.as_mut() {
        if let Err(error) = terminate_process_group(process) {
            failures.push(("child-terminate", error));
        }
        if let Err(error) = wait_child(process, CHILD_EXIT_TIMEOUT) {
            failures.push(("child-wait", error));
        }
    }
    if let Err(error) = delete_runner(args, minted.id) {
        failures.push(("delete", error));
    }
    if let Err(error) = wait_runner_absent(args, &minted) {
        failures.push(("absence", error));
    }
    if let Err(error) = root.remove() {
        failures.push(("root", error));
    }
    aggregate_cleanup(lifecycle, minted.id, &args.runner_name(), failures)
}

fn aggregate_cleanup(
    lifecycle: Result<ProvisionOutcome>,
    runner_id: u64,
    runner_name: &str,
    failures: Vec<(&'static str, JitError)>,
) -> Result<ProvisionOutcome> {
    if failures.is_empty() {
        return lifecycle;
    }
    let evidence = failures
        .into_iter()
        .map(|(stage, error)| format!("{stage}: {}", error.detail))
        .collect::<Vec<_>>()
        .join("; ");
    match lifecycle {
        Err(error) => Err(JitError::new(
            error.code,
            format!(
                "{}; cleanup failed for runner id={runner_id} name={runner_name}: {evidence}",
                error.detail
            ),
        )),
        Ok(_) => Err(JitError::new(
            JitErrorCode::Cleanup,
            format!("cleanup failed for runner id={runner_id} name={runner_name}: {evidence}"),
        )),
    }
}

fn terminate_process_group(child: &mut Child) -> Result<()> {
    #[allow(unsafe_code)]
    let term = unsafe { libc::killpg(child.id() as i32, libc::SIGTERM) };
    if term != 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ESRCH) {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                format!("cannot terminate runner namespace: {error}"),
            ));
        }
    }
    let deadline = Instant::now() + Duration::from_secs(30);
    while Instant::now() < deadline {
        if child.try_wait().ok().flatten().is_some() {
            return Ok(());
        }
        thread::sleep(Duration::from_millis(200));
    }
    #[allow(unsafe_code)]
    let kill = unsafe { libc::killpg(child.id() as i32, libc::SIGKILL) };
    if kill != 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ESRCH) {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                format!("cannot kill runner namespace: {error}"),
            ));
        }
    }
    Ok(())
}

fn wait_child(child: &mut Child, timeout: Duration) -> Result<()> {
    let deadline = Instant::now() + timeout;
    loop {
        if child
            .try_wait()
            .map_err(|error| {
                JitError::new(
                    JitErrorCode::Cleanup,
                    format!("cannot wait for runner process: {error}"),
                )
            })?
            .is_some()
        {
            return Ok(());
        }
        if Instant::now() >= deadline {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                "runner process did not exit after termination",
            ));
        }
        thread::sleep(Duration::from_millis(200));
    }
}

fn delete_runner(args: &ProvisionArgs, runner_id: u64) -> Result<()> {
    let path = args.repo.api(&format!("actions/runners/{runner_id}"));
    let status = gh_api_status(&path, "DELETE")?;
    if status == 204 || status == 404 {
        Ok(())
    } else {
        Err(JitError::new(
            JitErrorCode::Cleanup,
            format!("runner deletion returned HTTP {status}"),
        ))
    }
}

fn wait_runner_absent(args: &ProvisionArgs, minted: &MintedRunner) -> Result<()> {
    let deadline = Instant::now() + DISAPPEAR_TIMEOUT;
    loop {
        let direct = gh_api_status(
            &args.repo.api(&format!("actions/runners/{}", minted.id)),
            "GET",
        )?;
        let list = gh_api(
            &args.repo.api("actions/runners?per_page=100"),
            "GET",
            &[("--paginate", ""), ("--slurp", "")],
        )?;
        let listed = runner_list_contains(&list, &minted.name)?;
        if direct == 404 && !listed {
            return Ok(());
        }
        if Instant::now() >= deadline {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                "minted runner did not disappear from GitHub",
            ));
        }
        thread::sleep(Duration::from_secs(2));
    }
}

#[derive(Deserialize)]
struct RunnerList {
    runners: Vec<RunnerListEntry>,
}

#[derive(Deserialize)]
struct RunnerListEntry {
    id: u64,
    name: String,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum RunnerListResponse {
    One(RunnerList),
    Pages(Vec<RunnerList>),
}

fn list_runners(args: &ProvisionArgs) -> Result<Vec<RunnerListEntry>> {
    let bytes = gh_api(
        &args.repo.api("actions/runners?per_page=100"),
        "GET",
        &[("--paginate", ""), ("--slurp", "")],
    )?;
    let response: RunnerListResponse = parse_json(&bytes, "runner list")?;
    Ok(match response {
        RunnerListResponse::One(page) => page.runners,
        RunnerListResponse::Pages(pages) => {
            pages.into_iter().flat_map(|page| page.runners).collect()
        }
    })
}

fn runner_list_contains(bytes: &[u8], name: &str) -> Result<bool> {
    let response: RunnerListResponse = parse_json(bytes, "runner list")?;
    Ok(match response {
        RunnerListResponse::One(page) => page.runners.iter().any(|runner| runner.name == name),
        RunnerListResponse::Pages(pages) => pages
            .iter()
            .flat_map(|page| &page.runners)
            .any(|runner| runner.name == name),
    })
}

fn ensure_runner_name_absent(args: &ProvisionArgs, name: &str) -> Result<()> {
    if list_runners(args)?.iter().any(|runner| runner.name == name) {
        return Err(JitError::new(
            JitErrorCode::Precondition,
            format!("runner `{name}` is already registered"),
        ));
    }
    Ok(())
}

fn cleanup_unconsumed_mint(args: &ProvisionArgs, name: &str, original: JitError) -> JitError {
    match delete_runner_by_name(args, name) {
        Ok(()) => original,
        Err(cleanup) => JitError::new(
            original.code,
            format!(
                "{}; post-mint cleanup failed for runner name={name}: {}",
                original.detail, cleanup.detail
            ),
        ),
    }
}

fn delete_runner_by_name(args: &ProvisionArgs, name: &str) -> Result<()> {
    for runner in list_runners(args)?
        .into_iter()
        .filter(|runner| runner.name == name)
    {
        let status = gh_api_status(
            &args.repo.api(&format!("actions/runners/{}", runner.id)),
            "DELETE",
        )?;
        if status != 204 && status != 404 {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                format!("runner DELETE returned HTTP {status}"),
            ));
        }
    }

    let deadline = Instant::now() + DISAPPEAR_TIMEOUT;
    loop {
        if !list_runners(args)?.iter().any(|runner| runner.name == name) {
            return Ok(());
        }
        if Instant::now() >= deadline {
            return Err(JitError::new(
                JitErrorCode::Cleanup,
                format!("runner `{name}` did not disappear from GitHub"),
            ));
        }
        thread::sleep(Duration::from_secs(2));
    }
}

fn gh_api_status(path: &str, method: &str) -> Result<u16> {
    let output = bounded_output(
        Command::new("gh").env("GH_HTTP_TIMEOUT", "30").args([
            "api",
            path,
            "--method",
            method,
            "-H",
            ACCEPT,
            "-H",
            &format!("X-GitHub-Api-Version: {API_VERSION}"),
            "--include",
        ]),
        MAX_API_BYTES,
        "gh api status",
    )?;
    let text = String::from_utf8_lossy(&output.stdout);
    let status = text
        .lines()
        .find_map(|line| {
            line.strip_prefix("HTTP/")
                .and_then(|rest| rest.split_whitespace().nth(1))
                .and_then(|value| value.parse::<u16>().ok())
        })
        .ok_or_else(|| {
            JitError::new(JitErrorCode::Cleanup, "gh api response omitted HTTP status")
        })?;
    if output.status.success() || status == 404 {
        Ok(status)
    } else {
        Err(JitError::new(
            JitErrorCode::Cleanup,
            format!(
                "gh api {method} failed with HTTP {status}: {}",
                bounded_text(&output.stderr)
            ),
        ))
    }
}

fn install_signal_handlers() -> Result<()> {
    extern "C" fn interrupt(_: i32) {
        INTERRUPTED.store(true, Ordering::SeqCst);
    }
    let handler = interrupt as *const () as libc::sighandler_t;
    #[allow(unsafe_code)]
    unsafe {
        // SAFETY: `handler` has the POSIX signal-handler ABI and performs only
        // an async-signal-safe atomic store.
        if libc::signal(libc::SIGINT, handler) == libc::SIG_ERR
            || libc::signal(libc::SIGTERM, handler) == libc::SIG_ERR
        {
            return Err(JitError::new(
                JitErrorCode::Precondition,
                "cannot install signal handlers",
            ));
        }
    }
    Ok(())
}

fn check_interrupted() -> Result<()> {
    if INTERRUPTED.load(Ordering::SeqCst) {
        Err(JitError::new(
            JitErrorCode::Interrupted,
            "operator interrupted provisioning",
        ))
    } else {
        Ok(())
    }
}

fn write_control_files(args: &ProvisionArgs, control: &Path) -> Result<()> {
    let launcher = control.join("bh1_jit");
    fs::copy(
        env::current_exe().map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot identify JIT launcher: {error}"),
            )
        })?,
        &launcher,
    )
    .map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot copy JIT launcher: {error}"),
        )
    })?;
    fs::set_permissions(&launcher, Permissions::from_mode(0o700)).map_err(|error| {
        JitError::new(
            JitErrorCode::Provision,
            format!("cannot secure JIT launcher: {error}"),
        )
    })?;

    let hook = control.join("job-started");
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o700)
        .open(&hook)
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot create pre-job guard: {error}"),
            )
        })?;
    let hook_source = job_started_hook(args)?;
    file.write_all(hook_source.as_bytes())
        .and_then(|()| file.sync_all())
        .map_err(|error| {
            JitError::new(
                JitErrorCode::Provision,
                format!("cannot write pre-job guard: {error}"),
            )
        })
}

fn job_started_hook(args: &ProvisionArgs) -> Result<String> {
    let quote = |value: &str| {
        serde_json::to_string(value).map_err(|_| {
            JitError::new(
                JitErrorCode::Provision,
                "cannot encode pre-job guard inputs",
            )
        })
    };
    let expected_repo = quote(&args.repo.full_name())?;
    let expected_run = quote(&args.run_id.0.to_string())?;
    let expected_attempt = quote(&args.attempt.0.to_string())?;
    let expected_sha = quote(args.head_sha.as_str())?;
    let workflow_ref = quote(&format!(
        "{}/{}@refs/pull/{}/merge",
        args.repo.full_name(),
        WORKFLOW_PATH,
        args.pull_request.0
    ))?;
    Ok(format!(
        r#"#!/usr/bin/python3
import json
import os
import sys

expected_repo = {expected_repo}
expected_run = {expected_run}
expected_attempt = {expected_attempt}
expected_sha = {expected_sha}
expected_ref = {workflow_ref}
authorized = False
try:
    event_path = os.environ["GITHUB_EVENT_PATH"]
    if os.path.getsize(event_path) > {MAX_API_BYTES}:
        raise ValueError()
    with open(event_path, "rb") as source:
        event = json.load(source)
    pull = event["pull_request"]
    authorized = (
        os.environ.get("GITHUB_REPOSITORY") == expected_repo
        and os.environ.get("GITHUB_RUN_ID") == expected_run
        and os.environ.get("GITHUB_RUN_ATTEMPT") == expected_attempt
        and os.environ.get("GITHUB_JOB") == "{PERF_JOB}"
        and os.environ.get("GITHUB_WORKFLOW_REF") == expected_ref
        and event["repository"]["full_name"] == expected_repo
        and pull["number"] == {pull_request}
        and pull["head"]["repo"]["full_name"] == expected_repo
        and pull["head"]["sha"] == expected_sha
    )
except (KeyError, OSError, TypeError, ValueError, json.JSONDecodeError):
    authorized = False
if not authorized:
    print("BH1 pre-job authorization failed", file=sys.stderr)
    sys.exit(1)
"#,
        pull_request = args.pull_request.0,
    ))
}

#[cfg(any(target_os = "linux", test))]
fn read_jit_secret(mut input: impl Read) -> Result<String> {
    let bytes = read_bounded(&mut input, MAX_JIT_BYTES).map_err(|_| {
        JitError::new(
            JitErrorCode::Provision,
            "internal launcher input is invalid",
        )
    })?;
    if bytes.is_empty() || bytes.contains(&0) {
        return Err(JitError::new(
            JitErrorCode::Provision,
            "internal launcher input is invalid",
        ));
    }
    String::from_utf8(bytes).map_err(|_| {
        JitError::new(
            JitErrorCode::Provision,
            "internal launcher input is invalid",
        )
    })
}

#[cfg(target_os = "linux")]
pub fn run_internal_launcher() -> Result<()> {
    let secret = read_jit_secret(io::stdin().lock())?;
    #[allow(unsafe_code)]
    let result = unsafe {
        // SAFETY: `prctl` receives the documented scalar-only
        // PR_SET_DUMPABLE arguments and does not dereference process memory.
        libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0)
    };
    if result != 0 {
        return Err(JitError::new(
            JitErrorCode::Provision,
            "internal launcher could not secure process state",
        ));
    }
    // Linux preserves nondumpability across ordinary exec. The pinned
    // run.sh/Runner.Listener chain does not change IDs or gain capabilities.
    let error = Command::new("/runner/run.sh")
        .arg("--jitconfig")
        .arg(secret)
        .exec();
    Err(JitError::new(
        JitErrorCode::Provision,
        format!("internal launcher could not start runner: {}", error.kind()),
    ))
}

// Refuses before reading the secret: the launcher needs Linux process hardening.
#[cfg(not(target_os = "linux"))]
pub fn run_internal_launcher() -> Result<()> {
    Err(JitError::new(
        JitErrorCode::Provision,
        "internal launcher is supported only on Linux",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args() -> ProvisionArgs {
        ProvisionArgs {
            repo: "owner/repo".parse().unwrap(),
            pull_request: PullRequestNumber(7),
            run_id: RunId(41),
            attempt: Attempt(2),
            head_sha: "0123456789abcdef0123456789abcdef01234567".parse().unwrap(),
            runner_group_id: RunnerGroupId(9),
            runner_parent: None,
        }
    }
    fn run_json(attempt: u32) -> Vec<u8> {
        format!(r#"{{"event":"pull_request","name":"CI","path":".github/workflows/ci.yml","pull_requests":[{{"number":7}}],"run_attempt":{attempt},"head_sha":"0123456789abcdef0123456789abcdef01234567","status":"in_progress","conclusion":null,"head_repository":{{"full_name":"owner/repo"}},"repository":{{"full_name":"owner/repo"}}}}"#).into_bytes()
    }
    fn pr_json(repo: &str) -> Vec<u8> {
        format!(r#"{{"head":{{"sha":"0123456789abcdef0123456789abcdef01234567","repo":{{"full_name":"{repo}"}}}},"base":{{"repo":{{"full_name":"owner/repo"}}}},"state":"open"}}"#).into_bytes()
    }
    fn jobs_json(labels: &[&str], runner_id: &str) -> Vec<u8> {
        let labels = serde_json::to_string(labels).unwrap();
        format!(r#"{{"jobs":[{{"id":17,"name":"Performance (BH1)","status":"queued","conclusion":null,"runner_id":{runner_id},"runner_name":null,"labels":{labels}}}]}}"#).into_bytes()
    }

    #[test]
    fn input_types_reject_ambiguous_values() {
        assert!("owner/repo".parse::<RepoName>().is_ok());
        for bad in [
            "",
            "owner",
            "owner/repo/extra",
            "owner name/repo",
            "/repo",
            "owner/",
        ] {
            assert!(bad.parse::<RepoName>().is_err(), "{bad}");
        }
        assert!(
            "0123456789abcdef0123456789abcdef01234567"
                .parse::<HeadSha>()
                .is_ok()
        );
        for bad in [
            "0123",
            "0123456789ABCDEF0123456789ABCDEF01234567",
            "g123456789abcdef0123456789abcdef01234567",
        ] {
            assert!(bad.parse::<HeadSha>().is_err(), "{bad}");
        }
        assert!("0".parse::<RunId>().is_err());
    }

    #[test]
    fn labels_are_exact_as_a_set() {
        let expected = args().labels();
        assert!(expected.matches(&[
            "x64".into(),
            "bh1".into(),
            "linux".into(),
            "bh1-perf-41-2".into(),
            "self-hosted".into()
        ]));
        assert!(!expected.matches(&[
            "self-hosted".into(),
            "linux".into(),
            "x64".into(),
            "bh1".into()
        ]));
        assert!(!expected.matches(&[
            "self-hosted".into(),
            "linux".into(),
            "x64".into(),
            "bh1".into(),
            "bh1-perf-41-2".into(),
            "extra".into()
        ]));
    }

    #[test]
    fn run_pr_and_job_validation_fail_closed() {
        assert!(validate_run_json(&run_json(2), &args(), false).is_ok());
        let good = String::from_utf8(run_json(2)).unwrap();
        for hostile in [
            good.replace(".github/workflows/ci.yml", ".github/workflows/hostile.yml"),
            good.replace(r#"[{"number":7}]"#, "[]"),
            good.replace(r#"[{"number":7}]"#, r#"[{"number":8}]"#),
            good.replace(r#"[{"number":7}]"#, r#"[{"number":7},{"number":8}]"#),
        ] {
            assert!(validate_run_json(hostile.as_bytes(), &args(), false).is_err());
            assert_eq!(
                validate_run_json(hostile.as_bytes(), &args(), true)
                    .unwrap_err()
                    .code,
                JitErrorCode::Race
            );
        }
        assert!(validate_pull_request_json(&pr_json("owner/repo"), &args(), false).is_ok());
        assert!(validate_pull_request_json(&pr_json("fork/repo"), &args(), false).is_err());
        assert_eq!(
            validate_pull_request_json(&pr_json("fork/repo"), &args(), true)
                .unwrap_err()
                .code,
            JitErrorCode::Race
        );
        assert!(validate_pull_request_json(br#"{"head":false}"#, &args(), false).is_err());
        let labels = ["self-hosted", "linux", "x64", "bh1", "bh1-perf-41-2"];
        assert!(select_perf_job_json(&jobs_json(&labels, "null"), &args(), true, false).is_ok());
        assert_eq!(
            select_perf_job_json(&jobs_json(&labels, "99"), &args(), true, true)
                .unwrap_err()
                .code,
            JitErrorCode::Race
        );
        assert!(select_perf_job_json(br#"{"jobs":[]}"#, &args(), true, false).is_err());
        assert!(select_perf_job_json(br#"{"jobs":false}"#, &args(), true, false).is_err());
        let wrong_attempt = ["self-hosted", "linux", "x64", "bh1", "bh1-perf-41-3"];
        assert!(
            select_perf_job_json(&jobs_json(&wrong_attempt, "null"), &args(), true, false).is_err()
        );
        let page = String::from_utf8(jobs_json(&labels, "null")).unwrap();
        let pages = format!("[{page}]");
        assert!(select_perf_job_json(pages.as_bytes(), &args(), true, false).is_ok());
    }

    #[test]
    fn duplicate_perf_jobs_are_rejected() {
        let labels = r#"["self-hosted","linux","x64","bh1","bh1-perf-41-2"]"#;
        let job = format!(
            r#"{{"id":17,"name":"Performance (BH1)","status":"queued","conclusion":null,"runner_id":null,"runner_name":null,"labels":{labels}}}"#
        );
        let json = format!(r#"{{"jobs":[{job},{job}]}}"#);
        assert!(select_perf_job_json(json.as_bytes(), &args(), true, false).is_err());
    }

    #[test]
    fn download_requires_the_single_pinned_artifact() {
        let good = format!(
            r#"[{{"os":"linux","architecture":"x64","filename":"{RUNNER_FILENAME}","download_url":"{RUNNER_URL}","sha256_checksum":"{RUNNER_SHA256}"}}]"#
        );
        assert!(select_download_json(good.as_bytes()).is_ok());
        assert!(select_download_json(good.replace(RUNNER_VERSION, "2.335.0").as_bytes()).is_err());
        assert!(select_download_json(br#"[{"os":false}]"#).is_err());
        assert!(select_download_json(b"[]").is_err());
        let duplicate = format!(
            "[{},{}]",
            &good[1..good.len() - 1],
            &good[1..good.len() - 1]
        );
        assert!(select_download_json(duplicate.as_bytes()).is_err());
    }

    #[test]
    fn jit_secret_is_always_redacted() {
        let secret: JitSecret = serde_json::from_str(r#""fixture-secret""#).unwrap();
        assert_eq!(format!("{secret}"), "REDACTED");
        assert_eq!(format!("{secret:?}"), "REDACTED");
        assert!(!format!("{} {:?}", secret, secret).contains("fixture-secret"));
    }

    #[test]
    fn launcher_input_is_bounded_and_errors_are_redacted() {
        assert_eq!(
            read_jit_secret(&b"fixture-secret"[..]).unwrap(),
            "fixture-secret"
        );
        for hostile in [Vec::new(), vec![0], vec![b'x'; MAX_JIT_BYTES + 1]] {
            let error = read_jit_secret(hostile.as_slice()).unwrap_err();
            assert_eq!(error.code, JitErrorCode::Provision);
            assert!(!error.to_string().contains("fixture-secret"));
        }
    }

    #[test]
    fn generated_hook_accepts_only_exact_immutable_context() {
        let directory = env::temp_dir().join(format!(
            "bamts-jit-hook-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let hook = directory.join("hook.py");
        let event = directory.join("event.json");
        fs::write(&hook, job_started_hook(&args()).unwrap()).unwrap();
        fs::write(
            &event,
            r#"{"repository":{"full_name":"owner/repo"},"pull_request":{"number":7,"head":{"sha":"0123456789abcdef0123456789abcdef01234567","repo":{"full_name":"owner/repo"}}}}"#,
        )
        .unwrap();
        let run = |workflow_ref: &str| {
            Command::new("/usr/bin/python3")
                .arg(&hook)
                .env_clear()
                .env("GITHUB_EVENT_PATH", &event)
                .env("GITHUB_REPOSITORY", "owner/repo")
                .env("GITHUB_RUN_ID", "41")
                .env("GITHUB_RUN_ATTEMPT", "2")
                .env("GITHUB_JOB", PERF_JOB)
                .env("GITHUB_WORKFLOW_REF", workflow_ref)
                .output()
                .unwrap()
        };
        assert!(
            run("owner/repo/.github/workflows/ci.yml@refs/pull/7/merge")
                .status
                .success()
        );
        let rejected = run("owner/repo/.github/workflows/hostile.yml@refs/pull/7/merge");
        assert!(!rejected.status.success());
        let stderr = String::from_utf8(rejected.stderr).unwrap();
        assert_eq!(stderr.trim(), "BH1 pre-job authorization failed");
        assert!(!stderr.contains("hostile.yml"));
        fs::write(
            &event,
            r#"{"repository":{"full_name":"owner/repo"},"pull_request":{"number":7,"head":{"sha":"ffffffffffffffffffffffffffffffffffffffff","repo":{"full_name":"owner/repo"}}}}"#,
        )
        .unwrap();
        let rejected = run("owner/repo/.github/workflows/ci.yml@refs/pull/7/merge");
        assert!(!rejected.status.success());
        let stderr = String::from_utf8(rejected.stderr).unwrap();
        assert_eq!(stderr.trim(), "BH1 pre-job authorization failed");
        assert!(!stderr.contains("ffffffff"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn cleanup_failures_preserve_lifecycle_code_and_all_evidence() {
        let lifecycle = Err(JitError::new(JitErrorCode::RunnerFailed, "job failed"));
        let failures = vec![
            (
                "child",
                JitError::new(JitErrorCode::Cleanup, "child remained"),
            ),
            (
                "delete",
                JitError::new(JitErrorCode::Cleanup, "delete failed"),
            ),
            (
                "absence",
                JitError::new(JitErrorCode::Cleanup, "still present"),
            ),
            (
                "root",
                JitError::new(JitErrorCode::Cleanup, "root remained"),
            ),
        ];
        let error = aggregate_cleanup(lifecycle, 88, "bh1-jit-41-2", failures).unwrap_err();
        assert_eq!(error.code, JitErrorCode::RunnerFailed);
        let detail = error.to_string();
        for expected in [
            "runner id=88 name=bh1-jit-41-2",
            "child remained",
            "delete failed",
            "still present",
            "root remained",
        ] {
            assert!(detail.contains(expected), "{detail}");
        }

        let success = Ok(ProvisionOutcome {
            job_id: 17,
            conclusion: "success".to_owned(),
            runner_id: 88,
        });
        let error = aggregate_cleanup(
            success,
            88,
            "bh1-jit-41-2",
            vec![("delete", JitError::new(JitErrorCode::Cleanup, "failed"))],
        )
        .unwrap_err();
        assert_eq!(error.code, JitErrorCode::Cleanup);
    }

    #[test]
    fn provision_lock_rejects_overlapping_attempts() {
        let first = ProvisionLock::acquire().unwrap();
        let error = ProvisionLock::acquire().unwrap_err();
        assert_eq!(error.code, JitErrorCode::Race);
        drop(first);
        assert!(ProvisionLock::acquire().is_ok());
    }
}
