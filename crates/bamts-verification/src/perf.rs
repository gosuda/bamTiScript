//! Performance harness schemas and the `perf_budget` measurement/comparison
//! logic (U0.8 / PB-1).
//!
//! This module owns three schema records — the pinned host fingerprint
//! ([`HostManifest`]), the benchmark manifest ([`BenchmarkManifest`]), and the
//! budget policy ([`BudgetPolicy`]) — plus the [`MeasureResult`] the runner
//! writes and `compare` re-reads.
//!
//! Host identity is matched strictly: the immutable hardware/OS fields in
//! [`HostFingerprint`] must equal the live machine or the run is
//! [`PerfErrorCode::InvalidHost`]. Runtime conditions are read from the live
//! process, matched exactly before work starts, and serialized into every
//! measurement or scorecard. Drift yields [`PerfErrorCode::InvalidConditions`].
//!
//! For S0 the measurement drives [`crate::suite::run_suite_with_telemetry`] for
//! the requested slice. `total` is the measured seam wall; the `parse`, `bind`,
//! `check`, and `emit` keys (plus the optional `scan`) carry the real frontend
//! phase telemetry aggregated across every check-backend compile the runner
//! performs. A successful run whose result omits any required phase key is a
//! [`PerfErrorCode::HarnessError`] (see [`measure`]).

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use bamts_compiler::telemetry::Phase;
use serde::{Deserialize, Serialize};

use crate::fixtures::checked_root_path;
use crate::suite::{BackendFilter, RunFilterOptions, StatusFilter, run_suite_with_telemetry};

/// Schema version accepted by every perf schema loader.
pub const PERF_SCHEMA_VERSION: u32 = 2;
/// Default repeats when a benchmark omits the field.
pub const DEFAULT_REPEATS: u32 = 3;
/// Phase keys every measured result must carry (U0.9 fills real telemetry).
pub const PHASE_KEYS: [&str; 5] = ["parse", "bind", "check", "emit", "total"];

/// Terminal `perf_budget` failure code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PerfErrorCode {
    /// The current machine does not match the pinned host identity.
    InvalidHost,
    /// A baseline was requested but is missing.
    NoBaseline,
    /// A budget threshold was exceeded.
    BudgetBreach,
    /// The fixture tree differs from the pinned manifest.
    FixtureMismatch,
    /// Runtime tuning does not satisfy the baseline-capture contract.
    InvalidConditions,
    /// The harness could not complete measurement.
    HarnessError,
    /// Command-line usage error.
    Usage,
}

impl PerfErrorCode {
    /// Stable token printed to stderr and matched by callers.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidHost => "INVALID_HOST",
            Self::NoBaseline => "NO_BASELINE",
            Self::BudgetBreach => "BUDGET_BREACH",
            Self::FixtureMismatch => "FIXTURE_MISMATCH",
            Self::InvalidConditions => "INVALID_CONDITIONS",
            Self::HarnessError => "HARNESS_ERROR",
            Self::Usage => "USAGE",
        }
    }

    /// Process exit code for this failure.
    #[must_use]
    pub const fn exit_code(self) -> i32 {
        match self {
            Self::Usage => 2,
            Self::InvalidHost => 3,
            Self::NoBaseline => 4,
            Self::BudgetBreach => 5,
            Self::HarnessError => 6,
            Self::FixtureMismatch => 7,
            Self::InvalidConditions => 8,
        }
    }
}

/// A `perf_budget` error carrying a terminal [`PerfErrorCode`] and detail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PerfError {
    /// The terminal failure class.
    pub code: PerfErrorCode,
    /// Human-readable detail.
    pub detail: String,
}

impl PerfError {
    /// Builds a new error.
    #[must_use]
    pub fn new(code: PerfErrorCode, detail: impl Into<String>) -> Self {
        Self {
            code,
            detail: detail.into(),
        }
    }

    /// Convenience constructor for [`PerfErrorCode::HarnessError`].
    #[must_use]
    pub fn harness(detail: impl Into<String>) -> Self {
        Self::new(PerfErrorCode::HarnessError, detail)
    }

    /// Convenience constructor for [`PerfErrorCode::Usage`].
    #[must_use]
    pub fn usage(detail: impl Into<String>) -> Self {
        Self::new(PerfErrorCode::Usage, detail)
    }
}

impl fmt::Display for PerfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code.as_str(), self.detail)
    }
}

impl std::error::Error for PerfError {}

/// Module-local result type.
pub type Result<T, E = PerfError> = std::result::Result<T, E>;

// ---------------------------------------------------------------------------
// Host fingerprint schema
// ---------------------------------------------------------------------------

/// A pinned benchmark host manifest (`perf/hosts/bh1.toml`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostManifest {
    /// Schema version.
    pub schema: u32,
    /// Host identifier (for example `BH1`).
    pub host: String,
    /// Immutable hardware/OS identity, matched strictly.
    pub fingerprint: HostFingerprint,
    /// Runtime measurement conditions, matched strictly.
    pub conditions: HostConditions,
    /// Evidence source for each field.
    pub source: BTreeMap<String, String>,
}

impl HostManifest {
    /// Confirms the immutable hardware/OS identity matches the machine.
    ///
    /// Runtime conditions are validated separately and yield
    /// [`PerfErrorCode::InvalidConditions`] when they drift.
    ///
    /// # Errors
    /// Returns [`PerfErrorCode::InvalidHost`] naming every mismatched identity field.
    pub fn require_match(&self, machine: &MachineFingerprint) -> Result<()> {
        require_no_host_mismatches(self.fingerprint.identity_mismatches(machine))
    }
}

/// The immutable hardware/OS identity of a benchmark host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostFingerprint {
    /// `uname -r` kernel release, for example `7.0.0-28-generic`.
    pub kernel_release: String,
    /// Kernel build version tag (advisory; compared leniently).
    pub kernel_version: String,
    /// CPU architecture, for example `x86_64`.
    pub arch: String,
    /// CPU model name from `/proc/cpuinfo`.
    pub cpu_model: String,
    /// Distinct physical CPU sockets.
    pub sockets: u32,
    /// Physical cores per socket.
    pub cores_per_socket: u32,
    /// CPU microcode revision.
    pub microcode: String,
}

impl HostFingerprint {
    /// Verifies the immutable identity fields against a live machine reading.
    ///
    /// Returns the list of mismatched field names; empty means a match.
    /// `kernel_version` is compared leniently (substring) because the live
    /// string carries a build timestamp.
    #[must_use]
    pub fn identity_mismatches(&self, machine: &MachineFingerprint) -> Vec<String> {
        let mut diffs = Vec::new();
        if self.kernel_release != machine.kernel_release {
            diffs.push("kernel_release".to_owned());
        }
        if self.arch != machine.arch {
            diffs.push("arch".to_owned());
        }
        if self.cpu_model != machine.cpu_model {
            diffs.push("cpu_model".to_owned());
        }
        if self.sockets != machine.sockets {
            diffs.push("sockets".to_owned());
        }
        if self.cores_per_socket != machine.cores_per_socket {
            diffs.push("cores_per_socket".to_owned());
        }
        if self.microcode != machine.microcode {
            diffs.push("microcode".to_owned());
        }
        if !machine.kernel_version.contains(&self.kernel_version) {
            diffs.push("kernel_version".to_owned());
        }
        diffs
    }

    /// Confirms the machine matches this identity, or returns `INVALID_HOST`.
    ///
    /// # Errors
    /// Returns [`PerfErrorCode::InvalidHost`] naming the mismatched fields.
    pub fn require_match(&self, machine: &MachineFingerprint) -> Result<()> {
        require_no_host_mismatches(self.identity_mismatches(machine))
    }
}

fn require_no_host_mismatches(diffs: Vec<String>) -> Result<()> {
    if diffs.is_empty() {
        Ok(())
    } else {
        Err(PerfError::new(
            PerfErrorCode::InvalidHost,
            format!("host fingerprint mismatch on: {}", diffs.join(", ")),
        ))
    }
}

/// Runtime measurement conditions required by the pinned host manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostConditions {
    /// Required CPU frequency governor string, matched exactly.
    pub governor: String,
    /// Required total swap in KiB, matched exactly.
    pub swap_total_kib: u64,
    /// Required calling-thread CPU affinity list, matched exactly.
    pub cpu_affinity: String,
    /// Required calling-thread NUMA policy, matched exactly.
    pub memory_policy: String,
    /// Required calling-thread NUMA node list, matched exactly.
    pub memory_nodes: String,
}

/// Conditions observed on the live process at measurement time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObservedConditions {
    /// Live CPU governor.
    pub governor: String,
    /// Live total swap in KiB.
    pub swap_total_kib: u64,
    /// Calling-thread CPU affinity list.
    pub cpu_affinity: String,
    /// Calling-thread NUMA policy.
    pub memory_policy: String,
    /// Calling-thread NUMA node list.
    pub memory_nodes: String,
}

impl ObservedConditions {
    /// Whether observed conditions satisfy every manifest precondition exactly.
    #[must_use]
    pub fn satisfies(&self, expected: &HostConditions) -> bool {
        self.governor == expected.governor
            && self.swap_total_kib == expected.swap_total_kib
            && self.cpu_affinity == expected.cpu_affinity
            && self.memory_policy == expected.memory_policy
            && self.memory_nodes == expected.memory_nodes
    }
}

/// A live machine fingerprint read from the host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineFingerprint {
    /// `uname -r` kernel release.
    pub kernel_release: String,
    /// Kernel build version tail (from `#` onward).
    pub kernel_version: String,
    /// CPU architecture.
    pub arch: String,
    /// CPU model name.
    pub cpu_model: String,
    /// Distinct physical sockets.
    pub sockets: u32,
    /// Physical cores per socket.
    pub cores_per_socket: u32,
    /// CPU microcode revision.
    pub microcode: String,
    /// Live governor.
    pub governor: String,
    /// Live total swap (KiB).
    pub swap_total_kib: u64,
}

fn read_observed_conditions(machine: &MachineFingerprint) -> Result<ObservedConditions> {
    let placement = bamts_platform::thread_placement().map_err(platform_error)?;
    Ok(ObservedConditions {
        governor: machine.governor.clone(),
        swap_total_kib: machine.swap_total_kib,
        cpu_affinity: placement.cpu_affinity,
        memory_policy: placement.memory_policy,
        memory_nodes: placement.memory_nodes,
    })
}

fn platform_error(error: bamts_platform::PlatformError) -> PerfError {
    PerfError::harness(error.to_string())
}

fn require_conditions(observed: &ObservedConditions, expected: &HostConditions) -> Result<()> {
    if observed.satisfies(expected) {
        Ok(())
    } else {
        Err(invalid_conditions(observed, expected))
    }
}

fn read_validated_host(host: &HostManifest) -> Result<(MachineFingerprint, ObservedConditions)> {
    let machine = read_machine_fingerprint()?;
    host.require_match(&machine)?;
    let observed = read_observed_conditions(&machine)?;
    require_conditions(&observed, &host.conditions)?;
    Ok((machine, observed))
}

/// Reads the live machine fingerprint from the host.
///
/// # Errors
/// Returns [`PerfErrorCode::HarnessError`] if any host fact cannot be read
/// or parsed.
pub fn read_machine_fingerprint() -> Result<MachineFingerprint> {
    let facts = bamts_platform::machine_facts().map_err(platform_error)?;
    Ok(MachineFingerprint {
        kernel_release: facts.kernel_release,
        kernel_version: facts.kernel_version,
        arch: std::env::consts::ARCH.to_owned(),
        cpu_model: facts.cpu_model,
        sockets: facts.sockets,
        cores_per_socket: facts.cores_per_socket,
        microcode: facts.microcode,
        governor: facts.governor,
        swap_total_kib: facts.swap_total_kib,
    })
}

// ---------------------------------------------------------------------------
// Benchmark manifest schema
// ---------------------------------------------------------------------------

/// The benchmark manifest (`perf/benchmarks.toml`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BenchmarkManifest {
    /// Schema version.
    pub schema: u32,
    /// Benchmarks, one or more per slice.
    #[serde(rename = "benchmark")]
    pub benchmarks: Vec<Benchmark>,
    /// Pinned workload inputs and generated boundaries.
    #[serde(default, rename = "fixture")]
    pub fixtures: Vec<Fixture>,
}

/// A workload fixture pinned by the performance manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fixture {
    pub id: String,
    pub group: FixtureGroup,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bytes: Option<u64>,
    pub origin: FixtureOrigin,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_archive: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub spec: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tree_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file_count: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_fixture: Option<String>,
    #[serde(default)]
    pub argv: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generator: Option<String>,
    #[serde(default)]
    pub params: BTreeMap<String, u64>,
}

/// Closed workload role for a fixture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FixtureGroup {
    Bench,
    CliStartup,
    Corpus,
    Boundary,
}

/// Provenance class for a workload fixture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FixtureOrigin {
    Generated,
    TypescriptSuite,
    Corpus,
}

impl BenchmarkManifest {
    /// Finds the first benchmark owned by `slice` (case-insensitive).
    #[must_use]
    pub fn find_slice(&self, slice: &str) -> Option<&Benchmark> {
        let needle = slice.to_ascii_lowercase();
        self.benchmarks
            .iter()
            .find(|entry| entry.slice.to_ascii_lowercase() == needle)
    }
}

/// One benchmark entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Benchmark {
    /// Stable benchmark id.
    pub id: String,
    /// Owning slice id (`s0`…`s11`).
    pub slice: String,
    /// Input path relative to the materialized suite root.
    pub input: String,
    /// Measured facets.
    pub facets: Vec<String>,
    /// Measured backends.
    pub backends: Vec<String>,
    /// Baseline-artifact path.
    pub expected: String,
    /// Whether this slice is selected for the budget gate.
    #[serde(default)]
    pub selected: bool,
    /// Independent runs per measurement.
    #[serde(default = "default_repeats")]
    pub repeats: u32,
    /// Per-run timeout in milliseconds.
    pub timeout_ms: u64,
}

const fn default_repeats() -> u32 {
    DEFAULT_REPEATS
}

// ---------------------------------------------------------------------------
// Budget policy schema
// ---------------------------------------------------------------------------

/// The budget policy (`perf/budgets.toml`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BudgetPolicy {
    /// Schema version.
    pub schema: u32,
    /// Wall-time ratio thresholds (candidate/base).
    pub wall_ratio: WallRatioPolicy,
    /// Peak RSS budgets.
    pub rss: RssPolicy,
    /// Release scorecard comparator.
    pub release: ReleasePolicy,
}

/// Wall-time ratio thresholds.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WallRatioPolicy {
    /// p50 ratio ceiling.
    pub p50: f64,
    /// p95 ratio ceiling.
    pub p95: f64,
    /// p99 ratio ceiling.
    pub p99: f64,
}

/// Peak RSS budgets: `C <= B + max(abs, rel * B)`.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RssPolicy {
    /// p50 absolute floor (bytes).
    pub p50_abs_bytes: u64,
    /// p50 relative fraction.
    pub p50_rel: f64,
    /// p95 absolute floor (bytes).
    pub p95_abs_bytes: u64,
    /// p95 relative fraction.
    pub p95_rel: f64,
}

/// Artifact-byte budgets: `C <= B + max(abs, rel * B)`.
///
/// Not currently wired into [`BudgetPolicy`] or [`evaluate_budgets`]: the
/// harness does not yet measure emitted artifact size, so the budget is
/// removed from the policy to avoid advertising a gate it cannot perform.
/// Retained as a pub type so downstream re-exports remain valid until the
/// measurement lands and it can be re-wired.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPolicy {
    /// p50 absolute floor (bytes).
    pub p50_abs_bytes: u64,
    /// p50 relative fraction.
    pub p50_rel: f64,
}

/// Release scorecard comparator vs official upstream TypeScript.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReleasePolicy {
    /// Upstream comparator id, for example `typescript@7.0.2`.
    pub comparator: String,
    /// p95 wall ratio ceiling vs upstream.
    pub p95_ratio: f64,
    /// Geomean ratio ceiling vs upstream.
    pub geomean_ratio: f64,
}

// ---------------------------------------------------------------------------
// Measured result
// ---------------------------------------------------------------------------

/// Nearest-rank quantiles for one metric.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Quantiles {
    /// 50th percentile.
    pub p50: f64,
    /// 95th percentile.
    pub p95: f64,
    /// 99th percentile.
    pub p99: f64,
}

impl Quantiles {
    /// All-zero placeholder quantiles.
    #[must_use]
    pub const fn zero() -> Self {
        Self {
            p50: 0.0,
            p95: 0.0,
            p99: 0.0,
        }
    }

    /// Computes nearest-rank quantiles over `samples`.
    #[must_use]
    pub fn from_samples(samples: &[f64]) -> Self {
        Self {
            p50: nearest_rank(samples, 0.50),
            p95: nearest_rank(samples, 0.95),
            p99: nearest_rank(samples, 0.99),
        }
    }
}

/// Nearest-rank quantile over an unsorted sample slice.
#[must_use]
pub fn nearest_rank(samples: &[f64], q: f64) -> f64 {
    if samples.is_empty() {
        return 0.0;
    }
    let mut sorted = samples.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let count = sorted.len();
    let rank = (q * count as f64).ceil() as usize;
    let index = rank.saturating_sub(1).min(count - 1);
    sorted[index]
}

/// A baseline embedded in a measured result for comparison.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Baseline {
    /// Source path or comparator id.
    pub source: String,
    /// Base total wall time (ms) quantiles.
    pub wall_ms: Quantiles,
    /// Base peak RSS (bytes) quantiles.
    pub rss_bytes: Quantiles,
    /// Optional release comparator baseline.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub release: Option<ReleaseBaseline>,
}

/// A release-comparator baseline (candidate vs upstream TypeScript).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ReleaseBaseline {
    /// Upstream comparator id.
    pub comparator: String,
    /// Candidate/upstream wall p95 ratio.
    pub wall_p95_ratio: f64,
    /// Candidate/upstream geomean ratio.
    pub geomean_ratio: f64,
}

/// The measurement result written by `measure` and read by `compare`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MeasureResult {
    /// Schema version.
    pub schema: u32,
    /// Host id.
    pub host: String,
    /// Measured slice.
    pub slice: String,
    /// Benchmark id.
    pub benchmark_id: String,
    /// Host identity captured at measurement (re-checked by `compare`).
    pub fingerprint: HostFingerprint,
    /// Expected runtime conditions (re-checked by `compare`).
    pub conditions_expected: HostConditions,
    /// Live conditions observed at measurement.
    pub conditions_observed: ObservedConditions,
    /// Whether observed conditions satisfied the manifest preconditions.
    pub conditions_match: bool,
    /// Independent runs performed.
    pub repeats: u32,
    /// Phase wall-time quantiles (ms) keyed by [`PHASE_KEYS`].
    pub phases: BTreeMap<String, Quantiles>,
    /// Peak RSS (bytes) quantiles.
    pub rss_bytes: Quantiles,
    /// Optional baseline for ratio comparison.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub baseline: Option<Baseline>,
    /// Whether this slice is selected for the budget gate.
    #[serde(default)]
    pub selected: bool,
}

/// Official TypeScript comparator measurements captured under a pinned host contract.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Scorecard {
    pub schema: u32,
    pub comparator: String,
    pub node_version: String,
    pub host: String,
    pub fingerprint: HostFingerprint,
    pub conditions_expected: HostConditions,
    pub conditions_observed: ObservedConditions,
    pub conditions_match: bool,
    pub repeats: u32,
    pub fixtures: BTreeMap<String, FixtureScore>,
}

/// Comparator measurements and their retained raw evidence for one pinned fixture.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixtureScore {
    pub wall_ms: Quantiles,
    #[serde(default)]
    pub wall_ms_max: f64,
    #[serde(default)]
    pub wall_ms_samples: Vec<f64>,
    pub rss_bytes: Quantiles,
    #[serde(default)]
    pub rss_bytes_max: u64,
    #[serde(default)]
    pub rss_bytes_samples: Vec<u64>,
    pub argv: Vec<String>,
    pub exit_code: i32,
}

/// Inputs to [`capture_scorecard`].
#[derive(Debug, Clone)]
pub struct ScorecardOptions {
    pub host_path: PathBuf,
    pub manifest_path: PathBuf,
    pub out_path: PathBuf,
    pub workspace_root: PathBuf,
}

#[derive(Clone, Copy)]
struct ScorecardFixture {
    id: &'static str,
    path: &'static str,
    exit_code: i32,
}

const SCORECARD_REPEATS: usize = 30;

const SCORECARD_FIXTURES: [ScorecardFixture; 5] = [
    ScorecardFixture {
        id: "bench-checker-ts",
        path: "perf/fixtures/upstream/checker.ts",
        exit_code: 1,
    },
    ScorecardFixture {
        id: "bench-dom-dts",
        path: "perf/fixtures/upstream/dom.generated.d.ts",
        exit_code: 2,
    },
    ScorecardFixture {
        id: "bench-empty-ts",
        path: "perf/fixtures/upstream/empty.ts",
        exit_code: 0,
    },
    ScorecardFixture {
        id: "bench-herebyfile",
        path: "perf/fixtures/upstream/Herebyfile.mjs",
        exit_code: 1,
    },
    ScorecardFixture {
        id: "bench-jsx-complexity",
        path: "perf/fixtures/upstream/jsxComplexSignatureHasApplicabilityError.tsx",
        exit_code: 1,
    },
];

// ---------------------------------------------------------------------------
// Loading
// ---------------------------------------------------------------------------

/// Loads and validates a host manifest.
///
/// # Errors
/// Returns [`PerfErrorCode::HarnessError`] on read, parse, or schema failure.
pub fn load_host(path: &Path) -> Result<HostManifest> {
    let manifest: HostManifest = load_toml(path)?;
    require_schema(path, manifest.schema)?;
    Ok(manifest)
}

/// Loads and validates a benchmark manifest.
///
/// # Errors
/// Returns [`PerfErrorCode::HarnessError`] on read, parse, or schema failure.
pub fn load_manifest(path: &Path) -> Result<BenchmarkManifest> {
    let manifest: BenchmarkManifest = load_toml(path)?;
    require_schema(path, manifest.schema)?;
    let mut ids = BTreeSet::new();
    for fixture in &manifest.fixtures {
        if !ids.insert(fixture.id.as_str()) {
            return Err(PerfError::harness(format!(
                "{}: duplicate fixture id `{}`",
                path.display(),
                fixture.id
            )));
        }
    }
    Ok(manifest)
}

/// Loads and validates a budget policy.
///
/// # Errors
/// Returns [`PerfErrorCode::HarnessError`] on read, parse, or schema failure.
pub fn load_policy(path: &Path) -> Result<BudgetPolicy> {
    let policy: BudgetPolicy = load_toml(path)?;
    require_schema(path, policy.schema)?;
    Ok(policy)
}

fn load_toml<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    let text = fs::read_to_string(path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    toml::from_str(&text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))
}

fn require_schema(path: &Path, schema: u32) -> Result<()> {
    if schema == PERF_SCHEMA_VERSION {
        Ok(())
    } else {
        Err(PerfError::harness(format!(
            "{}: unsupported schema {schema}, expected {PERF_SCHEMA_VERSION}",
            path.display()
        )))
    }
}

// ---------------------------------------------------------------------------
// Measurement
// ---------------------------------------------------------------------------

/// Options for [`measure`].
#[derive(Debug, Clone)]
pub struct MeasureOptions {
    /// Path to the host manifest.
    pub host_path: PathBuf,
    /// Path to the benchmark manifest.
    pub manifest_path: PathBuf,
    /// Slice id to measure.
    pub slice: String,
    /// Output result path.
    pub out_path: PathBuf,
    /// Optional baseline artifact path.
    pub baseline_path: Option<PathBuf>,
    /// Workspace root (for the suite seam).
    pub workspace_root: PathBuf,
    /// Materialized suite root (for the suite seam).
    pub snapshot_root: PathBuf,
}

/// Runs the requested slice's benchmark and writes a [`MeasureResult`].
///
/// # Errors
/// - [`PerfErrorCode::InvalidHost`] if the machine does not match the host.
/// - [`PerfErrorCode::NoBaseline`] if a baseline is requested but missing.
/// - [`PerfErrorCode::HarnessError`] on load/seam/serialization failure.
pub fn measure(options: &MeasureOptions) -> Result<MeasureResult> {
    let host = load_host(&options.host_path)?;
    let _ = read_validated_host(&host)?;

    let manifest = load_manifest(&options.manifest_path)?;
    let benchmark = manifest
        .find_slice(&options.slice)
        .ok_or_else(|| PerfError::harness(format!("no benchmark for slice `{}`", options.slice)))?;

    let baseline = load_baseline(options.baseline_path.as_deref(), &host)?;

    // S0 seam: drive the suite for the slice `repeats` times, timing the whole
    // seam wall as `total` and aggregating real frontend phase telemetry from
    // every check-backend compile the runner performs.
    let repeats = benchmark.repeats.max(1);
    let mut wall_samples = Vec::with_capacity(repeats as usize);
    let mut scan_samples = Vec::with_capacity(repeats as usize);
    let mut parse_samples = Vec::with_capacity(repeats as usize);
    let mut bind_samples = Vec::with_capacity(repeats as usize);
    let mut check_samples = Vec::with_capacity(repeats as usize);
    let mut emit_samples = Vec::with_capacity(repeats as usize);
    let mut rss_samples = Vec::with_capacity(repeats as usize);
    // Reset the peak RSS high-water mark before every repeat so each sample
    // measures only that run's allocation peak, not the cumulative peak of
    // every prior repeat and the harness.
    for _ in 0..repeats {
        reset_peak_rss()?;
        let started = Instant::now();
        let (_report, telemetry) = run_suite_with_telemetry(
            &options.workspace_root,
            &options.snapshot_root,
            &RunFilterOptions {
                status: StatusFilter::All,
                slice: Some(options.slice.clone()),
                backends: BackendFilter::All,
                shards: None,
            },
        )
        .map_err(|error| PerfError::harness(format!("run_suite seam failed: {error}")))?;
        wall_samples.push(started.elapsed().as_secs_f64() * 1_000.0);
        scan_samples.push(telemetry.millis(Phase::Scan));
        parse_samples.push(telemetry.millis(Phase::Parse));
        bind_samples.push(telemetry.millis(Phase::Bind));
        check_samples.push(telemetry.millis(Phase::Check));
        emit_samples.push(telemetry.millis(Phase::Emit));
        rss_samples.push(read_peak_rss_bytes()? as f64);
    }

    // `total` is the whole measured seam wall; the phase split is the compiler's
    // own scan/parse/bind/check/emit telemetry. `scan` is emitted as an optional
    // key alongside the five required keys; zero-duration phases stay 0.0.
    let mut phases = BTreeMap::new();
    phases.insert("scan".to_owned(), Quantiles::from_samples(&scan_samples));
    phases.insert("parse".to_owned(), Quantiles::from_samples(&parse_samples));
    phases.insert("bind".to_owned(), Quantiles::from_samples(&bind_samples));
    phases.insert("check".to_owned(), Quantiles::from_samples(&check_samples));
    phases.insert("emit".to_owned(), Quantiles::from_samples(&emit_samples));
    phases.insert("total".to_owned(), Quantiles::from_samples(&wall_samples));
    require_phase_keys(&phases)?;

    let rss_bytes = Quantiles::from_samples(&rss_samples);
    let (_machine, conditions_observed) = read_validated_host(&host)?;

    let result = MeasureResult {
        schema: PERF_SCHEMA_VERSION,
        host: host.host,
        slice: options.slice.clone(),
        benchmark_id: benchmark.id.clone(),
        fingerprint: host.fingerprint,
        conditions_expected: host.conditions,
        conditions_observed,
        conditions_match: true,
        repeats,
        phases,
        rss_bytes,
        baseline,
        selected: benchmark.selected,
    };

    write_result(&options.out_path, &result)?;
    Ok(result)
}

/// Ensures a measured phase map carries every required phase key.
///
/// A successful run whose result omits any of [`PHASE_KEYS`] is a
/// [`PerfErrorCode::HarnessError`]: the backend produced a result the budget
/// comparator cannot evaluate.
fn require_phase_keys(phases: &BTreeMap<String, Quantiles>) -> Result<()> {
    for key in PHASE_KEYS {
        if !phases.contains_key(key) {
            return Err(PerfError::harness(format!(
                "measured result is missing required phase key `{key}`"
            )));
        }
    }
    Ok(())
}

fn load_baseline(path: Option<&Path>, host: &HostManifest) -> Result<Option<Baseline>> {
    let Some(path) = path else {
        return Ok(None);
    };
    if !path.exists() {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!("baseline not found: {}", path.display()),
        ));
    }
    let text = fs::read_to_string(path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    let base: MeasureResult = serde_json::from_str(&text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    if base.schema != PERF_SCHEMA_VERSION {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!(
                "baseline schema must be {PERF_SCHEMA_VERSION}, found {}",
                base.schema
            ),
        ));
    }
    if base.host != host.host {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!(
                "baseline host `{}` does not match `{}`",
                base.host, host.host
            ),
        ));
    }
    if !base.conditions_match || !base.conditions_observed.satisfies(&host.conditions) {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            "baseline captured under unmatched runtime conditions",
        ));
    }
    if base.fingerprint != host.fingerprint || base.conditions_expected != host.conditions {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            "baseline host fingerprint or expected conditions mismatch",
        ));
    }
    let wall_ms = base.phases.get("total").copied().ok_or_else(|| {
        PerfError::new(
            PerfErrorCode::NoBaseline,
            format!("{}: baseline has no `total` phase", path.display()),
        )
    })?;
    Ok(Some(Baseline {
        source: path.display().to_string(),
        wall_ms,
        rss_bytes: base.rss_bytes,
        release: None,
    }))
}

/// Resets the process peak RSS high-water mark (`VmHWM`) so each benchmark
/// repeat measures its own allocation peak.
///
/// On Linux this writes `5` to `/proc/self/clear_refs`, which the kernel
/// documents as resetting the high-water mark to the current resident set
/// size. On other platforms this returns a contextual error instead of
/// silently producing fake data.
fn reset_peak_rss() -> Result<()> {
    #[cfg(target_os = "linux")]
    {
        fs::write("/proc/self/clear_refs", "5")
            .map_err(|error| PerfError::harness(format!("/proc/self/clear_refs: {error}")))
    }

    #[cfg(not(target_os = "linux"))]
    {
        Err(PerfError::harness(
            "peak RSS reset requires /proc/self/clear_refs and is only available on Linux",
        ))
    }
}

/// Reads the current process peak RSS high-water mark (`VmHWM`) in bytes.
///
/// After a [`reset_peak_rss`] call this is the peak since that reset, so the
/// benchmark can attribute peak memory to each measured repeat. On non-Linux
/// hosts this returns a contextual error instead of a fake zero.
fn read_peak_rss_bytes() -> Result<u64> {
    #[cfg(target_os = "linux")]
    {
        let content = fs::read_to_string("/proc/self/status")
            .map_err(|error| PerfError::harness(format!("/proc/self/status: {error}")))?;
        for line in content.lines() {
            if let Some(rest) = line.strip_prefix("VmHWM:") {
                let kib: u64 = rest
                    .split_whitespace()
                    .next()
                    .ok_or_else(|| PerfError::harness("/proc/self/status: VmHWM has no value"))?
                    .parse()
                    .map_err(|error| {
                        PerfError::harness(format!(
                            "/proc/self/status: VmHWM is not a number: {error}"
                        ))
                    })?;
                return Ok(kib * 1024);
            }
        }
        Err(PerfError::harness(
            "/proc/self/status: VmHWM field not found",
        ))
    }

    #[cfg(not(target_os = "linux"))]
    {
        Err(PerfError::harness(
            "peak RSS read requires /proc/self/status and is only available on Linux",
        ))
    }
}

fn write_result(path: &Path, result: &MeasureResult) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .map_err(|error| PerfError::harness(format!("{}: {error}", parent.display())))?;
    }
    let json = serde_json::to_string_pretty(result)
        .map_err(|error| PerfError::harness(format!("serialize result: {error}")))?;
    fs::write(path, json)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))
}

/// Writes a measured result as a blessed baseline only after strict live validation.
pub fn bless_baseline(host_path: &Path, result_path: &Path, out_path: &Path) -> Result<()> {
    let host = load_host(host_path)?;
    let _ = read_validated_host(&host)?;
    let result = load_result(result_path)?;
    if result.schema != PERF_SCHEMA_VERSION
        || result.host != host.host
        || result.fingerprint != host.fingerprint
    {
        return Err(PerfError::new(
            PerfErrorCode::InvalidHost,
            "result schema or immutable host identity does not match the host manifest",
        ));
    }
    if result.conditions_expected != host.conditions {
        return Err(PerfError::new(
            PerfErrorCode::InvalidConditions,
            "result expected conditions do not match the host manifest",
        ));
    }
    if !result.conditions_match || !result.conditions_observed.satisfies(&host.conditions) {
        return Err(invalid_conditions(
            &result.conditions_observed,
            &host.conditions,
        ));
    }
    let json = serde_json::to_string_pretty(&result)
        .map_err(|error| PerfError::harness(format!("serialize baseline: {error}")))?;
    write_text(out_path, &json)
}

/// Validates a committed baseline against the pinned host and live identity.
pub fn check_baseline(host_path: &Path, baseline_path: &Path) -> Result<()> {
    let host = load_host(host_path)?;
    let _ = read_validated_host(&host)?;
    load_baseline(Some(baseline_path), &host).map(|_| ())
}

/// Loads a scorecard JSON.
pub fn load_scorecard(path: &Path) -> Result<Scorecard> {
    let text = fs::read_to_string(path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    serde_json::from_str(&text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))
}

/// Validates a scorecard against its host, comparator, and raw-evidence contracts.
pub fn validate_scorecard(card: &Scorecard, host: &HostManifest, comparator: &str) -> Result<()> {
    if card.schema != PERF_SCHEMA_VERSION {
        return Err(PerfError::harness(format!(
            "scorecard schema must be {PERF_SCHEMA_VERSION}, found {}",
            card.schema
        )));
    }
    if card.comparator != comparator {
        return Err(PerfError::harness(format!(
            "scorecard comparator `{}` does not match `{comparator}`",
            card.comparator
        )));
    }
    if card.node_version != crate::corpus::NODE_VERSION_OUTPUT {
        return Err(PerfError::harness(format!(
            "scorecard Node version must be `{}`, found `{}`",
            crate::corpus::NODE_VERSION_OUTPUT,
            card.node_version
        )));
    }
    if card.host != host.host || card.fingerprint != host.fingerprint {
        return Err(PerfError::new(
            PerfErrorCode::InvalidHost,
            "scorecard immutable host identity does not match the host manifest",
        ));
    }
    if card.conditions_expected != host.conditions {
        return Err(PerfError::new(
            PerfErrorCode::InvalidConditions,
            "scorecard expected conditions do not match the host manifest",
        ));
    }
    if !card.conditions_match || !card.conditions_observed.satisfies(&host.conditions) {
        return Err(invalid_conditions(
            &card.conditions_observed,
            &host.conditions,
        ));
    }
    if card.repeats as usize != SCORECARD_REPEATS {
        return Err(PerfError::harness(format!(
            "scorecard repeats must be {SCORECARD_REPEATS}, found {}",
            card.repeats
        )));
    }
    let actual_ids: Vec<_> = card.fixtures.keys().map(String::as_str).collect();
    let expected_ids: Vec<_> = SCORECARD_FIXTURES
        .iter()
        .map(|fixture| fixture.id)
        .collect();
    if actual_ids != expected_ids {
        return Err(PerfError::harness(format!(
            "scorecard fixture IDs must be [{}], found [{}]",
            expected_ids.join(", "),
            actual_ids.join(", ")
        )));
    }
    for fixture in SCORECARD_FIXTURES {
        let score = &card.fixtures[fixture.id];
        let expected_argv = canonical_scorecard_argv(fixture.path);
        if score.argv != expected_argv {
            return Err(PerfError::harness(format!(
                "scorecard fixture `{}` argv must be {:?}, found {:?}",
                fixture.id, expected_argv, score.argv
            )));
        }
        if score.exit_code != fixture.exit_code {
            return Err(PerfError::harness(format!(
                "scorecard fixture `{}` exit code must be {}, found {}",
                fixture.id, fixture.exit_code, score.exit_code
            )));
        }
        validate_positive_quantiles(fixture.id, "wall_ms", score.wall_ms)?;
        validate_positive_quantiles(fixture.id, "rss_bytes", score.rss_bytes)?;
        validate_scorecard_raw_evidence(fixture.id, score)?;
    }
    Ok(())
}

fn canonical_scorecard_argv(path: &str) -> Vec<String> {
    vec![
        "--noEmit".to_owned(),
        "--pretty".to_owned(),
        "false".to_owned(),
        "--allowJs".to_owned(),
        "--jsx".to_owned(),
        "preserve".to_owned(),
        path.to_owned(),
    ]
}

fn validate_positive_quantiles(id: &str, name: &str, values: Quantiles) -> Result<()> {
    for (quantile, value) in [
        ("p50", values.p50),
        ("p95", values.p95),
        ("p99", values.p99),
    ] {
        if !value.is_finite() || value <= 0.0 {
            return Err(PerfError::harness(format!(
                "scorecard fixture `{id}` {name}.{quantile} must be finite and positive, found {value}"
            )));
        }
    }
    if values.p50 > values.p95 || values.p95 > values.p99 {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` {name} quantiles must satisfy p50 <= p95 <= p99, found {}, {}, {}",
            values.p50, values.p95, values.p99
        )));
    }
    Ok(())
}

/// Maximum of a raw sample set (`f64::NEG_INFINITY` when empty).
#[must_use]
fn sample_max(samples: &[f64]) -> f64 {
    samples.iter().copied().fold(f64::NEG_INFINITY, f64::max)
}

/// Validates the retained raw sample matrix for one fixture and requires the
/// authored derived values to be exactly the nearest-rank statistics of that
/// evidence.
fn validate_scorecard_raw_evidence(id: &str, score: &FixtureScore) -> Result<()> {
    if score.wall_ms_samples.len() != SCORECARD_REPEATS
        || score.rss_bytes_samples.len() != SCORECARD_REPEATS
    {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` must retain exactly {SCORECARD_REPEATS} raw wall and \
             {SCORECARD_REPEATS} raw RSS samples, found {} wall and {} RSS",
            score.wall_ms_samples.len(),
            score.rss_bytes_samples.len()
        )));
    }
    for (index, sample) in score.wall_ms_samples.iter().enumerate() {
        if !sample.is_finite() || *sample <= 0.0 {
            return Err(PerfError::harness(format!(
                "scorecard fixture `{id}` wall_ms_samples[{index}] must be finite and positive, found {sample}"
            )));
        }
    }
    for (index, sample) in score.rss_bytes_samples.iter().enumerate() {
        if *sample == 0 {
            return Err(PerfError::harness(format!(
                "scorecard fixture `{id}` rss_bytes_samples[{index}] must be positive, found {sample}"
            )));
        }
    }
    let wall_quantiles = Quantiles::from_samples(&score.wall_ms_samples);
    if score.wall_ms != wall_quantiles {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` wall_ms quantiles must be the nearest-rank quantiles of the retained raw samples, found {:?}, expected {:?}",
            score.wall_ms, wall_quantiles
        )));
    }
    let wall_max = sample_max(&score.wall_ms_samples);
    if score.wall_ms_max != wall_max {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` wall_ms_max must be the maximum of the retained raw samples, found {}, expected {wall_max}",
            score.wall_ms_max
        )));
    }
    let rss_view: Vec<f64> = score
        .rss_bytes_samples
        .iter()
        .map(|&bytes| bytes as f64)
        .collect();
    let rss_quantiles = Quantiles::from_samples(&rss_view);
    if score.rss_bytes != rss_quantiles {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` rss_bytes quantiles must be the nearest-rank quantiles of the retained raw samples, found {:?}, expected {:?}",
            score.rss_bytes, rss_quantiles
        )));
    }
    let rss_max = score
        .rss_bytes_samples
        .iter()
        .copied()
        .max()
        .unwrap_or_default();
    if score.rss_bytes_max != rss_max {
        return Err(PerfError::harness(format!(
            "scorecard fixture `{id}` rss_bytes_max must be the maximum of the retained raw samples, found {}, expected {rss_max}",
            score.rss_bytes_max
        )));
    }
    Ok(())
}

/// Validates a scorecard against the supplied live machine identity and conditions.
///
/// # Errors
/// Returns an invalid-host or invalid-conditions error when the live machine
/// differs from the pinned contract, or a harness error for an invalid scorecard.
pub fn validate_scorecard_on_machine(
    card: &Scorecard,
    host: &HostManifest,
    comparator: &str,
    machine: &MachineFingerprint,
) -> Result<()> {
    let observed = read_observed_conditions(machine)?;
    validate_scorecard_with_conditions(card, host, comparator, machine, &observed)
}

fn validate_scorecard_with_conditions(
    card: &Scorecard,
    host: &HostManifest,
    comparator: &str,
    machine: &MachineFingerprint,
    observed: &ObservedConditions,
) -> Result<()> {
    host.require_match(machine)?;
    require_conditions(observed, &host.conditions)?;
    validate_scorecard(card, host, comparator)
}

fn require_positive_peak_rss(id: &str, peak: u64) -> Result<u64> {
    if peak == 0 {
        Err(PerfError::harness(format!(
            "RSS sampler captured zero bytes for fixture `{id}`"
        )))
    } else {
        Ok(peak)
    }
}

/// Captures the pinned official TypeScript scorecard under valid BH1 conditions.
pub fn capture_scorecard(options: &ScorecardOptions) -> Result<Scorecard> {
    crate::oracle_pins::verify_oracle_pins(&options.workspace_root)
        .map_err(|error| PerfError::harness(error.to_string()))?;
    let host = load_host(&options.host_path)?;
    let _ = read_validated_host(&host)?;

    let version = Command::new("node")
        .arg("--version")
        .output()
        .map_err(|error| PerfError::harness(format!("node --version: {error}")))?;
    let node_version = String::from_utf8_lossy(&version.stdout).trim().to_owned();
    if !version.status.success() || node_version != crate::corpus::NODE_VERSION_OUTPUT {
        return Err(PerfError::harness(format!(
            "node version must be `{}`, found `{node_version}`",
            crate::corpus::NODE_VERSION_OUTPUT
        )));
    }

    let manifest = load_manifest(&options.manifest_path)?;
    verify_bench_fixture_hashes(&options.workspace_root, &manifest)?;
    let repeats = SCORECARD_REPEATS as u32;
    let mut fixtures = BTreeMap::new();
    for fixture in manifest
        .fixtures
        .iter()
        .filter(|fixture| fixture.group == FixtureGroup::Bench)
    {
        let relative = fixture.path.as_deref().ok_or_else(|| {
            PerfError::harness(format!("bench fixture `{}` is missing path", fixture.id))
        })?;
        let fixture_path = checked_root_path(&options.workspace_root, relative)?;
        let contract = SCORECARD_FIXTURES
            .iter()
            .find(|contract| contract.id == fixture.id)
            .ok_or_else(|| {
                PerfError::harness(format!(
                    "bench fixture `{}` has no scorecard contract",
                    fixture.id
                ))
            })?;
        if contract.path != relative {
            return Err(PerfError::harness(format!(
                "bench fixture `{}` path must be `{}`, found `{relative}`",
                fixture.id, contract.path
            )));
        }
        let argv = canonical_scorecard_argv(relative);
        let command_argv = canonical_scorecard_argv(&fixture_path.to_string_lossy());
        let mut wall = Vec::with_capacity(SCORECARD_REPEATS);
        let mut rss = Vec::with_capacity(SCORECARD_REPEATS);
        for _ in 0..repeats {
            let started = Instant::now();
            let mut child = Command::new("node_modules/typescript/bin/tsc")
                .args(&command_argv)
                .current_dir(&options.workspace_root)
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .map_err(|error| PerfError::harness(format!("spawn tsc: {error}")))?;
            let pid = child.id();
            let sampler = thread::spawn(move || poll_child_peak_rss(pid));
            let status = child
                .wait()
                .map_err(|error| PerfError::harness(format!("wait for tsc: {error}")))?;
            let peak = sampler
                .join()
                .map_err(|_| PerfError::harness("RSS sampler panicked"))?;
            let exit_code = status.code().ok_or_else(|| {
                PerfError::harness(format!(
                    "tsc terminated by signal for fixture `{}`",
                    fixture.id
                ))
            })?;
            if exit_code != contract.exit_code {
                return Err(PerfError::harness(format!(
                    "tsc exit drift for fixture `{}`: expected {}, found {exit_code}",
                    fixture.id, contract.exit_code
                )));
            }
            wall.push(started.elapsed().as_secs_f64() * 1_000.0);
            rss.push(require_positive_peak_rss(&fixture.id, peak)?);
        }
        let rss_view: Vec<f64> = rss.iter().map(|&bytes| bytes as f64).collect();
        fixtures.insert(
            fixture.id.clone(),
            FixtureScore {
                wall_ms: Quantiles::from_samples(&wall),
                wall_ms_max: sample_max(&wall),
                wall_ms_samples: wall,
                rss_bytes: Quantiles::from_samples(&rss_view),
                rss_bytes_max: rss.iter().copied().max().unwrap_or_default(),
                rss_bytes_samples: rss,
                argv,
                exit_code: contract.exit_code,
            },
        );
    }

    let (_machine, observed) = read_validated_host(&host)?;
    let card = Scorecard {
        schema: PERF_SCHEMA_VERSION,
        comparator: crate::oracle_pins::NPM_SPECIFIER.to_owned(),
        node_version,
        host: host.host.clone(),
        fingerprint: host.fingerprint.clone(),
        conditions_expected: host.conditions.clone(),
        conditions_observed: observed,
        conditions_match: true,
        repeats,
        fixtures,
    };
    validate_scorecard(&card, &host, crate::oracle_pins::NPM_SPECIFIER)?;
    let json = serde_json::to_string_pretty(&card)
        .map_err(|error| PerfError::harness(format!("serialize scorecard: {error}")))?;
    write_text(&options.out_path, &json)?;
    Ok(card)
}

fn verify_bench_fixture_hashes(root: &Path, manifest: &BenchmarkManifest) -> Result<()> {
    let mut mismatches = Vec::new();
    for fixture in manifest
        .fixtures
        .iter()
        .filter(|fixture| fixture.group == FixtureGroup::Bench)
    {
        let Some(relative) = fixture.path.as_deref() else {
            mismatches.push(format!("{}: missing path", fixture.id));
            continue;
        };
        let path = match checked_root_path(root, relative) {
            Ok(path) => path,
            Err(error) => {
                mismatches.push(format!("{}: {}", fixture.id, error.detail));
                continue;
            }
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) => {
                mismatches.push(format!("{}: {error}", fixture.id));
                continue;
            }
        };
        let actual = crate::suite::sha256_hex(&bytes);
        if fixture.sha256.as_deref() != Some(actual.as_str())
            || fixture.bytes != Some(bytes.len() as u64)
        {
            mismatches.push(format!("{}: hash or byte count mismatch", fixture.id));
        }
    }
    if mismatches.is_empty() {
        Ok(())
    } else {
        Err(PerfError::new(
            PerfErrorCode::FixtureMismatch,
            mismatches.join("; "),
        ))
    }
}

fn invalid_conditions(observed: &ObservedConditions, expected: &HostConditions) -> PerfError {
    PerfError::new(
        PerfErrorCode::InvalidConditions,
        format!(
            "observed governor=`{}`, swap_total_kib={}, cpu_affinity=`{}`, memory_policy=`{}`, memory_nodes=`{}`; expected governor=`{}`, swap_total_kib={}, cpu_affinity=`{}`, memory_policy=`{}`, memory_nodes=`{}`",
            observed.governor,
            observed.swap_total_kib,
            observed.cpu_affinity,
            observed.memory_policy,
            observed.memory_nodes,
            expected.governor,
            expected.swap_total_kib,
            expected.cpu_affinity,
            expected.memory_policy,
            expected.memory_nodes,
        ),
    )
}

fn poll_child_peak_rss(pid: u32) -> u64 {
    let status_path = format!("/proc/{pid}/status");
    let mut peak = 0_u64;
    loop {
        let Ok(status) = fs::read_to_string(&status_path) else {
            return peak;
        };
        for line in status.lines() {
            if let Some(value) = line.strip_prefix("VmHWM:") {
                if let Some(kib) = value
                    .split_whitespace()
                    .next()
                    .and_then(|v| v.parse::<u64>().ok())
                {
                    peak = peak.max(kib.saturating_mul(1024));
                }
                break;
            }
        }
        thread::sleep(Duration::from_millis(2));
    }
}

fn write_text(path: &Path, text: &str) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .map_err(|error| PerfError::harness(format!("{}: {error}", parent.display())))?;
    }
    fs::write(path, text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// Loads a measured result JSON.
///
/// # Errors
/// Returns [`PerfErrorCode::HarnessError`] on read or parse failure.
pub fn load_result(path: &Path) -> Result<MeasureResult> {
    let text = fs::read_to_string(path)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))?;
    serde_json::from_str(&text)
        .map_err(|error| PerfError::harness(format!("{}: {error}", path.display())))
}

/// Evaluates a measured result against the budget policy, re-checking that the
/// live machine still matches the result's host identity.
///
/// # Errors
/// - [`PerfErrorCode::InvalidHost`] if the machine no longer matches.
/// - [`PerfErrorCode::NoBaseline`] if the baseline is missing or degenerate.
/// - [`PerfErrorCode::BudgetBreach`] if any threshold is exceeded.
/// - [`PerfErrorCode::HarnessError`] if the result is missing the required `total` phase
///   or contains non-finite values.
pub fn compare(
    result: &MeasureResult,
    policy: &BudgetPolicy,
    host: &HostManifest,
    machine: &MachineFingerprint,
) -> Result<()> {
    let observed = read_observed_conditions(machine)?;
    compare_with_conditions(result, policy, host, machine, &observed)
}

fn compare_with_conditions(
    result: &MeasureResult,
    policy: &BudgetPolicy,
    host: &HostManifest,
    machine: &MachineFingerprint,
    observed: &ObservedConditions,
) -> Result<()> {
    host.require_match(machine)?;
    if result.schema != PERF_SCHEMA_VERSION
        || result.host != host.host
        || result.fingerprint != host.fingerprint
    {
        return Err(PerfError::new(
            PerfErrorCode::InvalidHost,
            "result schema or immutable host identity does not match the host manifest",
        ));
    }
    if result.conditions_expected != host.conditions {
        return Err(PerfError::new(
            PerfErrorCode::InvalidConditions,
            "result expected conditions do not match the host manifest",
        ));
    }
    if !result.conditions_match || !result.conditions_observed.satisfies(&host.conditions) {
        return Err(invalid_conditions(
            &result.conditions_observed,
            &host.conditions,
        ));
    }
    require_conditions(observed, &host.conditions)?;
    evaluate_budgets(result, policy)
}

/// Evaluates only the budget thresholds (host identity assumed checked).
///
/// # Errors
/// - [`PerfErrorCode::NoBaseline`] if the baseline is missing or degenerate.
/// - [`PerfErrorCode::BudgetBreach`] naming the first exceeded threshold.
/// - [`PerfErrorCode::HarnessError`] if the result is missing the required `total` phase
///   or contains non-finite values.
pub fn evaluate_budgets(result: &MeasureResult, policy: &BudgetPolicy) -> Result<()> {
    if result.selected && result.baseline.is_none() {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!(
                "selected slice `{}` (benchmark `{}`) is missing a baseline for the budget gate",
                result.slice, result.benchmark_id
            ),
        ));
    }

    let Some(baseline) = &result.baseline else {
        // Unselected informational slice: nothing to ratio-gate.
        return Ok(());
    };

    // A measured result used for the budget gate must carry the `total` phase.
    // Do not fall back to zero: a missing `total` would silently pass every
    // wall-time budget.
    let candidate_wall = result.phases.get("total").copied().ok_or_else(|| {
        PerfError::harness(format!(
            "measured result for slice `{}` (benchmark `{}`) is missing required `total` phase",
            result.slice, result.benchmark_id
        ))
    })?;

    check_ratio(
        "wall.p50",
        candidate_wall.p50,
        baseline.wall_ms.p50,
        policy.wall_ratio.p50,
    )?;
    check_ratio(
        "wall.p95",
        candidate_wall.p95,
        baseline.wall_ms.p95,
        policy.wall_ratio.p95,
    )?;
    check_ratio(
        "wall.p99",
        candidate_wall.p99,
        baseline.wall_ms.p99,
        policy.wall_ratio.p99,
    )?;

    check_abs_rel(
        "rss.p50",
        result.rss_bytes.p50,
        baseline.rss_bytes.p50,
        policy.rss.p50_abs_bytes as f64,
        policy.rss.p50_rel,
    )?;
    check_abs_rel(
        "rss.p95",
        result.rss_bytes.p95,
        baseline.rss_bytes.p95,
        policy.rss.p95_abs_bytes as f64,
        policy.rss.p95_rel,
    )?;

    if let Some(release) = &baseline.release {
        if !release.wall_p95_ratio.is_finite()
            || !release.geomean_ratio.is_finite()
            || release.wall_p95_ratio <= 0.0
            || release.geomean_ratio <= 0.0
        {
            return Err(PerfError::new(
                PerfErrorCode::NoBaseline,
                "baseline release ratios are degenerate; cannot compare".to_owned(),
            ));
        }
        if release.wall_p95_ratio > policy.release.p95_ratio {
            return Err(budget_breach(
                "release.p95",
                release.wall_p95_ratio,
                policy.release.p95_ratio,
            ));
        }
        if release.geomean_ratio > policy.release.geomean_ratio {
            return Err(budget_breach(
                "release.geomean",
                release.geomean_ratio,
                policy.release.geomean_ratio,
            ));
        }
    }

    Ok(())
}

fn check_ratio(name: &str, candidate: f64, base: f64, ceiling: f64) -> Result<()> {
    if !base.is_finite() || base <= 0.0 {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!("{name}: baseline value is degenerate ({base}); cannot compare"),
        ));
    }
    if !candidate.is_finite() || candidate < 0.0 {
        return Err(PerfError::harness(format!(
            "{name}: candidate value is non-finite ({candidate}); cannot compare"
        )));
    }
    let ratio = candidate / base;
    if ratio > ceiling {
        Err(budget_breach(name, ratio, ceiling))
    } else {
        Ok(())
    }
}

fn check_abs_rel(name: &str, candidate: f64, base: f64, abs_floor: f64, rel: f64) -> Result<()> {
    if !base.is_finite() || base < 0.0 {
        return Err(PerfError::new(
            PerfErrorCode::NoBaseline,
            format!("{name}: baseline value is degenerate ({base}); cannot compare"),
        ));
    }
    if !candidate.is_finite() || candidate < 0.0 {
        return Err(PerfError::harness(format!(
            "{name}: candidate value is non-finite ({candidate}); cannot compare"
        )));
    }
    let allowance = abs_floor.max(rel * base);
    let limit = base + allowance;
    if !limit.is_finite() {
        return Err(PerfError::harness(format!(
            "{name}: computed budget limit is non-finite ({limit})"
        )));
    }
    if candidate > limit {
        Err(PerfError::new(
            PerfErrorCode::BudgetBreach,
            format!(
                "{name}: candidate {candidate} exceeds limit {limit} (base {base} + max({abs_floor}, {rel}*base))"
            ),
        ))
    } else {
        Ok(())
    }
}

fn budget_breach(name: &str, ratio: f64, ceiling: f64) -> PerfError {
    PerfError::new(
        PerfErrorCode::BudgetBreach,
        format!("{name}: ratio {ratio:.4} exceeds ceiling {ceiling:.4}"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bh1_toml() -> &'static str {
        include_str!("../../../perf/hosts/bh1.toml")
    }

    fn sample_machine() -> MachineFingerprint {
        MachineFingerprint {
            kernel_release: "7.0.0-28-generic".to_owned(),
            kernel_version: "#28-Ubuntu SMP PREEMPT_DYNAMIC Sun Jun 21 01:01:36 UTC 2026"
                .to_owned(),
            arch: "x86_64".to_owned(),
            cpu_model: "Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz".to_owned(),
            sockets: 2,
            cores_per_socket: 20,
            microcode: "0x2007006".to_owned(),
            governor: "performance".to_owned(),
            swap_total_kib: 0,
        }
    }

    fn sample_conditions() -> HostConditions {
        HostConditions {
            governor: "performance".to_owned(),
            swap_total_kib: 0,
            cpu_affinity: "0-19".to_owned(),
            memory_policy: "bind".to_owned(),
            memory_nodes: "0".to_owned(),
        }
    }

    fn sample_observed_conditions() -> ObservedConditions {
        ObservedConditions {
            governor: "performance".to_owned(),
            swap_total_kib: 0,
            cpu_affinity: "0-19".to_owned(),
            memory_policy: "bind".to_owned(),
            memory_nodes: "0".to_owned(),
        }
    }

    fn budget_policy() -> BudgetPolicy {
        BudgetPolicy {
            schema: PERF_SCHEMA_VERSION,
            wall_ratio: WallRatioPolicy {
                p50: 1.05,
                p95: 1.10,
                p99: 1.15,
            },
            rss: RssPolicy {
                p50_abs_bytes: 16 << 20,
                p50_rel: 0.05,
                p95_abs_bytes: 32 << 20,
                p95_rel: 0.10,
            },
            release: ReleasePolicy {
                comparator: "typescript@7.0.2".to_owned(),
                p95_ratio: 1.25,
                geomean_ratio: 1.00,
            },
        }
    }

    fn result_with_baseline(base: Quantiles, candidate: Quantiles) -> MeasureResult {
        let mut phases = BTreeMap::new();
        for key in PHASE_KEYS {
            let value = if key == "total" {
                candidate
            } else {
                Quantiles::zero()
            };
            phases.insert(key.to_owned(), value);
        }
        MeasureResult {
            schema: PERF_SCHEMA_VERSION,
            host: "BH1".to_owned(),
            slice: "s0".to_owned(),
            benchmark_id: "s0-conformance-foundation".to_owned(),
            fingerprint: host_fingerprint_from_machine(&sample_machine()),
            conditions_expected: sample_conditions(),
            conditions_observed: sample_observed_conditions(),
            conditions_match: true,
            repeats: 3,
            phases,
            rss_bytes: Quantiles {
                p50: 100_000_000.0,
                p95: 100_000_000.0,
                p99: 100_000_000.0,
            },
            baseline: Some(Baseline {
                source: "perf/baselines/s0.json".to_owned(),
                wall_ms: base,
                rss_bytes: Quantiles {
                    p50: 100_000_000.0,
                    p95: 100_000_000.0,
                    p99: 100_000_000.0,
                },
                release: None,
            }),
            selected: false,
        }
    }

    fn host_fingerprint_from_machine(machine: &MachineFingerprint) -> HostFingerprint {
        HostFingerprint {
            kernel_release: machine.kernel_release.clone(),
            kernel_version: "#28-Ubuntu SMP PREEMPT_DYNAMIC".to_owned(),
            arch: machine.arch.clone(),
            cpu_model: machine.cpu_model.clone(),
            sockets: machine.sockets,
            cores_per_socket: machine.cores_per_socket,
            microcode: machine.microcode.clone(),
        }
    }

    fn sample_host() -> HostManifest {
        HostManifest {
            schema: PERF_SCHEMA_VERSION,
            host: "BH1".to_owned(),
            fingerprint: host_fingerprint_from_machine(&sample_machine()),
            conditions: sample_conditions(),
            source: BTreeMap::new(),
        }
    }

    fn sample_wall_samples() -> Vec<f64> {
        (0..SCORECARD_REPEATS)
            .map(|index| 100.0 + index as f64)
            .collect()
    }

    fn sample_rss_samples() -> Vec<u64> {
        (1..=SCORECARD_REPEATS as u64).collect()
    }

    fn sample_scorecard(host: &HostManifest) -> Scorecard {
        let wall = sample_wall_samples();
        let rss = sample_rss_samples();
        let rss_view: Vec<f64> = rss.iter().map(|&bytes| bytes as f64).collect();
        let wall_ms = Quantiles::from_samples(&wall);
        let rss_bytes = Quantiles::from_samples(&rss_view);
        let wall_ms_max = sample_max(&wall);
        let rss_bytes_max = rss.iter().copied().max().unwrap_or_default();
        let fixtures = SCORECARD_FIXTURES
            .iter()
            .map(|fixture| {
                (
                    fixture.id.to_owned(),
                    FixtureScore {
                        wall_ms,
                        wall_ms_max,
                        wall_ms_samples: wall.clone(),
                        rss_bytes,
                        rss_bytes_max,
                        rss_bytes_samples: rss.clone(),
                        argv: canonical_scorecard_argv(fixture.path),
                        exit_code: fixture.exit_code,
                    },
                )
            })
            .collect();
        Scorecard {
            schema: PERF_SCHEMA_VERSION,
            comparator: "typescript@7.0.2".to_owned(),
            node_version: "v24.18.0".to_owned(),
            host: host.host.clone(),
            fingerprint: host.fingerprint.clone(),
            conditions_expected: host.conditions.clone(),
            conditions_observed: sample_observed_conditions(),
            conditions_match: true,
            repeats: SCORECARD_REPEATS as u32,
            fixtures,
        }
    }

    #[test]
    fn benchmark_manifest_without_fixtures_still_parses() {
        let manifest: BenchmarkManifest = toml::from_str(
            "schema = 2\n[[benchmark]]\nid = 'b'\nslice = 's0'\ninput = 'index.json'\nfacets = []\nbackends = []\nexpected = 'out.json'\ntimeout_ms = 1\n",
        )
        .unwrap();
        assert!(manifest.fixtures.is_empty());
    }

    #[test]
    fn load_baseline_rejects_unmatched_conditions_and_host() {
        let temp = crate::suite::TempDir::new("perf-baseline-validation").unwrap();
        let path = temp.path().join("baseline.json");
        let host = sample_host();
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.conditions_match = false;
        fs::write(&path, serde_json::to_vec(&result).unwrap()).unwrap();
        assert_eq!(
            load_baseline(Some(&path), &host).unwrap_err().code,
            PerfErrorCode::NoBaseline
        );
        result.conditions_match = true;
        result.conditions_observed.cpu_affinity = "0-18".to_owned();
        fs::write(&path, serde_json::to_vec(&result).unwrap()).unwrap();
        assert_eq!(
            load_baseline(Some(&path), &host).unwrap_err().code,
            PerfErrorCode::NoBaseline
        );
        result.conditions_observed = sample_observed_conditions();
        result.host = "other".to_owned();
        fs::write(&path, serde_json::to_vec(&result).unwrap()).unwrap();
        assert_eq!(
            load_baseline(Some(&path), &host).unwrap_err().code,
            PerfErrorCode::NoBaseline
        );
    }

    #[test]
    fn validate_scorecard_rejects_conditions_and_fingerprint_drift() {
        let host = sample_host();
        let mut card = sample_scorecard(&host);
        card.conditions_observed = ObservedConditions {
            governor: "powersave".to_owned(),
            ..sample_observed_conditions()
        };
        card.conditions_match = false;
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidConditions
        );
        card.conditions_match = true;
        card.conditions_observed = sample_observed_conditions();
        card.conditions_observed.cpu_affinity = "0-18".to_owned();
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidConditions
        );
        card.conditions_observed = sample_observed_conditions();
        card.conditions_observed.memory_nodes = "0-1".to_owned();
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidConditions
        );
        card.conditions_observed = sample_observed_conditions();
        card.fingerprint.cpu_model = "different".to_owned();
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidHost
        );
    }

    #[test]
    fn validate_scorecard_rejects_incomplete_and_degenerate_measurements() {
        let host = sample_host();
        let mut card = sample_scorecard(&host);
        validate_scorecard(&card, &host, "typescript@7.0.2").unwrap();

        card.fixtures.remove("bench-checker-ts");
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
        card = sample_scorecard(&host);
        card.repeats = 0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
        card = sample_scorecard(&host);
        card.fixtures.get_mut("bench-dom-dts").unwrap().argv.clear();
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
        card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-empty-ts")
            .unwrap()
            .rss_bytes
            .p95 = 0.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
        card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-herebyfile")
            .unwrap()
            .wall_ms
            .p99 = f64::NAN;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
    }

    #[test]
    fn validate_scorecard_rejects_node_and_quantile_order_drift() {
        let host = sample_host();
        let mut card = sample_scorecard(&host);
        card.node_version = "v24.17.0".to_owned();
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        let wall = &mut card.fixtures.get_mut("bench-checker-ts").unwrap().wall_ms;
        wall.p50 = wall.p95 + 1.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        let rss = &mut card.fixtures.get_mut("bench-dom-dts").unwrap().rss_bytes;
        rss.p95 = rss.p99 + 1.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
    }

    #[test]
    fn scorecard_rejects_fixture_exit_drift() {
        let host = sample_host();
        let mut card = sample_scorecard(&host);
        card.fixtures.get_mut("bench-checker-ts").unwrap().exit_code = 0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
    }

    #[test]
    fn validate_scorecard_requires_exact_raw_sample_matrices() {
        let host = sample_host();
        let mut card = sample_scorecard(&host);
        validate_scorecard(&card, &host, "typescript@7.0.2").unwrap();

        card.fixtures
            .get_mut("bench-checker-ts")
            .unwrap()
            .wall_ms_samples
            .truncate(SCORECARD_REPEATS - 1);
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-dom-dts")
            .unwrap()
            .wall_ms_samples
            .push(999.0);
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-empty-ts")
            .unwrap()
            .rss_bytes_samples
            .truncate(SCORECARD_REPEATS - 1);
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-herebyfile")
            .unwrap()
            .rss_bytes_samples
            .push(1);
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        for score in card.fixtures.values_mut() {
            score.wall_ms_samples.clear();
            score.rss_bytes_samples.clear();
        }
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
    }

    #[test]
    fn scorecard_without_raw_samples_fails_closed() {
        let host = sample_host();
        let card = sample_scorecard(&host);
        let mut value = serde_json::to_value(&card).unwrap();
        for fixture in value["fixtures"].as_object_mut().unwrap().values_mut() {
            let fixture = fixture.as_object_mut().unwrap();
            for field in [
                "wall_ms_max",
                "wall_ms_samples",
                "rss_bytes_max",
                "rss_bytes_samples",
            ] {
                fixture.remove(field);
            }
        }
        let legacy: Scorecard = serde_json::from_value(value).unwrap();
        assert_eq!(
            validate_scorecard(&legacy, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::HarnessError
        );
    }

    #[test]
    fn validate_scorecard_rejects_invalid_and_tampered_raw_evidence() {
        let host = sample_host();

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-checker-ts")
            .unwrap()
            .wall_ms_samples[0] = f64::NAN;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-checker-ts")
            .unwrap()
            .wall_ms_samples[0] = -1.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-dom-dts")
            .unwrap()
            .wall_ms_samples[0] = 0.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-empty-ts")
            .unwrap()
            .rss_bytes_samples[0] = 0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-herebyfile")
            .unwrap()
            .wall_ms
            .p95 += 0.5;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-jsx-complexity")
            .unwrap()
            .wall_ms_max += 1.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-checker-ts")
            .unwrap()
            .rss_bytes
            .p50 -= 1.0;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());

        let mut card = sample_scorecard(&host);
        card.fixtures
            .get_mut("bench-dom-dts")
            .unwrap()
            .rss_bytes_max += 1;
        assert!(validate_scorecard(&card, &host, "typescript@7.0.2").is_err());
    }

    #[test]
    fn zero_peak_rss_is_rejected_before_scorecard_capture() {
        assert!(require_positive_peak_rss("bench-empty-ts", 0).is_err());
        assert_eq!(require_positive_peak_rss("bench-empty-ts", 1).unwrap(), 1);
    }

    #[test]
    fn live_scorecard_validation_rejects_identity_and_condition_drift() {
        let host = sample_host();
        let card = sample_scorecard(&host);
        validate_scorecard_with_conditions(
            &card,
            &host,
            "typescript@7.0.2",
            &sample_machine(),
            &sample_observed_conditions(),
        )
        .unwrap();

        let mut machine = sample_machine();
        machine.cpu_model = "different".to_owned();
        assert_eq!(
            validate_scorecard_with_conditions(
                &card,
                &host,
                "typescript@7.0.2",
                &machine,
                &sample_observed_conditions(),
            )
            .unwrap_err()
            .code,
            PerfErrorCode::InvalidHost
        );
        let mut observed = sample_observed_conditions();
        observed.memory_policy = "default".to_owned();
        assert_eq!(
            validate_scorecard_with_conditions(
                &card,
                &host,
                "typescript@7.0.2",
                &sample_machine(),
                &observed,
            )
            .unwrap_err()
            .code,
            PerfErrorCode::InvalidConditions
        );
    }

    #[test]
    fn bless_baseline_refuses_unmatched_conditions_before_writing() {
        let machine = read_machine_fingerprint().unwrap();
        let live_conditions = read_observed_conditions(&machine).unwrap();
        let temp = crate::suite::TempDir::new("perf-bless-conditions").unwrap();
        let host = HostManifest {
            schema: PERF_SCHEMA_VERSION,
            host: "live".to_owned(),
            fingerprint: HostFingerprint {
                kernel_release: machine.kernel_release.clone(),
                kernel_version: machine.kernel_version.clone(),
                arch: machine.arch.clone(),
                cpu_model: machine.cpu_model.clone(),
                sockets: machine.sockets,
                cores_per_socket: machine.cores_per_socket,
                microcode: machine.microcode.clone(),
            },
            conditions: HostConditions {
                governor: live_conditions.governor.clone(),
                swap_total_kib: live_conditions.swap_total_kib,
                cpu_affinity: live_conditions.cpu_affinity.clone(),
                memory_policy: live_conditions.memory_policy.clone(),
                memory_nodes: live_conditions.memory_nodes.clone(),
            },
            source: BTreeMap::new(),
        };
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.host = host.host.clone();
        result.fingerprint = host.fingerprint.clone();
        result.conditions_expected = host.conditions.clone();
        result.conditions_observed = live_conditions;
        result.conditions_match = false;
        let host_path = temp.path().join("host.toml");
        let result_path = temp.path().join("result.json");
        let out_path = temp.path().join("baseline.json");
        fs::write(&host_path, toml::to_string(&host).unwrap()).unwrap();
        fs::write(&result_path, serde_json::to_vec(&result).unwrap()).unwrap();
        let error = bless_baseline(&host_path, &result_path, &out_path).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::InvalidConditions);
        assert!(!out_path.exists());

        result.conditions_match = true;
        result.conditions_expected.cpu_affinity = "0-18".to_owned();
        fs::write(&result_path, serde_json::to_vec(&result).unwrap()).unwrap();
        assert_eq!(
            bless_baseline(&host_path, &result_path, &out_path)
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidConditions
        );
        assert!(!out_path.exists());

        result.conditions_expected = host.conditions.clone();
        fs::write(&result_path, serde_json::to_vec(&result).unwrap()).unwrap();
        bless_baseline(&host_path, &result_path, &out_path).unwrap();
        assert_eq!(load_result(&out_path).unwrap(), result);
    }

    #[test]
    fn host_read_parses_committed_manifest() {
        let host = toml::from_str::<HostManifest>(bh1_toml()).expect("parse bh1.toml");
        assert_eq!(host.schema, PERF_SCHEMA_VERSION);
        assert_eq!(host.host, "BH1");
        assert_eq!(host.fingerprint.kernel_release, "7.0.0-30-generic");
        assert_eq!(host.fingerprint.arch, "x86_64");
        assert_eq!(
            host.fingerprint.cpu_model,
            "Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz"
        );
        assert_eq!(host.fingerprint.sockets, 2);
        assert_eq!(host.fingerprint.cores_per_socket, 20);
        assert_eq!(host.conditions.governor, "powersave");
        assert_eq!(host.conditions.swap_total_kib, 403_979_000);
        assert_eq!(
            host.source.get("governor").map(String::as_str),
            Some("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
        );
        assert_eq!(host.conditions.cpu_affinity, "0-19");
        assert_eq!(host.conditions.memory_policy, "bind");
        assert_eq!(host.conditions.memory_nodes, "0");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn host_read_reads_live_proc_and_sys_evidence() {
        let machine = read_machine_fingerprint().expect("read live host evidence");
        assert!(!machine.kernel_release.is_empty());
        assert!(!machine.cpu_model.is_empty());
        assert!(machine.sockets >= 1);
        assert!(machine.cores_per_socket >= 1);
        assert!(!machine.governor.is_empty());
    }

    #[test]
    fn fingerprint_matches_identical_identity() {
        let machine = sample_machine();
        let fingerprint = host_fingerprint_from_machine(&machine);
        assert!(fingerprint.identity_mismatches(&machine).is_empty());
        assert!(fingerprint.require_match(&machine).is_ok());
    }

    #[test]
    fn fingerprint_mismatch_is_invalid_host() {
        let machine = sample_machine();
        let mut fingerprint = host_fingerprint_from_machine(&machine);
        fingerprint.cpu_model = "Intel(R) Xeon(R) Gold 9999 CPU @ 9.00GHz".to_owned();
        let diffs = fingerprint.identity_mismatches(&machine);
        assert_eq!(diffs, vec!["cpu_model".to_owned()]);
        let error = fingerprint.require_match(&machine).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::InvalidHost);
    }

    #[test]
    fn runtime_condition_mismatch_is_advisory_not_invalid_host() {
        let machine = sample_machine();
        let fingerprint = host_fingerprint_from_machine(&machine);
        // Identity still matches even when governor/swap differ.
        assert!(fingerprint.require_match(&machine).is_ok());
        let untuned = HostConditions {
            governor: "powersave".to_owned(),
            swap_total_kib: 4096,
            ..sample_conditions()
        };
        let observed = sample_observed_conditions();
        // Observed (performance/0) does not satisfy an untuned expectation.
        assert!(!observed.satisfies(&untuned));
        // But a matching expectation is satisfied.
        let tuned = sample_conditions();
        assert!(observed.satisfies(&tuned));
    }

    #[test]
    fn compare_passes_when_within_budget() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 103.0,
            p95: 108.0,
            p99: 110.0,
        };
        let result = result_with_baseline(base, candidate);
        assert!(evaluate_budgets(&result, &budget_policy()).is_ok());
        assert!(
            compare_with_conditions(
                &result,
                &budget_policy(),
                &sample_host(),
                &sample_machine(),
                &sample_observed_conditions(),
            )
            .is_ok()
        );
    }

    #[test]
    fn compare_fails_on_wall_ratio_breach() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 100.0,
            p95: 150.0,
            p99: 100.0,
        };
        let result = result_with_baseline(base, candidate);
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::BudgetBreach);
        assert!(error.detail.contains("wall.p95"));
    }

    #[test]
    fn compare_without_baseline_passes() {
        let base = Quantiles::zero();
        let candidate = Quantiles::zero();
        let mut result = result_with_baseline(base, candidate);
        result.baseline = None;
        assert!(evaluate_budgets(&result, &budget_policy()).is_ok());
    }

    #[test]
    fn perf_budget_rejects_slice_without_baseline() {
        let manifest: BenchmarkManifest =
            toml::from_str(include_str!("../../../perf/benchmarks.toml"))
                .expect("parse benchmarks fixture");
        let s11 = manifest
            .find_slice("s11")
            .expect("s11 placeholder fixture must exist");
        assert!(
            s11.selected,
            "s11 placeholder must be selected for the budget gate"
        );

        let mut phases = BTreeMap::new();
        for key in PHASE_KEYS {
            phases.insert(key.to_owned(), Quantiles::zero());
        }

        let result = MeasureResult {
            schema: PERF_SCHEMA_VERSION,
            host: "BH1".to_owned(),
            slice: s11.slice.clone(),
            benchmark_id: s11.id.clone(),
            fingerprint: host_fingerprint_from_machine(&sample_machine()),
            conditions_expected: sample_conditions(),
            conditions_observed: sample_observed_conditions(),
            conditions_match: true,
            repeats: 3,
            phases,
            rss_bytes: Quantiles::zero(),
            baseline: None,
            selected: true,
        };

        let error = compare_with_conditions(
            &result,
            &budget_policy(),
            &sample_host(),
            &sample_machine(),
            &sample_observed_conditions(),
        )
        .expect_err("selected slice without baseline must fail the budget gate");
        assert_eq!(error.code, PerfErrorCode::NoBaseline);
        assert_eq!(error.code.exit_code(), 4);
        assert!(error.detail.contains("s11"), "error must name the slice");
        assert!(
            error.detail.contains("s11-language-service"),
            "error must name the benchmark"
        );
        assert!(
            error.detail.contains("baseline"),
            "error must name the missing baseline"
        );
    }

    #[test]
    fn compare_detects_stale_host_identity() {
        let base = Quantiles::zero();
        let result = result_with_baseline(base, base);
        let mut machine = sample_machine();
        machine.cpu_model = "Different CPU".to_owned();
        let error = compare_with_conditions(
            &result,
            &budget_policy(),
            &sample_host(),
            &machine,
            &sample_observed_conditions(),
        )
        .unwrap_err();
        assert_eq!(error.code, PerfErrorCode::InvalidHost);
    }

    #[test]
    fn nearest_rank_uses_ceil_rank() {
        let samples = [10.0, 20.0, 30.0, 40.0];
        assert_eq!(nearest_rank(&samples, 0.50), 20.0);
        assert_eq!(nearest_rank(&samples, 0.95), 40.0);
        assert_eq!(nearest_rank(&[], 0.5), 0.0);
    }

    #[test]
    fn measured_result_carries_all_required_phase_keys_with_positive_total() {
        let candidate = Quantiles {
            p50: 12.5,
            p95: 18.0,
            p99: 20.0,
        };
        let result = result_with_baseline(Quantiles::zero(), candidate);
        // Every required phase key is present in the measured result.
        for key in PHASE_KEYS {
            assert!(
                result.phases.contains_key(key),
                "measured result must carry phase key `{key}`"
            );
        }
        // The gate accepts a complete result, and total wall is positive.
        require_phase_keys(&result.phases).expect("complete phase map passes the gate");
        assert!(result.phases["total"].p50 > 0.0, "total wall is positive");
    }

    #[test]
    fn require_phase_keys_rejects_a_missing_key_as_harness_error() {
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.phases.remove("check");
        let error = require_phase_keys(&result.phases)
            .expect_err("a result missing `check` must be rejected");
        assert_eq!(error.code, PerfErrorCode::HarnessError);
        assert_eq!(error.code.exit_code(), 6);
        assert!(error.detail.contains("check"));
    }

    #[test]
    fn load_baseline_rejects_missing_total_phase() {
        // A baseline JSON that parsed successfully but has no `total` phase key
        // must fail loudly with NoBaseline, not silently fall back to zero and
        // pass every wall-time budget.
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.phases.remove("total");
        let json = serde_json::to_string_pretty(&result).expect("serialize baseline");
        let dir = std::env::temp_dir();
        let path = dir.join("bamts_perf_baseline_no_total.json");
        std::fs::write(&path, &json).expect("write temp baseline");
        let error = load_baseline(
            Some(&path),
            &HostManifest {
                schema: PERF_SCHEMA_VERSION,
                host: "BH1".to_owned(),
                fingerprint: HostFingerprint {
                    kernel_release: "7.0.0-28-generic".to_owned(),
                    kernel_version: "#28-Ubuntu SMP PREEMPT_DYNAMIC".to_owned(),
                    arch: "x86_64".to_owned(),
                    cpu_model: "Intel(R) Xeon(R) Gold 6138 CPU @ 2.00GHz".to_owned(),
                    sockets: 2,
                    cores_per_socket: 20,
                    microcode: "0x2007006".to_owned(),
                },
                conditions: sample_conditions(),
                source: BTreeMap::new(),
            },
        )
        .expect_err("baseline missing `total` must be rejected")
        .code;
        assert_eq!(error, PerfErrorCode::NoBaseline);
        assert_eq!(error.exit_code(), 4);
        let _ = std::fs::remove_file(&path);
    }

    #[cfg(target_os = "linux")]
    fn parse_proc_status_value(rest: &str, field: &str) -> Result<u64> {
        let kib: u64 = rest
            .split_whitespace()
            .next()
            .ok_or_else(|| PerfError::harness(format!("/proc/self/status: {field} has no value")))?
            .parse()
            .map_err(|error| {
                PerfError::harness(format!(
                    "/proc/self/status: {field} is not a number: {error}"
                ))
            })?;
        Ok(kib * 1024)
    }

    #[cfg(target_os = "linux")]
    /// Reads the current `(VmHWM, VmRSS)` pair from a single `/proc/self/status`
    /// snapshot so the test compares the two fields atomically.
    fn read_hwm_and_rss() -> Result<(u64, u64)> {
        let content = std::fs::read_to_string("/proc/self/status")
            .map_err(|error| PerfError::harness(format!("/proc/self/status: {error}")))?;
        let mut hwm = None;
        let mut rss = None;
        for line in content.lines() {
            if let Some(rest) = line.strip_prefix("VmHWM:") {
                hwm = Some(parse_proc_status_value(rest, "VmHWM")?);
            } else if let Some(rest) = line.strip_prefix("VmRSS:") {
                rss = Some(parse_proc_status_value(rest, "VmRSS")?);
            }
        }
        match (hwm, rss) {
            (Some(h), Some(r)) => Ok((h, r)),
            (None, _) => Err(PerfError::harness("/proc/self/status: VmHWM not found")),
            (_, None) => Err(PerfError::harness("/proc/self/status: VmRSS not found")),
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[ignore = "requires Node 24.18.0 or /proc/self/clear_refs permission; external_blocked in this environment"]
    fn reset_peak_rss_resets_hwm_to_current_rss() {
        // Raise the high-water mark by faulting in a large allocation.
        let (hwm_before, _rss_before) =
            read_hwm_and_rss().expect("read /proc/self/status before allocation");
        let big = {
            let mut v = vec![0u8; 64 * 1024 * 1024];
            for i in (0..v.len()).step_by(4096) {
                v[i] = 1;
            }
            std::hint::black_box(v)
        };
        let (hwm_during, _rss_during) =
            read_hwm_and_rss().expect("read /proc/self/status during allocation");
        assert!(hwm_during >= hwm_before, "allocation must not lower VmHWM");

        // Dropping the allocation returns the mapped pages to the OS on glibc,
        // lowering current RSS while leaving the lifetime HWM high.
        drop(big);

        reset_peak_rss().expect("reset VmHWM");

        let (hwm_after, rss_after) =
            read_hwm_and_rss().expect("read /proc/self/status after reset");
        assert!(
            hwm_after > 0,
            "VmHWM after reset must be positive, not fake"
        );
        assert!(
            hwm_after >= rss_after,
            "VmHWM cannot be below current VmRSS (hwm={hwm_after}, rss={rss_after})"
        );
        assert!(
            hwm_after <= rss_after + 8 * 1024 * 1024,
            "VmHWM after reset must be near current VmRSS (within test overhead); \
             got hwm={hwm_after}, rss={rss_after}"
        );
    }

    #[cfg(not(target_os = "linux"))]
    #[test]
    fn peak_rss_sampling_is_unsupported_outside_linux() {
        // Resetting and reading VmHWM are platform-specific; on non-Linux they
        // must fail with a typed, contextual error rather than return fake data.
        let reset =
            reset_peak_rss().expect_err("reset should fail on non-Linux with a contextual error");
        assert_eq!(reset.code, PerfErrorCode::HarnessError);
        assert!(
            reset.detail.contains("Linux"),
            "reset error must name the platform"
        );

        let read = read_peak_rss_bytes()
            .expect_err("read should fail on non-Linux with a contextual error");
        assert_eq!(read.code, PerfErrorCode::HarnessError);
        assert!(
            read.detail.contains("Linux"),
            "read error must name the platform"
        );
    }

    #[test]
    fn evaluate_budgets_rejects_missing_total_phase() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        result.phases.remove("total");
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::HarnessError);
        assert!(
            error.detail.contains("total"),
            "error must name the missing phase"
        );
        assert!(
            error.detail.contains(&result.slice),
            "error must name the slice"
        );
    }

    #[test]
    fn evaluate_budgets_rejects_zero_baseline_wall() {
        let mut result = result_with_baseline(
            Quantiles::zero(),
            Quantiles {
                p50: 100.0,
                p95: 100.0,
                p99: 100.0,
            },
        );
        result.selected = true;
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::NoBaseline);
        assert!(
            error.detail.contains("wall.p50"),
            "error must name the field"
        );
        assert!(
            error.detail.contains("degenerate"),
            "error must identify the baseline as degenerate"
        );
    }

    #[test]
    fn evaluate_budgets_rejects_nan_baseline_wall() {
        let mut base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        base.p95 = f64::NAN;
        let candidate = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::NoBaseline);
        assert!(
            error.detail.contains("wall.p95"),
            "error must name the field"
        );
        assert!(error.detail.contains("NaN") || error.detail.contains("degenerate"));
    }

    #[test]
    fn evaluate_budgets_rejects_infinite_baseline_wall() {
        let mut result = result_with_baseline(
            Quantiles {
                p50: f64::INFINITY,
                p95: 100.0,
                p99: 100.0,
            },
            Quantiles {
                p50: 100.0,
                p95: 100.0,
                p99: 100.0,
            },
        );
        result.selected = true;
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::NoBaseline);
        assert!(
            error.detail.contains("wall.p50"),
            "error must name the field"
        );
        assert!(error.detail.contains("degenerate"));
    }

    #[test]
    fn evaluate_budgets_rejects_nan_candidate_wall() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let mut candidate = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        candidate.p99 = f64::NAN;
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::HarnessError);
        assert!(
            error.detail.contains("wall.p99"),
            "error must name the field"
        );
        assert!(error.detail.contains("non-finite"));
    }

    #[test]
    fn evaluate_budgets_rejects_infinite_candidate_rss() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        result.rss_bytes.p95 = f64::INFINITY;
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::HarnessError);
        assert!(
            error.detail.contains("rss.p95"),
            "error must name the field"
        );
        assert!(error.detail.contains("non-finite"));
    }

    #[test]
    fn evaluate_budgets_rejects_nan_release_ratio() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        result.baseline.as_mut().unwrap().release = Some(ReleaseBaseline {
            comparator: "typescript@7.0.2".to_owned(),
            wall_p95_ratio: f64::NAN,
            geomean_ratio: 0.95,
        });
        let error = evaluate_budgets(&result, &budget_policy()).unwrap_err();
        assert_eq!(error.code, PerfErrorCode::NoBaseline);
        assert!(
            error.detail.contains("release"),
            "error must mention release ratios"
        );
    }

    #[test]
    fn evaluate_budgets_passes_valid_selected_baseline() {
        let base = Quantiles {
            p50: 100.0,
            p95: 100.0,
            p99: 100.0,
        };
        let candidate = Quantiles {
            p50: 103.0,
            p95: 108.0,
            p99: 110.0,
        };
        let mut result = result_with_baseline(base, candidate);
        result.selected = true;
        assert!(
            evaluate_budgets(&result, &budget_policy()).is_ok(),
            "valid selected baseline must pass the budget gate"
        );
    }

    #[test]
    fn schema_v2_pins_process_placement() {
        assert_eq!(PERF_SCHEMA_VERSION, 2);
        assert!(require_schema(Path::new("v1.toml"), 1).is_err());

        let host = sample_host();
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.schema = 1;
        assert_eq!(
            compare_with_conditions(
                &result,
                &budget_policy(),
                &host,
                &sample_machine(),
                &sample_observed_conditions(),
            )
            .unwrap_err()
            .code,
            PerfErrorCode::InvalidHost
        );
        let mut card = sample_scorecard(&host);
        card.schema = 1;
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::HarnessError
        );
    }

    #[test]
    fn recorded_expected_condition_drift_is_invalid_conditions() {
        let host = sample_host();
        let mut result = result_with_baseline(Quantiles::zero(), Quantiles::zero());
        result.conditions_expected.memory_policy = "default".to_owned();
        assert_eq!(
            compare_with_conditions(
                &result,
                &budget_policy(),
                &host,
                &sample_machine(),
                &sample_observed_conditions(),
            )
            .unwrap_err()
            .code,
            PerfErrorCode::InvalidConditions
        );

        let mut card = sample_scorecard(&host);
        card.conditions_expected.memory_nodes = "0-1".to_owned();
        assert_eq!(
            validate_scorecard(&card, &host, "typescript@7.0.2")
                .unwrap_err()
                .code,
            PerfErrorCode::InvalidConditions
        );
    }

    #[test]
    fn observed_conditions_match_every_field_exactly() {
        let expected = sample_conditions();
        let observed = sample_observed_conditions();
        assert!(observed.satisfies(&expected));

        let mismatches = [
            ObservedConditions {
                governor: "powersave".to_owned(),
                ..observed.clone()
            },
            ObservedConditions {
                swap_total_kib: 1,
                ..observed.clone()
            },
            ObservedConditions {
                cpu_affinity: "0-18".to_owned(),
                ..observed.clone()
            },
            ObservedConditions {
                memory_policy: "default".to_owned(),
                ..observed.clone()
            },
            ObservedConditions {
                memory_nodes: "0-1".to_owned(),
                ..observed
            },
        ];
        for mismatch in mismatches {
            assert!(!mismatch.satisfies(&expected));
        }
    }
}
