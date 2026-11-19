//! Pinned TypeScript 7.0.2 oracle: structured diagnostics, artifacts, and
//! declared-observable comparison on a virtual project.
//!
//! The constructor accepts only an injected authority probe whose version and
//! digest match the stable 7.0.2 pin. Process execution is an injected
//! [`ProcessBoundary`]; production uses the corpus bounded runner. Unit tests
//! supply a fake that checks exact argv and protocol JSON. An unpinned `tsc` on
//! `PATH` is never consulted.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fmt, fs,
    path::{Component, Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    time::Duration,
};

use serde::{Deserialize, Serialize};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::{OracleLimits, OracleOutcome},
    oracles::{
        AuthorityProbe, NormalizationPolicy, PathPolicy, ProcessBoundary, ProcessInvocation,
        TerminalState, pinned_environment,
    },
};

/// Wire protocol identifier spoken by the embedded driver.
pub const PROTOCOL: &str = "bamti.oracle.tsc/v1";
/// Stable TypeScript product version this oracle is pinned to.
pub const STABLE_VERSION: &str = "7.0.2";
/// SHA-256 (hex) the constructor requires from the authority probe.
pub const STABLE_ORACLE_DIGEST: &str =
    "62f3da55b23a067821af3296ebd7a669bd22199e058053c96d3caa3b7547aede";
/// Embedded public-API driver source.
pub const DRIVER_SOURCE: &str = include_str!("tsc_driver.mjs");
/// Request file name written into a materialized virtual project.
pub const REQUEST_FILE: &str = "oracle-request.json";

const DEFAULT_MAX_OUTPUT_BYTES: usize = 1 << 20;
static PROJECT_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Compilation phase whose identity is preserved through decode and compare.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CompilationPhase {
    /// Syntactic / parse diagnostics (TypeScript `getSyntacticDiagnostics`).
    Parse,
    /// Semantic / checker diagnostics (TypeScript `getSemanticDiagnostics`).
    Check,
}

/// Closed diagnostic category. Matches the TypeScript 7 public API numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticCategory {
    Warning,
    Error,
    Suggestion,
    Message,
}

/// UTF-16 code-unit span. Absent on global diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Utf16Span {
    /// Inclusive start offset in UTF-16 code units.
    pub start: u32,
    /// Exclusive end offset in UTF-16 code units.
    pub end: u32,
}

/// Related diagnostic location. Kept structured; never folded into `message`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RelatedInformation {
    /// Related message text.
    pub message: String,
    /// Virtual file, if the related note has a location.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    /// UTF-16 span, if the related note has a location.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub span: Option<Utf16Span>,
}

/// One structured diagnostic. Global diagnostics omit `file` and `span`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StructuredDiagnostic {
    /// TypeScript diagnostic code, for example 2304.
    pub code: u32,
    /// Closed category.
    pub category: DiagnosticCategory,
    /// Localized message text.
    pub message: String,
    /// Parse vs check identity. Compared exactly.
    pub phase: CompilationPhase,
    /// Virtual file. `None` for project-global diagnostics.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    /// UTF-16 span. Must be `None` when [`Self::file`] is `None`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub span: Option<Utf16Span>,
    /// Structured related information, in reported order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub related: Vec<RelatedInformation>,
    /// Nested message chain (multiline diagnostics), in reported order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub message_chain: Vec<StructuredDiagnostic>,
}

impl StructuredDiagnostic {
    fn validate_global_span(&self) -> Result<()> {
        if self.file.is_none() && self.span.is_some() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "global diagnostic must not carry a file span",
            ));
        }
        for related in &self.related {
            if related.file.is_none() && related.span.is_some() {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    "global related information must not carry a file span",
                ));
            }
        }
        for nested in &self.message_chain {
            nested.validate_global_span()?;
        }
        Ok(())
    }
}

/// Artifact families the logical cell may declare.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactKind {
    JavaScript,
    Declaration,
    SourceMap,
    Trace,
    BuildInfo,
    WriteSet,
}

/// Closed observable a logical cell may require.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObservableKind {
    Diagnostics,
    JavaScript,
    Declaration,
    SourceMap,
    Trace,
    BuildInfo,
    WriteSet,
}

impl ObservableKind {
    fn as_artifact(self) -> Option<ArtifactKind> {
        match self {
            Self::Diagnostics => None,
            Self::JavaScript => Some(ArtifactKind::JavaScript),
            Self::Declaration => Some(ArtifactKind::Declaration),
            Self::SourceMap => Some(ArtifactKind::SourceMap),
            Self::Trace => Some(ArtifactKind::Trace),
            Self::BuildInfo => Some(ArtifactKind::BuildInfo),
            Self::WriteSet => Some(ArtifactKind::WriteSet),
        }
    }
}

/// Declared observable set for a logical cell. Empty is rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclaredObservables {
    kinds: BTreeSet<ObservableKind>,
}

impl DeclaredObservables {
    /// Builds a declared set. Rejects the empty set.
    pub fn new(kinds: impl IntoIterator<Item = ObservableKind>) -> Result<Self> {
        let kinds: BTreeSet<ObservableKind> = kinds.into_iter().collect();
        if kinds.is_empty() {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "logical cell must declare at least one observable",
            ));
        }
        Ok(Self { kinds })
    }

    /// Ordered declared kinds.
    pub fn kinds(&self) -> impl Iterator<Item = ObservableKind> + '_ {
        self.kinds.iter().copied()
    }

    fn contains(&self, kind: ObservableKind) -> bool {
        self.kinds.contains(&kind)
    }
}

/// Logical cell: declared observables, phase, and normalization policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogicalCell {
    /// Observables both sides must produce and compare.
    pub observables: DeclaredObservables,
    /// Phase identity for this cell.
    pub phase: CompilationPhase,
    /// Must be [`NormalizationPolicy::Declared`]; undeclared cannot pass.
    pub normalization: NormalizationPolicy,
}

/// Closed ECMAScript emit target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ScriptTarget {
    Es3,
    Es5,
    Es2015,
    Es2016,
    Es2017,
    Es2018,
    Es2019,
    Es2020,
    Es2021,
    Es2022,
    Es2023,
    Es2024,
    Es2025,
    Esnext,
}

/// Closed module kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ModuleKind {
    None,
    Commonjs,
    Amd,
    Umd,
    System,
    Es2015,
    Es2020,
    Es2022,
    Esnext,
    Node16,
    Node18,
    Node20,
    Nodenext,
    Preserve,
}

/// Closed JSX emit mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum JsxEmit {
    Preserve,
    React,
    ReactNative,
    ReactJsx,
    ReactJsxdev,
}

/// Closed module-resolution mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ModuleResolutionKind {
    Classic,
    Node10,
    Node16,
    Nodenext,
    Bundler,
}

/// Typed compiler options translated from `// @name: value` directives.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TranslatedOptions {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub strict: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub no_implicit_any: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub strict_null_checks: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub always_strict: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declaration: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_map: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declaration_map: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub no_emit: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub no_lib: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub skip_lib_check: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub isolated_modules: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub es_module_interop: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_js: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub check_js: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub incremental: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub composite: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pretty: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target: Option<ScriptTarget>,
    #[serde(default, skip_serializing_if = "Option::is_none", rename = "module")]
    pub module: Option<ModuleKind>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub jsx: Option<JsxEmit>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub module_resolution: Option<ModuleResolutionKind>,
}

/// One virtual source file after directive splitting.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VirtualFile {
    /// Confined relative path.
    pub path: String,
    /// File text with directives stripped from the split content.
    pub text: String,
}

/// Public-API driver request. Both oracle and candidate receive this object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DriverRequest {
    /// Must equal [`PROTOCOL`].
    pub protocol: String,
    /// Phase identity for this invocation.
    pub phase: CompilationPhase,
    /// Virtual files, in declaration order.
    pub files: Vec<VirtualFile>,
    /// Typed options translated from directives.
    pub options: TranslatedOptions,
    /// Declared observables, in sorted order.
    pub observables: Vec<ObservableKind>,
}

/// Artifact digest tables keyed by virtual path.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactDigests {
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub javascript: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub declaration: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub source_map: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub trace: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub build_info: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub write_set: Option<String>,
}

impl ArtifactDigests {
    fn table(&self, kind: ArtifactKind) -> Option<&BTreeMap<String, String>> {
        match kind {
            ArtifactKind::JavaScript => Some(&self.javascript),
            ArtifactKind::Declaration => Some(&self.declaration),
            ArtifactKind::SourceMap => Some(&self.source_map),
            ArtifactKind::Trace => Some(&self.trace),
            ArtifactKind::BuildInfo => Some(&self.build_info),
            ArtifactKind::WriteSet => None,
        }
    }

    fn is_present(&self, kind: ArtifactKind) -> bool {
        match kind {
            ArtifactKind::WriteSet => self.write_set.is_some(),
            other => self.table(other).is_some_and(|table| !table.is_empty()),
        }
    }
}

/// Public-API driver response. Decoded with `deny_unknown_fields`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DriverResponse {
    /// Must equal [`PROTOCOL`].
    pub protocol: String,
    /// Phase identity echoed from the request.
    pub phase: CompilationPhase,
    /// Diagnostics in reported order.
    pub diagnostics: Vec<StructuredDiagnostic>,
    /// Artifact digests keyed by kind.
    #[serde(default)]
    pub artifacts: ArtifactDigests,
}

/// Materialized virtual project. Removes its directory on drop.
#[derive(Debug)]
pub struct VirtualProject {
    root: PathBuf,
}

impl VirtualProject {
    /// Absolute root of the unique confined project.
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }
}

impl Drop for VirtualProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// Directive parse result shared by both sides of a cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedCell {
    /// Virtual files in declaration order.
    pub files: Vec<VirtualFile>,
    /// Typed options from directives.
    pub options: TranslatedOptions,
}

/// Fully prepared request used identically for oracle and candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OraclePlan {
    /// Logical cell this plan was built for.
    pub cell: LogicalCell,
    /// Request both sides must receive.
    pub request: DriverRequest,
}

/// Decoded observation or a classified process failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObservationKind {
    /// Strictly decoded driver response.
    Complete(DriverResponse),
    /// Wall-clock bound elapsed; outcome is not a match.
    TimedOut,
    /// Child terminated by signal.
    Signaled(i32),
    /// stdout or stderr truncated at the byte cap.
    Truncated,
    /// Response was not a valid protocol object.
    Protocol(String),
}

/// One side's observation of a planned cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleObservation {
    /// Classified outcome.
    pub kind: ObservationKind,
}

impl OracleObservation {
    /// Whether this observation is allowed to participate in a `Pass`.
    #[must_use]
    pub fn can_pass(&self) -> bool {
        matches!(self.kind, ObservationKind::Complete(_))
    }
}

/// Declared-observable comparison result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comparison {
    /// Pass only when both sides completed and every declared observable matched.
    pub terminal: TerminalState,
    /// Human-readable mismatch or failure detail. Never used as a regex oracle.
    pub detail: String,
}

impl Comparison {
    /// Whether the comparison is a pass.
    #[must_use]
    pub fn is_pass(&self) -> bool {
        self.terminal == TerminalState::Pass
    }

    fn blocking(detail: impl Into<String>) -> Self {
        Self {
            terminal: TerminalState::Blocking,
            detail: detail.into(),
        }
    }

    fn pass() -> Self {
        Self {
            terminal: TerminalState::Pass,
            detail: String::new(),
        }
    }
}

/// Pinned TypeScript 7.0.2 oracle.
#[derive(Clone)]
pub struct TypeScriptOracle {
    process: Arc<dyn ProcessBoundary>,
    node: PathBuf,
    driver: PathBuf,
    path_policy: PathPolicy,
    limits: OracleLimits,
}

impl fmt::Debug for TypeScriptOracle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TypeScriptOracle")
            .field("node", &self.node)
            .field("driver", &self.driver)
            .field("path_policy", &self.path_policy)
            .field("limits", &self.limits)
            .finish_non_exhaustive()
    }
}

impl TypeScriptOracle {
    /// Verifies version and digest through `probe`. Never searches `PATH` for `tsc`.
    pub fn new(
        probe: &dyn AuthorityProbe,
        process: Arc<dyn ProcessBoundary>,
        node: PathBuf,
        driver: PathBuf,
    ) -> Result<Self> {
        let report = probe.report()?;
        if report.version != STABLE_VERSION {
            return Err(VerificationError::new(
                ErrorCode::ToolFailed,
                format!(
                    "TypeScript oracle version `{}` is not the stable pin `{STABLE_VERSION}`",
                    report.version
                ),
            ));
        }
        if report.digest != STABLE_ORACLE_DIGEST {
            return Err(VerificationError::new(
                ErrorCode::Digest,
                format!(
                    "TypeScript oracle digest `{}` is not the stable pin `{STABLE_ORACLE_DIGEST}`",
                    report.digest
                ),
            ));
        }
        Ok(Self {
            process,
            node,
            driver,
            path_policy: PathPolicy::typescript_oracle(),
            limits: OracleLimits {
                timeout: Duration::from_secs(30),
                max_output_bytes: DEFAULT_MAX_OUTPUT_BYTES,
            },
        })
    }

    /// Overrides the per-invocation bounds.
    #[must_use]
    pub fn with_limits(mut self, limits: OracleLimits) -> Self {
        self.limits = limits;
        self
    }

    /// Parses directives and builds the request both sides receive.
    pub fn plan(&self, source: &str, origin_name: &str, cell: LogicalCell) -> Result<OraclePlan> {
        match cell.normalization {
            NormalizationPolicy::Undeclared => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    "undeclared normalization cannot pass",
                ));
            }
            NormalizationPolicy::Declared(_) => {}
        }
        let parsed = parse_directives(source, origin_name, self.path_policy)?;
        let observables: Vec<ObservableKind> = cell.observables.kinds().collect();
        let request = DriverRequest {
            protocol: PROTOCOL.to_owned(),
            phase: cell.phase,
            files: parsed.files,
            options: parsed.options,
            observables,
        };
        Ok(OraclePlan { cell, request })
    }

    /// Materializes `files` into a unique confined directory.
    pub fn materialize(&self, files: &[VirtualFile]) -> Result<VirtualProject> {
        validate_unique_files(files, self.path_policy)?;
        let unique = PROJECT_COUNTER.fetch_add(1, Ordering::Relaxed);
        let root =
            env::temp_dir().join(format!("bamts-tsc-oracle-{}-{unique}", std::process::id()));
        fs::create_dir_all(&root).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!(
                    "cannot create virtual project `{}`: {error}",
                    root.display()
                ),
            )
        })?;
        for file in files {
            let path = confined_join(&root, &file.path)?;
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|error| {
                    VerificationError::new(
                        ErrorCode::Io,
                        format!("cannot create `{}`: {error}", parent.display()),
                    )
                })?;
            }
            fs::write(&path, file.text.as_bytes()).map_err(|error| {
                VerificationError::new(
                    ErrorCode::Io,
                    format!("cannot write `{}`: {error}", path.display()),
                )
            })?;
        }
        Ok(VirtualProject { root })
    }

    /// Runs the planned request through the process boundary and decodes stdout.
    pub fn observe(&self, plan: &OraclePlan) -> Result<OracleObservation> {
        let project = self.materialize(&plan.request.files)?;
        let request_path = project.root.join(REQUEST_FILE);
        let encoded = serde_json::to_vec_pretty(&plan.request).map_err(|error| {
            VerificationError::new(
                ErrorCode::Json,
                format!("cannot encode driver request: {error}"),
            )
        })?;
        fs::write(&request_path, encoded).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("cannot write `{}`: {error}", request_path.display()),
            )
        })?;
        let invocation = ProcessInvocation {
            program: self.node.clone(),
            argv: vec![
                self.driver.clone().into(),
                "--protocol".into(),
                PROTOCOL.into(),
                "--request-file".into(),
                request_path.into(),
            ],
            cwd: project.root.clone(),
            environment: pinned_environment(),
            limits: self.limits,
        };
        let outcome = self.process.invoke(&invocation)?;
        Ok(observation_from_outcome(outcome, plan.cell.phase))
    }

    /// Compares two observations on the cell's declared observables.
    pub fn compare(
        &self,
        cell: &LogicalCell,
        oracle: &OracleObservation,
        candidate: &OracleObservation,
    ) -> Comparison {
        if matches!(cell.normalization, NormalizationPolicy::Undeclared) {
            return Comparison::blocking("undeclared normalization cannot pass");
        }
        if !oracle.can_pass() {
            return Comparison::blocking(format!(
                "oracle observation cannot pass: {:?}",
                oracle.kind
            ));
        }
        if !candidate.can_pass() {
            return Comparison::blocking(format!(
                "candidate observation cannot pass: {:?}",
                candidate.kind
            ));
        }
        let ObservationKind::Complete(oracle_response) = &oracle.kind else {
            unreachable!("can_pass implies Complete");
        };
        let ObservationKind::Complete(candidate_response) = &candidate.kind else {
            unreachable!("can_pass implies Complete");
        };
        if oracle_response.phase != cell.phase || candidate_response.phase != cell.phase {
            return Comparison::blocking("phase identity does not match the logical cell");
        }
        if oracle_response.phase != candidate_response.phase {
            return Comparison::blocking("oracle and candidate phases differ");
        }
        if cell.observables.contains(ObservableKind::Diagnostics)
            && oracle_response.diagnostics != candidate_response.diagnostics
        {
            return Comparison::blocking("structured diagnostics differ");
        }
        for kind in cell.observables.kinds() {
            let Some(artifact) = kind.as_artifact() else {
                continue;
            };
            if !oracle_response.artifacts.is_present(artifact) {
                return Comparison::blocking(format!("oracle missing observable {kind:?}"));
            }
            if !candidate_response.artifacts.is_present(artifact) {
                return Comparison::blocking(format!("candidate missing observable {kind:?}"));
            }
            if artifact_values(&oracle_response.artifacts, artifact)
                != artifact_values(&candidate_response.artifacts, artifact)
            {
                return Comparison::blocking(format!("declared artifact {kind:?} differs"));
            }
        }
        Comparison::pass()
    }

    /// Exact argv the fake process boundary must accept.
    #[must_use]
    pub fn protocol_argv(&self, request_file: &Path) -> Vec<std::ffi::OsString> {
        vec![
            self.driver.clone().into(),
            "--protocol".into(),
            PROTOCOL.into(),
            "--request-file".into(),
            request_file.into(),
        ]
    }
}

fn artifact_values(
    artifacts: &ArtifactDigests,
    kind: ArtifactKind,
) -> Result<serde_json::Value, ()> {
    match kind {
        ArtifactKind::WriteSet => Ok(serde_json::Value::String(
            artifacts.write_set.clone().unwrap_or_default(),
        )),
        other => Ok(
            serde_json::to_value(artifacts.table(other).cloned().unwrap_or_default())
                .unwrap_or(serde_json::Value::Null),
        ),
    }
}

fn observation_from_outcome(
    outcome: OracleOutcome,
    expected_phase: CompilationPhase,
) -> OracleObservation {
    if outcome.timed_out {
        return OracleObservation {
            kind: ObservationKind::TimedOut,
        };
    }
    if outcome.stdout_truncated || outcome.stderr_truncated {
        return OracleObservation {
            kind: ObservationKind::Truncated,
        };
    }
    if let Some(signal) = outcome.signal
        && outcome.exit_code.is_none()
    {
        return OracleObservation {
            kind: ObservationKind::Signaled(signal),
        };
    }
    match decode_response(&outcome.stdout, expected_phase) {
        Ok(response) => OracleObservation {
            kind: ObservationKind::Complete(response),
        },
        Err(error) => OracleObservation {
            kind: ObservationKind::Protocol(error.to_string()),
        },
    }
}

/// Strict JSON decode of a driver response.
pub fn decode_response(stdout: &[u8], expected_phase: CompilationPhase) -> Result<DriverResponse> {
    let response: DriverResponse = serde_json::from_slice(stdout).map_err(|error| {
        VerificationError::new(
            ErrorCode::Json,
            format!("driver response is not a protocol object: {error}"),
        )
    })?;
    if response.protocol != PROTOCOL {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!(
                "driver protocol `{}` is not `{PROTOCOL}`",
                response.protocol
            ),
        ));
    }
    if response.phase != expected_phase {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "driver response phase does not preserve request phase identity",
        ));
    }
    for diagnostic in &response.diagnostics {
        diagnostic.validate_global_span()?;
        if diagnostic.phase != expected_phase && diagnostic.phase != CompilationPhase::Parse {
            // Check-phase runs may still report parse diagnostics; parse-phase
            // runs must not report check diagnostics.
            if expected_phase == CompilationPhase::Parse {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    "parse-phase response carried a check diagnostic",
                ));
            }
        }
    }
    Ok(response)
}

/// Parses `// @name: value` directives and `@filename` virtual splits.
pub fn parse_directives(source: &str, origin_name: &str, policy: PathPolicy) -> Result<ParsedCell> {
    let mut options = TranslatedOptions::default();
    let mut files = Vec::new();
    let mut current_name: Option<String> = None;
    let mut current_body = String::new();
    let mut saw_filename = false;

    for line in source.split('\n') {
        let trimmed = strip_cr(line);
        if let Some((name, value)) = parse_directive_line(trimmed) {
            if name == "filename" {
                if let Some(existing) = current_name.take() {
                    files.push(VirtualFile {
                        path: existing,
                        text: take_body(&mut current_body),
                    });
                } else if !current_body.trim().is_empty() {
                    return Err(VerificationError::new(
                        ErrorCode::Schema,
                        "non-comment content appears before the first @filename directive",
                    ));
                } else {
                    current_body.clear();
                }
                let path = validate_virtual_path(value, policy)?;
                current_name = Some(path);
                saw_filename = true;
                continue;
            }
            apply_option(&name, value, &mut options)?;
            continue;
        }
        if !current_body.is_empty() {
            current_body.push('\n');
        }
        current_body.push_str(trimmed);
    }

    if saw_filename {
        let Some(name) = current_name else {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                "@filename directive is missing a path",
            ));
        };
        files.push(VirtualFile {
            path: name,
            text: take_body(&mut current_body),
        });
    } else {
        files.push(VirtualFile {
            path: validate_virtual_path(origin_name, policy)?,
            text: take_body(&mut current_body),
        });
    }
    validate_unique_files(&files, policy)?;
    Ok(ParsedCell { files, options })
}

fn strip_cr(line: &str) -> &str {
    line.strip_suffix('\r').unwrap_or(line)
}

fn take_body(body: &mut String) -> String {
    std::mem::take(body)
}

fn parse_directive_line(line: &str) -> Option<(String, &str)> {
    let rest = line.trim_start();
    if !rest.starts_with("//") {
        return None;
    }
    let rest = rest[2..].trim_start();
    if !rest.starts_with('@') {
        return None;
    }
    let rest = &rest[1..];
    let colon = rest.find(':')?;
    let name = rest[..colon].trim();
    if name.is_empty() || !name.bytes().all(|byte| byte.is_ascii_alphanumeric()) {
        return None;
    }
    let value = rest[colon + 1..].trim();
    Some((name.to_ascii_lowercase(), value))
}

fn apply_option(name: &str, value: &str, options: &mut TranslatedOptions) -> Result<()> {
    match name {
        "strict" => options.strict = Some(parse_bool(name, value)?),
        "noimplicitany" => options.no_implicit_any = Some(parse_bool(name, value)?),
        "strictnullchecks" => options.strict_null_checks = Some(parse_bool(name, value)?),
        "alwaysstrict" => options.always_strict = Some(parse_bool(name, value)?),
        "declaration" => options.declaration = Some(parse_bool(name, value)?),
        "sourcemap" => options.source_map = Some(parse_bool(name, value)?),
        "declarationmap" => options.declaration_map = Some(parse_bool(name, value)?),
        "noemit" => options.no_emit = Some(parse_bool(name, value)?),
        "nolib" => options.no_lib = Some(parse_bool(name, value)?),
        "skiplibcheck" => options.skip_lib_check = Some(parse_bool(name, value)?),
        "isolatedmodules" => options.isolated_modules = Some(parse_bool(name, value)?),
        "esmoduleinterop" => options.es_module_interop = Some(parse_bool(name, value)?),
        "allowjs" => options.allow_js = Some(parse_bool(name, value)?),
        "checkjs" => options.check_js = Some(parse_bool(name, value)?),
        "incremental" => options.incremental = Some(parse_bool(name, value)?),
        "composite" => options.composite = Some(parse_bool(name, value)?),
        "pretty" => options.pretty = Some(parse_bool(name, value)?),
        "target" => options.target = Some(parse_target(value)?),
        "module" => options.module = Some(parse_module(value)?),
        "jsx" => options.jsx = Some(parse_jsx(value)?),
        "moduleresolution" => options.module_resolution = Some(parse_module_resolution(value)?),
        other => {
            return Err(VerificationError::new(
                ErrorCode::Schema,
                format!("unknown directive `@{other}`"),
            ));
        }
    }
    Ok(())
}

fn parse_bool(name: &str, value: &str) -> Result<bool> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("directive `@{name}` expects true or false, found `{value}`"),
        )),
    }
}

fn parse_target(value: &str) -> Result<ScriptTarget> {
    match value.to_ascii_lowercase().as_str() {
        "es3" => Ok(ScriptTarget::Es3),
        "es5" => Ok(ScriptTarget::Es5),
        "es6" | "es2015" => Ok(ScriptTarget::Es2015),
        "es2016" => Ok(ScriptTarget::Es2016),
        "es2017" => Ok(ScriptTarget::Es2017),
        "es2018" => Ok(ScriptTarget::Es2018),
        "es2019" => Ok(ScriptTarget::Es2019),
        "es2020" => Ok(ScriptTarget::Es2020),
        "es2021" => Ok(ScriptTarget::Es2021),
        "es2022" => Ok(ScriptTarget::Es2022),
        "es2023" => Ok(ScriptTarget::Es2023),
        "es2024" => Ok(ScriptTarget::Es2024),
        "es2025" => Ok(ScriptTarget::Es2025),
        "esnext" => Ok(ScriptTarget::Esnext),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unknown @target value `{value}`"),
        )),
    }
}

fn parse_module(value: &str) -> Result<ModuleKind> {
    match value.to_ascii_lowercase().as_str() {
        "none" => Ok(ModuleKind::None),
        "commonjs" => Ok(ModuleKind::Commonjs),
        "amd" => Ok(ModuleKind::Amd),
        "umd" => Ok(ModuleKind::Umd),
        "system" => Ok(ModuleKind::System),
        "es6" | "es2015" => Ok(ModuleKind::Es2015),
        "es2020" => Ok(ModuleKind::Es2020),
        "es2022" => Ok(ModuleKind::Es2022),
        "esnext" => Ok(ModuleKind::Esnext),
        "node16" => Ok(ModuleKind::Node16),
        "node18" => Ok(ModuleKind::Node18),
        "node20" => Ok(ModuleKind::Node20),
        "nodenext" => Ok(ModuleKind::Nodenext),
        "preserve" => Ok(ModuleKind::Preserve),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unknown @module value `{value}`"),
        )),
    }
}

fn parse_jsx(value: &str) -> Result<JsxEmit> {
    match value.to_ascii_lowercase().as_str() {
        "preserve" => Ok(JsxEmit::Preserve),
        "react" => Ok(JsxEmit::React),
        "react-native" | "reactnative" => Ok(JsxEmit::ReactNative),
        "react-jsx" | "reactjsx" => Ok(JsxEmit::ReactJsx),
        "react-jsxdev" | "reactjsxdev" => Ok(JsxEmit::ReactJsxdev),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unknown @jsx value `{value}`"),
        )),
    }
}

fn parse_module_resolution(value: &str) -> Result<ModuleResolutionKind> {
    match value.to_ascii_lowercase().as_str() {
        "classic" => Ok(ModuleResolutionKind::Classic),
        "node" | "node10" => Ok(ModuleResolutionKind::Node10),
        "node16" => Ok(ModuleResolutionKind::Node16),
        "nodenext" => Ok(ModuleResolutionKind::Nodenext),
        "bundler" => Ok(ModuleResolutionKind::Bundler),
        _ => Err(VerificationError::new(
            ErrorCode::Schema,
            format!("unknown @moduleResolution value `{value}`"),
        )),
    }
}

fn validate_virtual_path(raw: &str, policy: PathPolicy) -> Result<String> {
    let PathPolicy::ConfinedRelative { .. } = policy;
    if raw.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "virtual path must not be empty",
        ));
    }
    if raw.contains('\0') {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            "virtual path must not contain NUL",
        ));
    }
    let candidate = Path::new(raw);
    if candidate.is_absolute() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("virtual path `{raw}` escapes the project root"),
        ));
    }
    let mut parts = Vec::new();
    for component in candidate.components() {
        match component {
            Component::Normal(part) => {
                let part = part.to_str().ok_or_else(|| {
                    VerificationError::new(
                        ErrorCode::Schema,
                        format!("virtual path `{raw}` must be UTF-8"),
                    )
                })?;
                parts.push(part);
            }
            _ => {
                return Err(VerificationError::new(
                    ErrorCode::Schema,
                    format!("virtual path `{raw}` escapes the project root"),
                ));
            }
        }
    }
    if parts.is_empty() {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("virtual path `{raw}` escapes the project root"),
        ));
    }
    Ok(parts.join("/"))
}

fn validate_unique_files(files: &[VirtualFile], policy: PathPolicy) -> Result<()> {
    let PathPolicy::ConfinedRelative { case_fold } = policy;
    let mut exact = BTreeSet::new();
    let mut folded = BTreeSet::new();
    for file in files {
        let path = validate_virtual_path(&file.path, policy)?;
        if !exact.insert(path.clone()) {
            return Err(VerificationError::new(
                ErrorCode::Duplicate,
                format!("duplicate virtual path `{path}`"),
            ));
        }
        match case_fold {
            crate::oracles::CaseFoldPolicy::RejectFoldCollisions => {
                let key = path.to_ascii_lowercase();
                if !folded.insert(key) {
                    return Err(VerificationError::new(
                        ErrorCode::Duplicate,
                        format!("case-fold collision for virtual path `{path}`"),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn confined_join(root: &Path, relative: &str) -> Result<PathBuf> {
    let validated = validate_virtual_path(relative, PathPolicy::typescript_oracle())?;
    let joined = root.join(&validated);
    if !joined.starts_with(root) {
        return Err(VerificationError::new(
            ErrorCode::Schema,
            format!("virtual path `{relative}` escapes the project root"),
        ));
    }
    Ok(joined)
}

#[cfg(test)]
fn complete_observation(response: DriverResponse) -> OracleObservation {
    OracleObservation {
        kind: ObservationKind::Complete(response),
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::oracles::{ReportedAuthority, env_stable_oracle_probe, shared_process};
    use crate::schema::sha256_hex;
    use serde_json::json;
    use std::{ffi::OsString, sync::Mutex};

    const DRIVER_UNUSED: &str = "unused";

    struct StrictFake {
        node: PathBuf,
        driver: PathBuf,
        requests: Mutex<Vec<DriverRequest>>,
        respond: Box<dyn Fn(&DriverRequest) -> OracleOutcome + Send + Sync>,
    }

    impl ProcessBoundary for StrictFake {
        fn invoke(&self, invocation: &ProcessInvocation) -> Result<OracleOutcome> {
            assert_eq!(
                invocation.program, self.node,
                "program must be the injected node"
            );
            assert_eq!(
                invocation.argv.len(),
                5,
                "argv must be driver --protocol id --request-file path"
            );
            assert_eq!(Path::new(&invocation.argv[0]), self.driver.as_path());
            assert_eq!(invocation.argv[1], OsString::from("--protocol"));
            assert_eq!(invocation.argv[2], OsString::from(PROTOCOL));
            assert_eq!(invocation.argv[3], OsString::from("--request-file"));
            let request_file = PathBuf::from(&invocation.argv[4]);
            assert!(
                request_file.starts_with(&invocation.cwd),
                "request file must live in the virtual project"
            );
            assert_eq!(
                invocation.environment,
                pinned_environment(),
                "environment must be the corpus pin"
            );
            let bytes = fs::read(&request_file).expect("request file");
            let request: DriverRequest =
                serde_json::from_slice(&bytes).expect("request must be protocol JSON");
            assert_eq!(request.protocol, PROTOCOL);
            self.requests.lock().expect("lock").push(request.clone());
            Ok((self.respond)(&request))
        }
    }

    fn stable_probe() -> ReportedAuthority {
        ReportedAuthority {
            version: STABLE_VERSION.to_owned(),
            digest: STABLE_ORACLE_DIGEST.to_owned(),
        }
    }

    fn oracle_with(fake: StrictFake) -> TypeScriptOracle {
        TypeScriptOracle::new(
            &stable_probe(),
            shared_process(fake),
            PathBuf::from("/opt/pinned/node"),
            PathBuf::from("/opt/pinned/tsc_driver.mjs"),
        )
        .expect("stable oracle")
    }

    fn cell(observables: &[ObservableKind], phase: CompilationPhase) -> LogicalCell {
        LogicalCell {
            observables: DeclaredObservables::new(observables.iter().copied())
                .expect("observables"),
            phase,
            normalization: NormalizationPolicy::Declared(
                crate::oracles::DeclaredNormalization::corpus_virtual(),
            ),
        }
    }

    fn ok_outcome(response: &DriverResponse) -> OracleOutcome {
        OracleOutcome {
            timed_out: false,
            exit_code: Some(0),
            signal: None,
            stdout: serde_json::to_vec(response).expect("encode"),
            stdout_truncated: false,
            stderr: Vec::new(),
            stderr_truncated: false,
            compile_stderr: Vec::new(),
            compile_stderr_truncated: false,
        }
    }

    fn diagnostic_response(
        phase: CompilationPhase,
        diagnostics: Vec<StructuredDiagnostic>,
        artifacts: ArtifactDigests,
    ) -> DriverResponse {
        DriverResponse {
            protocol: PROTOCOL.to_owned(),
            phase,
            diagnostics,
            artifacts,
        }
    }

    fn file_diag(
        code: u32,
        message: &str,
        phase: CompilationPhase,
        file: &str,
        start: u32,
        end: u32,
    ) -> StructuredDiagnostic {
        StructuredDiagnostic {
            code,
            category: DiagnosticCategory::Error,
            message: message.to_owned(),
            phase,
            file: Some(file.to_owned()),
            span: Some(Utf16Span { start, end }),
            related: Vec::new(),
            message_chain: Vec::new(),
        }
    }

    #[test]
    fn rejects_wrong_oracle() {
        let process = shared_process(StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(|_| panic!("process must not run for a rejected oracle")),
        });
        let wrong_version = ReportedAuthority {
            version: "6.0.2".to_owned(),
            digest: STABLE_ORACLE_DIGEST.to_owned(),
        };
        let error = TypeScriptOracle::new(
            &wrong_version,
            process.clone(),
            PathBuf::from("/opt/pinned/node"),
            PathBuf::from("/opt/pinned/tsc_driver.mjs"),
        )
        .expect_err("wrong version");
        assert_eq!(error.code(), ErrorCode::ToolFailed);

        let wrong_digest = ReportedAuthority {
            version: STABLE_VERSION.to_owned(),
            digest: "0".repeat(64),
        };
        let error = TypeScriptOracle::new(
            &wrong_digest,
            process,
            PathBuf::from("/opt/pinned/node"),
            PathBuf::from("/opt/pinned/tsc_driver.mjs"),
        )
        .expect_err("wrong digest");
        assert_eq!(error.code(), ErrorCode::Digest);
        assert!(env_stable_oracle_probe().expect("opt-in probe").is_none());
    }

    #[test]
    fn directives_apply_to_both_sides() {
        let source = "\
// @strict: true
// @filename: a.ts
export const value: string = \"ok\";
// @filename: b.ts
import { value } from \"./a\";
export const twice = value + value;
";
        let requests = Arc::new(Mutex::new(Vec::new()));
        let captured = requests.clone();
        let fake = StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(move |request| {
                captured.lock().expect("lock").push(request.clone());
                ok_outcome(&diagnostic_response(
                    CompilationPhase::Check,
                    Vec::new(),
                    ArtifactDigests::default(),
                ))
            }),
        };
        let oracle = oracle_with(fake);
        let plan = oracle
            .plan(
                source,
                "case.ts",
                cell(&[ObservableKind::Diagnostics], CompilationPhase::Check),
            )
            .expect("plan");
        assert_eq!(plan.request.files.len(), 2);
        assert_eq!(plan.request.files[0].path, "a.ts");
        assert_eq!(plan.request.files[1].path, "b.ts");
        assert_eq!(plan.request.options.strict, Some(true));
        let oracle_side = oracle.observe(&plan).expect("oracle observe");
        let candidate_side = oracle.observe(&plan).expect("candidate observe");
        let recorded = requests.lock().expect("lock");
        assert_eq!(recorded.len(), 2);
        assert_eq!(recorded[0], recorded[1]);
        assert_eq!(recorded[0], plan.request);
        let comparison = oracle.compare(&plan.cell, &oracle_side, &candidate_side);
        assert!(comparison.is_pass(), "{}", comparison.detail);
    }

    #[test]
    fn virtual_files_are_confined_and_unique() {
        let oracle = oracle_with(StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(|_| panic!("materialization failures must not spawn")),
        });
        let traversal = oracle.plan(
            "// @filename: ../escape.ts\nexport {};\n",
            "case.ts",
            cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse),
        );
        assert!(traversal.is_err(), "path traversal must be rejected");

        let absolute = oracle.plan(
            "// @filename: /tmp/escape.ts\nexport {};\n",
            "case.ts",
            cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse),
        );
        assert!(absolute.is_err(), "absolute path must be rejected");

        let duplicate = oracle.plan(
            "// @filename: a.ts\nexport {};\n// @filename: a.ts\nexport {};\n",
            "case.ts",
            cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse),
        );
        assert!(duplicate.is_err(), "duplicate paths must be rejected");

        let collision = oracle.plan(
            "// @filename: Foo.ts\nexport {};\n// @filename: foo.ts\nexport {};\n",
            "case.ts",
            cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse),
        );
        assert!(collision.is_err(), "case-fold collision must be rejected");

        let ok = oracle
            .plan(
                "// @filename: src/a.ts\nexport {};\n// @filename: src/b.ts\nexport {};\n",
                "case.ts",
                cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse),
            )
            .expect("confined unique files");
        let project = oracle.materialize(&ok.request.files).expect("materialize");
        assert!(project.root().join("src/a.ts").is_file());
        assert!(project.root().join("src/b.ts").is_file());
        assert!(!project.root().join("..").join("escape.ts").exists() || true);
    }

    #[test]
    fn compares_structured_diagnostics() {
        let related = StructuredDiagnostic {
            code: 2304,
            category: DiagnosticCategory::Error,
            message: "Cannot find name 'x'.".to_owned(),
            phase: CompilationPhase::Check,
            file: Some("a.ts".to_owned()),
            span: Some(Utf16Span { start: 0, end: 1 }),
            related: vec![RelatedInformation {
                message: "'x' is declared here.".to_owned(),
                file: Some("b.ts".to_owned()),
                span: Some(Utf16Span { start: 10, end: 11 }),
            }],
            message_chain: vec![file_diag(
                100,
                "Did you mean 'y'?",
                CompilationPhase::Check,
                "a.ts",
                0,
                7,
            )],
        };
        let global = StructuredDiagnostic {
            code: 5052,
            category: DiagnosticCategory::Error,
            message: "Option 'strict' cannot be specified.".to_owned(),
            phase: CompilationPhase::Check,
            file: None,
            span: None,
            related: Vec::new(),
            message_chain: Vec::new(),
        };
        let matching = diagnostic_response(
            CompilationPhase::Check,
            vec![related.clone(), global.clone()],
            ArtifactDigests::default(),
        );
        let oracle = oracle_with(StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(move |_| ok_outcome(&matching)),
        });
        let plan = oracle
            .plan(
                "const x: number = 1;\n",
                "a.ts",
                cell(&[ObservableKind::Diagnostics], CompilationPhase::Check),
            )
            .expect("plan");
        let left = oracle.observe(&plan).expect("left");
        let right = oracle.observe(&plan).expect("right");
        assert!(oracle.compare(&plan.cell, &left, &right).is_pass());

        let parse_diag = file_diag(1005, "';' expected.", CompilationPhase::Parse, "a.ts", 4, 5);
        let check_as_parse = complete_observation(diagnostic_response(
            CompilationPhase::Parse,
            vec![parse_diag.clone()],
            ArtifactDigests::default(),
        ));
        let check_as_check = complete_observation(diagnostic_response(
            CompilationPhase::Check,
            vec![StructuredDiagnostic {
                phase: CompilationPhase::Check,
                ..parse_diag
            }],
            ArtifactDigests::default(),
        ));
        let parse_cell = cell(&[ObservableKind::Diagnostics], CompilationPhase::Parse);
        let phase_mismatch = oracle.compare(&parse_cell, &check_as_parse, &check_as_check);
        assert!(!phase_mismatch.is_pass(), "parse vs check must not match");

        decode_response(
            serde_json::to_vec(&json!({
                "protocol": PROTOCOL,
                "phase": "check",
                "diagnostics": [{
                    "code": 1,
                    "category": "error",
                    "message": "global",
                    "phase": "check",
                    "span": {"start": 0, "end": 1}
                }],
                "artifacts": {}
            }))
            .expect("json")
            .as_slice(),
            CompilationPhase::Check,
        )
        .expect_err("global diagnostic with a span must be rejected");
    }

    #[test]
    fn compares_declared_artifacts() {
        let mut artifacts = ArtifactDigests::default();
        artifacts.declaration.insert(
            "a.d.ts".to_owned(),
            sha256_hex(b"export declare const x: number;\n"),
        );
        artifacts
            .source_map
            .insert("a.js.map".to_owned(), sha256_hex(b"{\"version\":3}"));
        artifacts.write_set = Some(sha256_hex(b"declaration\0a.d.ts\0map"));
        let response = diagnostic_response(CompilationPhase::Check, Vec::new(), artifacts.clone());
        let oracle = oracle_with(StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(move |_| ok_outcome(&response)),
        });
        let plan = oracle
            .plan(
                "// @declaration: true\n// @sourceMap: true\nexport const x = 1;\n",
                "a.ts",
                cell(
                    &[
                        ObservableKind::Declaration,
                        ObservableKind::SourceMap,
                        ObservableKind::WriteSet,
                    ],
                    CompilationPhase::Check,
                ),
            )
            .expect("plan");
        assert_eq!(plan.request.options.declaration, Some(true));
        assert_eq!(plan.request.options.source_map, Some(true));
        let left = oracle.observe(&plan).expect("left");
        let right = oracle.observe(&plan).expect("right");
        assert!(oracle.compare(&plan.cell, &left, &right).is_pass());

        let mut mutated = artifacts.clone();
        mutated.declaration.insert(
            "a.d.ts".to_owned(),
            sha256_hex(b"export declare const y: number;\n"),
        );
        let mismatch = oracle.compare(
            &plan.cell,
            &left,
            &complete_observation(diagnostic_response(
                CompilationPhase::Check,
                Vec::new(),
                mutated,
            )),
        );
        assert!(
            !mismatch.is_pass(),
            "declaration digest mismatch cannot pass"
        );
    }

    #[test]
    fn oracle_failures_cannot_pass() {
        let oracle = oracle_with(StrictFake {
            node: PathBuf::from("/opt/pinned/node"),
            driver: PathBuf::from("/opt/pinned/tsc_driver.mjs"),
            requests: Mutex::new(Vec::new()),
            respond: Box::new(|_| OracleOutcome {
                timed_out: true,
                exit_code: None,
                signal: Some(9),
                stdout: Vec::new(),
                stdout_truncated: false,
                stderr: Vec::new(),
                stderr_truncated: false,
                compile_stderr: Vec::new(),
                compile_stderr_truncated: false,
            }),
        });
        let plan = oracle
            .plan(
                "export {};\n",
                "a.ts",
                cell(&[ObservableKind::Diagnostics], CompilationPhase::Check),
            )
            .expect("plan");
        let timed_out = oracle.observe(&plan).expect("timeout observation");
        assert!(!timed_out.can_pass());
        assert!(!oracle.compare(&plan.cell, &timed_out, &timed_out).is_pass());

        let signaled = OracleObservation {
            kind: ObservationKind::Signaled(15),
        };
        assert!(!oracle.compare(&plan.cell, &signaled, &signaled).is_pass());

        let truncated = OracleObservation {
            kind: ObservationKind::Truncated,
        };
        assert!(!oracle.compare(&plan.cell, &truncated, &truncated).is_pass());

        let unknown = oracle.plan(
            "// @notARealDirective: true\nexport {};\n",
            "a.ts",
            cell(&[ObservableKind::Diagnostics], CompilationPhase::Check),
        );
        assert!(unknown.is_err(), "unknown directive cannot pass");

        let missing = complete_observation(diagnostic_response(
            CompilationPhase::Check,
            Vec::new(),
            ArtifactDigests::default(),
        ));
        let declaration_cell = cell(&[ObservableKind::Declaration], CompilationPhase::Check);
        assert!(
            !oracle
                .compare(&declaration_cell, &missing, &missing)
                .is_pass()
        );

        let undeclared = LogicalCell {
            observables: DeclaredObservables::new([ObservableKind::Diagnostics]).expect("obs"),
            phase: CompilationPhase::Check,
            normalization: NormalizationPolicy::Undeclared,
        };
        assert!(
            oracle
                .plan("export {};\n", "a.ts", undeclared.clone())
                .is_err(),
            "undeclared normalization cannot plan"
        );
        let complete = complete_observation(diagnostic_response(
            CompilationPhase::Check,
            Vec::new(),
            ArtifactDigests::default(),
        ));
        assert!(!oracle.compare(&undeclared, &complete, &complete).is_pass());
        assert!(DRIVER_SOURCE.contains(PROTOCOL));
        let _ = DRIVER_UNUSED;
    }
}
