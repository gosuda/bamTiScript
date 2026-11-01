//! Strict Test262 frontmatter, harness, phase, and async `$DONE` oracle.
//!
//! Three execution backends run in-process through the public `bamts` facade:
//! the register **interpreter** (`bamts_runtime::run`), the **JIT** backend
//! (`bamts_codegen::compile_jit` + `run_linked_program`), and the **AOT**
//! backend (`bamts_codegen::compile_aot` + `link_aot_in_process` +
//! `run_linked_program`, which executes real compiled native code in-process).
//! Process-spawning backends stay outside.
//! Callers may also supply typed runner outcomes of their own.

use bamts_bytecode::EcmaString;
use bamts_compiler::diagnostic::Diagnostic;
use bamts_compiler::lint::{LintLevel, LintOverride, LintProfile, LintTable};
use bamts_runtime::{CancellationToken, RuntimeErrorKind, ThrowOrigin, run_linked_program};
use serde::Deserialize;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

pub const FRONTMATTER_OPEN: &str = "/*---";
pub const FRONTMATTER_CLOSE: &str = "---*/";
pub const MAX_FRONTMATTER_BYTES: usize = 16_384;
pub const DEFAULT_ASYNC_DEADLINE: Duration = Duration::from_millis(500);

const HARNESS_ASSERT: &str = "assert.js";
const HARNESS_STA: &str = "sta.js";
const HARNESS_DONE: &str = "doneprintHandle.js";
/// What names a file a test may import from its own directory.
const FIXTURE_MARKER: &str = "_FIXTURE";
const STRICT_PREFIX: &str = "\"use strict\";\n";
/// The host's `$262`, for every test that gets a harness. A member exists only
/// where the engine truly does the work, so a test of a missing facility fails.
/// `INTERPRETING.md` makes it a writable, configurable, non-enumerable global,
/// and the methods capture what they use because tests replace builtins.
const HOST_PRELUDE: &str = "(function (global) {\n\
    var apply = Reflect.apply;\n\
    var transfer = ArrayBuffer.prototype.transfer;\n\
    var evaluate = global.eval;\n\
    Object.defineProperty(global, '$262', {\n\
    value: {\n\
    global: global,\n\
    detachArrayBuffer: function (buffer) { apply(transfer, buffer, []); return null; },\n\
    evalScript: function (source) { return evaluate(source); },\n\
    },\n\
    writable: true,\n\
    enumerable: false,\n\
    configurable: true,\n\
    });\n\
    })(globalThis);\n";
/// Ends a module case. The compiler reads the goal from the tree, as `tsc` does,
/// so this is what makes a test with no `import` or `export` of its own a module.
/// It exports no name, so it cannot collide with one the test declares.
const MODULE_MARKER: &str = "\nexport {};\n";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleError {
    MissingDelimiter,
    UnterminatedFrontmatter,
    OversizeFrontmatter {
        bytes: usize,
    },
    Yaml(String),
    UnknownFlag(String),
    ConflictingFlags,
    UnknownNegativePhase(String),
    UnknownNegativeType(String),
    IncludeNotConfined {
        include: String,
    },
    MissingHarness {
        name: String,
    },
    ModeFailure(ModeFailure),
    Done(DoneFailure),
    ExpectationMismatch {
        expected: String,
        actual: String,
        /// What the throw said, when it said anything.
        message: String,
    },
    /// The runner could not observe the script at all. Always blocking.
    BlockedRun {
        detail: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModeFailure {
    pub mode: ExecutionMode,
    pub detail: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoneFailure {
    Error,
    Duplicate,
    Missing,
    Late,
    EarlyExit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExecutionMode {
    Interpreter,
    Jit,
    Aot,
}

impl ExecutionMode {
    pub const ALL: [Self; 3] = [Self::Interpreter, Self::Jit, Self::Aot];

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Interpreter => "interpreter",
            Self::Jit => "jit",
            Self::Aot => "aot",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flag {
    OnlyStrict,
    NoStrict,
    Module,
    Raw,
    Async,
    Generated,
    CanBlockIsFalse,
    CanBlockIsTrue,
    NonDeterministic,
}

impl Flag {
    pub fn parse(name: &str) -> Result<Self, OracleError> {
        match name {
            "onlyStrict" => Ok(Self::OnlyStrict),
            "noStrict" => Ok(Self::NoStrict),
            "module" => Ok(Self::Module),
            "raw" => Ok(Self::Raw),
            "async" => Ok(Self::Async),
            "generated" => Ok(Self::Generated),
            "CanBlockIsFalse" => Ok(Self::CanBlockIsFalse),
            "CanBlockIsTrue" => Ok(Self::CanBlockIsTrue),
            "non-deterministic" => Ok(Self::NonDeterministic),
            other => Err(OracleError::UnknownFlag(other.to_owned())),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NegativePhase {
    Parse,
    Resolution,
    Runtime,
}

impl NegativePhase {
    pub fn parse(name: &str) -> Result<Self, OracleError> {
        match name {
            "parse" => Ok(Self::Parse),
            "resolution" => Ok(Self::Resolution),
            "runtime" => Ok(Self::Runtime),
            other => Err(OracleError::UnknownNegativePhase(other.to_owned())),
        }
    }

    pub const fn is_early(self) -> bool {
        matches!(self, Self::Parse | Self::Resolution)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NegativeType {
    SyntaxError,
    TypeError,
    ReferenceError,
    RangeError,
    UriError,
    EvalError,
    Test262Error,
}

impl NegativeType {
    pub fn parse(name: &str) -> Result<Self, OracleError> {
        match name {
            "SyntaxError" => Ok(Self::SyntaxError),
            "TypeError" => Ok(Self::TypeError),
            "ReferenceError" => Ok(Self::ReferenceError),
            "RangeError" => Ok(Self::RangeError),
            "URIError" => Ok(Self::UriError),
            "EvalError" => Ok(Self::EvalError),
            "Test262Error" => Ok(Self::Test262Error),
            other => Err(OracleError::UnknownNegativeType(other.to_owned())),
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SyntaxError => "SyntaxError",
            Self::TypeError => "TypeError",
            Self::ReferenceError => "ReferenceError",
            Self::RangeError => "RangeError",
            Self::UriError => "URIError",
            Self::EvalError => "EvalError",
            Self::Test262Error => "Test262Error",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Negative {
    pub phase: NegativePhase,
    pub error_type: NegativeType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frontmatter {
    pub description: Option<String>,
    pub info: Option<String>,
    pub esid: Option<String>,
    pub es5id: Option<String>,
    pub es6id: Option<String>,
    pub features: Vec<String>,
    pub flags: Vec<Flag>,
    pub includes: Vec<String>,
    pub locale: Vec<String>,
    pub author: Option<String>,
    pub negative: Option<Negative>,
}

impl Frontmatter {
    pub fn has(&self, flag: Flag) -> bool {
        self.flags.contains(&flag)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtractedFrontmatter<'a> {
    pub yaml: &'a str,
    pub body: &'a str,
    pub close_end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedTest {
    pub source_bytes: Vec<u8>,
    pub yaml: String,
    pub frontmatter: Frontmatter,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceKind {
    ScriptNonStrict,
    ScriptStrict,
    Module,
    Raw,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionVariant {
    pub kind: SourceKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HarnessPlan {
    None,
    Canonical {
        files: Vec<ConfinedInclude>,
        async_done: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfinedInclude {
    pub requested: String,
    pub confined: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionPlan {
    pub variants: Vec<ExecutionVariant>,
    pub harness: HarnessPlan,
    pub negative: Option<Negative>,
    pub async_done: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposedScript {
    pub bytes: Vec<u8>,
    pub test_offset: usize,
    pub kind: SourceKind,
    pub untouched: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HarnessSource {
    pub name: String,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunRequest {
    pub mode: ExecutionMode,
    pub variant: ExecutionVariant,
    pub script: ComposedScript,
    pub negative: Option<Negative>,
    pub async_done: bool,
    pub deadline: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThrownError {
    pub phase: NegativePhase,
    pub error_type: NegativeType,
    /// What the throw said. Never part of a verdict.
    pub message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoneEventKind {
    Success,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DoneEvent {
    pub kind: DoneEventKind,
    pub at: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsyncTrace {
    pub events: Vec<DoneEvent>,
    /// The stringified `$DONE` argument of the first Error event, when one
    /// was observed. [`judge_run`] matches its leading constructor name
    /// against a negative expectation's `type`, mirroring the completed-run
    /// comparison.
    pub failure_value: Option<String>,
    pub exited_at: Option<Duration>,
    pub deadline: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunOutcome {
    Completed {
        thrown: Option<ThrownError>,
    },
    Async(AsyncTrace),
    /// No verdict-shaped observation was produced. This blocks the
    /// obligation; it can never judge as a pass.
    Blocked {
        detail: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AllModesReport {
    pub modes: Vec<ExecutionMode>,
}

pub trait Test262Runner {
    fn run(&self, request: &RunRequest) -> RunOutcome;
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FrontmatterYaml {
    #[serde(default)]
    description: Option<String>,
    #[serde(default)]
    info: Option<String>,
    #[serde(default)]
    esid: Option<String>,
    #[serde(default)]
    es5id: Option<String>,
    #[serde(default)]
    es6id: Option<String>,
    #[serde(default)]
    features: Vec<String>,
    #[serde(default)]
    flags: Vec<String>,
    #[serde(default)]
    includes: Vec<String>,
    #[serde(default)]
    locale: Vec<String>,
    #[serde(default)]
    author: Option<String>,
    #[serde(default)]
    negative: Option<NegativeYaml>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NegativeYaml {
    phase: String,
    #[serde(rename = "type")]
    error_type: String,
}

fn yaml_options() -> serde_saphyr::Options {
    serde_saphyr::options! {
        duplicate_keys: serde_saphyr::DuplicateKeyPolicy::Error,
        merge_keys: serde_saphyr::MergeKeyPolicy::Error,
        budget: serde_saphyr::budget! {
            max_reader_input_bytes: Some(MAX_FRONTMATTER_BYTES),
            max_events: 8_192,
            max_aliases: 0,
            max_anchors: 0,
            max_depth: 16,
            max_inclusion_depth: 0,
            max_documents: 1,
            max_nodes: 1_024,
            max_total_scalar_bytes: MAX_FRONTMATTER_BYTES,
            max_merge_keys: 0,
        },
    }
}

pub fn extract_frontmatter(source: &str) -> Result<ExtractedFrontmatter<'_>, OracleError> {
    let open = source
        .find(FRONTMATTER_OPEN)
        .ok_or(OracleError::MissingDelimiter)?;
    let yaml_start = open + FRONTMATTER_OPEN.len();
    let relative_close = source[yaml_start..]
        .find(FRONTMATTER_CLOSE)
        .ok_or(OracleError::UnterminatedFrontmatter)?;
    let yaml_end = yaml_start + relative_close;
    let close_end = yaml_end + FRONTMATTER_CLOSE.len();
    let yaml = source[yaml_start..yaml_end].trim();
    if yaml.len() > MAX_FRONTMATTER_BYTES {
        return Err(OracleError::OversizeFrontmatter { bytes: yaml.len() });
    }
    Ok(ExtractedFrontmatter {
        yaml,
        body: &source[close_end..],
        close_end,
    })
}

pub fn parse_frontmatter_yaml(yaml: &str) -> Result<Frontmatter, OracleError> {
    if yaml.len() > MAX_FRONTMATTER_BYTES {
        return Err(OracleError::OversizeFrontmatter { bytes: yaml.len() });
    }
    let raw: FrontmatterYaml = serde_saphyr::from_str_with_options(yaml, yaml_options())
        .map_err(|error| OracleError::Yaml(error.to_string()))?;
    let mut flags = Vec::with_capacity(raw.flags.len());
    for flag in &raw.flags {
        flags.push(Flag::parse(flag)?);
    }
    let negative = match raw.negative {
        Some(value) => Some(Negative {
            phase: NegativePhase::parse(&value.phase)?,
            error_type: NegativeType::parse(&value.error_type)?,
        }),
        None => None,
    };
    Ok(Frontmatter {
        description: raw.description,
        info: raw.info,
        esid: raw.esid,
        es5id: raw.es5id,
        es6id: raw.es6id,
        features: raw.features,
        flags,
        includes: raw.includes,
        locale: raw.locale,
        author: raw.author,
        negative,
    })
}

pub fn parse_test(source: &str) -> Result<ParsedTest, OracleError> {
    let extracted = extract_frontmatter(source)?;
    let frontmatter = parse_frontmatter_yaml(extracted.yaml)?;
    Ok(ParsedTest {
        source_bytes: source.as_bytes().to_vec(),
        yaml: extracted.yaml.to_owned(),
        frontmatter,
    })
}

pub fn confine_include(harness_root: &Path, include: &str) -> Result<ConfinedInclude, OracleError> {
    if include.is_empty()
        || include.contains("..")
        || include.contains('\\')
        || include.contains('\0')
    {
        return Err(OracleError::IncludeNotConfined {
            include: include.to_owned(),
        });
    }
    let relative = Path::new(include);
    if relative.is_absolute() {
        return Err(OracleError::IncludeNotConfined {
            include: include.to_owned(),
        });
    }
    for component in relative.components() {
        match component {
            Component::Normal(_) | Component::CurDir => {}
            Component::Prefix(_) | Component::RootDir | Component::ParentDir => {
                return Err(OracleError::IncludeNotConfined {
                    include: include.to_owned(),
                });
            }
        }
    }
    Ok(ConfinedInclude {
        requested: include.to_owned(),
        confined: harness_root.join(relative),
    })
}

fn flags_conflict(flags: &[Flag]) -> bool {
    flags.contains(&Flag::OnlyStrict) && flags.contains(&Flag::NoStrict)
}

pub fn plan_execution(
    frontmatter: &Frontmatter,
    harness_root: &Path,
) -> Result<ExecutionPlan, OracleError> {
    if flags_conflict(&frontmatter.flags) {
        return Err(OracleError::ConflictingFlags);
    }
    let raw = frontmatter.has(Flag::Raw);
    let module = frontmatter.has(Flag::Module);
    let only_strict = frontmatter.has(Flag::OnlyStrict);
    let no_strict = frontmatter.has(Flag::NoStrict);
    let async_done = frontmatter.has(Flag::Async);
    if raw && (module || only_strict) {
        return Err(OracleError::ConflictingFlags);
    }

    let variants = if raw {
        vec![ExecutionVariant {
            kind: SourceKind::Raw,
        }]
    } else if module {
        vec![ExecutionVariant {
            kind: SourceKind::Module,
        }]
    } else if only_strict {
        vec![ExecutionVariant {
            kind: SourceKind::ScriptStrict,
        }]
    } else if no_strict {
        vec![ExecutionVariant {
            kind: SourceKind::ScriptNonStrict,
        }]
    } else {
        vec![
            ExecutionVariant {
                kind: SourceKind::ScriptNonStrict,
            },
            ExecutionVariant {
                kind: SourceKind::ScriptStrict,
            },
        ]
    };

    let harness = if raw {
        HarnessPlan::None
    } else {
        let mut files = Vec::new();
        files.push(confine_include(harness_root, HARNESS_ASSERT)?);
        files.push(confine_include(harness_root, HARNESS_STA)?);
        if async_done {
            files.push(confine_include(harness_root, HARNESS_DONE)?);
        }
        for include in &frontmatter.includes {
            if include == HARNESS_ASSERT || include == HARNESS_STA || include == HARNESS_DONE {
                continue;
            }
            files.push(confine_include(harness_root, include)?);
        }
        HarnessPlan::Canonical { files, async_done }
    };

    Ok(ExecutionPlan {
        variants,
        harness,
        negative: frontmatter.negative.clone(),
        async_done,
    })
}

pub fn compose_script(
    parsed: &ParsedTest,
    plan: &ExecutionPlan,
    variant: &ExecutionVariant,
    harness_sources: &[HarnessSource],
) -> Result<ComposedScript, OracleError> {
    if variant.kind == SourceKind::Raw {
        return Ok(ComposedScript {
            bytes: parsed.source_bytes.clone(),
            test_offset: 0,
            kind: variant.kind,
            untouched: true,
        });
    }

    // `INTERPRETING.md`: the directive is the initial character sequence of the
    // file and precedes every other text modification, so it leads the harness.
    let mut bytes = Vec::new();
    if variant.kind == SourceKind::ScriptStrict {
        bytes.extend_from_slice(STRICT_PREFIX.as_bytes());
    }
    let early = plan
        .negative
        .as_ref()
        .is_some_and(|negative| negative.phase.is_early());
    if !early && let HarnessPlan::Canonical { files, .. } = &plan.harness {
        bytes.extend_from_slice(HOST_PRELUDE.as_bytes());
        for file in files {
            let source = harness_sources
                .iter()
                .find(|source| source.name == file.requested)
                .map(|source| source.bytes.as_slice())
                .ok_or_else(|| OracleError::MissingHarness {
                    name: file.requested.clone(),
                })?;
            bytes.extend_from_slice(source);
            if !source.ends_with(b"\n") {
                bytes.push(b'\n');
            }
        }
    }
    let test_offset = bytes.len();
    bytes.extend_from_slice(&parsed.source_bytes);
    if variant.kind == SourceKind::Module {
        bytes.extend_from_slice(MODULE_MARKER.as_bytes());
    }
    let untouched = bytes.len() == parsed.source_bytes.len();
    Ok(ComposedScript {
        bytes,
        test_offset,
        kind: variant.kind,
        untouched,
    })
}

pub fn judge_done(trace: &AsyncTrace) -> Result<(), DoneFailure> {
    if let Some(exited_at) = trace.exited_at
        && trace.events.is_empty()
        && exited_at <= trace.deadline
    {
        return Err(DoneFailure::EarlyExit);
    }
    match trace.events.as_slice() {
        [] => Err(DoneFailure::Missing),
        [first, rest @ ..] => {
            if first.at > trace.deadline {
                return Err(DoneFailure::Late);
            }
            if !rest.is_empty() {
                return Err(DoneFailure::Duplicate);
            }
            match first.kind {
                DoneEventKind::Error => Err(DoneFailure::Error),
                DoneEventKind::Success => Ok(()),
            }
        }
    }
}

/// What a failed run reports. A mismatch reads as its cause, so runs that failed
/// the same way group together in a sweep report.
fn failure_detail(error: &OracleError) -> String {
    match error {
        OracleError::ExpectationMismatch {
            expected,
            actual,
            message,
        } if message.is_empty() => format!("expected {expected}, got {actual}"),
        OracleError::ExpectationMismatch {
            expected,
            actual,
            message,
        } => format!("expected {expected}, got {actual}: {message}"),
        other => format!("{other:?}"),
    }
}

/// The first diagnostic of a rejected parse, which is what the parser objected to.
fn parse_message(diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .first()
        .map(|diagnostic| format!("{} {}", diagnostic.code().as_str(), diagnostic.message()))
        .unwrap_or_default()
}

pub fn judge_run(request: &RunRequest, outcome: &RunOutcome) -> Result<(), OracleError> {
    match outcome {
        RunOutcome::Async(trace) => {
            if !request.async_done {
                return Err(OracleError::ExpectationMismatch {
                    expected: "non-async".to_owned(),
                    actual: "async".to_owned(),
                    message: String::new(),
                });
            }
            match judge_done(trace) {
                Ok(()) => match &request.negative {
                    None => Ok(()),
                    Some(expected) => Err(OracleError::ExpectationMismatch {
                        expected: format!("{:?}/{}", expected.phase, expected.error_type.as_str()),
                        actual: "async completion".to_owned(),
                        message: String::new(),
                    }),
                },
                Err(DoneFailure::Error) => match &request.negative {
                    None => Err(OracleError::Done(DoneFailure::Error)),
                    Some(expected) => {
                        // The failure surfaced through the async completion
                        // callback after the body ran, so it is a runtime
                        // throw by construction. Per the Test262
                        // INTERPRETING rule the negative `type` must match
                        // the constructor named by the stringified argument
                        // exactly.
                        let actual_type = async_failure_type(trace);
                        if expected.phase == NegativePhase::Runtime
                            && actual_type == Some(expected.error_type)
                        {
                            Ok(())
                        } else {
                            Err(OracleError::ExpectationMismatch {
                                expected: format!(
                                    "{:?}/{}",
                                    expected.phase,
                                    expected.error_type.as_str()
                                ),
                                actual: match actual_type {
                                    Some(actual_type) => {
                                        format!("Runtime/{}", actual_type.as_str())
                                    }
                                    None => format!(
                                        "Runtime/{}",
                                        trace.failure_value.as_deref().unwrap_or_default()
                                    ),
                                },
                                message: trace.failure_value.clone().unwrap_or_default(),
                            })
                        }
                    }
                },
                Err(other) => Err(OracleError::Done(other)),
            }
        }
        RunOutcome::Completed { thrown } => match (&request.negative, thrown) {
            (None, None) => {
                if request.async_done {
                    Err(OracleError::Done(DoneFailure::Missing))
                } else {
                    Ok(())
                }
            }
            (Some(expected), Some(actual)) => {
                if expected.phase == actual.phase && expected.error_type == actual.error_type {
                    Ok(())
                } else {
                    Err(OracleError::ExpectationMismatch {
                        expected: format!("{:?}/{}", expected.phase, expected.error_type.as_str()),
                        actual: format!("{:?}/{}", actual.phase, actual.error_type.as_str()),
                        message: actual.message.clone(),
                    })
                }
            }
            (Some(expected), None) => Err(OracleError::ExpectationMismatch {
                expected: format!("{:?}/{}", expected.phase, expected.error_type.as_str()),
                actual: "completed".to_owned(),
                message: String::new(),
            }),
            (None, Some(actual)) => Err(OracleError::ExpectationMismatch {
                expected: "success".to_owned(),
                actual: format!("{:?}/{}", actual.phase, actual.error_type.as_str()),
                message: actual.message.clone(),
            }),
        },
        RunOutcome::Blocked { detail } => Err(OracleError::BlockedRun {
            detail: detail.clone(),
        }),
    }
}

/// Resolves the negative type named by the first async-failure value.
///
/// The harnesses stringify a `$DONE` argument as `<Constructor>: <message>`;
/// per the Test262 INTERPRETING rule the negative `type` names the throw's
/// constructor exactly. A value with no leading known constructor names no
/// negative type and can never satisfy an expectation.
#[must_use]
fn async_failure_type(trace: &AsyncTrace) -> Option<NegativeType> {
    let value = trace.failure_value.as_deref()?;
    NegativeType::parse(value.split(':').next()?.trim()).ok()
}

pub fn evaluate_in_all_modes<R: Test262Runner>(
    runner: &R,
    parsed: &ParsedTest,
    plan: &ExecutionPlan,
    harness_sources: &[HarnessSource],
    deadline: Duration,
) -> Result<AllModesReport, OracleError> {
    for mode in ExecutionMode::ALL {
        for variant in &plan.variants {
            let script = compose_script(parsed, plan, variant, harness_sources)?;
            let request = RunRequest {
                mode,
                variant: variant.clone(),
                script,
                negative: plan.negative.clone(),
                async_done: plan.async_done,
                deadline,
            };
            let outcome = runner.run(&request);
            if let Err(error) = judge_run(&request, &outcome) {
                return Err(OracleError::ModeFailure(ModeFailure {
                    mode,
                    detail: failure_detail(&error),
                }));
            }
        }
    }
    Ok(AllModesReport {
        modes: ExecutionMode::ALL.to_vec(),
    })
}

/// Returns the production runner for `mode`.
/// All three execution modes run in-process: the interpreter through
/// `bamts_runtime::run`, JIT through `compile_jit` + `run_linked_program`,
/// and AOT through `compile_aot` + `link_aot_in_process` +
/// `run_linked_program`. The runner dispatches internally on `request.mode`,
/// so one runner serves every mode.
pub fn backend_runner(
    _mode: ExecutionMode,
    scratch: impl Into<PathBuf>,
) -> Result<InterpreterRunner, &'static str> {
    Ok(InterpreterRunner::new(scratch))
}

/// Evaluates one test262 obligation in a single mode (the mode named by the
/// obligation key), running every declared variant and judging each against
/// the frontmatter expectation. Returns `Ok(())` when every variant passes,
/// or the first `OracleError` failure.
pub fn evaluate_in_mode<R: Test262Runner>(
    runner: &R,
    mode: ExecutionMode,
    parsed: &ParsedTest,
    plan: &ExecutionPlan,
    harness_sources: &[HarnessSource],
    deadline: Duration,
) -> Result<AllModesReport, OracleError> {
    for variant in &plan.variants {
        let script = compose_script(parsed, plan, variant, harness_sources)?;
        let request = RunRequest {
            mode,
            variant: variant.clone(),
            script,
            negative: plan.negative.clone(),
            async_done: plan.async_done,
            deadline,
        };
        let outcome = runner.run(&request);
        if let Err(error) = judge_run(&request, &outcome) {
            return Err(OracleError::ModeFailure(ModeFailure {
                mode,
                detail: failure_detail(&error),
            }));
        }
    }
    Ok(AllModesReport { modes: vec![mode] })
}

/// The production Test262 runner: in-process execution for all three modes.
///
/// One [`RunRequest`] becomes one engine run. The composed script is
/// materialized verbatim under `scratch`, compiled through the public `bamts`
/// facade, and executed by the backend selected by `request.mode`:
///
/// - **Interpreter** — `bamts_runtime::run` (the register interpreter).
/// - **JIT** — `bamts_codegen::compile_jit` finalizes native entries, then
///   `bamts_runtime::run_linked_program` executes them through the shared
///   `NativeOps` dispatch.
/// - **AOT** — `bamts_codegen::compile_aot` emits a relocatable object,
///   `link_aot_in_process` maps it into W^X memory and resolves helper
///   relocations against live `bamts_*` exports, then
///   `run_linked_program` executes the real compiled native entries.
///
/// Fuel is derived from the request deadline for all modes.
///
/// Classification is exactly what this boundary can observe:
///
/// - compile diagnostics in the lexical (`BAMTS-L`) or parser (`BAMTS-P`)
///   code families are a parse-phase `SyntaxError`;
/// - a runtime [`ThrowOrigin`] that names a native error class reports that
///   class;
/// - a guest-thrown value (`ThrowOrigin::Bytecode`) has no observable
///   constructor through the public runtime boundary, so the outcome is
///   [`RunOutcome::Blocked`] rather than a guessed type. The block can never
///   judge as a pass;
/// - exhausted fuel or a failed engine pipeline is likewise
///   [`RunOutcome::Blocked`]: no observation was made, so none is reported.
#[derive(Debug)]
pub struct InterpreterRunner {
    scratch: PathBuf,
    composed: AtomicU64,
    origin: Option<PathBuf>,
}

/// Removes a materialized case on every exit path, including early `?`-less
/// classification returns and panics.
struct MaterializedCase(PathBuf);

impl Drop for MaterializedCase {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Copies the `_FIXTURE` files beside a test, which it imports by relative path.
fn copy_fixtures(from: &Path, to: &Path) -> std::io::Result<()> {
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let name = entry.file_name();
        if name.to_string_lossy().contains(FIXTURE_MARKER) && entry.file_type()?.is_file() {
            fs::copy(entry.path(), to.join(name))?;
        }
    }
    Ok(())
}

impl InterpreterRunner {
    /// Creates a runner that materializes composed scripts under `scratch`.
    ///
    /// The directory is created on demand; the caller owns its lifetime.
    #[must_use]
    pub fn new(scratch: impl Into<PathBuf>) -> Self {
        Self {
            scratch: scratch.into(),
            composed: AtomicU64::new(0),
            origin: None,
        }
    }

    /// Materializes each composed script as `test_file` would be found: under
    /// its name, beside copies of its fixtures. Relative imports then resolve,
    /// including a module test that imports itself.
    #[must_use]
    pub fn for_test_file(mut self, test_file: impl Into<PathBuf>) -> Self {
        self.origin = Some(test_file.into());
        self
    }

    fn materialize(&self, request: &RunRequest, directory: &Path) -> std::io::Result<PathBuf> {
        fs::create_dir_all(directory)?;
        let origin = self.origin.as_deref();
        if let Some(parent) = origin.and_then(Path::parent)
            && request
                .script
                .bytes
                .windows(FIXTURE_MARKER.len())
                .any(|window| window == FIXTURE_MARKER.as_bytes())
        {
            copy_fixtures(parent, directory)?;
        }
        let name = origin
            .and_then(Path::file_name)
            .map_or_else(|| "composed.js".into(), std::ffi::OsStr::to_os_string);
        let script = directory.join(name);
        fs::write(&script, &request.script.bytes)?;
        Ok(script)
    }
}

impl Test262Runner for InterpreterRunner {
    fn run(&self, request: &RunRequest) -> RunOutcome {
        if let Err(error) = fs::create_dir_all(&self.scratch) {
            return RunOutcome::Blocked {
                detail: format!(
                    "could not create scratch directory `{}`: {error}",
                    self.scratch.display()
                ),
            };
        }
        let unique = self.composed.fetch_add(1, Ordering::Relaxed);
        let case = MaterializedCase(
            self.scratch
                .join(format!("case-{}-{unique}", std::process::id())),
        );
        let script = match self.materialize(request, &case.0) {
            Ok(script) => script,
            Err(error) => {
                return RunOutcome::Blocked {
                    detail: format!(
                        "could not materialize composed script in `{}`: {error}",
                        case.0.display()
                    ),
                };
            }
        };

        let lints = conformance_lints();
        let cancel = CancellationToken::new();
        let compiled = if request.script.kind == SourceKind::Module {
            bamts::compile_source_file_with_lints(&script, &lints, &cancel)
        } else {
            bamts::compile_script_file(&script, &lints, &cancel)
        };
        let executable = match compiled {
            Ok(executable) => executable,
            Err(bamts::Error::Diagnostics { diagnostics }) => {
                return parse_phase_outcome(&diagnostics);
            }
            Err(error) => {
                return RunOutcome::Blocked {
                    detail: format!("compile pipeline failed: {error}"),
                };
            }
        };

        let limits = interpreter_fuel(request.deadline);
        let started = Instant::now();
        let mut host = bamts_node::NodeHost::new();
        // Dynamic `Function(...)` synthesis needs a compile provider; the
        // facade's ScriptCompiler is the same one `bamts::run_program` uses.
        host.set_script_compiler(Box::new(bamts::ScriptCompiler));
        let result: Result<(), bamts_runtime::RuntimeError> = match request.mode {
            ExecutionMode::Interpreter => {
                bamts_runtime::run(executable.wire(), &mut host, &limits).map(|_| ())
            }
            ExecutionMode::Jit => {
                let jit_program = match bamts_codegen::compile_jit(executable.wire()) {
                    Ok(program) => program,
                    Err(error) => {
                        return RunOutcome::Blocked {
                            detail: format!("JIT compilation failed: {error}"),
                        };
                    }
                };
                run_linked_program(executable.wire(), &jit_program, &mut host, &limits)
                    .map(|_| ())
                    .map_err(|native_error| match native_error {
                        bamts_runtime::NativeError::Runtime(runtime_error) => runtime_error,
                        other => synthetic_runtime_error(other),
                    })
            }
            ExecutionMode::Aot => {
                // Compile to a relocatable object for the host target.
                let target = match bamts_codegen::host_target() {
                    Ok(t) => t,
                    Err(error) => {
                        return RunOutcome::Blocked {
                            detail: format!("aot: unsupported host target: {error}"),
                        };
                    }
                };
                let aot_object = match bamts_codegen::compile_aot(executable.wire(), target) {
                    Ok(obj) => obj,
                    Err(error) => {
                        return RunOutcome::Blocked {
                            detail: format!("aot: unsupported {error}"),
                        };
                    }
                };
                // Link the object in-process: parse ELF, map W^X memory,
                // resolve helper relocations, produce a real NativeEntryTable.
                let linked =
                    match bamts_codegen::link_aot_in_process(&aot_object, executable.wire()) {
                        Ok(prog) => prog,
                        Err(error) => {
                            return RunOutcome::Blocked {
                                detail: format!("aot: load failed: {error}"),
                            };
                        }
                    };
                run_linked_program(executable.wire(), &linked, &mut host, &limits)
                    .map(|_| ())
                    .map_err(|native_error| match native_error {
                        bamts_runtime::NativeError::Runtime(runtime_error) => runtime_error,
                        other => synthetic_runtime_error(other),
                    })
            }
        };
        let elapsed = started.elapsed();
        match result {
            Ok(_) if request.async_done => RunOutcome::Async(observed_done_trace(
                host.stdout(),
                host.stderr(),
                elapsed,
                request.deadline,
            )),
            Ok(_) => RunOutcome::Completed { thrown: None },
            Err(error) => observed_failure(&error, request.deadline),
        }
    }
}

/// Constructs a `RuntimeError` that wraps a non-runtime `NativeError` so the
/// JIT path can route every failure through the shared `observed_failure`
/// classifier. The error kind is `FuelExhausted` when the native backend
/// reported cancellation, otherwise `InvalidVerifiedProgram` — both are
/// shapes `observed_failure` maps to `RunOutcome::Blocked`.
fn synthetic_runtime_error(error: bamts_runtime::NativeError) -> bamts_runtime::RuntimeError {
    let kind = match &error {
        bamts_runtime::NativeError::Cancelled => RuntimeErrorKind::FuelExhausted { limit: 0 },
        _ => RuntimeErrorKind::InvalidVerifiedProgram {
            module: bamts_bytecode::ModuleId::new(0),
            instruction: bamts_bytecode::Instruction::Halt,
        },
    };
    bamts_runtime::RuntimeError {
        kind,
        function: bamts_bytecode::FunctionId::new(0),
        pc: bamts_bytecode::Pc::new(0),
        source: bamts_runtime::RuntimeSource {
            function_name: None,
            instruction: bamts_bytecode::Instruction::Halt,
        },
    }
}

/// Classifies compile diagnostics into a thrown parse error, or blocks when
/// the diagnostics are not parse-shaped.
///
/// Only the lexical (`BAMTS-L`) and parser (`BAMTS-P`) code families are
/// JavaScript parse errors. Any other diagnostic means the oracle pipeline
/// rejected source that Test262 considers valid, which is an observation
/// failure and never a Test262 verdict.
/// The lints a conformance run compiles under. A lint is project policy, so
/// one must not refuse a program the language allows.
fn conformance_lints() -> LintTable {
    let mut lints = LintTable::new(LintProfile::Default);
    lints
        .apply_cli([LintOverride::new("no-with", LintLevel::Allow, "test262")])
        .expect("the default profile forbids no rule");
    lints
}

fn parse_phase_outcome(diagnostics: &[Diagnostic]) -> RunOutcome {
    let parse_shaped = diagnostics.iter().any(|diagnostic| {
        let code = diagnostic.code().as_str();
        code.starts_with("BAMTS-L") || code.starts_with("BAMTS-P")
    });
    if parse_shaped {
        return RunOutcome::Completed {
            thrown: Some(ThrownError {
                phase: NegativePhase::Parse,
                error_type: NegativeType::SyntaxError,
                message: parse_message(diagnostics),
            }),
        };
    }
    let codes = diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code().as_str())
        .collect::<Vec<_>>()
        .join(", ");
    RunOutcome::Blocked {
        detail: format!(
            "compile produced {} non-parse diagnostic(s): {codes}",
            diagnostics.len()
        ),
    }
}

/// Maps an engine throw origin (and, for guest-thrown values, the resolved
/// constructor name) onto the Test262 negative type it names.
///
/// Engine-originated throws (`TypeError`, `RangeError`, `ReferenceError`,
/// `UriError`) name their constructor in the [`ThrowOrigin`] variant.
/// Guest-thrown values ([`ThrowOrigin::Bytecode`]) carry a resolved
/// `constructor_name` that the runtime boundary extracts by walking the
/// thrown value's prototype chain to a builtin error constructor or a
/// user-defined class name. Per the test262 INTERPRETING.md rule, the
/// negative `type` must match the constructor's name exactly.
#[must_use]
fn classify_thrown(
    origin: ThrowOrigin,
    constructor_name: Option<&EcmaString>,
) -> Option<NegativeType> {
    match origin {
        ThrowOrigin::TypeError { .. } => Some(NegativeType::TypeError),
        ThrowOrigin::RangeError { .. } => Some(NegativeType::RangeError),
        ThrowOrigin::ReferenceError { .. } => Some(NegativeType::ReferenceError),
        ThrowOrigin::UriError { .. } => Some(NegativeType::UriError),
        ThrowOrigin::Bytecode => {
            let name = constructor_name?.to_utf8_lossy();
            NegativeType::parse(&name).ok()
        }
    }
}

/// Classifies an engine failure into a thrown runtime error or a block.
fn observed_failure(error: &bamts_runtime::RuntimeError, deadline: Duration) -> RunOutcome {
    match &error.kind {
        RuntimeErrorKind::UncaughtThrow {
            origin,
            constructor_name,
            message,
            ..
        } => match classify_thrown(*origin, constructor_name.as_ref()) {
            Some(error_type) => RunOutcome::Completed {
                thrown: Some(ThrownError {
                    phase: NegativePhase::Runtime,
                    error_type,
                    message: message
                        .as_ref()
                        .map_or_else(|| format!("{origin:?}"), EcmaString::to_utf8_lossy),
                }),
            },
            None => {
                let site = error
                    .source
                    .function_name
                    .as_ref()
                    .map_or_else(|| "<anonymous>".to_owned(), |name| name.to_utf8_lossy());
                let constructor = constructor_name
                    .as_ref()
                    .map(|name| format!(" (constructor: {})", name.to_utf8_lossy()))
                    .unwrap_or_default();
                RunOutcome::Blocked {
                    detail: format!(
                        "guest threw a value whose constructor does not \
                             map to a Test262 negative type{constructor} (throw site: {site})"
                    ),
                }
            }
        },
        RuntimeErrorKind::FuelExhausted { .. } => RunOutcome::Blocked {
            detail: format!("fuel exhausted within the {deadline:?} deadline"),
        },
        _ => RunOutcome::Blocked {
            detail: format!("runtime failed without a throw: {error}"),
        },
    }
}

/// Converts a wall-clock deadline into deterministic interpreter fuel.
///
/// The interpreter has no preemption, so fuel checked at instruction
/// boundaries is the deadline's deterministic proxy, matching the corpus
/// runner's budget.
#[must_use]
fn interpreter_fuel(deadline: Duration) -> bamts_runtime::Limits {
    const FUEL_PER_MILLISECOND: u64 = 10_000;
    let milliseconds = u64::try_from(deadline.as_millis())
        .unwrap_or(u64::MAX)
        .max(1);
    bamts_runtime::Limits {
        fuel: milliseconds.saturating_mul(FUEL_PER_MILLISECOND),
        ..bamts_runtime::Limits::default()
    }
}

/// Observes completion markers in the captured host output.
///
/// The canonical Test262 `doneprintHandle.js` prints
/// `Test262:AsyncTestComplete` (success) or `Test262:AsyncTestFailure:…`
/// (error) via the global `print` function.  The internal test harness
/// additionally emits `$DONE()` / `$DONE(…)` through `console.log`.
/// Both marker families are recognised so production and fixture flows
/// share the same judge path.
/// The stringified argument of the first failure marker is captured on the
/// trace so `judge_run` can match it against a negative expectation.
#[must_use]
fn observed_done_trace(
    stdout: &[u8],
    stderr: &[u8],
    elapsed: Duration,
    deadline: Duration,
) -> AsyncTrace {
    let mut events = Vec::new();
    let mut failure_value = None;
    for stream in [stdout, stderr] {
        let mut cursor = 0;
        loop {
            let (at, kind, value) =
                if let Some(found) = find_marker(&stream[cursor..], COMPLETE_MARKER) {
                    (cursor + found, DoneEventKind::Success, None)
                } else if let Some(found) = find_marker(&stream[cursor..], FAILURE_MARKER) {
                    let at = cursor + found;
                    let rest = failure_marker_value(&stream[at + FAILURE_MARKER.len()..]);
                    (at, DoneEventKind::Error, Some(rest))
                } else if let Some(found) = find_marker(&stream[cursor..], MARKER_OPEN) {
                    let at = cursor + found;
                    let after = at + MARKER_OPEN.len();
                    if stream.get(after) == Some(&b')') {
                        (at, DoneEventKind::Success, None)
                    } else {
                        let rest = failure_marker_value(&stream[after..]);
                        (at, DoneEventKind::Error, Some(rest))
                    }
                } else {
                    break;
                };
            if kind == DoneEventKind::Error && failure_value.is_none() {
                failure_value = value;
            }
            events.push(DoneEvent { kind, at: elapsed });
            cursor = at + 1;
        }
    }
    AsyncTrace {
        events,
        failure_value,
        exited_at: Some(elapsed),
        deadline,
    }
}

/// The `$DONE(` invocation prefix used by the internal test harness.
const MARKER_OPEN: &[u8] = b"$DONE(";

/// Canonical Test262 async-completion marker (success).
const COMPLETE_MARKER: &[u8] = b"Test262:AsyncTestComplete";

/// Canonical Test262 async-completion marker (failure).
const FAILURE_MARKER: &[u8] = b"Test262:AsyncTestFailure";

fn find_marker(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

/// The stringified `$DONE` argument captured after a failure marker.
///
/// The canonical harness prints `Test262:AsyncTestFailure:` immediately
/// followed by the stringified argument, and the internal harness prints
/// `$DONE(` + argument + `)`; both occupy one line. The optional leading
/// `:`, the trailing `)`, and surrounding whitespace belong to the harness
/// shapes, not the argument, so they are stripped. Type resolution reads
/// only the leading constructor name, so an argument whose message itself
/// contains those characters is still classified correctly.
fn failure_marker_value(rest: &[u8]) -> String {
    let mut end = rest
        .iter()
        .position(|byte| *byte == b'\n')
        .unwrap_or(rest.len());
    let start = usize::from(rest.first() == Some(&b':'));
    if end > start && rest[end - 1] == b')' {
        end -= 1;
    }
    String::from_utf8_lossy(&rest[start..end]).trim().to_owned()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::fs;
    use std::path::Path;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::super::test262_harness::{FileHarnessLoader, load_harness_sources};

    static SCRATCH_COUNTER: AtomicU64 = AtomicU64::new(0);

    /// A unique per-test scratch directory for harness files and materialized
    /// composed scripts.
    fn runner_scratch(tag: &str) -> PathBuf {
        let unique = SCRATCH_COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "bamts-test262-{tag}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create runner scratch dir");
        dir
    }

    fn write_harness(root: &Path, name: &str, contents: &str) {
        fs::write(root.join(name), contents).expect("write harness include");
    }

    /// Minimal clean-room stand-ins for the canonical Test262 harness files:
    /// enough of `assert`, `$ERROR`, `Test262Error`, and `$DONE` for these
    /// fixtures, with none of the upstream bodies.
    const ASSERT_JS: &str = "var assert;\n\
(function () {\n\
  assert = {\n\
    sameValue: function (actual, expected, message) {\n\
      if (actual !== expected) {\n\
        $ERROR(message);\n\
      }\n\
    },\n\
  };\n\
})();\n";

    const STA_JS: &str = "function Test262Error(message) {\n\
  this.message = message;\n\
}\n\
function $ERROR(message) {\n\
  throw new Test262Error(message);\n\
}\n";

    const DONEPRINT_JS: &str = "function $DONE(failure) {\n\
  if (failure) {\n\
    console.log('$DONE(' + String(failure) + ')');\n\
  } else {\n\
    console.log('$DONE()');\n\
  }\n\
}\n";

    /// The production interpreter flow for one variant: compose, request,
    /// run in-process, and judge. Returns the judge verdict.
    fn run_variant(
        runner: &InterpreterRunner,
        parsed: &ParsedTest,
        plan: &ExecutionPlan,
        sources: &[HarnessSource],
        variant: &ExecutionVariant,
    ) -> Result<(), OracleError> {
        run_variant_in(
            ExecutionMode::Interpreter,
            runner,
            parsed,
            plan,
            sources,
            variant,
        )
    }

    fn run_variant_in(
        mode: ExecutionMode,
        runner: &InterpreterRunner,
        parsed: &ParsedTest,
        plan: &ExecutionPlan,
        sources: &[HarnessSource],
        variant: &ExecutionVariant,
    ) -> Result<(), OracleError> {
        // These real-engine fixtures check completion/error classification,
        // not host scheduling latency. Deadline policy is tested below with
        // explicit timestamps; retain a finite budget under parallel CI load.
        const SEMANTIC_FIXTURE_DEADLINE: Duration = Duration::from_secs(10);
        let script = compose_script(parsed, plan, variant, sources)?;
        let request = RunRequest {
            mode,
            variant: variant.clone(),
            script,
            negative: plan.negative.clone(),
            async_done: plan.async_done,
            deadline: SEMANTIC_FIXTURE_DEADLINE,
        };
        let outcome = runner.run(&request);
        judge_run(&request, &outcome)
    }

    fn wrap(yaml: &str, body: &str) -> String {
        format!("{FRONTMATTER_OPEN}\n{yaml}\n{FRONTMATTER_CLOSE}\n{body}")
    }

    /// Runs `body` as a module test named `case.js` beside `value_FIXTURE.js`.
    fn run_module_beside_fixture(name: &str, body: &str) -> (RunOutcome, usize) {
        let root =
            std::env::temp_dir().join(format!("bamts-test262-{}-{name}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let tests = root.join("tests");
        let scratch = root.join("scratch");
        fs::create_dir_all(&tests).expect("tests directory");
        fs::write(tests.join("value_FIXTURE.js"), "export const value = 42;\n").expect("fixture");
        fs::write(tests.join("unrelated.js"), "throw 1;\n").expect("sibling");

        let runner = InterpreterRunner::new(&scratch).for_test_file(tests.join("case.js"));
        let request = RunRequest {
            mode: ExecutionMode::Interpreter,
            variant: ExecutionVariant {
                kind: SourceKind::Module,
            },
            script: ComposedScript {
                bytes: body.as_bytes().to_vec(),
                test_offset: 0,
                kind: SourceKind::Module,
                untouched: true,
            },
            negative: None,
            async_done: false,
            deadline: Duration::from_secs(10),
        };
        let outcome = runner.run(&request);
        let left = fs::read_dir(&scratch).map_or(0, |entries| entries.count());
        fs::remove_dir_all(root).expect("remove scratch");
        (outcome, left)
    }

    #[test]
    fn a_composed_module_finds_the_fixtures_beside_its_test() {
        let (outcome, left) = run_module_beside_fixture(
            "fixture",
            "import { value } from './value_FIXTURE.js';\nif (value !== 42) { throw new Error('wrong'); }\n",
        );
        assert!(
            matches!(outcome, RunOutcome::Completed { thrown: None }),
            "{outcome:?}"
        );
        assert_eq!(left, 0, "a run leaves nothing behind");
    }

    #[test]
    fn a_composed_module_can_import_itself_by_its_test_name() {
        let (outcome, _) = run_module_beside_fixture(
            "self",
            "import * as self from './case.js';\nexport const mine = 1;\nif (self.mine !== 1) { throw new Error('wrong'); }\n",
        );
        assert!(
            matches!(outcome, RunOutcome::Completed { thrown: None }),
            "{outcome:?}"
        );
    }

    fn harness_root() -> PathBuf {
        PathBuf::from("/pinned/harness")
    }

    fn harness_sources() -> Vec<HarnessSource> {
        vec![
            HarnessSource {
                name: HARNESS_ASSERT.to_owned(),
                bytes: b"/*assert*/\n".to_vec(),
            },
            HarnessSource {
                name: HARNESS_STA.to_owned(),
                bytes: b"/*sta*/\n".to_vec(),
            },
            HarnessSource {
                name: HARNESS_DONE.to_owned(),
                bytes: b"/*done*/\n".to_vec(),
            },
            HarnessSource {
                name: "propertyHelper.js".to_owned(),
                bytes: b"/*helper*/\n".to_vec(),
            },
        ]
    }

    struct PassRunner;

    impl Test262Runner for PassRunner {
        fn run(&self, request: &RunRequest) -> RunOutcome {
            if request.async_done {
                RunOutcome::Async(AsyncTrace {
                    events: vec![DoneEvent {
                        kind: DoneEventKind::Success,
                        at: Duration::from_millis(1),
                    }],
                    failure_value: None,
                    exited_at: None,
                    deadline: request.deadline,
                })
            } else if let Some(negative) = &request.negative {
                RunOutcome::Completed {
                    thrown: Some(ThrownError {
                        phase: negative.phase,
                        error_type: negative.error_type,
                        message: String::new(),
                    }),
                }
            } else {
                RunOutcome::Completed { thrown: None }
            }
        }
    }

    struct FailJitRunner;

    impl Test262Runner for FailJitRunner {
        fn run(&self, request: &RunRequest) -> RunOutcome {
            if request.mode == ExecutionMode::Jit {
                RunOutcome::Completed {
                    thrown: Some(ThrownError {
                        phase: NegativePhase::Runtime,
                        error_type: NegativeType::TypeError,
                        message: String::new(),
                    }),
                }
            } else {
                PassRunner.run(request)
            }
        }
    }

    #[test]
    fn frontmatter_is_strict_and_bounded() {
        let block = wrap(
            "description: block yaml\nflags: [noStrict]\ninfo: |\n  line one\n  line two",
            "void 0;",
        );
        let parsed = parse_test(&block).expect("block yaml");
        assert_eq!(
            parsed.frontmatter.description.as_deref(),
            Some("block yaml")
        );
        assert_eq!(
            parsed.frontmatter.info.as_deref().map(str::trim),
            Some("line one\nline two")
        );
        assert!(parsed.frontmatter.has(Flag::NoStrict));

        let flow = wrap(
            "{description: flow, flags: [onlyStrict, async], includes: [propertyHelper.js]}",
            "$DONE();",
        );
        let parsed = parse_test(&flow).expect("flow yaml");
        assert_eq!(parsed.frontmatter.description.as_deref(), Some("flow"));
        assert!(parsed.frontmatter.has(Flag::OnlyStrict));
        assert!(parsed.frontmatter.has(Flag::Async));
        assert_eq!(parsed.frontmatter.includes, ["propertyHelper.js"]);

        let quoted = wrap("description: \"quoted scalar\"\nauthor: 'nobody'", "");
        let parsed = parse_test(&quoted).expect("quoted scalars");
        assert_eq!(
            parsed.frontmatter.description.as_deref(),
            Some("quoted scalar")
        );
        assert_eq!(parsed.frontmatter.author.as_deref(), Some("nobody"));

        let duplicate = wrap("description: one\ndescription: two", "");
        match parse_test(&duplicate) {
            Err(OracleError::Yaml(_)) => {}
            other => panic!("duplicate keys must fail, got {other:?}"),
        }

        let unknown = wrap("description: x\nmystery: true", "");
        match parse_test(&unknown) {
            Err(OracleError::Yaml(_)) => {}
            other => panic!("unknown fields must fail, got {other:?}"),
        }

        assert!(matches!(
            extract_frontmatter("no delimiter here"),
            Err(OracleError::MissingDelimiter)
        ));
        assert!(matches!(
            extract_frontmatter("/*---\nbad: true\n"),
            Err(OracleError::UnterminatedFrontmatter)
        ));

        let huge = "x".repeat(MAX_FRONTMATTER_BYTES + 1);
        match extract_frontmatter(&format!("/*---\n{huge}\n---*/\n")) {
            Err(OracleError::OversizeFrontmatter { bytes }) => {
                assert!(bytes > MAX_FRONTMATTER_BYTES);
            }
            other => panic!("oversize must fail, got {other:?}"),
        }
    }

    #[test]
    fn includes_are_confined_and_ordered() {
        let source = wrap(
            "description: includes\nincludes: [propertyHelper.js]",
            "void 0;",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness_root()).unwrap();
        let HarnessPlan::Canonical { files, async_done } = plan.harness else {
            panic!("canonical harness required");
        };
        assert!(!async_done);
        let names: Vec<&str> = files.iter().map(|file| file.requested.as_str()).collect();
        assert_eq!(names, ["assert.js", "sta.js", "propertyHelper.js"]);
        for file in &files {
            assert!(file.confined.starts_with(harness_root()));
        }

        let traversal = wrap("description: traversal\nincludes: [../secret.js]", "");
        let parsed = parse_test(&traversal).unwrap();
        assert!(matches!(
            plan_execution(&parsed.frontmatter, &harness_root()),
            Err(OracleError::IncludeNotConfined { .. })
        ));

        let absolute = wrap("description: abs\nincludes: [/etc/passwd]", "");
        let parsed = parse_test(&absolute).unwrap();
        assert!(matches!(
            plan_execution(&parsed.frontmatter, &harness_root()),
            Err(OracleError::IncludeNotConfined { .. })
        ));

        assert!(matches!(
            confine_include(Path::new("/pinned/harness"), "..\\escape.js"),
            Err(OracleError::IncludeNotConfined { .. })
        ));
    }

    #[test]
    fn early_negative_phase_and_type_are_exact() {
        for (phase, ty, yaml_phase, yaml_type) in [
            (
                NegativePhase::Parse,
                NegativeType::SyntaxError,
                "parse",
                "SyntaxError",
            ),
            (
                NegativePhase::Resolution,
                NegativeType::ReferenceError,
                "resolution",
                "ReferenceError",
            ),
            (
                NegativePhase::Runtime,
                NegativeType::TypeError,
                "runtime",
                "TypeError",
            ),
        ] {
            let flags = if phase == NegativePhase::Resolution {
                "flags: [module]\n"
            } else {
                "flags: [raw]\n"
            };
            let source = wrap(
                &format!(
                    "description: negative\n{flags}negative:\n  phase: {yaml_phase}\n  type: {yaml_type}"
                ),
                "throw 1;",
            );
            let parsed = parse_test(&source).unwrap();
            let negative = parsed.frontmatter.negative.clone().expect("negative");
            assert_eq!(negative.phase, phase);
            assert_eq!(negative.error_type, ty);
            let plan = plan_execution(&parsed.frontmatter, &harness_root()).unwrap();
            let variant = &plan.variants[0];
            let script = compose_script(&parsed, &plan, variant, &harness_sources())
                .expect("compose negative");
            if phase.is_early() {
                // No harness, though a module case keeps what makes it a module.
                assert_eq!(script.untouched, variant.kind == SourceKind::Raw);
                assert!(script.bytes.starts_with(&parsed.source_bytes));
                assert_eq!(script.test_offset, 0);
            }
            let request = RunRequest {
                mode: ExecutionMode::Interpreter,
                variant: variant.clone(),
                script,
                negative: plan.negative.clone(),
                async_done: plan.async_done,
                deadline: DEFAULT_ASYNC_DEADLINE,
            };
            let outcome = PassRunner.run(&request);
            judge_run(&request, &outcome).expect("exact negative match");
        }
    }

    #[test]
    fn runtime_harness_preserves_observables() {
        let source = wrap(
            "description: runtime\nincludes: [propertyHelper.js]",
            "observable();",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness_root()).unwrap();
        let variant = plan
            .variants
            .iter()
            .find(|variant| variant.kind == SourceKind::ScriptNonStrict)
            .expect("non-strict variant");
        let script =
            compose_script(&parsed, &plan, variant, &harness_sources()).expect("compose runtime");
        assert!(!script.untouched);
        let prefix = std::str::from_utf8(&script.bytes[..script.test_offset]).unwrap();
        assert!(prefix.contains("/*assert*/"));
        assert!(prefix.contains("/*sta*/"));
        assert!(prefix.contains("/*helper*/"));
        assert_eq!(
            &script.bytes[script.test_offset..],
            parsed.source_bytes.as_slice()
        );
        assert!(
            std::str::from_utf8(&script.bytes)
                .unwrap()
                .contains("observable();")
        );

        let strict = plan
            .variants
            .iter()
            .find(|variant| variant.kind == SourceKind::ScriptStrict)
            .expect("strict variant");
        let strict_script =
            compose_script(&parsed, &plan, strict, &harness_sources()).expect("compose strict");
        let before_test = &strict_script.bytes[..strict_script.test_offset];
        assert!(before_test.starts_with(STRICT_PREFIX.as_bytes()));
        assert_eq!(
            &strict_script.bytes[strict_script.test_offset..],
            parsed.source_bytes.as_slice()
        );
    }

    #[test]
    fn done_protocol_is_exact() {
        let deadline = Duration::from_millis(10);
        let success = AsyncTrace {
            events: vec![DoneEvent {
                kind: DoneEventKind::Success,
                at: Duration::from_millis(1),
            }],
            failure_value: None,
            exited_at: None,
            deadline,
        };
        assert!(judge_done(&success).is_ok());

        let error = AsyncTrace {
            events: vec![DoneEvent {
                kind: DoneEventKind::Error,
                at: Duration::from_millis(1),
            }],
            failure_value: None,
            exited_at: None,
            deadline,
        };
        assert_eq!(judge_done(&error), Err(DoneFailure::Error));

        let duplicate = AsyncTrace {
            events: vec![
                DoneEvent {
                    kind: DoneEventKind::Success,
                    at: Duration::from_millis(1),
                },
                DoneEvent {
                    kind: DoneEventKind::Success,
                    at: Duration::from_millis(2),
                },
            ],
            failure_value: None,
            exited_at: None,
            deadline,
        };
        assert_eq!(judge_done(&duplicate), Err(DoneFailure::Duplicate));

        let missing = AsyncTrace {
            events: vec![],
            failure_value: None,
            exited_at: None,
            deadline,
        };
        assert_eq!(judge_done(&missing), Err(DoneFailure::Missing));

        let late = AsyncTrace {
            events: vec![DoneEvent {
                kind: DoneEventKind::Success,
                at: Duration::from_millis(11),
            }],
            failure_value: None,
            exited_at: None,
            deadline,
        };
        assert_eq!(judge_done(&late), Err(DoneFailure::Late));

        let early = AsyncTrace {
            events: vec![],
            failure_value: None,
            exited_at: Some(Duration::from_millis(1)),
            deadline,
        };
        assert_eq!(judge_done(&early), Err(DoneFailure::EarlyExit));
    }

    #[test]
    fn production_done_deadline_boundary_remains_exact() {
        assert_eq!(DEFAULT_ASYNC_DEADLINE, Duration::from_millis(500));
        for (kind, at_boundary) in [
            (DoneEventKind::Success, Ok(())),
            (DoneEventKind::Error, Err(DoneFailure::Error)),
        ] {
            let mut trace = AsyncTrace {
                events: vec![DoneEvent {
                    kind,
                    at: DEFAULT_ASYNC_DEADLINE,
                }],
                failure_value: None,
                exited_at: None,
                deadline: DEFAULT_ASYNC_DEADLINE,
            };
            assert_eq!(judge_done(&trace), at_boundary);
            trace.events[0].at += Duration::from_nanos(1);
            assert_eq!(judge_done(&trace), Err(DoneFailure::Late));
        }
    }

    #[test]
    fn flags_select_exact_plan() {
        let root = harness_root();
        let default = parse_test(&wrap("description: default", "")).unwrap();
        let plan = plan_execution(&default.frontmatter, &root).unwrap();
        assert_eq!(
            plan.variants
                .iter()
                .map(|variant| variant.kind)
                .collect::<Vec<_>>(),
            [SourceKind::ScriptNonStrict, SourceKind::ScriptStrict]
        );

        let only = parse_test(&wrap("description: s\nflags: [onlyStrict]", "")).unwrap();
        let plan = plan_execution(&only.frontmatter, &root).unwrap();
        assert_eq!(plan.variants[0].kind, SourceKind::ScriptStrict);

        let no = parse_test(&wrap("description: n\nflags: [noStrict]", "")).unwrap();
        let plan = plan_execution(&no.frontmatter, &root).unwrap();
        assert_eq!(plan.variants[0].kind, SourceKind::ScriptNonStrict);

        let module = parse_test(&wrap("description: m\nflags: [module]", "")).unwrap();
        let plan = plan_execution(&module.frontmatter, &root).unwrap();
        assert_eq!(plan.variants[0].kind, SourceKind::Module);
        assert!(matches!(plan.harness, HarnessPlan::Canonical { .. }));

        let raw = parse_test(&wrap("description: r\nflags: [raw]", "")).unwrap();
        let plan = plan_execution(&raw.frontmatter, &root).unwrap();
        assert_eq!(plan.variants[0].kind, SourceKind::Raw);
        assert_eq!(plan.harness, HarnessPlan::None);

        let async_mod = parse_test(&wrap("description: a\nflags: [async, module]", "")).unwrap();
        let plan = plan_execution(&async_mod.frontmatter, &root).unwrap();
        assert!(plan.async_done);
        let HarnessPlan::Canonical { files, async_done } = plan.harness else {
            panic!("async module uses harness");
        };
        assert!(async_done);
        let names: Vec<&str> = files.iter().map(|file| file.requested.as_str()).collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js"]);

        let raw_strict =
            parse_test(&wrap("description: bad\nflags: [raw, onlyStrict]", "")).unwrap();
        assert!(matches!(
            plan_execution(&raw_strict.frontmatter, &root),
            Err(OracleError::ConflictingFlags)
        ));
    }

    #[test]
    fn requires_all_execution_modes() {
        let source = wrap("description: modes\nflags: [noStrict]", "void 0;");
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness_root()).unwrap();
        let report = evaluate_in_all_modes(
            &PassRunner,
            &parsed,
            &plan,
            &harness_sources(),
            DEFAULT_ASYNC_DEADLINE,
        )
        .expect("all modes pass");
        assert_eq!(
            report.modes,
            [
                ExecutionMode::Interpreter,
                ExecutionMode::Jit,
                ExecutionMode::Aot
            ]
        );

        match evaluate_in_all_modes(
            &FailJitRunner,
            &parsed,
            &plan,
            &harness_sources(),
            DEFAULT_ASYNC_DEADLINE,
        ) {
            Err(OracleError::ModeFailure(failure)) => {
                assert_eq!(failure.mode, ExecutionMode::Jit);
            }
            other => panic!("JIT failure must be recorded, got {other:?}"),
        }
    }

    #[test]
    fn interpreter_runner_passes_positive_same_value_fixture() {
        let harness = runner_scratch("pos-harness");
        let scratch = runner_scratch("pos-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: assert.sameValue passes on identical primitives",
            "assert.sameValue(1, 1, 'one is one');",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();

        // The strict variant opens with the directive, ahead of the harness.
        assert_eq!(plan.variants.len(), 2);
        let strict = compose_script(&parsed, &plan, &plan.variants[1], &sources).unwrap();
        assert_eq!(strict.kind, SourceKind::ScriptStrict);
        assert!(strict.bytes.starts_with(STRICT_PREFIX.as_bytes()));

        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            run_variant(&runner, &parsed, &plan, &sources, variant).unwrap();
        }
    }

    /// Runs every variant of `source` against the small fixture harness.
    fn run_fixture(label: &str, source: &str) -> Result<(), OracleError> {
        run_fixture_in(ExecutionMode::Interpreter, label, source)
    }

    fn run_fixture_in(mode: ExecutionMode, label: &str, source: &str) -> Result<(), OracleError> {
        let harness = runner_scratch(&format!("{label}-harness"));
        let scratch = runner_scratch(&format!("{label}-scratch"));
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        write_harness(&harness, "doneprintHandle.js", DONEPRINT_JS);
        let parsed = parse_test(source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(mode, &scratch).unwrap();
        for variant in &plan.variants {
            run_variant_in(mode, &runner, &parsed, &plan, &sources, variant)?;
        }
        Ok(())
    }

    #[test]
    fn an_object_pattern_collects_what_is_left() {
        let source = wrap(
            "description: object rest in an assignment pattern",
            "var a, rest, holder = {};\n\
             ({ a, ...rest } = { a: 1, b: 2, c: 3 });\n\
             assert.sameValue(a, 1);\n\
             assert.sameValue(rest.a, undefined);\n\
             assert.sameValue(rest.b, 2);\n\
             assert.sameValue(rest.c, 3);\n\
             ({ ...holder.rest } = { d: 4 });\n\
             assert.sameValue(holder.rest.d, 4);",
        );
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            run_fixture_in(mode, &format!("object-rest-{mode:?}"), &source).unwrap();
        }
    }

    #[test]
    fn an_object_pattern_refuses_null_and_undefined() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [(&str, &str); 3] = [
            (
                "",
                "assert.sameValue(throws(TypeError, function () { let {} = undefined; }), true);",
            ),
            (
                "",
                "var a; assert.sameValue(throws(TypeError, function () { ({} = null); }), true);",
            ),
            (
                "",
                "var read = 0; var key = function () { read += 1; return 'k'; }; assert.sameValue(throws(TypeError, function () { var { [key()]: x } = null; }), true); assert.sameValue(read, 0);",
            ),
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, (flags, body)) in CASES.iter().enumerate() {
                let source = wrap(
                    &format!("description: object patterns\n{flags}"),
                    &format!("{THROWS}{body}"),
                );
                let label = format!("object-patterns-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn a_generator_binds_its_parameters_at_the_call() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [(&str, &str); 9] = [
            (
                "",
                "function* g({}) {} assert.sameValue(throws(TypeError, function () { g(undefined); }), true);",
            ),
            (
                "",
                "async function* g({}) {} assert.sameValue(throws(TypeError, function () { g(undefined); }), true);",
            ),
            (
                "",
                "class C { static *m({}) {} } assert.sameValue(throws(TypeError, function () { C.m(undefined); }), true);",
            ),
            (
                "",
                "function* g(a = (function () { throw new Test262Error(); })()) {} assert.sameValue(throws(Test262Error, function () { g(); }), true);",
            ),
            (
                "",
                "var log = 0; function* g(a = log += 1) { log += 10; } var it = g(); assert.sameValue(log, 1); it.next(); assert.sameValue(log, 11);",
            ),
            (
                "",
                "function* g(a = 1) { yield a; } var it = g(); assert.sameValue(it.next(5).value, 1); assert.sameValue(it.next().done, true);",
            ),
            (
                "",
                "function* g(a = 1) { yield a; } var it = g(); assert.sameValue(it.return(7).value, 7); assert.sameValue(it.next().done, true);",
            ),
            (
                "",
                "function* g(a = 1) { yield a; } var it = g(); assert.sameValue(throws(Test262Error, function () { it.throw(new Test262Error()); }), true); assert.sameValue(it.next().done, true);",
            ),
            (
                "flags: [async]",
                "async function* g(a = 1) { yield a; } g().next().then(function (result) { assert.sameValue(result.value, 1); }).then($DONE, $DONE);",
            ),
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, (flags, body)) in CASES.iter().enumerate() {
                let source = wrap(
                    &format!("description: generator parameters\n{flags}"),
                    &format!("{THROWS}{body}"),
                );
                let label = format!("generator-parameters-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn the_host_object_does_real_work() {
        const CASES: [&str; 5] = [
            "var b = new ArrayBuffer(8); assert.sameValue($262.detachArrayBuffer(b), null); \
             assert.sameValue(b.detached, true); assert.sameValue(b.byteLength, 0);",
            "var view = new Uint8Array(4); $262.detachArrayBuffer(view.buffer); \
             assert.sameValue(view.length, 0);",
            "assert.sameValue($262.global, globalThis);",
            "assert.sameValue($262.evalScript('1 + 2'), 3);",
            "var d = Object.getOwnPropertyDescriptor(globalThis, '$262'); \
             assert.sameValue(d.enumerable, false); assert.sameValue(d.writable, true); \
             assert.sameValue(d.configurable, true);",
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, body) in CASES.iter().enumerate() {
                let source = wrap("description: the host object", body);
                let label = format!("host-object-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn wrapper_prototypes_report_their_own_primitive() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [&str; 7] = [
            "assert.sameValue('a'.toString(), 'a');",
            "assert.sameValue('a'.valueOf(), 'a');",
            "assert.sameValue(new String('a').toString(), 'a');",
            "assert.sameValue(String.prototype.toString.call(new String('')), '');",
            "assert.sameValue(throws(TypeError, function () { String.prototype.toString.call(1); }), true);",
            "assert.sameValue(true.toString(), 'true'); assert.sameValue(new Boolean(false).toString(), 'false');",
            "assert.sameValue(throws(TypeError, function () { Boolean.prototype.toString.call('a'); }), true);",
        ];
        for (index, body) in CASES.iter().enumerate() {
            let source = wrap(
                "description: wrapper prototypes",
                &format!("{THROWS}{body}"),
            );
            if let Err(error) = run_fixture(&format!("wrapper-prototypes-{index}"), &source) {
                panic!("{body}: {error:?}");
            }
        }
    }

    #[test]
    fn a_template_substitution_is_converted_with_to_string() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [&str; 4] = [
            "var o = { valueOf() { return 'V'; }, toString() { return 'T'; } }; \
             assert.sameValue(`${o}`, 'T');",
            "assert.sameValue(`${1}${'a'}${null}${undefined}`, '1anullundefined');",
            "assert.sameValue(throws(TypeError, function () { `${Symbol()}`; }), true);",
            "var log = ''; var part = function (name) { return { toString() { log += name; \
             return name; } }; }; assert.sameValue(`${part('a')}-${part('b')}`, 'a-b'); \
             assert.sameValue(log, 'ab');",
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, body) in CASES.iter().enumerate() {
                let source = wrap("description: template literals", &format!("{THROWS}{body}"));
                let label = format!("template-literal-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn an_anonymous_function_takes_the_name_it_initializes() {
        const CASES: [&str; 20] = [
            "var f = function () {}; assert.sameValue(f.name, 'f');",
            "var a = () => {}; assert.sameValue(a.name, 'a');",
            "var c = class {}; assert.sameValue(c.name, 'c');",
            "var g = function* () {}; assert.sameValue(g.name, 'g');",
            "var { x = function () {} } = {}; assert.sameValue(x.name, 'x');",
            "var [y = () => {}] = []; assert.sameValue(y.name, 'y');",
            "function p(z = class {}) { return z; } assert.sameValue(p().name, 'z');",
            "var h; h = function () {}; assert.sameValue(h.name, 'h');",
            "var i; i ??= function () {}; assert.sameValue(i.name, 'i');",
            "var j; j ||= () => {}; assert.sameValue(j.name, 'j');",
            "var u; [u = function () {}] = []; assert.sameValue(u.name, 'u');",
            "var v; ({ v = function () {} } = {}); assert.sameValue(v.name, 'v');",
            "var o = { m: function () {}, 'n': () => {} }; assert.sameValue(o.m.name, 'm'); \
             assert.sameValue(o.n.name, 'n');",
            "var paren = (function () {}); assert.sameValue(paren.name, 'paren');",
            "var kept = function other() {}; assert.sameValue(kept.name, 'other');",
            "var cover = (0, function () {}); assert.sameValue(cover.name, '');",
            "var q; (q) = function () {}; assert.sameValue(q.name, '');",
            "var s = class { static name() {} }; assert.sameValue(typeof s.name, 'function');",
            "var inner = class { static c = class {}; }; assert.sameValue(inner.c.name, 'c');",
            "var calls = 0; var [w = (calls += 1, undefined)] = []; assert.sameValue(calls, 1);",
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, body) in CASES.iter().enumerate() {
                let source = wrap("description: function names", body);
                let label = format!("function-names-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn indirect_eval_runs_in_the_global_scope() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [&str; 12] = [
            "assert.sameValue((0, eval)('1 + 1'), 2);",
            "assert.sameValue((0, eval)(1), 1);",
            "assert.sameValue((0, eval)(), undefined);",
            "var x = 1; assert.sameValue((0, eval)('x'), 1);",
            "(0, eval)('var y = 2'); assert.sameValue(globalThis.y, 2);",
            "(0, eval)('function g() { return 3; }'); assert.sameValue(globalThis.g(), 3);",
            "assert.sameValue((0, eval)('this'), globalThis);",
            "assert.sameValue((0, eval)('if (true) { 4; } else { 5; }'), 4);",
            "assert.sameValue(throws(SyntaxError, function () { (0, eval)('('); }), true);",
            "assert.sameValue(throws(TypeError, function () { new eval('1'); }), true);",
            "assert.sameValue(throws(SyntaxError, function () { (0, eval)('\"use strict\"; with (a) {}'); }), true);",
            "assert.sameValue(throws(SyntaxError, function () { Function('\"use strict\"; var public;'); }), true);",
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, body) in CASES.iter().enumerate() {
                let source = wrap("description: indirect eval", &format!("{THROWS}{body}"));
                let label = format!("indirect-eval-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn a_script_declares_on_the_global_object() {
        const CASES: [(&str, &str); 11] = [
            (
                "",
                "function f() { var x = 1; var x; return x; } assert.sameValue(f(), 1);",
            ),
            ("", "var x = 1; assert.sameValue(globalThis.x, 1);"),
            ("", "function f() {} assert.sameValue(globalThis.f, f);"),
            ("", "assert.sameValue(hoisted, undefined); var hoisted = 1;"),
            (
                "",
                "assert.sameValue(early(), 1); function early() { return 1; }",
            ),
            ("", "assert.sameValue(this, globalThis);"),
            ("", "var undefined; assert.sameValue(undefined, void 0);"),
            ("", "var Array; assert.sameValue(typeof Array, 'function');"),
            (
                "",
                "let y = 1; assert.sameValue(y, 1); assert.sameValue('y' in globalThis, false);",
            ),
            (
                "",
                "var v = 1; (function () { v = 2; })(); assert.sameValue(globalThis.v, 2);",
            ),
            (
                "flags: [module]",
                "var x = 1; assert.sameValue('x' in globalThis, false); assert.sameValue(this, undefined);",
            ),
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, (flags, body)) in CASES.iter().enumerate() {
                let source = wrap(&format!("description: script goal\n{flags}"), body);
                let label = format!("script-goal-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn module_syntax_is_an_early_error_in_a_script() {
        for (index, body) in ["export var x;", "import './composed.js';", "import.meta;"]
            .iter()
            .enumerate()
        {
            let source = wrap(
                "description: module syntax in a script\n\
                 negative:\n  phase: parse\n  type: SyntaxError",
                body,
            );
            run_fixture(&format!("script-goal-early-{index}"), &source)
                .unwrap_or_else(|error| panic!("{body}: {error:?}"));
        }
    }

    #[test]
    fn a_lint_cannot_refuse_a_valid_program() {
        let source = wrap(
            "description: a with statement is valid in sloppy code\nflags: [noStrict]",
            "with ({ a: 1 }) { assert.sameValue(a, 1); }",
        );
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            run_fixture_in(mode, &format!("with-{mode:?}"), &source).unwrap();
        }
    }

    #[test]
    fn strict_and_sloppy_code_differ_the_same_way_in_every_tier() {
        const THROWS: &str = "function throws(kind, body) {\n\
            try { body(); } catch (error) { return error instanceof kind; }\n\
            return false;\n\
            }\n";
        const CASES: [(&str, &str); 18] = [
            (
                "noStrict",
                "assert.sameValue((function () { return this; })(), globalThis);",
            ),
            (
                "onlyStrict",
                "assert.sameValue((function () { return this; })(), undefined);",
            ),
            (
                "noStrict",
                "assert.sameValue((function () { return this; }).call(null), globalThis);",
            ),
            (
                "noStrict",
                "assert.sameValue(typeof (function () { return this; }).call(1), 'object');",
            ),
            (
                "noStrict",
                "var f = function () { return this === this; }; assert.sameValue(f.call(1), true);",
            ),
            (
                "onlyStrict",
                "assert.sameValue((function () { return this; }).call(1), 1);",
            ),
            (
                "noStrict",
                "assert.sameValue((function () { return (() => this)(); })(), globalThis);",
            ),
            (
                "noStrict",
                "function *g() { yield this; } assert.sameValue(g().next().value, globalThis);",
            ),
            (
                "noStrict",
                "function f() { 'use strict'; return this; } assert.sameValue(f(), undefined);",
            ),
            (
                "noStrict",
                "class C { m() { return this; } } var m = new C().m; assert.sameValue(m(), undefined);",
            ),
            (
                "noStrict",
                "var o = Object.freeze({ a: 1 }); o.a = 2; assert.sameValue(o.a, 1);",
            ),
            (
                "onlyStrict",
                "var o = Object.freeze({ a: 1 }); assert.sameValue(throws(TypeError, function () { o.a = 2; }), true);",
            ),
            (
                "noStrict",
                "'text'.x = 1; (1).x = 1; assert.sameValue((1).x, undefined);",
            ),
            (
                "onlyStrict",
                "assert.sameValue(throws(TypeError, function () { 'text'.x = 1; }), true);",
            ),
            (
                "noStrict",
                "undeclared = 1; assert.sameValue(undeclared, 1);",
            ),
            (
                "onlyStrict",
                "assert.sameValue(throws(ReferenceError, function () { undeclared = 1; }), true);",
            ),
            (
                "noStrict",
                "assert.sameValue(delete Object.prototype, false);",
            ),
            (
                "onlyStrict",
                "assert.sameValue(throws(TypeError, function () { delete Object.prototype; }), true);",
            ),
        ];
        for mode in [
            ExecutionMode::Interpreter,
            ExecutionMode::Jit,
            ExecutionMode::Aot,
        ] {
            for (index, (flag, body)) in CASES.iter().enumerate() {
                let source = wrap(
                    &format!("description: strictness\nflags: [{flag}]"),
                    &format!("{THROWS}{body}"),
                );
                let label = format!("strictness-{mode:?}-{index}");
                if let Err(error) = run_fixture_in(mode, &label, &source) {
                    panic!("{mode:?} [{flag}] {body}: {error:?}");
                }
            }
        }
    }

    #[test]
    fn a_composed_test_is_compiled_as_strict_code() {
        let source = wrap(
            "description: reserved in strict code only, so this must not compile\n\
             flags: [onlyStrict]",
            "var public;",
        );
        assert!(
            run_fixture("strict-compiled", &source).is_err(),
            "the directive reaches the test past the harness"
        );
    }

    #[test]
    fn an_early_negative_is_parsed_under_its_own_flags() {
        let strict = wrap(
            "description: reserved in strict code only\n\
             flags: [onlyStrict]\n\
             negative:\n  phase: parse\n  type: SyntaxError",
            "var public;",
        );
        run_fixture("strict-parse", &strict).expect("rejected as strict code");
        let module = wrap(
            "description: reserved in module code only\n\
             flags: [module]\n\
             negative:\n  phase: parse\n  type: SyntaxError",
            "var await;",
        );
        run_fixture("module-parse", &module).expect("rejected as module code");
    }

    #[test]
    fn a_module_case_without_imports_has_the_module_goal() {
        let source = wrap(
            "description: reserved in module code only, so this must not compile\n\
             flags: [module]",
            "var await;",
        );
        assert!(
            run_fixture("module-goal", &source).is_err(),
            "a test with no import or export is still a module"
        );
    }

    #[test]
    fn interpreter_runner_judges_runtime_reference_error_fixture() {
        let harness = runner_scratch("neg-runtime-harness");
        let scratch = runner_scratch("neg-runtime-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: unresolvable reference throws\n\
             negative:\n  phase: runtime\n  type: ReferenceError",
            "unresolvableReference;",
        );
        let parsed = parse_test(&source).unwrap();
        assert_eq!(
            parsed.frontmatter.negative,
            Some(Negative {
                phase: NegativePhase::Runtime,
                error_type: NegativeType::ReferenceError,
            })
        );
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            run_variant(&runner, &parsed, &plan, &sources, variant).unwrap();
        }
    }

    #[test]
    fn interpreter_runner_judges_parse_syntax_error_fixture() {
        let harness = runner_scratch("neg-parse-harness");
        let scratch = runner_scratch("neg-parse-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: a numeric literal is not a binding target\n\
             negative:\n  phase: parse\n  type: SyntaxError",
            "var 1 = 1;",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            let script = compose_script(&parsed, &plan, variant, &sources).unwrap();
            assert_eq!(
                script.untouched,
                variant.kind == SourceKind::ScriptNonStrict,
                "an early negative takes no harness, only its strict directive"
            );
            assert_eq!(
                &script.bytes[script.test_offset..],
                parsed.source_bytes.as_slice()
            );
            run_variant(&runner, &parsed, &plan, &sources, variant).unwrap();
        }
    }

    #[test]
    fn interpreter_runner_judges_async_done_fixture() {
        let harness = runner_scratch("async-harness");
        let scratch = runner_scratch("async-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        write_harness(&harness, "doneprintHandle.js", DONEPRINT_JS);
        let source = wrap(
            "description: an async test completes through $DONE\nflags: [async]",
            "$DONE();",
        );
        let parsed = parse_test(&source).unwrap();
        assert!(parsed.frontmatter.has(Flag::Async));
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            run_variant(&runner, &parsed, &plan, &sources, variant).unwrap();
        }
    }

    /// An async request expecting `negative`, with the deadline the trace
    /// helpers below share.
    fn negative_async_request(negative: Option<Negative>) -> RunRequest {
        RunRequest {
            mode: ExecutionMode::Interpreter,
            variant: ExecutionVariant {
                kind: SourceKind::ScriptNonStrict,
            },
            script: ComposedScript {
                bytes: Vec::new(),
                test_offset: 0,
                kind: SourceKind::ScriptNonStrict,
                untouched: false,
            },
            negative,
            async_done: true,
            deadline: Duration::from_millis(100),
        }
    }

    /// An async outcome whose single `$DONE` event carries `failure_value`.
    fn async_done_outcome(kind: DoneEventKind, failure_value: Option<&str>) -> RunOutcome {
        RunOutcome::Async(AsyncTrace {
            events: vec![DoneEvent {
                kind,
                at: Duration::from_millis(1),
            }],
            failure_value: failure_value.map(str::to_owned),
            exited_at: None,
            deadline: Duration::from_millis(100),
        })
    }

    #[test]
    fn an_async_done_failure_satisfies_a_matching_runtime_negative() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let outcome =
            async_done_outcome(DoneEventKind::Error, Some("Test262Error: expected failure"));

        assert_eq!(judge_run(&request, &outcome), Ok(()));
    }

    #[test]
    fn an_async_done_failure_with_the_wrong_type_is_a_mismatch() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::TypeError,
        }));
        let outcome = async_done_outcome(
            DoneEventKind::Error,
            Some("Test262Error: a different class"),
        );

        assert!(matches!(
            judge_run(&request, &outcome),
            Err(OracleError::ExpectationMismatch { .. })
        ));
    }

    #[test]
    fn an_async_done_failure_demands_the_runtime_phase() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Parse,
            error_type: NegativeType::Test262Error,
        }));
        let outcome = async_done_outcome(
            DoneEventKind::Error,
            Some("Test262Error: not a parse error"),
        );

        assert!(matches!(
            judge_run(&request, &outcome),
            Err(OracleError::ExpectationMismatch { .. })
        ));
    }

    #[test]
    fn an_async_done_failure_still_fails_a_positive_request() {
        let request = negative_async_request(None);
        let outcome = async_done_outcome(DoneEventKind::Error, Some("Test262Error: unexpected"));

        assert_eq!(
            judge_run(&request, &outcome),
            Err(OracleError::Done(DoneFailure::Error))
        );
    }

    #[test]
    fn an_async_completion_cannot_satisfy_a_negative() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let outcome = async_done_outcome(DoneEventKind::Success, None);

        assert!(matches!(
            judge_run(&request, &outcome),
            Err(OracleError::ExpectationMismatch { .. })
        ));
    }

    #[test]
    fn a_malformed_async_trace_stays_blocking_under_a_negative() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let duplicate = RunOutcome::Async(AsyncTrace {
            events: vec![
                DoneEvent {
                    kind: DoneEventKind::Error,
                    at: Duration::from_millis(1),
                },
                DoneEvent {
                    kind: DoneEventKind::Success,
                    at: Duration::from_millis(2),
                },
            ],
            failure_value: Some("Test262Error: first".to_owned()),
            exited_at: None,
            deadline: Duration::from_millis(100),
        });

        assert_eq!(
            judge_run(&request, &duplicate),
            Err(OracleError::Done(DoneFailure::Duplicate))
        );
    }
    #[test]
    fn an_async_late_failure_dominates_a_negative_request() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let late = RunOutcome::Async(AsyncTrace {
            events: vec![DoneEvent {
                kind: DoneEventKind::Error,
                at: Duration::from_millis(101),
            }],
            failure_value: Some("Test262Error: too slow".to_owned()),
            exited_at: None,
            deadline: Duration::from_millis(100),
        });

        assert_eq!(
            judge_run(&request, &late),
            Err(OracleError::Done(DoneFailure::Late))
        );
    }

    #[test]
    fn an_async_missing_failure_dominates_a_negative_request() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let missing = RunOutcome::Async(AsyncTrace {
            events: vec![],
            failure_value: None,
            exited_at: None,
            deadline: Duration::from_millis(100),
        });

        assert_eq!(
            judge_run(&request, &missing),
            Err(OracleError::Done(DoneFailure::Missing))
        );
    }

    #[test]
    fn an_async_early_exit_dominates_a_negative_request() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let early = RunOutcome::Async(AsyncTrace {
            events: vec![],
            failure_value: None,
            exited_at: Some(Duration::from_millis(1)),
            deadline: Duration::from_millis(100),
        });

        assert_eq!(
            judge_run(&request, &early),
            Err(OracleError::Done(DoneFailure::EarlyExit))
        );
    }

    #[test]
    fn an_async_done_failure_with_an_unknown_constructor_is_a_mismatch() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));
        let outcome =
            async_done_outcome(DoneEventKind::Error, Some("CustomError: not a known type"));

        match judge_run(&request, &outcome) {
            Err(OracleError::ExpectationMismatch {
                expected, actual, ..
            }) => {
                assert_eq!(expected, "Runtime/Test262Error");
                assert_eq!(actual, "Runtime/CustomError: not a known type");
            }
            other => panic!("expected ExpectationMismatch, got {other:?}"),
        }
    }

    #[test]
    fn the_internal_marker_captures_the_done_argument_for_negative_matching() {
        let trace = observed_done_trace(
            b"$DONE(Test262Error: expected failure)\n",
            &[],
            Duration::from_millis(1),
            Duration::from_millis(100),
        );
        assert_eq!(
            trace.failure_value.as_deref(),
            Some("Test262Error: expected failure")
        );
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::Test262Error,
        }));

        assert_eq!(judge_run(&request, &RunOutcome::Async(trace)), Ok(()));
    }

    #[test]
    fn the_canonical_failure_marker_captures_the_thrown_type() {
        let trace = observed_done_trace(
            b"Test262:AsyncTestFailure: TypeError: nope\n",
            &[],
            Duration::from_millis(1),
            Duration::from_millis(100),
        );
        assert_eq!(trace.failure_value.as_deref(), Some("TypeError: nope"));
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::TypeError,
        }));

        assert_eq!(judge_run(&request, &RunOutcome::Async(trace)), Ok(()));
    }

    #[test]
    fn interpreter_runner_judges_async_negative_done_fixture() {
        let harness = runner_scratch("async-negative-harness");
        let scratch = runner_scratch("async-negative-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        write_harness(&harness, "doneprintHandle.js", DONEPRINT_JS);
        let source = wrap(
            "description: an async negative test fails through $DONE\n\
             flags: [async]\n\
             negative:\n  phase: runtime\n  type: TypeError",
            "$DONE(new TypeError('expected failure'));",
        );
        let parsed = parse_test(&source).unwrap();
        assert_eq!(
            parsed.frontmatter.negative,
            Some(Negative {
                phase: NegativePhase::Runtime,
                error_type: NegativeType::TypeError,
            })
        );
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            run_variant(&runner, &parsed, &plan, &sources, variant).unwrap();
        }
    }

    #[test]
    fn interpreter_runner_fails_a_positive_async_done_error_fixture() {
        let harness = runner_scratch("async-positive-error-harness");
        let scratch = runner_scratch("async-positive-error-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        write_harness(&harness, "doneprintHandle.js", DONEPRINT_JS);
        let source = wrap(
            "description: an async test fails through $DONE\nflags: [async]",
            "$DONE(new Test262Error('unexpected failure'));",
        );
        let parsed = parse_test(&source).unwrap();
        assert!(parsed.frontmatter.negative.is_none());
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            assert_eq!(
                run_variant(&runner, &parsed, &plan, &sources, variant),
                Err(OracleError::Done(DoneFailure::Error))
            );
        }
    }

    #[test]
    fn guest_throw_is_classified_not_blocked() {
        let harness = runner_scratch("guest-harness");
        let scratch = runner_scratch("guest-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: a guest throw is classified by constructor name",
            "throw new Test262Error('unmatched');",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            let result = run_variant(&runner, &parsed, &plan, &sources, variant);
            // The runtime boundary now resolves the thrown value's
            // constructor name (Test262Error) so the oracle classifies it
            // as Runtime/Test262Error. Since the test expects success,
            // this is an ExpectationMismatch, not a BlockedRun.
            assert!(
                matches!(&result,
                    Err(OracleError::ExpectationMismatch { expected, actual, .. })
                        if expected == "success" && actual == "Runtime/Test262Error"
                ),
                "a guest throw with a known constructor must be classified, not blocked: {result:?}"
            );
        }
    }

    #[test]
    fn a_failed_run_reads_as_what_it_expected_and_what_the_throw_said() {
        let mismatch = |message: &str| OracleError::ExpectationMismatch {
            expected: "success".to_owned(),
            actual: "Runtime/Test262Error".to_owned(),
            message: message.to_owned(),
        };
        assert_eq!(
            failure_detail(&mismatch("Expected SameValue(«1», «2»)")),
            "expected success, got Runtime/Test262Error: Expected SameValue(«1», «2»)"
        );
        assert_eq!(
            failure_detail(&mismatch("")),
            "expected success, got Runtime/Test262Error"
        );
        let blocked = OracleError::BlockedRun {
            detail: "no verdict".to_owned(),
        };
        assert!(failure_detail(&blocked).contains("no verdict"));
    }

    #[test]
    fn a_thrown_message_never_changes_a_verdict() {
        let request = negative_async_request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::TypeError,
        }));
        for message in ["", "anything at all"] {
            let outcome = RunOutcome::Completed {
                thrown: Some(ThrownError {
                    phase: NegativePhase::Runtime,
                    error_type: NegativeType::TypeError,
                    message: message.to_owned(),
                }),
            };
            assert!(judge_run(&request, &outcome).is_ok());
        }
    }

    #[test]
    fn fuel_exhaustion_blocks_the_run() {
        let harness = runner_scratch("fuel-harness");
        let scratch = runner_scratch("fuel-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: an endless loop never completes",
            "for (;;) {}",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        for variant in &plan.variants {
            let script = compose_script(&parsed, &plan, variant, &sources).unwrap();
            let request = RunRequest {
                mode: ExecutionMode::Interpreter,
                variant: variant.clone(),
                script,
                negative: plan.negative.clone(),
                async_done: plan.async_done,
                deadline: Duration::from_millis(1),
            };
            let outcome = runner.run(&request);
            assert!(matches!(
                judge_run(&request, &outcome),
                Err(OracleError::BlockedRun { .. })
            ));
        }
    }

    #[test]
    fn all_backends_resolve_successfully() {
        let scratch = runner_scratch("all-backends");
        for mode in ExecutionMode::ALL {
            let runner = backend_runner(mode, &scratch).unwrap_or_else(|reason| {
                panic!("backend_runner({mode:?}) should succeed: {reason}")
            });
            // The runner is the same type for all modes; it dispatches
            // internally on the request's mode field.
            let _ = runner.run(&RunRequest {
                mode,
                variant: ExecutionVariant {
                    kind: SourceKind::ScriptNonStrict,
                },
                script: ComposedScript {
                    bytes: b"// empty\n".to_vec(),
                    test_offset: 0,
                    kind: SourceKind::ScriptNonStrict,
                    untouched: false,
                },
                negative: None,
                async_done: false,
                deadline: Duration::from_millis(100),
            });
        }
    }

    #[test]
    fn trivially_passing_fixture_passes_in_all_modes() {
        let harness = runner_scratch("pass-harness");
        let scratch = runner_scratch("pass-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: a trivially passing test",
            "assert.sameValue(1, 1);",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        for mode in ExecutionMode::ALL {
            let runner = backend_runner(mode, &scratch).unwrap();
            let report = evaluate_in_mode(
                &runner,
                mode,
                &parsed,
                &plan,
                &sources,
                Duration::from_secs(5),
            );
            assert!(
                report.is_ok(),
                "trivially passing fixture should PASS in {mode:?}: {report:?}"
            );
        }
    }

    #[test]
    fn endless_loop_times_out_in_all_modes() {
        let harness = runner_scratch("timeout-harness");
        let scratch = runner_scratch("timeout-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: an endless loop never completes",
            "for (;;) {}",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        for mode in ExecutionMode::ALL {
            let runner = backend_runner(mode, &scratch).unwrap();
            let result = evaluate_in_mode(
                &runner,
                mode,
                &parsed,
                &plan,
                &sources,
                Duration::from_millis(1),
            );
            assert!(
                matches!(
                    result,
                    Err(OracleError::BlockedRun { .. }) | Err(OracleError::ModeFailure(_))
                ),
                "endless loop should time out (blocked or mode failure) in {mode:?}: {result:?}"
            );
        }
    }

    #[test]
    fn failing_assertion_yields_blocking_fail() {
        let harness = runner_scratch("fail-harness");
        let scratch = runner_scratch("fail-scratch");
        write_harness(&harness, "assert.js", ASSERT_JS);
        write_harness(&harness, "sta.js", STA_JS);
        let source = wrap(
            "description: a failing assertion",
            "assert.sameValue(1, 2);",
        );
        let parsed = parse_test(&source).unwrap();
        let plan = plan_execution(&parsed.frontmatter, &harness).unwrap();
        let sources = load_harness_sources(&plan, &FileHarnessLoader).unwrap();
        let runner = backend_runner(ExecutionMode::Interpreter, &scratch).unwrap();
        let result = evaluate_in_mode(
            &runner,
            ExecutionMode::Interpreter,
            &parsed,
            &plan,
            &sources,
            Duration::from_secs(5),
        );
        // assert.sameValue(1, 2) throws a Test262Error via the harness.
        // The runtime boundary now resolves the constructor name, so the
        // oracle classifies it as Runtime/Test262Error. Since the test
        // expects success, this is an ExpectationMismatch wrapped in
        // ModeFailure by evaluate_in_mode.
        assert!(
            matches!(&result,
                Err(OracleError::ModeFailure(failure))
                    if failure.detail.contains("Runtime/Test262Error")
            ),
            "failing assertion should yield ModeFailure with Runtime/Test262Error: {result:?}"
        );
    }
}
