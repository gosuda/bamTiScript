//! Test262 runtime harness: include loading, exact async `$DONE` accounting,
//! negative-phase classification, and fail-closed agent hooks.
//!
//! This module owns no verdict rules of its own. Ordering, duplication, and
//! phase comparison are decided by [`judge_done`] and [`judge_run`] in
//! [`super::test262`]; the harness only supplies exactly observed facts and
//! enriches the async failure with the stringified `$DONE` argument. An
//! unavailable runtime capability becomes [`HarnessError::Unsupported`], which
//! blocks the obligation and can never become a pass.

use std::fs;
use std::time::Duration;

use super::TerminalState;
use super::test262::{
    AsyncTrace, ConfinedInclude, DoneEvent, DoneEventKind, DoneFailure, ExecutionPlan, HarnessPlan,
    HarnessSource, NegativePhase, NegativeType, OracleError, RunOutcome, RunRequest, ThrownError,
    judge_done, judge_run,
};

/// A runtime facility Test262 asks for that this engine does not provide.
///
/// Every variant is a hard block. The harness reports the missing facility
/// instead of substituting an inert hook that would let a test report success.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Capability {
    /// `$262.createRealm`: the machine exposes no realm factory.
    CreateRealm,
    /// `$262.agent.start`: the host exposes no agent scheduler.
    AgentStart,
    /// `$262.agent.broadcast`: requires a started agent.
    AgentBroadcast,
    /// `$262.agent.getReport`: requires a started agent.
    AgentGetReport,
    /// `$262.agent.sleep`: requires a blocking scheduler.
    AgentSleep,
}

impl Capability {
    /// The exact `$262` member name this capability backs.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CreateRealm => "$262.createRealm",
            Self::AgentStart => "$262.agent.start",
            Self::AgentBroadcast => "$262.agent.broadcast",
            Self::AgentGetReport => "$262.agent.getReport",
            Self::AgentSleep => "$262.agent.sleep",
        }
    }
}

/// Why the harness refused to report a pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HarnessError {
    /// A failure the shared Test262 oracle already models.
    Oracle(OracleError),
    /// `$DONE` received an argument. `value` is its exact stringification.
    DoneFailed { value: String },
    /// The deadline elapsed with no `$DONE` call.
    Timeout { deadline: Duration },
    /// A required runtime facility does not exist.
    Unsupported { capability: Capability },
    /// A planned harness include could not be loaded.
    Include { requested: String, detail: String },
}

impl From<OracleError> for HarnessError {
    fn from(error: OracleError) -> Self {
        Self::Oracle(error)
    }
}

/// Maps a harness result onto the shared oracle terminal state.
///
/// Only a clean `Ok` is a pass; every error is blocking.
#[must_use]
pub fn terminal_state(result: &Result<(), HarnessError>) -> TerminalState {
    match result {
        Ok(()) => TerminalState::Pass,
        Err(_) => TerminalState::Blocking,
    }
}

/// The argument `$DONE` was invoked with.
///
/// [`Self::None`] and [`Self::Undefined`] stay distinct so a JavaScript string
/// whose text happens to be `"undefined"` is still a failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoneArgument<'a> {
    /// `$DONE()`.
    None,
    /// `$DONE(undefined)`.
    Undefined,
    /// `$DONE(v)` where `v` stringifies to this exact text.
    Value(&'a str),
}

/// One recorded `$DONE` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DoneCall {
    /// Whether this call reported completion or failure.
    pub kind: DoneEventKind,
    /// Elapsed time at the call.
    pub at: Duration,
    /// Exact stringified argument for a failure; `None` for a completion.
    pub value: Option<String>,
}

/// Accumulates `$DONE` calls for one async test.
///
/// The first call is authoritative and is never overwritten. Later calls are
/// still recorded so [`judge_done`] observes the duplication.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DoneRecorder {
    deadline: Duration,
    events: Vec<DoneEvent>,
    first: Option<DoneCall>,
    exited_at: Option<Duration>,
}

impl DoneRecorder {
    /// A recorder that treats `deadline` as the async completion budget.
    #[must_use]
    pub const fn new(deadline: Duration) -> Self {
        Self {
            deadline,
            events: Vec::new(),
            first: None,
            exited_at: None,
        }
    }

    /// Records one `$DONE` call at `at`.
    ///
    /// Returns the duplicate error for any call after the first; the first call
    /// remains the recorded outcome either way.
    pub fn call(&mut self, argument: DoneArgument<'_>, at: Duration) -> Result<(), HarnessError> {
        let (kind, value) = match argument {
            DoneArgument::None | DoneArgument::Undefined => (DoneEventKind::Success, None),
            DoneArgument::Value(text) => (DoneEventKind::Error, Some(text.to_owned())),
        };
        self.events.push(DoneEvent { kind, at });
        if self.first.is_some() {
            return Err(HarnessError::Oracle(OracleError::Done(
                DoneFailure::Duplicate,
            )));
        }
        self.first = Some(DoneCall { kind, at, value });
        Ok(())
    }

    /// Records that the script exited at `at`, for early-exit detection.
    pub fn record_exit(&mut self, at: Duration) {
        self.exited_at = Some(at);
    }

    /// The authoritative first call, if any.
    #[must_use]
    pub fn first_call(&self) -> Option<&DoneCall> {
        self.first.as_ref()
    }

    /// The observed calls as a shared-oracle trace.
    ///
    /// The first failure's stringified argument rides on the trace so
    /// [`judge_run`] can match it against a negative expectation.
    #[must_use]
    pub fn trace(&self) -> AsyncTrace {
        AsyncTrace {
            failure_value: self
                .first
                .as_ref()
                .filter(|call| call.kind == DoneEventKind::Error)
                .and_then(|call| call.value.clone()),
            events: self.events.clone(),
            exited_at: self.exited_at,
            deadline: self.deadline,
        }
    }

    /// Judges the recorded async run after observing it for `elapsed`.
    ///
    /// A deadline that elapses with no call is a typed timeout rather than a
    /// missing-call failure, so an unfinished test never resembles a pass.
    pub fn judge(&self, elapsed: Duration) -> Result<(), HarnessError> {
        if self.first.is_none() && elapsed >= self.deadline {
            return Err(HarnessError::Timeout {
                deadline: self.deadline,
            });
        }
        match judge_done(&self.trace()) {
            Ok(()) => Ok(()),
            Err(DoneFailure::Error) => Err(HarnessError::DoneFailed {
                value: self
                    .first
                    .as_ref()
                    .and_then(|call| call.value.clone())
                    .unwrap_or_default(),
            }),
            Err(other) => Err(HarnessError::Oracle(OracleError::Done(other))),
        }
    }
}

/// Supplies the bytes of a confined harness include.
pub trait HarnessLoader {
    /// Reads one planned include, or explains why it is unavailable.
    fn load(&self, include: &ConfinedInclude) -> Result<Vec<u8>, HarnessError>;
}

/// Reads includes from the confined path the plan resolved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileHarnessLoader;

impl HarnessLoader for FileHarnessLoader {
    fn load(&self, include: &ConfinedInclude) -> Result<Vec<u8>, HarnessError> {
        fs::read(&include.confined).map_err(|error| HarnessError::Include {
            requested: include.requested.clone(),
            detail: error.to_string(),
        })
    }
}

/// Loads every planned include in exactly its declared order.
///
/// Each source is named by its requested include so composition resolves it.
/// A raw plan needs no harness and yields an empty list. Any unreadable
/// include fails the whole load rather than silently shortening the prefix.
pub fn load_harness_sources<L: HarnessLoader>(
    plan: &ExecutionPlan,
    loader: &L,
) -> Result<Vec<HarnessSource>, HarnessError> {
    let HarnessPlan::Canonical { files, .. } = &plan.harness else {
        return Ok(Vec::new());
    };
    let mut sources = Vec::with_capacity(files.len());
    for file in files {
        sources.push(HarnessSource {
            name: file.requested.clone(),
            bytes: loader.load(file)?,
        });
    }
    Ok(sources)
}

/// The pipeline stage that reported a failure.
///
/// The stage, not the error type, fixes the Test262 negative phase, so a
/// runtime throw can never satisfy a `parse` expectation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// Source was rejected before any code ran.
    Compile,
    /// Module linking or binding resolution failed.
    Instantiate,
    /// Compiled code threw while running.
    Execute,
}

impl Stage {
    /// The Test262 negative phase this stage corresponds to.
    #[must_use]
    pub const fn phase(self) -> NegativePhase {
        match self {
            Self::Compile => NegativePhase::Parse,
            Self::Instantiate => NegativePhase::Resolution,
            Self::Execute => NegativePhase::Runtime,
        }
    }
}

/// Judges a synchronous run whose failure, if any, was observed at `failure`.
///
/// Delegates the expectation comparison to [`judge_run`] so the harness keeps a
/// single verdict authority.
pub fn judge_stage_outcome(
    request: &RunRequest,
    failure: Option<(Stage, NegativeType)>,
) -> Result<(), HarnessError> {
    let thrown = failure.map(|(stage, error_type)| ThrownError {
        phase: stage.phase(),
        error_type,
        message: String::new(),
    });
    judge_run(request, &RunOutcome::Completed { thrown }).map_err(HarnessError::Oracle)
}

/// An agent's report text.
///
/// Deliberately opaque: it exposes only its bytes. No comparison, parsing, or
/// conversion here can turn report text into a verdict, so a test cannot pass
/// itself by printing a magic string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AgentReport(String);

impl AgentReport {
    /// Wraps report text exactly as the agent produced it.
    #[must_use]
    pub fn new(text: impl Into<String>) -> Self {
        Self(text.into())
    }

    /// The exact report text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A started agent, identified by start order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AgentId(pub usize);

/// The scheduler backing `$262.agent`.
pub trait AgentRuntime {
    /// Starts an agent running `source`.
    fn start(&mut self, source: &str) -> Result<AgentId, HarnessError>;

    /// Publishes a broadcast to every started agent.
    fn broadcast(&mut self, payload: &str) -> Result<(), HarnessError>;

    /// Drains pending reports in arrival order.
    fn drain_reports(&mut self) -> Result<Vec<AgentReport>, HarnessError>;

    /// Stops one agent and reclaims it. Must tolerate repeat calls.
    fn terminate(&mut self, agent: AgentId);
}

/// The scheduler this engine actually has: none.
///
/// Every start attempt blocks the obligation with a typed capability error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsupportedAgents;

impl AgentRuntime for UnsupportedAgents {
    fn start(&mut self, _source: &str) -> Result<AgentId, HarnessError> {
        Err(HarnessError::Unsupported {
            capability: Capability::AgentStart,
        })
    }

    fn broadcast(&mut self, _payload: &str) -> Result<(), HarnessError> {
        Err(HarnessError::Unsupported {
            capability: Capability::AgentBroadcast,
        })
    }

    fn drain_reports(&mut self) -> Result<Vec<AgentReport>, HarnessError> {
        Err(HarnessError::Unsupported {
            capability: Capability::AgentGetReport,
        })
    }

    fn terminate(&mut self, _agent: AgentId) {}
}

/// Owns every agent started for one test and tears them down on drop.
///
/// Teardown is deterministic: agents stop in reverse start order on every exit
/// path, including an early `?` return, a timeout, and a panic unwind.
#[derive(Debug)]
pub struct AgentSession<'a, R: AgentRuntime> {
    runtime: &'a mut R,
    started: Vec<AgentId>,
}

impl<'a, R: AgentRuntime> AgentSession<'a, R> {
    /// Binds a session to `runtime`.
    pub fn new(runtime: &'a mut R) -> Self {
        Self {
            runtime,
            started: Vec::new(),
        }
    }

    /// Starts an agent and takes ownership of its teardown.
    pub fn start(&mut self, source: &str) -> Result<AgentId, HarnessError> {
        let agent = self.runtime.start(source)?;
        self.started.push(agent);
        Ok(agent)
    }

    /// Broadcasts to every started agent.
    pub fn broadcast(&mut self, payload: &str) -> Result<(), HarnessError> {
        self.runtime.broadcast(payload)
    }

    /// Drains pending reports in arrival order.
    pub fn drain_reports(&mut self) -> Result<Vec<AgentReport>, HarnessError> {
        self.runtime.drain_reports()
    }

    /// The agents this session still owns, in start order.
    #[must_use]
    pub fn live(&self) -> &[AgentId] {
        &self.started
    }
}

impl<R: AgentRuntime> Drop for AgentSession<'_, R> {
    fn drop(&mut self) {
        while let Some(agent) = self.started.pop() {
            self.runtime.terminate(agent);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::path::PathBuf;

    use super::super::test262::{
        ComposedScript, ExecutionMode, ExecutionVariant, Negative, SourceKind, parse_test,
        plan_execution,
    };
    use super::*;

    const DEADLINE: Duration = Duration::from_millis(500);

    fn at(millis: u64) -> Duration {
        Duration::from_millis(millis)
    }

    fn include(name: &str) -> ConfinedInclude {
        ConfinedInclude {
            requested: name.to_owned(),
            confined: PathBuf::from("/harness").join(name),
        }
    }

    struct RecordingLoader {
        loaded: RefCell<Vec<String>>,
        missing: Option<String>,
    }

    impl RecordingLoader {
        fn new() -> Self {
            Self {
                loaded: RefCell::new(Vec::new()),
                missing: None,
            }
        }

        fn missing(name: &str) -> Self {
            Self {
                loaded: RefCell::new(Vec::new()),
                missing: Some(name.to_owned()),
            }
        }
    }

    impl HarnessLoader for RecordingLoader {
        fn load(&self, include: &ConfinedInclude) -> Result<Vec<u8>, HarnessError> {
            if self.missing.as_deref() == Some(include.requested.as_str()) {
                return Err(HarnessError::Include {
                    requested: include.requested.clone(),
                    detail: "absent".to_owned(),
                });
            }
            self.loaded.borrow_mut().push(include.requested.clone());
            Ok(format!("// {}\n", include.requested).into_bytes())
        }
    }

    #[derive(Default)]
    struct FakeAgents {
        next: usize,
        started: Vec<AgentId>,
        terminated: Vec<AgentId>,
    }

    impl AgentRuntime for FakeAgents {
        fn start(&mut self, _source: &str) -> Result<AgentId, HarnessError> {
            self.next += 1;
            let agent = AgentId(self.next);
            self.started.push(agent);
            Ok(agent)
        }

        fn broadcast(&mut self, _payload: &str) -> Result<(), HarnessError> {
            Ok(())
        }

        fn drain_reports(&mut self) -> Result<Vec<AgentReport>, HarnessError> {
            Ok(vec![AgentReport::new("Test262:AsyncTestComplete")])
        }

        fn terminate(&mut self, agent: AgentId) {
            self.terminated.push(agent);
        }
    }

    fn request(negative: Option<Negative>) -> RunRequest {
        RunRequest {
            mode: ExecutionMode::Interpreter,
            variant: ExecutionVariant {
                kind: SourceKind::ScriptNonStrict,
            },
            script: ComposedScript {
                bytes: b"var x = 1;".to_vec(),
                test_offset: 0,
                kind: SourceKind::ScriptNonStrict,
                untouched: true,
            },
            negative,
            async_done: false,
            can_block: true,
            deadline: DEADLINE,
        }
    }

    // -- async `$DONE` ------------------------------------------------------

    #[test]
    fn done_without_argument_completes() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::None, at(10)).unwrap();

        assert_eq!(recorder.judge(at(20)), Ok(()));
        assert_eq!(terminal_state(&recorder.judge(at(20))), TerminalState::Pass);
    }

    #[test]
    fn done_with_explicit_undefined_completes() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::Undefined, at(10)).unwrap();

        assert_eq!(recorder.judge(at(20)), Ok(()));
    }

    #[test]
    fn done_with_argument_fails_with_the_exact_stringified_value() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder
            .call(DoneArgument::Value("Test262Error: expected 1"), at(10))
            .unwrap();

        assert_eq!(
            recorder.judge(at(20)),
            Err(HarnessError::DoneFailed {
                value: "Test262Error: expected 1".to_owned(),
            })
        );
    }

    #[test]
    fn a_recorded_failure_trace_carries_the_value_for_negative_matching() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder
            .call(DoneArgument::Value("TypeError: nope"), at(10))
            .unwrap();
        assert_eq!(
            recorder.trace().failure_value,
            Some("TypeError: nope".to_owned())
        );

        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::None, at(10)).unwrap();
        assert_eq!(recorder.trace().failure_value, None);
    }

    #[test]
    fn done_argument_that_stringifies_to_undefined_still_fails() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder
            .call(DoneArgument::Value("undefined"), at(10))
            .unwrap();

        assert_eq!(
            recorder.judge(at(20)),
            Err(HarnessError::DoneFailed {
                value: "undefined".to_owned(),
            })
        );
    }

    #[test]
    fn duplicate_done_is_an_error_and_the_first_call_wins() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::None, at(10)).unwrap();

        let duplicate = recorder.call(DoneArgument::Value("late failure"), at(20));

        assert_eq!(
            duplicate,
            Err(HarnessError::Oracle(OracleError::Done(
                DoneFailure::Duplicate
            )))
        );
        let first = recorder.first_call().expect("first call is retained");
        assert_eq!(first.kind, DoneEventKind::Success);
        assert_eq!(first.at, at(10));
        assert_eq!(first.value, None);
        assert_eq!(
            recorder.judge(at(30)),
            Err(HarnessError::Oracle(OracleError::Done(
                DoneFailure::Duplicate
            )))
        );
    }

    #[test]
    fn a_second_successful_done_is_still_a_duplicate() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::None, at(5)).unwrap();

        assert!(recorder.call(DoneArgument::None, at(6)).is_err());
        assert!(recorder.judge(at(10)).is_err());
    }

    #[test]
    fn elapsed_deadline_without_any_done_is_a_typed_timeout() {
        let recorder = DoneRecorder::new(DEADLINE);

        assert_eq!(
            recorder.judge(DEADLINE),
            Err(HarnessError::Timeout { deadline: DEADLINE })
        );
        assert_eq!(
            terminal_state(&recorder.judge(DEADLINE)),
            TerminalState::Blocking
        );
    }

    #[test]
    fn a_done_call_past_the_deadline_is_late_not_a_pass() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.call(DoneArgument::None, at(900)).unwrap();

        assert_eq!(
            recorder.judge(at(900)),
            Err(HarnessError::Oracle(OracleError::Done(DoneFailure::Late)))
        );
    }

    #[test]
    fn exiting_before_any_done_is_an_early_exit() {
        let mut recorder = DoneRecorder::new(DEADLINE);
        recorder.record_exit(at(5));

        assert_eq!(
            recorder.judge(at(5)),
            Err(HarnessError::Oracle(OracleError::Done(
                DoneFailure::EarlyExit
            )))
        );
    }

    // -- include loading ----------------------------------------------------

    #[test]
    fn includes_load_in_declared_order_with_canonical_files_first() {
        let parsed = parse_test(
            "/*---\nflags: [async]\nincludes: [compareArray.js, propertyHelper.js]\n---*/\n",
        )
        .unwrap();
        let plan = plan_execution(&parsed.frontmatter, &PathBuf::from("/harness")).unwrap();
        let loader = RecordingLoader::new();

        let sources = load_harness_sources(&plan, &loader).unwrap();

        let expected = [
            "assert.js",
            "sta.js",
            "doneprintHandle.js",
            "compareArray.js",
            "propertyHelper.js",
        ];
        assert_eq!(
            sources.iter().map(|s| s.name.as_str()).collect::<Vec<_>>(),
            expected
        );
        assert_eq!(loader.loaded.borrow().as_slice(), expected);
        assert_eq!(sources[0].bytes, b"// assert.js\n");
    }

    #[test]
    fn a_missing_include_blocks_instead_of_shortening_the_prefix() {
        let parsed = parse_test("/*---\nincludes: [compareArray.js]\n---*/\n").unwrap();
        let plan = plan_execution(&parsed.frontmatter, &PathBuf::from("/harness")).unwrap();
        let loader = RecordingLoader::missing("compareArray.js");

        assert_eq!(
            load_harness_sources(&plan, &loader),
            Err(HarnessError::Include {
                requested: "compareArray.js".to_owned(),
                detail: "absent".to_owned(),
            })
        );
    }

    #[test]
    fn a_raw_plan_loads_no_harness() {
        let parsed = parse_test("/*---\nflags: [raw]\n---*/\n").unwrap();
        let plan = plan_execution(&parsed.frontmatter, &PathBuf::from("/harness")).unwrap();
        let loader = RecordingLoader::new();

        assert_eq!(load_harness_sources(&plan, &loader).unwrap(), Vec::new());
        assert!(loader.loaded.borrow().is_empty());
    }

    #[test]
    fn the_file_loader_reports_the_requested_name_when_absent() {
        let error = FileHarnessLoader
            .load(&include("definitely-absent.js"))
            .expect_err("an absent include cannot load");

        let HarnessError::Include { requested, .. } = error else {
            panic!("an unreadable include must be an include failure");
        };
        assert_eq!(requested, "definitely-absent.js");
    }

    // -- negative phases ----------------------------------------------------

    #[test]
    fn stages_map_onto_test262_phases() {
        assert_eq!(Stage::Compile.phase(), NegativePhase::Parse);
        assert_eq!(Stage::Instantiate.phase(), NegativePhase::Resolution);
        assert_eq!(Stage::Execute.phase(), NegativePhase::Runtime);
    }

    #[test]
    fn a_matching_negative_phase_and_type_passes() {
        let request = request(Some(Negative {
            phase: NegativePhase::Parse,
            error_type: NegativeType::SyntaxError,
        }));

        assert_eq!(
            judge_stage_outcome(&request, Some((Stage::Compile, NegativeType::SyntaxError))),
            Ok(())
        );
    }

    #[test]
    fn a_runtime_throw_never_satisfies_a_parse_expectation() {
        let request = request(Some(Negative {
            phase: NegativePhase::Parse,
            error_type: NegativeType::SyntaxError,
        }));

        let result =
            judge_stage_outcome(&request, Some((Stage::Execute, NegativeType::SyntaxError)));

        assert!(matches!(
            result,
            Err(HarnessError::Oracle(
                OracleError::ExpectationMismatch { .. }
            ))
        ));
        assert_eq!(terminal_state(&result), TerminalState::Blocking);
    }

    #[test]
    fn a_wrong_error_type_in_the_right_phase_still_blocks() {
        let request = request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::TypeError,
        }));

        assert!(matches!(
            judge_stage_outcome(&request, Some((Stage::Execute, NegativeType::RangeError))),
            Err(HarnessError::Oracle(
                OracleError::ExpectationMismatch { .. }
            ))
        ));
    }

    #[test]
    fn an_unexpected_success_on_a_negative_test_blocks() {
        let request = request(Some(Negative {
            phase: NegativePhase::Runtime,
            error_type: NegativeType::TypeError,
        }));

        assert!(matches!(
            judge_stage_outcome(&request, None),
            Err(HarnessError::Oracle(
                OracleError::ExpectationMismatch { .. }
            ))
        ));
    }

    #[test]
    fn an_unexpected_throw_on_a_positive_test_blocks() {
        assert!(matches!(
            judge_stage_outcome(
                &request(None),
                Some((Stage::Execute, NegativeType::TypeError))
            ),
            Err(HarnessError::Oracle(
                OracleError::ExpectationMismatch { .. }
            ))
        ));
    }

    #[test]
    fn a_clean_positive_run_passes() {
        assert_eq!(judge_stage_outcome(&request(None), None), Ok(()));
    }

    // -- agents -------------------------------------------------------------

    #[test]
    fn the_real_agent_runtime_fails_closed_on_every_hook() {
        let mut runtime = UnsupportedAgents;

        assert_eq!(
            runtime.start("$262.agent.report(1);"),
            Err(HarnessError::Unsupported {
                capability: Capability::AgentStart,
            })
        );
        assert_eq!(
            runtime.broadcast("0"),
            Err(HarnessError::Unsupported {
                capability: Capability::AgentBroadcast,
            })
        );
        assert_eq!(
            runtime.drain_reports(),
            Err(HarnessError::Unsupported {
                capability: Capability::AgentGetReport,
            })
        );
    }

    #[test]
    fn an_unsupported_agent_start_blocks_rather_than_passing() {
        let mut runtime = UnsupportedAgents;
        let mut session = AgentSession::new(&mut runtime);

        let result = session.start("$262.agent.report(1);").map(|_| ());

        assert_eq!(terminal_state(&result), TerminalState::Blocking);
        assert!(session.live().is_empty());
    }

    #[test]
    fn unsupported_capabilities_name_their_262_member() {
        assert_eq!(Capability::CreateRealm.as_str(), "$262.createRealm");
        assert_eq!(Capability::AgentSleep.as_str(), "$262.agent.sleep");
    }

    #[test]
    fn dropping_a_session_terminates_every_agent_in_reverse_start_order() {
        let mut runtime = FakeAgents::default();
        {
            let mut session = AgentSession::new(&mut runtime);
            session.start("first").unwrap();
            session.start("second").unwrap();
            assert_eq!(session.live(), [AgentId(1), AgentId(2)]);
        }

        assert_eq!(runtime.started, [AgentId(1), AgentId(2)]);
        assert_eq!(runtime.terminated, [AgentId(2), AgentId(1)]);
    }

    #[test]
    fn an_early_return_still_tears_down_started_agents() {
        let mut runtime = FakeAgents::default();
        let result = (|| -> Result<(), HarnessError> {
            let mut session = AgentSession::new(&mut runtime);
            session.start("first")?;
            Err(HarnessError::Timeout { deadline: DEADLINE })
        })();

        assert!(result.is_err());
        assert_eq!(runtime.terminated, [AgentId(1)]);
    }

    #[test]
    fn report_text_is_opaque_and_cannot_mint_a_verdict() {
        let mut runtime = FakeAgents::default();
        let reports = {
            let mut session = AgentSession::new(&mut runtime);
            session.start("agent").unwrap();
            session.drain_reports().unwrap()
        };

        // The report carries the canonical async-completion string, yet the
        // only pass in this module comes from `$DONE` accounting.
        assert_eq!(reports[0].as_str(), "Test262:AsyncTestComplete");
        let recorder = DoneRecorder::new(DEADLINE);
        assert_eq!(
            recorder.judge(DEADLINE),
            Err(HarnessError::Timeout { deadline: DEADLINE })
        );
        assert_eq!(runtime.terminated, [AgentId(1)]);
    }
}
