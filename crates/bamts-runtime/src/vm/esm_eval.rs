#![cfg(test)]
//! Pure policy for ECMAScript module evaluation.
//!
//! The runtime owns module records, promises, and binding cells. This module
//! only decides evaluation-state transitions; it never owns a second copy of
//! module state.

use crate::{ModuleState, RuntimeError, RuntimeErrorKind};

/// Non-owning classification of the runtime's module state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ModulePhase {
    Unevaluated,
    Evaluating,
    EvaluatingAsync,
    EvaluatedOk,
    EvaluatedErr,
}

impl From<&ModuleState> for ModulePhase {
    fn from(state: &ModuleState) -> Self {
        match state {
            ModuleState::Unevaluated => Self::Unevaluated,
            ModuleState::Evaluating => Self::Evaluating,
            ModuleState::EvaluatingAsync { .. } => Self::EvaluatingAsync,
            ModuleState::Evaluated(Ok(())) => Self::EvaluatedOk,
            ModuleState::Evaluated(Err(_)) => Self::EvaluatedErr,
        }
    }
}

/// One observable event delivered to the evaluation policy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModuleEvalEvent {
    Begin,
    DependencyCycle,
    DependencyPending,
    DependenciesScanned {
        pending: usize,
    },
    DependencyFailed(RuntimeError),
    /// A dependency reaction fired after the adapter decremented its count.
    DependencySettled {
        remaining: usize,
    },
    EntryReady,
    EntrySuspended,
    EntryCompleted(Result<(), RuntimeError>),
    AbortToUnevaluated,
}

/// Runtime work selected by [`module_eval_step`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModuleEvalEffect {
    Ignore,
    BeginDependencies,
    CycleReady,
    ReusePending,
    DependencyReady,
    AttachReaction,
    WaitForDependencies,
    StartEntry,
    ParkAsync,
    CacheSuccess,
    CacheFailure(RuntimeError),
    /// Propagate a fatal runtime failure without caching it.
    AbortRetry(RuntimeError),
    AbortRetryWithoutFailure,
}

/// The next state classification and the only side effect the adapter performs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModuleEvalDecision {
    pub(crate) next_phase: ModulePhase,
    pub(crate) effect: ModuleEvalEffect,
}

impl ModuleEvalDecision {
    const fn new(next_phase: ModulePhase, effect: ModuleEvalEffect) -> Self {
        Self { next_phase, effect }
    }
}

/// Selects one total module-evaluation transition.
///
/// Settled modules are absorbing: success is reused and failure remains cached.
/// A fatal (non-language-throw) entry failure instead returns to `Unevaluated`,
/// allowing a later attempt after capacity becomes available.
pub(crate) fn module_eval_step(phase: ModulePhase, event: ModuleEvalEvent) -> ModuleEvalDecision {
    use ModuleEvalEffect as Effect;
    use ModuleEvalEvent as Event;
    use ModulePhase as Phase;

    if matches!(phase, Phase::EvaluatedOk | Phase::EvaluatedErr) {
        return ModuleEvalDecision::new(phase, Effect::Ignore);
    }

    match (phase, event) {
        (Phase::Unevaluated, Event::Begin) => {
            ModuleEvalDecision::new(Phase::Evaluating, Effect::BeginDependencies)
        }
        (Phase::Evaluating, Event::Begin) => {
            ModuleEvalDecision::new(Phase::Evaluating, Effect::CycleReady)
        }
        (Phase::EvaluatingAsync, Event::Begin) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::ReusePending)
        }

        (Phase::Evaluating | Phase::EvaluatingAsync, Event::DependencyCycle) => {
            ModuleEvalDecision::new(phase, Effect::DependencyReady)
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::DependencyPending) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::AttachReaction)
        }
        (Phase::Evaluating, Event::DependenciesScanned { pending: 0 }) => {
            ModuleEvalDecision::new(Phase::Evaluating, Effect::StartEntry)
        }
        (Phase::Evaluating, Event::DependenciesScanned { pending: _ }) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::WaitForDependencies)
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::DependencyFailed(error))
            if matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }) =>
        {
            ModuleEvalDecision::new(Phase::EvaluatedErr, Effect::CacheFailure(error))
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::DependencyFailed(error)) => {
            ModuleEvalDecision::new(Phase::Unevaluated, Effect::AbortRetry(error))
        }
        (Phase::EvaluatingAsync, Event::DependencySettled { remaining: 0 }) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::StartEntry)
        }
        (Phase::EvaluatingAsync, Event::DependencySettled { remaining: _ }) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::WaitForDependencies)
        }

        (Phase::Evaluating | Phase::EvaluatingAsync, Event::EntryReady) => {
            ModuleEvalDecision::new(phase, Effect::StartEntry)
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::EntrySuspended) => {
            ModuleEvalDecision::new(Phase::EvaluatingAsync, Effect::ParkAsync)
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::EntryCompleted(Ok(()))) => {
            ModuleEvalDecision::new(Phase::EvaluatedOk, Effect::CacheSuccess)
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::EntryCompleted(Err(error)))
            if matches!(error.kind, RuntimeErrorKind::UncaughtThrow { .. }) =>
        {
            ModuleEvalDecision::new(Phase::EvaluatedErr, Effect::CacheFailure(error))
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::EntryCompleted(Err(error))) => {
            ModuleEvalDecision::new(Phase::Unevaluated, Effect::AbortRetry(error))
        }
        (Phase::Evaluating | Phase::EvaluatingAsync, Event::AbortToUnevaluated) => {
            ModuleEvalDecision::new(Phase::Unevaluated, Effect::AbortRetryWithoutFailure)
        }

        (phase, _) => ModuleEvalDecision::new(phase, Effect::Ignore),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bamts_bytecode::{FunctionId, Instruction, Pc};
    use bamts_native::Value;

    use crate::{RuntimeSource, ThrowOrigin};

    fn error(kind: RuntimeErrorKind) -> RuntimeError {
        RuntimeError {
            kind,
            function: FunctionId::new(0),
            pc: Pc::new(0),
            source: RuntimeSource {
                function_name: None,
                instruction: Instruction::Halt,
            },
        }
    }

    fn thrown() -> RuntimeError {
        error(RuntimeErrorKind::UncaughtThrow {
            value: Value::UNDEFINED,
            origin: ThrowOrigin::Bytecode,
            constructor_name: None,
            message: None,
        })
    }

    fn fatal() -> RuntimeError {
        error(RuntimeErrorKind::HeapSlotLimitExceeded { limit: 0 })
    }

    fn event(kind: usize) -> ModuleEvalEvent {
        match kind {
            0 => ModuleEvalEvent::Begin,
            1 => ModuleEvalEvent::DependencyCycle,
            2 => ModuleEvalEvent::DependencyPending,
            3 => ModuleEvalEvent::DependenciesScanned { pending: 1 },
            4 => ModuleEvalEvent::DependencyFailed(thrown()),
            5 => ModuleEvalEvent::DependencySettled { remaining: 1 },
            6 => ModuleEvalEvent::DependencySettled { remaining: 0 },
            7 => ModuleEvalEvent::EntryReady,
            8 => ModuleEvalEvent::EntrySuspended,
            9 => ModuleEvalEvent::EntryCompleted(Ok(())),
            10 => ModuleEvalEvent::EntryCompleted(Err(thrown())),
            11 => ModuleEvalEvent::EntryCompleted(Err(fatal())),
            12 => ModuleEvalEvent::AbortToUnevaluated,
            _ => unreachable!(),
        }
    }

    #[test]
    fn every_phase_event_pair_is_total_and_settled_states_are_absorbing() {
        let phases = [
            ModulePhase::Unevaluated,
            ModulePhase::Evaluating,
            ModulePhase::EvaluatingAsync,
            ModulePhase::EvaluatedOk,
            ModulePhase::EvaluatedErr,
        ];
        for phase in phases {
            for kind in 0..=12 {
                let decision = module_eval_step(phase, event(kind));
                if matches!(phase, ModulePhase::EvaluatedOk | ModulePhase::EvaluatedErr) {
                    assert_eq!(decision.next_phase, phase);
                    assert_eq!(decision.effect, ModuleEvalEffect::Ignore);
                }
            }
        }
    }

    #[test]
    fn transition_effects_cover_begin_dependencies_and_entry_events() {
        let cases = [
            (
                ModulePhase::Unevaluated,
                ModuleEvalEvent::Begin,
                ModulePhase::Evaluating,
                ModuleEvalEffect::BeginDependencies,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::Begin,
                ModulePhase::Evaluating,
                ModuleEvalEffect::CycleReady,
            ),
            (
                ModulePhase::EvaluatingAsync,
                ModuleEvalEvent::Begin,
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::ReusePending,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::DependencyCycle,
                ModulePhase::Evaluating,
                ModuleEvalEffect::DependencyReady,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::DependencyPending,
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::AttachReaction,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::DependenciesScanned { pending: 1 },
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::WaitForDependencies,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::DependenciesScanned { pending: 0 },
                ModulePhase::Evaluating,
                ModuleEvalEffect::StartEntry,
            ),
            (
                ModulePhase::EvaluatingAsync,
                ModuleEvalEvent::DependencySettled { remaining: 1 },
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::WaitForDependencies,
            ),
            (
                ModulePhase::EvaluatingAsync,
                ModuleEvalEvent::DependencySettled { remaining: 0 },
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::StartEntry,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::EntryReady,
                ModulePhase::Evaluating,
                ModuleEvalEffect::StartEntry,
            ),
            (
                ModulePhase::Evaluating,
                ModuleEvalEvent::EntrySuspended,
                ModulePhase::EvaluatingAsync,
                ModuleEvalEffect::ParkAsync,
            ),
        ];
        for (phase, event, next_phase, effect) in cases {
            assert_eq!(
                module_eval_step(phase, event),
                ModuleEvalDecision::new(next_phase, effect)
            );
        }
    }

    #[test]
    fn rejection_is_cached_and_entry_never_starts() {
        let failure = thrown();
        let decision = module_eval_step(
            ModulePhase::EvaluatingAsync,
            ModuleEvalEvent::DependencyFailed(failure.clone()),
        );
        assert_eq!(decision.next_phase, ModulePhase::EvaluatedErr);
        assert_eq!(decision.effect, ModuleEvalEffect::CacheFailure(failure));
        assert!(!matches!(decision.effect, ModuleEvalEffect::StartEntry));

        let cached = module_eval_step(ModulePhase::EvaluatedErr, ModuleEvalEvent::Begin);
        assert_eq!(cached.next_phase, ModulePhase::EvaluatedErr);
        assert_eq!(cached.effect, ModuleEvalEffect::Ignore);
    }

    #[test]
    fn language_throw_caches_but_fatal_abort_retries() {
        let rejected = module_eval_step(
            ModulePhase::Evaluating,
            ModuleEvalEvent::EntryCompleted(Err(thrown())),
        );
        assert_eq!(rejected.next_phase, ModulePhase::EvaluatedErr);
        assert!(matches!(rejected.effect, ModuleEvalEffect::CacheFailure(_)));

        let aborted = module_eval_step(
            ModulePhase::EvaluatingAsync,
            ModuleEvalEvent::EntryCompleted(Err(fatal())),
        );
        assert_eq!(aborted.next_phase, ModulePhase::Unevaluated);
        assert!(matches!(aborted.effect, ModuleEvalEffect::AbortRetry(_)));
        assert_eq!(
            module_eval_step(aborted.next_phase, ModuleEvalEvent::Begin).effect,
            ModuleEvalEffect::BeginDependencies
        );
    }
}
