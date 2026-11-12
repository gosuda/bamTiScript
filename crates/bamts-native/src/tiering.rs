//! Tiering policy for the host JIT: warmup promotion, on-stack replacement
//! eligibility, and deoptimization accounting.
//!
//! The policy is a pure, deterministic state machine over saturating counters.
//! It owns no code memory and holds no pointers. Tier decisions select *which*
//! compiled artifact runs, while W^X mapping transitions stay in the host-JIT
//! memory provider (`bamts_codegen::jit_memory`) and its
//! `Writable -> Executable -> Freed` phases. Cancellation mirrors that one-way
//! discipline: a cancelled unit emits no further decisions, ever.

use crate::{
    CompletionTag, TRAP_INVALID_COMPLETION_TAG, TRAP_INVALID_FRAME, TRAP_INVALID_REGISTER,
    TRAP_MISSING_NATIVE_OPS, TRAP_PANIC,
};
use bamts_bytecode::Pc;

/// The execution tier of one function unit.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tier {
    /// The bytecode interpreter; every unit starts here.
    Interpreter,
    /// The directly lowered host-JIT code.
    Baseline,
    /// The recompiled hot artifact.
    Optimized,
}

/// Deterministic promotion thresholds and the deoptimization budget.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WarmupPolicy {
    /// Invocations before an interpreted unit promotes to [`Tier::Baseline`].
    pub baseline_invocations: u32,
    /// Invocations before a baseline unit promotes to [`Tier::Optimized`].
    pub optimized_invocations: u32,
    /// Loop back-edges before a running activation becomes OSR-eligible.
    pub osr_back_edges: u32,
    /// Deoptimizations tolerated before the unit is pinned to the interpreter.
    pub deopt_budget: u32,
}

impl WarmupPolicy {
    /// The shipped policy.
    pub const DEFAULT: WarmupPolicy = WarmupPolicy {
        baseline_invocations: 1,
        optimized_invocations: 1_000,
        osr_back_edges: 100,
        deopt_budget: 8,
    };
    /// The conformance policy: eager baseline with a short optimized fuse so
    /// the test262 JIT sweep exercises optimized code and loop-header entry.
    pub const STRESS: WarmupPolicy = WarmupPolicy {
        baseline_invocations: 1,
        optimized_invocations: 2,
        osr_back_edges: 2,
        deopt_budget: 8,
    };

    /// Rejects degenerate threshold orderings instead of running with them.
    ///
    /// Thresholds must be nonzero (a zero threshold would promote before any
    /// observation, making warmup a lie) and baseline must not exceed
    /// optimized (a unit cannot become hot before it is warm).
    pub const fn validated(self) -> Result<WarmupPolicy, TieringError> {
        if self.baseline_invocations == 0
            || self.optimized_invocations == 0
            || self.osr_back_edges == 0
            || self.deopt_budget == 0
        {
            return Err(TieringError::ZeroThreshold);
        }
        if self.baseline_invocations > self.optimized_invocations {
            return Err(TieringError::InvertedThresholds {
                baseline: self.baseline_invocations,
                optimized: self.optimized_invocations,
            });
        }
        Ok(self)
    }
}

/// One tier promotion decision.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TierTransition {
    /// The tier the unit leaves.
    pub from: Tier,
    /// The tier the unit enters.
    pub to: Tier,
}

/// One on-stack-replacement decision: enter compiled code at this bytecode pc.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OsrEntry {
    /// The loop-header pc the replacement activation resumes at.
    pub pc: Pc,
}

/// Why a native activation abandoned compiled code.
///
/// Only [`CompletionTag::FatalTrap`] deoptimizes. `Normal` and `Throw` are
/// ordinary completions (`Throw` routes through bytecode handlers), and
/// `Suspend` is the generator/async contract, so none of them indicts the
/// compiled artifact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeoptReason {
    /// The wrapper ran without an installed dispatcher.
    MissingNativeOps,
    /// The wrapper received an invalid frame pointer.
    InvalidFrame,
    /// The dispatcher panicked and was caught at the boundary.
    Panic,
    /// A helper received an out-of-range register index.
    InvalidRegister,
    /// A native entry returned an unrecognized completion tag.
    InvalidCompletionTag,
    /// A fatal trap whose record id this policy does not recognize. Kept
    /// distinct so an unknown failure still demotes loudly instead of being
    /// absorbed into a known bucket.
    UnknownTrap {
        /// The unrecognized trap record id.
        trap_id: u32,
    },
}

/// Classifies a native completion. `Some` exactly when the activation must
/// deoptimize; total over every tag, so no completion class is ever dropped.
///
/// Runtime note: [`DeoptReason::Panic`] is recorded (budget/pin still apply)
/// but the live engine does **not** reconstruct that activation — a panic
/// caught at the helper boundary may carry partial side effects, so
/// mid-function resume would be dishonest. All other reasons are pre-dispatch
/// validation traps and resume safely.
#[must_use]
pub const fn deopt_reason(tag: CompletionTag, trap_id: u32) -> Option<DeoptReason> {
    match tag {
        CompletionTag::Normal | CompletionTag::Throw | CompletionTag::Suspend => None,
        CompletionTag::FatalTrap => Some(match trap_id {
            TRAP_MISSING_NATIVE_OPS => DeoptReason::MissingNativeOps,
            TRAP_INVALID_FRAME => DeoptReason::InvalidFrame,
            TRAP_PANIC => DeoptReason::Panic,
            TRAP_INVALID_REGISTER => DeoptReason::InvalidRegister,
            TRAP_INVALID_COMPLETION_TAG => DeoptReason::InvalidCompletionTag,
            trap_id => DeoptReason::UnknownTrap { trap_id },
        }),
    }
}

/// A policy or contract violation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TieringError {
    /// A threshold of zero would decide before observing.
    ZeroThreshold,
    /// The baseline threshold exceeds the optimized threshold.
    InvertedThresholds {
        /// The offending baseline threshold.
        baseline: u32,
        /// The offending optimized threshold.
        optimized: u32,
    },
    /// A contract vector observed a decision that violates the policy.
    ContractViolation {
        /// The violated vector, by stable name.
        vector: &'static str,
    },
}

impl core::fmt::Display for TieringError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TieringError::ZeroThreshold => f.write_str("warmup thresholds must be nonzero"),
            TieringError::InvertedThresholds {
                baseline,
                optimized,
            } => write!(
                f,
                "baseline threshold {baseline} exceeds optimized threshold {optimized}"
            ),
            TieringError::ContractViolation { vector } => {
                write!(f, "tiering contract vector failed: {vector}")
            }
        }
    }
}

impl std::error::Error for TieringError {}

/// The tiering state of one function unit.
///
/// Counters saturate: a unit that ran `u32::MAX` times is exactly as hot as
/// one that ran once more, and wraparound must never demote by accident.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TieringState {
    policy: WarmupPolicy,
    tier: Tier,
    invocations: u32,
    back_edges: u32,
    deopts: u32,
    pinned: bool,
    cancelled: bool,
}

impl TieringState {
    /// A fresh interpreted unit under `policy`.
    ///
    /// Policy validation happens here, once, so every live state was
    /// constructed from a coherent policy.
    pub const fn new(policy: WarmupPolicy) -> Result<TieringState, TieringError> {
        let policy = match policy.validated() {
            Ok(policy) => policy,
            Err(error) => return Err(error),
        };
        Ok(TieringState {
            policy,
            tier: Tier::Interpreter,
            invocations: 0,
            back_edges: 0,
            deopts: 0,
            pinned: false,
            cancelled: false,
        })
    }

    /// The unit's current tier.
    #[must_use]
    pub const fn tier(&self) -> Tier {
        self.tier
    }

    /// Saturating invocation counter observed so far.
    #[must_use]
    pub const fn invocations(&self) -> u32 {
        self.invocations
    }

    /// Saturating taken-back-edge counter observed so far.
    #[must_use]
    pub const fn back_edges(&self) -> u32 {
        self.back_edges
    }

    /// Saturating deoptimization counter observed so far.
    #[must_use]
    pub const fn deopts(&self) -> u32 {
        self.deopts
    }

    /// True once the deopt budget is exhausted; a pinned unit never leaves
    /// the interpreter again.
    #[must_use]
    pub const fn is_pinned(&self) -> bool {
        self.pinned
    }

    /// True once [`TieringState::cancel`] ran.
    #[must_use]
    pub const fn is_cancelled(&self) -> bool {
        self.cancelled
    }

    /// Records one invocation; returns the promotion it triggers, if any.
    ///
    /// Promotion fires exactly when the counter reaches a threshold, so a
    /// policy of `n` observes `n` complete invocations before deciding.
    pub fn observe_invocation(&mut self) -> Option<TierTransition> {
        if self.cancelled || self.pinned {
            return None;
        }
        self.invocations = self.invocations.saturating_add(1);
        let to = match self.tier {
            Tier::Interpreter if self.invocations >= self.policy.baseline_invocations => {
                Tier::Baseline
            }
            Tier::Baseline if self.invocations >= self.policy.optimized_invocations => {
                Tier::Optimized
            }
            Tier::Interpreter | Tier::Baseline | Tier::Optimized => return None,
        };
        let from = self.tier;
        self.tier = to;
        Some(TierTransition { from, to })
    }

    /// Records one taken loop edge; returns an OSR decision when the running
    /// activation should transfer into compiled code at `target`.
    ///
    /// Only true back edges (`target <= current`) count: a forward branch is
    /// not a loop, and replacing an activation at a pc it has not reached
    /// would fabricate state. Interpreted-tier activations are the only OSR
    /// beneficiaries; compiled tiers are already native.
    pub fn observe_back_edge(&mut self, target: Pc, current: Pc) -> Option<OsrEntry> {
        if self.cancelled || self.pinned || target.get() > current.get() {
            return None;
        }
        self.back_edges = self.back_edges.saturating_add(1);
        if self.tier == Tier::Interpreter && self.back_edges >= self.policy.osr_back_edges {
            // Consume the accumulated heat: one OSR decision per warmup, so a
            // caller that ignores the decision must re-earn it.
            self.back_edges = 0;
            return Some(OsrEntry { pc: target });
        }
        None
    }

    /// Records one deoptimization: the unit re-enters the interpreter, its
    /// warmup restarts from cold, and once the budget is spent the unit is
    /// pinned there permanently.
    pub fn record_deopt(&mut self, _reason: DeoptReason) -> Tier {
        if self.cancelled {
            return self.tier;
        }
        self.tier = Tier::Interpreter;
        self.invocations = 0;
        self.back_edges = 0;
        self.deopts = self.deopts.saturating_add(1);
        if self.deopts >= self.policy.deopt_budget {
            self.pinned = true;
        }
        self.tier
    }

    /// Cancels the unit: every later observation and deopt is inert.
    ///
    /// One-way by design, mirroring the memory provider's `Freed` phase: a
    /// cancelled compilation must not race a fresh decision into existence.
    pub fn cancel(&mut self) {
        self.cancelled = true;
    }
}

/// The E2.2 contract vector: exercises the canonical policy decisions and
/// fails on the first violation. Input-free and deterministic.
pub fn verify_tiering_contract() -> Result<(), TieringError> {
    let policy = WarmupPolicy {
        baseline_invocations: 2,
        optimized_invocations: 4,
        osr_back_edges: 3,
        deopt_budget: 2,
    };
    let vector = |name: &'static str| TieringError::ContractViolation { vector: name };

    // Warmup: exact-threshold promotion through both tiers.
    let mut state = TieringState::new(policy)?;
    if state.observe_invocation().is_some() {
        return Err(vector("no promotion before the baseline threshold"));
    }
    if state.observe_invocation()
        != Some(TierTransition {
            from: Tier::Interpreter,
            to: Tier::Baseline,
        })
    {
        return Err(vector("promotion at exactly the baseline threshold"));
    }
    if state.observe_invocation().is_some() {
        return Err(vector("no promotion between thresholds"));
    }
    if state.observe_invocation()
        != Some(TierTransition {
            from: Tier::Baseline,
            to: Tier::Optimized,
        })
    {
        return Err(vector("promotion at exactly the optimized threshold"));
    }
    if state.observe_invocation().is_some() {
        return Err(vector("no promotion past the top tier"));
    }

    // OSR: three interpreted back edges earn one entry; forward edges never do.
    let mut state = TieringState::new(policy)?;
    let header = Pc::new(1);
    let latch = Pc::new(9);
    if state.observe_back_edge(latch, header).is_some() {
        return Err(vector("a forward edge is never OSR-eligible"));
    }
    if state.observe_back_edge(header, latch).is_some()
        || state.observe_back_edge(header, latch).is_some()
    {
        return Err(vector("no OSR before the back-edge threshold"));
    }
    if state.observe_back_edge(header, latch) != Some(OsrEntry { pc: header }) {
        return Err(vector("OSR at exactly the back-edge threshold"));
    }
    if state.observe_back_edge(header, latch).is_some() {
        return Err(vector("OSR heat is consumed by the decision"));
    }

    // Deopt: demotion, budget exhaustion, and pin permanence.
    let mut state = TieringState::new(policy)?;
    state.observe_invocation();
    state.observe_invocation();
    if state.tier() != Tier::Baseline {
        return Err(vector("warmup precedes the deopt vector"));
    }
    if state.record_deopt(DeoptReason::Panic) != Tier::Interpreter {
        return Err(vector("deopt demotes to the interpreter"));
    }
    if state.is_pinned() {
        return Err(vector("no pin while budget remains"));
    }
    if state.record_deopt(DeoptReason::InvalidRegister) != Tier::Interpreter || !state.is_pinned() {
        return Err(vector("budget exhaustion pins the unit"));
    }
    for _ in 0..policy.optimized_invocations {
        if state.observe_invocation().is_some() {
            return Err(vector("a pinned unit never re-promotes"));
        }
    }

    // Cancellation: one-way terminality.
    let mut state = TieringState::new(policy)?;
    state.cancel();
    if state.observe_invocation().is_some()
        || state.observe_back_edge(header, latch).is_some()
        || state.record_deopt(DeoptReason::Panic) != Tier::Interpreter
        || state.is_pinned()
    {
        return Err(vector("a cancelled unit emits no decisions"));
    }

    // Completion classification: totality over the tag algebra.
    if deopt_reason(CompletionTag::Normal, 0).is_some()
        || deopt_reason(CompletionTag::Throw, 0).is_some()
        || deopt_reason(CompletionTag::Suspend, 0).is_some()
    {
        return Err(vector("only fatal traps deoptimize"));
    }
    if deopt_reason(CompletionTag::FatalTrap, TRAP_PANIC) != Some(DeoptReason::Panic) {
        return Err(vector("known trap ids classify precisely"));
    }
    if deopt_reason(CompletionTag::FatalTrap, 0xdead)
        != Some(DeoptReason::UnknownTrap { trap_id: 0xdead })
    {
        return Err(vector("unknown trap ids still deoptimize"));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tight_policy() -> WarmupPolicy {
        WarmupPolicy {
            baseline_invocations: 3,
            optimized_invocations: 5,
            osr_back_edges: 2,
            deopt_budget: 1,
        }
    }

    #[test]
    fn contract_vector_passes() {
        assert_eq!(verify_tiering_contract(), Ok(()));
    }

    #[test]
    fn default_policy_is_valid() {
        assert_eq!(WarmupPolicy::DEFAULT.validated(), Ok(WarmupPolicy::DEFAULT));
    }

    #[test]
    fn zero_thresholds_are_rejected() {
        for broken in [
            WarmupPolicy {
                baseline_invocations: 0,
                ..WarmupPolicy::DEFAULT
            },
            WarmupPolicy {
                optimized_invocations: 0,
                ..WarmupPolicy::DEFAULT
            },
            WarmupPolicy {
                osr_back_edges: 0,
                ..WarmupPolicy::DEFAULT
            },
            WarmupPolicy {
                deopt_budget: 0,
                ..WarmupPolicy::DEFAULT
            },
        ] {
            assert_eq!(broken.validated(), Err(TieringError::ZeroThreshold));
            assert!(TieringState::new(broken).is_err());
        }
    }

    #[test]
    fn inverted_thresholds_are_rejected() {
        let broken = WarmupPolicy {
            baseline_invocations: 9,
            optimized_invocations: 3,
            ..WarmupPolicy::DEFAULT
        };
        assert_eq!(
            broken.validated(),
            Err(TieringError::InvertedThresholds {
                baseline: 9,
                optimized: 3,
            })
        );
    }

    #[test]
    fn promotion_fires_at_exactly_the_threshold() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(
            state.observe_invocation(),
            Some(TierTransition {
                from: Tier::Interpreter,
                to: Tier::Baseline,
            })
        );
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(
            state.observe_invocation(),
            Some(TierTransition {
                from: Tier::Baseline,
                to: Tier::Optimized,
            })
        );
        assert_eq!(state.tier(), Tier::Optimized);
    }

    #[test]
    fn saturated_counters_never_wrap_or_demote() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        for _ in 0..5 {
            state.observe_invocation();
        }
        assert_eq!(state.tier(), Tier::Optimized);
        state.invocations = u32::MAX;
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(state.invocations, u32::MAX, "counter saturates");
        assert_eq!(state.tier(), Tier::Optimized, "saturation never demotes");
    }

    #[test]
    fn forward_edges_never_earn_osr() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        for _ in 0..64 {
            assert_eq!(state.observe_back_edge(Pc::new(8), Pc::new(2)), None);
        }
    }

    #[test]
    fn back_edge_threshold_is_exact_and_heat_is_consumed() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        let header = Pc::new(4);
        let latch = Pc::new(20);
        assert_eq!(state.observe_back_edge(header, latch), None);
        assert_eq!(
            state.observe_back_edge(header, latch),
            Some(OsrEntry { pc: header })
        );
        assert_eq!(
            state.observe_back_edge(header, latch),
            None,
            "the decision consumes the accumulated heat"
        );
    }

    #[test]
    fn self_loop_counts_as_a_back_edge() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        let pc = Pc::new(7);
        assert_eq!(state.observe_back_edge(pc, pc), None);
        assert_eq!(state.observe_back_edge(pc, pc), Some(OsrEntry { pc }));
    }

    #[test]
    fn compiled_tiers_do_not_request_osr() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        for _ in 0..3 {
            state.observe_invocation();
        }
        assert_eq!(state.tier(), Tier::Baseline);
        for _ in 0..8 {
            assert_eq!(state.observe_back_edge(Pc::new(1), Pc::new(9)), None);
        }
    }

    #[test]
    fn deopt_demotes_resets_warmup_and_pins_on_budget() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        for _ in 0..3 {
            state.observe_invocation();
        }
        assert_eq!(state.tier(), Tier::Baseline);
        // Budget is 1: the first deopt demotes *and* pins.
        assert_eq!(
            state.record_deopt(DeoptReason::MissingNativeOps),
            Tier::Interpreter
        );
        assert!(state.is_pinned());
        for _ in 0..64 {
            assert_eq!(state.observe_invocation(), None, "pinned units stay cold");
        }
        assert_eq!(state.tier(), Tier::Interpreter);
    }

    #[test]
    fn budget_larger_than_one_survives_early_deopts() {
        let policy = WarmupPolicy {
            deopt_budget: 3,
            ..tight_policy()
        };
        let mut state = TieringState::new(policy).expect("valid policy");
        state.record_deopt(DeoptReason::Panic);
        state.record_deopt(DeoptReason::Panic);
        assert!(!state.is_pinned());
        // Warmup restarted from cold: the unit can still re-promote.
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(state.observe_invocation(), None);
        assert_eq!(
            state.observe_invocation(),
            Some(TierTransition {
                from: Tier::Interpreter,
                to: Tier::Baseline,
            })
        );
        state.record_deopt(DeoptReason::Panic);
        assert!(state.is_pinned());
    }

    #[test]
    fn cancellation_is_terminal_for_every_observer() {
        let mut state = TieringState::new(tight_policy()).expect("valid policy");
        state.observe_invocation();
        state.cancel();
        assert!(state.is_cancelled());
        for _ in 0..8 {
            assert_eq!(state.observe_invocation(), None);
            assert_eq!(state.observe_back_edge(Pc::new(0), Pc::new(9)), None);
        }
        assert_eq!(state.record_deopt(DeoptReason::Panic), Tier::Interpreter);
        assert!(!state.is_pinned(), "a cancelled unit accrues no deopts");
    }

    #[test]
    fn every_completion_tag_is_classified() {
        assert_eq!(deopt_reason(CompletionTag::Normal, TRAP_PANIC), None);
        assert_eq!(deopt_reason(CompletionTag::Throw, TRAP_PANIC), None);
        assert_eq!(deopt_reason(CompletionTag::Suspend, TRAP_PANIC), None);
        for (trap_id, reason) in [
            (TRAP_MISSING_NATIVE_OPS, DeoptReason::MissingNativeOps),
            (TRAP_INVALID_FRAME, DeoptReason::InvalidFrame),
            (TRAP_PANIC, DeoptReason::Panic),
            (TRAP_INVALID_REGISTER, DeoptReason::InvalidRegister),
            (
                TRAP_INVALID_COMPLETION_TAG,
                DeoptReason::InvalidCompletionTag,
            ),
        ] {
            assert_eq!(
                deopt_reason(CompletionTag::FatalTrap, trap_id),
                Some(reason)
            );
        }
        assert_eq!(
            deopt_reason(CompletionTag::FatalTrap, 0xffff),
            Some(DeoptReason::UnknownTrap { trap_id: 0xffff })
        );
    }
}
