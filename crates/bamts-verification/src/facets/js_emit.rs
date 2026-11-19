use super::{FacetVerdict, compare_structural};
use crate::corpus::{CaseSpec, NodeOracle, OracleOutcome};
use crate::Result;

/// Line-wise comparator for `.js` emit baselines.
///
/// Newlines are normalized to `\n` and trailing spaces are stripped. Marker
/// order and code text stay source-order; emit is not a declaration set.
pub fn compare_js_emit(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("javascript", expected, actual, canonicalize_js_emit)
}

pub fn compare_declaration_emit(expected: &str, actual: &str) -> FacetVerdict {
    compare_structural("declaration", expected, actual, canonicalize_js_emit)
}

fn canonicalize_js_emit(text: &str) -> Result<Vec<String>, ()> {
    Ok(text
        .replace("\r\n", "\n")
        .replace('\r', "\n")
        .lines()
        .map(|line| line.trim_end().to_owned())
        .collect())
}

/// JS facet observation captured under a pinned, bounded [`NodeOracle`].
///
/// Raw [`OracleOutcome`] values are forgeable and therefore insufficient as a
/// public proof input. Construction goes through [`VerifiedJsOutcome::capture`],
/// which requires Node [`crate::corpus::NODE_VERSION`] verification plus case
/// timeout/output bounds enforced by the oracle runner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedJsOutcome {
    pub(super) outcome: OracleOutcome,
}

impl VerifiedJsOutcome {
    /// Runs `case` under `oracle` (pinned Node [`crate::corpus::NODE_VERSION`],
    /// bounded I/O).
    ///
    /// `NodeOracle::new` / `discover` already verify the pinned interpreter
    /// before `run_case` applies case timeout and output caps.
    pub fn capture(oracle: &NodeOracle, case: &CaseSpec) -> Result<Self> {
        Ok(Self {
            outcome: oracle.run_case(case)?,
        })
    }

    /// Borrows the captured oracle outcome for inspection.
    #[must_use]
    pub fn outcome(&self) -> &OracleOutcome {
        &self.outcome
    }
}

/// Behavioral `.js` comparator for oracle-proven outcomes.
///
/// Matching empty stdout cannot pass: the facet returns
/// [`FacetVerdict::Unproven`] so another owned facet must prove the case.
pub fn compare_js(expected: &VerifiedJsOutcome, actual: &VerifiedJsOutcome) -> FacetVerdict {
    compare_js_outcomes(expected.outcome(), actual.outcome())
}

/// Runs both programs under pinned [`NodeOracle`] instances, then compares
/// stdout bytes and exit code under the same parity key and limits as `corpus.rs`.
pub fn compare_js_cases(
    expected_oracle: &NodeOracle,
    expected_case: &CaseSpec,
    actual_oracle: &NodeOracle,
    actual_case: &CaseSpec,
) -> Result<FacetVerdict> {
    let expected = VerifiedJsOutcome::capture(expected_oracle, expected_case)?;
    let actual = VerifiedJsOutcome::capture(actual_oracle, actual_case)?;
    Ok(compare_js(&expected, &actual))
}

pub(super) fn compare_js_outcomes(expected: &OracleOutcome, actual: &OracleOutcome) -> FacetVerdict {
    if !expected.is_reliable() {
        return FacetVerdict::Fail {
            reason: "expected JS outcome is unreliable (timeout or truncated stdout)".to_owned(),
        };
    }
    if !actual.is_reliable() {
        return FacetVerdict::Fail {
            reason: "actual JS outcome is unreliable (timeout or truncated stdout)".to_owned(),
        };
    }

    if expected.exit_code != actual.exit_code {
        return FacetVerdict::Fail {
            reason: format!(
                "JS exit_code mismatch: expected {:?} actual {:?}",
                expected.exit_code, actual.exit_code
            ),
        };
    }

    if expected.stdout != actual.stdout {
        return FacetVerdict::Fail {
            reason: format!(
                "JS stdout mismatch: expected {} bytes actual {} bytes",
                expected.stdout.len(),
                actual.stdout.len()
            ),
        };
    }

    if expected.stdout.is_empty() {
        return FacetVerdict::Unproven {
            reason:
                "empty stdout cannot prove JS facet parity by itself; prove via another owned facet"
                    .to_owned(),
        };
    }

    FacetVerdict::Pass
}
