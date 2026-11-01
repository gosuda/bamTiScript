pub mod authority;
pub mod catalog;
pub mod check_cells;
pub mod classification;
pub mod completion;
pub mod corpus;
pub mod diagnostic_catalog;
pub mod evidence;
pub mod facets;
pub mod fixtures;
pub mod formal_bridge;
pub mod formal_gates;
#[cfg(unix)]
pub mod jit_runner;
pub mod lane;
pub mod leaf_evidence;
pub mod ledger;
#[path = "../../../formal/ledger_wiring.rs"]
pub mod ledger_wiring;
pub mod oracle_pins;
pub mod oracles;
pub mod perf;
pub mod perf_guard;
pub mod perf_jit;
pub mod perf_stage0;
pub mod rebuild;
pub(crate) mod schema;
pub mod shard;
pub mod source_fetch;
pub mod suite;
pub mod sweep_report;
pub mod toolchain_schema;
pub mod ts_ledger;
pub mod unicode;
pub mod workspace_guard;

use std::fmt;

pub type Result<T, E = VerificationError> = std::result::Result<T, E>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Gate {
    G0,
    G1,
    G2,
    G3,
    G4,
    G5,
    G6,
}

impl Gate {
    pub const FORMAL_ORDER: [Self; 6] =
        [Self::G1, Self::G2, Self::G5, Self::G3, Self::G4, Self::G6];

    pub fn parse(value: &str) -> Result<Self> {
        match value {
            "G0" => Ok(Self::G0),
            "G1" => Ok(Self::G1),
            "G2" => Ok(Self::G2),
            "G3" => Ok(Self::G3),
            "G4" => Ok(Self::G4),
            "G5" => Ok(Self::G5),
            "G6" => Ok(Self::G6),
            _ => Err(VerificationError::new(
                ErrorCode::Usage,
                format!("unknown gate `{value}`"),
            )),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateReport {
    pub gate: Gate,
    pub checks: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    Usage,
    Io,
    Json,
    Toml,
    Schema,
    Digest,
    Duplicate,
    SetMismatch,
    Transition,
    Workspace,
    GateDependency,
    ToolMissing,
    ToolFailed,
    Replay,
    ProvenanceMismatch,
}

impl ErrorCode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Usage => "E_USAGE",
            Self::Io => "E_IO",
            Self::Json => "E_JSON",
            Self::Toml => "E_TOML",
            Self::Schema => "E_SCHEMA",
            Self::Digest => "E_DIGEST",
            Self::Duplicate => "E_DUPLICATE",
            Self::SetMismatch => "E_SET_MISMATCH",
            Self::Transition => "E_TRANSITION",
            Self::Workspace => "E_WORKSPACE",
            Self::GateDependency => "E_GATE_DEPENDENCY",
            Self::ToolMissing => "E_TOOL_MISSING",
            Self::ToolFailed => "E_TOOL_FAILED",
            Self::Replay => "E_REPLAY",
            Self::ProvenanceMismatch => "PROVENANCE_MISMATCH",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationError {
    code: ErrorCode,
    detail: String,
}

impl VerificationError {
    pub fn new(code: ErrorCode, detail: impl Into<String>) -> Self {
        Self {
            code,
            detail: detail.into(),
        }
    }

    pub const fn code(&self) -> ErrorCode {
        self.code
    }
}

impl fmt::Display for VerificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "bamts-verification: {}: {}",
            self.code.as_str(),
            self.detail
        )
    }
}

impl std::error::Error for VerificationError {}

#[cfg(test)]
mod tests {
    use super::ErrorCode;

    #[test]
    fn error_codes_have_stable_strings() {
        let cases = [
            (ErrorCode::Usage, "E_USAGE"),
            (ErrorCode::Io, "E_IO"),
            (ErrorCode::Json, "E_JSON"),
            (ErrorCode::Toml, "E_TOML"),
            (ErrorCode::Schema, "E_SCHEMA"),
            (ErrorCode::Digest, "E_DIGEST"),
            (ErrorCode::Duplicate, "E_DUPLICATE"),
            (ErrorCode::SetMismatch, "E_SET_MISMATCH"),
            (ErrorCode::Transition, "E_TRANSITION"),
            (ErrorCode::Workspace, "E_WORKSPACE"),
            (ErrorCode::GateDependency, "E_GATE_DEPENDENCY"),
            (ErrorCode::ToolMissing, "E_TOOL_MISSING"),
            (ErrorCode::ToolFailed, "E_TOOL_FAILED"),
            (ErrorCode::Replay, "E_REPLAY"),
            (ErrorCode::ProvenanceMismatch, "PROVENANCE_MISMATCH"),
        ];

        for (code, expected) in cases {
            assert_eq!(code.as_str(), expected);
        }
    }
}
