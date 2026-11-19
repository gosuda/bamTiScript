//! Shared oracle framework: path policy, normalization, process boundary, and
//! authority probes.
//!
//! Leaves add disjoint oracle modules under this directory. This file owns the
//! closed policy types and the bounded process adapter that reuses the corpus
//! runner rather than spawning an unpinned tool from `PATH`.

pub mod test262;
pub mod test262_harness;
pub mod tsc;

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    ErrorCode, Result, VerificationError,
    corpus::{self, OracleLimits, OracleOutcome},
    schema::sha256_hex,
};

/// How virtual paths are confined when materializing a project.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathPolicy {
    /// Relative paths only. Rejects escape, duplicates, and case-fold collisions.
    ConfinedRelative {
        /// ASCII case-fold collisions are rejected even on case-sensitive hosts.
        case_fold: CaseFoldPolicy,
    },
}

impl PathPolicy {
    /// The TypeScript-oracle path policy: confined relatives, fold collisions fail.
    #[must_use]
    pub const fn typescript_oracle() -> Self {
        Self::ConfinedRelative {
            case_fold: CaseFoldPolicy::RejectFoldCollisions,
        }
    }
}

/// Case-folding rule applied while checking virtual-path uniqueness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseFoldPolicy {
    /// `Foo.ts` and `foo.ts` are the same path and cannot both be materialized.
    RejectFoldCollisions,
}

/// Whether comparison is allowed to treat two observations as equivalent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalizationPolicy {
    /// Comparison is a blocking receipt: no policy was declared for the cell.
    Undeclared,
    /// Explicit environment and path normalization for both sides.
    Declared(DeclaredNormalization),
}

/// The declared environment and path comparison rules for a logical cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclaredNormalization {
    /// Environment isolation applied to both oracle and candidate.
    pub environment: EnvironmentNormalization,
    /// Path identity used when comparing artifacts and diagnostic files.
    pub paths: PathNormalization,
}

impl DeclaredNormalization {
    /// Corpus-pinned environment and virtual-relative path identity.
    #[must_use]
    pub const fn corpus_virtual() -> Self {
        Self {
            environment: EnvironmentNormalization::CorpusPinned,
            paths: PathNormalization::VirtualRelative,
        }
    }
}

/// Environment isolation applied to an oracle process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvironmentNormalization {
    /// Exactly `TZ=UTC`, `LANG=C`, `LC_ALL=C`, `NO_COLOR=1`; parent env is cleared.
    CorpusPinned,
}

/// Path identity used when comparing declared artifacts and diagnostic files.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathNormalization {
    /// Compare using confined virtual relative paths, never host absolute paths.
    VirtualRelative,
}

/// Algorithm used for oracle binary and artifact digests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigestAlgorithm {
    /// SHA-256, encoded as lowercase hex.
    Sha256,
}

/// Closed terminal state for an oracle receipt. Failures cannot become `Pass`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminalState {
    /// Both sides completed and every declared observable matched.
    Pass,
    /// Timeout, signal, truncation, protocol error, or mismatch.
    Blocking,
}

/// Version and digest reported by an injected authority probe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorityReport {
    /// Exact version string, for example `7.0.2`.
    pub version: String,
    /// Lowercase hex digest of the oracle binary.
    pub digest: String,
    /// Digest algorithm used for [`Self::digest`].
    pub algorithm: DigestAlgorithm,
}

/// Supplies the version and digest the constructor pins against.
pub trait AuthorityProbe {
    /// Reads identity from the injected authority. Must not search `PATH`.
    fn report(&self) -> Result<AuthorityReport>;
}

/// A probe that returns a caller-supplied identity. Used by unit tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReportedAuthority {
    /// Version string the constructor will check.
    pub version: String,
    /// Hex digest the constructor will check.
    pub digest: String,
}

impl AuthorityProbe for ReportedAuthority {
    fn report(&self) -> Result<AuthorityReport> {
        Ok(AuthorityReport {
            version: self.version.clone(),
            digest: self.digest.clone(),
            algorithm: DigestAlgorithm::Sha256,
        })
    }
}

/// Hashes an explicit oracle binary. Never searches `PATH`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashedFileProbe {
    version: String,
    digest: String,
}

impl HashedFileProbe {
    /// Hashes `binary` and records `version` as the reported identity.
    pub fn hash_file(binary: &Path, version: impl Into<String>) -> Result<Self> {
        let bytes = fs::read(binary).map_err(|error| {
            VerificationError::new(
                ErrorCode::Io,
                format!("cannot read oracle binary `{}`: {error}", binary.display()),
            )
        })?;
        Ok(Self {
            version: version.into(),
            digest: sha256_hex(&bytes),
        })
    }
}

impl AuthorityProbe for HashedFileProbe {
    fn report(&self) -> Result<AuthorityReport> {
        Ok(AuthorityReport {
            version: self.version.clone(),
            digest: self.digest.clone(),
            algorithm: DigestAlgorithm::Sha256,
        })
    }
}

/// Opt-in live probe for a pinned binary.
///
/// Returns `Ok(None)` unless `BAMTS_STABLE_TSC` names an explicit binary. Unit
/// tests leave the variable unset and never require a real 7.0.2 install.
pub fn env_stable_oracle_probe() -> Result<Option<HashedFileProbe>> {
    let Some(path) = env::var_os("BAMTS_STABLE_TSC") else {
        return Ok(None);
    };
    if path.is_empty() {
        return Ok(None);
    }
    let version = env::var("BAMTS_STABLE_TSC_VERSION").unwrap_or_else(|_| "7.0.2".to_owned());
    HashedFileProbe::hash_file(Path::new(&path), version).map(Some)
}

/// One bounded process invocation: program, argv, cwd, env, and limits.
#[derive(Debug, Clone)]
pub struct ProcessInvocation {
    /// Executable path. Injected; never discovered from an unpinned `tsc` on `PATH`.
    pub program: PathBuf,
    /// Exact argument vector after the program name.
    pub argv: Vec<OsString>,
    /// Working directory for the child.
    pub cwd: PathBuf,
    /// Isolated environment entries (`KEY=VALUE` already split).
    pub environment: Vec<(String, String)>,
    /// Timeout and output-byte ceiling.
    pub limits: OracleLimits,
}

/// Spawns a child under timeout and output bounds.
pub trait ProcessBoundary: Send + Sync {
    /// Runs `invocation` and returns the captured outcome.
    fn invoke(&self, invocation: &ProcessInvocation) -> Result<OracleOutcome>;
}

/// Production boundary: the corpus bounded runner.
#[derive(Debug, Clone, Copy, Default)]
pub struct CorpusProcessBoundary;

impl ProcessBoundary for CorpusProcessBoundary {
    fn invoke(&self, invocation: &ProcessInvocation) -> Result<OracleOutcome> {
        corpus::run_process(
            "TypeScript oracle",
            &invocation.program,
            &invocation.cwd,
            &invocation.environment,
            &invocation.argv,
            &invocation.limits,
        )
    }
}

/// Corpus-pinned environment pairs, in declaration order.
#[must_use]
pub fn pinned_environment() -> Vec<(String, String)> {
    corpus::NORMALIZED_ENV
        .iter()
        .map(|entry| {
            let (key, value) = entry
                .split_once('=')
                .expect("corpus NORMALIZED_ENV entries are KEY=VALUE");
            (key.to_owned(), value.to_owned())
        })
        .collect()
}

/// Shared constructor helper for an `Arc` process boundary.
#[must_use]
pub fn shared_process(boundary: impl ProcessBoundary + 'static) -> Arc<dyn ProcessBoundary> {
    Arc::new(boundary)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_stable_oracle_probe_is_opt_in() {
        assert!(env_stable_oracle_probe().expect("probe lookup").is_none());
    }
}
