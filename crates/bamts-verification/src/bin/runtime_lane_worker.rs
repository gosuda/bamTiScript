//! Runtime lane worker for the test262 catalog.
//!
//! Reads a [`LaneRequest`] from `BAMTS_LANE_WORKER_REQUEST`, resolves the
//! test262 source file from the obligation key's `case` path relative to the
//! authority root (`target/authority/test262`), parses frontmatter, plans
//! execution, loads harness includes, and evaluates the test in the single
//! mode named by the key's `mode` field (`interpreter` / `jit` / `aot`).
//!
//! The worker never mints `PASS`; it returns [`LaneOutcome::Completed`] when
//! every variant judged clean, [`LaneOutcome::BlockingFail`] with the first
//! failing assertion or thrown value, [`LaneOutcome::Timeout`] when the
//! deadline expired, or [`LaneOutcome::InapplicableOutOfScopeHostFeature`]
//! when the test requests a capability this engine does not provide.

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Duration,
};

use bamts_verification::{
    ErrorCode, Result, VerificationError,
    lane::{LANE_WORKER_REQUEST, LaneOutcome, LaneRequest, LaneResponse},
    oracles::{
        test262::{self, ExecutionMode, OracleError, backend_runner, evaluate_in_mode},
        test262_harness::{FileHarnessLoader, load_harness_sources},
    },
    shard::ExecutionMode as ShardExecutionMode,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("runtime_lane_worker: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let request_path = env::var_os(LANE_WORKER_REQUEST).ok_or_else(|| {
        VerificationError::new(
            ErrorCode::Usage,
            format!("{LANE_WORKER_REQUEST} is not set"),
        )
    })?;
    let request_path = PathBuf::from(request_path);
    let request_bytes = fs::read(&request_path).map_err(|error| {
        VerificationError::new(
            ErrorCode::Io,
            format!("{}: {error}", request_path.display()),
        )
    })?;
    let request: LaneRequest = serde_json::from_slice(&request_bytes).map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("decode lane request: {error}"))
    })?;
    request.validate()?;

    let workspace = env::current_dir().map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("current directory: {error}"))
    })?;

    let outcome = execute_obligation(&workspace, &request);
    let response = LaneResponse::new(
        request.binding().clone(),
        request.request_id(),
        request.key().clone(),
        outcome,
    )?;
    let encoded = serde_json::to_vec(&response).map_err(|error| {
        VerificationError::new(ErrorCode::Json, format!("encode lane response: {error}"))
    })?;
    let response_path = request_path.with_extension("response.json");
    write_atomically(&response_path, &encoded)
}

/// Resolves the test262 authority root relative to the workspace.
fn authority_root(workspace: &Path) -> PathBuf {
    workspace.join("target/authority/test262")
}

/// Maps the shard `ExecutionMode` to the oracle `ExecutionMode`.
fn oracle_mode(mode: ShardExecutionMode) -> ExecutionMode {
    match mode {
        ShardExecutionMode::Interpreter => ExecutionMode::Interpreter,
        ShardExecutionMode::Jit => ExecutionMode::Jit,
        ShardExecutionMode::Aot => ExecutionMode::Aot,
    }
}

/// Executes one test262 obligation and returns the lane outcome.
fn execute_obligation(workspace: &Path, request: &LaneRequest) -> LaneOutcome {
    let key = request.key();
    if key.catalog() != "test262" {
        return LaneOutcome::BlockingFail {
            detail: format!(
                "runtime lane worker received non-test262 catalog `{}`",
                key.catalog()
            ),
        };
    }

    let mode = oracle_mode(key.mode());
    let root = authority_root(workspace);
    let harness_root = root.join("harness");
    let test_root = root.join("test");

    // The obligation key's `case` is the path after the authority prefix
    // has been stripped (e.g. `test262/test/annexB/…/file.js`). The actual
    // file lives under `<root>/test/<relative-after-test262/test/>`.
    let case = key.case();
    let relative = match case.strip_prefix("test262/test/") {
        Some(rest) => PathBuf::from(rest),
        None => PathBuf::from(case),
    };
    let test_file = test_root.join(&relative);

    let source = match fs::read_to_string(&test_file) {
        Ok(source) => source,
        Err(error) => {
            return LaneOutcome::BlockingFail {
                detail: format!(
                    "could not read test262 source `{}`: {error}",
                    test_file.display()
                ),
            };
        }
    };

    let parsed = match test262::parse_test(&source) {
        Ok(parsed) => parsed,
        Err(error) => {
            return LaneOutcome::BlockingFail {
                detail: format!("test262 frontmatter parse error: {error:?}"),
            };
        }
    };

    let plan = match test262::plan_execution(&parsed.frontmatter, &harness_root) {
        Ok(plan) => plan,
        Err(error) => {
            return LaneOutcome::BlockingFail {
                detail: format!("test262 execution plan error: {error:?}"),
            };
        }
    };

    let harness_sources = match load_harness_sources(&plan, &FileHarnessLoader) {
        Ok(sources) => sources,
        Err(error) => {
            return LaneOutcome::BlockingFail {
                detail: format!("test262 harness load error: {error:?}"),
            };
        }
    };

    let deadline = Duration::from_millis(request.timeout_ms());
    let scratch = workspace.join("target/tmp/runtime-worker");
    let runner = match backend_runner(mode, scratch) {
        Ok(runner) => runner.for_test_file(&test_file),
        Err(reason) => {
            return LaneOutcome::BlockingFail {
                detail: reason.to_owned(),
            };
        }
    };

    match evaluate_in_mode(&runner, mode, &parsed, &plan, &harness_sources, deadline) {
        Ok(_) => {
            // Every variant judged clean. Return Completed with the declared
            // observables as artifacts (SHA-256 of the source, matching the
            // compiler lane's pattern of content-addressing evidence).
            let digest = sha256_hex(source.as_bytes());
            LaneOutcome::Completed {
                artifacts: request
                    .observables()
                    .iter()
                    .map(|observable| (observable.clone(), digest.clone()))
                    .collect(),
            }
        }
        Err(OracleError::ModeFailure(failure)) => {
            // Check if the failure was a timeout (fuel exhaustion).
            if is_timeout_failure(&failure.detail) {
                LaneOutcome::Timeout {
                    detail: format!(
                        "test262 {} mode timed out within {:?}: {}",
                        mode.as_str(),
                        deadline,
                        failure.detail
                    ),
                }
            } else {
                LaneOutcome::BlockingFail {
                    detail: format!("test262 {} mode failure: {}", mode.as_str(), failure.detail),
                }
            }
        }
        Err(OracleError::BlockedRun { detail }) => {
            if is_timeout_failure(&detail) {
                LaneOutcome::Timeout {
                    detail: format!(
                        "test262 {} mode timed out within {:?}: {}",
                        mode.as_str(),
                        deadline,
                        detail
                    ),
                }
            } else {
                LaneOutcome::BlockingFail {
                    detail: format!("test262 {} mode blocked: {}", mode.as_str(), detail),
                }
            }
        }
        Err(error) => LaneOutcome::BlockingFail {
            detail: format!("test262 {} mode error: {error:?}", mode.as_str()),
        },
    }
}

/// Heuristic: checks whether a failure detail string indicates a timeout or
/// fuel exhaustion rather than a genuine assertion failure.
fn is_timeout_failure(detail: &str) -> bool {
    detail.contains("FuelExhausted")
        || detail.contains("fuel exhausted")
        || detail.contains("timeout")
        || detail.contains("Timeout")
}

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn write_atomically(path: &Path, bytes: &[u8]) -> Result<()> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", parent.display()))
    })?;
    let temp = path.with_extension("response.tmp");
    fs::write(&temp, bytes).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", temp.display()))
    })?;
    fs::rename(&temp, path).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use bamts_verification::evidence::WorkingDirectoryPolicy;
    use bamts_verification::lane::LaneBinding;
    use bamts_verification::shard::{ExecutionMode, ObligationKey};
    use std::collections::BTreeSet;

    fn test_binding() -> LaneBinding {
        LaneBinding::unbound("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
            .expect("binding")
    }

    #[test]
    fn oracle_mode_maps_correctly() {
        assert_eq!(
            oracle_mode(ExecutionMode::Interpreter),
            test262::ExecutionMode::Interpreter
        );
        assert_eq!(oracle_mode(ExecutionMode::Jit), test262::ExecutionMode::Jit);
        assert_eq!(oracle_mode(ExecutionMode::Aot), test262::ExecutionMode::Aot);
    }

    #[test]
    fn timeout_detection() {
        assert!(is_timeout_failure("FuelExhausted { limit: 100000 }"));
        assert!(is_timeout_failure("fuel exhausted within the deadline"));
        assert!(!is_timeout_failure("assertion failed: 1 !== 2"));
    }

    #[test]
    fn non_test262_catalog_rejected() {
        let key = ObligationKey::new(
            "typescript-7.0.2",
            "some-case",
            "default",
            ExecutionMode::Interpreter,
            "test-platform",
        )
        .expect("key");
        let request = LaneRequest::new(
            test_binding(),
            1,
            key,
            BTreeSet::from(["stdout".to_owned()]),
            vec!["worker".to_owned()],
            WorkingDirectoryPolicy::RepositoryRoot,
            1_000,
        )
        .expect("request");
        let outcome = execute_obligation(Path::new("/nonexistent"), &request);
        assert!(matches!(outcome, LaneOutcome::BlockingFail { .. }));
    }
}
