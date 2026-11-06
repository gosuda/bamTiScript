//! Compiler lane worker.
//!
//! With `BAMTS_LANE_WORKER_REQUEST` set, it answers that one request and exits.
//! With `BAMTS_LANE_WORKER_SERVE` set instead, it prints [`LANE_WORKER_READY`],
//! then answers one request path per line of standard input and prints
//! [`LANE_WORKER_DONE`] with the request ID after each response is written.
//! A serving worker authenticates the snapshot of a binding once and keeps it
//! for the later requests of that binding. A failure that ends a one-request
//! worker ends a serving worker the same way, so the parent records the same row.

use std::{
    env, fs,
    fs::OpenOptions,
    io::{BufRead, Write},
    path::{Path, PathBuf},
};

use bamts_verification::{
    ErrorCode, Result, VerificationError,
    check_cells::{CheckContext, baseline_groups},
    facets::load_diagnostic_code_map,
    historical::{is_historical, observe_historical_lane},
    lane::{
        LANE_WORKER_DONE, LANE_WORKER_READY, LANE_WORKER_REQUEST, LANE_WORKER_SERVE, LaneBinding,
        LaneOutcome, LaneRequest, LaneResponse,
    },
    suite::{
        CompilerSnapshot, DEFAULT_SNAPSHOT_REL, load_bound_compiler_snapshot, observe_compiler_lane,
    },
};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    if let Some(request_path) = env::var_os(LANE_WORKER_REQUEST) {
        return answer(&PathBuf::from(request_path), &mut None).map(|_| ());
    }
    if env::var_os(LANE_WORKER_SERVE).is_some() {
        return serve();
    }
    Err(VerificationError::new(
        ErrorCode::Usage,
        format!("{LANE_WORKER_REQUEST} is not set"),
    ))
}

/// The authenticated snapshot of one binding and the check context built from it.
struct Prepared {
    binding: LaneBinding,
    snapshot: CompilerSnapshot,
    ctx: CheckContext,
}

fn serve() -> Result<()> {
    let mut prepared = None;
    say(LANE_WORKER_READY)?;
    for line in std::io::stdin().lock().lines() {
        let line = line.map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("standard input: {error}"))
        })?;
        let request_id = answer(Path::new(&line), &mut prepared)?;
        // The empty line ends any line that the compile above left open.
        say(&format!("\n{LANE_WORKER_DONE} {request_id}"))?;
    }
    Ok(())
}

/// Prints one line to standard output and flushes it, so the parent reads it now.
fn say(line: &str) -> Result<()> {
    let mut stdout = std::io::stdout();
    writeln!(stdout, "{line}")
        .and_then(|()| stdout.flush())
        .map_err(|error| VerificationError::new(ErrorCode::Io, format!("standard output: {error}")))
}

/// Answers the request at `request_path` and returns its request ID.
fn answer(request_path: &Path, prepared: &mut Option<Prepared>) -> Result<u64> {
    let request_bytes = fs::read(request_path).map_err(|error| {
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
    let snapshot_root = workspace.join(DEFAULT_SNAPSHOT_REL);
    let outcome = if !request.binding().has_snapshot() {
        LaneOutcome::BlockingFail {
            detail: "compiler worker request is missing snapshot binding".to_owned(),
        }
    } else {
        match observe_from_workspace(&workspace, &snapshot_root, prepared, &request) {
            Ok(outcome) => outcome,
            Err(error) => LaneOutcome::BlockingFail {
                detail: error.to_string(),
            },
        }
    };
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
    write_atomically(&response_path, &encoded)?;
    Ok(request.request_id())
}

fn observe_from_workspace(
    workspace: &Path,
    snapshot_root: &Path,
    prepared: &mut Option<Prepared>,
    request: &LaneRequest,
) -> Result<LaneOutcome> {
    if prepared
        .as_ref()
        .is_none_or(|current| &current.binding != request.binding())
    {
        // Let go of the old snapshot before the new one is loaded beside it.
        *prepared = None;
        let snapshot = load_bound_compiler_snapshot(snapshot_root, request.binding())?;
        let ctx = CheckContext {
            code_map: load_diagnostic_code_map(workspace)?,
            baseline_groups: baseline_groups(&snapshot.index),
        };
        *prepared = Some(Prepared {
            binding: request.binding().clone(),
            snapshot,
            ctx,
        });
    }
    let current = prepared
        .as_ref()
        .expect("the snapshot of this binding was prepared above");
    if is_historical(request.key().catalog()) {
        observe_historical_lane(workspace, &current.snapshot, &current.ctx, request)
    } else {
        Ok(observe_compiler_lane(&current.snapshot, &current.ctx, request).lane_outcome())
    }
}

/// Writes the response under a temporary name and renames it, so the parent never
/// reads half of one. It is not synced: the parent reads it from the page cache of
/// this host, and a power failure ends the run that needs it.
fn write_atomically(path: &Path, bytes: &[u8]) -> Result<()> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent).map_err(|error| {
        VerificationError::new(ErrorCode::Io, format!("{}: {error}", parent.display()))
    })?;
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            VerificationError::new(
                ErrorCode::Io,
                format!("{}: response file name is not UTF-8", path.display()),
            )
        })?;
    let temporary = parent.join(format!(".{file_name}.{}.tmp", std::process::id()));
    let result = (|| {
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temporary)
            .map_err(|error| {
                VerificationError::new(ErrorCode::Io, format!("{}: {error}", temporary.display()))
            })?;
        file.write_all(bytes).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("{}: {error}", temporary.display()))
        })?;
        drop(file);
        fs::rename(&temporary, path).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
        })
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_requires_compiler_snapshot_binding() {
        let binding = LaneBinding::unbound(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        )
        .expect("binding");
        assert!(!binding.has_snapshot());
        let error = load_bound_compiler_snapshot(Path::new("."), &binding)
            .expect_err("unbound request cannot use the fast path");
        assert_eq!(error.code(), ErrorCode::Schema);
        assert!(error.to_string().contains("missing snapshot binding"));
    }
}
