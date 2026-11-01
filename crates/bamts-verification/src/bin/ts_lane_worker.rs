use std::{
    env, fs,
    fs::OpenOptions,
    io::Write,
    path::{Path, PathBuf},
};

use bamts_verification::{
    ErrorCode, Result, VerificationError,
    check_cells::{CheckContext, baseline_groups},
    facets::load_diagnostic_code_map,
    historical::{is_historical, observe_historical_lane},
    lane::{LANE_WORKER_REQUEST, LaneOutcome, LaneRequest, LaneResponse},
    suite::{DEFAULT_SNAPSHOT_REL, load_bound_compiler_snapshot, observe_compiler_lane},
};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
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
    let snapshot_root = workspace.join(DEFAULT_SNAPSHOT_REL);
    let outcome = if !request.binding().has_snapshot() {
        LaneOutcome::BlockingFail {
            detail: "compiler worker request is missing snapshot binding".to_owned(),
        }
    } else {
        match observe_from_workspace(&workspace, &snapshot_root, &request) {
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
    write_atomically(&response_path, &encoded)
}

fn observe_from_workspace(
    workspace: &Path,
    snapshot_root: &Path,
    request: &LaneRequest,
) -> Result<LaneOutcome> {
    let snapshot = load_bound_compiler_snapshot(snapshot_root, request.binding())?;
    let ctx = CheckContext {
        code_map: load_diagnostic_code_map(workspace)?,
        baseline_groups: baseline_groups(&snapshot.index),
    };
    if is_historical(request.key().catalog()) {
        observe_historical_lane(workspace, &snapshot, &ctx, request)
    } else {
        Ok(observe_compiler_lane(&snapshot, &ctx, request).lane_outcome())
    }
}

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
        file.sync_all().map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("{}: {error}", temporary.display()))
        })?;
        fs::rename(&temporary, path).map_err(|error| {
            VerificationError::new(ErrorCode::Io, format!("{}: {error}", path.display()))
        })?;
        if let Ok(directory) = fs::File::open(parent) {
            let _ = directory.sync_all();
        }
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use bamts_verification::lane::LaneBinding;

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
