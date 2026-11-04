//! A serving compiler lane worker answers many requests from one process, and
//! gives each request the response and the failure of a one-request worker.

use std::{
    collections::BTreeSet,
    fs,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use bamts_verification::{
    evidence::WorkingDirectoryPolicy,
    lane::{
        LANE_WORKER_DONE, LANE_WORKER_READY, LANE_WORKER_REQUEST, LANE_WORKER_SERVE, LaneBinding,
        LaneRequest, LaneResponse,
    },
    shard::{ExecutionMode, ObligationKey},
};

const WORKER: &str = env!("CARGO_BIN_EXE_ts_lane_worker");
const RUN_ID: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";

fn scratch(label: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "bamts-lane-serving-{label}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("scratch");
    dir
}

/// A request whose binding names no snapshot, which a worker answers without one.
fn unbound_request(request_id: u64) -> LaneRequest {
    LaneRequest::new(
        LaneBinding::unbound(RUN_ID).expect("binding"),
        request_id,
        ObligationKey::new(
            "typescript-7.0.2",
            format!("compiler/tests/cases/compiler/case{request_id}.ts"),
            "default",
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key"),
        BTreeSet::from(["diagnostics".to_owned()]),
        vec!["lane".to_owned()],
        WorkingDirectoryPolicy::RepositoryRoot,
        30_000,
    )
    .expect("request")
}

fn write_request(dir: &Path, request: &LaneRequest) -> PathBuf {
    let path = dir.join(format!("lane-{RUN_ID}-{}.json", request.request_id()));
    fs::write(&path, serde_json::to_vec(request).expect("encode")).expect("write request");
    path
}

fn response(request_path: &Path) -> LaneResponse {
    let body = fs::read(request_path.with_extension("response.json")).expect("response");
    serde_json::from_slice(&body).expect("decode response")
}

fn one_request_worker(dir: &Path, request_path: &Path) -> std::process::Output {
    Command::new(WORKER)
        .current_dir(dir)
        .env_remove(LANE_WORKER_SERVE)
        .env(LANE_WORKER_REQUEST, request_path)
        .output()
        .expect("one-request worker")
}

fn serving_worker(dir: &Path) -> std::process::Child {
    Command::new(WORKER)
        .current_dir(dir)
        .env_remove(LANE_WORKER_REQUEST)
        .env(LANE_WORKER_SERVE, "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("serving worker")
}

#[test]
fn a_serving_worker_answers_each_request_like_a_one_request_worker() {
    let dir = scratch("answers");
    let single = write_request(&dir, &unbound_request(1));
    assert!(one_request_worker(&dir, &single).status.success());
    let expected = response(&single);

    let mut child = serving_worker(&dir);
    let mut stdin = child.stdin.take().expect("stdin");
    let mut lines = BufReader::new(child.stdout.take().expect("stdout"))
        .lines()
        .map(|line| line.expect("line"))
        .filter(|line| !line.is_empty());
    assert_eq!(lines.next().as_deref(), Some(LANE_WORKER_READY));
    for request_id in [2, 3] {
        let path = write_request(&dir, &unbound_request(request_id));
        writeln!(stdin, "{}", path.display()).expect("send request");
        stdin.flush().expect("flush request");
        assert_eq!(
            lines.next(),
            Some(format!("{LANE_WORKER_DONE} {request_id}"))
        );
        let answered = response(&path);
        assert_eq!(answered.request_id(), request_id);
        assert_eq!(answered.binding(), expected.binding());
        assert_eq!(answered.outcome(), expected.outcome());
    }
    drop(stdin);
    let status = child.wait().expect("worker exits");
    let _ = fs::remove_dir_all(&dir);
    assert!(status.success(), "{status}");
}

#[test]
fn a_serving_worker_ends_on_an_unreadable_request_like_a_one_request_worker() {
    let dir = scratch("unreadable");
    let missing = dir.join(format!("lane-{RUN_ID}-9.json"));
    let expected = one_request_worker(&dir, &missing);
    assert_eq!(expected.status.code(), Some(1));

    let mut child = serving_worker(&dir);
    let mut ready = String::new();
    BufReader::new(child.stdout.take().expect("stdout"))
        .read_line(&mut ready)
        .expect("ready line");
    assert_eq!(ready.trim_end(), LANE_WORKER_READY);
    let mut stdin = child.stdin.take().expect("stdin");
    writeln!(stdin, "{}", missing.display()).expect("send request");
    drop(stdin);
    let served = child.wait_with_output().expect("worker exits");
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(served.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&served.stderr),
        String::from_utf8_lossy(&expected.stderr)
    );
}
