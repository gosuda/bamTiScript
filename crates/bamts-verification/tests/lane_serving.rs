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
    facets::DIAGNOSTIC_CODE_MAP_PATH,
    lane::{
        LANE_WORKER_DONE, LANE_WORKER_READY, LANE_WORKER_REQUEST, LANE_WORKER_SERVE, LaneBinding,
        LaneOutcome, LaneRequest, LaneResponse, ProcessExecutor, ServingExecutor, run_lane,
    },
    shard::{ExecutionMode, ObligationKey},
    suite::{DEFAULT_SNAPSHOT_REL, materialize_from_extracted},
};

const WORKER: &str = env!("CARGO_BIN_EXE_ts_lane_worker");
const CATALOG: &str = "typescript-7.0.2";
const RUN_ID: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
const OTHER_RUN_ID: &str = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";

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

/// A one-case compiler snapshot where a worker that runs in `dir` looks for one.
fn write_snapshot(dir: &Path) -> PathBuf {
    let extracted = dir.join("extracted");
    let case = extracted.join("tests/cases/compiler/scalarPin.ts");
    fs::create_dir_all(case.parent().expect("case directory")).expect("case directory");
    fs::write(&case, "var x: any;\n").expect("case");
    let baseline = extracted.join("tests/baselines/reference/scalarPin.types");
    fs::create_dir_all(baseline.parent().expect("baseline directory")).expect("baseline directory");
    fs::write(
        &baseline,
        "//// [tests/cases/compiler/scalarPin.ts] ////\n\n=== scalarPin.ts ===\nvar x: any;\n>x : any\n>  : ^^^\n\n",
    )
    .expect("baseline");
    fs::write(extracted.join("LICENSE"), b"Apache-2.0\n").expect("license");
    let root = dir.join(DEFAULT_SNAPSHOT_REL);
    fs::create_dir_all(&root).expect("snapshot root");
    materialize_from_extracted(&root, &extracted).expect("snapshot");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    fs::copy(
        repository.join(DIAGNOSTIC_CODE_MAP_PATH),
        dir.join(DIAGNOSTIC_CODE_MAP_PATH),
    )
    .expect("diagnostic code map");
    root
}

fn bind_snapshot(root: &Path, run_id: &str) -> LaneBinding {
    let root = fs::canonicalize(root).expect("snapshot root");
    let read = |name: &str| fs::read(root.join(name)).expect("snapshot metadata");
    LaneBinding::unbound(run_id)
        .expect("binding")
        .with_snapshot(
            CATALOG,
            &root,
            &read("oracle/pin.json"),
            &read("index.json"),
            &read("ledger.json"),
        )
        .expect("snapshot binding")
}

fn bound_request(binding: &LaneBinding, request_id: u64) -> LaneRequest {
    LaneRequest::new(
        binding.clone(),
        request_id,
        ObligationKey::new(
            CATALOG,
            "compiler/tests/cases/compiler/scalarPin.ts",
            "default#types",
            ExecutionMode::Aot,
            "x86_64-unknown-linux-gnu",
        )
        .expect("key"),
        BTreeSet::from(["types".to_owned()]),
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

/// The stack of the main thread, in the optional header of the image: after the
/// 4-byte signature and the 20-byte file header, at offset 72 in the PE32+ format.
#[cfg(target_env = "msvc")]
#[test]
fn a_lane_worker_has_the_main_thread_stack_of_unix() {
    let image = fs::read(WORKER).expect("worker image");
    let signature = u32::from_le_bytes(image[0x3c..0x40].try_into().expect("four bytes"));
    let reserve = usize::try_from(signature).expect("an offset") + 4 + 20 + 72;
    let bytes = image[reserve..reserve + 8].try_into().expect("eight bytes");
    assert_eq!(u64::from_le_bytes(bytes), 8 * 1024 * 1024);
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
fn a_serving_worker_keeps_the_snapshot_of_a_binding_until_the_binding_changes() {
    let dir = scratch("bound");
    let root = write_snapshot(&dir);
    let first = bind_snapshot(&root, RUN_ID);
    let second = bind_snapshot(&root, OTHER_RUN_ID);
    let single = write_request(&dir, &bound_request(&first, 1));
    assert!(one_request_worker(&dir, &single).status.success());
    let expected = response(&single);
    assert!(
        matches!(expected.outcome(), LaneOutcome::Completed { .. }),
        "{:?}",
        expected.outcome()
    );

    let mut child = serving_worker(&dir);
    let mut stdin = child.stdin.take().expect("stdin");
    let mut lines = BufReader::new(child.stdout.take().expect("stdout"))
        .lines()
        .map(|line| line.expect("line"))
        .filter(|line| !line.is_empty());
    assert_eq!(lines.next().as_deref(), Some(LANE_WORKER_READY));
    let mut ask = |binding: &LaneBinding, request_id: u64| {
        let path = write_request(&dir, &bound_request(binding, request_id));
        writeln!(stdin, "{}", path.display()).expect("send request");
        stdin.flush().expect("flush request");
        assert_eq!(
            lines.next(),
            Some(format!("{LANE_WORKER_DONE} {request_id}"))
        );
        response(&path)
    };

    assert_eq!(ask(&first, 2).outcome(), expected.outcome());
    // No binding matches the metadata on disk now, so a load fails. The next request
    // of the same binding can only be answered from the snapshot in memory.
    fs::write(root.join("index.json"), b"{}").expect("change the snapshot");
    assert_eq!(ask(&first, 3).outcome(), expected.outcome());
    // A new binding is authenticated again, and that lets go of the old snapshot.
    for (binding, request_id) in [(&second, 4), (&first, 5)] {
        let answered = ask(binding, request_id);
        assert_eq!(answered.binding(), binding);
        assert!(
            matches!(answered.outcome(), LaneOutcome::BlockingFail { .. }),
            "{:?}",
            answered.outcome()
        );
    }

    drop(stdin);
    let status = child.wait().expect("worker exits");
    let _ = fs::remove_dir_all(&dir);
    assert!(status.success(), "{status}");
}

#[test]
fn the_serving_executor_records_the_rows_of_one_worker_per_request() {
    let dir = scratch("executors");
    let requests: Vec<LaneRequest> = (1..=3).map(unbound_request).collect();
    let mut one_per_request = ProcessExecutor::new(WORKER, Vec::new(), &dir, dir.join("one"));
    let expected = run_lane(&mut one_per_request, &requests).expect("one worker per request");
    let mut serving = ServingExecutor::new(WORKER, Vec::new(), &dir, dir.join("serving"));
    let served = run_lane(&mut serving, &requests).expect("one serving worker");
    let started = serving.workers_started();
    drop(serving);
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(started, 1, "one worker answers every request");
    assert_eq!(served.len(), expected.len());
    for (served, expected) in served.iter().zip(&expected) {
        assert_eq!(served.key(), expected.key());
        assert_eq!(served.state(), expected.state());
        assert_eq!(served.artifacts(), expected.artifacts());
        assert_eq!(served.detail(), expected.detail());
    }
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
