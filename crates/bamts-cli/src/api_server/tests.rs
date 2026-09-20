use std::{
    fs,
    io::{self, Cursor, Read, Write},
    path::{Path, PathBuf},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use bamts_compiler::service::r#async::CancellationToken;
use serde_json::{Value, json};

use super::control::{
    Control, Inbound, MAX_ID_BYTES, MAX_QUEUED_BYTES, MAX_QUEUED_REJECTS, MAX_QUEUED_WORK, Next,
};
use super::input::{ReaderWaker, TransportInput};
use super::session::*;
use super::wire::*;
use super::*;

fn version_request(id: i64) -> Request {
    Request {
        id: Some(Id::Number(id)),
        method: "compiler/version".to_owned(),
        params: None,
    }
}

#[test]
fn cancel_before_begin_is_pre_cancelled() {
    let control = Control::new();
    assert!(matches!(
        control.offer(version_request(1), 1),
        control::Admission::Accepted
    ));
    control.offer(
        Request {
            id: None,
            method: "$/cancelRequest".to_owned(),
            params: Some(json!({"id": 1})),
        },
        1,
    );
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("work")
    };
    assert!(
        control
            .begin(ticket, Some(request.id.as_ref().expect("id")))
            .is_err()
    );
}

#[test]
fn cancel_during_run_flips_shared_token() {
    let control = Control::new();
    control.offer(version_request(2), 1);
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("work")
    };
    let token = control
        .begin(ticket, Some(request.id.as_ref().expect("id")))
        .expect("token");
    control.offer(
        Request {
            id: None,
            method: "$/cancelRequest".to_owned(),
            params: Some(json!({"id": 2})),
        },
        1,
    );
    assert!(token.is_cancelled());
}

#[test]
fn cancel_after_finish_is_ignored_and_id_reuse_is_clean() {
    let control = Control::new();
    control.offer(version_request(3), 1);
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("work")
    };
    let id = request.id.expect("id");
    control.begin(ticket, Some(&id)).expect("token");
    control.retire(ticket, Some(&id));
    control.offer(
        Request {
            id: None,
            method: "$/cancelRequest".to_owned(),
            params: Some(json!({"id": 3})),
        },
        1,
    );
    control.offer(version_request(3), 1);
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("reused work")
    };
    assert!(
        control
            .begin(ticket, Some(request.id.as_ref().expect("id")))
            .is_ok()
    );
}

#[test]
fn ordinary_partition_never_exceeds_max_in_flight() {
    let control = Control::new();
    for id in 0..=MAX_QUEUED_WORK {
        control.offer(version_request(id as i64), 1);
    }
    let mut work = 0;
    let mut rejects = 0;
    for _ in 0..=MAX_QUEUED_WORK {
        match control.next() {
            Next::Inbound(Inbound::Work { .. }) => work += 1,
            Next::Inbound(Inbound::Reject {
                error: ApiError::IntakeFull,
                ..
            }) => rejects += 1,
            _ => panic!("unexpected"),
        }
    }
    assert_eq!((work, rejects), (MAX_QUEUED_WORK, 1));
}

#[test]
fn notifications_survive_a_full_ordinary_partition() {
    let control = Control::new();
    for id in 0..MAX_QUEUED_WORK {
        control.offer(version_request(id as i64), 1);
    }
    assert!(matches!(
        control.offer(
            Request {
                id: None,
                method: "exit".to_owned(),
                params: None
            },
            1
        ),
        control::Admission::Halt
    ));
    for _ in 0..MAX_QUEUED_WORK {
        assert!(matches!(
            control.next(),
            Next::Inbound(Inbound::Work { .. })
        ));
    }
    assert!(matches!(
        control.next(),
        Next::Inbound(Inbound::Control(control::ControlKind::Exit))
    ));
}

#[test]
fn finish_allows_id_retirement() {
    let control = Control::new();
    control.offer(version_request(9), 1);
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("work")
    };
    let id = request.id.expect("id");
    control.retire(ticket, Some(&id));
    assert_eq!(control.obligation_count(), 0);
}

/// A reader that yields one byte per `read`, proving frame reassembly does
/// not depend on a whole frame arriving in one chunk.
struct Trickle {
    bytes: Vec<u8>,
    offset: usize,
}

impl io::Read for Trickle {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        if self.offset >= self.bytes.len() || buffer.is_empty() {
            return Ok(0);
        }
        buffer[0] = self.bytes[self.offset];
        self.offset += 1;
        Ok(1)
    }
}

fn frame(payload: &str) -> Vec<u8> {
    let mut bytes = format!("Content-Length: {}\r\n\r\n", payload.len()).into_bytes();
    bytes.extend_from_slice(payload.as_bytes());
    bytes
}

fn temp_root(tag: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let root = std::env::temp_dir().join(format!("bamts-api-{tag}-{}-{nonce}", std::process::id()));
    fs::create_dir(&root).expect("create root");
    root
}

/// Runs a whole scripted session, returning the decoded responses.
fn run(input: Vec<u8>) -> Vec<Value> {
    let mut output = Vec::new();
    let mut log = Vec::new();
    serve(ChannelInput::from_bytes(input), &mut output, &mut log).expect("serve");
    decode(&output)
}

fn rpc(session: &mut Session, id: i64, method: &str, params: Value) -> Value {
    rpc_with_token(session, id, method, params, &CancellationToken::new())
}

fn rpc_with_token(
    session: &mut Session,
    id: i64,
    method: &str,
    params: Value,
    cancellation: &CancellationToken,
) -> Value {
    let request = Request {
        id: Some(Id::Number(id)),
        method: method.to_owned(),
        params: Some(params),
    };
    serde_json::to_value(
        session
            .handle(request, cancellation)
            .expect("request response"),
    )
    .expect("response json")
}

fn decode(bytes: &[u8]) -> Vec<Value> {
    let mut reader = Cursor::new(bytes);
    let mut responses = Vec::new();
    loop {
        match read_frame(&mut reader).expect("read response frame") {
            Frame::Payload(body) => {
                responses.push(serde_json::from_slice(&body).expect("response json"));
            }
            Frame::Eof => break,
            other => panic!("unexpected response frame: {other:?}"),
        }
    }
    responses
}

fn error_code(response: &Value) -> i64 {
    response["error"]["code"].as_i64().expect("error code")
}

fn init(root: &Path) -> String {
    format!(
        r#"{{"id":1,"method":"initialize","params":{{"root":{}}}}}"#,
        Value::String(path_text(root))
    )
}

#[test]
fn fragmented_frame_reassembles_across_single_byte_reads() {
    let bytes = frame(r#"{"id":7,"method":"compiler/version"}"#);
    let mut reader = io::BufReader::new(Trickle { bytes, offset: 0 });
    let Frame::Payload(body) = read_frame(&mut reader).expect("frame") else {
        panic!("expected a payload frame");
    };
    let request: Request = serde_json::from_slice(&body).expect("request");
    assert_eq!(request.method, "compiler/version");
    assert_eq!(request.id, Some(Id::Number(7)));
}

#[test]
fn multiple_frames_in_one_buffer_each_answer() {
    let mut input = frame(r#"{"id":1,"method":"compiler/version"}"#);
    input.extend(frame(r#"{"id":2,"method":"compiler/version"}"#));
    input.extend(frame(r#"{"id":3,"method":"compiler/version"}"#));
    let responses = run(input);
    assert_eq!(responses.len(), 3);
    assert_eq!(responses[0]["id"], json!(1));
    assert_eq!(responses[1]["id"], json!(2));
    assert_eq!(responses[2]["id"], json!(3));
    assert!(
        responses
            .iter()
            .all(|response| response["result"]["version"].is_string())
    );
}

#[test]
fn oversize_frame_reports_typed_error_and_keeps_stream_aligned() {
    let declared = MAX_FRAME_BYTES + 1;
    let mut input = format!("Content-Length: {declared}\r\n\r\n").into_bytes();
    input.extend(std::iter::repeat_n(b'x', declared));
    input.extend(frame(r#"{"id":9,"method":"compiler/version"}"#));

    let responses = run(input);
    assert_eq!(
        responses.len(),
        2,
        "oversize must not consume the following frame"
    );
    assert_eq!(error_code(&responses[0]), CODE_FRAME_TOO_LARGE);
    assert_eq!(responses[0]["error"]["data"]["declared"], json!(declared));
    assert_eq!(responses[0]["id"], Value::Null);
    assert_eq!(responses[1]["id"], json!(9), "the next frame still parses");
    assert!(responses[1]["result"]["version"].is_string());
}

#[test]
fn unrecoverable_header_closes_without_desynchronizing() {
    let mut input = b"Content-Length: not-a-number\r\n\r\n".to_vec();
    input.extend(frame(r#"{"id":4,"method":"compiler/version"}"#));
    let responses = run(input);
    assert_eq!(responses.len(), 1);
    assert_eq!(error_code(&responses[0]), CODE_PARSE_ERROR);
}

#[test]
fn duplicate_content_length_is_rejected_as_unrecoverable() {
    let input = b"Content-Length: 2\r\nContent-Length: 2\r\n\r\n{}".to_vec();
    let responses = run(input);
    assert_eq!(responses.len(), 1);
    assert_eq!(error_code(&responses[0]), CODE_PARSE_ERROR);
}

#[test]
fn header_read_stops_at_the_budget_before_a_newline() {
    for prefix in ["", "Content-Length: 2\r\n", "X: y\r\n"].map(str::as_bytes) {
        let mut bytes = prefix.to_vec();
        bytes.extend_from_slice(b"X-Padding: ");
        bytes.extend(std::iter::repeat_n(b'x', MAX_HEADER_BYTES * 2));
        let mut input = Cursor::new(bytes);

        assert!(matches!(
            read_frame(&mut input).expect("bounded header read"),
            Frame::Malformed(_)
        ));
        assert_eq!(
            input.position(),
            (MAX_HEADER_BYTES + 1) as u64,
            "the reader must detect overflow without consuming the rest of the line"
        );
    }
}

#[test]
fn exact_header_budget_preserves_the_body_and_following_frame() {
    let mut bytes = b"Content-Length: 2\r\nX-Padding: ".to_vec();
    bytes.resize(MAX_HEADER_BYTES - 4, b'x');
    bytes.extend_from_slice(b"\r\n\r\n{}");
    bytes.extend(frame(r#"{"id":1,"method":"compiler/version"}"#));
    let mut input = Cursor::new(bytes);

    assert_eq!(
        read_frame(&mut input).expect("exact budget"),
        Frame::Payload(b"{}".to_vec())
    );
    assert!(matches!(
        read_frame(&mut input).expect("next frame"),
        Frame::Payload(_)
    ));
    assert_eq!(read_frame(&mut input).expect("frame boundary"), Frame::Eof);
}

#[test]
fn malformed_json_body_is_answered_and_the_stream_continues() {
    let mut input = frame("{ this is not json ");
    input.extend(frame(r#"{"id":5,"method":"compiler/version"}"#));
    let responses = run(input);
    assert_eq!(responses.len(), 2);
    assert_eq!(error_code(&responses[0]), CODE_PARSE_ERROR);
    assert_eq!(responses[1]["id"], json!(5));
}

#[test]
fn unknown_method_reports_method_not_found() {
    let responses = run(frame(r#"{"id":"a","method":"service/nope"}"#));
    assert_eq!(responses.len(), 1);
    assert_eq!(error_code(&responses[0]), CODE_METHOD_NOT_FOUND);
    assert_eq!(
        responses[0]["error"]["data"]["method"],
        json!("service/nope")
    );
    assert_eq!(responses[0]["id"], json!("a"), "string ids echo exactly");
}

#[test]
fn identifiers_echo_exactly_in_receipt_order() {
    let mut input = frame(r#"{"id":-4,"method":"compiler/version"}"#);
    input.extend(frame(r#"{"id":"second","method":"compiler/version"}"#));
    input.extend(frame(r#"{"id":-4,"method":"compiler/version"}"#));
    let responses = run(input);
    let ids: Vec<&Value> = responses.iter().map(|response| &response["id"]).collect();
    assert_eq!(ids, vec![&json!(-4), &json!("second"), &json!(-4)]);
}

#[test]
fn notification_emits_no_response() {
    let mut input = frame(r#"{"method":"$/cancelRequest","params":{"id":1}}"#);
    input.extend(frame(r#"{"id":2,"method":"compiler/version"}"#));
    let responses = run(input);
    assert_eq!(responses.len(), 1, "notifications are silent");
    assert_eq!(responses[0]["id"], json!(2));
}

#[test]
fn async_route_reports_service_cancellation() {
    let root = temp_root("async-cancel");
    let mut session = Session::new();
    let initialized = rpc(
        &mut session,
        1,
        "initialize",
        json!({ "root": path_text(&root) }),
    );
    assert!(initialized.get("error").is_none());

    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let response = rpc_with_token(
        &mut session,
        2,
        "service/open",
        json!({
            "path": "a.ts",
            "text": "const a = 1;",
            "version": 1,
            "async": true
        }),
        &cancellation,
    );
    assert_eq!(error_code(&response), CODE_REQUEST_CANCELLED);
    assert_eq!(
        rpc(&mut session, 3, "service/snapshot", Value::Null)["result"]["documents"],
        json!([]),
        "a cancelled async open must not mutate service state"
    );
    fs::remove_dir_all(&root).expect("remove root");
}
#[test]
fn cancelled_execute_reports_request_cancelled() {
    let root = temp_root("execute-cancel");
    let mut session = Session::new();
    let initialized = rpc(
        &mut session,
        1,
        "initialize",
        json!({ "root": path_text(&root) }),
    );
    assert!(initialized.get("error").is_none());
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let response = session
        .handle(
            Request {
                id: Some(Id::Number(2)),
                method: "compiler/execute".to_owned(),
                params: Some(json!({ "args": ["--version"] })),
            },
            &cancellation,
        )
        .expect("request response");
    let response = serde_json::to_value(response).expect("response json");
    fs::remove_dir_all(root).expect("remove root");
    assert_eq!(error_code(&response), CODE_REQUEST_CANCELLED);
}

#[test]
fn late_cancel_after_response_does_not_poison_reused_id() {
    let root = temp_root("late-cancel");
    let (input_reader, mut input_writer) = io::pipe().expect("input pipe");
    let (output_reader, output_writer) = io::pipe().expect("output pipe");
    let server =
        std::thread::spawn(move || serve(PollInput(input_reader), output_writer, Vec::new()));

    input_writer
        .write_all(&frame(&init(&root)))
        .expect("initialize");
    input_writer
        .write_all(&frame(r#"{"id":2,"method":"compiler/version"}"#))
        .expect("first version");
    let mut responses = io::BufReader::new(output_reader);
    for expected_id in [1, 2] {
        let Frame::Payload(body) = read_frame(&mut responses).expect("response") else {
            panic!("expected response payload");
        };
        let response: Value = serde_json::from_slice(&body).expect("response json");
        assert_eq!(response["id"], expected_id);
        assert!(response["error"].is_null());
    }

    input_writer
        .write_all(&frame(r#"{"method":"$/cancelRequest","params":{"id":2}}"#))
        .expect("late cancel");
    input_writer
        .write_all(&frame(r#"{"id":2,"method":"compiler/version"}"#))
        .expect("reused id");
    input_writer
        .write_all(&frame(r#"{"method":"exit"}"#))
        .expect("exit");
    drop(input_writer);

    let Frame::Payload(body) = read_frame(&mut responses).expect("reused response") else {
        panic!("expected reused response payload");
    };
    let response: Value = serde_json::from_slice(&body).expect("response json");
    assert_eq!(response["id"], 2);
    assert!(response["error"].is_null());
    server.join().expect("server thread").expect("serve");
    fs::remove_dir_all(root).expect("remove root");
}

#[test]
fn queue_saturation_pipe_cancel() {
    let root = temp_root("queue-saturation");
    let (reader, mut writer) = io::pipe().expect("pipe");
    let root_text = path_text(&root);
    let producer = std::thread::spawn(move || {
        writer
            .write_all(&frame(&format!(
                r#"{{"id":1,"method":"initialize","params":{{"root":{}}}}}"#,
                Value::String(root_text)
            )))
            .expect("initialize");
        let source = "let value = 1;
"
        .repeat((12 * 1024 * 1024) / 15 + 1);
        writer
            .write_all(&frame(
                &json!({
                    "id": 2,
                    "method": "service/open",
                    "params": { "path": "large.ts", "text": source, "version": 1 }
                })
                .to_string(),
            ))
            .expect("large open");
        for id in 3..=72 {
            writer
                .write_all(&frame(&format!(
                    r#"{{"id":{id},"method":"compiler/version"}}"#
                )))
                .expect("version request");
        }
        writer
            .write_all(&frame(r#"{"method":"$/cancelRequest","params":{"id":2}}"#))
            .expect("cancel");
    });

    let started = Instant::now();
    let mut output = Vec::new();
    serve(PollInput(reader), &mut output, Vec::new()).expect("serve");
    producer.join().expect("producer");
    assert!(started.elapsed() < Duration::from_secs(30));
    let responses = decode(&output);
    assert_eq!(responses.len(), 72);
    let open = responses
        .iter()
        .find(|response| response["id"] == 2)
        .expect("open response");
    assert_eq!(error_code(open), CODE_INTAKE_FULL);
    let versions: Vec<_> = responses
        .iter()
        .filter(|response| {
            response["id"]
                .as_i64()
                .is_some_and(|id| (3..=72).contains(&id))
        })
        .collect();
    assert_eq!(versions.len(), 70);
    assert!(versions.iter().all(|response| {
        response["result"]["version"].is_string() || response["error"]["code"] == CODE_INTAKE_FULL
    }));
    fs::remove_dir_all(root).expect("remove root");
}

fn exit_join_elapsed() -> Duration {
    let (reader, mut writer) = io::pipe().expect("pipe");
    let producer = std::thread::spawn(move || {
        writer
            .write_all(&frame(r#"{"method":"exit"}"#))
            .expect("exit");
        std::thread::sleep(Duration::from_millis(100));
    });
    let started = Instant::now();
    serve(PollInput(reader), Vec::new(), Vec::new()).expect("serve");
    let elapsed = started.elapsed();
    producer.join().expect("producer");
    elapsed
}

#[test]
fn repeated_exit_sessions_reap_readers() {
    for _ in 0..4 {
        assert!(exit_join_elapsed() < Duration::from_millis(80));
    }
}

fn shutdown_join_elapsed() -> Duration {
    let (reader, mut writer) = io::pipe().expect("pipe");
    let producer = std::thread::spawn(move || {
        writer
            .write_all(&frame(r#"{"id":1,"method":"shutdown"}"#))
            .expect("shutdown");
        std::thread::sleep(Duration::from_millis(100));
        writer
            .write_all(&frame(r#"{"method":"exit"}"#))
            .expect("exit");
        std::thread::sleep(Duration::from_millis(100));
    });
    let started = Instant::now();
    serve(PollInput(reader), Vec::new(), Vec::new()).expect("serve");
    let elapsed = started.elapsed();
    producer.join().expect("producer");
    elapsed
}

#[test]
fn shutdown_joins_the_reader() {
    assert!(shutdown_join_elapsed() < Duration::from_millis(500));
}

#[test]
fn repeated_shutdown_sessions_reap_readers() {
    for _ in 0..4 {
        assert!(shutdown_join_elapsed() < Duration::from_millis(500));
    }
}

#[test]
fn in_flight_cancel_over_pipe_preserves_session() {
    let root = temp_root("pipe-cancel");
    let (reader, mut writer) = io::pipe().expect("pipe");
    let root_text = path_text(&root);
    let producer = std::thread::spawn(move || {
        writer
            .write_all(&frame(&format!(
                r#"{{"id":1,"method":"initialize","params":{{"root":{}}}}}"#,
                Value::String(root_text)
            )))
            .expect("write initialize");
        let text = "0;\n".repeat(4 * 1024 * 1024);
        let open = serde_json::to_string(&json!({
            "id": 2,
            "method": "service/open",
            "params": {
                "path": "large.ts",
                "text": text,
                "version": 1
            }
        }))
        .expect("open request json");
        writer.write_all(&frame(&open)).expect("write open");
        writer
            .write_all(&frame(r#"{"method":"$/cancelRequest","params":{"id":2}}"#))
            .expect("write cancellation");
        writer
            .write_all(&frame(r#"{"id":3,"method":"service/snapshot"}"#))
            .expect("write snapshot");
    });

    let started = std::time::Instant::now();
    let mut output = Vec::new();
    let mut log = Vec::new();
    serve(PollInput(reader), &mut output, &mut log).expect("serve pipe");
    producer.join().expect("producer");
    let responses = decode(&output);
    fs::remove_dir_all(root).expect("remove root");

    assert!(started.elapsed() < std::time::Duration::from_secs(30));
    assert_eq!(responses.len(), 3);
    assert_eq!(responses[1]["id"], json!(2));
    assert_eq!(error_code(&responses[1]), CODE_INTAKE_FULL);
    assert_eq!(responses[2]["id"], json!(3));
    assert!(
        responses[2].get("error").is_none() || responses[2]["error"]["code"] == CODE_INTAKE_FULL,
        "responses: {responses:#?}"
    );
}

#[test]
fn requests_before_initialize_are_rejected() {
    let responses = run(frame(r#"{"id":1,"method":"service/snapshot"}"#));
    assert_eq!(error_code(&responses[0]), CODE_NOT_INITIALIZED);
}

#[test]
fn compiler_execute_requires_initialize_and_confines_source_inputs() {
    let root = temp_root("execute-confine");
    let execute =
        r#"{"id":1,"method":"compiler/execute","params":{"args":["check","../escape.ts"]}}"#;
    let before_initialize = run(frame(execute));
    assert_eq!(error_code(&before_initialize[0]), CODE_NOT_INITIALIZED);

    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"compiler/execute","params":{"args":["check","../escape.ts"]}}"#,
    ));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
}

#[test]
fn initialize_confines_paths_to_the_session_root() {
    let root = temp_root("confine");
    let mut input = frame(&init(&root));
    input.extend(frame(
            r#"{"id":2,"method":"service/open","params":{"path":"../escape.ts","text":"const a = 1;","version":1}}"#,
        ));
    let canonical_root = fs::canonicalize(&root).expect("canonical root");
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");

    assert_eq!(
        responses[0]["result"]["root"],
        json!(path_text(&canonical_root))
    );
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
}

#[test]
fn ast_scan_reports_cancellation() {
    let mut session = Session::new();
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let response = rpc_with_token(
        &mut session,
        1,
        "ast/scanner/scan",
        json!({ "text": "let value = 1;", "scriptKind": "ts" }),
        &cancellation,
    );
    assert_eq!(error_code(&response), CODE_REQUEST_CANCELLED);
}

#[test]
fn ast_visit_source_file_reports_cancellation() {
    let root = temp_root("ast-cancel");
    let mut session = Session::new();
    assert!(
        rpc(
            &mut session,
            1,
            "initialize",
            json!({ "root": path_text(&root) })
        )["error"]
            .is_null()
    );
    assert!(
        rpc(
            &mut session,
            2,
            "service/open",
            json!({ "path": "a.ts", "text": "let value = 1;", "version": 1 }),
        )["error"]
            .is_null()
    );

    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let visited = rpc_with_token(
        &mut session,
        3,
        "ast/visitor/visitSourceFile",
        json!({ "path": "a.ts" }),
        &cancellation,
    );
    assert_eq!(error_code(&visited), CODE_REQUEST_CANCELLED);
    let resolved = rpc_with_token(
        &mut session,
        4,
        "ast/id",
        json!({ "path": "a.ts" }),
        &cancellation,
    );
    assert_eq!(error_code(&resolved), CODE_REQUEST_CANCELLED);
    fs::remove_dir_all(root).expect("remove root");
}

#[test]
fn public_ast_dispatches_all_twenty_operations_over_one_snapshot() {
    let root = temp_root("public-ast");
    let mut session = Session::new();
    let initialized = rpc(
        &mut session,
        1,
        "initialize",
        json!({ "root": path_text(&root) }),
    );
    assert!(initialized.get("error").is_none());
    let opened = rpc(
        &mut session,
        2,
        "service/open",
        json!({ "path": "a.ts", "text": "const alpha = 1;", "version": 1 }),
    );
    assert!(opened.get("error").is_none());

    let visited = rpc(
        &mut session,
        3,
        "ast/visitor/visitSourceFile",
        json!({ "path": "a.ts" }),
    );
    let nodes = visited["result"].as_array().expect("visited nodes");
    let statement = nodes
        .iter()
        .find(|node| {
            node["nodeKind"]
                .as_str()
                .is_some_and(|kind| kind != "SourceFile")
                && node["id"].is_number()
        })
        .expect("canonical non-root node");
    let node_id = statement["id"].as_u64().expect("node id");
    let range = statement["range"].clone();
    let selector = json!({ "path": "a.ts", "nodeId": node_id });

    let calls = [
        ("ast/id", selector.clone()),
        ("ast/range", selector.clone()),
        ("ast/syntaxKind", selector.clone()),
        ("ast/nodeKind", selector.clone()),
        (
            "ast/is",
            json!({ "path": "a.ts", "nodeId": node_id, "predicate": "node" }),
        ),
        (
            "ast/factory/create",
            json!({ "path": "a.ts", "nodeId": node_id, "id": 900, "range": range }),
        ),
        (
            "ast/factory/update",
            json!({ "path": "a.ts", "nodeId": node_id, "changedId": 901, "range": range }),
        ),
        (
            "ast/factory/asNode",
            json!({ "path": "a.ts", "nodeId": node_id, "changedId": 902, "range": range }),
        ),
        (
            "ast/factory/intoOwned",
            json!({ "path": "a.ts", "nodeId": node_id, "changedId": 903, "range": { "start": 0, "end": 1 } }),
        ),
        (
            "ast/utils/textOfRange",
            json!({ "path": "a.ts", "range": { "start": 0, "end": 5 } }),
        ),
        ("ast/utils/nodeText", selector.clone()),
        (
            "ast/utils/containsRange",
            json!({ "outer": { "start": 0, "end": 16 }, "inner": { "start": 6, "end": 11 } }),
        ),
        (
            "ast/utils/containsPosition",
            json!({ "range": { "start": 0, "end": 16 }, "position": 6 }),
        ),
        (
            "ast/utils/narrowestContaining",
            json!({ "path": "a.ts", "position": 6 }),
        ),
        ("ast/scanner/scan", json!({ "path": "a.ts" })),
        ("ast/visitor/visitSourceFile", json!({ "path": "a.ts" })),
        ("ast/visitor/visitNode", selector.clone()),
        ("ast/clone", selector.clone()),
        (
            "ast/cloneWithId",
            json!({ "path": "a.ts", "nodeId": node_id, "id": 904 }),
        ),
    ];
    assert_eq!(calls.len(), 19);
    for (offset, (method, params)) in calls.into_iter().enumerate() {
        let response = rpc(&mut session, 10 + offset as i64, method, params);
        assert!(
            response.get("error").is_none(),
            "{method} failed: {response}"
        );
    }
    assert_eq!(nodes[0]["nodeKind"], json!("SourceFile"));
    fs::remove_dir_all(root).expect("remove root");
}

#[test]
fn public_ast_rejects_stale_ids_ranges_predicates_and_escaped_paths() {
    let root = temp_root("public-ast-errors");
    let mut session = Session::new();
    let _ = rpc(
        &mut session,
        1,
        "initialize",
        json!({ "root": path_text(&root) }),
    );
    let _ = rpc(
        &mut session,
        2,
        "service/open",
        json!({ "path": "a.ts", "text": "const alpha = 1;", "version": 1 }),
    );

    let invalid = [
        rpc(
            &mut session,
            3,
            "ast/range",
            json!({ "path": "a.ts", "nodeId": u32::MAX }),
        ),
        rpc(
            &mut session,
            4,
            "ast/utils/textOfRange",
            json!({ "path": "a.ts", "range": { "start": 9, "end": 2 } }),
        ),
        rpc(
            &mut session,
            5,
            "ast/is",
            json!({ "path": "a.ts", "predicate": "invented" }),
        ),
        rpc(
            &mut session,
            6,
            "ast/scanner/scan",
            json!({ "path": "../escape.ts" }),
        ),
    ];
    assert_eq!(error_code(&invalid[0]), CODE_INVALID_PARAMS);
    assert_eq!(error_code(&invalid[1]), CODE_INVALID_PARAMS);
    assert_eq!(error_code(&invalid[2]), CODE_INVALID_PARAMS);
    assert_eq!(error_code(&invalid[3]), CODE_ROOT_CONFINEMENT);
    fs::remove_dir_all(root).expect("remove root");
}

#[test]
fn initialize_reports_all_ten_service_methods_once() {
    let root = temp_root("methods");
    let mut input = frame(&init(&root));
    input.extend(frame(&format!(
        r#"{{"id":2,"method":"initialize","params":{{"root":{}}}}}"#,
        Value::String(path_text(&root))
    )));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");

    let methods = responses[0]["result"]["methods"]
        .as_array()
        .expect("methods");
    assert_eq!(methods.len(), 10);
    for method in SERVICE_METHODS {
        assert!(
            methods.contains(&json!(method)),
            "{method} must be advertised"
        );
    }
    assert_eq!(error_code(&responses[1]), CODE_INVALID_REQUEST);
}

#[test]
fn service_state_persists_across_requests() {
    let root = temp_root("persist");
    let mut input = frame(&init(&root));
    input.extend(frame(
            r#"{"id":2,"method":"service/open","params":{"path":"a.ts","text":"const alpha = 1;","version":1}}"#,
        ));
    input.extend(frame(
            r#"{"id":3,"method":"service/update","params":{"path":"a.ts","text":"const alpha = 2;","version":2}}"#,
        ));
    input.extend(frame(
        r#"{"id":4,"method":"service/snapshot","params":{"async":true}}"#,
    ));
    input.extend(frame(
        r#"{"id":5,"method":"service/diagnostics","params":{"path":"a.ts"}}"#,
    ));
    input.extend(frame(
        r#"{"id":6,"method":"service/completions","params":{"path":"a.ts","position":6}}"#,
    ));
    input.extend(frame(
        r#"{"id":7,"method":"service/definition","params":{"path":"a.ts","position":6}}"#,
    ));
    input.extend(frame(
        r#"{"id":8,"method":"service/quickInfo","params":{"path":"a.ts","position":6}}"#,
    ));
    input.extend(frame(
        r#"{"id":9,"method":"service/quickInfo","params":{"path":"a.ts","position":5}}"#,
    ));
    input.extend(frame(
        r#"{"id":10,"method":"service/references","params":{"path":"a.ts","position":6}}"#,
    ));
    input.extend(frame(
        r#"{"id":11,"method":"service/rename","params":{"path":"a.ts","position":6,"newName":"beta"}}"#,
    ));
    input.extend(frame(
        r#"{"id":12,"method":"service/close","params":{"path":"a.ts"}}"#,
    ));

    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(responses.len(), 12);

    assert_eq!(responses[1]["result"]["version"], json!(1));
    assert_eq!(responses[2]["result"]["version"], json!(2));

    let documents = responses[3]["result"]["documents"]
        .as_array()
        .expect("documents");
    assert_eq!(
        documents.len(),
        1,
        "the async route shares one service state"
    );
    assert_eq!(
        documents[0]["version"],
        json!(2),
        "update survived into the snapshot"
    );
    assert_eq!(documents[0]["open"], json!(true));

    for (index, response) in responses.iter().enumerate().skip(4).take(7) {
        assert!(
            response.get("error").is_none(),
            "response {index} failed: {response}"
        );
    }
    assert!(responses[4]["result"].is_array(), "diagnostics is a list");
    assert!(responses[5]["result"].is_array(), "completions is a list");
    assert_eq!(
        responses[7]["result"],
        json!({
            "name": "alpha",
            "kind": "const",
            "typeDisplay": "2",
            "display": "const alpha: 2",
            "range": { "start": 6, "end": 11 },
        })
    );
    assert_eq!(responses[8]["result"], Value::Null);
    assert!(responses[9]["result"].is_array(), "references is a list");
    assert!(
        responses[10]["result"]["symbol"].is_string(),
        "rename names its symbol"
    );
    assert_eq!(responses[11]["result"]["closed"], json!(true));
}

#[test]
fn missing_parameters_report_invalid_params() {
    let root = temp_root("params");
    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"service/open","params":{"path":"a.ts"}}"#,
    ));
    input.extend(frame(
        r#"{"id":3,"method":"service/completions","params":{"path":"a.ts"}}"#,
    ));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");

    assert_eq!(error_code(&responses[1]), CODE_INVALID_PARAMS);
    assert_eq!(error_code(&responses[2]), CODE_INVALID_PARAMS);
}

#[test]
fn shutdown_answers_then_stops_the_loop() {
    let mut input = frame(r#"{"id":1,"method":"shutdown"}"#);
    input.extend(frame(r#"{"id":2,"method":"compiler/version"}"#));
    let responses = run(input);
    assert_eq!(
        responses.len(),
        2,
        "admitted work receives a terminal response"
    );
    assert_eq!(responses[0]["id"], json!(1));
    assert_eq!(responses[1]["id"], json!(2));
    assert_eq!(responses[1]["error"]["code"], CODE_REQUEST_CANCELLED);
}

#[test]
fn stdout_carries_only_protocol_frames() {
    let mut output = Vec::new();
    let mut log = Vec::new();
    serve(
        ChannelInput::from_bytes(b"Content-Length: bogus\r\n\r\n".to_vec()),
        &mut output,
        &mut log,
    )
    .expect("serve");

    assert!(
        output.starts_with(b"Content-Length: "),
        "stdout begins with a frame header"
    );
    assert_eq!(decode(&output).len(), 1, "stdout decodes as frames only");
    assert!(!log.is_empty(), "the close reason went to the log writer");
}

#[test]
fn scanner_rejects_oversize_request_text() {
    let mut session = Session::new();
    let oversized = "a".repeat(bamts_compiler::source::MAX_SOURCE_BYTES + 1);
    let response = rpc(
        &mut session,
        1,
        "ast/scanner/scan",
        json!({
            "text": oversized,
            "sourceId": 0,
            "scriptKind": "ts",
        }),
    );
    assert_eq!(error_code(&response), CODE_INVALID_PARAMS);
    let message = response["error"]["message"].as_str().expect("message");
    assert!(
        message.contains("exceeds"),
        "message should describe size: {message}"
    );
    assert!(
        message.contains("per-file budget"),
        "message should mention budget: {message}"
    );
}

#[test]
fn maybe_run_declines_argv_without_the_api_token() {
    assert_eq!(maybe_run(&["tsc".to_owned(), "main.ts".to_owned()]), None);
}

#[test]
fn saturation_beyond_128_answers_every_admitted_id() {
    let mut input = Vec::new();
    for id in 0..300 {
        input.extend(frame(&format!(
            r#"{{"id":{id},"method":"compiler/version"}}"#
        )));
    }
    input.extend(frame(r#"{"method":"exit"}"#));
    let responses = run(input);
    assert_eq!(responses.len(), 300);
    let mut ids: Vec<i64> = responses
        .iter()
        .map(|response| response["id"].as_i64().expect("numeric id"))
        .collect();
    ids.sort_unstable();
    assert_eq!(ids, (0..300).collect::<Vec<_>>());
    assert!(responses.iter().all(|response| {
        response.get("result").is_some() || response["error"]["code"] == CODE_INTAKE_FULL
    }));
}

#[test]
fn exit_behind_saturation_terminates_and_answers_fifo() {
    let mut input = Vec::new();
    for id in 0..200 {
        input.extend(frame(&format!(
            r#"{{"id":{id},"method":"compiler/version"}}"#
        )));
    }
    input.extend(frame(r#"{"method":"exit"}"#));
    let started = Instant::now();
    let responses = run(input);
    assert!(started.elapsed() < Duration::from_secs(5));
    assert_eq!(responses.len(), 200);
    assert_eq!(responses.first().expect("first")["id"], 0);
    assert_eq!(responses.last().expect("last")["id"], 199);
}

#[test]
fn eof_drains_all_response_obligations_before_returning() {
    let mut input = Vec::new();
    for id in 1..=80 {
        input.extend(frame(&format!(
            r#"{{"id":{id},"method":"compiler/version"}}"#
        )));
    }
    let responses = run(input);
    assert_eq!(responses.len(), 80);
    assert!(responses.iter().all(|response| {
        response["result"]["version"].is_string() || response["error"]["code"] == CODE_INTAKE_FULL
    }));
}

#[test]
fn duplicate_live_id_is_rejected_without_losing_first_obligation() {
    let control = Control::new();
    let request = || Request {
        id: Some(Id::Text("same".to_owned())),
        method: "compiler/version".to_owned(),
        params: None,
    };
    control.offer(request(), 1);
    control.offer(request(), 1);
    assert!(matches!(
        control.next(),
        Next::Inbound(Inbound::Work { .. })
    ));
    assert!(matches!(
        control.next(),
        Next::Inbound(Inbound::Reject {
            error: ApiError::InvalidRequest(_),
            ..
        })
    ));
}

#[test]
fn oversize_text_id_is_rejected_with_null_id() {
    let id = "x".repeat(MAX_ID_BYTES + 1);
    let responses = run(frame(
        &json!({ "id": id, "method": "compiler/version" }).to_string(),
    ));
    assert_eq!(responses.len(), 1);
    assert_eq!(responses[0]["id"], Value::Null);
    assert_eq!(responses[0]["error"]["code"], CODE_INVALID_REQUEST);
}

#[test]
fn flood_boundary_is_terminal_and_never_silent() {
    let control = Control::new();
    for id in 0..1_200 {
        let admission = control.offer(version_request(id), 1);
        if matches!(admission, control::Admission::Halt) {
            break;
        }
    }
    let mut responses = 0;
    loop {
        match control.next() {
            Next::Inbound(Inbound::Work { .. } | Inbound::Reject { .. }) => responses += 1,
            Next::Fatal(response, _) => {
                assert_eq!(response.error.expect("flood error").code, CODE_FLOODED);
                break;
            }
            _ => panic!("unexpected reader exit"),
        }
    }
    assert_eq!(responses, MAX_QUEUED_WORK + MAX_QUEUED_REJECTS);
}

struct ImmediateReadError;

impl Read for ImmediateReadError {
    fn read(&mut self, _buffer: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::new(
            io::ErrorKind::ConnectionReset,
            "read failed",
        ))
    }
}

struct ImmediateWake;

impl ReaderWaker for ImmediateWake {
    const REAPABLE: bool = true;

    fn wake(&self) -> io::Result<()> {
        Ok(())
    }
}

struct ErrorInput;

impl TransportInput for ErrorInput {
    type Reader = io::BufReader<ImmediateReadError>;
    type Waker = ImmediateWake;

    fn split(self) -> io::Result<(Self::Reader, Self::Waker)> {
        Ok((io::BufReader::new(ImmediateReadError), ImmediateWake))
    }
}

#[test]
fn read_error_wakes_executor_and_is_reaped() {
    let started = Instant::now();
    let (result, reaped) = serve_reaped(ErrorInput, Vec::new(), Vec::new());
    assert_eq!(
        result.expect_err("read failure").kind(),
        io::ErrorKind::ConnectionReset
    );
    assert!(matches!(reaped, Reaped::Joined(_)));
    assert!(started.elapsed() < Duration::from_secs(1));
}

struct FailWriter;

impl Write for FailWriter {
    fn write(&mut self, _buffer: &[u8]) -> io::Result<usize> {
        Err(io::Error::new(io::ErrorKind::BrokenPipe, "write failed"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn write_error_with_input_held_open_returns_and_reaps() {
    let (sender, input) = ChannelInput::channel();
    sender
        .send(frame(r#"{"id":1,"method":"compiler/version"}"#))
        .expect("send request");
    let started = Instant::now();
    let (result, reaped) = serve_reaped(input, FailWriter, Vec::new());
    drop(sender);
    assert_eq!(
        result.expect_err("write failure").kind(),
        io::ErrorKind::BrokenPipe
    );
    assert!(matches!(reaped, Reaped::Joined(_)));
    assert!(started.elapsed() < Duration::from_secs(1));
}

#[test]
fn response_obligations_conserve_across_offer_cancel_retire_sequences() {
    let control = Control::new();
    for id in 0..MAX_QUEUED_WORK {
        assert!(matches!(
            control.offer(version_request(id as i64), id + 1),
            control::Admission::Accepted
        ));
        if id % 3 == 0 {
            control.offer(
                Request {
                    id: None,
                    method: "$/cancelRequest".to_owned(),
                    params: Some(json!({ "id": id })),
                },
                0,
            );
        }
    }
    for _ in 0..MAX_QUEUED_WORK {
        let Next::Inbound(Inbound::Work {
            ticket, request, ..
        }) = control.next()
        else {
            panic!("work partition changed shape");
        };
        let id = request.id.expect("id");
        let _ = control.begin(ticket, Some(&id));
        control.retire(ticket, Some(&id));
    }
    assert_eq!(control.obligation_count(), 0);
}

#[test]
fn first_oversized_admission_is_rejected_and_bytes_never_exceed_cap() {
    let control = Control::new();
    assert!(matches!(
        control.offer(version_request(1), MAX_QUEUED_BYTES + 1),
        control::Admission::Accepted
    ));
    assert_eq!(control.queued_accounting_for_test(), (0, 0));
    let Next::Inbound(Inbound::Reject {
        ticket,
        id,
        error: ApiError::IntakeFull,
    }) = control.next()
    else {
        panic!("oversized first request must be an answered rejection");
    };
    control.retire(ticket, id.as_ref());
    assert_eq!(control.obligation_count(), 0);

    let chunk = MAX_QUEUED_BYTES / 4;
    for id in 2..=5 {
        control.offer(version_request(id), chunk);
        let (work, bytes) = control.queued_accounting_for_test();
        assert_eq!(work, (id - 1) as usize);
        assert!(bytes <= MAX_QUEUED_BYTES);
    }
    control.offer(version_request(6), 1);
    assert_eq!(control.queued_accounting_for_test(), (4, MAX_QUEUED_BYTES));
    assert_eq!(control.obligation_count(), 5);
    for _ in 0..5 {
        match control.next() {
            Next::Inbound(Inbound::Work {
                ticket, request, ..
            }) => control.retire(ticket, request.id.as_ref()),
            Next::Inbound(Inbound::Reject { ticket, id, .. }) => {
                control.retire(ticket, id.as_ref());
            }
            _ => panic!("admission queue changed shape"),
        }
    }
    assert_eq!(control.queued_accounting_for_test(), (0, 0));
    assert_eq!(control.obligation_count(), 0);
}
#[test]
fn notifications_execute_in_fifo_order_with_requests() {
    let root = temp_root("notify-fifo");
    let init_frame = init(&root);
    let mut input = frame(&init_frame);
    // Notification: service/open — side-effect only, no response.
    input.extend(frame(
        r#"{"method":"service/open","params":{"path":"a.ts","text":"const prior = 1;","version":1}}"#,
    ));
    input.extend(frame(
        r#"{"id":2,"method":"service/open","params":{"path":"b.ts","text":"const extra = 2;","version":1}}"#,
    ));
    input.extend(frame(
        r#"{"id":3,"method":"service/diagnostics","params":{"path":"a.ts"}}"#,
    ));
    input.extend(frame(
        r#"{"id":4,"method":"service/diagnostics","params":{"path":"b.ts"}}"#,
    ));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(
        responses.len(),
        4,
        "notification must not produce a frame: {responses:#?}"
    );
    assert_eq!(responses[0]["id"], json!(1));
    assert!(
        responses[0]["error"].is_null(),
        "initialize: {responses:#?}"
    );
    assert_eq!(responses[1]["id"], json!(2));
    assert!(
        responses[1]["error"].is_null(),
        "second open: {responses:#?}"
    );
    assert_eq!(responses[2]["id"], json!(3));
    assert!(
        responses[2]["error"].is_null(),
        "diagnostics a.ts — notification before it must have executed: {responses:#?}"
    );
    assert_eq!(responses[3]["id"], json!(4));
    assert!(
        responses[3]["error"].is_null(),
        "diagnostics b.ts: {responses:#?}"
    );
}

#[test]
fn notification_produces_no_response_frame_even_on_bad_method() {
    let root = temp_root("notify-noresp");
    let mut input = frame(&init(&root));
    input.extend(frame(r#"{"method":"not/a/method"}"#));
    input.extend(frame(r#"{"id":2,"method":"compiler/version"}"#));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(
        responses.len(),
        2,
        "bad-method notification must not add a frame"
    );
    assert_eq!(responses[0]["id"], json!(1));
    assert!(responses[0]["error"].is_null());
    assert_eq!(responses[1]["id"], json!(2));
    assert!(responses[1]["result"]["version"].is_string());
}

#[test]
fn notification_admission_counts_against_work_bounds() {
    let control = Control::new();
    control.offer(
        Request {
            id: None,
            method: "service/open".to_owned(),
            params: Some(json!({ "path": "a.ts", "text": "x", "version": 1 })),
        },
        11,
    );
    assert_eq!(control.queued_accounting_for_test(), (1, 11));
    let Next::Inbound(Inbound::Work {
        ticket, request, ..
    }) = control.next()
    else {
        panic!("notification work");
    };
    assert!(request.id.is_none());
    control.begin(ticket, request.id.as_ref()).expect("token");
    control.retire(ticket, request.id.as_ref());
    assert_eq!(control.queued_accounting_for_test(), (0, 0));
}

#[test]
fn notification_dropped_silently_on_full_queue_and_idd_still_rejected() {
    let control = Control::new();
    for id in 0..MAX_QUEUED_WORK {
        assert!(matches!(
            control.offer(version_request(id as i64), 1),
            control::Admission::Accepted
        ));
    }
    assert_eq!(control.queued_accounting_for_test().0, MAX_QUEUED_WORK);
    // Notification on a full queue: accepted, not enqueued, no Reject frame.
    assert!(matches!(
        control.offer(
            Request {
                id: None,
                method: "service/open".to_owned(),
                params: None
            },
            1
        ),
        control::Admission::Accepted
    ));
    assert_eq!(control.queued_accounting_for_test().0, MAX_QUEUED_WORK);
    for _ in 0..MAX_QUEUED_WORK {
        assert!(matches!(
            control.next(),
            Next::Inbound(Inbound::Work { .. })
        ));
    }
    control.reader_exited(ReaderExit::Eof);
    assert!(matches!(
        control.next(),
        Next::ReaderExited(ReaderExit::Eof)
    ));

    // Identify the 65th identified work request that still gets IntakeFull.
    let control2 = Control::new();
    for id in 0..MAX_QUEUED_WORK {
        control2.offer(version_request(id as i64), 1);
    }
    assert!(matches!(
        control2.offer(version_request(999), 1),
        control::Admission::Accepted
    ));
    let mut saw_reject = false;
    for _ in 0..=MAX_QUEUED_WORK {
        if let Next::Inbound(Inbound::Reject {
            error: ApiError::IntakeFull,
            ..
        }) = control2.next()
        {
            saw_reject = true;
        }
    }
    assert!(saw_reject, "65th id'd request must be rejected IntakeFull");
}

#[test]
fn execute_rejects_output_file_escape() {
    let root = temp_root("exec-out-escape");
    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"compiler/execute","params":{"args":["compile","main.ts","-o","../escape.js"]}}"#,
    ));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
}

#[test]
fn execute_rejects_absolute_output_file_outside_root() {
    let root = temp_root("exec-out-abs");
    let outside = std::env::temp_dir().join(format!(
        "bamts-api-exec-out-abs-target-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos(),
    ));
    let mut input = frame(&init(&root));
    let payload = format!(
        r#"{{"id":2,"method":"compiler/execute","params":{{"args":["compile","main.ts","-o",{}]}}}}"#,
        Value::String(path_text(&outside))
    );
    input.extend(frame(&payload));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
}

#[cfg(unix)]
#[test]
fn execute_rejects_output_below_escaping_symlink() {
    use std::os::unix::fs::symlink;

    let root = temp_root("exec-out-symlink");
    let outside = temp_root("exec-out-symlink-target");
    symlink(&outside, root.join("link")).expect("create output symlink");
    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"compiler/execute","params":{"args":["compile","main.ts","-o","link/escape.js"]}}"#,
    ));
    let responses = run(input);
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
    assert!(!outside.join("escape.js").exists(), "output escaped root");
    fs::remove_dir_all(&root).expect("remove root");
    fs::remove_dir_all(&outside).expect("remove outside");
}

#[test]
fn execute_rejects_out_dir_escape() {
    let root = temp_root("exec-outdir-escape");
    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"compiler/execute","params":{"args":["compile","main.ts","--out-dir","../escape"]}}"#,
    ));
    let responses = run(input);
    fs::remove_dir_all(&root).expect("remove root");
    assert_eq!(error_code(&responses[1]), CODE_ROOT_CONFINEMENT);
}

#[test]
fn execute_accepts_in_root_output_file() {
    let root = temp_root("exec-out-inroot");
    fs::write(root.join("main.ts"), "const a = 1;\n").expect("write source");
    let mut input = frame(&init(&root));
    input.extend(frame(
        r#"{"id":2,"method":"compiler/execute","params":{"args":["compile","main.ts","-o","main.js"]}}"#,
    ));
    let responses = run(input);
    assert!(
        responses[1]["error"].is_null(),
        "in-root output failed: {responses:#?}"
    );
    assert!(root.join("main.js").is_file(), "output was not written");
    fs::remove_dir_all(&root).expect("remove root");
}
