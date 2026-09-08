use std::fs;
use std::io::Write;
#[cfg(unix)]
use std::os::unix::io::OwnedFd;
#[cfg(unix)]
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;
use std::time::{Duration, Instant};

const EXPECTED_STDOUT: &[u8] = b"hello from bamts\n";
const UTF16_PROGRAM: &str = r#"const s = "\uD800";
process.stdout.write(String(s.length) + "\n");
process.stdout.write(s.charCodeAt(0).toString(16) + "\n");
process.stdout.write(s.codePointAt(0).toString(16) + "\n");
process.stdout.write(String(/./gu.exec("\u{1F600}")[0].length) + "\n");
process.stdout.write(String("\u{10003}" < "\u{E000}") + "\n");
const key = Object.keys({["\u{1F600}"]: 3})[0];
process.stdout.write(String(key.length) + "\n");
process.stdout.write(key.codePointAt(0).toString(16) + "\n");
"#;
const UTF16_STDOUT: &[u8] = b"1\nd800\nd800\n2\ntrue\n2\n1f600\n";
const CALLABLE_PROGRAM: &str = r#"function probe(a: unknown, b: unknown) {
    const values = [this, a, b];
    return values;
}

const receiver = { tag: "right" };
const ignored = { tag: "wrong" };
const applied = probe.apply(receiver, { 0: 7, 1: 8, length: 2 });
if (applied[0] !== receiver || applied[1] !== 7 || applied[2] !== 8) {
    throw "apply mismatch";
}

const bound = probe.bind(receiver, 1);
const called = bound.call(ignored, 2);
if (called[0] !== receiver || called[1] !== 1 || called[2] !== 2) {
    throw "bind mismatch";
}
if (bound.length !== 1 || bound.name !== "bound probe") {
    throw "bound metadata mismatch";
}
if (Object.hasOwn(bound, "prototype")) {
    throw "bound shape mismatch";
}

function Box(a: number, b: number) {
    this.sum = a + b;
}
Object.defineProperty(Box, "prototype", {
    value: { kind: "box" },
    writable: true,
});
const BoundBox = Box.bind({ sum: 99 }, 4);
const box = new BoundBox(5);
if (
    box.sum !== 9 ||
    box.kind !== "box" ||
    !(box instanceof Box) ||
    !(box instanceof BoundBox)
) {
    throw "bound construction mismatch";
}
"#;
const VM_PROGRAM: &str = r#"import { runInNewContext } from 'node:vm';
console.log(runInNewContext('1 + 1'));
console.log(typeof runInNewContext('({})'));
"#;
const CLASSIC_DYNAMIC_IMPORT_PROGRAM: &str = r#"import vm from 'node:vm';
vm.runInThisContext("import('node:util').then(function(ns) { process.stdout.write(String(typeof ns.parseArgs) + '\\n'); })");
"#;
static NEXT_DIRECTORY: AtomicU32 = AtomicU32::new(0);

#[test]
fn api_execution_preserves_stdout_and_exit_code() {
    let directory = ScratchDirectory::new();
    directory.write("hello.ts", include_str!("fixtures/hello.ts"));
    let output = directory.execute("jit", "hello.ts", &[]);
    assert_execution_success(&output, "compiler/execute fixture");
    assert_eq!(output.stdout, EXPECTED_STDOUT);
}

#[test]
fn tsc_argument_diagnostics_use_stdout() {
    let project = ScratchDirectory::new();
    let output = project
        .command()
        .args(["--target", "es3", "--ignoreConfig"])
        .current_dir(&project.path)
        .output()
        .expect("tsc argument validation starts");

    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stdout).contains("error TS5108:"));
    assert!(output.stderr.is_empty());
}

#[test]
fn api_execution_reports_bounded_resource_exhaustion() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "for (;;) {}\n");

    let response = project.execute_response("jit", "main.ts", &[]);

    let message = response["error"]["message"]
        .as_str()
        .expect("resource exhaustion is an API error");
    assert!(message.contains("fuel exhausted"), "{message}");
}

/// Node spawns `--api` with `stdio: "pipe"`, which is a socket pair on Unix;
/// the transport must serve the inherited descriptor because no pathname can
/// reopen a socket.
#[cfg(unix)]
#[test]
fn api_transport_serves_socket_backed_stdin() {
    let directory = ScratchDirectory::new();
    let (mut peer, child_stdin) = UnixStream::pair().expect("socket pair for child stdin");
    let child = directory
        .command()
        .arg("--api")
        .current_dir(&directory.path)
        .stdin(Stdio::from(OwnedFd::from(child_stdin)))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("bamts API child starts");

    let requests = [
        serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": { "root": directory.path },
        }),
        serde_json::json!({
            "jsonrpc": "2.0",
            "id": 2,
            "method": "shutdown",
        }),
    ];
    let mut input = Vec::new();
    for request in requests {
        let payload = serde_json::to_vec(&request).expect("API request serializes");
        input.extend(framed(&payload));
    }
    peer.write_all(&input).expect("API requests are written");

    // `peer` stays open across the wait: the child must exit because shutdown
    // was requested and its reader reaped, not because stdin reached EOF.
    let output = wait_for_output(child, "bamts --api");
    drop(peer);

    assert_success(&output, "bamts --api");
    let canonical_root = fs::canonicalize(&directory.path).expect("session root canonicalizes");
    let responses = decode_frames(&output.stdout);
    assert_eq!(
        responses,
        vec![
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "result": {
                    "root": canonical_root.to_string_lossy(),
                    "methods": [
                        "service/open",
                        "service/update",
                        "service/close",
                        "service/snapshot",
                        "service/completions",
                        "service/definition",
                        "service/quickInfo",
                        "service/references",
                        "service/rename",
                        "service/diagnostics",
                    ],
                },
            }),
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": 2,
                "result": null,
            }),
        ],
        "initialize and shutdown return exact protocol responses"
    );
}

#[test]
fn aot_and_jit_share_process_argv_entrypoint_parity() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"process.stdout.write(process.argv[0] + "\n");
process.stdout.write(process.argv[1] + "\n");
process.stdout.write(process.argv[2] + "\n");
process.stdout.write(process.argv[3] + "\n");
process.stdout.write(process.env.BAMTS_AOT_ENTRYPOINT === undefined ? "hidden\n" : "leaked\n");
"#,
    );

    let jit = project.execute("jit", "main.ts", &["first", "second"]);
    assert_execution_success(&jit, "compiler/execute JIT argv program");
    let aot = project.execute("aot", "main.ts", &["first", "second"]);
    assert_execution_success(&aot, "compiler/execute AOT argv program");

    let expected = format!(
        "bamts\n{}\nfirst\nsecond\nhidden\n",
        fs::canonicalize(project.path.join("main.ts"))
            .expect("entrypoint canonicalizes")
            .display()
    );
    assert_eq!(jit.stdout, expected.as_bytes());
    assert_eq!(aot.stdout, jit.stdout);
}

#[test]
fn aot_and_jit_execute_non_decimal_bigint_literals() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"const hex = 0x100000000000000000000000000000001n;
const octal = 0o20n;
const binary = 0b1_0000n;
if (
    hex !== 340282366920938463463374607431768211457n ||
    octal !== 16n ||
    binary !== 16n
) {
    throw "non-decimal BigInt mismatch";
}
process.stdout.write("ok\n");
"#,
    );

    let jit = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&jit, "compiler/execute JIT BigInt program");
    let aot = project.execute("aot", "main.ts", &[]);
    assert_execution_success(&aot, "compiler/execute AOT BigInt program");

    assert_eq!(jit.stdout, b"ok\n");
    assert_eq!(aot.stdout, jit.stdout);
}

#[test]
fn aot_and_jit_execute_classic_script_dynamic_imports() {
    let project = ScratchDirectory::new();
    project.write("main.ts", CLASSIC_DYNAMIC_IMPORT_PROGRAM);

    let jit = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&jit, "compiler/execute JIT classic dynamic import program");
    let aot = project.execute("aot", "main.ts", &[]);
    assert_execution_success(&aot, "compiler/execute AOT classic dynamic import program");

    assert_eq!(jit.stdout, b"function\n");
    assert_eq!(aot.stdout, jit.stdout);
}

#[test]
fn aot_and_jit_run_all_nested_finally_completions() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"const trace: string[] = [];
function returnProbe(): number {
    try {
        try { return 7; } finally { trace.push("return-inner"); }
    } finally {
        trace.push("return-outer");
    }
}
trace.push("return:" + returnProbe());
try {
    try {
        try { throw "boom"; } finally { trace.push("throw-inner"); }
    } finally {
        trace.push("throw-outer");
    }
} catch (error) {
    trace.push("catch:" + error);
}
for (;;) {
    try {
        try { trace.push("break-body"); break; } finally { trace.push("break-inner"); }
    } finally {
        trace.push("break-outer");
    }
}
for (let i = 0; i < 2; i++) {
    try {
        try { trace.push("continue-body:" + i); continue; }
        finally { trace.push("continue-inner:" + i); }
    } finally {
        trace.push("continue-outer:" + i);
    }
}
process.stdout.write(trace.join(",") + "\n");
"#,
    );

    let expected = b"return-inner,return-outer,return:7,throw-inner,throw-outer,catch:boom,\
break-body,break-inner,break-outer,continue-body:0,continue-inner:0,continue-outer:0,\
continue-body:1,continue-inner:1,continue-outer:1\n";
    for target in ["jit", "aot"] {
        let output = project.execute(target, "main.ts", &[]);
        assert_execution_success(
            &output,
            &format!("compiler/execute {target} nested-finally program"),
        );
        assert_eq!(output.stdout, expected, "{target}");
    }
}

#[test]
fn aot_and_jit_run_labeled_control_flow() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"const trace: string[] = [];
block: {
    trace.push("block");
    break block;
    trace.push("bad-block");
}
trace.push("after-block");
let visits = 0;
first: second: for (let i = 0; i < 3; i++) {
    visits++;
    if (i < 2) continue first;
    trace.push("loop:" + i);
}
trace.push("visits:" + visits);
exit: {
    try {
        try { trace.push("break-body"); break exit; }
        finally { trace.push("break-inner"); }
    } finally {
        trace.push("break-outer");
    }
    trace.push("bad-exit");
}
outer: for (let i = 0; i < 2; i++) {
    try {
        try { trace.push("continue-body:" + i); continue outer; }
        finally { trace.push("continue-inner:" + i); }
    } finally {
        trace.push("continue-outer:" + i);
    }
}
crossed: for (let i = 0; i < 2; i++) {
    try {
        for (let j = 0; j < 2; j++) {
            try { break crossed; } finally { trace.push("crossed-inner:" + i); }
        }
        trace.push("bad-crossed:" + i);
    } finally {
        trace.push("crossed-outer:" + i);
    }
}
choice: switch (1) {
    case 1: trace.push("switch"); break choice;
    default: trace.push("bad-switch");
}
process.stdout.write(trace.join(",") + "\n");
"#,
    );

    let expected = b"block,after-block,loop:2,visits:3,break-body,break-inner,break-outer,\
continue-body:0,continue-inner:0,continue-outer:0,continue-body:1,continue-inner:1,\
continue-outer:1,crossed-inner:0,crossed-outer:0,switch\n";
    for target in ["jit", "aot"] {
        let output = project.execute(target, "main.ts", &[]);
        assert_execution_success(
            &output,
            &format!("compiler/execute {target} labeled program"),
        );
        assert_eq!(output.stdout, expected, "{target}");
    }
}

#[test]
fn aot_and_jit_close_iterators_after_finally_and_preserve_body_throw() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"const trace: string[] = [];
const iterable = {
    [Symbol.iterator]() {
        return {
            next() { return { value: 1, done: false }; },
            return() {
                trace.push("return()");
                throw "close-error";
            },
        };
    },
};
try {
    for (const value of iterable) {
        try {
            trace.push("body:" + value);
            throw "body-error";
        } finally {
            trace.push("finally");
        }
    }
} catch (error) {
    trace.push("catch:" + error);
}
process.stdout.write(trace.join(",") + "\n");
"#,
    );

    let expected = b"body:1,finally,return(),catch:body-error\n";
    for target in ["jit", "aot"] {
        let output = project.execute(target, "main.ts", &[]);
        assert_execution_success(
            &output,
            &format!("compiler/execute {target} iterator-close ordering program"),
        );
        assert_eq!(output.stdout, expected, "{target}");
    }
}

#[test]
fn aot_and_jit_share_escaped_identifier_identity() {
    let project = ScratchDirectory::new();
    project.write("dependency.ts", "export const \\u0076alue = 41;\n");
    project.write(
        "main.ts",
        r#"import { value as \u0061lias } from "./dependency.ts";
const increment = (\u{0000006e}: number) => n + 1;
process.stdout.write(String(increment(alias)) + "\n");
"#,
    );

    for target in ["jit", "aot"] {
        let output = project.execute(target, "main.ts", &[]);
        assert_execution_success(
            &output,
            &format!("compiler/execute {target} escaped-name program"),
        );
        assert_eq!(output.stdout, b"42\n", "{target}");
    }
}

#[test]
fn aot_fixture_matches_jit_stdout_and_exit_code() {
    let directory = ScratchDirectory::new();
    let executable = directory
        .path
        .join(format!("hello{}", std::env::consts::EXE_SUFFIX));
    let compile = directory.emit(&fixture().to_string_lossy(), &executable);
    assert_success(&compile, "bamts tsc-compatible emit");

    let output = Command::new(&executable)
        .output()
        .expect("compiled executable starts");
    assert_success(&output, "compiled fixture");
    assert_eq!(output.stdout, EXPECTED_STDOUT);
}

#[test]
fn jit_runs_two_module_program_with_live_imported_mutation() {
    let project = ScratchDirectory::new();
    project.write("dependency.ts", "export let value = 1; value = 2;\n");
    project.write(
        "main.ts",
        "import { value } from './dependency.js'; console.log(value);\n",
    );

    let output = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&output, "compiler/execute two-module JIT");
    assert_eq!(output.stdout, b"2\n");
}

#[test]
fn aot_runs_two_module_program_with_live_imported_mutation() {
    let project = ScratchDirectory::new();
    project.write("dependency.ts", "export let value = 1; value = 2;\n");
    project.write(
        "main.ts",
        "import { value } from './dependency.js'; console.log(value);\n",
    );
    let executable = project
        .path
        .join(format!("two-module{}", std::env::consts::EXE_SUFFIX));

    let compile = project.emit("main.ts", &executable);
    assert_success(&compile, "bamts tsc-compatible two-module emit");

    let output = Command::new(&executable)
        .output()
        .expect("two-module AOT executable starts");
    assert_success(&output, "compiled two-module program");
    assert_eq!(output.stdout, b"2\n");
}

#[test]
fn jit_preserves_lone_surrogates_end_to_end() {
    let project = ScratchDirectory::new();
    project.write("main.ts", UTF16_PROGRAM);

    let output = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&output, "compiler/execute UTF-16 JIT");
    assert_eq!(output.stdout, UTF16_STDOUT);
}

#[test]
fn aot_preserves_lone_surrogates_end_to_end() {
    let project = ScratchDirectory::new();
    project.write("main.ts", UTF16_PROGRAM);
    let executable = project
        .path
        .join(format!("utf16{}", std::env::consts::EXE_SUFFIX));

    let compile = project.emit("main.ts", &executable);
    assert_success(&compile, "bamts tsc-compatible UTF-16 emit");

    let output = Command::new(&executable)
        .output()
        .expect("UTF-16 AOT executable starts");
    assert_success(&output, "compiled UTF-16 program");
    assert_eq!(output.stdout, UTF16_STDOUT);
}

#[test]
fn jit_supports_apply_and_bound_callables() {
    let project = ScratchDirectory::new();
    project.write("main.ts", CALLABLE_PROGRAM);

    let output = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&output, "compiler/execute callable JIT");
    assert!(output.stdout.is_empty());
}

#[test]
fn aot_supports_apply_and_bound_callables() {
    let project = ScratchDirectory::new();
    project.write("main.ts", CALLABLE_PROGRAM);
    let executable = project
        .path
        .join(format!("callable{}", std::env::consts::EXE_SUFFIX));

    let compile = project.emit("main.ts", &executable);
    assert_success(&compile, "bamts tsc-compatible callable AOT emit");

    let output = Command::new(&executable)
        .output()
        .expect("callable AOT executable starts");
    assert_success(&output, "compiled callable program");
    assert!(output.stdout.is_empty());
}

#[test]
fn aot_runs_node_vm_in_new_context() {
    let project = ScratchDirectory::new();
    project.write("main.ts", VM_PROGRAM);
    let executable = project
        .path
        .join(format!("node-vm{}", std::env::consts::EXE_SUFFIX));

    let compile = project.emit("main.ts", &executable);
    assert_success(&compile, "bamts tsc-compatible node:vm AOT emit");

    let output = Command::new(&executable)
        .output()
        .expect("node:vm AOT executable starts");
    assert_success(&output, "compiled node:vm program");
    assert!(
        !stderr(&output).contains("bamts: aot runtime"),
        "{}",
        stderr(&output)
    );
    assert_eq!(output.stdout, b"2\nobject\n");
}

#[test]
fn jit_runs_external_import_equals_with_one_binding() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        r#"import util = require('node:util');
process.stdout.write(String(typeof util.parseArgs) + "\n");
"#,
    );

    let output = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&output, "compiler/execute import-equals JIT");
    assert_eq!(output.stdout, b"function\n");
}

#[test]
fn jit_runs_local_commonjs_style_import_equals_with_one_binding() {
    let project = ScratchDirectory::new();
    project.write("dependency.ts", "export const value = 41;\n");
    project.write(
        "main.ts",
        r#"import dependency = require('./dependency.js');
process.stdout.write(String(dependency.value + 1) + "\n");
"#,
    );

    let output = project.execute("jit", "main.ts", &[]);
    assert_execution_success(&output, "compiler/execute local import-equals JIT");
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn check_reports_dependency_errors() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "import './dependency.ts';\n");
    project.write("dependency.ts", "const = 1;\n");

    let output = project.check("main.ts");

    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(1));
    let stdout = stdout(&output);
    assert!(stdout.contains("dependency.ts"), "{}", stdout);
}

#[test]
fn check_loads_type_only_dependencies() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        "import type { Shape } from './types.ts';\nexport const loaded = true;\n",
    );
    project.write("types.ts", "export interface Shape { value: string }\n");

    assert_success(&project.check("main.ts"), "bamts check type-only graph");
}

#[test]
fn check_loads_diamond_graph_once() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "import './left.ts';\nimport './right.ts';\n");
    project.write("left.ts", "import './leaf.ts';\nexport const left = 1;\n");
    project.write("right.ts", "import './leaf.ts';\nexport const right = 2;\n");
    project.write("leaf.ts", "export const leaf = 3;\n");

    assert_success(&project.check("main.ts"), "bamts check diamond graph");
}

#[test]
fn check_accepts_module_cycles() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "import './a.ts';\n");
    project.write("a.ts", "import './b.ts';\nexport const a = 1;\n");
    project.write("b.ts", "import './a.ts';\nexport const b = 2;\n");

    assert_success(&project.check("main.ts"), "bamts check cyclic graph");
}

#[test]
fn check_applies_project_lint_config_to_dependencies() {
    let project = ScratchDirectory::new();
    project.write("bamts.toml", "[lints.rules]\nexplicit-any = \"deny\"\n");
    project.write("src/main.ts", "import '../dependency.ts';\n");
    project.write("dependency.ts", "export const value: any = 1;\n");

    let output = project.check_from("src", "main.ts");

    assert!(!output.status.success());
    let stdout = stdout(&output);
    assert!(stdout.contains("dependency.ts"), "{stdout}");
    assert!(stdout.contains("BAMTS-W017"), "{stdout}");
}

#[test]
fn check_renders_multi_file_diagnostics_in_stable_source_order() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "import './first.ts';\nimport './second.ts';\n");
    project.write("first.ts", "const = 1;\n");
    project.write("second.ts", "const = 2;\n");

    let first = project.check("main.ts");
    let second = project.check("main.ts");

    assert!(!first.status.success());
    assert_eq!(first.stdout, second.stdout);
    let stdout = stdout(&first);
    let first_position = stdout.find("first.ts").expect("first diagnostic");
    let second_position = stdout.find("second.ts").expect("second diagnostic");
    assert!(first_position < second_position, "{stdout}");
}

fn assert_not_implemented(output: &Output, option: &str) {
    assert_eq!(
        output.status.code(),
        Some(5),
        "exit: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout(output),
        stderr(output)
    );
    assert_eq!(
        stderr(output),
        format!(
            "error TS5047: Compiler option '--{option}' has no canonical native driver mapping.\n"
        )
    );
    assert!(stdout(output).is_empty(), "{}", stdout(output));
}

fn assert_parse_failure(output: &Output, code: u32, message: &str) {
    assert_eq!(
        output.status.code(),
        Some(1),
        "exit: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout(output),
        stderr(output)
    );
    assert!(stderr(output).is_empty());
    let out = stdout(output);
    assert!(out.contains(&format!("error TS{code}: {message}")), "{out}");
}

#[test]
fn project_mode_forwards_native_option_overrides() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"rootDir":"src","outDir":"config-out","declaration":true}}"#,
    );

    let forwarded = project
        .command()
        .args([
            "-p",
            "tsconfig.json",
            "--outDir",
            "cli-out",
            "--declaration",
            "false",
            "--pretty",
            "false",
        ])
        .current_dir(&project.path)
        .output()
        .expect("project compile starts");

    assert_success(&forwarded, "project compile with CLI overrides");
    assert!(project.path.join("cli-out/main.js").is_file());
    assert!(
        !project.path.join("cli-out/main.d.ts").exists(),
        "the declaration override must disable the config declaration"
    );
    assert!(
        !project.path.join("config-out").exists(),
        "config outDir must not be used while the CLI override applies"
    );
}

#[test]
fn project_mode_rejects_unimplemented_options() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"outDir":"dist"}}"#,
    );

    for (option, name) in [
        (vec!["--watch"], "watch"),
        (vec!["--ignoreConfig"], "ignoreConfig"),
    ] {
        let output = project
            .command()
            .args(["-p", "tsconfig.json", "--pretty", "false"])
            .args(&option)
            .current_dir(&project.path)
            .output()
            .expect("project option gate starts");
        assert_not_implemented(&output, name);
    }

    assert!(
        !project.path.join("dist").exists(),
        "option classification must precede project loading"
    );
}

#[test]
fn project_mode_lists_files_and_list_only_skips_emit() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "import './dependency.ts';\n");
    project.write("src/dependency.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"outDir":"dist"}}"#,
    );

    let only = project
        .command()
        .args(["-p", "tsconfig.json", "--listFilesOnly"])
        .current_dir(&project.path)
        .output()
        .expect("listFilesOnly starts");
    assert!(only.status.success(), "{}", stderr(&only));
    let only_stdout = stdout(&only);
    assert!(only_stdout.contains("dependency.ts"), "{only_stdout}");
    assert!(only_stdout.contains("main.ts"), "{only_stdout}");
    assert!(!project.path.join("dist").exists());

    let listed = project
        .command()
        .args(["-p", "tsconfig.json", "--listFiles"])
        .current_dir(&project.path)
        .output()
        .expect("listFiles starts");
    assert!(listed.status.success(), "{}", stderr(&listed));
    let listed_stdout = stdout(&listed);
    assert!(listed_stdout.contains("dependency.ts"), "{listed_stdout}");
    assert!(listed_stdout.contains("main.ts"), "{listed_stdout}");
    assert!(project.path.join("dist/main.js").is_file());
    assert!(project.path.join("dist/dependency.js").is_file());
}

#[test]
fn build_mode_rejects_unimplemented_options() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"rootDir":"src","outDir":"dist"}}"#,
    );

    for (option, name) in [
        (vec!["--watch"], "watch"),
        (vec!["--builders", "4"], "builders"),
        (vec!["--noEmit"], "noEmit"),
        (vec!["--incremental"], "incremental"),
    ] {
        let output = project
            .command()
            .args(["--build", "tsconfig.json"])
            .args(&option)
            .current_dir(&project.path)
            .output()
            .expect("build option gate starts");
        assert_not_implemented(&output, name);
    }

    assert!(
        !project.path.join("dist").exists(),
        "option classification must precede any build work"
    );
}

#[test]
fn build_mode_consumes_build_controls_and_reports_verbose_status() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"composite":true,"rootDir":"src","outDir":"dist"}}"#,
    );

    let building = project
        .command()
        .args(["--build", "--verbose", "--pretty", "false"])
        .current_dir(&project.path)
        .output()
        .expect("verbose first build starts");
    assert_success(&building, "verbose first build");
    let building_out = stdout(&building);
    assert!(
        building_out.contains("Building project '"),
        "{building_out}"
    );
    assert!(project.path.join("dist/main.js").is_file());

    let forced = project
        .command()
        .args([
            "--build",
            "--force",
            "--stopBuildOnErrors",
            "false",
            "--pretty",
            "false",
        ])
        .current_dir(&project.path)
        .output()
        .expect("forced rebuild starts");
    assert_success(&forced, "forced rebuild consumes build controls");

    let up_to_date = project
        .command()
        .args(["--build", "--verbose", "--pretty", "false"])
        .current_dir(&project.path)
        .output()
        .expect("verbose up-to-date build starts");
    assert_success(&up_to_date, "verbose up-to-date build");
    let up_to_date_out = stdout(&up_to_date);
    assert!(up_to_date_out.contains("is up to date"), "{up_to_date_out}");
    assert!(up_to_date_out.contains("tsconfig.json"), "{up_to_date_out}");
}

#[test]
fn show_config_direct_matches_typescript_bytes() {
    let project = ScratchDirectory::new();
    project.write("file.ts", "export const value = 1;\n");

    let output = project
        .command()
        .args([
            "--showConfig",
            "--ignoreConfig",
            "file.ts",
            "--target",
            "ES2024",
            "--strict",
            "false",
        ])
        .current_dir(&project.path)
        .output()
        .expect("showConfig direct probe starts");

    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
    let expected = "{\n    \"compilerOptions\": {\n        \"strict\": false,\n        \"target\": \"es2024\"\n    },\n    \"files\": [\n        \"./file.ts\"\n    ]\n}\n";
    assert_eq!(stdout(&output), expected);
}

#[test]
fn show_config_project_merges_effective_view_without_emit() {
    let project = ScratchDirectory::new();
    project.write("app/src/main.ts", "export const main = 1;\n");
    project.write(
        "app/src/helper.ts",
        "import { lib } from '../../shared/lib';\nexport const main = lib;\n",
    );
    project.write("shared/lib/src/lib.ts", "export const lib = 1;\n");
    project.write(
        "shared/tsconfig.json",
        r#"{"compilerOptions":{"composite":true,"outDir":"out"},"include":["lib/src/**/*"]}"#,
    );
    project.write(
        "app/tsconfig.base.json",
        r#"{"compilerOptions":{"target":"ES2020","noUnusedLocals":true}}"#,
    );
    project.write(
        "app/tsconfig.json",
        r#"{"extends":"./tsconfig.base.json","compilerOptions":{"target":"ES2022","outDir":"dist","module":"nodenext"},"include":["src/**/*"],"exclude":["node_modules"],"references":[{"path":"../shared"}]}"#,
    );

    let output = project
        .command()
        .args(["--showConfig", "-p", "app"])
        .current_dir(&project.path)
        .output()
        .expect("showConfig project probe starts");

    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
    let text = stdout(&output);
    // Exact structural assertion: parse the document and verify the JSON
    // shape. serde_json sorts object keys (BTreeMap), so key ordering is
    // verified separately by text position below.
    let json: serde_json::Value =
        serde_json::from_str(text.trim_end()).expect("showConfig output is valid JSON");
    let root = json.as_object().expect("root is a JSON object");

    // Top-level keys are exactly the TypeScript project document keys.
    // This fails if any implied option leaks to the document root.
    let expected_top_keys = [
        "compilerOptions",
        "references",
        "files",
        "include",
        "exclude",
    ];
    assert_eq!(
        root.len(),
        expected_top_keys.len(),
        "top-level key count: {text}"
    );
    for key in expected_top_keys {
        assert!(
            root.contains_key(key),
            "missing top-level key \"{key}\": {text}"
        );
    }
    assert!(
        !root.contains_key("moduleResolution") && !root.contains_key("moduleDetection"),
        "implied option leaked to top level: {text}",
    );

    // `extends` is never emitted; the child overrides the base.
    let compiler_options = root
        .get("compilerOptions")
        .and_then(|v| v.as_object())
        .expect("compilerOptions is an object");
    assert!(!compiler_options.contains_key("extends"), "{text}");
    assert_eq!(
        compiler_options.get("target").and_then(|v| v.as_str()),
        Some("es2022")
    );
    assert_eq!(
        compiler_options.get("module").and_then(|v| v.as_str()),
        Some("nodenext")
    );
    assert_eq!(
        compiler_options.get("outDir").and_then(|v| v.as_str()),
        Some("./dist")
    );
    assert_eq!(
        compiler_options
            .get("noUnusedLocals")
            .and_then(|v| v.as_bool()),
        Some(true)
    );

    // Implied options are nested inside `compilerOptions`, not at the root.
    assert_eq!(
        compiler_options
            .get("moduleResolution")
            .and_then(|v| v.as_str()),
        Some("nodenext"),
        "moduleResolution must be inside compilerOptions: {text}",
    );
    assert_eq!(
        compiler_options
            .get("moduleDetection")
            .and_then(|v| v.as_str()),
        Some("force"),
        "moduleDetection must be inside compilerOptions: {text}",
    );

    // References, files, include, exclude.
    let references = root
        .get("references")
        .and_then(|v| v.as_array())
        .expect("references array");
    assert_eq!(references.len(), 1, "{text}");
    assert_eq!(
        references[0].get("path").and_then(|v| v.as_str()),
        Some("../shared"),
        "{text}",
    );
    let files = root
        .get("files")
        .and_then(|v| v.as_array())
        .expect("files array");
    let file_paths: Vec<&str> = files
        .iter()
        .map(|v| v.as_str().expect("file string"))
        .collect();
    assert!(file_paths.contains(&"./src/main.ts"), "{text}");
    assert!(file_paths.contains(&"./src/helper.ts"), "{text}");
    let include = root
        .get("include")
        .and_then(|v| v.as_array())
        .expect("include array");
    assert_eq!(
        include
            .iter()
            .map(|v| v.as_str().expect("include string"))
            .collect::<Vec<_>>(),
        vec!["./src/**/*"],
        "{text}",
    );
    let exclude = root
        .get("exclude")
        .and_then(|v| v.as_array())
        .expect("exclude array");
    assert_eq!(
        exclude
            .iter()
            .map(|v| v.as_str().expect("exclude string"))
            .collect::<Vec<_>>(),
        vec!["./node_modules"],
        "{text}",
    );

    // Top-level TypeScript order: compilerOptions, references, files,
    // include, exclude.
    let options_at = text
        .find("\"compilerOptions\"")
        .expect("compilerOptions key");
    let references_at = text.find("\"references\"").expect("references key");
    let files_at = text.find("\"files\"").expect("files key");
    let include_at = text.find("\"include\"").expect("include key");
    let exclude_at = text.find("\"exclude\"").expect("exclude key");
    assert!(options_at < references_at, "{text}");
    assert!(references_at < files_at, "{text}");
    assert!(files_at < include_at, "{text}");
    assert!(include_at < exclude_at, "{text}");

    // Implied options appear inside the compilerOptions block (after the
    // explicit entries, before the block closes) — not between top-level
    // keys.
    let module_resolution_at = text
        .find("\"moduleResolution\"")
        .expect("moduleResolution key");
    let module_detection_at = text
        .find("\"moduleDetection\"")
        .expect("moduleDetection key");
    let module_at = text.find("\"module\":").expect("module key");
    assert!(
        module_at < module_resolution_at,
        "explicit before implied: {text}"
    );
    assert!(
        module_resolution_at < module_detection_at,
        "implied order: {text}"
    );
    assert!(
        module_detection_at < references_at,
        "implied options must be inside compilerOptions, before references: {text}",
    );

    // No absolute fallback for anything inside the project root.
    assert!(
        !text.contains(project.path.to_str().expect("UTF-8 scratch root")),
        "{text}"
    );

    // The trailing byte is exactly one newline.
    assert!(text.ends_with("}\n"), "{text}");

    // No emit happened on this route.
    assert!(!project.path.join("app/dist").exists());
    assert!(!project.path.join("shared/out").exists());
}

#[test]
fn show_config_build_dispatch_rejects_at_parse_time() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "tsconfig.json",
        r#"{"files":["src/main.ts"],"compilerOptions":{"outDir":"dist"}}"#,
    );

    assert_parse_failure(
        &project
            .command()
            .args(["--build", "tsconfig.json", "--showConfig"])
            .current_dir(&project.path)
            .output()
            .expect("build showConfig rejection starts"),
        6387,
        "Compiler option 'showConfig' may not be used with '--build'.",
    );
}

#[test]
fn show_config_project_malformed_config_stays_fail_closed() {
    let project = ScratchDirectory::new();
    project.write("src/main.ts", "export const answer = 42;\n");
    project.write(
        "broken/tsconfig.json",
        r#"{"files":["../src/main.ts"],"compilerOptions":{"outDir":"dist""#,
    );

    let output = project
        .command()
        .args(["--showConfig", "-p", "broken"])
        .current_dir(&project.path)
        .output()
        .expect("malformed config probe starts");

    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert!(stderr(&output).is_empty());
    let text = stdout(&output);
    assert!(text.starts_with("error TS"), "{text}");
    assert!(!text.contains("compilerOptions"), "{text}");
}

#[test]
fn direct_mode_preserves_its_option_surface() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", include_str!("fixtures/hello.ts"));

    let consumed = project
        .command()
        .args([
            "--ignoreConfig",
            "hello.ts",
            "--strict",
            "--pretty",
            "false",
        ])
        .current_dir(&project.path)
        .output()
        .expect("direct compile starts");
    assert_success(&consumed, "direct compile with consumed options");

    let rejected = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--diagnostics"])
        .current_dir(&project.path)
        .output()
        .expect("direct rejection starts");
    assert_not_implemented(&rejected, "diagnostics");

    let unset_watch = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--watch", "null"])
        .current_dir(&project.path)
        .output()
        .expect("direct null watch starts");
    assert_not_implemented(&unset_watch, "watch");
}

#[test]
fn tsc_direct_emits_declaration_for_single_root() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", "export const value: number = 1;\n");

    let output = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--declaration"])
        .current_dir(&project.path)
        .output()
        .expect("direct declaration compile starts");

    assert_success(&output, "direct declaration compile");
    assert!(stderr(&output).is_empty(), "{}", stderr(&output));
    assert!(!stdout(&output).contains("error TS"), "{}", stdout(&output));
    let javascript =
        fs::read_to_string(project.path.join("hello.js")).expect("javascript output is written");
    assert_eq!(javascript, "export const value = 1;\n");
    let declaration =
        fs::read_to_string(project.path.join("hello.d.ts")).expect("declaration output is written");
    assert_eq!(declaration, "export declare const value: number;\n");
}

#[test]
fn tsc_direct_emits_source_map_trailer() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", "export const value: number = 1;\n");

    let output = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--sourceMap"])
        .current_dir(&project.path)
        .output()
        .expect("direct source map compile starts");

    assert_success(&output, "direct source map compile");
    let javascript =
        fs::read_to_string(project.path.join("hello.js")).expect("javascript output is written");
    assert!(
        javascript.ends_with("//# sourceMappingURL=hello.js.map"),
        "{javascript}"
    );
    let map_text =
        fs::read_to_string(project.path.join("hello.js.map")).expect("map output is written");
    let map: serde_json::Value = serde_json::from_str(&map_text).expect("map is valid JSON");
    assert_eq!(map["version"], 3);
    assert_eq!(map["file"], "hello.js");
    assert_eq!(map["sources"], serde_json::json!(["hello.ts"]));
    assert_eq!(map["names"], serde_json::json!([]));
}

#[test]
fn tsc_direct_emits_combined_artifacts_without_declaration_map() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", "export const value: number = 1;\n");

    let output = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--declaration", "--sourceMap"])
        .current_dir(&project.path)
        .output()
        .expect("direct combined compile starts");

    assert_success(&output, "direct combined compile");
    assert!(project.path.join("hello.js").is_file());
    assert!(project.path.join("hello.d.ts").is_file());
    assert!(project.path.join("hello.js.map").is_file());
    assert!(
        !project.path.join("hello.d.ts.map").exists(),
        "declarationMap stays off unless requested"
    );
    let declaration =
        fs::read_to_string(project.path.join("hello.d.ts")).expect("declaration output is written");
    assert!(!declaration.contains("sourceMappingURL"), "{declaration}");
}

#[test]
fn tsc_direct_compiles_multi_root_program() {
    let project = ScratchDirectory::new();
    project.write("a.ts", "export const value = 1;\n");
    project.write(
        "b.ts",
        "import { value } from \"./a\";\nexport const doubled = value * 2;\n",
    );

    let output = project
        .command()
        .args(["--ignoreConfig", "a.ts", "b.ts"])
        .current_dir(&project.path)
        .output()
        .expect("direct multi-root compile starts");

    assert_success(&output, "direct multi-root compile");
    assert!(!stdout(&output).contains("error TS"), "{}", stdout(&output));
    assert!(project.path.join("a.js").is_file());
    assert!(project.path.join("b.js").is_file());
    let imported = fs::read_to_string(project.path.join("b.js")).expect("b.js is written");
    assert!(imported.contains("import { value }"), "{imported}");
    assert!(imported.contains("doubled"), "{imported}");
}

#[test]
fn tsc_direct_multi_root_reports_errors_and_still_emits() {
    let project = ScratchDirectory::new();
    project.write("a.ts", "export const value = 1;\n");
    project.write("bad.ts", "export const broken: string = 1;\n");

    let output = project
        .command()
        .args(["--ignoreConfig", "a.ts", "bad.ts"])
        .current_dir(&project.path)
        .output()
        .expect("direct multi-root error compile starts");

    assert_eq!(
        output.status.code(),
        Some(2),
        "exit: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout(&output),
        stderr(&output)
    );
    assert!(stdout(&output).contains("bad.ts"), "{}", stdout(&output));
    assert!(
        project.path.join("a.js").is_file(),
        "present roots still emit by default"
    );
    assert!(project.path.join("bad.js").is_file());
}

#[test]
fn tsc_direct_reports_missing_root_like_typescript() {
    let project = ScratchDirectory::new();
    project.write("a.ts", "export const value = 1;\n");

    let output = project
        .command()
        .args(["--ignoreConfig", "a.ts", "missing.ts", "--declaration"])
        .current_dir(&project.path)
        .output()
        .expect("direct missing-root compile starts");

    assert_eq!(output.status.code(), Some(2));
    let out = stdout(&output);
    assert!(
        out.contains("error TS6053: File 'missing.ts' not found."),
        "{out}"
    );
    assert!(out.contains("Root file specified for compilation"), "{out}");
    assert!(project.path.join("a.js").is_file());
    assert!(project.path.join("a.d.ts").is_file());
}

#[test]
fn tsc_direct_places_artifacts_under_out_dir() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", "export const value: number = 1;\n");

    let output = project
        .command()
        .args([
            "--ignoreConfig",
            "hello.ts",
            "--declaration",
            "--sourceMap",
            "--outDir",
            "out",
        ])
        .current_dir(&project.path)
        .output()
        .expect("direct outDir compile starts");

    assert_success(&output, "direct outDir compile");
    let javascript = fs::read_to_string(project.path.join("out/hello.js"))
        .expect("outDir javascript output is written");
    assert!(javascript.ends_with("//# sourceMappingURL=hello.js.map"));
    assert!(project.path.join("out/hello.d.ts").is_file());
    let map_text = fs::read_to_string(project.path.join("out/hello.js.map"))
        .expect("outDir map output is written");
    let map: serde_json::Value = serde_json::from_str(&map_text).expect("map is valid JSON");
    assert_eq!(map["sources"], serde_json::json!(["../hello.ts"]));
}

#[test]
fn tsc_direct_ignores_config_document_for_artifacts() {
    let project = ScratchDirectory::new();
    project.write("hello.ts", "export const value = 1;\n");
    project.write(
        "tsconfig.json",
        r#"{"compilerOptions":{"declaration":true,"outDir":"config-out"}}"#,
    );

    let output = project
        .command()
        .args(["--ignoreConfig", "hello.ts", "--sourceMap"])
        .current_dir(&project.path)
        .output()
        .expect("direct ignoreConfig compile starts");

    assert_success(&output, "direct ignoreConfig compile");
    assert!(
        !project.path.join("hello.d.ts").exists(),
        "the ignored config must not enable declarations"
    );
    assert!(
        !project.path.join("config-out").exists(),
        "the ignored config outDir must not be used"
    );
}

#[test]
fn tsc_direct_multi_root_no_emit_checks_without_writing() {
    let project = ScratchDirectory::new();
    project.write("a.ts", "export const value = 1;\n");
    project.write(
        "b.ts",
        "import { value } from \"./a\";\nexport const doubled = value * 2;\n",
    );

    let output = project
        .command()
        .args(["--ignoreConfig", "a.ts", "b.ts", "--noEmit"])
        .current_dir(&project.path)
        .output()
        .expect("direct multi-root noEmit compile starts");

    assert_success(&output, "direct multi-root noEmit compile");
    assert!(!stdout(&output).contains("error TS"), "{}", stdout(&output));
    assert!(!project.path.join("a.js").exists());
    assert!(!project.path.join("b.js").exists());
}

#[test]
fn mode_conflict_boundaries_fail_at_parse_time() {
    let project = ScratchDirectory::new();
    project.write("main.ts", "export const value = 1;\n");

    let run = |args: &[&str]| {
        project
            .command()
            .args(args)
            .current_dir(&project.path)
            .output()
            .expect("conflict command starts")
    };

    assert_parse_failure(
        &run(&["--dry", "main.ts"]),
        6388,
        "Compiler option 'dry' may only be used with '--build'.",
    );
    assert_parse_failure(
        &run(&["--build", "--target", "esnext"]),
        6387,
        "Compiler option 'target' may not be used with '--build'.",
    );
    assert_parse_failure(
        &run(&["-p", "tsconfig.json", "main.ts"]),
        5042,
        "Option 'project' cannot be mixed with source files on a command line.",
    );
    assert_parse_failure(
        &run(&["--build", "--clean", "--verbose"]),
        6370,
        "Options 'clean' and 'verbose' cannot be combined.",
    );
}

fn bamts_binary() -> &'static str {
    env!("CARGO_BIN_EXE_bamts")
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/hello.ts")
}

fn assert_success(output: &Output, command: &str) {
    assert!(
        output.status.success(),
        "{command} failed with {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

struct ExecutionOutput {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    exit_code: i64,
}

fn assert_execution_success(output: &ExecutionOutput, command: &str) {
    assert_eq!(
        output.exit_code,
        0,
        "{command} failed with exit code {}\nstdout:\n{}\nstderr:\n{}",
        output.exit_code,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn wait_for_output(mut child: Child, command: &str) -> Output {
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        match child.try_wait() {
            Ok(Some(_)) => return child.wait_with_output().expect("finished child output"),
            Ok(None) if Instant::now() < deadline => thread::sleep(Duration::from_millis(10)),
            Ok(None) => {
                child.kill().expect("timed-out child is killed");
                let output = child.wait_with_output().expect("timed-out child output");
                panic!(
                    "{command} exceeded 120 seconds\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            Err(error) => panic!("could not wait for {command}: {error}"),
        }
    }
}

fn framed(payload: &[u8]) -> Vec<u8> {
    let mut frame = format!("Content-Length: {}\r\n\r\n", payload.len()).into_bytes();
    frame.extend_from_slice(payload);
    frame
}

fn decode_frames(bytes: &[u8]) -> Vec<serde_json::Value> {
    const MAX_FRAME_BYTES: usize = 32 * 1024 * 1024;
    let mut offset = 0;
    let mut responses = Vec::new();
    while offset < bytes.len() {
        let header_end = bytes[offset..]
            .windows(4)
            .position(|window| window == b"\r\n\r\n")
            .map(|position| offset + position)
            .expect("API response has a complete header");
        let header =
            std::str::from_utf8(&bytes[offset..header_end]).expect("API response header is UTF-8");
        let length = header
            .lines()
            .find_map(|line| {
                let (name, value) = line.split_once(':')?;
                name.eq_ignore_ascii_case("content-length")
                    .then(|| value.trim().parse::<usize>().expect("valid content length"))
            })
            .expect("API response declares content length");
        assert!(length <= MAX_FRAME_BYTES, "API response frame is bounded");
        let body_start = header_end + 4;
        let body_end = body_start
            .checked_add(length)
            .expect("frame length does not overflow");
        assert!(body_end <= bytes.len(), "API response body is complete");
        responses.push(
            serde_json::from_slice(&bytes[body_start..body_end])
                .expect("API response body is JSON"),
        );
        offset = body_end;
    }
    responses
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

struct ScratchDirectory {
    path: PathBuf,
}

impl ScratchDirectory {
    fn new() -> Self {
        let root = std::env::temp_dir();
        for _ in 0..128 {
            let index = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = root.join(format!("bamts-cli-test-{}-{index}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self { path },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("could not create `{}`: {error}", path.display()),
            }
        }
        panic!("could not allocate a unique CLI test directory");
    }

    fn write(&self, relative: &str, source: &str) {
        let path = self.path.join(relative);
        fs::create_dir_all(path.parent().expect("fixture path has a parent"))
            .expect("fixture directory is created");
        fs::write(path, source).expect("fixture source is written");
    }

    fn command(&self) -> Command {
        let mut command = Command::new(bamts_binary());
        command
            .env("BAMTS_CACHE_DIR", self.path.join("cache"))
            .env_remove("BAMTS_AOT_ENTRYPOINT");
        command
    }

    fn check(&self, entrypoint: &str) -> Output {
        self.check_from(".", entrypoint)
    }

    fn check_from(&self, directory: &str, entrypoint: &str) -> Output {
        self.command()
            .args(["--noEmit", "--pretty", "false", entrypoint])
            .current_dir(self.path.join(directory))
            .output()
            .expect("bamts type-check starts")
    }

    fn emit(&self, entrypoint: &str, output: &Path) -> Output {
        self.command()
            .args(["--pretty", "false", "--outFile"])
            .arg(output)
            .arg(entrypoint)
            .current_dir(&self.path)
            .output()
            .expect("bamts emit starts")
    }

    fn execute(&self, target: &str, entrypoint: &str, program_args: &[&str]) -> ExecutionOutput {
        let response = self.execute_response(target, entrypoint, program_args);
        assert!(
            response.get("error").is_none(),
            "compiler/execute returned an error: {response}"
        );
        let result = response["result"]
            .as_object()
            .expect("compiler/execute returns an object");
        ExecutionOutput {
            stdout: result["stdout"]
                .as_str()
                .expect("execution stdout is text")
                .as_bytes()
                .to_vec(),
            stderr: result["stderr"]
                .as_str()
                .expect("execution stderr is text")
                .as_bytes()
                .to_vec(),
            exit_code: result["exitCode"]
                .as_i64()
                .expect("execution exit code is an integer"),
        }
    }

    fn execute_response(
        &self,
        target: &str,
        entrypoint: &str,
        program_args: &[&str],
    ) -> serde_json::Value {
        let mut service_args = vec![
            "run".to_owned(),
            "--target".to_owned(),
            target.to_owned(),
            entrypoint.to_owned(),
        ];
        if !program_args.is_empty() {
            service_args.push("--".to_owned());
            service_args.extend(program_args.iter().map(|argument| (*argument).to_owned()));
        }
        let requests = [
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": { "root": self.path },
            }),
            serde_json::json!({
                "jsonrpc": "2.0",
                "id": 2,
                "method": "compiler/execute",
                "params": { "args": service_args },
            }),
        ];
        let mut input = Vec::new();
        for request in requests {
            let payload = serde_json::to_vec(&request).expect("API request serializes");
            input.extend(framed(&payload));
        }

        let mut child = self
            .command()
            .arg("--api")
            .current_dir(&self.path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("bamts API child starts");
        child
            .stdin
            .take()
            .expect("API child stdin is piped")
            .write_all(&input)
            .expect("API requests are written");
        let output = wait_for_output(child, "bamts --api");
        assert_success(&output, "bamts --api");
        let responses = decode_frames(&output.stdout);
        assert_eq!(responses.len(), 2, "initialize and execute both respond");
        assert!(
            responses[0].get("error").is_none(),
            "initialize returned an error: {}",
            responses[0]
        );
        responses.into_iter().nth(1).expect("execute response")
    }
}

impl Drop for ScratchDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
