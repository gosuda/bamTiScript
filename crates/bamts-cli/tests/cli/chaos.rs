//! Reproducible real-process tests. No random seed is drawn from the host.

use super::*;
use std::fmt::Write as _;

const SEEDS: [u32; 8] = [0, 1, 2, 7, 42, 0x5eed, 0xdead_beef, u32::MAX];

fn reference_output(project: &ScratchDirectory, entrypoint: &str) -> Vec<u8> {
    verify_oracle_versions();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let compiler = root.join("node_modules/typescript/bin/tsc");
    assert!(
        compiler.is_file(),
        "run npm ci at the repository root before oracle E2E tests"
    );
    let mut compile = Command::new("node");
    compile
        .arg(compiler)
        .args([
            "--ignoreConfig",
            "--strict",
            "--target",
            "es2022",
            "--module",
            "commonjs",
            "--outDir",
            "oracle",
            entrypoint,
        ])
        .current_dir(&project.path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let output = wait_for_output(
        compile.spawn().expect("TypeScript oracle starts"),
        "TypeScript oracle",
    );
    assert_success(&output, "TypeScript oracle");
    let javascript = project
        .path
        .join("oracle")
        .join(Path::new(entrypoint).with_extension("js"));
    let child = Command::new("node")
        .arg(javascript)
        .current_dir(&project.path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Node oracle starts");
    let output = wait_for_output(child, "Node oracle");
    assert_success(&output, "Node oracle");
    assert!(
        output.stderr.is_empty(),
        "Node oracle stderr: {}",
        stderr(&output)
    );
    output.stdout
}

#[test]
fn oracle_versions_match_the_repository_pins() {
    verify_oracle_versions();
}

fn verify_oracle_versions() {
    static VERIFIED: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    VERIFIED.get_or_init(|| {
        let child = Command::new("node")
            .arg("--version")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Node oracle is installed");
        let node = wait_for_output(child, "Node version");
        assert_success(&node, "Node version");
        assert_eq!(
            stdout(&node).trim(),
            "v24.18.0",
            "select the repository-pinned Node on PATH"
        );
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let child = Command::new("node")
            .arg(root.join("node_modules/typescript/bin/tsc"))
            .arg("--version")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("TypeScript oracle is installed");
        let typescript = wait_for_output(child, "TypeScript version");
        assert_success(&typescript, "TypeScript version");
        assert_eq!(stdout(&typescript).trim(), "Version 7.0.2");
    });
}

#[test]
fn real_typescript_workloads_match_the_pinned_oracle_in_both_modes() {
    for (name, source) in [
        (
            "runtime-workload",
            include_str!("../fixtures/runtime-workload.ts"),
        ),
        (
            "optional-chain-continuations",
            include_str!("../fixtures/optional-chain-continuations.ts"),
        ),
    ] {
        let project = ScratchDirectory::new();
        project.write("main.ts", source);
        let expected = reference_output(&project, "main.ts");
        for mode in ["jit", "aot"] {
            let actual = project.execute(mode, "main.ts", &[]);
            assert_execution_success(&actual, mode);
            assert_eq!(actual.stdout, expected, "{name}, {mode}");
        }
    }
}

#[test]
fn seeded_typescript_control_flow_matches_independent_arithmetic_and_node() {
    for seed in SEEDS {
        let mut state = seed;
        let mut source =
            String::from("declare const process: { stdout: { write(text: string): void } };\n");
        let mut expected = String::new();
        for case in 0..16 {
            let mut next = || {
                state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                state
            };
            let initial = next() % 997;
            let factor = next() % 8 + 2;
            let addend = next() % 31 + 1;
            let divisor = next() % 6 + 2;
            let iterations = next() % 24 + 8;
            writeln!(source, "function case{case}(): number {{ let value: number = {initial}; for (let i = 0; i < {iterations}; i++) {{ try {{ if (i % {divisor} === 0) {{ continue; }} value = (value * {factor} + {addend}) % 10007; }} finally {{ value = (value + 7) % 10007; }} }} return value; }} process.stdout.write('{seed}:{case}:' + case{case}() + '\\n');").expect("write generated TypeScript");
            let mut value = initial;
            for index in 0..iterations {
                if index % divisor != 0 {
                    value = (value * factor + addend) % 10007;
                }
                value = (value + 7) % 10007;
            }
            writeln!(expected, "{seed}:{case}:{value}").expect("write independent result");
        }
        let project = ScratchDirectory::new();
        project.write("main.ts", &source);
        assert_eq!(
            reference_output(&project, "main.ts"),
            expected.as_bytes(),
            "oracle seed={seed}\n{source}"
        );
        for mode in ["jit", "aot"] {
            let actual = project.execute(mode, "main.ts", &[]);
            assert_execution_success(&actual, mode);
            assert_eq!(
                actual.stdout,
                expected.as_bytes(),
                "seed={seed}, mode={mode}\n{source}"
            );
        }
    }
}

#[test]
fn large_typescript_output_survives_real_api_backpressure() {
    let project = ScratchDirectory::new();
    project.write(
        "main.ts",
        "for (let i = 0; i < 4096; i++) { process.stdout.write('0123456789abcdef'.repeat(8)); }\n",
    );
    let expected = "0123456789abcdef".repeat(8 * 4096);
    for mode in ["jit", "aot"] {
        let output = project.execute(mode, "main.ts", &[]);
        assert_execution_success(&output, mode);
        assert_eq!(
            output.stdout,
            expected.as_bytes(),
            "{mode}: 512 KiB response must not fill a pipe and hang"
        );
    }
}

#[test]
fn seeded_malformed_json_and_fragmentation_preserve_api_recovery() {
    let malformed: [(&[u8], i64); 6] = [
        (b"{", -32700),
        (b"\xff", -32700),
        (b"null", -32600),
        (b"[]", -32600),
        (br#"{"method":1}"#, -32600),
        (br#"{"id":true,"method":"compiler/version"}"#, -32600),
    ];
    for seed in SEEDS {
        let project = ScratchDirectory::new();
        let mut state = seed;
        let mut input = Vec::new();
        let mut errors = Vec::new();
        for id in 1..=12 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let (payload, code) = malformed[(state as usize) % malformed.len()];
            input.extend(framed(payload));
            input.extend(framed(
                &serde_json::to_vec(&serde_json::json!({
                    "jsonrpc":"2.0", "id":id, "method":"compiler/version"
                }))
                .expect("version request serializes"),
            ));
            errors.push(code);
        }
        let mut child = project
            .command()
            .arg("--api")
            .current_dir(&project.path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("real API child starts");
        let mut stdin = child.stdin.take().expect("piped stdin");
        let mut offset = 0;
        while offset < input.len() {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let end = (offset + (state as usize % 17) + 1).min(input.len());
            stdin
                .write_all(&input[offset..end])
                .expect("fragment is written");
            offset = end;
        }
        drop(stdin);
        let output = wait_for_output(child, "seeded malformed API frames");
        assert_success(&output, "seeded malformed API frames");
        let responses = decode_frames(&output.stdout);
        assert_eq!(responses.len(), 24, "seed={seed}: {responses:?}");
        for (index, code) in errors.iter().enumerate() {
            assert_eq!(responses[index * 2]["id"], serde_json::Value::Null);
            assert_eq!(responses[index * 2]["error"]["code"], *code, "seed={seed}");
            assert_eq!(responses[index * 2 + 1]["id"], index + 1, "seed={seed}");
            assert!(
                responses[index * 2 + 1]["result"]["version"].is_string(),
                "seed={seed}"
            );
        }
    }
}
