from __future__ import annotations

import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time
from typing import cast


def mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise TypeError("expected string-key mapping")
    return cast(dict[str, object], value)


def sequence(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected list")
    return cast(list[object], value)


def string(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("expected string")
    return value


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


workspace = Path.cwd()
proof = workspace / "proof/ci-tools/bamti-interleaved-baseline-r31"
source = workspace / "source"
output = Path(os.environ["RUNNER_TEMP"]) / "bamti-interleaved-baseline-r31"
output.mkdir(exist_ok=False)
manifest = mapping(json.loads((proof / "manifest.json").read_text(encoding="utf-8")))
assert sha((workspace / "proof/.github/workflows/bamti-interleaved-baseline-r31.yml").read_bytes()) == manifest["workflow_sha256"]
for path, expected in mapping(manifest["proof_sha256"]).items():
    assert sha((proof / path).read_bytes()) == expected, path
index = [mapping(item) for item in sequence(json.loads((proof / "source-index.json").read_text(encoding="utf-8")))]
assert len(index) == 1609
base_paths = {string(entry["path"]) for entry in index}
authored = [mapping(item) for item in sequence(json.loads((proof / "authored.json").read_text(encoding="utf-8")))]
assert len(authored) == 4
changed_paths = {string(item["path"]) for item in authored}
for item in authored:
    assert sha(string(item["content"]).encode()) == item["sha256"]
environment: dict[str, str] = dict(os.environ)
environment.update(
    CARGO_TARGET_DIR=str(Path(os.environ["RUNNER_TEMP"]) / "bamti-interleaved-target-r31"),
    CARGO_BUILD_JOBS="4",
    CARGO_INCREMENTAL="0",
    RUSTC_WRAPPER="",
    RUSTC_WORKSPACE_WRAPPER="",
)
results: list[dict[str, object]] = []
observations: list[str] = []
oracle_records: list[dict[str, object]] = []
candidate_hashes: dict[str, str] = {}
candidate_tree = ""
candidate_payload: dict[str, object] = {}
status = "incomplete"
restored = False
gates_passed = False


def identity(label: str, expected: dict[str, str] | None = None) -> dict[str, str]:
    expected_source = mapping(manifest["source"])
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    tree = subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=source, text=True).strip()
    assert head == expected_source["head"] and tree == expected_source["tree"]
    hashes: dict[str, str] = {}
    for entry in index:
        path = string(entry["path"])
        data = (source / path).read_bytes()
        assert entry["mode"] in ("100644", "100755")
        assert bool((source / path).stat().st_mode & 0o111) == (entry["mode"] == "100755"), path
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        hashes[path] = sha(data)
        if expected is None:
            assert blob == entry["sha"], path
        else:
            assert hashes[path] == expected[path], path
    allowed: set[str] = set()
    if expected is not None:
        allowed = expected.keys() - base_paths
        for path in allowed:
            hashes[path] = sha((source / path).read_bytes())
            assert hashes[path] == expected[path] and not (source / path).stat().st_mode & 0o111, path
        assert hashes == expected
    unknown = set(subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard"], cwd=source, text=True).splitlines())
    assert unknown == allowed, sorted(unknown)
    if expected is None:
        assert subprocess.check_output(["git", "diff", "--name-only"], cwd=source, text=True) == ""
    write_json(output / (label + "-source.json"), {"head": head, "base_tree": tree, "hashes": hashes})
    print("BAMTI_MEMO_SOURCE_IDENTITY " + json.dumps({"label": label, "head": head, "base_tree": tree, "verified_files": len(hashes), "index_sha256": sha((output / (label + "-source.json")).read_bytes())}), flush=True)
    return hashes


def run(name: str, command: list[str], expected: int = 0, required: tuple[str, ...] = (), timeout: int = 600) -> str:
    print("COMMAND " + name + " " + json.dumps(command), flush=True)
    started = time.monotonic()
    timed_out = False
    raw_exit: int | None
    text: str
    try:
        completed = subprocess.run(command, cwd=source, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace", check=False, timeout=timeout)
        raw_exit, text = completed.returncode, completed.stdout
    except subprocess.TimeoutExpired as error:
        timed_out = True
        raw_exit = None
        captured = error.stdout
        text = captured.decode("utf-8", errors="replace") if isinstance(captured, bytes) else captured or ""
    accepted = not timed_out and raw_exit == expected and all(marker in text for marker in required)
    entry: dict[str, object] = {"name": name, "command": command, "raw_exit": raw_exit, "expected_exit": expected, "timed_out": timed_out, "accepted": accepted, "seconds": time.monotonic() - started, "log_sha256": sha(text.encode())}
    (output / (name + ".log")).write_text(text, encoding="utf-8")
    results.append(entry)
    write_json(output / "partial-results.json", {"results": results, "observations": observations, "oracle_records": oracle_records})
    print(text, end="", flush=True)
    print("BAMTI_MEMO_COMMAND_RESULT " + json.dumps(entry, sort_keys=True), flush=True)
    if not accepted:
        raise RuntimeError("unexpected command outcome: " + name)
    return text


def test(name: str, filter_name: str, required: tuple[str, ...] = (), exact: bool = True, expected: int = 0) -> str:
    command = ["cargo", "test", "--locked", "-p", "bamts-compiler", "--lib", "--", filter_name]
    if exact:
        command.append("--exact")
    command.extend(["--nocapture", "--test-threads=1"])
    return run(name, command, expected=expected, required=required)


def freeze_tree() -> str:
    index_environment = dict(environment)
    index_environment["GIT_INDEX_FILE"] = str(output / "candidate.git-index")
    subprocess.run(["git", "read-tree", "HEAD"], cwd=source, env=index_environment, check=True)
    subprocess.run(["git", "add", "--", *sorted(changed_paths)], cwd=source, env=index_environment, check=True)
    return subprocess.check_output(["git", "write-tree"], cwd=source, env=index_environment, text=True).strip()


def emit_payload() -> dict[str, object]:
    files: list[dict[str, object]] = []
    for path in sorted(changed_paths):
        data = (source / path).read_bytes()
        files.append({
            "path": path,
            "mode": "100644",
            "sha256": sha(data),
            "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
            "content": data.decode("utf-8"),
        })
    payload = json.dumps(files, ensure_ascii=False, separators=(",", ":")).encode()
    packed = gzip.compress(payload, compresslevel=9, mtime=0)
    (output / "candidate-files.json").write_bytes(payload)
    (output / "candidate-files.json.gz").write_bytes(packed)
    encoded = base64.b64encode(packed).decode("ascii")
    chunks = [encoded[start:start + 16384] for start in range(0, len(encoded), 16384)]
    summary: dict[str, object] = {
        "tree": candidate_tree,
        "files": [{key: value for key, value in file.items() if key != "content"} for file in files],
        "payload_sha256": sha(payload),
        "gzip_sha256": sha(packed),
        "gzip_bytes": len(packed),
        "chunks": len(chunks),
    }
    print("BAMTI_MEMO_CANDIDATE_PAYLOAD " + json.dumps(summary, sort_keys=True), flush=True)
    for part, chunk in enumerate(chunks):
        print("BAMTI_MEMO_CANDIDATE_CHUNK " + json.dumps({"part": part, "data": chunk}), flush=True)
    return summary


try:
    original_hashes = identity("initial")
    assert run("rust-version", ["rustc", "--version"]).startswith("rustc 1.97.1 ")
    assert run("node-version", ["node", "--version"]).strip() == "v24.18.0"
    run("npm-pinned-typescript", ["npm", "ci"])
    for item in authored:
        path = string(item["path"])
        destination = source / path
        if path.endswith("/relations.rs"):
            original = destination.read_text(encoding="utf-8")
            assert original.endswith("\n}\n")
            assert string(item["content"]).startswith(original.rsplit("\n}", 1)[0])
        elif path.endswith("/tests.rs"):
            assert string(item["content"]).startswith(destination.read_text(encoding="utf-8"))
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(string(item["content"]), encoding="utf-8")
    candidate_hashes = dict(original_hashes)
    for item in authored:
        candidate_hashes[string(item["path"])] = string(item["sha256"])
    identity("frozen-test-only", candidate_hashes)
    candidate_tree = freeze_tree()
    candidate_payload = emit_payload()
    native = run("native-typescript-oracle", ["node", str(proof / "native-oracle.mjs"), str(source)])
    for line in native.splitlines():
        if line.startswith("TYPESCRIPT_MEMO_ORACLE "):
            record = mapping(json.loads(line.removeprefix("TYPESCRIPT_MEMO_ORACLE ")))
            assert record["accepted"] is True and record["typescript"] == "7.0.2" and record["node"] == "v24.18.0"
            fixture = "crates/bamts-compiler/src/checker/fixtures/" + string(record["id"])
            assert record["source_sha256"] == candidate_hashes[fixture]
            oracle_records.append(record)
    assert len(oracle_records) == 2
    run("compile-frozen-regressions", ["cargo", "test", "--locked", "-p", "bamts-compiler", "--lib", "--no-run"], timeout=1500)
    interleaved = test(
        "interleaved-current-baseline",
        "checker::relations::tests::saturated_memo_preserves_bounded_interleaved_reuse",
        required=("test result: FAILED. 0 passed; 1 failed", "bounded interleaving recomputed shared children:"),
        expected=101,
    )
    records = [match.group(0) for match in re.finditer(r"MEMO_INTERLEAVED graph=\d+ compatible=(?:true|false) computed=\d+ clean=\d+ contextual=\d+", interleaved)]
    assert len(records) == 128
    assert {int(record.split()[1].split("=")[1]) for record in records} == set(range(128))
    assert all("compatible=true" in record and "clean=4096 contextual=4096" in record for record in records)
    assert any(int(record.split()[3].split("=")[1]) >= 100 for record in records)
    observations.extend(records)
    test("external-adjacent-diamond-control", "checker::relations::tests::saturated_memo_still_shares_nested_comparisons", required=("test result: ok. 1 passed",))
    test("external-alias-view-control", "checker::relations::tests::alias_repeat_hits_alias_memo_not_expanded_view", required=("test result: ok. 1 passed",))
    test("incompatible-leaf-control", "checker::relations::tests::saturated_shared_graph_rejects_incompatible_leaf", required=("test result: ok. 1 passed",))
    test("source-assignment-controls", "checker::tests::source_assignment_after_", required=("test result: ok. 2 passed",), exact=False)
    churn = test("current-churn-observer", "checker::relations::tests::observe_shared_graph_with_intervening_cache_churn", required=("test result: ok. 1 passed",))
    churn_records = [match.group(0) for match in re.finditer(r"MEMO_CHURN depth=\d+ compatible=(?:true|false) computed=\d+ clean=\d+ contextual=\d+", churn)]
    assert len(churn_records) == 3
    assert {int(record.split()[1].split("=")[1]) for record in churn_records} == {2, 4, 6}
    observations.extend(churn_records)
    identity("frozen-test-only-after", candidate_hashes)
    assert freeze_tree() == candidate_tree
    status = "Authentic unchanged-current-source interleaving RED and adjacent/native/alias controls recorded. Test-only snapshot; no source repair or general complexity claim."

finally:
    subprocess.run(["git", "restore", "--worktree", "--", "."], cwd=source, check=True)
    for item in authored:
        path = string(item["path"])
        if path not in base_paths:
            (source / path).unlink(missing_ok=True)
    identity("final-original")
    restored = True
    report = {"schema": 1, "status": status, "manifest": manifest, "candidate_tree": candidate_tree, "candidate_payload": candidate_payload, "results": results, "observations": observations, "oracle_records": oracle_records, "source_restored": restored, "source_gates_passed": gates_passed, "publication_eligible": False}
    write_json(output / "results.json", report)
    print("BAMTI_MEMO_FINAL_REPORT " + json.dumps(report, sort_keys=True), flush=True)
