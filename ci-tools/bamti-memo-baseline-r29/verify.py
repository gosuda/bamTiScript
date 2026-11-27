from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
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
proof = workspace / "proof/ci-tools/bamti-memo-baseline-r29"
source = workspace / "source"
output = Path(os.environ["RUNNER_TEMP"]) / "bamti-memo-baseline-r29"
output.mkdir(exist_ok=False)
manifest = mapping(json.loads((proof / "manifest.json").read_text(encoding="utf-8")))
assert sha((workspace / "proof/.github/workflows/bamti-memo-baseline-r29.yml").read_bytes()) == manifest["workflow_sha256"]
for path, expected in mapping(manifest["proof_sha256"]).items():
    assert sha((proof / path).read_bytes()) == expected, path
index = [mapping(item) for item in sequence(json.loads((proof / "source-index.json").read_text(encoding="utf-8")))]
assert len(index) == 1609
base_paths = {string(entry["path"]) for entry in index}
authored = [mapping(item) for item in sequence(json.loads((proof / "authored.json").read_text(encoding="utf-8")))]
assert len(authored) == 4
for item in authored:
    assert sha(string(item["content"]).encode()) == item["sha256"]
environment: dict[str, str] = dict(os.environ)
environment.update(
    CARGO_TARGET_DIR=str(Path(os.environ["RUNNER_TEMP"]) / "bamti-memo-target-r29"),
    CARGO_BUILD_JOBS="4",
    CARGO_INCREMENTAL="0",
    RUSTC_WRAPPER="",
    RUSTC_WORKSPACE_WRAPPER="",
)
results: list[dict[str, object]] = []
observations: list[str] = []
oracle_records: list[dict[str, object]] = []
baseline_hashes: dict[str, str] = {}
status = "incomplete"
restored = False


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


def test(name: str, filter_name: str, expected: int = 0, required: tuple[str, ...] = (), exact: bool = True) -> str:
    command = ["cargo", "test", "--locked", "-p", "bamts-compiler", "--lib", "--", filter_name]
    if exact:
        command.append("--exact")
    command.extend(["--nocapture", "--test-threads=1"])
    return run(name, command, expected=expected, required=required)


try:
    original_hashes = identity("initial")
    assert run("rust-version", ["rustc", "--version"]).startswith("rustc 1.97.1 ")
    assert run("node-version", ["node", "--version"]).strip() == "v24.18.0"
    run("npm-pinned-typescript", ["npm", "ci"])
    for item in authored:
        path = string(item["path"])
        destination = source / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(string(item["content"]), encoding="utf-8")
    baseline_hashes = dict(original_hashes)
    for item in authored:
        baseline_hashes[string(item["path"])] = string(item["sha256"])
    identity("instrumented-baseline-before-tests", baseline_hashes)
    native = run("native-typescript-oracle", ["node", str(proof / "native-oracle.mjs"), str(source)])
    for line in native.splitlines():
        if line.startswith("TYPESCRIPT_MEMO_ORACLE "):
            record = mapping(json.loads(line.removeprefix("TYPESCRIPT_MEMO_ORACLE ")))
            assert record["accepted"] is True and record["typescript"] == "7.0.2" and record["node"] == "v24.18.0"
            fixture = "crates/bamts-compiler/src/checker/fixtures/" + string(record["id"])
            assert record["source_sha256"] == baseline_hashes[fixture]
            oracle_records.append(record)
    assert len(oracle_records) == 2
    run("compile-frozen-regressions", ["cargo", "test", "--locked", "-p", "bamts-compiler", "--lib", "--no-run"], timeout=1500)
    red = test("saturation-baseline-red", "checker::relations::tests::saturated_memos_admit_shared_named_relations", expected=101, required=("shared relation work grew after saturation:", "1 failed", "MEMO_SATURATION compatible=true"))
    observations.extend(match.group(0) for match in re.finditer(r"MEMO_SATURATION compatible=(?:true|false) computed=\d+ clean=\d+ contextual=\d+", red))
    assert len(observations) == 1
    test("incompatible-leaf-control", "checker::relations::tests::saturated_shared_graph_rejects_incompatible_leaf", required=("test result: ok. 1 passed",))
    test("source-assignment-controls", "checker::tests::source_assignment_after_", required=("test result: ok. 2 passed",), exact=False)
    churn = test("unchanged-source-churn-observer", "checker::relations::tests::observe_shared_graph_with_intervening_cache_churn", required=("test result: ok. 1 passed",))
    churn_records = [match.group(0) for match in re.finditer(r"MEMO_CHURN depth=\d+ compatible=(?:true|false) computed=\d+ clean=\d+ contextual=\d+", churn)]
    assert len(churn_records) == 3
    assert {int(record.split()[1].split("=")[1]) for record in churn_records} == {2, 4, 6}
    observations.extend(churn_records)
    test("alias-view-positive-control", "checker::relations::tests::memo_returns_settled_alias_comparison_without_recompute", required=("test result: ok. 1 passed",))
    relations_path = source / "crates/bamts-compiler/src/checker/relations.rs"
    baseline_relations = relations_path.read_text(encoding="utf-8")
    cacheable = "let cacheable = self.is_structural(source) || self.is_structural(target);"
    assert baseline_relations.count(cacheable) == 1
    no_alias_memo = baseline_relations.replace(cacheable, "let cacheable = !matches!(self.table.get(source), Type::AppliedAlias { .. })\n            && (self.is_structural(source) || self.is_structural(target));")
    old_alias = (proof / "old-alias-test.txt").read_text(encoding="utf-8")
    strong_alias = (proof / "strong-alias-test.txt").read_text(encoding="utf-8")
    assert no_alias_memo.count(strong_alias) == 1
    weak_mutant = no_alias_memo.replace(strong_alias, old_alias)
    try:
        relations_path.write_text(weak_mutant, encoding="utf-8")
        variant_hashes = dict(baseline_hashes)
        variant_hashes["crates/bamts-compiler/src/checker/relations.rs"] = sha(weak_mutant.encode())
        identity("alias-mutant-old-control", variant_hashes)
        test("alias-mutant-old-computed-control", "checker::relations::tests::memo_returns_settled_alias_comparison_without_recompute", required=("test result: ok. 1 passed",))
        relations_path.write_text(no_alias_memo, encoding="utf-8")
        variant_hashes["crates/bamts-compiler/src/checker/relations.rs"] = sha(no_alias_memo.encode())
        identity("alias-mutant-new-control", variant_hashes)
        test("alias-mutant-view-counter-red", "checker::relations::tests::memo_returns_settled_alias_comparison_without_recompute", expected=101, required=("a settled alias comparison must not traverse the alias view again", "1 failed"))
    finally:
        relations_path.write_text(baseline_relations, encoding="utf-8")
        identity("instrumented-baseline-after-mutation", baseline_hashes)
    status = "Expected saturation RED and incompatible-leaf/binder/TypeScript controls completed on unchanged production behavior; bounded churn is observational. The old alias computation assertion passes when root alias memoization is bypassed, while the frozen view-step assertion fails. No cache policy repair has been applied."
finally:
    subprocess.run(["git", "restore", "--worktree", "--", "."], cwd=source, check=True)
    for item in authored:
        path = string(item["path"])
        if path not in base_paths:
            (source / path).unlink(missing_ok=True)
    identity("final-original")
    restored = True
    report = {"schema": 1, "status": status, "manifest": manifest, "results": results, "observations": observations, "oracle_records": oracle_records, "source_restored": restored, "publication_eligible": False}
    write_json(output / "results.json", report)
    print("BAMTI_MEMO_FINAL_REPORT " + json.dumps(report, sort_keys=True), flush=True)
