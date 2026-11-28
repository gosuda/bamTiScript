"""Build and compare two clean checkouts on one Linux 5.3+ host; not BH1 evidence.

Run with Python 3.11+ through uv:
  uv run --no-project python perf/compare_optimization.py \
      --baseline ../baseline --candidate . --output ../comparison

Instrumentation uses a disposable local clone of the baseline: only benchmark
examples, their manifest stanza, and three ignored tests are replaced. Both
caller checkouts remain unchanged. Baseline production source must not change.
Each revision has an isolated target directory and must produce fresh, distinct
benchmark executables. Both builds finish before measurement. Raw subprocess
output and an incomplete report survive failure; only a fully validated run
receives status "complete".
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import re
import select
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Literal, cast

RUST_VERSION = "1.97.1"
PROFILES = (
    "profile_property_cache_hits",
    "profile_shaped_gc",
    "profile_function_site_initialization",
)
EXAMPLES = (
    "crates/bamts-compiler/examples/compiler_perf.rs",
    "crates/bamts/examples/run_perf.rs",
)
RUNTIME_TESTS = "crates/bamts-runtime/src/tests.rs"
FACADE_MANIFEST = "crates/bamts/Cargo.toml"
Side = Literal["baseline", "candidate"]
Role = Literal["warmup", "measurement", "diagnostic"]


@dataclass(frozen=True)
class Binary:
    side: Side
    name: str
    path: str
    sha256: str


@dataclass(frozen=True)
class Case:
    name: str
    binary: str
    arguments: tuple[str, ...]
    kind: Literal["compiler", "runtime", "execution"]
    expected_stdout: str = ""


@dataclass(frozen=True)
class Observation:
    timings_ns: dict[str, int]
    invariants: dict[str, int | str]
    details: dict[str, int]


@dataclass(frozen=True)
class Sample:
    case: str
    side: Side
    role: Role
    round: int
    order: int
    observation: Observation
    stdout_sha256: str
    stderr_sha256: str
    log_prefix: str


@dataclass(frozen=True)
class Summary:
    case: str
    side: Side
    metric: str
    count: int
    median_ns: float
    minimum_ns: int
    maximum_ns: int


@dataclass(frozen=True)
class Report:
    schema: str
    scope: str
    status: str
    revisions: dict[str, str]
    host: dict[str, object]
    build_environment: dict[str, str]
    rounds: int
    instrumentation: dict[str, str]
    fixture_sha256: dict[str, str] | None = None
    binaries: tuple[Binary, ...] = ()
    samples: tuple[Sample, ...] = ()
    summaries: tuple[Summary, ...] = ()
    error: str | None = None


class ComparisonError(RuntimeError):
    """A build, output, or comparison invariant failed."""


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ComparisonError("expected a JSON object with string keys")
    return cast(dict[str, object], value)


def json_object(text: str) -> dict[str, object]:
    value: object = json.loads(text)
    return mapping(value)


def natural(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ComparisonError(f"expected a nonnegative integer, got {value!r}")
    return value


def git(root: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ["git", *arguments], cwd=root, text=True, timeout=30
    ).strip()


def source_revision(root: Path) -> str:
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ComparisonError(f"checkout must be clean: {root}")
    return git(root, "rev-parse", "HEAD")


def profile_function(source: str, name: str) -> str:
    marker = (
        '#[test]\n#[ignore = "development-host performance measurement"]\n'
        f"fn {name}() {{"
    )
    if source.count(marker) != 1:
        raise ComparisonError(f"expected one ignored measurement function: {name}")
    start = source.index(marker)
    end = source.find("\n#[test]", start + len(marker))
    if end < 0:
        raise ComparisonError(f"missing measurement function boundary: {name}")
    return source[start:end].strip() + "\n"


def prepare_baseline(
    baseline: Path, candidate: Path, execution_only: bool = False
) -> dict[str, str]:
    wanted = (
        tuple(p for p in EXAMPLES if p.endswith("run_perf.rs"))
        if execution_only
        else EXAMPLES
    )
    for relative in wanted:
        destination = baseline / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(candidate / relative, destination)
    manifest = baseline / FACADE_MANIFEST
    text = manifest.read_text(encoding="utf-8")
    data = tomllib.loads(text)
    examples: object = data.get("example", [])
    if not isinstance(examples, list):
        raise ComparisonError("example declarations must be an array")
    matching = [
        mapping(item)
        for item in cast(list[object], examples)
        if mapping(item).get("name") == "run_perf"
    ]
    if matching:
        if len(matching) != 1 or matching[0].get("required-features") != ["node-host"]:
            raise ComparisonError("unexpected existing run_perf example declaration")
    else:
        manifest.write_text(
            text
            + '\n[[example]]\nname = "run_perf"\nrequired-features = ["node-host"]\n',
            encoding="utf-8",
        )
    if execution_only:
        allowed = {*wanted, FACADE_MANIFEST}
    else:
        candidate_tests = (candidate / RUNTIME_TESTS).read_text(encoding="utf-8")
        baseline_tests = (baseline / RUNTIME_TESTS).read_text(encoding="utf-8")
        for name in PROFILES:
            replacement = profile_function(candidate_tests, name)
            if f"fn {name}()" in baseline_tests:
                previous = profile_function(baseline_tests, name)
                baseline_tests = baseline_tests.replace(previous, replacement, 1)
            else:
                baseline_tests += "\n" + replacement
        (baseline / RUNTIME_TESTS).write_text(baseline_tests, encoding="utf-8")
        allowed = {*EXAMPLES, FACADE_MANIFEST, RUNTIME_TESTS}
    changed = set(git(baseline, "diff", "--name-only").splitlines())
    untracked = set(
        git(baseline, "ls-files", "--others", "--exclude-standard").splitlines()
    )
    if not (changed | untracked) <= allowed:
        raise ComparisonError(
            "baseline production source changed during instrumentation"
        )
    return {relative: sha256(baseline / relative) for relative in sorted(allowed)}


def save(report: Report, output: Path) -> None:
    temporary = output / "comparison.pending.json"
    temporary.write_text(json.dumps(asdict(report), indent=2) + "\n", encoding="utf-8")
    temporary.replace(output / "comparison.json")


def logged(
    command: tuple[str, ...],
    cwd: Path,
    environment: dict[str, str],
    prefix: Path,
    deadline: float,
    maximum_seconds: float,
) -> int:
    """Capture a child group and reap it before returning or propagating failure.

    Requires Linux pidfds, normal SIGCHLD handling, and exclusive child reaping.
    """
    now = time.monotonic()
    expires_at = min(deadline, now + maximum_seconds)
    timeout = expires_at - now
    if timeout <= 0:
        raise ComparisonError("comparison exceeded its overall time budget")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prefix.with_suffix(".command.json").write_text(
        json.dumps({"arguments": command, "cwd": str(cwd)}, indent=2) + "\n",
        encoding="utf-8",
    )
    started = time.perf_counter_ns()
    with (
        prefix.with_suffix(".stdout.log").open("wb") as stdout,
        prefix.with_suffix(".stderr.log").open("wb") as stderr,
        subprocess.Popen(
            command,
            cwd=cwd,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            start_new_session=True,
        ) as process,
    ):
        try:
            pidfd = os.pidfd_open(process.pid)
            try:
                poller = select.poll()
                poller.register(pidfd, select.POLLIN)
                remaining = expires_at - time.monotonic()
                if remaining <= 0:
                    raise subprocess.TimeoutExpired(command, timeout)
                events = poller.poll(math.ceil(remaining * 1000))
                if not events:
                    raise subprocess.TimeoutExpired(command, timeout)
                if not (events[0][1] & select.POLLIN):
                    raise ComparisonError("unexpected process-exit notification")
                returncode = process.wait()
            finally:
                os.close(pidfd)
        finally:
            if process.returncode is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    process.kill()
                finally:
                    process.wait()
    elapsed = time.perf_counter_ns() - started
    if returncode != 0:
        raise ComparisonError(f"command exited {returncode}; see {prefix}.stderr.log")
    return elapsed


def artifact(
    stdout: Path, name: str, is_test: bool, target_root: Path, manifest: Path
) -> Path:
    paths: set[Path] = set()
    for line in stdout.read_text(encoding="utf-8").splitlines():
        message = json_object(line)
        if message.get("reason") != "compiler-artifact":
            continue
        target = mapping(message.get("target"))
        profile = mapping(message.get("profile"))
        executable = message.get("executable")
        if target.get("name") == name and profile.get("test") is is_test:
            if not isinstance(executable, str):
                continue
            if message.get("fresh") is not False:
                raise ComparisonError("Cargo reused a cached benchmark executable")
            manifest_path = message.get("manifest_path")
            if (
                not isinstance(manifest_path, str)
                or Path(manifest_path).resolve() != manifest.resolve()
            ):
                raise ComparisonError(
                    "Cargo artifact belongs to a different source checkout"
                )
            path = Path(executable).resolve(strict=True)
            if not path.is_relative_to(target_root.resolve()) or not path.is_file():
                raise ComparisonError(
                    "Cargo executable is outside its variant target directory"
                )
            paths.add(path)
    if len(paths) != 1:
        raise ComparisonError(
            f"expected one executable artifact for {name}, got {paths}"
        )
    return paths.pop()


def build(
    root: Path,
    side: Side,
    work: Path,
    output: Path,
    environment: dict[str, str],
    deadline: float,
    required_binaries: frozenset[str],
) -> tuple[Binary, ...]:
    targets = (
        (
            "compiler_perf",
            "build",
            "bamts-compiler",
            ("--example", "compiler_perf"),
            False,
        ),
        (
            "run_perf",
            "build",
            "bamts",
            ("--features", "node-host", "--example", "run_perf"),
            False,
        ),
        ("bamts_runtime", "test", "bamts-runtime", ("--lib", "--no-run"), True),
    )
    target_root = work / "target" / side
    build_environment = {
        **environment,
        "CARGO_TARGET_DIR": str(target_root),
        "CARGO_BUILD_BUILD_DIR": str(target_root),
        "RUSTC_WRAPPER": "",
        "RUSTC_WORKSPACE_WRAPPER": "",
    }
    binaries: list[Binary] = []
    for name, operation, package, arguments, is_test in targets:
        if name not in required_binaries:
            continue
        prefix = output / "build" / f"{side}-{name}"
        command = (
            "cargo",
            f"+{RUST_VERSION}",
            operation,
            "--locked",
            "--release",
            "-j",
            "1",
            "-p",
            package,
            *arguments,
            "--message-format=json",
        )
        print(f"Building {side} {name}", flush=True)
        logged(command, root, build_environment, prefix, deadline, 1200)
        executable = artifact(
            prefix.with_suffix(".stdout.log"),
            name,
            is_test,
            target_root,
            root / "crates" / package / "Cargo.toml",
        )
        destination = work / "bin" / side / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(executable, destination)
        binaries.append(Binary(side, name, str(destination), sha256(destination)))
    return tuple(binaries)


def compiler_observation(case: Case, stdout: str, stderr: str) -> Observation:
    if stderr:
        raise ComparisonError(f"unexpected compiler benchmark stderr: {stderr!r}")
    record = json_object(stdout)
    expected_fields = {
        "lookup": {"workload", "width", "operations", "elapsed_ns", "checksum"},
        "parse": {
            "workload",
            "bytes",
            "operations",
            "tokens",
            "elapsed_ns",
            "scan_ns",
            "parse_ns",
            "checksum",
        },
        "program": {
            "workload",
            "modules",
            "operations",
            "elapsed_ns",
            "scan_ns",
            "parse_ns",
            "check_ns",
            "total_ns",
            "checksum",
        },
    }
    workload = case.arguments[0]
    if set(record) != expected_fields[workload] or record["workload"] != workload:
        raise ComparisonError(f"unexpected compiler benchmark fields for {workload}")
    timings: dict[str, int] = {}
    invariants: dict[str, int | str] = {"workload": workload}
    for key, value in record.items():
        if key == "workload":
            continue
        number = natural(value)
        if key.endswith("_ns"):
            timings[key] = number
        else:
            invariants[key] = number
    repetitions = int(case.arguments[2])
    expected_operations = repetitions * 2 if workload == "lookup" else repetitions
    if invariants["operations"] != expected_operations:
        raise ComparisonError("compiler benchmark performed the wrong operation count")
    if workload == "lookup" and invariants["width"] != int(case.arguments[1]):
        raise ComparisonError("lookup width differs from requested work")
    if (
        workload == "parse"
        and invariants["checksum"] != int(case.arguments[1]) * repetitions
    ):
        raise ComparisonError("parser statement count differs from requested work")
    if workload == "program" and invariants["modules"] != 33:
        raise ComparisonError("loaded program must contain all 33 fixture modules")
    return Observation(timings, invariants, {})


def key_values(line: str) -> tuple[str, dict[str, int]]:
    parts = line.split()
    if not parts:
        raise ComparisonError("empty metric line")
    fields: dict[str, int] = {}
    for field in parts[1:]:
        match = re.fullmatch(r"([a-z_]+)=([0-9]+)", field)
        if match is None or match[1] in fields:
            raise ComparisonError(f"invalid or duplicate metric field: {field!r}")
        fields[match[1]] = int(match[2])
    return parts[0], fields


def runtime_observation(case: Case, stdout: str, stderr: str) -> Observation:
    if (
        f"test {case.arguments[0]} ... ok" not in stdout
        or len(re.findall(r"test result: ok\. 1 passed; 0 failed; 0 ignored;", stdout))
        != 1
    ):
        raise ComparisonError(
            "runtime measurement did not run exactly one passing test"
        )
    expected = {
        "runtime_cache": {
            "property_cache_get": {"iterations", "elapsed_ns", "checksum"},
            "property_cache_set": {"iterations", "elapsed_ns", "final_value"},
        },
        "runtime_gc": {
            "shaped_gc": {"objects", "collections", "elapsed_ns", "live_slots"}
        },
        "runtime_sites": {
            "function_sites": {
                "instructions",
                "iterations",
                "elapsed_ns",
                "sites_found",
                "site_bytes",
            }
        },
    }[case.name]
    lines = [key_values(line) for line in stderr.splitlines()]
    if len(lines) != len(expected) or {name for name, _ in lines} != set(expected):
        raise ComparisonError("unexpected runtime measurement output")
    timings: dict[str, int] = {}
    invariants: dict[str, int | str] = {}
    details: dict[str, int] = {}
    for name, fields in lines:
        if set(fields) != expected[name]:
            raise ComparisonError(f"unexpected fields for {name}")
        required = {
            "property_cache_get": {"iterations": 2_000_000},
            "property_cache_set": {"iterations": 2_000_000, "final_value": 1_999_999},
            "shaped_gc": {"objects": 10_000, "collections": 20},
            "function_sites": {
                "instructions": 100_000,
                "iterations": 100,
                "sites_found": 200,
            },
        }[name]
        if any(fields[key] != value for key, value in required.items()):
            raise ComparisonError(f"unexpected work count for {name}")
        for key, value in fields.items():
            if key == "elapsed_ns":
                timings[f"{name}_ns"] = value
            elif key == "site_bytes":
                details[key] = value
            else:
                invariants[f"{name}_{key}"] = value
    return Observation(timings, invariants, details)


def execution_observation(
    case: Case, stdout: str, stderr: str, diagnostic: bool
) -> Observation:
    if stdout != case.expected_stdout:
        raise ComparisonError(f"execution output mismatch for {case.name}: {stdout!r}")
    timings: dict[str, int] = {}
    if diagnostic:
        lines = stderr.splitlines()
        if len(lines) != 1:
            raise ComparisonError("expected one end-to-end diagnostic line")
        _, fields = key_values("profile " + lines[0])
        if (
            set(fields)
            != {
                "compile_ns",
                "scan_ns",
                "parse_ns",
                "check_ns",
                "frontend_ns",
                "run_ns",
                "modules",
            }
            or fields["modules"] != 1
        ):
            raise ComparisonError("unexpected end-to-end diagnostic fields")
        timings = {key: value for key, value in fields.items() if key.endswith("_ns")}
    elif stderr:
        raise ComparisonError(f"unexpected execution stderr: {stderr!r}")
    return Observation(timings, {"stdout": stdout}, {})


def observe(
    case: Case,
    binary: Binary,
    root: Path,
    output: Path,
    environment: dict[str, str],
    deadline: float,
    role: Role,
    round_number: int,
    order: int,
) -> Sample:
    prefix = (
        output
        / "samples"
        / f"{case.name}-{role}-{round_number:02}-{order}-{binary.side}"
    )
    arguments = case.arguments
    if role == "diagnostic":
        arguments = ("--profile", *arguments)
    elapsed = logged(
        (binary.path, *arguments), root, environment, prefix, deadline, 180
    )
    stdout_path = prefix.with_suffix(".stdout.log")
    stderr_path = prefix.with_suffix(".stderr.log")
    stdout = stdout_path.read_bytes().decode("utf-8")
    stderr = stderr_path.read_bytes().decode("utf-8")
    if case.kind == "compiler":
        observation = compiler_observation(case, stdout, stderr)
    elif case.kind == "runtime":
        observation = runtime_observation(case, stdout, stderr)
    else:
        observation = execution_observation(case, stdout, stderr, role == "diagnostic")
    observation = replace(
        observation,
        timings_ns={**observation.timings_ns, "process_wall_ns": elapsed},
    )
    return Sample(
        case.name,
        binary.side,
        role,
        round_number,
        order,
        observation,
        sha256(stdout_path),
        sha256(stderr_path),
        str(prefix.relative_to(output)),
    )


def cases(fixtures: Path) -> tuple[Case, ...]:
    runtime_arguments = ("--exact", "--ignored", "--nocapture", "--test-threads=1")
    return (
        Case(
            "compiler_lookup", "compiler_perf", ("lookup", "256", "20000"), "compiler"
        ),
        Case("compiler_parse", "compiler_perf", ("parse", "10000", "5"), "compiler"),
        Case(
            "compiler_program",
            "compiler_perf",
            ("program", str(fixtures / "graph/main.ts"), "5"),
            "compiler",
        ),
        Case(
            "runtime_cache",
            "bamts_runtime",
            ("tests::profile_property_cache_hits", *runtime_arguments),
            "runtime",
        ),
        Case(
            "runtime_gc",
            "bamts_runtime",
            ("tests::profile_shaped_gc", *runtime_arguments),
            "runtime",
        ),
        Case(
            "runtime_sites",
            "bamts_runtime",
            ("tests::profile_function_site_initialization", *runtime_arguments),
            "runtime",
        ),
        Case(
            "execution_properties",
            "run_perf",
            (str(fixtures / "property_loop.ts"),),
            "execution",
            "3600000\n",
        ),
        Case(
            "execution_allocations",
            "run_perf",
            (str(fixtures / "allocation_churn.ts"),),
            "execution",
            "5049901000\n",
        ),
    )


def summarize(samples: tuple[Sample, ...]) -> tuple[Summary, ...]:
    groups: dict[tuple[str, Side, str], list[int]] = {}
    for sample in samples:
        if sample.role != "measurement":
            continue
        for metric, value in sample.observation.timings_ns.items():
            groups.setdefault((sample.case, sample.side, metric), []).append(value)
    return tuple(
        Summary(
            case,
            side,
            metric,
            len(values),
            statistics.median(values),
            min(values),
            max(values),
        )
        for (case, side, metric), values in sorted(groups.items())
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, type=Path)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--rounds", type=int, default=6)
    parser.add_argument(
        "--execution-only",
        action="store_true",
        help="build and measure only the two compile-and-execute workloads",
    )
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error(
            "this runner requires Linux 5.3+ process descriptors and CPU affinity APIs"
        )
    baseline: Path = args.baseline.resolve(strict=True)
    candidate: Path = args.candidate.resolve(strict=True)
    output: Path = args.output.resolve()
    rounds: int = args.rounds
    execution_only: bool = args.execution_only
    if rounds < 6 or rounds % 2 != 0:
        parser.error("--rounds must be even and at least six")
    if baseline == candidate or any(
        output.is_relative_to(root) for root in (baseline, candidate)
    ):
        parser.error("use distinct checkouts and an output directory outside both")
    output.mkdir(parents=True, exist_ok=False)
    deadline = time.monotonic() + 55 * 60
    controls = {
        "CARGO_BUILD_JOBS": "1",
        "CARGO_INCREMENTAL": "0",
        "CARGO_PROFILE_RELEASE_OPT_LEVEL": "3",
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16",
        "CARGO_PROFILE_RELEASE_DEBUG": "0",
        "CARGO_PROFILE_RELEASE_LTO": "false",
    }
    environment = dict(os.environ)
    environment.pop("RUSTFLAGS", None)
    environment.pop("CARGO_ENCODED_RUSTFLAGS", None)
    environment.update(controls)
    environment.update({"NO_COLOR": "1", "RUST_BACKTRACE": "1", "TZ": "UTC"})
    report = Report(
        "bamts.optimization-comparison/v1",
        (
            "Same-host execution-only development comparison; not BH1 or "
            "product-completion evidence. Process wall time uses Linux pidfd readiness."
            if execution_only
            else (
                "Same-host development comparison; not BH1 or product-completion "
                "evidence. Process wall time uses Linux pidfd readiness."
            )
        ),
        "incomplete",
        {},
        {
            "platform": platform.platform(),
            "python": sys.version,
            "cpu_count": os.cpu_count(),
            "cpu_affinity": sorted(os.sched_getaffinity(0)),
            "load_before": os.getloadavg(),
        },
        controls,
        rounds,
        {},
    )
    save(report, output)
    try:
        revisions = {
            side: source_revision(root)
            for side, root in (("baseline", baseline), ("candidate", candidate))
        }
        tooling = Path(__file__).resolve().parent.parent
        revisions["tooling"] = git(tooling, "rev-parse", "HEAD")
        report = replace(report, revisions=revisions)
        save(report, output)
        for root in (baseline, candidate):
            pin = tomllib.loads(
                (root / "rust-toolchain.toml").read_text(encoding="utf-8")
            )
            if mapping(pin.get("toolchain")).get("channel") != RUST_VERSION:
                raise ComparisonError(f"both revisions must pin Rust {RUST_VERSION}")
        with tempfile.TemporaryDirectory(
            prefix="bamts-optimization-", dir=output.parent
        ) as temporary:
            work = Path(temporary)
            fixtures = work / "fixtures"
            selected_cases = tuple(
                case
                for case in cases(fixtures)
                if not execution_only or case.kind == "execution"
            )
            required_binaries = frozenset(case.binary for case in selected_cases)
            disposable_baseline = work / "baseline"
            logged(
                (
                    "git",
                    "clone",
                    "--quiet",
                    "--shared",
                    "--no-checkout",
                    "--",
                    str(baseline),
                    str(disposable_baseline),
                ),
                candidate,
                environment,
                output / "clone-baseline",
                deadline,
                120,
            )
            logged(
                ("git", "checkout", "--quiet", "--detach", revisions["baseline"]),
                disposable_baseline,
                environment,
                output / "checkout-baseline",
                deadline,
                120,
            )
            report = replace(
                report,
                instrumentation=prepare_baseline(
                    disposable_baseline, candidate, execution_only
                ),
            )
            save(report, output)
            logged(
                ("rustc", f"+{RUST_VERSION}", "--version", "--verbose"),
                candidate,
                environment,
                output / "rustc",
                deadline,
                30,
            )
            for side, root in cast(
                tuple[tuple[Side, Path], ...],
                (("baseline", disposable_baseline), ("candidate", candidate)),
            ):
                report = replace(
                    report,
                    binaries=(
                        *report.binaries,
                        *build(
                            root,
                            side,
                            work,
                            output,
                            environment,
                            deadline,
                            required_binaries,
                        ),
                    ),
                )
                save(report, output)
            logged(
                (
                    sys.executable,
                    str(candidate / "perf/generate_local.py"),
                    str(fixtures),
                ),
                candidate,
                environment,
                output / "generate-fixtures",
                deadline,
                30,
            )
            report = replace(
                report,
                fixture_sha256={
                    str(path.relative_to(fixtures)): sha256(path)
                    for path in sorted(fixtures.rglob("*"))
                    if path.is_file()
                },
            )
            save(report, output)
            available = {
                (binary.side, binary.name): binary for binary in report.binaries
            }
            expected_binaries = {
                (side, name)
                for side in ("baseline", "candidate")
                for name in required_binaries
            }
            if set(available) != expected_binaries or len(report.binaries) != len(
                expected_binaries
            ):
                raise ComparisonError(
                    "built executables do not match selected workloads"
                )
            for name in sorted(required_binaries):
                if (
                    available[("baseline", name)].sha256
                    == available[("candidate", name)].sha256
                ):
                    raise ComparisonError(
                        f"identical {name} binaries cannot measure a code change"
                    )
            for case in selected_cases:
                expected: dict[str, int | str] | None = None
                roles: tuple[Role, ...] = (
                    ("warmup", "diagnostic")
                    if case.kind == "execution"
                    else ("warmup",)
                )
                schedule: list[tuple[Role, int, tuple[Side, Side]]] = [
                    (role, 0, ("baseline", "candidate")) for role in roles
                ]
                schedule.extend(
                    (
                        "measurement",
                        number,
                        ("baseline", "candidate")
                        if number % 2
                        else ("candidate", "baseline"),
                    )
                    for number in range(1, rounds + 1)
                )
                for role, number, order in schedule:
                    for position, side in enumerate(order, 1):
                        sample = observe(
                            case,
                            available[(side, case.binary)],
                            candidate,
                            output,
                            environment,
                            deadline,
                            role,
                            number,
                            position,
                        )
                        if expected is None:
                            expected = sample.observation.invariants
                        if sample.observation.invariants != expected:
                            raise ComparisonError(
                                f"output invariants differ for {case.name} {side}"
                            )
                        report = replace(report, samples=(*report.samples, sample))
                        save(report, output)
                print(
                    f"Validated {case.name}: {rounds} counterbalanced rounds",
                    flush=True,
                )
        expected_counts: dict[Role, int] = {
            "measurement": 2 * rounds * len(selected_cases),
            "warmup": 2 * len(selected_cases),
            "diagnostic": 2 * sum(case.kind == "execution" for case in selected_cases),
        }
        if any(
            sum(sample.role == role for sample in report.samples) != count
            for role, count in expected_counts.items()
        ):
            raise ComparisonError("incomplete selected workloads")
        summaries = summarize(report.samples)
        if not summaries or any(summary.count != rounds for summary in summaries):
            raise ComparisonError("incomplete measurement groups")
        report = replace(
            report,
            status="complete",
            summaries=summaries,
            host={**report.host, "load_after": os.getloadavg()},
        )
        save(report, output)
        try:
            print("BEGIN_OPTIMIZATION_REPORT", flush=True)
            print(json.dumps(asdict(report), indent=2), flush=True)
            print("END_OPTIMIZATION_REPORT", flush=True)
        except BrokenPipeError:
            pass
    except (ComparisonError, OSError, ValueError, subprocess.SubprocessError) as error:
        save(replace(report, status="failed", error=str(error)), output)
        raise


if __name__ == "__main__":
    main()
