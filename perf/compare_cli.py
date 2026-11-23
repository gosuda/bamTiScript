"""Compare two release CLI binaries without producing BH1 gate evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import resource
import statistics
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class Sample:
    side: str
    iteration: int
    wall_ms: float
    user_ms: float
    system_ms: float
    stdout_sha256: str


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def measure(
    binary: Path,
    arguments: list[str],
    expected_stdout: bytes,
    timeout: float,
    side: str,
    iteration: int,
) -> Sample:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter_ns()
    result = subprocess.run(
        [str(binary), *arguments],
        stdin=subprocess.DEVNULL,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    elapsed = time.perf_counter_ns() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if result.returncode != 0:
        raise RuntimeError(
            f"{side} exited {result.returncode}: "
            f"{result.stderr.decode(errors='replace')}"
        )
    if result.stdout != expected_stdout or result.stderr:
        raise RuntimeError(
            f"{side} output mismatch: stdout={result.stdout!r}, "
            f"stderr={result.stderr!r}, expected stdout={expected_stdout!r}"
        )
    return Sample(
        side=side,
        iteration=iteration,
        wall_ms=elapsed / 1_000_000,
        user_ms=(after.ru_utime - before.ru_utime) * 1000,
        system_ms=(after.ru_stime - before.ru_stime) * 1000,
        stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
    )


def summarize(samples: list[Sample], side: str) -> dict[str, float]:
    selected = [sample for sample in samples if sample.side == side]
    walls = [sample.wall_ms for sample in selected]
    return {
        "median_wall_ms": statistics.median(walls),
        "min_wall_ms": min(walls),
        "max_wall_ms": max(walls),
        "median_user_ms": statistics.median(sample.user_ms for sample in selected),
        "median_system_ms": statistics.median(sample.system_ms for sample in selected),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--expected-stdout", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.repeats < 5:
        parser.error("--repeats must be at least 5")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    arguments: list[str] = args.arguments
    if arguments[:1] == ["--"]:
        arguments = arguments[1:]
    if not arguments:
        parser.error("provide the CLI arguments after --")
    binaries = {
        "baseline": args.baseline.resolve(strict=True),
        "candidate": args.candidate.resolve(strict=True),
    }
    expected_stdout = (
        args.expected_stdout.read_bytes() if args.expected_stdout is not None else b""
    )
    load_before = os.getloadavg()
    for side, binary in binaries.items():
        measure(binary, arguments, expected_stdout, args.timeout, side, -1)
    samples: list[Sample] = []
    for iteration in range(args.repeats):
        order = (
            ("baseline", "candidate")
            if iteration % 2 == 0
            else ("candidate", "baseline")
        )
        for side in order:
            sample = measure(
                binaries[side],
                arguments,
                expected_stdout,
                args.timeout,
                side,
                iteration,
            )
            samples.append(sample)
            print(f"{side} {iteration + 1}: {sample.wall_ms:.3f} ms", flush=True)
    report = {
        "scope": "Local development comparison; not BH1 release evidence",
        "platform": platform.platform(),
        "cpu_count": os.cpu_count(),
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "load_before": load_before,
        "load_after": os.getloadavg(),
        "repeats": args.repeats,
        "warmups_per_side": 1,
        "arguments": arguments,
        "binaries": {
            side: {
                "path": str(binary),
                "sha256": digest(binary),
            }
            for side, binary in binaries.items()
        },
        "expected_stdout_sha256": hashlib.sha256(expected_stdout).hexdigest(),
        "failures": 0,
        "summary": {side: summarize(samples, side) for side in binaries},
        "samples": [asdict(sample) for sample in samples],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
