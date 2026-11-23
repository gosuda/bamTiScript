from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import statistics
import subprocess
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path


@dataclass(frozen=True)
class Workload:
    name: str
    kind: str
    instructions: int
    registers: int
    iterations: int


@dataclass(frozen=True)
class Variant:
    name: str
    binary: Path


@dataclass(frozen=True)
class Sample:
    case: str
    variant: str
    round: int
    position: int
    sequence: int
    ns_per_verify: int
    total_ns: int
    iterations: int
    failures: int
    wire_digest: str
    fact_digest: str
    stdout: str


WORKLOADS = (
    Workload("straight-32", "straight", 32, 8, 20000),
    Workload("straight-4096", "straight", 4096, 64, 100),
    Workload("straight-wide", "straight", 4096, 512, 100),
    Workload("branches-4096", "branches", 4096, 64, 100),
    Workload("reverse-2048", "reverse", 2048, 64, 2),
    Workload("handlers-1024", "handlers", 1024, 64, 2),
)
EXPECTED_FIELDS = frozenset(
    {
        "case",
        "instructions",
        "registers",
        "iterations",
        "failures",
        "total_ns",
        "ns_per_verify",
        "wire_digest",
        "fact_digest",
    }
)


def checked_fields(stdout: str, workload: Workload) -> dict[str, str]:
    fields: dict[str, str] = {}
    for part in stdout.split():
        key, separator, value = part.partition("=")
        if not separator or not value or key in fields:
            raise ValueError(f"Malformed benchmark output: {stdout!r}")
        fields[key] = value
    if fields.keys() != EXPECTED_FIELDS:
        raise ValueError(f"Unexpected benchmark fields: {stdout!r}")
    expected = {
        "case": workload.kind,
        "instructions": str(workload.instructions),
        "registers": str(workload.registers),
        "iterations": str(workload.iterations),
        "failures": "0",
    }
    for key, value in expected.items():
        if fields[key] != value:
            raise ValueError(f"Unexpected {key}: {stdout!r}")
    total = int(fields["total_ns"])
    per_verify = int(fields["ns_per_verify"])
    if per_verify <= 0 or total // workload.iterations != per_verify:
        raise ValueError(f"Inconsistent benchmark timing: {stdout!r}")
    for key in ("wire_digest", "fact_digest"):
        digest = fields[key]
        if len(digest) != 16 or any(char not in "0123456789abcdef" for char in digest):
            raise ValueError(f"Invalid {key}: {stdout!r}")
    return fields


def run_sample(
    workload: Workload,
    variant: Variant,
    round_number: int,
    position: int,
    sequence: int,
) -> Sample:
    completed = subprocess.run(
        [
            str(variant.binary),
            workload.kind,
            str(workload.instructions),
            str(workload.registers),
            str(workload.iterations),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=120,
    )
    if completed.stderr:
        raise ValueError(f"Unexpected benchmark stderr: {completed.stderr!r}")
    fields = checked_fields(completed.stdout, workload)
    return Sample(
        case=workload.name,
        variant=variant.name,
        round=round_number,
        position=position,
        sequence=sequence,
        ns_per_verify=int(fields["ns_per_verify"]),
        total_ns=int(fields["total_ns"]),
        iterations=workload.iterations,
        failures=0,
        wire_digest=fields["wire_digest"],
        fact_digest=fields["fact_digest"],
        stdout=completed.stdout.strip(),
    )


def save_report(path: Path, report: dict[str, object]) -> None:
    temporary = path.with_suffix(f"{path.suffix}.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compare verifier binaries in counterbalanced A/B and B/A pairs."
    )
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=6)
    arguments = parser.parse_args()
    baseline: Path = arguments.baseline.resolve(strict=True)
    candidate: Path = arguments.candidate.resolve(strict=True)
    output: Path = arguments.output.resolve()
    rounds: int = arguments.rounds
    if rounds < 6 or rounds % 2:
        parser.error("--rounds must be an even integer of at least six")
    if output.exists():
        parser.error(f"refusing to replace an existing result: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)

    variants = (Variant("base", baseline), Variant("worklist", candidate))
    samples: list[Sample] = []
    records: list[dict[str, object]] = []
    expected_digests: dict[str, tuple[str, str]] = {}
    report: dict[str, object] = {
        "schema": "bamts.local-verifier-counterbalanced/v1",
        "complete": False,
        "started_utc": datetime.now(UTC).isoformat(),
        "compiler": subprocess.check_output(["rustc", "--version"], text=True).strip(),
        "platform": platform.platform(),
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "load_before": os.getloadavg(),
        "binary_paths": {variant.name: str(variant.binary) for variant in variants},
        "binary_sha256": {
            variant.name: hashlib.sha256(variant.binary.read_bytes()).hexdigest()
            for variant in variants
        },
        "rounds": rounds,
        "method": (
            "For each workload, odd rounds run base then worklist; even rounds run "
            "worklist then base. Every process performs its own untimed warmup. "
            "Only public verification calls are timed. Module cloning, wire and "
            "complete certificate validation, and destruction are outside the "
            "timed regions. Both variants perform the same number of iterations. "
            "All samples must succeed with zero failures, empty stderr, and "
            "matching wire and full-certificate digests."
        ),
        "workloads": [asdict(workload) for workload in WORKLOADS],
        "samples": records,
    }
    save_report(output, report)
    for workload in WORKLOADS:
        for round_number in range(1, rounds + 1):
            ordered = variants if round_number % 2 else variants[::-1]
            for position, variant in enumerate(ordered, start=1):
                sample = run_sample(
                    workload, variant, round_number, position, len(samples) + 1
                )
                digest = (sample.wire_digest, sample.fact_digest)
                if expected_digests.setdefault(workload.name, digest) != digest:
                    raise ValueError(f"Wire or certificate digest differs: {sample}")
                samples.append(sample)
                records.append(asdict(sample))
                save_report(output, report)
                print(json.dumps(asdict(sample)), flush=True)

    summaries: list[dict[str, str | int | float]] = []
    for workload in WORKLOADS:
        for variant in variants:
            timings = [
                sample.ns_per_verify
                for sample in samples
                if sample.case == workload.name and sample.variant == variant.name
            ]
            assert len(timings) == rounds
            summaries.append(
                {
                    "case": workload.name,
                    "variant": variant.name,
                    "samples": len(timings),
                    "median_ns": statistics.median(timings),
                    "minimum_ns": min(timings),
                    "maximum_ns": max(timings),
                }
            )
    report.update(
        complete=True,
        finished_utc=datetime.now(UTC).isoformat(),
        load_after=os.getloadavg(),
        summaries=summaries,
    )
    save_report(output, report)
    print(
        json.dumps({"complete": True, "samples": len(samples), "output": str(output)})
    )


if __name__ == "__main__":
    main()
