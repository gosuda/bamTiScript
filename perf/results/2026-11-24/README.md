# Local optimization evidence: 2026-11-24

## Scope and provenance

This directory preserves local bytecode-verifier evidence for the optimization
integration. Compiler and runtime changes are integrated; their tests and
performance results remain pending. These measurements do not establish product
completion.

| Source | Commit |
| --- | --- |
| Original base | `37f76d4f68e5b9b1797f61c44d1893a7705f8389` |
| Reusable verifier scratch buffers | `f68b4325c1e848d19a1703d1b029cf585aa32d20` |
| Predecessor-driven worklist, applied after scratch buffers | `1afd6f9c81a83079809019444229f11365778fbc` |
| Cross-variant benchmark wire/certificate digest validation | `a98ce2b2250ea43a6723997b6344fbd2e96d0d8e` |

These are source commits from `codex/perf-bytecode-20261124`; integration commits
may have different hashes. The original and scratch variants use the same final
benchmark digest checks as the worklist variant.

The integrated production changes move owned semantic models and scanner tokens
into their consumers, borrow object metadata for sorted property lookup, cache
resolved runtime property slots while checking live descriptors, trace shaped
GC properties without ordered-key allocations, and allocate cache records only
for property instructions. The verifier changes reuse transfer storage and
schedule changed facts with a worklist. Wire formats, source-coordinate rules,
generated authority files, and formal obligations are unchanged.

## Method and limits

The runner is `crates/bamts-bytecode/examples/verify_perf.rs`. It constructs each
fixture and warms verification. Each timed operation consumes a fresh unverified
module through the public verification API. Module cloning, exact encoded-byte
and complete certificate comparisons, and destruction occur outside the timed
region. The dependency-free crate and runners were built directly with pinned
Rust 1.97.1, edition 2024, optimization level 3, and forbidden unsafe code.

[worklist-counterbalanced-comparison.json](worklist-counterbalanced-comparison.json)
is the primary timing evidence. It contains 72 raw samples: six workloads, six
rounds, and two variants per round. Odd rounds run original then worklist; even
rounds run worklist then original. Each variant runs first three times and
second three times per workload. Every sample reports zero failures, and each
workload has matching wire and complete-public-certificate digests across all
12 samples. The file retains the actual sequence, binary hashes, CPU affinity,
and host load. [COUNTERBALANCED.md](COUNTERBALANCED.md) records the detailed audit.

The run used a busy local host with affinity to CPUs 0 through 8. The one-minute
load average was 44.43 before and 43.28 after. **This is not BH1 evidence.** No
performance host requirements or official performance artifacts were changed.

The historical [worklist-validated-comparison.json](worklist-validated-comparison.json)
is preserved unchanged. Its 90 samples used five fixed-order rounds of original,
scratch, then worklist for each workload. Its metadata incorrectly called that
order alternating. The samples and digests remain valid records, but that
description is superseded and the timing table below uses the new
counterbalanced run. Order balancing reduces systematic order bias; it does
not remove interference from the busy host.

## Bytecode verification timings

Values are median microseconds per verification, with `[minimum, maximum]` over
six samples per variant. Every table cell was recomputed from the raw JSON with
`uv run --offline --no-project python` before this report was written. Displayed
values use decimal half-up rounding to 0.001 microsecond; the JSON preserves the
nanosecond summaries.

| Workload | Original | Scratch and worklist |
| --- | ---: | ---: |
| 32 straight-line instructions | 5.152 [3.739, 6.454] | 2.866 [1.932, 5.021] |
| 4,096 straight-line instructions, 64 registers | 444.598 [197.134, 604.532] | 208.011 [126.572, 434.878] |
| 4,096 straight-line instructions, 512 registers | 332.265 [275.151, 453.225] | 261.286 [155.872, 476.992] |
| 4,096 instructions with forward branches | 611.178 [322.617, 758.787] | 450.253 [216.971, 759.553] |
| 2,048 instructions in a backward chain | 147,586.490 [99,833.330, 271,872.325] | 107.906 [86.871, 519.350] |
| 1,024 backward instructions with 32 nested handlers | 95,433.583 [60,623.311, 278,683.110] | 99.811 [61.392, 385.923] |

The original and worklist ranges are disjoint for both backward-order stress
fixtures on this host. All four ordinary fixtures have overlapping ranges, so
ordinary-case improvements or regressions remain inconclusive. These results
support a bytecode-verifier improvement on the stress fixtures only; they do not
measure general compiler, runtime, or end-to-end speed.

## Solver operation counts

[limiter-profile.json](limiter-profile.json) contains separately instrumented
runs. Their timings are excluded from the table above. Each recorded pair of
warmup/measured counter lines agrees. Counter-run output reports zero failures
and matching wire digests; this file does not record certificate digests.

| Workload | Original normal transfers | Worklist normal transfers | Original handler transfers | Worklist handler transfers |
| --- | ---: | ---: | ---: | ---: |
| Straight 4,096 | 8,192 | 4,096 | 0 | 0 |
| Backward 2,048 | 4,192,256 | 2,048 | 0 | 0 |
| Nested handlers 1,024 | 1,047,552 | 1,024 | 32,736 | 32 |

For nested handlers, protected-fact intersections fall from 32,506,848 to 31,744.
These counts identify redundant global fixed-point transfers as the removed
work. They are separate evidence from the elapsed-time samples.

## Validation status

| Area | Status and evidence |
| --- | --- |
| Source bytecode tests | **138 passed** through pinned direct `rustc --test`, including a differential test over **280,893 exhaustive cases** comparing complete certificates or exact first errors with the original solver. |
| Benchmark output agreement | **Checked:** zero failures and matching wire/certificate digests across the 72 counterbalanced samples. Their binary hashes and workload digests match the historical run. Exact encoded bytes and complete certificates are checked by each runner outside timing. |
| Integration formatting and whitespace | **PASS** at `602530a3bde07e47fd290e783133c48b095b0aea`: `cargo fmt --all --check` and `git diff --check`. |
| Full workspace checks and root gates | **PENDING.** Leaf bytecode tests do not satisfy workspace or product gates. |
| Compiler tests and performance | **PENDING.** Source changes are integrated; no compiler speed claim is made. |
| Runtime tests and performance | **PENDING.** Source changes are integrated; no runtime speed claim is made. |
| End-to-end compilation and execution | **PENDING.** |
| BH1 performance qualification | **PENDING.** The recorded local host is not BH1. |

Both baseline release-build attempts ended in SIGKILL without a Rust diagnostic,
including the retry with 256 codegen units. The subsequent baseline
`cargo check --locked -p bamts-compiler --examples -j 1` also ended in SIGKILL
without a diagnostic. These attempts did not validate compiler or runtime
changes. They do not relax any gate, and no CI result is claimed here.

Append later validation with its exact revision, commands, host identity, and raw
results. Preserve the distinction between these imported source-branch checks
and checks run on the final integration revision.

## Reproduce the verifier comparison

Run these commands from the repository root on Linux with a rustup-managed
Rust 1.97.1 installation, Python 3.11 or newer, and `uv`. The checkout must
contain the pinned base commit and this change. If the checkout is shallow,
fetch the base commit before running `git archive`.

The dependency-free bytecode crate can be built directly with `rustc`. The
commands extract the original production source from the pinned base and the
candidate source from the current commit. Both binaries use the same candidate
`verify_perf.rs`, so the original also performs the final wire and certificate
checks. No prebuilt local benchmark binary or unpublished source branch is
required. The commands leave the checkout unchanged and retain source revisions
beside the new result.

```bash
set -euo pipefail
export RUSTUP_TOOLCHAIN=1.97.1
baseline_revision=37f76d4f68e5b9b1797f61c44d1893a7705f8389
candidate_revision="$(git rev-parse HEAD)"
verifier_tmp="$(mktemp -d "${TMPDIR:-/tmp}/bamts-verifier.XXXXXX")"
mkdir -p "$verifier_tmp/base-src" "$verifier_tmp/candidate-src"
mkdir -p "$verifier_tmp/base" "$verifier_tmp/candidate"

git archive "$baseline_revision" crates/bamts-bytecode/src |
  tar -x -C "$verifier_tmp/base-src"
git archive "$candidate_revision" \
  crates/bamts-bytecode/src \
  crates/bamts-bytecode/examples/verify_perf.rs |
  tar -x -C "$verifier_tmp/candidate-src"

printf '%s\n' "baseline=$baseline_revision" "candidate=$candidate_revision" \
  > "$verifier_tmp/revisions.txt"
rustc --version >> "$verifier_tmp/revisions.txt"

for variant in base candidate; do
  rustc --edition=2024 -C opt-level=3 -F unsafe-code \
    --crate-name bamts_bytecode --crate-type rlib \
    "$verifier_tmp/$variant-src/crates/bamts-bytecode/src/lib.rs" \
    -o "$verifier_tmp/$variant/libbamts_bytecode.rlib"
  rustc --edition=2024 -C opt-level=3 -F unsafe-code \
    "$verifier_tmp/candidate-src/crates/bamts-bytecode/examples/verify_perf.rs" \
    --extern "bamts_bytecode=$verifier_tmp/$variant/libbamts_bytecode.rlib" \
    -o "$verifier_tmp/$variant/verify_perf"
done

uv run --offline --no-project python perf/measure_verifier.py \
  --baseline "$verifier_tmp/base/verify_perf" \
  --candidate "$verifier_tmp/candidate/verify_perf" \
  --output "$verifier_tmp/comparison.json" \
  --rounds 6
printf 'Results: %s\n' "$verifier_tmp"
```

The measurement script requires an even number of rounds of at least six and
refuses to overwrite an existing result. It records `complete: false` until all
samples pass output validation and every summary is present. Repeating the
commands creates a fresh result directory. Compiler identity is read from
`rustc` on `PATH`; keep the pinned toolchain selected for both compilation and
measurement. Host conditions, rebuilt binary hashes, and elapsed times need not
match the archived run.

For one public-API workload, the built runner accepts
`verify_perf <straight|reverse|branches|handlers> <instructions> <registers> <iterations>`.
The committed [measurement script](../../measure_verifier.py) fixes all six
workload dimensions for the reported comparison. Direct builds and local
measurements do not establish workspace, end-to-end, or BH1 gate completion.
