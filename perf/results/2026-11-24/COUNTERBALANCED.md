# Counterbalanced verifier comparison

This run supersedes the earlier timing table. It measures the same original
and final verifier binaries with the run order reversed on every other round.
No production code or binary changed for this measurement.

Original production revision: `37f76d4f68e5b9b1797f61c44d1893a7705f8389`.
Final source revision: `a98ce2b2250ea43a6723997b6344fbd2e96d0d8e`.
Both use the final `verify_perf.rs` runner, including certificate fingerprints.

## Method

`worklist-counterbalanced-comparison.json` records 72 samples: six workloads,
six rounds each, two variants per round. Odd rounds run the original before the
worklist variant; even rounds reverse that order. Each variant therefore runs
first three times and second three times for every workload. The JSON records
the actual position and sequence of each sample.

The runner performs an untimed warmup in each process. It then times only the
public verification calls. Module cloning, wire-byte comparison, full
certificate comparison within each variant, and destruction are outside the
timed regions. Both variants perform the same number of iterations. Every
sample must finish successfully with zero verification failures and empty
stderr. Wire and full-certificate digests must match across variants and rounds.

The two binaries are byte-identical to those in the earlier validated report:

| Variant | SHA-256 |
| --- | --- |
| Original | `ed6dbd80602b1902bdbae6f6b7aa50fea4a4522aa0ff95fbd73cc453abfff574` |
| Scratch buffer and worklist | `81cee9ff87376a4b7a1f210b0e6b1ffbbd5e7de34487d49c53c37f8dd871c355` |

Those binaries were built directly with pinned Rust 1.97.1, edition 2024,
optimization level 3, and forbidden unsafe code. This run did not rebuild them.
The benchmark ran from `2026-11-23T17:30:27Z` to `2026-11-23T17:31:30Z`.
The host exposed nine CPUs; the one-minute load average was 44.43 before and
43.28 after. This is a busy development host, not a BH1-qualified run.

## Results

Values are median microseconds per verification, followed by the minimum and
maximum of six samples in brackets. Displayed values use decimal half-up
rounding to 0.001 microsecond. Raw nanosecond values are retained in JSON.

| Workload | Original | Scratch buffer and worklist |
| --- | ---: | ---: |
| 32 straight-line instructions | 5.152 [3.739, 6.454] | 2.866 [1.932, 5.021] |
| 4,096 straight-line instructions, 64 registers | 444.598 [197.134, 604.532] | 208.011 [126.572, 434.878] |
| 4,096 straight-line instructions, 512 registers | 332.265 [275.151, 453.225] | 261.286 [155.872, 476.992] |
| 4,096 instructions with forward branches | 611.178 [322.617, 758.787] | 450.253 [216.971, 759.553] |
| 2,048 instructions in a backward chain | 147,586.490 [99,833.330, 271,872.325] | 107.906 [86.871, 519.350] |
| 1,024 backward instructions with 32 nested handlers | 95,433.583 [60,623.311, 278,683.110] | 99.811 [61.392, 385.923] |

The backward-chain and nested-handler reductions remain decisive under
counterbalanced ordering. For both fixtures, the slowest final sample is still
faster than the fastest original sample by more than two orders of magnitude.
The ordinary-case ranges overlap. Their medians do not justify a precise
general speedup claim, and these synthetic verifier measurements do not measure
whole-program compilation or execution.

The separate, untimed limiter profile is unchanged. It attributes the
backward-chain improvement to normal transfers falling from 4,192,256 to 2,048.
For nested handlers, normal transfers fall from 1,047,552 to 1,024, handler
transfers from 32,736 to 32, and protected-fact intersections from 32,506,848 to
31,744. See `limiter-profile.json` for the raw counter output.

## Audit and correction

An independent read of the completed JSON verified all 72 sequence numbers,
all 36 ordered pairs, all zero-failure results, both binary hashes, and every
wire and certificate digest. Both hashes and all workload digests match the
earlier validated report. All 12 median, minimum, and maximum summaries were
recomputed from the raw samples and matched exactly.

The earlier `measure.py` always iterated variants in the supplied order. Its
metadata incorrectly described those rounds as alternating. Its raw output
remains historical evidence and must be described as fixed-order measurements.
The new script, committed as
[`perf/measure_verifier.py`](../../measure_verifier.py), implements and records
the intended counterbalanced order explicitly.

The new Python runner passed Ruff formatting and lint checks and `ty check`.
The previously reported 138 bytecode tests, including 280,893 differential
cases, apply to the same final source. This measurement adds no claim that the
workspace, compiler, runtime, end-to-end, or BH1 gates have completed.

## Reproduction

Build the original and final verifier libraries with the same Rust version and
flags. Compile the final `crates/bamts-bytecode/examples/verify_perf.rs` against
each library so both binaries contain the same validation code. The original
production library uses the base revision; only its benchmark runner comes
from the final revision.

Follow the complete [source-build and measurement instructions](README.md#reproduce-the-verifier-comparison)
from the repository root. They extract the base and current candidate from Git,
build both libraries and the shared runner with Rust 1.97.1, and call the
committed Python script with `--rounds 6`. The archived raw JSON retains the
original local binary paths and hashes as provenance; those local binaries are
not prerequisites for reproduction.

Use a new output path for a repeat run. The runner refuses to overwrite an
existing result. It marks the report complete only after every expected sample
and summary is present.
