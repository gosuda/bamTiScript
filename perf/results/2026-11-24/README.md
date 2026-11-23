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

[worklist-validated-comparison.json](worklist-validated-comparison.json) contains
90 raw samples: five rounds for each of six workloads, always in the fixed order
original, scratch, then worklist. This interleaves variants but does not
counterbalance their order; changing host load or thermal conditions can bias
the comparison. Every sample reports zero failures. For each workload, all 15
samples have matching wire and complete-public-certificate digests across
variants. The file retains binary hashes, CPU affinity, and host load.

The run used a busy local host with affinity to CPUs 0 through 8. The one-minute
load average was 28.38 before and 25.86 after. **This is not BH1 evidence.** No
performance host requirements or official performance artifacts were changed.

## Bytecode verification timings

Values are median microseconds per verification, with `[minimum, maximum]` over
five samples per variant. Every table cell was recomputed from the raw JSON with
`uv run --offline --no-project python` before this report was written.

| Workload | Original | Scratch only | Scratch and worklist |
| --- | ---: | ---: | ---: |
| 32 straight-line instructions | 3.960 [2.160, 5.778] | 3.019 [1.898, 3.128] | 2.355 [1.279, 4.646] |
| 4,096 straight-line instructions, 64 registers | 423.140 [178.006, 930.128] | 235.308 [184.153, 465.400] | 238.470 [173.275, 350.314] |
| 4,096 straight-line instructions, 512 registers | 619.842 [375.854, 745.458] | 498.792 [186.270, 650.658] | 307.287 [166.043, 395.105] |
| 4,096 instructions with forward branches | 293.912 [200.959, 634.452] | 257.821 [216.723, 463.794] | 268.765 [119.215, 558.523] |
| 2,048 instructions in a backward chain | 75,512.770 [73,439.043, 129,945.201] | 26,526.945 [21,593.892, 54,053.347] | 66.891 [63.441, 216.172] |
| 1,024 backward instructions with 32 nested handlers | 66,720.704 [49,764.118, 147,654.657] | 46,815.066 [35,823.464, 51,828.927] | 93.387 [61.628, 113.922] |

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
| Benchmark output agreement | **Checked:** zero failures and matching wire/certificate digests across the 90 timing samples; exact encoded bytes and complete certificates are checked by each runner outside timing. |
| Full workspace checks and root gates | **PENDING.** Leaf bytecode tests do not satisfy workspace or product gates. |
| Compiler tests and performance | **PENDING.** Source changes are integrated; no compiler speed claim is made. |
| Runtime tests and performance | **PENDING.** Source changes are integrated; no runtime speed claim is made. |
| End-to-end compilation and execution | **PENDING.** |
| BH1 performance qualification | **PENDING.** The recorded local host is not BH1. |

Append later validation with its exact revision, commands, host identity, and raw
results. Preserve the distinction between these imported source-branch checks
and checks run on the final integration revision.
