# Optimization comparison: final CI evidence

## Outcome and scope

The implementation in [PR #245](https://github.com/gosuda/bamTiScript/pull/245)
and the measurement correction in
[PR #248](https://github.com/gosuda/bamTiScript/pull/248) are merged.
The accepted comparisons below measure the original base against the optimized
source revision that passed its ordinary correctness jobs. The corrected
end-to-end property fixture used **7.16% less elapsed time**. Compiler and runtime
microbenchmarks also improved, with the phase and memory tradeoffs stated below.

These are development comparisons on ordinary CI hosts. **They do not satisfy
BH1 qualification or establish TypeScript product completion.** Later changes
on main are outside the measured source pair. The evidence directory keeps its
original date label; CI run times and decision-log additions use UTC.

## Source and artifact provenance

| Role | Exact revision |
| --- | --- |
| Baseline production source | `37f76d4f68e5b9b1797f61c44d1893a7705f8389` |
| Optimized production source | `cef40437c4d698755af60b47b577f26971fd3432` |
| Internal comparison controller | `cef40437c4d698755af60b47b577f26971fd3432` |
| Corrected execution comparison controller | `aad1ef83b03c5b76b46c99735ab1c36cecc7841b` |

The execution controller is distinct from the candidate it measures. Its three
checkouts hold measurement tooling, the pinned optimized source, and the pinned
baseline. This excludes subsequent main-branch stabilization changes from the
original optimization experiment.

| Evidence | Run and job | Uploaded artifact |
| --- | --- | --- |
| Accepted internal Rust timers; restricted external wall timers | [Run 45240005538](https://github.com/gosuda/bamTiScript/actions/runs/45240005538), [job 137921766928](https://github.com/gosuda/bamTiScript/actions/runs/45240005538/job/137921766928) | `14854035030` |
| Corrected compile-and-execute wall timers | [Run 45250086013](https://github.com/gosuda/bamTiScript/actions/runs/45250086013), [job 137957091947](https://github.com/gosuda/bamTiScript/actions/runs/45250086013/job/137957091947) | `14856652236` |

The uploaded archive SHA-256 digests are:

- Internal run: `8c7af133633c03107002531fb1b39f36822f110514eeafe749c21861143685dd`.
- Corrected execution run: `3793b4f6e316556db87663e63299416175c4726a8e5787cb9e9be70bb6905743`.

The durable reports are
[compiler-runtime-internal-comparison.json](compiler-runtime-internal-comparison.json)
and [execution-comparison.json](execution-comparison.json). They retain the
original report text extracted from the completed job logs, respectively
100,752 and 26,435 bytes, including the final newline. Their published contents
were compared directly with that original text. These are report files, not the
complete artifact archives; archive digests do not describe the JSON files.

Exact integer preservation matters. For example, the compiler lookup checksum
is `9402542114664782525`, and the cached-get checksum is
`16501189034687497344`. Both exceed JavaScript's exact integer range.
The archived JSON was not parsed and reserialized through JavaScript numbers.
Audits preserve such tokens as exact decimal strings.

## Measurement controls

Both revisions finish building before measurements start. Each revision uses
separate Cargo target and intermediate directories. Compiler wrappers are
disabled. Selected Cargo artifacts must be reported as freshly compiled
(`fresh: false`), have the expected manifest and variant path, and produce
different baseline and candidate executable hashes. Benchmark instrumentation
is applied to a disposable baseline checkout while baseline production source
is checked for unintended changes.

The toolchain is Rust 1.97.1. Release controls are optimization level 3,
16 codegen units, no debug information, no LTO, no incremental compilation, and
one build job. Each workload has six measured observations per variant.
Odd rounds run baseline then candidate; even rounds reverse that order.
Warmups and diagnostics are excluded from the timing summaries.

The internal run contains 96 measurements, 16 warmups, and four diagnostics:
116 observations and 42 summary rows in total. Summary counts, medians, extrema,
sample order, fixture identity, and workload invariants were audited against the
raw observations. All 42 rows remain in the raw file, including the external
wall-time rows excluded from performance claims below.

## Accepted compiler and runtime results

These values use timers inside the Rust benchmark processes. Values are
**milliseconds per stated batch**, shown as median [minimum, maximum] across
six samples. Reduction is relative to the baseline median.

| Workload | Baseline ms | Optimized ms | Elapsed reduction |
| --- | ---: | ---: | ---: |
| 40,000 property lookups, object width 256 | 250.8124635 [250.226481, 255.148033] | 1.945001 [1.904243, 1.967117] | 99.22% |
| Scan and parse 10,000 declarations, five iterations | 53.8488925 [52.724045, 57.262331] | 48.7896485 [47.880853, 51.648073] | 9.40% |
| 33-module frontend, five iterations | 2088.608854 [2080.81238, 2096.301422] | 1971.539927 [1970.395082, 1978.327669] | 5.61% |
| 2,000,000 cached property gets | 42.781869 [42.669811, 42.84518] | 21.101972 [21.023594, 21.169364] | 50.68% |
| 2,000,000 cached property sets | 50.794201 [50.51707, 50.872082] | 25.0711915 [24.903968, 26.16814] | 50.64% |
| 20 GC collections with 10,000 rooted shaped objects | 17.454321 [17.385124, 17.685299] | 9.092216 [8.901978, 10.069624] | 47.91% |
| 100 FunctionSites constructions, 100,000 instructions each | 54.8118405 [54.336972, 55.151701] | 7.017382 [6.646172, 7.885145] | 87.20% |

All six paired observations favor the optimized revision for each of these
seven metrics, and their baseline and candidate sample ranges are disjoint.
These observations support the named workload results; they do not establish
the same gains for arbitrary programs.

The internal run used Linux `7.0.0-1014-aws`, Python 3.12.3, four logical CPUs,
and affinity to CPUs 0 through 3. Its one-minute load average changed from
0.5908 to 0.9399. It was not a qualified BH1 host.

### Measured tradeoffs

The 33-module program's scan subphase became slower: its median increased
from **11.868327 ms** [11.802767, 11.952278] to
**12.648550 ms** [12.584523, 12.710032]. That is **0.780223 ms**, or **6.57%**,
with all six pairs slower and disjoint ranges. The whole frontend batch
nevertheless improved by **117.068927 ms**, or **5.61%**. Program parsing was
10.43% lower and checking 3.50% lower. Retention is justified by the measured
whole-workload result; the cause of the scan-phase change was not isolated.
The standalone parse fixture's scan-phase ranges overlap.

The reported `site_bytes` value describes one `PropertySite` record. It grows
from **52 to 68 bytes**, a 30.77% increase, because a record now stores resolved
slots. The new layout creates records for actual property instructions and
uses a compact per-PC map, replacing two full per-PC record vectors.
This comparison measures construction time and individual record size.
It does **not** measure total heap allocation, peak RSS, or a whole-program
memory reduction.

## Rejected and restricted measurements

The first [comparison run 45236601421](https://github.com/gosuda/bamTiScript/actions/runs/45236601421)
is **rejected as timing evidence**. It shared a Cargo target directory between
revisions. Candidate build commands finished in about 0.07 seconds after the
baseline commands took minutes. Manifest paths alone did not establish fresh
candidate executable provenance. No speed claim in this report uses that run.

Every `process_wall_ns` value in run 45240005538 is also **excluded from precise
application elapsed-time claims**. Its wrapper timed `Popen.wait(timeout=...)`.
On POSIX, that wait uses a polling loop with sleeps, which delayed observation
of process exit and produced timing bands near 31.8, 63.9, 114, 214, and 264 ms.
The independent Rust timers inside the processes remain usable.
See [Python 3.12 subprocess documentation](https://docs.python.org/3.12/library/subprocess.html#subprocess.Popen.wait)
and the [CPython 3.12.3 implementation](https://github.com/python/cpython/blob/v3.12.3/Lib/subprocess.py).

The corrected controller waits for Linux process-descriptor readiness with
`os.pidfd_open` and `select.poll`, then reaps the already-exited process with
an untimed `wait()`. Absolute deadlines retain the timeout budget. Every
failure path closes an opened descriptor and kills and reaps an unreaped child
process group. There is no fallback to the polling implementation.
The prerequisites are Linux 5.3 or newer, normal SIGCHLD handling, and exclusive
ownership of child reaping.

## Corrected end-to-end execution

The execution-only comparison rebuilds just `run_perf` for each pinned source.
It contains **24 measurements, four warmups, and four diagnostics**, for
32 observations and four summary rows. The two measured workloads compile and
execute their fixtures within the child process. The timer includes process
startup and completion.

| Workload | Baseline ms, median [min, max] | Optimized ms, median [min, max] | Interpretation |
| --- | ---: | ---: | --- |
| Property-heavy loop | 280.3952785 [267.586353, 284.405214] | 260.316523 [254.254775, 263.396158] | 7.16% less elapsed; sample ranges are disjoint |
| Allocation churn | 339.011205 [333.716537, 340.676814] | 334.6821565 [330.761045, 337.096914] | 1.28% lower median; sample ranges overlap |

Every paired round improves for both workloads. The property-loop reduction
ranges from 3.52% to 8.50% across pairs. Allocation churn improves by only
0.09% to 2.91% per pair, with overlapping overall ranges. Its 1.28% median
reduction is a small observed improvement, not a general runtime speedup claim.

All measured property-loop processes produce exactly `3600000\n`; allocation
processes produce exactly `5049901000\n`. Diagnostic observations are separate
single samples and are not used for repeated-performance claims.

This run used Linux `7.0.0-1017-azure`, Python 3.12.3, four logical CPUs, and
affinity to CPUs 0 through 3. Its one-minute load average changed from 0.6265
to 1.1514. This is a different host from the internal run, so absolute process
durations must not be compared across those runs.

Both freshly built `run_perf` binaries match their corresponding hashes in the
internal run, and all 38 fixture hashes agree across the reports:

| Variant | Executable SHA-256 |
| --- | --- |
| Baseline | `cd26cc119cbfac32c4cd449ac1916ddff183794a62e12e8cfe4b8c21ef5cf21a` |
| Optimized | `1cb3cd7e06967717877cd5e18a1dbdb3ee177c31fe6d223358f71108abec065a` |

The controller passed Ruff 0.14.3 lint and format checks, ty 0.0.52 type checks,
and **three pytest 9.0.2 tests in 1.08 seconds** before building either revision.
Those tests cover short-child output and reaping, timeout cleanup of a parent
and its descendant, and cleanup after a forced `pidfd_open` failure.

## Correctness at the measured optimized revision

These results apply to `cef40437c4d698755af60b47b577f26971fd3432`, not to every
later main revision.

| Validation | Evidence |
| --- | --- |
| Ordinary CI jobs | [CI run 45240005716](https://github.com/gosuda/bamTiScript/actions/runs/45240005716): quality, Windows linked-native, corpus, conformance accounting, preflight, formal, and all four conformance shards passed. |
| Independent full test execution | [Depot run 45240006162](https://github.com/gosuda/bamTiScript/actions/runs/45240006162): all four jobs passed. Both full test logs independently sum to 46 Cargo test summaries with **5,914 passed, zero failed, and 14 ignored**. These are the same suite run twice, not 11,828 distinct tests. |
| Bytecode semantics | **138 tests**, including **280,893 exhaustive differential cases** that compare complete public certificates or the exact first error against the original solver. |
| Windows cancellation and linked-native execution | [Windows job 137921775258](https://github.com/gosuda/bamTiScript/actions/runs/45240005716/job/137921775258): **18 linked-native tests passed**, including cancellation after native image publication and process cleanup. This does not separately prove entry into guest code. |
| Corpus | [Corpus job 137921775919](https://github.com/gosuda/bamTiScript/actions/runs/45240005716/job/137921775919): **46 passed, zero failed, one ignored**. |
| BH1 performance qualification | No passing qualified result was available when this report was prepared. The [BH1 job 137942253503](https://github.com/gosuda/bamTiScript/actions/runs/45240005716/job/137942253503) was waiting for its matching self-hosted runner at the last inspection. Host fingerprints and gate requirements remain unchanged. |

The verifier's separate local stress evidence is retained in
[README.md](README.md) and [COUNTERBALANCED.md](COUNTERBALANCED.md).
Its 72 counterbalanced samples agree on wire and certificate digests.
The backward-chain median falls from 147.586490 ms to 0.107906 ms; the nested
handler median falls from 95.433583 ms to 0.099811 ms. Ordinary-case ranges
overlap on that busy local host. Deterministic normal-transfer counts fall
from 4,192,256 to 2,048 and from 1,047,552 to 1,024 for those stress cases.
Neither those local results nor the CI comparisons replace BH1 evidence.

## Later main failures are outside this source comparison

The follow-up tooling PR was based on main revision
`2a98e04489c78e6acbc92aa23ebe3c59437cb588`, which included separate stabilization
work from [PR #244](https://github.com/gosuda/bamTiScript/pull/244).
Its [base CI run 45246740635](https://github.com/gosuda/bamTiScript/actions/runs/45246740635)
already reproduced the failures below before the timing-controller changes.

| Test or area | Observed failure on the exact base |
| --- | --- |
| `check_resolves_paths_from_the_config_directory` | TS5112 rejects explicit input files when a tsconfig is present; the test panics at `crates/bamts-cli/tests/cli.rs:2943`. |
| `program::tests::lowers_and_verifies_every_manifest_pinned_corpus_program` | Stack overflow and process abort. |
| `a_captured_constructor_type_alias_keeps_its_construct_signature` | Unexpected BAMTS-C057 diagnostic in `crates/bamts-compiler/tests/namespace_static_inheritance.rs:35`. |
| `declaration_owned_self_captures_match_node_in_every_execution_mode` | Stack overflow and SIGABRT in the corpus differential test. |

See the base [quality job](https://github.com/gosuda/bamTiScript/actions/runs/45246740635/job/137945361377)
and [corpus job](https://github.com/gosuda/bamTiScript/actions/runs/45246740635/job/137945361200).
The follow-up [CI run 45250086767](https://github.com/gosuda/bamTiScript/actions/runs/45250086767)
inherits these failures. The successful execution comparison establishes the
scoped performance result; it does not make that later main revision green.
No production fix for those separate failures is included in this evidence PR.

## Reproduce the corrected comparison

Use Linux 5.3 or newer, Python 3.11 or newer, `uv`, rustup, and clean source
checkouts. Run from a clone of this repository with access to the pinned commits.
The output directory must be new and outside both measured checkouts.

```bash
set -euo pipefail
baseline_revision=37f76d4f68e5b9b1797f61c44d1893a7705f8389
candidate_revision=cef40437c4d698755af60b47b577f26971fd3432
controller_revision=aad1ef83b03c5b76b46c99735ab1c36cecc7841b
comparison_directory="$(mktemp -d)"
git fetch origin "$baseline_revision" "$candidate_revision" "$controller_revision"
git worktree add --detach "$comparison_directory/baseline" "$baseline_revision"
git worktree add --detach "$comparison_directory/candidate" "$candidate_revision"
git worktree add --detach "$comparison_directory/tooling" "$controller_revision"
rustup toolchain install 1.97.1 --profile minimal
uv run --no-project python \
  "$comparison_directory/tooling/perf/compare_optimization.py" \
  --baseline "$comparison_directory/baseline" \
  --candidate "$comparison_directory/candidate" \
  --output "$comparison_directory/results" \
  --rounds 6 --execution-only
```

Omit `--execution-only` to run the full eight-case suite. The manual
`Optimization comparison` workflow exposes baseline and candidate refs and
defaults to the full suite; automatic pull-request runs select the two execution
cases. Reproduction produces its own report, host conditions, and executable
hashes. It is another development comparison unless the separate BH1
fingerprint and runtime requirements are satisfied.
