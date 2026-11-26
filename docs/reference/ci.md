# Continuous integration

GitHub Actions owns workflow events. Every job runs on Depot hardware.
Linux uses pinned `depot-ubuntu-24.04` or `depot-ubuntu-24.04-arm` labels,
macOS uses `depot-macos-latest`, and Windows uses `depot-windows-2025-4`.

## Routine verification

`ci.yml` runs for pull requests, merge queue groups, and manual dispatch.
It retains formatting, workspace checks, Clippy, the full workspace test
suite, pinned Node oracle contracts, npm interface checks, formal gates,
and four conformance receipt shards with complete receipt accounting.
The workspace suite includes `corpus_differential`, so a second corpus
job does not run on the same commit. Main pushes do not repeat the PR
and merge queue pipeline. Superseded PR runs are cancelled.

Every CI ref can save its own Rust dependency cache. The cache prefix
includes the full ref, while the action retains its job and compiler keys,
so a later run on the same PR can reuse dependencies without a separate
cache-warming pipeline. Depot Cache is repository-scoped; these keys are
ordinary reuse partitions, not an access-control boundary.

## Extended verification

`nightly.yml` remains the daily and manual full conformance pipeline.
It also runs Windows platform, linker, cache, executable, and lane tests
in one job with one compiler setup. Those Windows tests no longer run
on each PR. The Linux native addon lifecycle check runs with the nightly
corpus job. The duplicate `ci-depot.yml` workflow has been removed.

Optimization comparisons and the native string oracle are manual tools.
BH1 measurements must run on the exact host described by
`perf/hosts/bh1.toml`. The automatic self-hosted BH1 job has been removed.
Depot results must never be presented as BH1 performance evidence.
The local benchmark tools, host fingerprint, and budgets remain intact.

## Release builds

Manual CLI and native addon builds retain all five target artifacts.
macOS x64 uses an x86_64-hosted Rust toolchain and x64 Node under Rosetta
on Apple silicon. Each build asserts that Rust's host equals its target;
the packaged Intel CLI and addon must compile and run an AOT program.
This proves translated execution on macOS, not
execution on physical Intel hardware. The workflow fails if Rosetta is
unavailable. ARM64 macOS and x64 Windows execute on their matching Depot
hosts. Build records and preflight checks name the actual Depot labels.

Release packaging omits the shared CI Rust cache. Its infrequent builds
compile dependencies from source rather than trust build artifacts written
by PR workflows. The release jobs do not claim warm compiled dependencies.

Release publication remains disabled by the existing U11.7 gate.

Runner inventory: <https://depot.dev/docs/github-actions/runner-types>.
