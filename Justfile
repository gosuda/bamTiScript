set shell := ["bash", "-euo", "pipefail", "-c"]

host_triple := `rustc -vV | awk '/^host:/{print $2}'`
export PATH := env_var_or_default('HOME', '') + "/.nvm/versions/node/v24.18.0/bin:/opt/homebrew/opt/lld/bin:/opt/homebrew/opt/llvm/bin:" + env_var('PATH')
xcheck_targets := "x86_64-apple-darwin x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu x86_64-pc-windows-msvc"

doctor:
    [[ "$(node -v)" == "v24.18.0" ]]
    [[ "$(rustc -V)" == "rustc 1.97.1 "* ]]
    [[ "$(racket --version)" == *" v9.2 "* ]]
    command -v ld.lld
    command -v llvm-readelf
    command -v lake
    command -v npm
    test -x formal/quint/node_modules/.bin/quint
    installed="$(rustup target list --installed)"; for target in {{xcheck_targets}}; do grep -qx "$target" <<< "$installed"; done
    printf '%s\n' 'DOCTOR PASS'

# The finish line: prints PRODUCT COMPLETE or a bounded failure summary.
gate-status:
    cargo run --locked -q -p bamts-verification --bin bamts-verification -- completion verify --root product

ci: ci-quality ci-npm ci-corpus ci-native-boundary xcheck portability-check
    printf '%s\n' 'LOCAL CI PASS'

ci-quality:
    cargo fmt --all --check
    cargo check --workspace --locked
    cargo clippy --workspace --all-targets --locked -- -D warnings
    cargo test --workspace --locked

# Every npm test except the two groups that need the assembled five-host release
# set: the staged leaf archives and the clean-consumer install. One machine cannot
# build all five leaves, so those run in ci-npm-release instead of being dropped.
ci-npm:
    npm ci
    node --test --test-skip-pattern='staged cli-|clean consumer' npm/test/*.test.mjs

# The whole npm suite. It needs every host's leaf archive in npm/dist, so it is the
# gate for the five-host install, not for a single machine.
ci-npm-release:
    npm ci
    node --test npm/test/*.test.mjs

ci-corpus:
    cargo test -p bamts-verification --test corpus_differential --locked -- --nocapture

# The cache ownership and publication tests, which the CI job "Windows native boundary"
# also runs. `cargo test --workspace` leaves the cache-guard feature off, so on a Windows host
# ci-quality never builds the Win32 module or its tests. On other hosts the feature
# compiles only the portable part of the module, which has no tests of its own.
ci-native-boundary:
    cargo test --locked -p bamts-native --features cache-guard

ci-accounting:
    cargo run --locked -p bamts-verification --bin ts_conformance -- sync --verify-pin --write-snapshot
    cargo run --locked -p bamts-verification --bin ts_conformance -- audit-ledger --require-complete

authority:
    cargo run --locked -p bamts-verification -- source fetch typescript-7-compiler --dest target/authority/typescript-7.0.2
    cargo run --locked -p bamts-verification -- source fetch typescript-primary-tests --dest target/authority/typescript-7.0.2-tests
    cargo run --locked -p bamts-verification -- source fetch typescript-6.0-tests --dest target/authority/typescript-6.0.2-tests
    cargo run --locked -p bamts-verification -- source fetch typescript-compat-tests --dest target/authority/typescript-5.9.3-tests
    cargo run --locked -p bamts-verification -- source fetch test262 --dest target/authority/test262

ci-catalog: authority
    cargo run --locked -p bamts-verification --bin bamts-verification -- catalog regenerate --release typescript-7.0.2 --check

ci-formal: ci-catalog
    cargo run --locked -p bamts-verification --bin bamts-verification -- formal audit --gates G1,G2,G5,G3,G4

ci-string-oracle:
    node npm/scripts/native-string-oracle.mjs

sweep catalog runner shards="32" jobs="10":
    #!/usr/bin/env bash
    set -euo pipefail
    test -z "$(git status --porcelain)" || { echo "sweep needs a clean tree"; exit 1; }
    cargo build --locked --release -p bamts-verification --bin bamts-verification --bin ts_lane_worker --bin runtime_lane_worker
    sha="$(git rev-parse HEAD)"
    run="local-${sha:0:12}"
    out="target/evidence-local/{{catalog}}/{{runner}}/{{host_triple}}/$run"
    mkdir -p "$out" target/evidence-local/merged
    export BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker
    export BAMTS_SUITE_INTERPRETER_ADAPTER=target/release/runtime_lane_worker
    export BAMTS_SUITE_JIT_ADAPTER=target/release/runtime_lane_worker
    export BAMTS_SUITE_AOT_ADAPTER=target/release/runtime_lane_worker
    test -f verification/ts-suite/index.json || cargo run --locked -p bamts-verification --bin ts_conformance -- sync --verify-pin --write-snapshot
    seq 0 $(( {{shards}} - 1 )) | xargs -P {{jobs}} -I{} target/release/bamts-verification suite run \
      --catalog {{catalog}} --shard "{}/{{shards}}" --receipt "$out/{}.jsonl" \
      --runner {{runner}} --platform {{host_triple}} \
      --workflow Justfile --run-id "$run" --run-attempt 1 --source-sha "$sha" \
      --job sweep --host "$(uname -sm | tr ' ' '-')" \
      --runtime "node-v24.18.0;rust-$(rustc --version)"
    merged="target/evidence-local/merged/{{catalog}}-{{runner}}-{{host_triple}}.jsonl"
    target/release/bamts-verification suite merge --catalog {{catalog}} --receipts "$out" --out "$merged"
    target/release/bamts-verification suite merge --catalog {{catalog}} --receipts "$out" --out "$merged" --check
    target/release/bamts-verification suite status --receipts target/evidence-local/merged --out target/evidence-local/status.md
    printf 'SWEEP PASS %s\n' "$merged"

# Counts by state, facet and failure family for one sweep. `receipt` defaults to
# the merged file `sweep` writes; pass another, such as a smoke shard, to read it.
status catalog runner receipt="" top="20":
    #!/usr/bin/env bash
    set -euo pipefail
    receipt="{{receipt}}"
    receipt="${receipt:-target/evidence-local/merged/{{catalog}}-{{runner}}-{{host_triple}}.jsonl}"
    cargo run --locked -q -p bamts-verification --bin bamts-verification -- suite families "$receipt" --top {{top}}

# The rows of one failure family, smallest input first. Family names come from `status`.
family-show family catalog="typescript-7.0.2" runner="compiler" receipt="":
    #!/usr/bin/env bash
    set -euo pipefail
    case "{{catalog}}" in
      typescript-7.0.2) root=target/authority/typescript-7.0.2-tests ;;
      typescript-6.0.2) root=target/authority/typescript-6.0.2-tests ;;
      typescript-5.9.3) root=target/authority/typescript-5.9.3-tests ;;
      test262) root=target/authority/test262 ;;
      *) echo "family-show: no authority tree is known for catalog {{catalog}}"; exit 1 ;;
    esac
    receipt="{{receipt}}"
    receipt="${receipt:-target/evidence-local/merged/{{catalog}}-{{runner}}-{{host_triple}}.jsonl}"
    cargo run --locked -q -p bamts-verification --bin bamts-verification -- suite families "$receipt" --family "{{family}}" --root "$root"

# Rebuilds the lane workers, reruns one family plus a sample of the passing rows, and
# fails if a sampled row no longer passes. A fix must convert a row and regress none.
# The sample catches a broad regression between sweeps; only a sweep proves none.
recount family catalog="typescript-7.0.2" runner="compiler" receipt="":
    #!/usr/bin/env bash
    set -euo pipefail
    receipt="{{receipt}}"
    receipt="${receipt:-target/evidence-local/merged/{{catalog}}-{{runner}}-{{host_triple}}.jsonl}"
    cargo build --locked --release -p bamts-verification --bin ts_lane_worker --bin runtime_lane_worker
    export BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker
    export BAMTS_SUITE_INTERPRETER_ADAPTER=target/release/runtime_lane_worker
    export BAMTS_SUITE_JIT_ADAPTER=target/release/runtime_lane_worker
    export BAMTS_SUITE_AOT_ADAPTER=target/release/runtime_lane_worker
    cargo run --locked -q -p bamts-verification --bin bamts-verification -- suite recount --catalog {{catalog}} --runner {{runner}} --baseline "$receipt" --family "{{family}}" --fail-on-regression

# Rewrites target/evidence-local/status.md from every receipt in a directory (the merged
# ones `sweep` writes) and shows what changed since the previous report.
status-report receipts="target/evidence-local/merged" out="target/evidence-local/status.md":
    cargo run --locked -q -p bamts-verification --bin bamts-verification -- suite status --receipts {{receipts}} --out {{out}}

nightly: ci ci-accounting ci-formal
    just sweep typescript-7.0.2 compiler
    just sweep typescript-6.0.2 compiler
    just sweep typescript-5.9.3 compiler
    just sweep test262 interpreter
    just sweep test262 jit
    just sweep test262 aot
    printf '%s\n' 'NIGHTLY PASS'

# Deterministic receipt-aware TypeScript product release root.
#
# A receipt content-addresses the binary that measured it, so the process
# verifying a receipt has to resolve the same lane worker the process that
# wrote it resolved. That makes BAMTS_SUITE_COMPILER_ADAPTER load-bearing at
# verification time, not only at capture time: without it, `ledger rebuild`
# resolves the harness, the receipt names the worker, and every row is
# rejected as a stale candidate binding.
release-gate:
    just ci
    just ci-formal
    just sweep typescript-7.0.2 compiler
    just sweep typescript-6.0.2 compiler
    just sweep typescript-5.9.3 compiler
    just sweep test262 interpreter
    just sweep test262 jit
    just sweep test262 aot
    for d in verification/receipts verification/evidence/pr-merged verification/evidence/nightly-merged verification/evidence/typescript-7.0.2; do test -z "$(ls -A "$d" 2>/dev/null)" || { echo "stale receipt set: $d"; exit 1; }; done
    rm -rf verification/evidence/release && mkdir -p verification/evidence/release
    cp target/evidence-local/merged/*.jsonl verification/evidence/release/
    cargo run --locked -p bamts-verification --bin bamts-verification -- completion regenerate --check
    BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker BAMTS_SUITE_INTERPRETER_ADAPTER=target/release/runtime_lane_worker BAMTS_SUITE_JIT_ADAPTER=target/release/runtime_lane_worker BAMTS_SUITE_AOT_ADAPTER=target/release/runtime_lane_worker cargo run --locked -p bamts-verification --bin bamts-verification -- ledger rebuild --write
    cargo run --locked -p bamts-verification --bin bamts-verification -- completion verify --root product
    printf '%s\n' 'RELEASE GATE PASS'

# Run one compiler conformance shard locally with the lane worker wired.
# The compiler runner ships no built-in adapter, so without
# BAMTS_SUITE_COMPILER_ADAPTER every cell records BLOCKING_FAIL carrying
# "no registered adapter" and the receipt measures nothing at all.
conformance-shard index count="4" catalog="typescript-7.0.2":
    cargo build --locked --release -p bamts-verification --bin ts_lane_worker
    receipt="target/evidence-local/{{catalog}}/{{index}}.jsonl" && mkdir -p "$(dirname "$receipt")" && BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker cargo run --locked --release -p bamts-verification --bin bamts-verification -- suite run --catalog {{catalog}} --shard "{{index}}/{{count}}" --receipt "$receipt" --runner compiler --platform {{host_triple}} --workflow local --run-id local --run-attempt 1 --source-sha "$(git rev-parse HEAD)" --job conformance-shard --host "$(uname -sm | tr ' ' '-')" --runtime "node-v24.18.0;rust-$(rustc --version)" && printf 'SHARD %s/%s RECEIPT %s\n' "{{index}}" "{{count}}" "$receipt"

# Check that the whole workspace, tests included, still builds for every host
# the product targets. This proves only that it compiles.
xcheck:
    for target in {{xcheck_targets}}; do cargo check --workspace --all-targets --locked --target "$target"; done
    printf '%s\n' 'XCHECK PASS'

# Fail when code outside bamts-platform reads /proc or /sys, or runs numactl or
# sysctl, so OS facts stay behind the platform crate. It is a tripwire for
# literals, not a proof: it misses a path built from parts or a command named by
# a variable. It uses grep because it exists on every host; an rg missing from
# PATH would make a ripgrep search print nothing and pass.
#
# A search that cannot see must not pass. BSD grep on macOS exits 1 for a missing
# directory, the same as "no match", so exit codes cannot tell. bamts-platform
# reads /proc and /sys by design, so a search that finds nothing there is blind.
portability-check:
    #!/usr/bin/env bash
    set -euo pipefail
    pattern='"/(proc|sys)/|Command::new\("(numactl|sysctl)"'
    status=0
    found="$(grep -rnE --include='*.rs' "$pattern" crates)" || status=$?
    if [[ $status -gt 1 ]]; then
        printf '%s\n' 'PORTABILITY ERROR: the search itself failed'
        exit 1
    fi
    if ! grep -q '^crates/bamts-platform/src/' <<<"$found"; then
        printf '%s\n' 'PORTABILITY ERROR: the search found nothing in bamts-platform, so it cannot be trusted'
        exit 1
    fi
    hits="$(grep -v '^crates/bamts-platform/src/' <<<"$found" || true)"
    if [[ -n "$hits" ]]; then
        printf '%s\n' "$hits"
        printf '%s\n' 'PORTABILITY FAIL'
        exit 1
    fi
    printf '%s\n' 'PORTABILITY PASS'
