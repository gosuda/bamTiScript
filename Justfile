set shell := ["bash", "-euo", "pipefail", "-c"]

host_triple := `rustc -vV | awk '/^host:/{print $2}'`
export PATH := env_var('HOME') + "/.nvm/versions/node/v24.18.0/bin:/opt/homebrew/opt/lld/bin:/opt/homebrew/opt/llvm/bin:" + env_var('PATH')

doctor:
    [[ "$(node -v)" == "v24.18.0" ]]
    [[ "$(rustc -V)" == *"1.97.1"* ]]
    [[ "$(racket --version)" == *"9.2"* ]]
    command -v ld.lld llvm-readelf lake
    test -x formal/quint/node_modules/.bin/quint
    printf '%s\n' 'DOCTOR PASS'

# Fails while any gate ledger has an unchecked box or pending evidence, and lists
# the open ledgers; prints ALL MET otherwise. This is the check for GATES.md G1.
gate-status:
    python3 -c 'import glob,re,sys; rows=[(f,len(re.findall(r"(?m)^- \[ \]",t)),len(re.findall(r"(?m)^  EVIDENCE: pending\s*$",t))) for f in sorted(glob.glob(".outline/gates/*.md")) for t in [open(f).read()]]; open_=[r for r in rows if r[1] or r[2]]; [print("OPEN %s unchecked=%d pending=%d"%r) for r in open_]; print("NO LEDGERS FOUND" if not rows else "ALL MET" if not open_ else "OPEN LEDGERS: %d of %d"%(len(open_),len(rows))); sys.exit(1 if open_ or not rows else 0)'

ci: ci-quality ci-npm ci-corpus xcheck portability-check
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

# Rebuilds the lane workers, reruns only the rows of one family, and fails if any row
# that passed in the receipt no longer does. A fix must convert a row and regress none.
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
    cargo build --locked --release -p bamts-verification --bin ts_lane_worker
    cargo run --locked -p bamts-verification --bin bamts-verification -- completion regenerate --check
    cargo run --locked -p bamts-verification --bin ts_conformance -- audit-ledger --require-complete
    BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker cargo run --locked -p bamts-verification --bin bamts-verification -- ledger rebuild --check
    cargo run --locked -p bamts-verification --bin bamts-verification -- completion verify --root product
    printf '%s\n' 'RELEASE GATE PASS'

# Machine-local checker (proven on this host); a portable in-repo checker is a deliberate future decision.
# Verify one outline leaf gate file without mutating it: the gate whose
# CHECK is `just leaf-gate <id>` is the leaf's recursive self-gate, so
# every other gate must already carry a checked box and non-pending
# evidence. This attests to recorded checkbox state from a prior checker
# pass, not to freshly re-run checks; the mutating checker's run of this
# recipe then supplies the self-gate's own evidence (run leaves twice:
# the first flips the body, the second converges the self-gate).
leaf-gate leaf:
    python3 -c 'import sys,re; t=open(sys.argv[1]).read(); blocks=re.split(r"(?m)^(?=- \[[ x]\] G\d+)",t); body="\n".join(b for b in blocks if "just leaf-gate" not in b); sys.exit(1 if (re.search(r"^- \[ \]",body,re.M) or re.search(r"^  EVIDENCE: pending\s*$",body,re.M)) else 0)' .outline/gates/{{leaf}}.md
    printf 'LEAF %s PASS\n' "{{leaf}}"

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
    cargo check --workspace --all-targets --locked --target x86_64-apple-darwin
    cargo check --workspace --all-targets --locked --target x86_64-unknown-linux-gnu
    cargo check --workspace --all-targets --locked --target aarch64-unknown-linux-gnu
    cargo check --workspace --all-targets --locked --target x86_64-pc-windows-msvc
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
