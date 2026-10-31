set shell := ["bash", "-euo", "pipefail", "-c"]

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
    receipt="target/evidence-local/{{catalog}}/{{index}}.jsonl" && mkdir -p "$(dirname "$receipt")" && BAMTS_SUITE_COMPILER_ADAPTER=target/release/ts_lane_worker cargo run --locked --release -p bamts-verification --bin bamts-verification -- suite run --catalog {{catalog}} --shard "{{index}}/{{count}}" --receipt "$receipt" --runner compiler --platform x86_64-unknown-linux-gnu --workflow local --run-id local --run-attempt 1 --source-sha "$(git rev-parse HEAD)" --job conformance-shard --host "$(uname -sm | tr ' ' '-')" --runtime "node-v24.18.0;rust-$(rustc --version)" && printf 'SHARD %s/%s RECEIPT %s\n' "{{index}}" "{{count}}" "$receipt"

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
