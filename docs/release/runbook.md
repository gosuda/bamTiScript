# TypeScript 7.0.2 completion runbook

This runbook defines the maintainer procedure for the stable TypeScript 7.0.2 product gate. It does not declare the product complete.

The release is eligible only when every check in `.outline/GATES.md` passes with current evidence. At present, several leaf gates and the authenticated evidence path are blocked. Do not create a release tag or publish a stable package while any required gate is open.

## Authorities

Use these files as the release authorities:

- `.outline/type-script-7.0.2-completion.md` defines the product scope.
- `.outline/GATES.md` defines the root checks and expected output.
- `vendor/sources.toml` defines pinned external sources.
- `verification/catalog-inputs.json` defines the sorted catalog inputs.
- `verification/manifest.lock.json` is the generated catalog manifest.
- `verification/completion-program.toml` is the completion program: the closed leaf set, edited directly and canonicalized with `completion regenerate`.
- `proof/completeness-ledger.json` is the generated completion ledger.

Treat `.references/` as read-only study material. Do not copy implementation code from it.

## Stop conditions

Stop the release procedure when one of these conditions is true:

- A required gate is unchecked or lacks current evidence.
- A required obligation is not `PASS`.
- A receipt is missing, stale, or not produced by the approved independent runner.
- An external target runner or exact performance host is unavailable.
- A generated-file check reports drift.
- The repository release command is unavailable.
- The working tree does not identify one release commit.

Do not replace authenticated evidence with local hashes or a hand-written receipt. Do not convert a blocked result into a pass.

## Prepare the release candidate

1. Select one release commit.
2. Confirm that the working tree is clean.
3. Use the Rust toolchain pinned by `rust-toolchain.toml`.
4. Use Node.js 24 for package and corpus checks.
5. Materialize each required external source from `vendor/sources.toml`.
6. For BH1 performance evidence, match every condition in `perf/hosts/bh1.toml`. A mismatched run is invalid evidence.

The TypeScript primary-test source can be materialized with:

```bash
cargo run -p bamts-verification -- source fetch typescript-primary-tests --dest target/authority/typescript-7.0.2-tests
```

Use `source fetch <name> --dest <directory>` for other declared sources. Do not use an unpinned checkout as release evidence.

## Regenerate authority-derived files

Never hand-edit the generated files named in this section.

### Catalog manifest

```bash
cargo run -p bamts-verification -- catalog regenerate --release typescript-7.0.2
cargo run -p bamts-verification -- catalog regenerate --release typescript-7.0.2 --check
```

### Diagnostic messages

```bash
cargo run -p bamts-verification -- diagnostics regenerate
cargo run -p bamts-verification -- diagnostics regenerate --check
```

### Completion program

```bash
cargo run -p bamts-verification -- completion regenerate
cargo run -p bamts-verification -- completion regenerate --check
```

### Completion ledger

```bash
cargo run -p bamts-verification -- ledger rebuild --write
cargo run -p bamts-verification -- ledger rebuild --check
```

Run these commands directly. Do not pipe a verification command through another process. A successful consumer can hide a failed producer.

When a formal obligation changes, follow `formal/extension_policy.md` before catalog regeneration. The cluster integrator owns the dependency-closed G4 receipt and the ledger rebuild.

## Produce and merge suite evidence

The verification CLI accepts these suite forms:

```text
suite run --catalog <id> --shard <index>/<count> --receipt <path> --runner <name> --platform <name>
suite merge --catalog <id> --receipts <directory> --out <path> [--check]
```

Only the approved independent runner may produce release receipts. Each shard must bind the selected source, candidate, harness, runner, and platform required by the evidence schema. Merge only a complete and consistent shard set. `ts_conformance --shards k/N` is one-based and `suite run --shard i/N` is zero-based; workflows convert once before they invoke `suite run`.

`verification/ts-suite-ledger.json` is ephemeral and ignored. Never force-stage it. `proof/completeness-ledger.json` and `verification/evidence/` are ignored build outputs; `just release-gate` regenerates them at HEAD.

## Run repository checks

Run the repository checks on the completed tree. The clean-port integration ladder requires:

```bash
cargo check -p bamts-compiler --lib --locked
cargo build --workspace --all-targets --locked
cargo test --workspace --locked
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked -- -D warnings
```

Run the package, corpus, formal, and performance checks that the affected gates require. A leaf test or one execution tier does not prove a product root.

`.outline/GATES.md` also requires:

```bash
just release-gate
```

Run just release-gate from the repository root.

## Completion gate ritual

Every leaf, cluster, and root gate is a completion verify invocation. Pass exactly one of --leaf, --cluster, or --root; there is no aspect argument.

```bash
cargo run -p bamts-verification -- completion verify --leaf <LEAF>
```

A passing gate prints its success line (`LEAF <LEAF> COMPLETE`). A non-zero exit or a different line fails the gate.

### Global completeness ledger

`proof/completeness-ledger.json` (schema `bamti.completeness-ledger/v2`) is generated from the canonical receipt set. Do not hand-edit it.

```bash
cargo run -p bamts-verification -- ledger rebuild --write
cargo run -p bamts-verification -- ledger rebuild --check
```

`--write` rewrites the ledger. `--check` reports drift without writing. The two flags are mutually exclusive. Rebuild after any exit-gate evidence change, then re-run the affected `completion verify` commands.

## Verify F3 and completion roots

Run the F3 checks before the dependent F3 cluster and product root checks:

```bash
cargo run -p bamts-verification -- completion verify --leaf F3.1
cargo run -p bamts-verification -- completion verify --leaf F3.2
```

F3.1 proves the runbook obligation. F3.2 owns final release and tag evidence. F3.1 cannot override F3.2.

Run each root command exactly as recorded in `.outline/GATES.md`:

```bash
cargo run -p bamts-verification -- completion verify --root authority
cargo run -p bamts-verification -- completion verify --root compiler
cargo run -p bamts-verification -- completion verify --root package
cargo run -p bamts-verification -- completion verify --root runtime
cargo run -p bamts-verification -- completion verify --root native
cargo run -p bamts-verification -- completion verify --root product
```

Compare the output with the expected line in `.outline/GATES.md`. A non-zero exit status or different result blocks the release.

## Audit evidence

Before release, confirm all of these facts:

- Every required leaf, cluster, and root check passes.
- Every selected obligation has one current receipt.
- The receipt binds the selected release commit and required execution mode.
- The ledger contains no blocking, external-blocked, catalog-error, timeout, crash, skip, or missing-receipt state in release scope.
- BH1 evidence matches `perf/hosts/bh1.toml` exactly.
- Every generated-file `--check` command reports identical bytes.
- The product root reports the exact expected completion line.

## Prepare release notes

`CHANGELOG.md` at the repository root is an in-progress evidence record. It must not claim a release, version, tag, or shipped package while any required gate is open. Entries in that file cite the exact `completion verify` and `ledger rebuild` commands used as evidence. Release notes for a published tag remain an F3.2 deliverable and are prepared only after the product root passes.

Prepare release notes after the product root passes. Derive each statement from the release diff and accepted receipts. Include:

- the `bamti` package version;
- the stable TypeScript 7.0.2 authority;
- user-visible compiler, CLI, package, runtime, and native changes;
- breaking changes and required user action;
- supported targets covered by the release-build workflow matrices;
- known limitations that remain in the accepted product contract;
- links to migration or operator instructions when they exist.

Do not publish test counts, performance claims, target support, or compatibility claims without current evidence.

## Tag eligibility

A maintainer may create the release tag only when:

1. Every check in `.outline/GATES.md` is complete.
2. `completion verify --root product` returns the exact expected result.
3. F3.2 passes with current tag evidence.
4. All generated-file checks are identical.
5. The working tree is clean at the selected release commit.
6. The release notes contain only evidence-backed claims.

The tag name and publication command belong to the approved F3.2 release procedure. This runbook does not invent them.

## Abort and retry

When a check fails:

1. Stop the release procedure.
2. Keep the failing output and identify the owning gate.
3. Classify the result as a product defect, evidence defect, missing runner, or host mismatch.
4. Fix the source of the failure. Do not edit generated evidence by hand.
5. Regenerate only through the approved commands.
6. Re-run the affected leaf, its parent gates, and every invalidated root.
7. Restart tag eligibility review only after all required checks pass.

Do not discard unrelated working-tree changes. Do not move a tag to hide a failed release. Publish a later corrected release only through a newly approved F3.2 procedure.
