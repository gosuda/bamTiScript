# Repository obligations

## Authority and evidence

- Treat `.references/` as read-only study material. Inspect release metadata, public declarations, tests, baselines, and observable behavior, but never copy implementation code or transcribe reference function bodies; bamTiScript is a clean-room Rust implementation.
- Keep completion claims inside the stable TypeScript 7.0.2 product contract in `.outline/type-script-7.0.2-completion.md`, and require the receipt-backed root gates in `.outline/GATES.md`. A passing leaf test or one execution tier is not evidence that the compiler, package, runtime, native tiers, or product root is complete.
- Never hand-edit generated authority outputs. Regenerate `verification/manifest.lock.json` with `cargo run -p bamts-verification -- catalog regenerate --release typescript-7.0.2` and `crates/bamts-compiler/src/generated/diagnostic_messages.rs` with `cargo run -p bamts-verification -- diagnostics regenerate`; use the corresponding `--check` mode to prove committed bytes are current. Edit `verification/completion-program.toml` directly, then run `cargo run -p bamts-verification -- completion regenerate` to canonicalize it. `proof/completeness-ledger.json` and `verification/evidence/` are ignored build outputs; `just release-gate` regenerates them at HEAD.
- When adding, removing, or renaming a formal obligation, follow `formal/extension_policy.md` end to end: change the authority first, update the sorted `verification/catalog-inputs.json`, and route manifest regeneration, the dependency-closed G4 receipt, and ledger rebuild through the cluster integrator. Direct edits or a solo G4 result cannot establish formal-catalog authority.

## Compiler invariants

- Append `NodeKind` and `TokenKind` variants rather than reordering or removing them; their discriminants cross scanner, parser, binder, checker, and emitter boundaries.
- Preserve source coordinates as `Utf16Pos`/`TextRange` values. Convert through `SourceText` rather than assigning UTF-8 byte offsets, and reject boundaries inside surrogate pairs; TypeScript diagnostics and source maps use UTF-16 code units.

## Evidence hazards

- Keep `verification/ts-suite-ledger.json` ignored and ephemeral; never force-stage it.
- Accept BH1 performance evidence only when every fingerprint and runtime condition in `perf/hosts/bh1.toml` matches exactly. In particular, preserve the pinned governor, swap total, CPU affinity, NUMA policy, and memory nodes; an unbound or mismatched run is invalid evidence, not a slower sample.
- Keep each commit to one mechanism and make every intermediate commit build with its applicable checks. This repository relies on bisectable commit series, so a definition rename and all required callers belong in the same buildable commit rather than in temporarily broken stages.
