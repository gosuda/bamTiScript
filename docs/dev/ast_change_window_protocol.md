# AST and Diagnostic Change-Window Protocol

## Purpose

Coordinate edits to shared AST discriminants, scanner/parser roots, checker interfaces, and diagnostic identity so concurrent waves cannot collide, break matches, emit invalid UTF-16 spans, or reuse diagnostic codes.

## Shared Root Modules

Only one announced owner may modify shared compiler root files during a wave:

| File Path | Functional Responsibility |
| :--- | :--- |
| `crates/bamts-compiler/src/syntax.rs` | `NodeKind`, `TokenKind`, `SourceFile`, `Statement`, `Expression` |
| `crates/bamts-compiler/src/scanner.rs` | Lexer recognition and BAMTS-L minting |
| `crates/bamts-compiler/src/parser.rs` | Grammar, BAMTS-P minting, tree construction |
| `crates/bamts-compiler/src/checker.rs` | Root checker and a C-band mint site |
| `crates/bamts-compiler/src/enum_plan.rs` | Enum-plan C-band mint site |
| `crates/bamts-compiler/src/program.rs` | Program load; BAMTS-R001 / BAMTS-R002 |
| `crates/bamts-compiler/src/diagnostic.rs` | `DiagnosticCode`, `DiagnosticSeverity` |
| `crates/bamts-compiler/src/diagnostics_parser.rs` | Native lexer/parser codes to TypeScript parse codes |
| `crates/bamts-compiler/src/generated/diagnostic_messages.rs` | Generated TypeScript 7.0.2 message table |
| `crates/bamts-compiler/src/tsc_directives.rs` | `// @flags` / `@filename`; BAMTS-D001 .. D007 |
| `crates/bamts-compiler/src/lint.rs` | Warning rule registry (`RULES`); BAMTS-W minting |

Child modules under `crates/bamts-compiler/src/binder/`, `checker/`, `emitter/`, `project/`, and `crates/bamts-cli/src/cli/` are leaf-owned. New C-band codes still require the window owner even when the mint lands in a child file.

## Window Ownership Announcement

Before editing any shared root file, acquire exclusive ownership over `hub`.

### Acquisition

Send `to: "all"`:

`ACQUIRE_AST_WINDOW: wave=<WAVE_ID> owner=<AGENT_OR_MAINTAINER> files=<FILE_LIST> pre_hashes=<path:sha256,...> reason=<SUMMARY>`

`files` and `pre_hashes` name the same paths. Record a SHA-256 for every announced file.

```bash
sha256sum <each announced file>
```

Proceed only after a hub delivery receipt of `delivered`. Treat `failed` as no acquisition.

If another live owner already holds an overlapping file, serialize: wait for that owner's `RELEASE_AST_WINDOW`. Do not edit overlapping files.

Example:

```json
{
  "op": "send",
  "to": "all",
  "message": "ACQUIRE_AST_WINDOW: wave=W2 owner=AstWindowProtocol files=crates/bamts-compiler/src/syntax.rs,crates/bamts-compiler/src/parser.rs pre_hashes=crates/bamts-compiler/src/syntax.rs:<sha256>,crates/bamts-compiler/src/parser.rs:<sha256> reason=Add import attribute syntax nodes"
}
```

### Single-worker procedure

When one worker runs alone, no hub exists. Replace the hub messages with `.outline/change-window.log`:

1. Before the first edit, append `ACQUIRE_AST_WINDOW: owner=<worker> files=<paths> pre_hashes=<path:sha256,...> reason=<summary>`. Compute hashes with `shasum -a 256 <file>`.
2. Do not acquire if the log's last entry for an overlapping file is an unreleased `ACQUIRE_AST_WINDOW`. Stop and escalate instead.
3. After the last verified edit, append `RELEASE_AST_WINDOW: owner=<worker> files=<paths> post_hashes=<path:sha256,...>`.

Fresh reads, append-only discriminants, UTF-16 rules, and diagnostic bands apply unchanged.

## Content Hashes and Fresh Reads

Hash every announced file before the first edit and after the last verified edit. Do not reuse a hash from a previous wave.

Always perform a fresh line-anchored read before modifying a file. Do not use elided rows (`…`, `..`), pagination footers, or snapshot headers as write input.

## AST and Span Invariants

### Append-only discriminants

- Append new grammar nodes to `NodeKind` in `crates/bamts-compiler/src/syntax.rs`.
- Append new token variants to `TokenKind` in `crates/bamts-compiler/src/syntax.rs`.
- Do not reorder or remove existing enum variants.
- Update matches in `scanner.rs`, `parser.rs`, `binder/`, `checker/`, and `emitter/` for every new variant.
- Do not use a non-exhaustive wildcard default in critical scanner, parser, binder, checker, or emitter passes; enumerate every variant.

### UTF-16 Code-Unit Range Invariants

- Source positions are UTF-16 code-unit offsets (`Utf16Pos` in `crates/bamts-compiler/src/source.rs`).
- `SourceText::new` indexes UTF-16 length; do not store UTF-8 byte offsets on a span.
- Construct every span with fallible `TextRange::new(start, end) -> Result<TextRange, SourcePositionError>`.
- `start.get() > end.get()` is `SourcePositionError::RangeStartAfterEnd`. Do not build a `TextRange` by struct literal.
- A UTF-16 coordinate that splits a surrogate pair is `SourcePositionError::Utf16PositionInsideSurrogatePair`.

## Diagnostic Code Bands and Catalog Generation

### Diagnostic Bands

Mint only inside the assigned band, at the listed sites:

| Band | Subsystem | Mint / definition location | Notes |
| :--- | :--- | :--- | :--- |
| `BAMTS-L001` .. | Lexer | `scanner.rs` (`parser.rs` also mints `L004`) | Scanner and lexical errors |
| `BAMTS-P001` .. | Parser | `parser.rs` | Grammar and syntax errors |
| `BAMTS-C001` .. | Checker | `checker.rs`, `enum_plan.rs`, `parser.rs` (`C051`), `binder/exports.rs`, `binder/merging.rs`, `checker/decorators.rs`, `checker/enum_namespace.rs`, `checker/overloads.rs` | Semantic / type errors |
| `BAMTS-D001` .. `BAMTS-D007` | Directives | `tsc_directives.rs` | `D001` through `D007` only |
| `BAMTS-R001` .. `BAMTS-R002` | Resource | `program.rs` | Per-file `R001`, session `R002` |
| `BAMTS-W001` .. | Warnings | `lint.rs` (`RULES`) | Warning / lint identities |
| `BAMTS-E001` .. | Engine | `diagnostic.rs` | Pipeline / engine errors |
| `TS1002` .. `TS95197` | Parity | `generated/diagnostic_messages.rs` | TypeScript 7.0.2 catalog (`CATALOG_LEN` 2130, sparse) |

Do not invent bands. Do not hand-mint `TSxxxx` codes.

### High-water-mark allocation

A new native code is the next unused integer after the highest minted code in that band. Find the mark by searching `DiagnosticCode::new("BAMTS-<band>")` under `crates/bamts-compiler/src`. Do not reuse holes. Leaves request codes through handoff; the window owner mints.

`BAMTS-D` and `BAMTS-R` are closed at the rows above until this protocol is revised against source.

### Diagnostic catalog regeneration

`crates/bamts-compiler/src/generated/diagnostic_messages.rs` is generated from `target/authority/typescript-7.0.2-tests/src/compiler/diagnosticMessages.json` by `crates/bamts-verification/src/diagnostic_catalog.rs`. Do not edit the generated module by hand.

Materialize the pinned TypeScript 7.0.2 test tree, then regenerate or check:

```bash
cargo run -p bamts-verification -- source fetch typescript-primary-tests --dest target/authority/typescript-7.0.2-tests
cargo run -p bamts-verification -- diagnostics regenerate
cargo run -p bamts-verification -- diagnostics regenerate --check
```

These argv forms are `Command::SourceFetch` and `Command::DiagnosticsRegenerate` in `crates/bamts-verification/src/main.rs`. The fetch name is `typescript-primary-tests` in `vendor/sources.toml`. `--check` must be identical to a write.

## Child Leaf Handoff Contract

Leaves in `binder/`, `checker/`, `emitter/`, and `project/` send integration requests to the window owner when a shared root must change.

Handoff payload:

1. `leaf_id`: completion leaf (for example `B1.2`).
2. `required_nodes`: new `NodeKind` / `TokenKind` variants and fields.
3. `required_diagnostics`: requested band and count; the owner assigns high-water codes.
4. `child_patch`: path or contents of the isolated child changes.
5. `pre_hashes`: SHA-256 of each announced shared-root file the request depends on.
6. `post_hashes`: SHA-256 of the leaf's child files after the leaf's work.

If the owner rebases, or any listed `pre_hashes` no longer match the tree, rehash, reject the stale handoff, and require the leaf to re-read and resubmit. Do not integrate against stale pre-hashes.

The owner mints into shared roots, verifies, and notifies the leaf.

## Operational Rules

1. Non-owners must never `git restore`, `git checkout`, or `git reset` on the shared root files listed above.
2. Apply edits using exact line numbers and target strings from a recent snapshot.
3. Run verification commands directly. Do not pipe through `head` or `tail`.

## Verification Ladder

```bash
cargo check -p bamts-compiler
cargo test -p bamts-compiler --lib
cargo run -p bamts-verification -- diagnostics regenerate --check
cargo clippy -p bamts-compiler --all-targets -- -D warnings
```

If the leaf gate includes mutation verification (G5 aspect), apply a temporary mutation that must fail, then restore the correct implementation.

## Window Release Announcement

After verification, hash every announced file again and broadcast `to: "all"`:

`RELEASE_AST_WINDOW: wave=<WAVE_ID> owner=<AGENT_OR_MAINTAINER> files=<FILE_LIST> status=VERIFIED pre_hashes=<path:sha256,...> post_hashes=<path:sha256,...>`

`pre_hashes` and `post_hashes` cover every announced file. Require a `delivered` receipt.

Example:

```json
{
  "op": "send",
  "to": "all",
  "message": "RELEASE_AST_WINDOW: wave=W2 owner=AstWindowProtocol files=crates/bamts-compiler/src/syntax.rs,crates/bamts-compiler/src/parser.rs status=VERIFIED pre_hashes=crates/bamts-compiler/src/syntax.rs:<sha256>,crates/bamts-compiler/src/parser.rs:<sha256> post_hashes=crates/bamts-compiler/src/syntax.rs:<sha256>,crates/bamts-compiler/src/parser.rs:<sha256>"
}
```
