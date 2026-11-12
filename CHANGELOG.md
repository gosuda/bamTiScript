# Changelog

This file records in-progress, evidence-backed changes only. It claims no release: no
version has shipped, and no tag or stable package exists while any gate in
`.outline/GATES.md` is open. Release notes remain a downstream F3.2 deliverable per
`docs/release/runbook.md`.

## Unreleased — in progress

### Changed

- Property definition and reference navigation now uses the same property
  identities as rename. Package API and LSP results keep unrelated objects
  separate, and LSP reference filtering respects declaration locations.
- API startup now duplicates inherited standard input instead of reopening
  `/dev/stdin`. Node-spawned socket input works with the existing reader
  cancellation and shutdown path.

- `bamts-verification completion verify` takes exactly one of `--leaf`,
  `--cluster`, or `--root` and reads measured rows from
  `proof/completeness-ledger.json`. The aspect, track, and wave scopes, the
  `leaf-evidence`, `completion evidence`, `toolchain`, and `perf` commands, the
  Markdown gate ledgers, the target-cell records, and the weekly audit workflow
  are removed. The ledger and `verification/evidence/` are ignored build
  outputs; `just release-gate` regenerates them at HEAD:

  ```bash
  cargo run -p bamts-verification -- completion verify --root product
  cargo run -p bamts-verification -- ledger rebuild --write
  ```

- `CHANGELOG.md`: created under F3.1 as an in-progress evidence record. The runbook
  previously forbade an authored root changelog; that clause is updated to require
  this file carry in-progress entries only, so no line here asserts a release.

- Interface binding now records additive metadata for the identity and
  overload work ahead: per-member declaration occurrences, signature
  parameter symbols, call-candidate order, and written return-type
  provenance, plus a purity-guarded overload-signature view. Parameter
  labels and declared returns now participate in signature identity, so
  `(a: string)` and `(b: string)` spellings intern distinctly. No consumer
  reads the new surfaces yet; rendered output and relation checks are
  unchanged.

### Known incomplete

- F3.2 (final TypeScript-product release gate and tag evidence) is blocked: the
  authenticated evidence authority is unavailable.
- Completion roots (`authority`, `compiler`, `package`, `runtime`, `native`,
  `product`) exit 1 until receipt-backed obligations are proven.
