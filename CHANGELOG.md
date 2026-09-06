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

- `docs/release/runbook.md`: F3.1 completion runbook reconciled with the completion
  evidence program. The completion-gate ritual is the verified CLI surface:

  ```bash
  cargo run -p bamts-verification -- completion verify --leaf <LEAF> --aspect <ASPECT>
  # scopes: --leaf | --cluster | --track | --wave | --root; exactly one required
  # aspects: contract, evidence, coverage, regression, mutation, aggregate (default: aggregate)
  ```

  Gate evidence binds content-addressed receipts over the `EVIDENCE:` line grammar:

  ```text
  EVIDENCE: receipt=<repo-relative-path> sha256=<64-hex-digest>
  ```

  The verifier canonicalizes the receipt under the repository root and requires
  `sha256(file bytes) = sha256` (see `crates/bamts-verification/src/completion.rs`,
  `current_evidence`). The global completeness ledger `proof/completeness-ledger.json`
  (schema `bamti.completeness-ledger/v1`) is rebuilt from the canonical receipt set:

  ```bash
  cargo run -p bamts-verification -- ledger rebuild --write   # rewrite proof/completeness-ledger.json
  cargo run -p bamts-verification -- ledger rebuild --check   # drift-check only
  ```

- `CHANGELOG.md`: created under F3.1 as an in-progress evidence record. The runbook
  previously forbade an authored root changelog; that clause is updated to require
  this file carry in-progress entries only, so no line here asserts a release.

### Known incomplete

- F3.2 (final TypeScript-product release gate and tag evidence) is blocked: the
  authenticated evidence authority and repository `Justfile` (`just release-gate`)
  are unavailable, and the no-commit/no-push constraint forbids tag creation.
- Completion roots (`authority`, `package`, `native`, `product`) exit 1 until
  receipt-backed obligations are proven (see `.outline/sdd/progress.md`).
