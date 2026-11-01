# Gates: bamTiScript stable TypeScript 7.0.2 completion

Scope: Complete the clean-room Rust compiler, TypeScript-compatible Node 24 API package, ECMAScript runtime, native tiers, formal proof bindings, target cells, and release evidence for the stable TypeScript 7.0.2 product contract.

- [ ] G1: Every leaf and integration ledger is met with recorded evidence
  CHECK: just gate-status
  EXPECT: ALL MET
  EVIDENCE: 2026-08-28 not run to ALL MET; leaf ledgers still have unchecked G1-G6 boxes (F2.1, A3.1, C4.2, A2.7 G2-G6)

- [ ] G2: The immutable authority and generated catalogs bind stable TypeScript 7.0.2 and no stale primary TypeScript release
  CHECK: cargo run -p bamts-verification -- completion verify --root authority
  EXPECT: AUTHORITY COMPLETE release=typescript-7.0.2
  EVIDENCE: 2026-08-28 `bamts-verification completion verify --root authority` exit 1: unproven children A1.1 through A1.5, A2.1 through A2.3, A2.6, A2.7, and 11 more

- [ ] G3: Every applicable stable TypeScript 7.0.2 compiler, toolchain, CLI, and historical-compatibility obligation has an observed PASS receipt
  CHECK: cargo run -p bamts-verification -- completion verify --root compiler
  EXPECT: COMPILER COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0
  EVIDENCE: 2026-08-28 `completion verify --root compiler` exit 1: unproven B0.1, B1.1 through B1.4, B2.1, B2.2, B3.1 through B3.3, and 19515 more. Ledger n=78498 PASS=0 BLOCKING_FAIL=71750
  STATUS: progress is not recorded in this file. Run `just status-report`; it writes target/evidence-local/status.md from the receipts. Dated notes that used to be here are in .outline/notes/gates-progress-2026-09.md.

- [ ] G4: The bamti Node 24 package implements tsc and all thirteen stable native-preview export subpaths, including API-reachable language-service behavior
  CHECK: cargo run -p bamts-verification -- completion verify --root package
  EXPECT: PACKAGE COMPLETE exports=13 cli=PASS api=PASS
  EVIDENCE: 2026-08-28 `completion verify --root package` exit 1: unproven F2.1 through F2.4, cluster:F2, root:package; F2.1 through F2.3 have no checked mutation contract; `typescript-7.0.2:tests/cases/compiler/2dArrays.ts` BLOCKING_FAIL and 19363 more. F2.1 orphan path is gone

- [ ] G5: The ECMAScript runtime passes every applicable test262 obligation in Interpreter, JIT, and AOT modes
  CHECK: cargo run -p bamts-verification -- completion verify --root runtime
  EXPECT: RUNTIME COMPLETE modes=3 blocking=0 external_blocked=0
  EVIDENCE: 2026-08-28 `completion verify --root runtime` exit 1: unproven C0.1, C1.1 through C1.3, C10.1 through C10.6, and 53679 more

- [ ] G6: Interpreter, JIT, AOT, formal correspondence, target cells, and performance evidence satisfy every compiler-product release obligation
  CHECK: cargo run -p bamts-verification -- completion verify --root native
  EXPECT: NATIVE COMPLETE formal=PASS targets=49/49 benchmarks=9/9
  EVIDENCE: 2026-08-28 `completion verify --root native` exit 1: unproven E1.1, E1.2, E2.1 through E2.3, E3.1 through E3.3, E4.1, E4.2, and 389 more

- [ ] G7: The strict TypeScript-product completion gate accepts only receipt-backed PASS states or exact machine-evidenced policy exclusions
  CHECK: cargo run -p bamts-verification -- completion verify --root product
  EXPECT: PRODUCT COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0 catalog_errors=0
  EVIDENCE: 2026-08-28 `completion verify --root product` exit 1: unproven B0.1, B1.1 through B3.3, and 73626 more. `ledger rebuild --check` reports E_SET_MISMATCH: no canonical receipt set found
  RECEIPTS: `ts_conformance --shards k/N` is deliberately one-based. `bamts-verification suite run --shard i/N` is deliberately zero-based. Workflows convert once before invoking the low-level runner.

- [ ] G8: Repository-required Rust, formal, corpus, npm, workflow, and release checks pass once on the completed tree
  CHECK: just release-gate
  EXPECT: RELEASE GATE PASS
  EVIDENCE: 2026-08-28 not run; the root `Justfile` now defines the ordered fail-closed release gate

- [x] G9: Regenerating every authority-derived artifact is byte-identical to the committed completion evidence
  CHECK: cargo run -p bamts-verification -- completion regenerate --check
  EXPECT: COMPLETION PROGRAM PASS mode=check
  EVIDENCE: 2026-08-28 `cargo run -p bamts-verification --locked -- completion regenerate --check` → `COMPLETION PROGRAM PASS mode=check` (exit 0). A2.7/A3.1/C4.2/F2.1 `owns` match `.outline/type-script-7.0.2-completion.md` Owned paths (`ci.yml`; `verification/evidence/typescript-7.0.2/*.jsonl`; `regexp_v/`; `api_server/`)
