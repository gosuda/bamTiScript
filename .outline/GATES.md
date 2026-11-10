# Gates: bamTiScript stable TypeScript 7.0.2 completion

Scope: Complete the clean-room Rust compiler, TypeScript-compatible Node 24 API package, ECMAScript runtime, native tiers, formal proof bindings, target cells, and release evidence for the stable TypeScript 7.0.2 product contract.

- [ ] G2: The immutable authority and generated catalogs bind stable TypeScript 7.0.2 and no stale primary TypeScript release
  CHECK: cargo run -p bamts-verification -- completion verify --root authority
  EXPECT: AUTHORITY COMPLETE release=typescript-7.0.2

- [ ] G3: Every applicable stable TypeScript 7.0.2 compiler, toolchain, CLI, and historical-compatibility obligation has an observed PASS receipt
  CHECK: cargo run -p bamts-verification -- completion verify --root compiler
  EXPECT: COMPILER COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0

- [ ] G4: The bamti Node 24 package implements tsc and all thirteen stable native-preview export subpaths, including API-reachable language-service behavior
  CHECK: cargo run -p bamts-verification -- completion verify --root package
  EXPECT: PACKAGE COMPLETE exports=13 cli=PASS api=PASS

- [ ] G5: The ECMAScript runtime passes every applicable test262 obligation in Interpreter, JIT, and AOT modes
  CHECK: cargo run -p bamts-verification -- completion verify --root runtime
  EXPECT: RUNTIME COMPLETE modes=3 blocking=0 external_blocked=0

- [ ] G6: Interpreter, JIT, AOT, formal correspondence, target cells, and performance evidence satisfy every compiler-product release obligation
  CHECK: cargo run -p bamts-verification -- completion verify --root native
  EXPECT: NATIVE COMPLETE formal=PASS

- [ ] G7: The strict TypeScript-product completion gate accepts only receipt-backed PASS states or exact machine-evidenced policy exclusions
  CHECK: cargo run -p bamts-verification -- completion verify --root product
  EXPECT: PRODUCT COMPLETE release=typescript-7.0.2 blocking=0 external_blocked=0 catalog_errors=0

- [ ] G8: Repository-required Rust, formal, corpus, npm, workflow, and release checks pass once on the completed tree
  CHECK: just release-gate
  EXPECT: RELEASE GATE PASS

- [x] G9: Regenerating every authority-derived artifact is byte-identical to the committed completion evidence
  CHECK: cargo run -p bamts-verification -- completion regenerate --check
  EXPECT: COMPLETION PROGRAM PASS mode=check
