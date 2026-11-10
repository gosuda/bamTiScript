---
artifact_readiness: implementation-ready
execution: code
release: typescript-7.0.2
product: bamti
host: node-24
---

# bamTiScript stable TypeScript 7.0.2 completion

## Goal capsule

Complete the clean-room Rust TypeScript compiler and native execution product against stable TypeScript 7.0.2. Ship the `bamti` Node 24 package with `tsc` and all thirteen stable native-preview export subpaths. Require current receipt-backed evidence for compiler, package, ECMAScript runtime, Interpreter/JIT/AOT, formal correspondence, target cells, and performance. Do not call unrelated full-Node, N-API, WebAssembly, WASI, VS Code, or standalone LSP work part of this completion root.

## Frozen scope

- Stable authority: TypeScript tag `v7.0.2`, commit `1e4744d68260a7cb91b62b12edc3f6a2187faaf1`, and the published npm tarball digest already locked by `package-lock.json`.
- Historical compatibility: retain TypeScript 5.9 and 6.0 inputs only when the stable 7.0.2 oracle still accepts them. They never act as oracles.
- Public package: package identity `bamti`; Node 24 host; current five artifact targets; `tsc`; package root; `package.json`; sync, async, filesystem, protocol, AST, is, factory, utils, scanner, visitor, and clone subpaths.
- Public API behavior: program, project, snapshot, checker, symbol, type, signature, completion, reference, and disposal behavior reachable from those subpaths is blocking.
- Exact exclusions: standalone LSP transport, VS Code extension, the internal fourslash DSL, V8 internals, proposal-stage test262 staging, full Node runtime parity, N-API, WebAssembly, and WASI. An excluded directory cannot hide an API-reachable operation.
- Runtime: every applicable stable test262 obligation required by bamTiScript native execution must pass in Interpreter, JIT, and AOT modes. Stable `Intl` and `Temporal` stay in scope.
- Final scoped roots permit zero `BLOCKING_FAIL`, zero `EXTERNAL_BLOCKED`, and zero `INAPPLICABLE_CATALOG_ERROR`.
- `.references/` is study-only. Workers may inspect release metadata, public declarations, test inputs, baselines, and observable behavior. They must not copy implementation code.
- Execution hosts: Interpreter, JIT, AOT, and direct native executable output run on `aarch64-apple-darwin`, `x86_64-apple-darwin`, `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `x86_64-pc-windows-msvc`. `s390x-unknown-linux-gnu` and `riscv64gc-unknown-linux-gnu` remain target cells.
- Evidence host: primary receipts for every catalog are produced on `aarch64-apple-darwin` through the repository `Justfile`. Other hosts are proven by their target cell, the corpus differential, and the clean-install contract.
- Continuous integration: hosted workflows remain. Local `Justfile` recipes are an additional runner, not a replacement.
- Historical catalogs are owned, measured locally, and filtered by the 7.0.2 applicability rule above.

## Product roots

```text
TypeScript product
|- compiler: scanner -> parser -> binder -> checker -> emit -> projects -> CLI
|- package: tsc + persistent API transport + thirteen public export subpaths
|- runtime: stable ECMAScript behavior in Interpreter, JIT, and AOT
'- native: bytecode + JIT + AOT + formal correspondence + targets + performance
```

Each root is independently measurable. The product root requires all four. Node 24 is the package host contract, not a promise to reimplement every Node subsystem.

## Evidence contract

`verification/completion-program.toml` owns the root, cluster, leaf, obligation-matcher, and check mapping. Workers cannot choose their own scope or exclusions.

A logical obligation identity is:

```text
<authority>/<runner>/<case>#<configuration>#<observable>#<mode>#<platform>
```

`verification/evidence/<catalog>/<shard>.jsonl` uses `bamti.evidence/v1`. Its header binds the source authority digest, catalog manifest digest, candidate tree and binary digests, harness digest, execution mode, platform, normalized environment, and runner version. Every sorted row records the logical obligation, exact argv and working-directory policy, declared observable set, observed artifact digests, terminal state, duration, and diagnostic detail. A `PASS` without a matching current receipt is invalid.

Shards use sorted-index striding: obligation at sorted index `i` belongs to shard `k/N` iff `i % N == k`. Merge rejects a missing shard, duplicate obligation, zero-case shard, mixed authority, mixed candidate, mixed harness, undeclared normalization, missing observable, timeout reclassified as PASS, and any unconsumed row.

`proof/completeness-ledger.json` is a generated projection of the authority manifest, evidence, and exact policy records. G0 continues to prove integrity. The strict completion roots additionally reject every incomplete state.

## Public interfaces

- One compiler-host and virtual-filesystem contract serves CLI, configuration, module resolution, build, watch, and package callbacks.
- Immutable workspace snapshots own project generations, open-file state, invalidation, disposal, and stale-handle errors.
- Public AST values preserve stable `SyntaxKind` numbers, UTF-16 spans, trivia, child order, factories, updates, cloning, visiting, and scanner behavior.
- Public node, symbol, type, and signature handles are snapshot-scoped and cannot alias after disposal.
- One protocol schema generates Rust dispatch and the sync and async JavaScript clients. The package transport is the stable child-process `--api` contract; N-API is not its transport.
- Diagnostics and artifacts are deterministic values: code, category, message, UTF-16 span, order, path policy, exit status, JavaScript, declarations, maps, traces, build info, and explicit writes.
- Interpreter, JIT, and AOT consume the same lowered program and have identical observable semantics.

## Definition of done

.outline/GATES.md is the acceptance contract; verification/completion-program.toml is the closed leaf set.
