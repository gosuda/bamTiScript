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

`verification/completion-program.toml` owns the root, track, cluster, leaf, obligation-matcher, mutation, and check mapping. Workers cannot choose their own scope or exclusions.

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

## Command surface

Wave W0 adds these commands and keeps existing formal and G0 commands:

```text
bamts-verification authority verify --release typescript-7.0.2
bamts-verification source fetch <name> --dest <path>
bamts-verification catalog regenerate --release typescript-7.0.2 [--check]
bamts-verification suite run --catalog <id> --shard <k>/<n> --receipt <path>
bamts-verification suite merge --catalog <id> --receipts <dir> --out <path>
bamts-verification ledger rebuild
bamts-verification completion verify (--leaf|--cluster|--track|--wave|--root) <id> [--aspect <name>]
bamts-verification completion regenerate --check
just leaf-gate <id>
just cluster-gate <id>
just track-gate <id>
just wave-gate <id>
just root-gate <id>
just release-gate
```

## Ownership contract

A leaf owns only the paths in its row. Shared registries and generated artifacts have one serialized integration owner: workspace `Cargo.toml`, verification `lib.rs` and `main.rs`, ledger vocabulary and command registration, compiler module registries, `verification/manifest.lock.json`, `proof/completeness-ledger.json`, evidence merges, npm workspace registration, and release metadata. Leaves that need a shared registry add a disjoint module and hand the one-line registry change to their cluster integrator. No shard worker edits a manifest, ledger, or another shard receipt.

## Depth tree and waves

Depth is seven: product -> root -> track -> cluster -> leaf -> logical shard -> obligation cell. Leaves are the only implementation units. W0 makes completion decidable. W1 records the honest baseline. W2-W5 close semantics. W6 closes proof and performance. W7 closes the package and release.

| Leaf | Wave | Cluster | Deliverable | Owned paths | Gate ledger |
|---|---|---|---|---|---|
| A1.1 | W0 | A1 | re-pin typescript-primary(+tests) to 7.0.2 in vendor/sources.toml | `vendor/sources.toml` | `.outline/gates/A1.1.md` |
| A1.2 | W0 | A1 | `source fetch <name> --dest <dir>` command (digest-verified materialization into .cache/, gitignored) | `crates/bamts-verification/src/source_fetch.rs` | `.outline/gates/A1.2.md` |
| A1.3 | W0 | A1 | `catalog extract --catalog <id>` extractor command (typescript-runner first) | `crates/bamts-verification/src/catalog.rs` | `.outline/gates/A1.3.md` |
| A1.4 | W0 | A1 | manifest regeneration + typescript-7.0.2 cutover in ledger.rs consts | `crates/bamts-verification/src/ledger.rs; verification/manifest.lock.json` | `.outline/gates/A1.4.md` |
| A1.5 | W0 | A1 | classification/blocker framework generalization (verification/classification/*.toml loader + validation) | `crates/bamts-verification/src/classification.rs; verification/classification/*.toml` | `.outline/gates/A1.5.md` |
| A2.1 | W0 | A2 | lane core: lane.rs + shard.rs + evidence.rs + BAMTS_LANE_WORKER_REQUEST worker protocol | `crates/bamts-verification/src/lane.rs; crates/bamts-verification/src/shard.rs; crates/bamts-verification/src/evidence.rs` | `.outline/gates/A2.1.md` |
| A2.2 | W0 | A2 | oracle framework + oracles/tsc.rs (+ directive parser shared with B1.1) | `crates/bamts-verification/src/oracles/mod.rs; crates/bamts-verification/src/oracles/tsc.rs` | `.outline/gates/A2.2.md` |
| A2.3 | W0 | A2 | strict Test262 frontmatter, harness, phase, and async oracle | `crates/bamts-verification/src/oracles/test262.rs; crates/bamts-verification/Cargo.toml` | `.outline/gates/A2.3.md` |
| A2.6 | W0 | A2 | `ledger rebuild` (streaming writer) + `ledger verify --gate G7` completion gate | `crates/bamts-verification/src/rebuild.rs` | `.outline/gates/A2.6.md` |
| A2.7 | W0 | A2 | SHA-pinned pull-request, nightly, adaptive full-audit, and release verification workflows | `.github/workflows/ci.yml; .github/workflows/nightly.yml; .github/workflows/weekly-audit.yml; .github/workflows/release.yml` | `.outline/gates/A2.7.md` |
| A3.1 | W1 | A3 | first full measurement sweep across every scoped product catalog, with evidence committed and the ledger rebuilt | `verification/evidence/typescript-7.0.2/*.jsonl; proof/completeness-ledger.json` | `.outline/gates/A3.1.md` |
| B0.1 | W2 | B0 | AST/diagnostic change-window protocol (contract doc; syntax.rs/checker.rs edits batched per wave) | `docs/dev/ast_change_window_protocol.md` | `.outline/gates/B0.1.md` |
| B1.1 | W2 | B1 | tsc directive parser (// @flags, @filename virtual splits) feeding driver + lane | `crates/bamts-compiler/src/tsc_directives.rs` | `.outline/gates/B1.1.md` |
| B1.2 | W2 | B1 | grammar residual closure (lane-driven: import attributes, decorator forms, regexp-v syntax) | `crates/bamts-compiler/src/parser.rs` | `.outline/gates/B1.2.md` |
| B1.3 | W2 | B1 | parse diagnostic parity (TS1xxx mapping, spans) | `crates/bamts-compiler/src/diagnostics_parser.rs` | `.outline/gates/B1.3.md` |
| B1.4 | W2 | B1 | scanner edge parity (unicode/separators/bigint/rescans) | `crates/bamts-compiler/src/scanner.rs` | `.outline/gates/B1.4.md` |
| B2.1 | W2 | B2 | declaration merging + augmentation parity | `crates/bamts-compiler/src/binder/merging.rs` | `.outline/gates/B2.1.md` |
| B2.2 | W2 | B2 | export/symbol-flag parity (visibility, re-export chains) | `crates/bamts-compiler/src/binder/exports.rs` | `.outline/gates/B2.2.md` |
| B3.1 | W2 | B3 | generated diagnostic message catalog + ts_code layer | `crates/bamts-compiler/src/generated/diagnostic_messages.rs` | `.outline/gates/B3.1.md` |
| B3.2 | W2 | B3 | type relations completeness (assignability/variance/structural depth) | `crates/bamts-compiler/src/checker/relations.rs` | `.outline/gates/B3.2.md` |
| B3.3 | W2 | B3 | conditional + infer + template-literal + mapped types | `crates/bamts-compiler/src/checker/conditional_types.rs` | `.outline/gates/B3.3.md` |
| B3.4 | W2 | B3 | generic inference depth (priorities, contextual typing) | `crates/bamts-compiler/src/checker/inference.rs` | `.outline/gates/B3.4.md` |
| B3.5 | W3 | B3 | control-flow analysis + narrowing completeness | `crates/bamts-compiler/src/checker/narrowing.rs` | `.outline/gates/B3.5.md` |
| B3.6 | W3 | B3 | JSX checking parity | `crates/bamts-compiler/src/checker/jsx.rs` | `.outline/gates/B3.6.md` |
| B3.7 | W3 | B3 | overloads + signature resolution parity | `crates/bamts-compiler/src/checker/overloads.rs` | `.outline/gates/B3.7.md` |
| B3.8 | W3 | B3 | enum/namespace semantic parity (extends enum_plan.rs/namespace_plan.rs) | `crates/bamts-compiler/src/checker/enum_namespace.rs` | `.outline/gates/B3.8.md` |
| B3.9 | W3 | B3 | decorators semantics (stage-3 + legacy experimental) | `crates/bamts-compiler/src/checker/decorators.rs` | `.outline/gates/B3.9.md` |
| B4.1 | W3 | B4 | JS emit parity incl. target downlevels (async/generator/class-fields/destructuring transforms) | `crates/bamts-compiler/src/emitter/transforms.rs` | `.outline/gates/B4.1.md` |
| B4.2 | W3 | B4 | .d.ts emit parity | `crates/bamts-compiler/src/emitter/declarations.rs` | `.outline/gates/B4.2.md` |
| B4.3 | W3 | B4 | sourcemap parity | `crates/bamts-compiler/src/emitter/sourcemap.rs` | `.outline/gates/B4.3.md` |
| B4.4 | W3 | B4 | import helpers / tslib behavior parity | `crates/bamts-compiler/src/emitter/helpers.rs` | `.outline/gates/B4.4.md` |
| B4.5 | W3 | B4 | transpile-mode parity (transpileRunner 22 cases; single-file API) | `crates/bamts-compiler/src/emitter/transpile.rs` | `.outline/gates/B4.5.md` |
| B5.1 | W4 | B5 | module resolution modes (node16/nodenext/bundler, resolution-mode, package exports/imports) | `crates/bamts-compiler/src/project/resolution.rs` | `.outline/gates/B5.1.md` |
| B5.2 | W4 | B5 | tsconfig full option surface + extends/references parsing parity | `crates/bamts-compiler/src/project/tsconfig.rs` | `.outline/gates/B5.2.md` |
| B5.3 | W4 | B5 | project references + composite + incremental (.tsbuildinfo) | `crates/bamts-compiler/src/project/references.rs` | `.outline/gates/B5.3.md` |
| B5.4 | W4 | B5 | build mode (tsc -b) parity | `crates/bamts-compiler/src/project/build_mode.rs` | `.outline/gates/B5.4.md` |
| B6.1 | W4 | B6 | tsc argv surface + exit-code parity | `crates/bamts-cli/src/cli/tsc_args.rs` | `.outline/gates/B6.1.md` |
| B6.2 | W4 | B6 | diagnostic rendering parity (pretty false canonical text; json) | `crates/bamts-cli/src/cli/diagnostic_format.rs` | `.outline/gates/B6.2.md` |
| B7.1 | W4 | B7 | corpus expansion wave (add projects per failure clusters; corpus/manifest.toml + specs + projects) | `corpus/manifest.toml; corpus/cases/*.ts` | `.outline/gates/B7.1.md` |
| B7.2 | W4 | B7 | historical 6.0.2 and 5.9.3 catalog ownership and 7.0.2 applicability filter | `crates/bamts-verification/src/historical.rs` | `.outline/gates/B7.2.md` |
| C0.1 | W2 | C0 | $262 host + harness loader + async $DONE + agent/Atomics hooks (blocks every C leaf) | `crates/bamts-runtime/src/host_objects.rs; crates/bamts-verification/src/oracles/test262_harness.rs` | `.outline/gates/C0.1.md` |
| C1.1 | W2 | C1 | BigInt full family (value model, operations, literals, asIntN/asUintN, JSON interplay) | `crates/bamts-runtime/src/builtins/bigint.rs` | `.outline/gates/C1.1.md` |
| C1.2 | W2 | C1 | Number formatting/parsing exactness (toFixed/toPrecision/toExponential/radix) | `crates/bamts-runtime/src/builtins/number_format.rs` | `.outline/gates/C1.2.md` |
| C1.3 | W2 | C1 | Math edge exactness (hypot/cbrt/expm1/log1p/...) | `crates/bamts-runtime/src/builtins/math_edge.rs` | `.outline/gates/C1.3.md` |
| C2.1 | W2 | C2 | Proxy: all 13 traps + invariants + revocation | `crates/bamts-runtime/src/builtins/proxy.rs` | `.outline/gates/C2.1.md` |
| C2.2 | W2 | C2 | Reflect full surface | `crates/bamts-runtime/src/builtins/reflect.rs` | `.outline/gates/C2.2.md` |
| C2.3 | W2 | C2 | property descriptor algebra edge cases + prototype invariants | `crates/bamts-runtime/src/builtins/property_descriptor.rs` | `.outline/gates/C2.3.md` |
| C2.4 | W2 | C2 | Object statics gaps (getOwnPropertyDescriptors/Symbols, seal family, groupBy, fromEntries edge) | `crates/bamts-runtime/src/builtins/object_statics.rs` | `.outline/gates/C2.4.md` |
| C3.1 | W3 | C3 | Array ES2023+ (with/toSorted/toSpliced/toReversed, fromAsync) + iterator helpers | `crates/bamts-runtime/src/builtins/array_es2023.rs` | `.outline/gates/C3.1.md` |
| C3.2 | W3 | C3 | TypedArray full family (Int8/Uint8Clamped/Int16/Uint16/Int32/Uint32/Float32/Float64/BigInt64/BigUint64 + %TypedArray% shared methods) | `crates/bamts-runtime/src/builtins/typedarray_all.rs` | `.outline/gates/C3.2.md` |
| C3.3 | W3 | C3 | DataView full | `crates/bamts-runtime/src/builtins/dataview.rs` | `.outline/gates/C3.3.md` |
| C3.4 | W3 | C3 | ArrayBuffer resize/transfer/maxByteLength | `crates/bamts-runtime/src/builtins/arraybuffer.rs` | `.outline/gates/C3.4.md` |
| C3.5 | W3 | C3 | Atomics + SharedArrayBuffer (+ agent integration with C0.1) | `crates/bamts-runtime/src/builtins/atomics.rs` | `.outline/gates/C3.5.md` |
| C3.6 | W3 | C3 | Set methods (union/intersection/difference/...) | `crates/bamts-runtime/src/builtins/set_methods.rs` | `.outline/gates/C3.6.md` |
| C3.7 | W3 | C3 | Map/Set/WeakMap/WeakSet edge semantics | `crates/bamts-runtime/src/builtins/map_set_edge.rs` | `.outline/gates/C3.7.md` |
| C4.1 | W3 | C4 | String gaps (isWellFormed/toWellFormed, at, replaceAll edge, normalize forms) | `crates/bamts-runtime/src/builtins/string_edge.rs` | `.outline/gates/C4.1.md` |
| C4.2 | W3 | C4 | RegExp v-flag + unicode sets + duplicate named groups + lookbehind verification | `crates/bamts-runtime/src/builtins/regexp_v/` | `.outline/gates/C4.2.md` |
| C4.3 | W3 | C4 | URI encoding family edge cases | `crates/bamts-runtime/src/builtins/uri.rs` | `.outline/gates/C4.3.md` |
| C5.1 | W3 | C5 | generator + async function gap closure | `crates/bamts-runtime/src/vm/generator_async.rs` | `.outline/gates/C5.1.md` |
| C5.2 | W3 | C5 | async iterators/generators + for-await-of + TLA | `crates/bamts-runtime/src/vm/async_iterators.rs` | `.outline/gates/C5.2.md` |
| C5.3 | W3 | C5 | explicit resource management runtime (using/await using disposal, DisposableStack) | `crates/bamts-runtime/src/vm/explicit_resource.rs` | `.outline/gates/C5.3.md` |
| C5.4 | W3 | C5 | Error edge (cause chains, AggregateError, stack formatting contract) | `crates/bamts-runtime/src/builtins/error_edge.rs` | `.outline/gates/C5.4.md` |
| C6.1 | W4 | C6 | ESM evaluation semantics (cycles, live bindings, TLA) in vm/program | `crates/bamts-runtime/src/vm/esm_eval.rs` | `.outline/gates/C6.1.md` |
| C6.2 | W4 | C6 | import attributes + JSON modules | `crates/bamts-runtime/src/vm/import_attributes.rs` | `.outline/gates/C6.2.md` |
| C6.3 | W4 | C6 | dynamic import + host hook contract | `crates/bamts-runtime/src/vm/dynamic_import.rs` | `.outline/gates/C6.3.md` |
| C7.1 | W4 | C7 | WeakRef + FinalizationRegistry (GC hooks) | `crates/bamts-runtime/src/builtins/weakref_finalization.rs` | `.outline/gates/C7.1.md` |
| C7.2 | W4 | C7 | GC stress hardening (ephemeron edge, watermark tuning under lane) | `crates/bamts-runtime/src/gc/stress_hardening.rs` | `.outline/gates/C7.2.md` |
| C8.1 | W4 | C8 | JSON edge (source access? parse reviver done; stringify edge + modules interplay) | `crates/bamts-runtime/src/builtins/json_edge.rs` | `.outline/gates/C8.1.md` |
| C8.2 | W4 | C8 | Date full surface parity (parsing quirks, setters, two-digit years annexB overlap) | `crates/bamts-runtime/src/builtins/date_full.rs` | `.outline/gates/C8.2.md` |
| C8.3 | W4 | C8 | structuredClone/serialization edge | `crates/bamts-runtime/src/builtins/structured_clone.rs` | `.outline/gates/C8.3.md` |
| C9 | W4 | C9 | annexB (1,086 rows: legacy octals, HTML comments, __proto__, String HTML methods, Date extras) | `crates/bamts-runtime/src/builtins/annex_b.rs` | `.outline/gates/C9.md` |
| C10.1 | W5 | C10 | locale negotiation + canonicalization core | `crates/bamts-runtime/src/intl/locale_negotiation.rs` | `.outline/gates/C10.1.md` |
| C10.2 | W5 | C10 | Collator | `crates/bamts-runtime/src/intl/collator.rs` | `.outline/gates/C10.2.md` |
| C10.3 | W5 | C10 | NumberFormat (+ Number/Date toLocaleString integration) | `crates/bamts-runtime/src/intl/number_format.rs` | `.outline/gates/C10.3.md` |
| C10.4 | W5 | C10 | DateTimeFormat | `crates/bamts-runtime/src/intl/date_time_format.rs` | `.outline/gates/C10.4.md` |
| C10.5 | W5 | C10 | PluralRules/RelativeTimeFormat/ListFormat/Segmenter/DisplayNames | `crates/bamts-runtime/src/intl/plural_rules.rs` | `.outline/gates/C10.5.md` |
| C10.6 | W5 | C10 | getCanonicalLocales/supportedValuesOf + intl402 cross-cutting | `crates/bamts-runtime/src/intl/canonical_locales.rs` | `.outline/gates/C10.6.md` |
| C11.1 | W5 | C11 | Instant + PlainTime + Duration core arithmetic | `crates/bamts-runtime/src/temporal/instant_duration.rs` | `.outline/gates/C11.1.md` |
| C11.2 | W5 | C11 | PlainDate/PlainDateTime/PlainYearMonth/PlainMonthDay + ISO calendar | `crates/bamts-runtime/src/temporal/plain_types.rs` | `.outline/gates/C11.2.md` |
| C11.3 | W5 | C11 | ZonedDateTime + TimeZone protocol | `crates/bamts-runtime/src/temporal/zoned_date_time.rs` | `.outline/gates/C11.3.md` |
| C11.4 | W5 | C11 | Now + rounding/balancing + Intl interplay + toString/serialization | `crates/bamts-runtime/src/temporal/now_rounding.rs` | `.outline/gates/C11.4.md` |
| E1.1 | W2 | E1 | bytecode ISA gap closures (lane-driven opcode/operand additions) | `crates/bamts-bytecode/src/isa.rs` | `.outline/gates/E1.1.md` |
| E1.2 | W2 | E1 | bytecode verifier co-extension (definite-init/bounds per ISA change) | `crates/bamts-bytecode/src/verifier.rs` | `.outline/gates/E1.2.md` |
| E2.1 | W3 | E2 | JIT helper coverage completeness (46 helpers vs ISA) | `crates/bamts-codegen/src/jit/helpers.rs` | `.outline/gates/E2.1.md` |
| E2.2 | W3 | E2 | JIT tiering: OSR + deopt + warmup policy | `crates/bamts-codegen/src/jit/tiering.rs` | `.outline/gates/E2.2.md` |
| E2.3 | W3 | E2 | JIT-vs-interpreter differential stress (random program corpus) | `crates/bamts-codegen/tests/jit_differential.rs` | `.outline/gates/E2.3.md` |
| E2.4 | W3 | E2 | JIT execution and W^X proof on Apple Silicon | `crates/bamts-codegen/src/jit_memory.rs` | `.outline/gates/E2.4.md` |
| E3.1 | W4 | E3 | AOT object emission per target triple | `crates/bamts-codegen/src/aot/emission.rs` | `.outline/gates/E3.1.md` |
| E3.2 | W4 | E3 | AOT linking + cache correctness (existing fallback-cache lessons) | `crates/bamts-codegen/src/aot/linking.rs` | `.outline/gates/E3.2.md` |
| E3.3 | W4 | E3 | reproducible-build pipeline (deterministic objects) | `crates/bamts-codegen/src/aot/reproducible.rs` | `.outline/gates/E3.3.md` |
| E3.4 | W4 | E3 | native executable link and run on macOS hosts | `crates/bamts-cli/src/driver.rs` | `.outline/gates/E3.4.md` |
| E3.5 | W4 | E3 | native executable link and run on Windows MSVC | `crates/bamts-cli/src/windows_link.rs` | `.outline/gates/E3.5.md` |
| E3.6 | W4 | E3 | shared platform facts: host triple, machine facts, process regions, and peak memory on every execution host | `crates/bamts-platform/` | `.outline/gates/E3.6.md` |
| E3.7 | W4 | E3 | in-process AOT linking on every execution host | `crates/bamts-codegen/src/aot/in_process_link.rs` | `.outline/gates/E3.7.md` |
| E4.1 | W5 | E4 | target-cell evidence schema + verification/toolchains/<triple>.json generator | `crates/bamts-verification/src/toolchain_schema.rs` | `.outline/gates/E4.1.md` |
| E4.2 | W5 | E4 | x86_64-unknown-linux-gnu cell closure (native host) | `verification/toolchains/x86_64-unknown-linux-gnu.json` | `.outline/gates/E4.2.md` |
| E4.3 | W5 | E4 | aarch64 cell (cross + QEMU) | `verification/toolchains/aarch64-unknown-linux-gnu.json` | `.outline/gates/E4.3.md` |
| E4.4 | W5 | E4 | s390x cell (cross + QEMU) | `verification/toolchains/s390x-unknown-linux-gnu.json` | `.outline/gates/E4.4.md` |
| E4.5 | W5 | E4 | riscv64gc cell (cross + QEMU) | `verification/toolchains/riscv64gc-unknown-linux-gnu.json` | `.outline/gates/E4.5.md` |
| E4.6 | W5 | E4 | aarch64-apple-darwin cell (native host) | `verification/toolchains/aarch64-apple-darwin.json` | `.outline/gates/E4.6.md` |
| E4.7 | W5 | E4 | x86_64-apple-darwin cell (Rosetta) | `verification/toolchains/x86_64-apple-darwin.json` | `.outline/gates/E4.7.md` |
| E4.8 | W5 | E4 | x86_64-pc-windows-msvc cell (native host) | `verification/toolchains/x86_64-pc-windows-msvc.json` | `.outline/gates/E4.8.md` |
| E5.1 | W6 | E5 | bench/compiler-rules.toml schema + measure harness (conditions record: governor/affinity/swap; INVALID_CONDITIONS on mismatch; median-of-N) | `bench/compiler-rules.toml` | `.outline/gates/E5.1.md` |
| E5.2 | W6 | E5 | jit.compile-cost/payback/queue-tail-latency accepted measurements | `bench/jit_benchmarks.rs` | `.outline/gates/E5.2.md` |
| E5.3 | W6 | E5 | stage0.{correctness,integrity,no-rwx,event-completeness,aot-no-jit-allocator} evidence | `bench/stage0_evidence.rs` | `.outline/gates/E5.3.md` |
| E5.4 | W6 | E5 | stage1.pre-registered-regression guard wired to nightly | `bench/stage1_regression_guard.rs` | `.outline/gates/E5.4.md` |
| F1.1 | W6 | F1 | formal evidence -> ledger wiring (239 P0.7 rows flip via G1-G6 audit outputs) | `formal/ledger_wiring.rs` | `.outline/gates/F1.1.md` |
| F1.2 | W6 | F1 | formal model extension policy (catalog additions only via manifest regeneration + G4 authority) | `formal/extension_policy.md` | `.outline/gates/F1.2.md` |
| F2.1 | W7 | F2 | bamti package manifest, tsc executable, persistent API transport, and thirteen-subpath export map | `npm/bamti/package.json; npm/bamti/index.js; crates/bamts-cli/src/api_server/` | `.outline/gates/F2.1.md` |
| F2.2 | W7 | F2 | sync, async, filesystem, protocol, project, checker, snapshot, completion, and reference API behavior | `crates/bamts-compiler/src/service/; npm/bamti/unstable/sync.js; npm/bamti/unstable/async.js; npm/bamti/unstable/fs.js; npm/bamti/unstable/proto.js` | `.outline/gates/F2.2.md` |
| F2.3 | W7 | F2 | public AST, is, factory, utils, scanner, visitor, and clone export behavior | `crates/bamts-compiler/src/public_ast/; npm/bamti/unstable/ast/` | `.outline/gates/F2.3.md` |
| F2.4 | W7 | F2 | clean-install package contract across five artifact targets and all public entry points | `npm/test/bamti-api.test.mjs; npm/artifacts/` | `.outline/gates/F2.4.md` |
| F3.1 | W7 | F3 | completion runbook + docs + changelog | `docs/release/runbook.md` | `.outline/gates/F3.1.md` |
| F3.2 | W7 | F3 | final TypeScript-product release gate and tag evidence | `verification/release/typescript-7.0.2.json` | `.outline/gates/F3.2.md` |

## Integration nodes

| Cluster | Children | Gate ledger |
|---|---|---|
| A1 | A1.1, A1.2, A1.3, A1.4, A1.5 | `.outline/gates/cluster-A1.md` |
| A2 | A2.1, A2.2, A2.3, A2.6, A2.7 | `.outline/gates/cluster-A2.md` |
| A3 | A3.1 | `.outline/gates/cluster-A3.md` |
| B0 | B0.1 | `.outline/gates/cluster-B0.md` |
| B1 | B1.1, B1.2, B1.3, B1.4 | `.outline/gates/cluster-B1.md` |
| B2 | B2.1, B2.2 | `.outline/gates/cluster-B2.md` |
| B3 | B3.1, B3.2, B3.3, B3.4, B3.5, B3.6, B3.7, B3.8, B3.9 | `.outline/gates/cluster-B3.md` |
| B4 | B4.1, B4.2, B4.3, B4.4, B4.5 | `.outline/gates/cluster-B4.md` |
| B5 | B5.1, B5.2, B5.3, B5.4 | `.outline/gates/cluster-B5.md` |
| B6 | B6.1, B6.2 | `.outline/gates/cluster-B6.md` |
| B7 | B7.1, B7.2 | `.outline/gates/cluster-B7.md` |
| C0 | C0.1 | `.outline/gates/cluster-C0.md` |
| C1 | C1.1, C1.2, C1.3 | `.outline/gates/cluster-C1.md` |
| C2 | C2.1, C2.2, C2.3, C2.4 | `.outline/gates/cluster-C2.md` |
| C3 | C3.1, C3.2, C3.3, C3.4, C3.5, C3.6, C3.7 | `.outline/gates/cluster-C3.md` |
| C4 | C4.1, C4.2, C4.3 | `.outline/gates/cluster-C4.md` |
| C5 | C5.1, C5.2, C5.3, C5.4 | `.outline/gates/cluster-C5.md` |
| C6 | C6.1, C6.2, C6.3 | `.outline/gates/cluster-C6.md` |
| C7 | C7.1, C7.2 | `.outline/gates/cluster-C7.md` |
| C8 | C8.1, C8.2, C8.3 | `.outline/gates/cluster-C8.md` |
| C9 | C9 | `.outline/gates/cluster-C9.md` |
| C10 | C10.1, C10.2, C10.3, C10.4, C10.5, C10.6 | `.outline/gates/cluster-C10.md` |
| C11 | C11.1, C11.2, C11.3, C11.4 | `.outline/gates/cluster-C11.md` |
| E1 | E1.1, E1.2 | `.outline/gates/cluster-E1.md` |
| E2 | E2.1, E2.2, E2.3, E2.4 | `.outline/gates/cluster-E2.md` |
| E3 | E3.1, E3.2, E3.3, E3.4, E3.5, E3.6, E3.7 | `.outline/gates/cluster-E3.md` |
| E4 | E4.1, E4.2, E4.3, E4.4, E4.5, E4.6, E4.7, E4.8 | `.outline/gates/cluster-E4.md` |
| E5 | E5.1, E5.2, E5.3, E5.4 | `.outline/gates/cluster-E5.md` |
| F1 | F1.1, F1.2 | `.outline/gates/cluster-F1.md` |
| F2 | F2.1, F2.2, F2.3, F2.4 | `.outline/gates/cluster-F2.md` |
| F3 | F3.1, F3.2 | `.outline/gates/cluster-F3.md` |

| Node | Children | Gate ledger |
|---|---|---|
| Track A | A1, A2, A3 | `.outline/gates/track-A.md` |
| Track B | B0, B1, B2, B3, B4, B5, B6, B7 | `.outline/gates/track-B.md` |
| Track C | C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11 | `.outline/gates/track-C.md` |
| Track E | E1, E2, E3, E4, E5 | `.outline/gates/track-E.md` |
| Track F | F1, F2, F3 | `.outline/gates/track-F.md` |
| Compiler root | Track B | `.outline/gates/root-compiler.md` |
| Runtime root | Track C | `.outline/gates/root-runtime.md` |
| Native root | Track E and F1 | `.outline/gates/root-native.md` |
| Package root | F2 | `.outline/gates/root-package.md` |
| Product root | compiler, runtime, native, package | `.outline/gates/root-product.md` |

## Execution waves

- W0: A1 and A2. Freeze authority, logical catalogs, exact policy, receipts, oracles, rebuild, strict gates, and CI.
- W1: A3. Run the first full scoped baseline and replace guessed failure counts with evidence.
- W2: B0-B3.4, C0-C2, and E1. Close compiler and runtime foundations.
- W3: B3.5-B4, C3-C5, and E2. Close structured type, emit, collection, async, and JIT behavior.
- W4: B5-B7, C6-C9, and E3. Close projects, CLI, modules, weak/GC, core builtins, Annex B, and AOT reproducibility.
- W5: C10-C11 and E4. Close stable Intl, Temporal, and target cells.
- W6: E5 and F1. Close pre-registered performance and production-to-model correspondence.
- W7: F2-F3. Close the Node 24 package, public APIs, clean-install matrix, documentation, and release evidence.

Independent leaves with disjoint files may run in parallel. Leaves in a monolithic existing module run serially through the cluster integrator until the module split gives them disjoint ownership.

## Leaf execution

For each leaf:

1. Implement the complete owned behavior. Do not add placeholders, fallbacks, compatibility aliases, or unregistered exclusions.
2. Re-read the result against the pinned oracle and public contract. Replace recovery or error-type fallbacks that hide accepted behavior.
3. Hunt boundary, failure, concurrency, memory, and performance defects. Run the registered mutation proof.
4. Apply free polish. Then run the leaf ledger. The parent reruns its status and one decisive CHECK.
5. The cluster integrator applies shared registry edits, merges receipts, rebuilds generated projections, and runs the cluster ledger.

A passing check is settled until code, evidence, authority, or the relevant generated artifact changes.

## Risks that remain blocking

- Path-only catalogs can hide missing configurations and observables. Logical cells prevent this.
- Recovery diagnostics can make coarse case comparisons look stable. Each applicable stage and observable needs evidence.
- Public API methods make blanket language-service exclusions false. Reachable behavior remains blocking.
- Candidate, oracle, harness, or catalog drift can make old PASS receipts lie. Every receipt binds all four.
- Parallel workers can overwrite monolithic ledgers or compiler files. Only the integration owner writes shared files.
- Formal proofs can drift from production. Release evidence binds production opcode and transition manifests to model identifiers and includes a production mutation.
- Performance JSON can certify itself. Root checks recompute scorecards from raw condition-bound samples.
- Stable Intl and Temporal are long poles. They are normal blocking leaves, not later phases or exclusions.

## Verification contract

Leaf ledgers contain the exact checks. Integration requires:

- current leaf, cluster, track, wave, and root ledgers with no pending evidence;
- G0 integrity and strict scoped completion roots;
- unpiped workspace format, Clippy `-D warnings`, and tests;
- Interpreter/JIT/AOT corpus differential;
- formal G1, G2, G5, G3, G4, and G6 in order;
- 49 target obligations and 9 pre-registered benchmark rules;
- clean Node 24 package install and import of all thirteen export subpaths across five artifacts;
- byte-identical catalog, evidence merge, ledger, proof, package, and release regeneration.

## Definition of done

`.outline/GATES.md` is the root acceptance contract. Completion requires every box and every child ledger to contain actual evidence, every scoped logical obligation to be receipt-backed PASS or an exact machine-evidenced policy exclusion, all four product roots green, the repository release gate green once on the completed tree, and regeneration byte-identical. Any abandoned gate is visible in this plan status log and the final report; there is no silent scope reduction.

## Status log

Append-only.

- 2026-08-25 CONTRACT_WRITTEN: stable 7.0.2 TypeScript-product scope, interfaces, evidence, ownership, depth tree, waves, and unlazy gates fixed before production edits.
- 2026-08-25 LEAF_STARTED A1.1-A1.5: authority, source materialization, logical catalog, manifest cutover, and exact-classification vertical slice dispatched under one integration owner.
- 2026-08-25 LEAF_STARTED A2.1: closed shard, lane, receipt, bounded-memory merge, and atomic-publication core dispatched with disjoint ownership.
- 2026-11-01 CONTRACT_AMENDED: execution hosts widened to the five artifact targets, with `aarch64-apple-darwin` as the primary evidence host through the repository `Justfile` and hosted workflows kept beside it. Nine leaves added (B7.2, E2.4, E3.4 to E3.7, E4.6 to E4.8), taking the frozen authority from 105 to 114 leaves and the target obligations from 28 to 49 (seven cells of seven obligations).
