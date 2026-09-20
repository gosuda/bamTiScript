# CLI execution and chaos tests

Use the repository-pinned Node 24.18.0 on `PATH`, then install the locked TypeScript 7.0.2 oracle from the repository root:

```sh
npm ci
cargo test --locked -p bamts-cli
```

Run the bounded chaos suite alone:

```sh
cargo test --locked -p bamts-cli --test cli chaos::
```

The oracle helpers verify both versions, even when a single differential test is selected. They compile the original `.ts` files with `tsc --strict`, execute the emitted JavaScript in Node, and compare it with the original TypeScript executed through real `bamts --api` processes in JIT and AOT modes. Compiler internals and transport dispatch are not mocked.

## Coverage

`runtime-workload.ts` exercises typed record processing, loop closure capture, destructuring defaults, Map iteration, generators, labeled control flow with `finally`, and asynchronous completion. `optional-chain-continuations.ts` covers skipped computed keys and arguments, optional-call continuations, non-null assertions, grouped method receivers, and deletion.

The generated-program test uses eight fixed seeds and sixteen bounded functions per seed. Each function executes arithmetic through `continue` and `finally`. Expected results are calculated independently in Rust and checked against Node before comparison with JIT and AOT. Failures print the seed and complete generated source. No source depends on wall time or host randomness.

The transport test interleaves 96 malformed JSON/request frames with valid version requests across eight sessions. Seeded fragments split headers and bodies into 1–17-byte writes. Every malformed frame must produce the expected typed error, and every subsequent request must receive its own response in order.

Additional tests cover exact header limits, unterminated headers with the peer still connected, duplicate lengths, truncated frames, LSP edit recovery, 512 KiB TypeScript output, and simultaneous 256 KiB stdout/stderr capture. The process harness drains both pipes while the child runs, retains a 120-second child deadline, and kills/reaps a timed-out child. The capture regression has a five-second deadline; the watchdog regression uses 200 milliseconds.

## Limits

These tests provide bounded regression evidence, not exhaustive fuzzing, formal gate admission, full TypeScript compatibility, or performance benchmark evidence. Socket-specific process tests are Unix-only. The deterministic framing unit tests remain portable. The watchdog controls the direct child, not arbitrary descendant process trees.

The checker still diagnoses some valid optional-chain indexed accesses with `BAMTS-C064`; the optional-chain fixture separately establishes corrected execution semantics. No reference implementation source is copied into these fixtures.
