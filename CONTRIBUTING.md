# Contributing to bamTiScript

This guide describes how to set up your environment, navigate the repository, validate changes locally, and submit contributions to bamTiScript.

## Project status

bamTiScript is in pre-release state (`0.2.0`).

- `bamti` and `bamti-cli` 0.1.0 are published, but their referenced platform binary packages are unavailable.
- TypeScript 7.0.2 serves as the primary compatibility oracle, not a completed compatibility claim.
- No repository-local GitHub Actions workflow is present. Run the verification gates locally before committing or pushing.

---

## Prerequisites and Rust setup

### Pinned toolchain

bamTiScript requires the toolchain pinned in `rust-toolchain.toml` and declared in `Cargo.toml`:

- Rust version: `1.97.1`
- Edition: `2024`
- Components: `rustfmt`, `clippy`, `rust-src`
- Profile: `minimal`

Ensure your local toolchain matches `rust-toolchain.toml` before building.

### Safety policy

The workspace root `Cargo.toml` enforces a strict lint policy:

```toml
[workspace.lints.rust]
unsafe_code = "forbid"
```

The root policy defaults to `unsafe_code = "forbid"`. Most crates inherit it. `bamts-codegen`, `bamts-napi`, `bamts-node`, `bamts-platform`, and `bamts-verification` use `deny` with narrowly scoped exceptions. `bamts-native` contains documented unsafe FFI and native-bridge code. This policy and encapsulation are not an end-to-end memory-safety proof.

### Host C toolchain

AOT steps require a working C compiler driver selected by `$CC`, defaulting to `cc`. For example, use `CC=gcc` or `CC=clang` when that compiler is not installed as `cc`. AOT targets the host architecture and does not cross-compile.

---

## Repository architecture and components

The project is structured as a Cargo workspace under `crates/`. Architectural concepts and rules are documented in:

- [`docs/explanation/architecture.md`](docs/explanation/architecture.md) — System architecture, pipeline design, and runtime execution model.
- [`crates/bamts-compiler/RULES.md`](crates/bamts-compiler/RULES.md) — Diagnostic lint and strictness rules catalog.
- [`docs/solutions/architecture-patterns/exact-ecmascript-utf16-strings.md`](docs/solutions/architecture-patterns/exact-ecmascript-utf16-strings.md) — Exact UTF-16 code-unit string representation (`EcmaString`).

### Workspace crates

- `crates/bamts-compiler`: Scanner, lexer, AST definitions, parser, binder, type checker, and strictness rules engine.
- `crates/bamts-bytecode`: Bytecode instruction set, program structures, and string storage model.
- `crates/bamts-runtime`: Memory layout, garbage collector, JS VM interpreter, and standard builtins (`Object`, `Array`, `Promise`, `Uint8Array`, `JSON`, `Date`, etc.).
- `crates/bamts-codegen`: Execution backends including JIT compiler and host C AOT emission.
- `crates/bamts-cli`: Main executable binary (`bamts`), command line argument parsing, and diagnostic formatters.
- `crates/bamts-native`: Host interop bridge and C runtime linkage.
- `crates/bamts-node`: Subset implementation of Node.js host APIs (e.g. `process.stdout.write`, timers).
- `crates/bamts-verification`: Conformance test runner, differential testing harnesses, and formal gates.
- `crates/bamts`: Root workspace library facade.

---

## Development and validation workflow

### Narrow-first validation

During active development, run focused checks against the specific crate or subsystem you are modifying to maintain fast feedback loops.

Examples of narrow validation commands:

```bash
# Check compiler crate only
cargo check -p bamts-compiler

# Run targeted unit tests matching a filter
cargo test -p bamts-compiler --lib filter_name

# Check CLI binary package
cargo check -p bamts-cli

# Build release CLI binary
cargo build --release -p bamts-cli
```

### Conventions for tests and examples

- Use `process.stdout.write` for program output in TypeScript examples and fixtures. Do not use `console.log`, `console.debug`, `console.trace`, `console.table`, or `debugger` statements.
- Single entrypoint source files are supported for compilation. Generation of declaration files (`.d.ts`) and source maps is rejected in version `0.2.0`.

---

## Mandatory unpiped verification gates

All changes must pass the full workspace verification suite before publication or merging.

### Gate sequence

Run the following commands in sequence from the workspace root:

```bash
cargo fmt --all --check
cargo check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

### Execution rules

Commands MUST run without pipes. Do not pipe a gate into `tail`, `head`, `grep`,
or a log command. A pipeline can hide the Cargo command's exit status.

---

## Commit and documentation discipline

### Commit discipline

- One mechanism per commit: Each commit contains one logical change. Do not combine unrelated fixes or cleanups.
- Every commit builds: Each commit must compile and pass its applicable checks so `git bisect` remains useful.

### Documentation discipline

- Separate current behavior from targets.
- Link claims about evidence to [`docs/explanation/verification.md`](docs/explanation/verification.md).
