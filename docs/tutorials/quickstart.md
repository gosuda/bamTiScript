# Quickstart: build and use `bamts`

This tutorial builds the pre-release CLI from source, type-checks a TypeScript file, emits a native host executable, and runs that executable.

## 1. Install prerequisites

You need:

* Rust 1.97.1 or later
* Cargo
* A Linux x64 host matching the current native output target

## 2. Build the CLI

From the repository root:

```bash
cargo build --release -p bamts-cli
```

The executable is written to `target/release/bamts`.

## 3. Create a TypeScript file

Create `hello.ts`:

```ts
const message: string = "hello from bamts";
process.stdout.write(`${message}\n`);
```

## 4. Type-check without emitting files

```bash
target/release/bamts --noEmit --pretty false hello.ts
```

A successful invocation exits with status 0. Type errors are reported as diagnostics and produce a nonzero status.

## 5. Emit a native executable

```bash
target/release/bamts hello.ts --outDir out
```

Run the emitted host binary:

```bash
./out/hello
```

Expected output:

```text
hello from bamts
```

## 6. Explore compiler options

```bash
target/release/bamts --help
target/release/bamts --help --all
```

The CLI follows the TypeScript 7.0.2 `tsc` argument model. It supports direct source-file compilation, `tsconfig.json` discovery, `--project`, `--build`, and response files. Use `bamts --run --jit hello.ts` or `bamts --run --aot hello.ts` to compile and execute a program directly. The bare `check`, `run`, `compile`, and `explain` subcommand forms do not select this public interface. See the [CLI reference](../reference/cli.md) for the native execution options.

## Resource limits

The frontend enforces two source-input budgets:

* One source file can contain at most **16 MiB** (16,777,216 bytes).
* One compilation session can load at most **256 MiB** (268,435,456 bytes) across all source files.

Exceeding a budget produces a diagnostic and stops compilation before later frontend stages.

## Next steps

* [CLI reference](../reference/cli.md)
* [Diagnostics reference](../reference/diagnostics.md)
* [Architecture](../explanation/architecture.md)
* [Verification](../explanation/verification.md)
