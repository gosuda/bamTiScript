# Command line interface (CLI) reference

`bamts` is the TypeScript 7.0.2-compatible command-line interface. It accepts `tsc` option names and short names, response files, project configuration, and build mode.

## Help and version

```bash
bamts --help
bamts --help --all
bamts --version
```

The concise help identifies the program as `tsc: The TypeScript Compiler - Version 7.0.2`. `bamts`, `bamti`, `tsc`, and executable paths ending in those names are accepted as the program token.

## Common commands

```bash
# Compile the project selected by tsconfig.json in the working directory
bamts

# Compile explicit source files with command-line options
bamts --ignoreConfig app.ts util.ts

# Type-check without writing output files
bamts --noEmit

# Compile the project selected by a configuration path
bamts --project ./path/to/tsconfig.json

# Build a composite project and its references
bamts --build

# Create a recommended tsconfig.json
bamts --init
```

With no explicit source files, `bamts` discovers `tsconfig.json` in the working directory. Use `--project` (`-p`) for a specific configuration or `--build` (`-b`) for composite projects.

When direct source files run in a directory that contains `tsconfig.json`, the CLI returns `TS5112`. Add `--ignoreConfig` to compile those files with command-line options instead.

`bamts --init` writes the TypeScript 7.0.2 recommended configuration when `tsconfig.json` is absent. If it already exists, the command returns `TS5054` and leaves it unchanged. Initialization ignores source, project, pretty, and target options.

## Output options

The parser accepts TypeScript output option names including `--outDir`, `--outFile`, `--declaration` (`-d`), `--declarationMap`, `--sourceMap`, and `--noEmit`.

With emission enabled, compiling one source file without `--declaration`, `--sourceMap`, or `--outFile` writes a native host executable. With `--outDir <dir>`, it writes `<dir>/<entrypoint-name>`; otherwise it writes beside the source file. `--declaration` or `--sourceMap` selects JavaScript artifact emission instead. Multiple explicit source files also use the JavaScript artifact pipeline.

```bash
bamts --ignoreConfig app.ts --outDir out                    # native executable
bamts --ignoreConfig app.ts --declaration --outDir out      # .js and .d.ts
bamts --ignoreConfig app.ts --sourceMap --outDir out        # .js and .js.map
bamts --ignoreConfig app.ts util.ts --outDir out            # per-file JavaScript
```

Project mode writes JavaScript and declaration outputs from the corresponding `tsconfig.json` options.

`--outFile` is parsed so the compilation can report the TypeScript 7.0.2 removal diagnostic `TS5102`; it does not select a bundled native executable.

## Option classification by mode

Before compilation, accepted compiler options are classified by dispatch mode. A recognized option outside that mode's consumed-option table fails with `error TS5047: Compiler option '--<name>' has no canonical native driver mapping.` on stderr and exit status 5.

* Direct and project modes classify emit, checking, and module-resolution options through the consumed-option tables in [`tsc_args.rs`](../../crates/bamts-cli/src/cli/tsc_args.rs). These include `--declaration`, `--sourceMap`, `--target`, `--module`, `--moduleResolution`, and `--strict`. The JavaScript artifact pipeline applies them as project configuration overrides. `--ignoreConfig` is direct-only and rejected in project mode; `--listFiles` and `--listFilesOnly` are project-only.
* Build mode consumes `--build`, `--verbose`, `--dry`, `--force`, `--clean`, `--stopBuildOnErrors`, `--pretty`, `--help`, and `--version`. `--verbose` prints a `Building project '<config>'...` or `Project '<config>' is up to date` line per project. Compiler-only options can fail during argument parsing; accepted options without a build mapping, such as `--noEmit`, fail with `TS5047`.

The obsolete `--out` spelling is an unknown compiler option and returns `TS5023`.

## Parsing behavior

The parser accepts supported TypeScript 7.0.2 compiler option names and rejects unknown options instead of silently discarding them. Boolean options accept an omitted value, `true`, `false`, or `null`; on the command line, `null` leaves the flag unset. Response files use the `@path` form.

`--target es3` returns `TS5108` because that target was removed. `--target es5` parses successfully. In the TypeScript-compatible interface, `--target` names an ECMAScript target, such as `es2022`; project and JavaScript artifact compilation apply it as a compiler-option override.

The bare `check`, `run`, `compile`, and `explain` subcommand forms do not select the public TypeScript-compatible interface. Use `--run` to execute a program.

## Native execution

`--run` (`-r`) selects the native execution interface. Its default execution target is AOT; `--jit`, `--aot`, or `--target <aot|jit>` selects the target explicitly.

```bash
bamts --run --jit app.ts
bamts --run --aot app.ts -- first-argument second-argument
bamts --run --target jit app.ts
bamts --run --help
```

This interface has its own option names, shown by `--run --help`. Arguments after `--` are passed to the program. AOT execution requires the platform linker described in the [source-build quickstart](../tutorials/quickstart.md).

## Exit codes

The TypeScript-compatible interface uses status classes 0 through 4 and reserves 5 for native compilation constraints.

| Status | Meaning |
|---:|---|
| 0 | Success |
| 1 | Diagnostics were generated and output was skipped |
| 2 | Diagnostics were generated and output was emitted |
| 3 | Invalid project output prevented emission |
| 4 | A project-reference cycle prevented emission |
| 5 | The requested behavior has no canonical native mapping |

TypeScript-format parse, project, and compiler diagnostics are written to stdout. Argument and configuration failures use the same status model.

The native execution interface reports usage errors with status 2 and driver failures with status 1, writing those diagnostics to stderr. Successful execution returns the program's exit status.

## Resource budgets

The compiler frontend enforces source-input budgets:

* `BAMTS-R001` (`source-too-large`): one source file can contain at most **16 MiB** (16,777,216 bytes).
* `BAMTS-R002` (`source-budget-exceeded`): one session can load at most **256 MiB** (268,435,456 bytes) across all source files.

## Related documentation

* [Diagnostics reference](./diagnostics.md)
* [Source-build quickstart](../tutorials/quickstart.md)
