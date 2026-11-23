# Diagnostics reference

The bamTiScript compiler emits diagnostics during lexical analysis, parsing, semantic analysis, type checking, and resource checking.

## Diagnostic code families

Diagnostic codes use the form `BAMTS-<FAMILY><NUMBER>`:

| Family | Name | Scope and description |
|---|---|---|
| `BAMTS-L` | Lexer | Scans source text into tokens and reports malformed lexical input. |
| `BAMTS-P` | Parser | Builds the abstract syntax tree and reports grammar errors. |
| `BAMTS-C` | Checker | Binds symbols, evaluates types, and reports semantic errors. |
| `BAMTS-W` | Warning | Reports configurable lint rules. |
| `BAMTS-R` | Resource | Enforces source-input budgets. |

For the lint rules in the `BAMTS-W` family, see [`crates/bamts-compiler/RULES.md`](../../crates/bamts-compiler/RULES.md).

## Public CLI presentation

The public CLI follows the TypeScript 7.0.2 diagnostic presentation model:

```bash
bamts --noEmit --pretty false example.ts
bamts --noEmit --pretty example.ts
```

`--pretty false` produces stable one-line TypeScript diagnostics. `--pretty` enables color and context intended for an interactive terminal. The native execution interface selected by `--run` accepts `--diagnostics-format`, `--format`, and `--error-limit`; the TypeScript-compatible interface does not accept those option names.

## Coordinate system and UTF-16 positioning

Diagnostic line and column coordinates are 1-based. Columns and source offsets count UTF-16 code units.

* Line numbers start at line 1.
* Diagnostic line and column coordinates are 1-based.
* Source offsets count UTF-16 code units.

For the string representation and coordinate mapping, see [`docs/solutions/architecture-patterns/exact-ecmascript-utf16-strings.md`](../solutions/architecture-patterns/exact-ecmascript-utf16-strings.md).

## TypeScript diagnostic mapping

[`verification/diagnostic-code-map.json`](../../verification/diagnostic-code-map.json) records a mapping only when the repository has TypeScript evidence for an equivalent rule. Unmapped bamTiScript diagnostics remain explicit. Each mapping record contains the bamTiScript code, TypeScript code, test snippet, and observed `tsc` output.

## Example

Given `example.ts`:

```typescript
const value: number = "not a number";
```

Run:

```bash
bamts --noEmit --pretty false example.ts
```

The CLI reports a TypeScript-style diagnostic with the source location, category, code, and message.

## Related documentation

* [CLI reference](./cli.md)
