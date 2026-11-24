# Numeric update and escaped-name oracle

This note records four executable observations from the repository's pinned TypeScript 7.0.2 compiler. The cases ran before the workspace executor became unavailable. The sources and diagnostics below were copied from those observed results.

## Compiler and command

- Compiler: TypeScript 7.0.2.
- Native executable: `node_modules/@typescript/typescript-linux-x64/lib/tsc`.
- Native executable SHA-256: `4f2de678286401759b3fb4475bafe35b8f32b4b3a07d92642bbf37eadc9b34a4`.
- Arguments: `--strict --noEmit --target ESNext --module NodeNext --lib ESNext --pretty false`, followed by the fixture path.

The executable identity is the same pinned authority used in the [indexed-access oracle](indexed-access-oracle.md). No reference implementation source was inspected.

## Observed cases

| Case | Result | Consequence |
| --- | --- | --- |
| Branded number | One TS2322 for assignment to bigint | Updates retain the branded binding and produce a number expression |
| Branded bigint | One TS2322 for assignment to number | Updates retain the branded binding and produce a bigint expression |
| Branded numeric literal | No diagnostics | The branded binding retains its literal identity; the update expression is number |
| Escaped receiver | Two TS2322 diagnostics for later literal assignments | Both escaped and plain reads see the widened bigint value after the update |

### branded-number

```ts
type Brand = number & { readonly brand: 'n' };
declare let root: Brand | undefined;
if(root!==undefined){const post=root++;const prefix=--root;const after=root;const accepted:number=after;const branded:Brand=after;const wrong:bigint=after;const result:number=post;}
```

Observed diagnostics:

```text
number.ts(3,137): error TS2322: Type 'Brand' is not assignable to type 'bigint'.
```

### branded-bigint

```ts
type Brand = bigint & { readonly brand: 'b' };
declare let root: Brand | undefined;
if(root!==undefined){const post=root++;const prefix=--root;const after=root;const accepted:bigint=after;const branded:Brand=after;const wrong:number=after;const result:bigint=post;}
```

Observed diagnostics:

```text
bigint.ts(3,137): error TS2322: Type 'Brand' is not assignable to type 'number'.
```

### branded-number-literal

```ts
type Brand = 1 & { readonly brand: 'n' };
declare let root: Brand | undefined;
if(root!==undefined){const post=root++;const after=root;const literal:1=after;const result:number=post;}
```

Observed diagnostics:

```text
(none)
```

### escaped-receiver

```ts
declare const obj: { inner: { value: 1n } };
const post = obj.\u0069nner.value++;
const escapedAfter = obj.\u0069nner.value;
const plainAfter = obj.inner.value;
const rejectedEscaped: 1n = escapedAfter;
const rejectedPlain: 1n = plainAfter;
const accepted: bigint = escapedAfter;
```

Observed diagnostics:

```text
escaped.ts(5,7): error TS2322: Type 'bigint' is not assignable to type '1n'.
escaped.ts(6,7): error TS2322: Type 'bigint' is not assignable to type '1n'.
```

## Verification boundary

These observations settle the four listed reference cases. The expanded Rust regressions also cover optional properties, prefix and postfix operations, nullable intersection factors, unrelated nonnumeric intersections, root identifier escapes, and guard invalidation. Those expanded tests had not executed when this note was prepared; their execution is a hosted CI gate.

The escaped-name correction uses the existing identifier decoder for property flow keys. It does not change source ranges or UTF-16 positions. The numeric correction preserves the existing generic update-expression category while keeping numeric validity, explicit nullability, and dynamic-any absorption separate.

Evidence claims follow the [verification guide](../explanation/verification.md).
