# Indexed-access oracle evidence

The pinned TypeScript 7.0.2 executable accepts the broad numeric tuple key below and rejects the empty-tuple control. This observation resolves the review finding that the broad numeric case should require an intersection of tuple element types.

## Executable identity

- Packages: `typescript@7.0.2` and `@typescript/typescript-linux-x64@7.0.2`.
- `tsc --version`: `Version 7.0.2`.
- Package `gitHead`: `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`.
- Native executable: `node_modules/@typescript/typescript-linux-x64/lib/tsc`.
- Executable SHA-256: `4f2de678286401759b3fb4475bafe35b8f32b4b3a07d92642bbf37eadc9b34a4`.

## Fixture and command

Save this exact source as `tuple-number-index-oracle.ts` in the directory containing the pinned packages:

```typescript
type Pair = [number, string];
function broad<K extends number>(): Pair[K] { return 1; }
type Empty = [];
function empty<K extends number>(): Empty[K] { return 1; }
```

```sh
node node_modules/typescript/bin/tsc --ignoreConfig --strict --noEmit \
  --target ESNext --module NodeNext --lib ESNext --pretty false \
  tuple-number-index-oracle.ts
```

The sole diagnostic is:

```text
tuple-number-index-oracle.ts(4,48): error TS2322: Type 'number' is not assignable to type '[][K]'.
  Type '1' is not assignable to type 'never'.
```

`broad` produces no diagnostic. The regression `numeric_tuple_keys_keep_the_pinned_broad_index_behavior` in [key_reductions.rs](../../crates/bamts-compiler/tests/key_reductions.rs) preserves that accepted behavior and the empty-tuple rejection, with a separate literal-key-union rejection control.

This is executable evidence for these cases. Product completion requires the gates described in [Verification](../explanation/verification.md).
