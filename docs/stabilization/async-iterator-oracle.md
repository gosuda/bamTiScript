# Async iterator payload contract

The pinned TypeScript 7.0.2 compiler preserves a promise-valued payload from a
structural async iterator. It awaits that payload when the returned iterator
retains the builtin `AsyncIterator` identity. Awaiting every `for await` value
therefore disagrees with the pinned compiler.

The [verification guide](../explanation/verification.md) explains how these
checks relate to the separate product completion gates.

## Reference executable

Observed on 2026-11-23:

- `node --version`: `v24.18.0`.
- `node node_modules/typescript/bin/tsc --version`: `Version 7.0.2`.
- Native executable: `node_modules/@typescript/typescript-linux-x64/lib/tsc`.
- Native executable SHA-256:
  `4f2de678286401759b3fb4475bafe35b8f32b4b3a07d92642bbf37eadc9b34a4`.
- Both installed package manifests identify version `7.0.2` and published
  `gitHead` `2bd066d87f5bafd315be9f40889d0a60b9e58e0b`.

The observations use executable diagnostics, package metadata, and public
declarations. No reference implementation was inspected or copied.

## Reproduce the distinction

Compile each fixture separately with:

```sh
node node_modules/typescript/bin/tsc --strict --noEmit --target ESNext --module NodeNext --lib ESNext --pretty false <fixture.ts>
```

`async-promise.ts`:

```ts
declare const values: AsyncIterable<Promise<number>>;

async function consume(): Promise<void> {
    for await (const value of values) {
        const numeric: number = value;
        const promised: Promise<number> = value;
        const wrong: string = value;
    }
}
```

Observed diagnostics:

```text
async-promise.ts(6,15): error TS2322: Type 'number' is not assignable to type 'Promise<number>'.
async-promise.ts(7,15): error TS2322: Type 'number' is not assignable to type 'string'.
```

`record-async-promise.ts`:

```ts
class IteratorKeys { static next = 0; }
class ResultKeys { static value = 0; }
declare const values: {
    [Symbol.asyncIterator](): Record<keyof typeof IteratorKeys,
        () => Promise<Record<keyof typeof ResultKeys, Promise<number>>>>;
};
async function consume(): Promise<void> {
    for await (const value of values) {
        const numeric: number = value;
        const promised: Promise<number> = value;
        const wrong: string = value;
    }
}
```

Observed diagnostics:

```text
record-async-promise.ts(9,15): error TS2322: Type 'Promise<number>' is not assignable to type 'number'.
record-async-promise.ts(11,15): error TS2322: Type 'Promise<number>' is not assignable to type 'string'.
```

Both commands exit 1 because their incompatible assignments are deliberate
negative controls. The accepted assignments distinguish the two inferred types;
the additional string assignments exclude permissive recovery types.

## Boundary controls

These controls were compiled with the same executable and options:

| Returned iterator or iteration source | Loop value type |
| --- | --- |
| `AsyncIterable<number>` | `number` |
| `Iterable<Promise<number>>` consumed by `for await` | `number` |
| Custom synchronous iterator yielding `Promise<number>` | `number` |
| Custom async method returning `AsyncIterator<Promise<number>>` | `number` |
| Custom async method returning `AsyncIterableIterator<Promise<number>>` | `number` |
| Custom async method returning `AsyncGenerator<Promise<number>>` | `number` |
| Alias of that returned builtin iterator | `number` |
| Interface extending that returned builtin iterator | `Promise<number>` |
| Returned builtin iterator intersected with `{ tag: true }` | `Promise<number>` |
| Returned builtin iterator intersected with `object` | `Promise<number>` |
| Returned builtin iterator intersected with `{}` or `unknown` | `number` |
| Aliased or nested empty/unknown factors around the returned builtin iterator | `number` |
| Duplicate intersection of the same returned builtin iterator | `number` |
| Custom `next(): Promise<IteratorResult<Promise<number>, void>>` | `Promise<number>` |

The interface and intersection distinctions concern the object returned by
`[Symbol.asyncIterator]()`. An outer `Stream<T> extends AsyncIterable<T>` still
returns the builtin iterator and retains its payload adaptation.

An async generator delegating with `yield*` to the structural promise-valued
iterator was also accepted with return annotation
`AsyncGenerator<number, void, undefined>`. Direct `await iterator.next()` reads
retain the declared `Promise<number>` payload; adapting iteration must not alter
the `next()` return type.

## Regression evidence and implementation invariant

The exact source snippets in
[`retained_record_iterators.rs`](../../crates/bamts-compiler/tests/retained_record_iterators.rs)
were compiled independently by the reference executable. The following eight
fixtures produced only the expected TS2322 diagnostics:

| Fixture | Expected and observed TS2322 count |
| --- | ---: |
| Retained Record structural async payload | 1 |
| Mixed async and synchronous union | 1 |
| Async protocol selected from an intersection | 1 |
| Builtin alias/generic propagation and direct `next()` control | 3 |
| Derived and intersected iterator compositions | 2 |
| Async generator delegation | 1 |
| Array and structural synchronous fallback | 2 |
| Imported builtin and structural aliases | 2 |

The neutral-intersection regression adds eight independently compiled cases:
empty object, unknown, duplicate builtin, aliased empty object, aliased unknown,
nested neutral factors, primitive object, and a tagged object. Each produces
exactly one expected TS2322 negative control. The first six retain the builtin
`number` result; the last two retain the structural `Promise<number>` result.

All supported builtin iterator return forms were checked together:
`AsyncIterator`, `AsyncIterableIterator`, and `AsyncGenerator`, each instantiated
with `<Promise<number>, void, undefined>`. Each source produces exactly two
TS2322 controls: assigning the loop's `number` to `Promise<number>`, and assigning
the direct `await next()` result's `Promise<number>` payload to `number` after a
`done === false` guard. The `AsyncIterable` source case is covered separately
above; it supplies an iterator method rather than a `next()` method.

Builtin iterator provenance participates in interned object identity, survives
import and generic substitution, and is absent from fresh structural copies.
Alias reduction preserves it. Genuine interface and intersection composition
uses the declared structural payload. Each union branch selects and adapts its
own protocol. Synchronous fallback awaits its payload, and async `yield*` awaits
the delegated payload separately.

Neutral intersection reduction is confined to iterator identity. It follows
aliases and type queries with a bounded active path, removes only unknown and
wholly empty object factors, and requires one distinct builtin iterator identity.
It does not change global intersection normalization or erase named interfaces.

These reference observations establish the expected compiler contract. They do
not establish a bamTiScript test pass, JavaScript runtime behavior, or a product
completion gate.
