---
title: Preserve ECMAScript strings as exact UTF-16 code units
date: 2026-07-31
category: architecture-patterns
module: compiler and runtime
problem_type: architecture_pattern
component: string-representation
severity: high
applies_when:
  - A Rust compiler or runtime must preserve ECMAScript string semantics across parsing, bytecode, interpretation, JIT, AOT, and host I/O
tags: [utf-16, ecmascript, strings, bytecode, regexp, boundaries]
---

# Preserve ECMAScript strings as exact UTF-16 code units

## Context

ECMAScript strings are sequences of 16-bit code units. They may contain lone surrogates. Rust `String` values are valid UTF-8, so they cannot represent every ECMAScript string without changing data.

This difference affects more than storage. It changes length, indexing, slicing, regular expressions, JSON escaping, property keys, bytecode constants, source positions, and native backends. A partial migration creates a mixed model where each conversion may lose a surrogate or count the wrong unit.

## Guidance

### Use one exact internal string type

Store engine strings as code units. BamTS uses `EcmaString(Arc<[u16]>)` and an `EcmaStringBuilder` for incremental construction. Keep this type through the bytecode, compiler, runtime, JIT, and AOT paths.

Make construction names state the source encoding:

```rust
let source_text = EcmaString::from_utf8("hello");
let exact_value = EcmaString::from_units(&[0xd800, u16::from(b'a')]);

assert_eq!(exact_value.as_units(), &[0xd800, 0x0061]);
```

`from_utf8` encodes Unicode scalar values as UTF-16. `from_units` preserves an existing ECMAScript value exactly. Do not route `from_units` through Rust `String`.

### Convert only at named host boundaries

Keep strict and lossy conversions separate. A strict conversion reports a lone surrogate when the host API requires valid Unicode. A lossy conversion is acceptable only when the host contract calls for replacement characters, and its name must say that it is lossy.

Do not use `String::from_utf16_lossy` inside language operations. It changes the value before the engine can apply ECMAScript rules.

### Define wire formats in code units

Encode the code-unit count, then each `u16` in the format's declared byte order. Decode with checked arithmetic before allocating or reading:

```text
byte_length = code_unit_count * 2
```

Treat a change from UTF-8 bytes to UTF-16 units as a bytecode format break. Bump the format version. Reject old data instead of guessing its encoding.

### Move every semantic consumer to code-unit indexing

Audit all operations that once accepted `&str`, `char`, byte offsets, or scalar-value counts. The migration is incomplete until these paths use UTF-16 units:

- `length`, indexing, slicing, splitting, searching, and comparison
- `charAt`, `charCodeAt`, code-point conversion, URI functions, and escaping
- regular-expression parsing, matching, captures, and replacement
- JSON quoting and parsing
- property names, symbols, module specifiers, and diagnostics that carry runtime strings

Keep source files as UTF-8. Source byte offsets still serve file I/O and parser slicing. Map them to `Utf16Pos` for TypeScript and ECMAScript-facing positions. Sparse checkpoints avoid rescanning the whole prefix for every position.

### Prove preservation across each boundary

Use lone surrogates as the main regression value. Valid Unicode alone cannot expose a lossy conversion. Cover these boundaries:

1. `EcmaString::from_units` preserves the exact `u16` sequence.
2. Bytecode encode and decode round-trip the same units.
3. Interpreter operations observe the same length and `charCodeAt` values.
4. JIT and AOT constant loading produce the same units as the interpreter.
5. CLI or host tests inspect code units before any terminal encoding can replace a surrogate.

A test must cross the real boundary it protects. A unit test for `EcmaString` does not prove the bytecode decoder or native constant path.

## Why This Matters

A UTF-8 internal string model silently makes some valid ECMAScript values unrepresentable. Lossy conversion can merge distinct property keys, change regular-expression matches, corrupt serialized constants, and move source columns. These defects often stay hidden because normal text and emoji remain valid through both encodings.

One exact representation removes conversion branches from the engine. Each host boundary then makes one explicit policy choice: preserve units, reject invalid host text, or replace invalid units because the external contract requires it.

## When to Apply

- When an ECMAScript engine uses a host language whose string type requires Unicode scalar values.
- When bytecode or native artifacts must preserve strings across processes or architectures.
- When string, regular-expression, JSON, or property-key behavior depends on UTF-16 code-unit offsets.
- When source maps or diagnostics must report UTF-16 columns while source files remain UTF-8.

## Examples

A lossy internal path changes a valid ECMAScript value:

```rust
let units = [0xd800];
let changed = String::from_utf16_lossy(&units);
assert_eq!(changed, "\u{fffd}");
```

The exact path keeps the language value intact and delays host conversion:

```rust
let value = EcmaString::from_units(&[0xd800]);
assert_eq!(value.len(), 1);
assert_eq!(value.unit_at(0), Some(0xd800));
```

For wire data, count units rather than UTF-8 bytes. The value `[0xd800, 0x0061]` has two code units and four payload bytes, even though it has no lossless Rust `String` form.

## Related

- [`EcmaString` representation](../../../crates/bamts-bytecode/src/string.rs)
- [Bytecode string encoding](../../../crates/bamts-bytecode/src/lib.rs)
- [UTF-8 byte to UTF-16 source positions](../../../crates/bamts-compiler/src/source.rs)
- [String builtins](../../../crates/bamts-runtime/src/intrinsics/builtins/string.rs)
- [Regular-expression engine](../../../crates/bamts-runtime/src/intrinsics/regexp.rs)
- [RegExp builtins](../../../crates/bamts-runtime/src/intrinsics/builtins/regexp.rs)
- [CLI boundary tests](../../../crates/bamts-cli/tests/cli.rs)
