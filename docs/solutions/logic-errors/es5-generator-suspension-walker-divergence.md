---
title: ES5 generator suspension walkers must agree before inline cloning
date: 2026-09-05
category: logic-errors
module: compiler
problem_type: logic_error
component: es5-generator-lowerer
severity: critical
symptoms:
  - "ES5 lowering of generator functions emits `__generator` helper wrapping a live `yield` inside a plain (non-generator) function"
  - "Expressions with array-spread, computed-key update, or pattern-assignment targets are cloned verbatim when the inline-clone gate reports zero yields"
  - "debug_assert_eq! on segments/exit_label fires (left:2 right:3) for identifier-assignment loop tests; release builds jump to a wrong case"
  - "The contains_yield, count_yields, and contains_await views disagree per shape"
root_cause: logic_error
resolution_type: code_fix
related_components: [emitter, transforms]
tags: [es5, generator, walker, duality, miscompile, inline-clone, sentinel]
applies_when:
  - "Editing contains_yield, count_yields, contains_await, contains_yield_array, or statements_contain_await in crates/bamts-compiler/src/emitter/transforms.rs"
  - "Adding an expression or member shape the machine may clone inline in loop/branch tests"
  - "Changing eval acceptance (eval-refused vs eval-accepted shapes)"
---

# ES5 generator suspension walkers must agree before inline cloning

## Problem

The ES5 downleveler keeps three overlapping views of "does this expression
suspend?": `contains_yield`/`contains_await` (boolean; gate statement-level
cloning in `machine_emit_expression` and `eval`), `count_yields` (u32; gates
the loop/branch TEST inline clone at `machine_emit_while`/`do`/`for` and
drives `exit_label = head + test_resumes + body_resumes + 1`), and
`contains_yield_array` (boolean; guards `eval_array`). They were not kept in
per-shape sync. Any shape where the inline gate's view under-reports what
`eval` would refuse gets cloned verbatim with a live `yield` inside a plain
function — a silent miscompile. Any shape where it OVER-reports on an
eval-accepted target inflates label arithmetic and mints a wrong case.

## Symptoms

Three concrete instances of the one class, all present at HEAD 43bdcb6 and
caught by adversarial review:

1. `count_yields` had no `Expression::Update` arm. `while (o[yield k]++ < 3)`
   counted 0, cloned verbatim, and emitted:
   ```js
   function g() { return __generator(this, function (_a) {
       while (o[yield k]++ < 3) { }
       return [2 /*return*/];
   }); }
   ```
   (plain `function g`, live `yield` — the never-miscompile contract broken).
2. `contains_yield_array` ignored `ArrayElement::Spread`. `[...(yield x)]`
   reported clean and cloned at the statement gate; same wrapper form.
3. A pattern-target sentinel in `count_yields`' Assignment arm swallowed
   `AssignmentTarget::Identifier`: `while (x = 1) { await y; }` counted a
   phantom resume, inflating `exit_label` — debug builds fail
   `debug_assert_eq!(ctx.segments.len() as u32 - 1, exit_label)` with
   `left: 2 right: 3`; release builds jump to a wrong case.

## What Didn't Work

- Statement-level probes missed instance 1 twice: the statement gate
  (`machine_emit_expression`, keyed on `contains_yield` at ~4265) and the
  loop-test gate (`machine_emit_while`, keyed on `count_yields` at ~4435)
  are DIFFERENT gates. Probe the claimed trigger shape, not an adjacent one.
- Fixing only the boolean walkers left label arithmetic wrong.
- The original `count_yields` catch-all `_ => 0` declared every unlisted
  shape "provably clean" — the polarity itself was the defect class.
- Three earlier commits (c3ddb6d, 01e5c5a, 34cef0e) re-learned this class
  one arm at a time.

## Solution

Two rules, applied to `transforms.rs` (~7016-7130, ~7450-7540):

1. **Precise arms for eval-ACCEPTED shapes** — count exactly what `eval`
   splits: `AssignmentTarget::Identifier(_) => 0`, Member targets
   (object + computed key), `Expression::Update` (member object + computed
   key; Identifier 0), `Expression::Import` (source + options), and
   `ObjectMember::Spread` / `ArrayElement::Spread` arguments. Method-like
   object members stay 0 (nested function-likes own their suspensions,
   consistent with `Expression::Function => 0`).
2. **Non-zero sentinel ONLY for eval-REFUSED shapes** — the outer catch-all
   is `_ => 1` (zero now means provably clean; unknown routes to `eval`,
   whose refusal keeps the native generator + `GENERATOR_REQUIRES_ES2015`).
   Verified: eval has no accepting arms for TaggedTemplate, Satisfies,
   TypeAssertion, or the JSX variants. A sentinel on an eval-accepted shape
   is instance 3 again.

```rust
// count_yields, the two load-bearing arm shapes:
Expression::Update(update) => match update.argument.data() {
    AssignmentTarget::Member(member) => {
        count_yields(&member.object)
            + match &member.property {
                MemberProperty::Computed(key) => count_yields(key),
                _ => 0,
            }
    }
    AssignmentTarget::Identifier(_) => 0,
    _ => 1, // pattern/invalid targets: eval refuses them
},
// ...
    AssignmentTarget::Identifier(_) => 0,
    _ => 1,
// outer catch-all:
_ => 1, // unknown: never the inline clone; eval refuses
```

## Why This Works

The inline-clone fast-path (`if test_resumes == 0 && body_resumes == 0 {
ctx.push(statement.clone()); }`) is only safe when zero is a PROOF of
cleanliness. Making every non-provably-clean shape non-zero routes it to
`eval`, which either splits it correctly or refuses (native fallback +
diagnostic) — both contract-compliant. Exact counting on eval-accepted
shapes keeps `exit_label` arithmetic equal to the number of segments eval
actually mints.

## Prevention

- Audit `contains_yield` / `count_yields` / `contains_await` /
  `statements_contain_await` as ONE SET on any walker edit; the
  enumerate-all-arms diff across the three views is the systematic close.
- A sentinel wildcard is only safe on shapes the fallback consumer
  (eval) REFUSES; enumerate eval-accepted shapes as explicit arms first.
- Pin the CONTRACT, not just refusal shapes: a pin per gate (statement
  gate AND loop-test gate), each mutation-proven by deleting the arm and
  recording the exact miscompile output. Existing pins:
  `es5_generator_update_computed_key_refuses`,
  `es5_generator_array_spread_yield_never_clones`,
  `es5_generator_object_spread_yield_refuses`,
  `es5_async_identifier_assignment_test_stays_inline`,
  `es5_async_for_update_increment_lowers` (emitter.rs cfg(test)).
- The corpus-level regression gate is the suite pair
  (`cargo test -p bamts-compiler` + `cargo test -p bamts-verification`),
  never the bare CLI `-p` path (it never lowers the machine — refusal form
  only). The verification crate's corpus_differential target additionally
  demands the pinned `node@24.18.0` first on `PATH`
  (`mise install node@24.18.0`, then prefix the install's bin dir) — the
  `BAMTS_ALLOW_NODE_COMPAT=1` flag covers the lib target only and leaves
  corpus_differential panicking on the version check. That pair is the
  leaf evidence;
  the completion claim itself binds to the receipt-backed G3 compiler root
  gate in `.outline/GATES.md` — a green suite pair is necessary, not
  sufficient, and closure language must cite the G3 receipts, not the leaf
  suites alone.
