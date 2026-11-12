import assert from "node:assert/strict";
import test from "node:test";
import {
  CLASS_SOURCE,
  NESTED_SOURCE,
  bamtiRanges,
  pairByUniqueRange,
  pinnedPreorder,
  pinnedRanges,
  withVisited,
} from "./oracle-support.mjs";

const visitor = await import("../bamti/unstable/ast/visitor.js");

test("package shape: the visitor subpath declares exactly two operations (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(visitor).sort(), ["visitNode", "visitSourceFile"]);
});

for (const [name, text] of [
  ["a nested if block, a function name, and a member name", NESTED_SOURCE],
  ["a class name, a private field, a method name, and a private member access", CLASS_SOURCE],
]) {
  test(`visitor.visitSourceFile range order equals pinned visitEachChild preorder on ${name}`, async () => {
    await withVisited(text, async ({ sf, preorder, visited }) => {
      assert.deepStrictEqual(bamtiRanges(visited), pinnedRanges(preorder, sf));
    });
  });

  test(`visitor.visitNode range order equals pinned visitEachChild subtree preorder on ${name}`, async () => {
    await withVisited(text, async ({ session, sf, preorder, visited }) => {
      for (const { pinned, bamti } of pairByUniqueRange(visited, preorder, sf)) {
        const subtree = await visitor.visitNode(session, { path: "a.ts", nodeId: bamti.id });
        assert.deepStrictEqual(bamtiRanges(subtree), pinnedRanges(pinnedPreorder(pinned, sf), sf));
      }
    });
  });
}
