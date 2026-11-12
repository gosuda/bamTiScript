import assert from "node:assert/strict";
import test from "node:test";
import {
  NESTED_SOURCE,
  bamtiRanges,
  pairByUniqueRange,
  pinnedAst,
  pinnedRange,
  pinnedRanges,
  withVisited,
} from "./oracle-support.mjs";

const clone = await import("../bamti/unstable/ast/clone.js");
const visitor = await import("../bamti/unstable/ast/visitor.js");
const pinnedFactory = await import("typescript/unstable/ast/factory");

const CALLER_ID = 987654;

async function compareCloneRanges(operation, params) {
  await withVisited(NESTED_SOURCE, async ({ session, sf, preorder, visited }) => {
    const pairs = pairByUniqueRange(visited, preorder, sf).filter(({ pinned }) => pinned !== sf);
    for (const { pinned, bamti } of pairs) {
      const cloned = await operation(session, { path: "a.ts", nodeId: bamti.id, ...params });
      assert.deepStrictEqual(cloned.range, pinnedRange(pinnedFactory.cloneNode(pinned), sf), pinnedAst.formatSyntaxKind(pinned.kind));
    }
    assert.deepStrictEqual(bamtiRanges(await visitor.visitSourceFile(session, { path: "a.ts" })), pinnedRanges(preorder, sf));
  });
}

test("package shape: the clone subpath declares exactly two operations (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(clone).sort(), ["cloneNode", "cloneNodeWithId"]);
});

test("clone.cloneNode range equals the range of pinned cloneNode of the node with the same unique range", async () => {
  await compareCloneRanges(clone.cloneNode, {});
});

test("clone.cloneNodeWithId range equals the range of pinned cloneNode of the node with the same unique range", async () => {
  await compareCloneRanges(clone.cloneNodeWithId, { id: CALLER_ID });
});
