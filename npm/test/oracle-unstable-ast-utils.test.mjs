import assert from "node:assert/strict";
import test from "node:test";
import {
  NESTED_SOURCE,
  RICH_SOURCE,
  ancestorsOrSelf,
  pairByUniqueRange,
  pinnedAst,
  pinnedRange,
  withPinnedSourceFile,
  withSession,
  withVisited,
} from "./oracle-support.mjs";

const utils = await import("../bamti/unstable/ast/utils.js");
const { isTokenKind } = await import("typescript/unstable/ast/is");

function pinnedTokenAt(sf, position) {
  const token = pinnedAst.getTokenAtPosition(sf, position);
  if (!isTokenKind(token.kind) || position < token.getStart(sf) || position >= token.end) {
    return null;
  }
  return token;
}

test("package shape: the utils subpath declares exactly five operations (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(utils).sort(), [
    "containsPosition",
    "containsRange",
    "narrowestContaining",
    "nodeText",
    "textOfRange",
  ]);
});

test("utils.textOfRange equals pinned Node.getText at every pinned node range", async () => {
  await withSession(RICH_SOURCE, async (session) => {
    await withPinnedSourceFile(RICH_SOURCE, async ({ sf, preorder }) => {
      for (const node of preorder) {
        const range = pinnedRange(node, sf);
        assert.strictEqual(await utils.textOfRange(session, { path: "a.ts", range }), node.getText(sf));
      }
    });
  });
});

test("utils.nodeText equals pinned Node.getText of the pinned node with the same unique range", async () => {
  await withVisited(RICH_SOURCE, async ({ session, sf, preorder, visited }) => {
    for (const { pinned, bamti } of pairByUniqueRange(visited, preorder, sf)) {
      assert.strictEqual(await utils.nodeText(session, { path: "a.ts", nodeId: bamti.id }), pinned.getText(sf));
    }
  });
});

test("utils.containsPosition equals whether the pinned getTokenAtPosition token descends from the node", async () => {
  await withSession(RICH_SOURCE, async (session) => {
    await withPinnedSourceFile(RICH_SOURCE, async ({ sf, preorder }) => {
      const covered = new Set();
      for (const node of preorder) {
        const range = pinnedRange(node, sf);
        const probes = [
          ["before", range.start - 1],
          ["start", range.start],
          ["inside", range.start + 1],
          ["inside", range.end - 1],
          ["end", range.end],
          ["after", range.end + 1],
        ];
        for (const [where, position] of probes) {
          if (position < 0 || pinnedTokenAt(sf, position) === null) {
            continue;
          }
          const expected = ancestorsOrSelf(pinnedTokenAt(sf, position)).includes(node);
          covered.add(`${where}:${expected}`);
          assert.strictEqual(
            await utils.containsPosition(session, { range, position }),
            expected,
            `${JSON.stringify(range)} contains ${position}`,
          );
        }
      }
      for (const required of ["before:false", "start:true", "inside:true", "end:false"]) {
        assert.ok(covered.has(required), `no pinned case ${required}`);
      }
    });
  });
});

test("utils.narrowestContaining range equals the nearest pinned visitEachChild node on the pinned getTokenAtPosition ancestor chain", async () => {
  await withSession(NESTED_SOURCE, async (session) => {
    await withPinnedSourceFile(NESTED_SOURCE, async ({ sf, preorder }) => {
      const visitedByPinned = new Set(preorder);
      let compared = 0;
      for (let position = 0; position <= sf.end; position += 1) {
        const token = pinnedTokenAt(sf, position);
        if (token === null) {
          continue;
        }
        const nearest = ancestorsOrSelf(token).find((node) => visitedByPinned.has(node));
        assert.ok(nearest, `position ${position} has no pinned visited ancestor`);
        const node = await utils.narrowestContaining(session, { path: "a.ts", position });
        assert.deepStrictEqual(node?.range, pinnedRange(nearest, sf), `position ${position}`);
        compared += 1;
      }
      assert.ok(compared > 0);
    });
  });
});

test("utils.containsRange equals ordinary UTF-16 interval containment on pinned ranges", async () => {
  await withSession(RICH_SOURCE, async (session) => {
    await withPinnedSourceFile(RICH_SOURCE, async ({ sf, preorder }) => {
      const outers = preorder
        .map((node) => pinnedRange(node, sf))
        .filter((range) => range.start >= 1 && range.end - range.start >= 3)
        .slice(0, 4);
      assert.ok(outers.length > 0, "no pinned range admits boundary probes");
      const covered = new Set();
      for (const outer of outers) {
        const inners = [
          ["equal", { start: outer.start, end: outer.end }],
          ["strict-interior", { start: outer.start + 1, end: outer.end - 1 }],
          ["touches-start", { start: outer.start, end: outer.start + 1 }],
          ["touches-end", { start: outer.end - 1, end: outer.end }],
          ["empty-at-start", { start: outer.start, end: outer.start }],
          ["empty-at-end", { start: outer.end, end: outer.end }],
          ["empty-inside", { start: outer.start + 1, end: outer.start + 1 }],
          ["overlap-left", { start: outer.start - 1, end: outer.start + 1 }],
          ["overlap-right", { start: outer.end - 1, end: outer.end + 1 }],
          ["adjacent-before", { start: outer.start - 1, end: outer.start }],
          ["adjacent-after", { start: outer.end, end: outer.end + 1 }],
          ["wider", { start: outer.start - 1, end: outer.end + 1 }],
          ["empty-outside", { start: outer.end + 1, end: outer.end + 1 }],
        ];
        for (const [label, inner] of inners) {
          const expected = outer.start <= inner.start && inner.end <= outer.end;
          const actual = await utils.containsRange(session, { outer, inner });
          assert.strictEqual(
            actual,
            expected,
            `${label} ${JSON.stringify(outer)} vs ${JSON.stringify(inner)}`,
          );
          covered.add(`${label}:${actual}`);
        }
      }
      for (const required of [
        "equal:true",
        "touches-start:true",
        "touches-end:true",
        "empty-at-start:true",
        "empty-at-end:true",
        "overlap-left:false",
        "overlap-right:false",
        "adjacent-before:false",
        "adjacent-after:false",
        "wider:false",
        "empty-outside:false",
      ]) {
        assert.ok(covered.has(required), `no case ${required}`);
      }
    });
  });
});
