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
