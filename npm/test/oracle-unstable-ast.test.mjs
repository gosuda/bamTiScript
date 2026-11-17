import assert from "node:assert/strict";
import test from "node:test";
import { CLASS_SOURCE, NESTED_SOURCE, pairByUniqueRange, pinnedAst, pinnedRange, withVisited } from "./oracle-support.mjs";

const ast = await import("../bamti/unstable/ast/index.js");
const pinnedIs = await import("typescript/unstable/ast/is");

// bamti classifies every parser node as a grammar node and never emits lexical
// tokens, so the pinned kinds that areTokenKind covers but bamti lifts into
// grammar nodes (identifiers, literals, keyword types, keyword expressions)
// project to the "node" category; only punctuation projects to "token".
function pinnedCategory(node) {
  const kind = node.kind;
  return pinnedIs.isTokenKind(kind) && !pinnedIs.isTypeNode(node) && !pinnedIs.isExpression(node) ? "token" : "node";
}

test("package shape: the ast barrel declares exactly four operations (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(ast).sort(), ["nodeId", "nodeKind", "nodeRange", "syntaxKind"]);
});

test("ast.nodeRange equals pinned getStart/getEnd of the node with the same unique range", async () => {
  await withVisited(NESTED_SOURCE, async ({ session, sf, preorder, visited }) => {
    for (const { pinned, bamti } of pairByUniqueRange(visited, preorder, sf)) {
      assert.deepStrictEqual(
        await ast.nodeRange(session, { path: "a.ts", nodeId: bamti.id }),
        pinnedRange(pinned, sf),
        pinnedAst.formatSyntaxKind(pinned.kind),
      );
    }
  });
});

test("ast.syntaxKind category matches the pinned kind with bamti grammar-node lifting; kind is a non-empty name", async () => {
  await withVisited(NESTED_SOURCE, async ({ session, sf, preorder, visited }) => {
    for (const { pinned, bamti } of pairByUniqueRange(visited, preorder, sf)) {
      const syntaxKind = await ast.syntaxKind(session, { path: "a.ts", nodeId: bamti.id });
      assert.deepStrictEqual(
        { category: syntaxKind.category, kindType: typeof syntaxKind.kind },
        { category: pinnedCategory(pinned), kindType: "string" },
        pinnedAst.formatSyntaxKind(pinned.kind),
      );
      assert.ok(syntaxKind.kind.length > 0);
    }
  });
});

test("ast.nodeKind is null exactly for projected token kinds and a non-empty name otherwise", async () => {
  await withVisited(NESTED_SOURCE, async ({ session, sf, preorder, visited }) => {
    for (const { pinned, bamti } of pairByUniqueRange(visited, preorder, sf)) {
      const nodeKind = await ast.nodeKind(session, { path: "a.ts", nodeId: bamti.id });
      assert.deepStrictEqual(
        { isNull: nodeKind === null, kindType: nodeKind === null ? "object" : typeof nodeKind },
        { isNull: pinnedCategory(pinned) === "token", kindType: pinnedCategory(pinned) === "token" ? "object" : "string" },
        pinnedAst.formatSyntaxKind(pinned.kind),
      );
    }
  });
});

test("ast.nodeId is bamti's stable parser-assigned identity (no pinned counterpart: pinned Node has no id)", async () => {
  await withVisited(CLASS_SOURCE, async ({ session, visited }) => {
    const ids = visited.filter((node) => node.id !== null).map((node) => node.id);
    assert.ok(ids.length > 0);
    assert.deepStrictEqual(new Set(ids).size, ids.length);
    for (const id of ids.slice(0, 8)) {
      assert.strictEqual(await ast.nodeId(session, { path: "a.ts", nodeId: id }), id);
    }
  });
});
