import assert from "node:assert/strict";
import test from "node:test";
import { NESTED_SOURCE, nonEmpty, pairByUniqueRange, pinnedAst, withVisited } from "./oracle-support.mjs";

const factory = await import("../bamti/unstable/ast/factory.js");
const f = await import("typescript/unstable/ast/factory");

const CHANGE_ID = 9103;

const PINNED_UPDATE_WITH_SAME_CHILDREN = {
  FunctionDeclaration: (n) =>
    f.updateFunctionDeclaration(n, n.modifiers, n.asteriskToken, n.name, n.typeParameters, n.parameters, n.type, n.body),
  Block: (n) => f.updateBlock(n, n.statements),
  IfStatement: (n) => f.updateIfStatement(n, n.expression, n.thenStatement, n.elseStatement),
  ExpressionStatement: (n) => f.updateExpressionStatement(n, n.expression),
  PropertyAccessExpression: (n) => f.updatePropertyAccessExpression(n, n.expression, n.questionDotToken, n.name),
};

async function withUpdatable(fn) {
  await withVisited(NESTED_SOURCE, async ({ session, sf, preorder, visited }) => {
    const pairs = pairByUniqueRange(visited, preorder, sf).filter(({ pinned }) =>
      Object.hasOwn(PINNED_UPDATE_WITH_SAME_CHILDREN, pinnedAst.formatSyntaxKind(pinned.kind)),
    );
    nonEmpty(pairs, "nodes with a pinned update function");
    for (const { pinned, bamti } of pairs) {
      const updated = PINNED_UPDATE_WITH_SAME_CHILDREN[pinnedAst.formatSyntaxKind(pinned.kind)](pinned);
      await fn({ session, sf, pinned, bamti, updated });
    }
  });
}

test("package shape: the factory subpath declares exactly four operations (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(factory).sort(), ["asNode", "createNode", "intoOwned", "updateNode"]);
});

test("factory.updateNode with the node's own range is original exactly when pinned update* with the same children returns its input", async () => {
  await withUpdatable(async ({ session, pinned, bamti, updated }) => {
    const result = await factory.updateNode(session, { path: "a.ts", nodeId: bamti.id, changedId: CHANGE_ID, range: bamti.range });
    assert.strictEqual(result.original, updated === pinned, pinnedAst.formatSyntaxKind(pinned.kind));
  });
});
