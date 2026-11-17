import assert from "node:assert/strict";
import test from "node:test";
import { CLASS_SOURCE, pairByUniqueRange, pinnedAst, withVisited } from "./oracle-support.mjs";

const isMod = await import("../bamti/unstable/ast/is.js");
const pinnedIs = await import("typescript/unstable/ast/is");

// Fixed source exercising declarations, type nodes, literals, keyword types,
// keyword expressions, private identifiers, and member access.
const TYPE_SOURCE = "const rate: number = 1;\nexport function scale(value: number): number { return value * rate; }\n";

// Projections (bamti reclassifies shapes the pinned kind space folds into
// keyword-token-range kinds):
// - token/node: bamti never emits lexical tokens, so a paired node is "token"
//   only under pinned punctuation kinds; keyword kinds that bamti lifts into
//   grammar nodes (keyword types, keyword expressions like this) are "node".
// - keyword: the keyword-token part of the token projection.
// - statement/expression/typeNode: pinned isStatement/isExpression/isTypeNode.
// - declaration: the pinned package has no isDeclaration guard, so the union is
//   composed from exported guards; bamti's VariableDeclaration is pinned
//   VariableStatement, its VariableDeclarator is pinned VariableDeclaration,
//   and its NamespaceDeclaration is pinned ModuleDeclaration.
// - literal: pinned isLiteralExpression (numeric/bigint/string/regex kinds)
//   or isLiteralTypeNode for bamti's LiteralType nodes.
function keywordTokenProjection(node) {
  return pinnedIs.isKeywordKind(node.kind) && !pinnedIs.isTypeNode(node) && !pinnedIs.isExpression(node);
}
function tokenProjection(node) {
  return pinnedIs.isPunctuationKind(node.kind) || keywordTokenProjection(node);
}
function declarationProjection(node) {
  return (
    pinnedIs.isImportDeclaration(node) ||
    pinnedIs.isImportEqualsDeclaration(node) ||
    pinnedIs.isExportDeclaration(node) ||
    pinnedIs.isVariableStatement(node) ||
    pinnedIs.isVariableDeclaration(node) ||
    pinnedIs.isFunctionDeclaration(node) ||
    pinnedIs.isClassDeclaration(node) ||
    pinnedIs.isInterfaceDeclaration(node) ||
    pinnedIs.isTypeAliasDeclaration(node) ||
    pinnedIs.isEnumDeclaration(node) ||
    pinnedIs.isEnumMember(node) ||
    pinnedIs.isModuleDeclaration(node)
  );
}
function literalProjection(node) {
  return pinnedIs.isLiteralExpression(node) || pinnedIs.isLiteralTypeNode(node);
}
// A pinned Identifier or PrivateIdentifier in a name position (a declaration or
// member name) is a name in bamti, not an expression; the pinned guard calls
// every one of them an expression.
function expressionProjection(node) {
  const isName = (pinnedIs.isIdentifier(node) || pinnedIs.isPrivateIdentifier(node)) && node.parent?.name === node;
  return pinnedIs.isExpression(node) && !isName;
}
function pinnedPredicates(node) {
  return {
    token: tokenProjection(node),
    node: !tokenProjection(node),
    keyword: keywordTokenProjection(node),
    statement: pinnedIs.isStatement(node),
    expression: expressionProjection(node),
    typeNode: pinnedIs.isTypeNode(node),
    declaration: declarationProjection(node),
    literal: literalProjection(node),
  };
}

const PREDICATES = ["token", "node", "keyword", "statement", "expression", "typeNode", "declaration", "literal"];

async function bamtiPredicates(session, bamtiId) {
  const out = {};
  for (const predicate of PREDICATES) {
    out[predicate] = await isMod.nodeIs(session, { path: "a.ts", nodeId: bamtiId, predicate });
  }
  return out;
}

test("package shape: the ast/is subpath declares exactly one operation (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(isMod), ["nodeIs"]);
});

// The class declaration spans the whole class source, so it shares a range with the
// file and cannot be paired; only the first source has a declaration to require.
for (const [name, text, required] of [
  ["declarations, annotations, and literals", TYPE_SOURCE, ["node", "statement", "expression", "declaration"]],
  ["a class with a private field and a method", CLASS_SOURCE, ["node", "statement", "expression"]],
]) {
  test(`nodeIs matches the pinned type-guard projections on ${name}`, async () => {
    await withVisited(text, async ({ session, sf, preorder, visited }) => {
      const covered = new Set();
      const pairs = pairByUniqueRange(visited, preorder, sf).filter(({ bamti }) => bamti.id !== null);
      assert.ok(pairs.length > 0, `no paired nodes for ${name}`);
      for (const { pinned, bamti } of pairs) {
        const expected = pinnedPredicates(pinned);
        const actual = await bamtiPredicates(session, bamti.id);
        assert.deepStrictEqual(actual, expected, pinnedAst.formatSyntaxKind(pinned.kind));
        for (const [predicate, value] of Object.entries(expected)) {
          if (value) {
            covered.add(predicate);
          }
        }
      }
      for (const predicate of required) {
        assert.ok(covered.has(predicate), `no true case for ${predicate}`);
      }
    });
  });
}

test("nodeIs exercises true literal and typeNode cases with keyword-lifted kinds staying node", async () => {
  await withVisited(TYPE_SOURCE, async ({ session, sf, preorder, visited }) => {
    const pairs = pairByUniqueRange(visited, preorder, sf).filter(({ bamti }) => bamti.id !== null);
    const byFlag = new Map();
    for (const { pinned, bamti } of pairs) {
      const actual = await bamtiPredicates(session, bamti.id);
      const expected = pinnedPredicates(pinned);
      assert.deepStrictEqual(actual, expected, pinnedAst.formatSyntaxKind(pinned.kind));
      for (const predicate of PREDICATES) {
        if (expected[predicate]) {
          byFlag.set(predicate, pinnedAst.formatSyntaxKind(pinned.kind));
        }
      }
    }
    assert.ok(byFlag.has("literal"), `no literal true case, got ${[...byFlag]}`);
    assert.ok(byFlag.has("typeNode"), `no typeNode true case, got ${[...byFlag]}`);
    assert.ok(byFlag.has("expression"), `no expression true case, got ${[...byFlag]}`);
    assert.deepStrictEqual(byFlag.get("typeNode"), "NumberKeyword");
    assert.deepStrictEqual(byFlag.get("literal"), "NumericLiteral");
  });
});
