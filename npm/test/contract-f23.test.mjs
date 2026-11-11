import assert from "node:assert/strict";
import { registerHooks } from "node:module";
import { dirname, join } from "node:path";
import test from "node:test";
import { fileURLToPath, pathToFileURL } from "node:url";

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");

registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === "bamti-cli") {
      return {
        shortCircuit: true,
        url: pathToFileURL(join(npmRoot, "bamti-cli", "index.js")).href,
      };
    }
    return nextResolve(specifier);
  },
});

const ast = await import("../bamti/unstable/ast/index.js");
test("ast.nodeId is function", () => assert.ok(typeof ast.nodeId === "function"));
test("ast.nodeRange is function", () => assert.ok(typeof ast.nodeRange === "function"));
test("ast.syntaxKind is function", () => assert.ok(typeof ast.syntaxKind === "function"));
test("ast.nodeKind is function", () => assert.ok(typeof ast.nodeKind === "function"));

const isMod = await import("../bamti/unstable/ast/is.js");
test("is.nodeIs is function", () => assert.ok(typeof isMod.nodeIs === "function"));

const factory = await import("../bamti/unstable/ast/factory.js");
test("factory.createNode is function", () => assert.ok(typeof factory.createNode === "function"));
test("factory.updateNode is function", () => assert.ok(typeof factory.updateNode === "function"));
test("factory.asNode is function", () => assert.ok(typeof factory.asNode === "function"));
test("factory.intoOwned is function", () => assert.ok(typeof factory.intoOwned === "function"));

const utils = await import("../bamti/unstable/ast/utils.js");
test("utils.textOfRange is function", () => assert.ok(typeof utils.textOfRange === "function"));
test("utils.nodeText is function", () => assert.ok(typeof utils.nodeText === "function"));
test("utils.containsRange is function", () => assert.ok(typeof utils.containsRange === "function"));
test("utils.containsPosition is function", () => assert.ok(typeof utils.containsPosition === "function"));
test("utils.narrowestContaining is function", () => assert.ok(typeof utils.narrowestContaining === "function"));

const scanner = await import("../bamti/unstable/ast/scanner.js");
test("scanner.scan is function", () => assert.ok(typeof scanner.scan === "function"));

const visitor = await import("../bamti/unstable/ast/visitor.js");
test("visitor.visitSourceFile is function", () => assert.ok(typeof visitor.visitSourceFile === "function"));
test("visitor.visitNode is function", () => assert.ok(typeof visitor.visitNode === "function"));

const clone = await import("../bamti/unstable/ast/clone.js");
test("clone.cloneNode is function", () => assert.ok(typeof clone.cloneNode === "function"));
test("clone.cloneNodeWithId is function", () => assert.ok(typeof clone.cloneNodeWithId === "function"));

test("total 19 operations across 7 modules", () => {
  const all = [
    ast.nodeId, ast.nodeRange, ast.syntaxKind, ast.nodeKind,
    isMod.nodeIs,
    factory.createNode, factory.updateNode, factory.asNode, factory.intoOwned,
    utils.textOfRange, utils.nodeText, utils.containsRange, utils.containsPosition, utils.narrowestContaining,
    scanner.scan,
    visitor.visitSourceFile, visitor.visitNode,
    clone.cloneNode, clone.cloneNodeWithId,
  ];
  assert.equal(all.length, 19, `expected 19 operations, got ${all.length}`);
  for (const fn of all) {
    assert.ok(typeof fn === "function", "all operations must be functions");
  }
});

test("dispatch probe: 19 ast method names", () => {
  const calls = [];
  const fakeSession = {
    request(method, params, options) {
      calls.push(method);
      return Promise.resolve(null);
    },
  };
  ast.nodeId(fakeSession, {});
  ast.nodeRange(fakeSession, {});
  ast.syntaxKind(fakeSession, {});
  ast.nodeKind(fakeSession, {});
  isMod.nodeIs(fakeSession, {});
  factory.createNode(fakeSession, {});
  factory.updateNode(fakeSession, {});
  factory.asNode(fakeSession, {});
  factory.intoOwned(fakeSession, {});
  utils.textOfRange(fakeSession, {});
  utils.nodeText(fakeSession, {});
  utils.containsRange(fakeSession, {});
  utils.containsPosition(fakeSession, {});
  utils.narrowestContaining(fakeSession, {});
  scanner.scan(fakeSession, {});
  visitor.visitSourceFile(fakeSession, {});
  visitor.visitNode(fakeSession, {});
  clone.cloneNode(fakeSession, {});
  clone.cloneNodeWithId(fakeSession, {});

  const expected = [
    "ast/id", "ast/range", "ast/syntaxKind", "ast/nodeKind",
    "ast/is",
    "ast/factory/create", "ast/factory/update", "ast/factory/asNode", "ast/factory/intoOwned",
    "ast/utils/textOfRange", "ast/utils/nodeText", "ast/utils/containsRange", "ast/utils/containsPosition", "ast/utils/narrowestContaining",
    "ast/scanner/scan",
    "ast/visitor/visitSourceFile", "ast/visitor/visitNode",
    "ast/clone", "ast/cloneWithId",
  ];
  assert.equal(calls.length, 19, `got ${calls.length} calls`);
  assert.deepEqual(calls, expected, `method mismatch: ${JSON.stringify(calls)}`);
});
