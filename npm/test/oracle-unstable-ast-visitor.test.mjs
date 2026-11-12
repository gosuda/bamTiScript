import assert from "node:assert/strict";
import fs from "node:fs";
import { registerHooks } from "node:module";
import os from "node:os";
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
    return nextResolve(specifier, context);
  },
});

const { createSession } = await import("../bamti/internal/session.js");
const visitor = await import("../bamti/unstable/ast/visitor.js");
const { API } = await import("typescript/unstable/sync");
const pinnedAst = await import("typescript/unstable/ast");
const { visitEachChild } = await import("typescript/unstable/ast/visitor");

const worktreeRoot = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const SOURCE = "const alpha = 1;";

const PINNED_TO_BAMTI_NODE_KIND = {
  SourceFile: "SourceFile",
  VariableStatement: "VariableDeclaration",
  VariableDeclaration: "VariableDeclarator",
  Identifier: "BindingIdentifier",
  NumericLiteral: "LiteralExpression",
};

const PINNED_WITHOUT_BAMTI_COUNTERPART = ["EndOfFileToken", "VariableDeclarationList"];

async function withSession(text, fn) {
  const session = createSession({ transportOptions: { binary: BINARY } });
  try {
    await session.open({ path: "a.ts", text, version: 1 });
    await fn(session);
  } finally {
    await session.dispose();
  }
}

async function withPinnedSourceFile(text, fn) {
  const dir = fs.mkdtempSync(join(os.tmpdir(), "bamti-pinned-"));
  fs.writeFileSync(join(dir, "a.ts"), text);
  fs.writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: {}, files: ["a.ts"] }));
  const api = new API({});
  const snap = api.updateSnapshot({ openProjects: [join(dir, "tsconfig.json")] });
  try {
    const proj =
      snap.getProject(join(dir, "tsconfig.json")) ??
      snap.getDefaultProjectForFile(join(dir, "a.ts"));
    const sf = proj.program.getSourceFile(join(dir, "a.ts"));
    assert.ok(sf);
    const preorder = [];
    const record = (node) => {
      preorder.push(node);
      return visitEachChild(node, record);
    };
    record(sf);
    await fn({ sf, preorder });
  } finally {
    snap.dispose();
    api.close();
  }
}

function pinnedRow(node, sf) {
  return {
    pinnedName: pinnedAst.formatSyntaxKind(node.kind),
    tokenStart: pinnedAst.getTokenPosOfNode(node, sf),
    end: node.end,
  };
}

test("visitor subpath exports exactly two operations", () => {
  assert.deepStrictEqual(Object.keys(visitor).sort(), ["visitNode", "visitSourceFile"]);
});

test("visitor.visitSourceFile matches pinned preorder and token ranges (npm/bamti/unstable/ast/visitor.d.ts:3, typescript/dist/ast/visitor.d.ts:9)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const rows = preorder.map((node) => pinnedRow(node, sf));
      const unmapped = rows.filter((row) => !Object.hasOwn(PINNED_TO_BAMTI_NODE_KIND, row.pinnedName));
      assert.deepStrictEqual(
        unmapped.map((row) => row.pinnedName).sort(),
        PINNED_WITHOUT_BAMTI_COUNTERPART.slice().sort(),
      );
      const mapped = rows.filter((row) => Object.hasOwn(PINNED_TO_BAMTI_NODE_KIND, row.pinnedName));
      const nodes = await visitor.visitSourceFile(session, { path: "a.ts" });
      assert.strictEqual(nodes.length, mapped.length);
      for (const [index, want] of mapped.entries()) {
        const got = nodes[index];
        assert.strictEqual(got.nodeKind, PINNED_TO_BAMTI_NODE_KIND[want.pinnedName]);
        assert.deepStrictEqual(got.range, { start: want.tokenStart, end: want.end });
        assert.deepStrictEqual(got.syntaxKind, { category: "node", kind: got.nodeKind });
      }
      const ids = nodes.map((node) => node.id);
      assert.ok(ids.every((id) => typeof id === "number"));
      assert.strictEqual(new Set(ids).size, ids.length);
    });
  });
});

test("visitor.visitNode returns the pinned subtree at the selector (npm/bamti/unstable/ast/visitor.d.ts:4)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
      const statement = visited.find((node) => node.nodeKind === "VariableDeclaration");
      assert.ok(statement);
      const subtree = await visitor.visitNode(session, { path: "a.ts", nodeId: statement.id });
      assert.deepStrictEqual(subtree, visited.slice(1));
      const anchor = preorder.find(
        (node) => pinnedAst.formatSyntaxKind(node.kind) === "VariableStatement",
      );
      assert.ok(anchor);
      const pinnedSubtree = [];
      const collect = (node) => {
        pinnedSubtree.push(node);
        return visitEachChild(node, collect);
      };
      collect(anchor);
      const mapped = pinnedSubtree
        .map((node) => pinnedRow(node, sf))
        .filter((row) => Object.hasOwn(PINNED_TO_BAMTI_NODE_KIND, row.pinnedName));
      assert.strictEqual(subtree.length, mapped.length);
      for (const [index, want] of mapped.entries()) {
        const got = subtree[index];
        assert.strictEqual(got.nodeKind, PINNED_TO_BAMTI_NODE_KIND[want.pinnedName]);
        assert.deepStrictEqual(got.range, { start: want.tokenStart, end: want.end });
      }
    });
  });
});
