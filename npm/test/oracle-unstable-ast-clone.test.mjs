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
const clone = await import("../bamti/unstable/ast/clone.js");
const visitor = await import("../bamti/unstable/ast/visitor.js");
const { API } = await import("typescript/unstable/sync");
const pinnedAst = await import("typescript/unstable/ast");
const { visitEachChild } = await import("typescript/unstable/ast/visitor");
const { SyntaxKind } = await import("../../node_modules/typescript/dist/enums/syntaxKind.js");

const worktreeRoot = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const SOURCE = "const alpha = 1;";
const CALLER_ID = 987654;

const WANT_NODE_KIND = "VariableDeclaration";
const WANT_SYNTAX_KIND = { category: "node", kind: "VariableDeclaration" };
const PINNED_NAME = "VariableStatement";

const CLONE_CASES = { cloneNode: true, cloneNodeWithId: true };

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

function pinnedWant(preorder, sf) {
  const anchor = preorder.find((node) => pinnedAst.formatSyntaxKind(node.kind) === PINNED_NAME);
  assert.ok(anchor);
  assert.strictEqual(SyntaxKind[PINNED_NAME], anchor.kind);
  return { tokenStart: pinnedAst.getTokenPosOfNode(anchor, sf), end: anchor.end };
}

test("clone subpath exports exactly two operations", () => {
  const names = Object.keys(clone).sort();
  assert.deepStrictEqual(names, ["cloneNode", "cloneNodeWithId"]);
  for (const name of names) {
    assert.ok(Object.hasOwn(CLONE_CASES, name), `no case covers exported ${name}`);
  }
});

test("clone.cloneNode preserves identity and matches the pinned node (npm/bamti/unstable/ast/clone.d.ts:3)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
      const statement = visited.find((node) => node.nodeKind === WANT_NODE_KIND);
      assert.ok(statement);
      const copied = await clone.cloneNode(session, { path: "a.ts", nodeId: statement.id });
      assert.notStrictEqual(copied, statement);
      assert.strictEqual(copied.id, statement.id);
      assert.deepStrictEqual(copied.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(copied.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(copied.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(copied.range.start, copied.range.end), SOURCE);
      copied.range.start = -1;
      copied.nodeKind = "Bogus";
      const again = await visitor.visitSourceFile(session, { path: "a.ts" });
      const original = again.find((node) => node.id === statement.id);
      assert.deepStrictEqual(original.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(original.nodeKind, WANT_NODE_KIND);
    });
  });
});

test("clone.cloneNodeWithId takes the caller id and leaves the original alone (npm/bamti/unstable/ast/clone.d.ts:4)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
      const statement = visited.find((node) => node.nodeKind === WANT_NODE_KIND);
      assert.ok(statement);
      const copied = await clone.cloneNodeWithId(session, {
        path: "a.ts",
        nodeId: statement.id,
        id: CALLER_ID,
      });
      assert.strictEqual(copied.id, CALLER_ID);
      assert.deepStrictEqual(copied.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(copied.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(copied.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(copied.range.start, copied.range.end), SOURCE);
      const again = await visitor.visitSourceFile(session, { path: "a.ts" });
      assert.ok(again.some((node) => node.id === statement.id));
      assert.ok(!again.some((node) => node.id === CALLER_ID));
    });
  });
});
