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
const factory = await import("../bamti/unstable/ast/factory.js");
const visitor = await import("../bamti/unstable/ast/visitor.js");
const { API } = await import("typescript/unstable/sync");
const pinnedAst = await import("typescript/unstable/ast");
const { visitEachChild } = await import("typescript/unstable/ast/visitor");
const { SyntaxKind } = await import("../../node_modules/typescript/dist/enums/syntaxKind.js");

const worktreeRoot = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const SOURCE = "const alpha = 1;";
const PREFIX_RANGE = { start: 0, end: 1 };
const CREATE_ID = 9101;
const REUSE_ID = 9102;
const CHANGE_ID = 9103;
const AS_ID = 9104;
const OWNED_SAME_ID = 9105;
const OWNED_CHANGE_ID = 9106;

const WANT_NODE_KIND = "VariableDeclaration";
const WANT_SYNTAX_KIND = { category: "node", kind: "VariableDeclaration" };
const PINNED_NAME = "VariableStatement";

const FACTORY_CASES = { createNode: true, updateNode: true, asNode: true, intoOwned: true };

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

async function bamtiStatement(session, want) {
  const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
  const statement = visited.find((node) => node.nodeKind === WANT_NODE_KIND);
  assert.ok(statement);
  assert.deepStrictEqual(statement.range, { start: want.tokenStart, end: want.end });
  return statement;
}

test("factory subpath exports exactly four operations", () => {
  const names = Object.keys(factory).sort();
  assert.deepStrictEqual(names, ["asNode", "createNode", "intoOwned", "updateNode"]);
  for (const name of names) {
    assert.ok(Object.hasOwn(FACTORY_CASES, name), `no case covers exported ${name}`);
  }
});

test("factory.createNode honors caller id and range (npm/bamti/unstable/ast/factory.d.ts:3)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const created = await factory.createNode(session, {
        path: "a.ts",
        nodeId: statement.id,
        id: CREATE_ID,
        range: { start: want.tokenStart, end: want.end },
      });
      assert.strictEqual(created.id, CREATE_ID);
      assert.deepStrictEqual(created.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(created.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(created.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(created.range.start, created.range.end), SOURCE);
    });
  });
});

test("factory.updateNode reuses the node when range is unchanged (npm/bamti/unstable/ast/factory.d.ts:4)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const updated = await factory.updateNode(session, {
        path: "a.ts",
        nodeId: statement.id,
        changedId: REUSE_ID,
        range: { start: want.tokenStart, end: want.end },
      });
      assert.strictEqual(updated.original, true);
      assert.strictEqual(updated.node.id, statement.id);
      assert.deepStrictEqual(updated.node.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(updated.node.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(updated.node.syntaxKind, WANT_SYNTAX_KIND);
    });
  });
});

test("factory.updateNode allocates the caller id when range changes (npm/bamti/unstable/ast/factory.d.ts:4)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const updated = await factory.updateNode(session, {
        path: "a.ts",
        nodeId: statement.id,
        changedId: CHANGE_ID,
        range: PREFIX_RANGE,
      });
      assert.strictEqual(updated.original, false);
      assert.strictEqual(updated.node.id, CHANGE_ID);
      assert.deepStrictEqual(updated.node.range, PREFIX_RANGE);
      assert.strictEqual(updated.node.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(updated.node.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(updated.node.range.start, updated.node.range.end), "c");
    });
  });
});

test("factory.asNode projects the unchanged node (npm/bamti/unstable/ast/factory.d.ts:5)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const node = await factory.asNode(session, {
        path: "a.ts",
        nodeId: statement.id,
        changedId: AS_ID,
        range: { start: want.tokenStart, end: want.end },
      });
      assert.strictEqual(node.id, statement.id);
      assert.deepStrictEqual(node.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(node.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(node.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(node.range.start, node.range.end), SOURCE);
    });
  });
});

test("factory.intoOwned resolves null when nothing changed (npm/bamti/unstable/ast/factory.d.ts:6)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const owned = await factory.intoOwned(session, {
        path: "a.ts",
        nodeId: statement.id,
        changedId: OWNED_SAME_ID,
        range: { start: want.tokenStart, end: want.end },
      });
      assert.strictEqual(owned, null);
    });
  });
});

test("factory.intoOwned resolves the changed node (npm/bamti/unstable/ast/factory.d.ts:6)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedWant(preorder, sf);
      const statement = await bamtiStatement(session, want);
      const owned = await factory.intoOwned(session, {
        path: "a.ts",
        nodeId: statement.id,
        changedId: OWNED_CHANGE_ID,
        range: PREFIX_RANGE,
      });
      assert.strictEqual(owned.id, OWNED_CHANGE_ID);
      assert.deepStrictEqual(owned.range, PREFIX_RANGE);
      assert.strictEqual(owned.nodeKind, WANT_NODE_KIND);
      assert.deepStrictEqual(owned.syntaxKind, WANT_SYNTAX_KIND);
      assert.strictEqual(SOURCE.slice(owned.range.start, owned.range.end), "c");
    });
  });
});
