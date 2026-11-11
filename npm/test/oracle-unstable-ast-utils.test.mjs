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
const utils = await import("../bamti/unstable/ast/utils.js");
const { API } = await import("typescript/unstable/sync");
const pinnedAst = await import("typescript/unstable/ast");
const { visitEachChild } = await import("typescript/unstable/ast/visitor");

const worktreeRoot = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const SOURCE = "const alpha = 1;";
const POSITION = 6;

const PINNED_TO_BAMTI_NODE_KIND = {
  SourceFile: "SourceFile",
  VariableStatement: "VariableDeclaration",
  VariableDeclaration: "VariableDeclarator",
  Identifier: "BindingIdentifier",
  NumericLiteral: "LiteralExpression",
};

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

function pinnedNarrowest(preorder, sf, position) {
  const mapped = preorder
    .map((node) => ({
      pinnedName: pinnedAst.formatSyntaxKind(node.kind),
      tokenStart: pinnedAst.getTokenPosOfNode(node, sf),
      end: node.end,
    }))
    .filter((row) => Object.hasOwn(PINNED_TO_BAMTI_NODE_KIND, row.pinnedName));
  let best = null;
  for (const row of mapped) {
    if (!(row.tokenStart <= position && position < row.end)) {
      continue;
    }
    if (best === null || row.end - row.tokenStart <= best.end - best.tokenStart) {
      best = row;
    }
  }
  return best;
}

test("utils subpath exports exactly five operations", () => {
  assert.deepStrictEqual(Object.keys(utils).sort(), [
    "containsPosition",
    "containsRange",
    "narrowestContaining",
    "nodeText",
    "textOfRange",
  ]);
});

test("utils.textOfRange slices the source text (npm/bamti/unstable/ast/utils.d.ts:3)", async () => {
  await withSession(SOURCE, async (session) => {
    const text = await utils.textOfRange(session, {
      path: "a.ts",
      range: { start: 6, end: 11 },
    });
    assert.strictEqual(text, "alpha");
    assert.strictEqual(text, SOURCE.slice(6, 11));
  });
});

test("utils.nodeText resolves the node source slice (npm/bamti/unstable/ast/utils.d.ts:4)", async () => {
  await withSession(SOURCE, async (session) => {
    const visitor = await import("../bamti/unstable/ast/visitor.js");
    const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
    const statement = visited.find((node) => node.nodeKind === "VariableDeclaration");
    const text = await utils.nodeText(session, { path: "a.ts", nodeId: statement.id });
    assert.strictEqual(text, SOURCE);
  });
});

test("utils.containsRange holds when bounds are equal (npm/bamti/unstable/ast/utils.d.ts:5)", async () => {
  await withSession(SOURCE, async (session) => {
    const contained = await utils.containsRange(session, {
      outer: { start: 0, end: 16 },
      inner: { start: 0, end: 16 },
    });
    assert.strictEqual(contained, true);
  });
});

test("utils.containsPosition is half-open at the end (npm/bamti/unstable/ast/utils.d.ts:6)", async () => {
  await withSession(SOURCE, async (session) => {
    const atEnd = await utils.containsPosition(session, {
      range: { start: 0, end: 16 },
      position: 16,
    });
    assert.strictEqual(atEnd, false);
  });
});

test("utils.narrowestContaining matches the pinned deepest node (npm/bamti/unstable/ast/utils.d.ts:7)", async () => {
  await withSession(SOURCE, async (session) => {
    await withPinnedSourceFile(SOURCE, async ({ sf, preorder }) => {
      const want = pinnedNarrowest(preorder, sf, POSITION);
      assert.ok(want);
      const node = await utils.narrowestContaining(session, { path: "a.ts", position: POSITION });
      assert.deepStrictEqual(node.range, { start: want.tokenStart, end: want.end });
      assert.strictEqual(node.nodeKind, PINNED_TO_BAMTI_NODE_KIND[want.pinnedName]);
      assert.deepStrictEqual(node.syntaxKind, { category: "node", kind: node.nodeKind });
    });
  });
});
