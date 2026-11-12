import assert from "node:assert/strict";
import fs from "node:fs";
import { registerHooks } from "node:module";
import os from "node:os";
import { dirname, join } from "node:path";
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
const { API } = await import("typescript/unstable/sync");
export const pinnedAst = await import("typescript/unstable/ast");
const { visitEachChild } = await import("typescript/unstable/ast/visitor");

const worktreeRoot = join(npmRoot, "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

export const SOURCE = "const alpha = 1;";

export const RICH_SOURCE = [
  "/** Leading JSDoc. */",
  "// line comment",
  'const café = "𝒳y";',
  "function outer(count) {",
  "  if (count > 0) {",
  "    return café.length + count;",
  "  }",
  "  return 0;",
  "}",
  "outer(2);",
  "",
].join("\r\n");

export const NESTED_SOURCE = "function outer() {\n  if (0) {\n    this.length;\n  }\n}\n";

export const CLASS_SOURCE = "class C { #x; m() { this.#x; } }";

export const BROKEN_SOURCE = 'let text = "unterminated;\r\n';

export function pinnedRange(node, sf) {
  return { start: node.getStart(sf), end: node.end };
}

export function nonEmpty(collection, what) {
  assert.ok(collection.length > 0, `${what} is empty`);
  return collection;
}

export function pinnedPreorder(root, sf) {
  const preorder = [];
  const record = (node) => {
    if (node !== sf.endOfFileToken) {
      preorder.push(node);
    }
    return visitEachChild(node, record);
  };
  record(root);
  return nonEmpty(preorder, "pinned preorder");
}

export function pinnedRanges(preorder, sf) {
  return preorder.map((node) => pinnedRange(node, sf));
}

export function bamtiRanges(visited) {
  return nonEmpty(visited, "bamti nodes").map(({ range }) => ({ start: range.start, end: range.end }));
}

export function ancestorsOrSelf(node) {
  const chain = [];
  for (let current = node; current !== undefined; current = current.parent) {
    chain.push(current);
  }
  return chain;
}

export async function withSession(text, fn) {
  const session = createSession({ transportOptions: { binary: BINARY } });
  try {
    await session.open({ path: "a.ts", text, version: 1 });
    await fn(session);
  } finally {
    await session.dispose();
  }
}

export async function withPinnedSourceFile(text, fn) {
  const dir = fs.mkdtempSync(join(os.tmpdir(), "bamti-pinned-"));
  const file = join(dir, "a.ts");
  fs.writeFileSync(file, text);
  fs.writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: {}, files: ["a.ts"] }));
  const api = new API({});
  const snap = api.updateSnapshot({ openProjects: [join(dir, "tsconfig.json")] });
  try {
    const project = snap.getProject(join(dir, "tsconfig.json"));
    assert.ok(project);
    const sf = project.program.getSourceFile(file);
    assert.ok(sf);
    await fn({ sf, file, program: project.program, preorder: pinnedPreorder(sf, sf) });
  } finally {
    snap.dispose();
    api.close();
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

const rangeKey = ({ start, end }) => `${start}:${end}`;

export function pairByUniqueRange(visited, preorder, sf) {
  const count = (keys) => keys.reduce((counts, key) => counts.set(key, (counts.get(key) ?? 0) + 1), new Map());
  const bamtiCounts = count(visited.map(({ range }) => rangeKey(range)));
  const pinnedCounts = count(preorder.map((node) => rangeKey(pinnedRange(node, sf))));
  const pairs = [];
  for (const pinned of preorder) {
    const key = rangeKey(pinnedRange(pinned, sf));
    if (pinnedCounts.get(key) === 1 && bamtiCounts.get(key) === 1) {
      pairs.push({ pinned, bamti: visited.find(({ range }) => rangeKey(range) === key) });
    }
  }
  return nonEmpty(pairs, "nodes with a range unique on both sides");
}

export async function withVisited(text, fn) {
  const visitor = await import("../bamti/unstable/ast/visitor.js");
  await withSession(text, async (session) => {
    await withPinnedSourceFile(text, async ({ sf, preorder }) => {
      const visited = await visitor.visitSourceFile(session, { path: "a.ts" });
      await fn({ session, sf, preorder, visited });
    });
  });
}
