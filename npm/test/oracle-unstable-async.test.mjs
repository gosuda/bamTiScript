import assert from "node:assert/strict";
import test from "node:test";
import fs from "node:fs";
import os from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { BROKEN_SOURCE, SOURCE } from "./oracle-support.mjs";

const { API: PinnedAsyncAPI, DiagnosticCategory } = await import("typescript/unstable/async");
const asyncModule = await import("../bamti/unstable/async.js");
const bamtiRoot = await import("../bamti/index.js");

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(npmRoot, "..", "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

async function withPinnedAsyncSourceFile(text, fn) {
  const dir = fs.mkdtempSync(join(os.tmpdir(), "bamti-pinned-async-"));
  const file = join(dir, "a.ts");
  fs.writeFileSync(file, text);
  fs.writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: {}, files: ["a.ts"] }));
  const api = new PinnedAsyncAPI({});
  const snapshot = await api.updateSnapshot({ openProjects: [join(dir, "tsconfig.json")] });
  try {
    const project = snapshot.getProject(join(dir, "tsconfig.json"));
    assert.ok(project);
    const sf = await project.program.getSourceFile(file);
    assert.ok(sf);
    await fn({ file, program: project.program });
  } finally {
    await snapshot.dispose();
    await api.close();
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

// bamti lint warnings (the default lint profile) have no counterpart in the pinned
// syntactic and semantic calls, so only errors are compared.
function diagnosticProjection(diagnostics) {
  return diagnostics
    .filter(({ severity }) => severity === "error")
    .map(({ range, severity }) => ({ start: range.start, end: range.end, severity }))
    .sort((left, right) => left.start - right.start || left.end - right.end);
}

function pinnedDiagnosticProjection(diagnostics) {
  return diagnostics
    .filter((d) => d.category === DiagnosticCategory.Error || d.category === DiagnosticCategory.Warning)
    .map((d) => ({
      start: d.pos,
      end: d.end,
      severity: d.category === DiagnosticCategory.Error ? "error" : "warning",
    }))
    .sort((left, right) => left.start - right.start || left.end - right.end);
}

async function compareDiagnosticsAgainstPinnedAsync(text, serviceMethod) {
  const service = serviceMethod();
  try {
    await service.open({ path: "a.ts", text, version: 1 });
    const bamtiDiags = await service.diagnostics({ path: "a.ts" });
    await withPinnedAsyncSourceFile(text, async ({ file, program }) => {
      const pinnedDiags = [
        ...(await program.getSyntacticDiagnostics(file)),
        ...(await program.getSemanticDiagnostics(file)),
      ];
      assert.ok(bamtiDiags.length > 0, "bamti reported no diagnostics for a broken source");
      assert.ok(pinnedDiags.length > 0, "pinned reported no diagnostics for a broken source");
      assert.deepStrictEqual(diagnosticProjection(bamtiDiags), pinnedDiagnosticProjection(pinnedDiags));
    });
  } finally {
    await service.dispose();
  }
}

test("package shape: the async subpath declares exactly Session, createAsyncService, createSession (bamti unstable/async.js, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(asyncModule).sort(), ["Session", "createAsyncService", "createSession"]);
});

test("Session and createSession are the same bindings the root export carries (re-export identity, not an oracle comparison)", () => {
  assert.strictEqual(asyncModule.Session, bamtiRoot.Session);
  assert.strictEqual(asyncModule.createSession, bamtiRoot.createSession);
});

test("createAsyncService diagnostics equal the pinned async API syntactic+semantic diagnostics on a broken source (projection: {start, end, severity}, message text excluded as clean-room wording)", async () => {
  await compareDiagnosticsAgainstPinnedAsync(BROKEN_SOURCE, () =>
    asyncModule.createAsyncService({ transportOptions: { binary: BINARY } }),
  );
});

test("createAsyncService open returns the documented DocumentSnapshot for a fixed TypeScript source (projection: {path, version, open}; the service resolves the path against its working directory)", async () => {
  const service = asyncModule.createAsyncService({ transportOptions: { binary: BINARY } });
  try {
    const snapshot = await service.open({ path: "a.ts", text: SOURCE, version: 1 });
    assert.deepStrictEqual(snapshot, { path: resolve("a.ts"), version: 1, open: true });
  } finally {
    await service.dispose();
  }
});

test("createAsyncService stamps async: true onto every service call and addresses the service/<operation> methods (bamti async.js contract, not an oracle comparison)", async () => {
  const calls = [];
  const transport = {
    ready: () => 0,
    request: (method, params) => {
      calls.push({ method, params });
      return Promise.resolve({});
    },
    dispose: () => Promise.resolve(),
  };
  const service = asyncModule.createAsyncService({ transport });
  await service.diagnostics({ path: "a.ts" });
  await service.quickInfo({ path: "a.ts", position: 4 });
  assert.deepStrictEqual(calls, [
    { method: "service/diagnostics", params: { path: "a.ts", async: true } },
    { method: "service/quickInfo", params: { path: "a.ts", position: 4, async: true } },
  ]);
  await service.dispose();
});

test("Session from the async subpath equals the pinned async API diagnostics on a broken source (projection: {start, end, severity}, message text excluded as clean-room wording)", async () => {
  await compareDiagnosticsAgainstPinnedAsync(BROKEN_SOURCE, () =>
    new asyncModule.Session({ transportOptions: { binary: BINARY } }),
  );
});

test("createSession returns a Session instance and disposes cleanly (documented shape; no pinned counterpart for the session factory)", async () => {
  const session = asyncModule.createSession({ transportOptions: { binary: BINARY } });
  assert.ok(session instanceof asyncModule.Session);
  await session.dispose();
});
