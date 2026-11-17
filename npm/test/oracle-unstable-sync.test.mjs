import assert from "node:assert/strict";
import test from "node:test";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import {
  BROKEN_SOURCE,
  RICH_SOURCE,
  nonEmpty,
  pinnedAst,
  withPinnedSourceFile,
} from "./oracle-support.mjs";

const { DiagnosticCategory } = await import("typescript/unstable/sync");
const sync = await import("../bamti/unstable/sync.js");

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(npmRoot, "..", "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

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

function pinnedIdentifierPositions(sf) {
  const { SyntaxKind, visitEachChild } = pinnedAst;
  const positions = [];
  const record = (node) => {
    if (node.kind === SyntaxKind.Identifier) {
      positions.push({ position: node.getStart(sf), text: node.getText(sf) });
    }
    visitEachChild(node, record);
  };
  record(sf);
  return nonEmpty(positions, "pinned identifiers");
}

test("package shape: the sync subpath declares exactly createSerialService (bamti unstable/sync.js, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(sync).sort(), ["createSerialService"]);
});

test("createSerialService diagnostics equal the pinned sync API syntactic+semantic diagnostics on a broken source (projection: {start, end, severity}, message text excluded as clean-room wording)", async () => {
  const service = sync.createSerialService({ transportOptions: { binary: BINARY } });
  try {
    await service.open({ path: "a.ts", text: BROKEN_SOURCE, version: 1 });
    const bamtiDiags = await service.diagnostics({ path: "a.ts" });
    await withPinnedSourceFile(BROKEN_SOURCE, async ({ file, program }) => {
      const pinnedDiags = [
        ...program.getSyntacticDiagnostics(file),
        ...program.getSemanticDiagnostics(file),
      ];
      assert.ok(bamtiDiags.length > 0, "bamti reported no diagnostics for a broken source");
      assert.ok(pinnedDiags.length > 0, "pinned reported no diagnostics for a broken source");
      assert.deepStrictEqual(diagnosticProjection(bamtiDiags), pinnedDiagnosticProjection(pinnedDiags));
    });
  } finally {
    await service.dispose();
  }
});

test("createSerialService quickInfo names equal the pinned identifier token text at every pinned identifier position (projection: symbol name at the identifier start)", async () => {
  const service = sync.createSerialService({ transportOptions: { binary: BINARY } });
  try {
    await service.open({ path: "a.ts", text: RICH_SOURCE, version: 1 });
    await withPinnedSourceFile(RICH_SOURCE, async ({ sf }) => {
      for (const { position, text } of pinnedIdentifierPositions(sf)) {
        const info = await service.quickInfo({ path: "a.ts", position });
        assert.strictEqual(info === null ? null : info.name, text, `quickInfo name at ${position}`);
      }
    });
  } finally {
    await service.dispose();
  }
});

test("createSerialService queues through the session tail: concurrent dispatch reaches the transport strictly in request order, and each response echoes its own request (bamti sync.js contract, not an oracle comparison)", async () => {
  const calls = [];
  const transport = {
    ready: () => 0,
    request: (method, params) => {
      calls.push({ method, params });
      return Promise.resolve({ method, params });
    },
    dispose: () => Promise.resolve(),
  };
  const service = sync.createSerialService({ transport });
  const positions = [3, 7, 11];
  const dispatched = positions.map((position) => service.quickInfo({ path: "a.ts", position }));
  const answered = await Promise.all(dispatched);
  assert.deepStrictEqual(
    calls.map(({ method }) => method),
    ["service/quickInfo", "service/quickInfo", "service/quickInfo"],
  );
  assert.deepStrictEqual(calls.map(({ params }) => params.position), positions);
  answered.forEach((result, index) => {
    assert.deepStrictEqual(result, { method: "service/quickInfo", params: { path: "a.ts", position: positions[index] } });
  });
  await service.dispose();
});

test("createSerialService serializes concurrent dispatch: every queued response carries its own request's answer (projection: per-position identifier names)", async () => {
  const service = sync.createSerialService({ transportOptions: { binary: BINARY } });
  try {
    await service.open({ path: "a.ts", text: RICH_SOURCE, version: 1 });
    await withPinnedSourceFile(RICH_SOURCE, async ({ sf }) => {
      const probes = pinnedIdentifierPositions(sf).slice(0, 6);
      assert.ok(probes.length >= 2, "not enough pinned identifiers to prove serialization");
      const dispatched = probes.map(({ position }) => service.quickInfo({ path: "a.ts", position }));
      const answered = await Promise.all(dispatched);
      answered.forEach((info, index) => {
        assert.strictEqual(info === null ? null : info.name, probes[index].text, `queued response ${index}`);
      });
    });
  } finally {
    await service.dispose();
  }
});
