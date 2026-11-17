import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { BROKEN_SOURCE, withPinnedSourceFile, withSession } from "./oracle-support.mjs";

const { DiagnosticCategory } = await import("typescript/unstable/sync");
const pinnedRoot = await import("typescript");
const bamti = await import("../bamti/index.js");

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(npmRoot, "..", "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const ROOT_NAMES = [
  "ArtifactNotFoundError",
  "BamtiError",
  "DisposedError",
  "NATIVE_TARGETS",
  "NativeArtifactLoadError",
  "NativeArtifactNotFoundError",
  "ProtocolError",
  "RestartLimitError",
  "ServiceRequestError",
  "Session",
  "Transport",
  "TransportBusyError",
  "TransportCrashError",
  "UnsupportedPlatformError",
  "artifactPackage",
  "createSession",
  "loadNativeAddon",
  "resolveArtifact",
  "resolveBinary",
  "run",
  "runNative",
  "selectNativeTarget",
];

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

test("package shape: the root export declares exactly the documented names (bamti index.js, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(bamti).sort(), ROOT_NAMES);
});

test("the pinned typescript root export carries only version data, so root names other than the service surface have no pinned counterpart", () => {
  assert.deepStrictEqual(
    Object.keys(pinnedRoot)
      .filter((name) => name !== "default" && name !== "module.exports")
      .sort(),
    ["version", "versionMajorMinor"],
  );
  const pinnedManifest = JSON.parse(readFileSync(join(npmRoot, "..", "node_modules", "typescript", "package.json"), "utf8"));
  assert.strictEqual(pinnedRoot.version, pinnedManifest.version);
  assert.strictEqual(pinnedRoot.versionMajorMinor, pinnedManifest.version.slice(0, pinnedManifest.version.lastIndexOf(".")));
});

test("Session.diagnostics equals the pinned sync API syntactic+semantic diagnostics on a broken source (projection: {start, end, severity}, message text excluded as clean-room wording)", async () => {
  await withSession(BROKEN_SOURCE, async (session) => {
    await withPinnedSourceFile(BROKEN_SOURCE, async ({ file, program }) => {
      const bamtiDiags = await session.diagnostics({ path: "a.ts" });
      const pinnedDiags = [
        ...program.getSyntacticDiagnostics(file),
        ...program.getSemanticDiagnostics(file),
      ];
      assert.ok(bamtiDiags.length > 0, "bamti reported no diagnostics for a broken source");
      assert.ok(pinnedDiags.length > 0, "pinned reported no diagnostics for a broken source");
      assert.deepStrictEqual(diagnosticProjection(bamtiDiags), pinnedDiagnosticProjection(pinnedDiags));
    });
  });
});

test("createSession returns a Session whose dispose completes (documented shape; the diagnostics oracle above covers the session surface)", async () => {
  const session = bamti.createSession({ transportOptions: { binary: BINARY } });
  assert.ok(session instanceof bamti.Session);
  await session.dispose();
});

test("Session exposes exactly the ten service operations plus request and dispose (documented Service interface)", () => {
  const session = bamti.createSession({ transportOptions: { binary: BINARY } });
  assert.deepStrictEqual(
    Object.keys(session).filter((key) => key !== "transport" && key !== "initializeParams").sort(),
    ["close", "completions", "definition", "diagnostics", "open", "quickInfo", "references", "rename", "snapshot", "update"],
  );
  return session.dispose();
});

test("artifactPackage maps the documented platform/arch pairs to the @bamti/cli package names", () => {
  assert.strictEqual(bamti.artifactPackage("linux", "x64"), "@bamti/cli-linux-x64");
  assert.strictEqual(bamti.artifactPackage("linux", "arm64"), "@bamti/cli-linux-arm64");
  assert.strictEqual(bamti.artifactPackage("darwin", "x64"), "@bamti/cli-darwin-x64");
  assert.strictEqual(bamti.artifactPackage("darwin", "arm64"), "@bamti/cli-darwin-arm64");
  assert.strictEqual(bamti.artifactPackage("win32", "x64"), "@bamti/cli-win32-x64");
  assert.throws(() => bamti.artifactPackage("sunos", "x64"), { name: "UnsupportedPlatformError" });
});

test("NATIVE_TARGETS rows agree with the manifest optionalDependencies package names", () => {
  const bamtiManifest = JSON.parse(readFileSync(join(npmRoot, "bamti", "package.json"), "utf8"));
  assert.strictEqual(bamti.NATIVE_TARGETS.length, 5);
  for (const row of bamti.NATIVE_TARGETS) {
    for (const key of ["selector", "target", "package", "entry", "os", "cpu", "artifactKind"]) {
      assert.strictEqual(typeof row[key], "string", `target ${row.selector} lacks ${key}`);
    }
  }
  assert.deepStrictEqual(
    bamti.NATIVE_TARGETS.map((row) => row.package).sort(),
    Object.keys(bamtiManifest.optionalDependencies).sort(),
  );
});

test("selectNativeTarget returns the matching NATIVE_TARGETS row and rejects unsupported hosts", () => {
  assert.deepStrictEqual(
    bamti.selectNativeTarget({ platform: "linux", arch: "x64", libc: "glibc" }),
    bamti.NATIVE_TARGETS[0],
  );
  assert.deepStrictEqual(
    bamti.selectNativeTarget({ platform: "darwin", arch: "arm64" }),
    bamti.NATIVE_TARGETS[3],
  );
  assert.throws(() => bamti.selectNativeTarget({ platform: "linux", arch: "x64" }), bamti.UnsupportedPlatformError);
  assert.throws(() => bamti.selectNativeTarget({ platform: "sunos", arch: "x64" }), bamti.UnsupportedPlatformError);
});

test("resolveArtifact is the same binding as resolveBinary (documented alias)", () => {
  assert.strictEqual(bamti.resolveArtifact, bamti.resolveBinary);
  assert.strictEqual(typeof bamti.resolveBinary, "function");
});

for (const [name, build, fields] of [
  ["BamtiError", () => new bamti.BamtiError("boom"), {}],
  ["ProtocolError", () => new bamti.ProtocolError("bad frame"), {}],
  ["DisposedError", () => new bamti.DisposedError("session"), {}],
  ["TransportBusyError", () => new bamti.TransportBusyError(1, 2), { inFlight: 1, maxInFlight: 2 }],
  ["TransportCrashError", () => new bamti.TransportCrashError({ code: 9, signal: null, stderr: "died" }), { code: 9, signal: null, stderr: "died" }],
  ["RestartLimitError", () => new bamti.RestartLimitError(3, 2), { restarts: 3, maxRestarts: 2 }],
  ["ServiceRequestError", () => new bamti.ServiceRequestError("service/open", { code: "E_X", message: "m" }), { method: "service/open", code: "E_X" }],
  ["UnsupportedPlatformError", () => new bamti.UnsupportedPlatformError("sunos", "x64"), {}],
  ["NativeArtifactNotFoundError", () => new bamti.NativeArtifactNotFoundError("@bamti/bamti-linux-x64-gnu", "0.2.0"), {}],
  ["NativeArtifactLoadError", () => new bamti.NativeArtifactLoadError("corrupt", new Error("sha")), {}],
]) {
  test(`${name} constructs with its documented signature and chains from BamtiError where declared (no pinned counterpart: pinned root export is version data only)`, () => {
    const error = build();
    assert.ok(error instanceof Error, `${name} is not an Error`);
    assert.strictEqual(error.name, name);
    for (const [key, value] of Object.entries(fields)) {
      assert.deepStrictEqual(error[key], value, `${name}.${key}`);
    }
    const bamtiErrorNames = ["BamtiError", "ProtocolError", "DisposedError", "TransportBusyError", "TransportCrashError", "RestartLimitError", "ServiceRequestError"];
    assert.strictEqual(
      error instanceof bamti.BamtiError,
      bamtiErrorNames.includes(name),
      `${name} BamtiError membership`,
    );
  });
}

test("Transport constructs without spawning and reports a clean disposed state after dispose (documented shape; transport protocol has no pinned counterpart)", async () => {
  const transport = new bamti.Transport({ binary: BINARY, maxRestarts: 0 });
  assert.strictEqual(transport.disposed, false);
  assert.strictEqual(transport.inFlight, 0);
  await transport.dispose();
  assert.strictEqual(transport.disposed, true);
});

test("run and runNative and loadNativeAddon are functions of the documented arity shape (not invoked: they require packaged artifacts absent from the source tree)", () => {
  assert.strictEqual(typeof bamti.run, "function");
  assert.strictEqual(bamti.run.length <= 2, true);
  assert.strictEqual(typeof bamti.runNative, "function");
  assert.strictEqual(bamti.runNative.length, 1);
  assert.strictEqual(typeof bamti.loadNativeAddon, "function");
});
