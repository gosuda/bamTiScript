import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { access, readFile } from "node:fs/promises";
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
const pkgPath = join(npmRoot, "bamti", "package.json");
const pkg = JSON.parse(await readFile(pkgPath, "utf8"));

const EXPECTED_EXPORTS = [
  ".",
  "./unstable/sync",
  "./unstable/async",
  "./unstable/fs",
  "./unstable/proto",
  "./unstable/ast",
  "./unstable/ast/is",
  "./unstable/ast/factory",
  "./unstable/ast/utils",
  "./unstable/ast/scanner",
  "./unstable/ast/visitor",
  "./unstable/ast/clone",
  "./package.json",
];

test("manifest has 13 exports", () => {
  const keys = Object.keys(pkg.exports);
  assert.equal(keys.length, 13, `expected 13 exports, got ${keys.length}: ${keys.join(", ")}`);
});

for (const sub of EXPECTED_EXPORTS) {
  test(`export ${sub} exists`, () => {
    assert.ok(pkg.exports[sub], `missing export ${sub}`);
  });
}

test("bin.tsc points to native-runner.js", () => {
  assert.equal(pkg.bin?.tsc, "native-runner.js");
});

test("name is bamti", () => assert.equal(pkg.name, "bamti"));
test("type is module", () => assert.equal(pkg.type, "module"));
test("engines.node >=24", () => {
  assert.ok(pkg.engines?.node?.includes("24"), `engines.node=${pkg.engines?.node}`);
});

const mod = await import("../bamti/index.js");

test("Session exported", () => assert.ok(typeof mod.Session === "function"));
test("createSession exported", () => assert.ok(typeof mod.createSession === "function"));
test("Transport exported", () => assert.ok(typeof mod.Transport === "function"));
test("run exported", () => assert.ok(typeof mod.run === "function"));
test("runNative exported", () => assert.ok(typeof mod.runNative === "function"));
test("BamtiError exported", () => assert.ok(mod.BamtiError));
test("DisposedError exported", () => assert.ok(mod.DisposedError));
test("ProtocolError exported", () => assert.ok(mod.ProtocolError));
test("TransportBusyError exported", () => assert.ok(mod.TransportBusyError));
test("TransportCrashError exported", () => assert.ok(mod.TransportCrashError));
test("loadNativeAddon exported", () => assert.ok(typeof mod.loadNativeAddon === "function"));
test("selectNativeTarget exported", () => assert.ok(typeof mod.selectNativeTarget === "function"));
test("NativeArtifactLoadError exported", () => assert.ok(mod.NativeArtifactLoadError));
test("NativeArtifactNotFoundError exported", () => assert.ok(mod.NativeArtifactNotFoundError));
test("UnsupportedPlatformError exported", () => assert.ok(mod.UnsupportedPlatformError));
test("ArtifactNotFoundError exported", () => assert.ok(mod.ArtifactNotFoundError));
test("artifactPackage exported", () => assert.ok(typeof mod.artifactPackage === "function"));
test("resolveBinary exported", () => assert.ok(typeof mod.resolveBinary === "function"));

test("package.json self-import works", async () => {
  const pkgMod = await import("../bamti/package.json", { with: { type: "json" } });
  assert.equal(pkgMod.default.name, "bamti");
});

test("internal/errors.js exists", async () => {
  await access(join(npmRoot, "bamti", "internal", "errors.js"));
});
test("internal/framing.js exists", async () => {
  await access(join(npmRoot, "bamti", "internal", "framing.js"));
});
test("internal/session.js exists", async () => {
  await access(join(npmRoot, "bamti", "internal", "session.js"));
});
test("internal/transport.js exists", async () => {
  await access(join(npmRoot, "bamti", "internal", "transport.js"));
});

test("native-runner.js exists", () => {
  assert.ok(existsSync(join(npmRoot, "bamti", "native-runner.js")));
});
test("native-loader.js exists", () => {
  assert.ok(existsSync(join(npmRoot, "bamti", "native-loader.js")));
});

const CLI = process.env.BAMTS_CLI ?? join(process.env.HOME, ".cache", "bamts-main-target", "release", "bamts");
test("prebuilt CLI --version succeeds", () => {
  const r = spawnSync(CLI, ["--version"], { encoding: "utf8", timeout: 10000 });
  assert.equal(r.status, 0, `exit ${r.status}, stderr=${r.stderr}`);
  assert.ok(r.stdout.trim().length > 0, `stdout empty`);
});
