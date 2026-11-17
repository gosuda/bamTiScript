import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");
const packageDir = join(npmRoot, "bamti");
const manifestPath = join(packageDir, "package.json");
const manifestBytes = readFileSync(manifestPath);
const manifest = JSON.parse(manifestBytes);

const SUBPATHS = [
  ".",
  "./package.json",
  "./unstable/ast",
  "./unstable/ast/clone",
  "./unstable/ast/factory",
  "./unstable/ast/is",
  "./unstable/ast/scanner",
  "./unstable/ast/utils",
  "./unstable/ast/visitor",
  "./unstable/async",
  "./unstable/fs",
  "./unstable/proto",
  "./unstable/sync",
];

test("package shape: the manifest declares exactly the thirteen export subpaths", () => {
  assert.deepStrictEqual(Object.keys(manifest.exports).sort(), [...SUBPATHS].sort());
});

test("the ./package.json export target is the manifest file itself, byte for byte", () => {
  const target = manifest.exports["./package.json"];
  assert.strictEqual(target, "./package.json");
  assert.deepStrictEqual(readFileSync(join(packageDir, target)), manifestBytes);
  assert.deepStrictEqual(JSON.parse(readFileSync(join(packageDir, target))), manifest);
});

for (const subpath of SUBPATHS) {
  test(`export ${subpath} points at files that exist in npm/bamti`, () => {
    const entry = manifest.exports[subpath];
    const targets = typeof entry === "string" ? [entry] : [entry.types, entry.import];
    for (const target of targets) {
      assert.ok(typeof target === "string" && target.startsWith("./"), `${subpath} target ${target} is not a relative path`);
      assert.ok(!target.includes(".."), `${subpath} target ${target} escapes the package`);
    }
    for (const target of targets) {
      const resolved = join(packageDir, target);
      assert.ok(statIsFile(resolved), `${subpath} target ${target} is not a file`);
    }
  });
}

function statIsFile(path) {
  try {
    return readFileSync(path).length >= 0;
  } catch {
    return false;
  }
}
