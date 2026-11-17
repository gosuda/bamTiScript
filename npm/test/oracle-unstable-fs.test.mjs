import assert from "node:assert/strict";
import { resolve } from "node:path";
import test from "node:test";

const fsModule = await import("../bamti/unstable/fs.js");
const pinnedFs = await import("typescript/unstable/fs");

test("package shape: ./unstable/fs declares exactly one operation (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(fsModule).sort(), ["osFileSystem"]);
});

test("fs.osFileSystem returns the frozen OS descriptor rooted at the resolved path", () => {
  const root = resolve("fixtures", "virtual-root");
  const descriptor = fsModule.osFileSystem(root);
  assert.deepStrictEqual(Object.keys(descriptor).sort(), ["kind", "root"]);
  assert.deepStrictEqual(
    { kind: descriptor.kind, root: descriptor.root },
    { kind: "os", root },
  );
  assert.ok(Object.isFrozen(descriptor));
});

test("fs.osFileSystem defaults its root to the process working directory", () => {
  const descriptor = fsModule.osFileSystem();
  assert.deepStrictEqual(
    { kind: descriptor.kind, root: descriptor.root },
    { kind: "os", root: resolve() },
  );
});

test("pinned counterpart note: typescript/unstable/fs exports only createVirtualFileSystem and fsCallbackNames; osFileSystem has no pinned counterpart, so its documented {kind, root} shape is asserted instead", () => {
  assert.deepStrictEqual(Object.keys(pinnedFs).sort(), [
    "createVirtualFileSystem",
    "fsCallbackNames",
  ]);
});
