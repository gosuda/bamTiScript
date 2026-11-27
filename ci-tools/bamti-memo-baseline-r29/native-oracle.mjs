import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { basename, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const source = resolve(process.argv[2]);
const require = createRequire(resolve(source, "package.json"));
const ts = require("typescript");
const apiPath = require.resolve("typescript/unstable/sync");
const { API } = await import(pathToFileURL(apiPath).href);
assert.equal(process.version, "v24.18.0");
assert.equal(ts.version, "7.0.2");
const cases = [
  ["relation_memo_saturation.ts", []],
  ["relation_memo_saturation_invalid.ts", [2322]],
];
let failures = 0;
for (const [name, expected] of cases) {
  const path = resolve(source, "crates/bamts-compiler/src/checker/fixtures", name);
  const text = readFileSync(path, "utf8");
  const directory = mkdtempSync(join(process.env.RUNNER_TEMP, "bamti-memo-oracle-"));
  const config = join(directory, "tsconfig.json");
  writeFileSync(config, JSON.stringify({
    compilerOptions: {
      target: "ESNext",
      module: "NodeNext",
      moduleResolution: "NodeNext",
      strict: true,
      noUncheckedIndexedAccess: true,
      noEmit: true,
    },
    files: [path],
  }));
  const api = new API({});
  let snapshot;
  try {
    snapshot = api.updateSnapshot({ openProjects: [config] });
    const project = snapshot.getProject(config);
    assert.ok(project, "the pinned native API must open the exact project");
    const diagnostics = [
      ...project.getSyntacticDiagnostics(),
      ...project.getSemanticDiagnostics(),
    ].map((diagnostic) => ({
      code: diagnostic.code,
      category: diagnostic.category,
      file: diagnostic.fileName ? basename(diagnostic.fileName) : null,
      start: diagnostic.pos ?? null,
      end: diagnostic.end ?? null,
      message: diagnostic.text,
    }));
    const actual = diagnostics.map((diagnostic) => diagnostic.code);
    const accepted = JSON.stringify(actual) === JSON.stringify(expected);
    console.log("TYPESCRIPT_MEMO_ORACLE " + JSON.stringify({
      id: name, node: process.version, typescript: ts.version,
      adapter: "typescript/unstable/sync",
      api_module_sha256: createHash("sha256").update(readFileSync(apiPath)).digest("hex"),
      source_sha256: createHash("sha256").update(text).digest("hex"),
      expected, actual, accepted, diagnostics,
    }));
    if (!accepted) failures += 1;
  } finally {
    snapshot?.dispose();
    api.close();
    rmSync(directory, { recursive: true, force: true });
  }
}
assert.equal(failures, 0);
