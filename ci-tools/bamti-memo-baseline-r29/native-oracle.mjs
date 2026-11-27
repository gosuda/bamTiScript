import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { basename, resolve } from "node:path";

const source = resolve(process.argv[2]);
const require = createRequire(resolve(source, "package.json"));
const ts = require("typescript");
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
  const options = {
    target: ts.ScriptTarget.ESNext,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    strict: true,
    noUncheckedIndexedAccess: true,
    noEmit: true,
  };
  const program = ts.createProgram([path], options);
  const diagnostics = ts.getPreEmitDiagnostics(program).map((diagnostic) => ({
    code: diagnostic.code,
    category: diagnostic.category,
    file: diagnostic.file ? basename(diagnostic.file.fileName) : null,
    start: diagnostic.start ?? null,
    length: diagnostic.length ?? null,
    message: ts.flattenDiagnosticMessageText(diagnostic.messageText, "\n"),
  }));
  const actual = diagnostics.map((diagnostic) => diagnostic.code);
  const accepted = JSON.stringify(actual) === JSON.stringify(expected);
  console.log("TYPESCRIPT_MEMO_ORACLE " + JSON.stringify({
    id: name, node: process.version, typescript: ts.version,
    source_sha256: createHash("sha256").update(text).digest("hex"),
    expected, actual, accepted, diagnostics,
  }));
  if (!accepted) failures += 1;
}
assert.equal(failures, 0);
