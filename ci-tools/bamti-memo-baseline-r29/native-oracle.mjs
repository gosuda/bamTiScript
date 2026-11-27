import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";

const source = resolve(process.argv[2]);
const metadata = JSON.parse(readFileSync(resolve(source, "node_modules/typescript/package.json"), "utf8"));
const compiler = resolve(source, "node_modules/.bin/tsc");
assert.equal(process.version, "v24.18.0");
assert.equal(metadata.version, "7.0.2");
const version = spawnSync(compiler, ["--version"], {
  cwd: source, encoding: "utf8", timeout: 120_000, maxBuffer: 8 * 1024 * 1024,
});
assert.equal(version.error, undefined);
assert.equal(version.signal, null);
assert.equal(version.status, 0);
assert.equal(version.stdout.trim(), "Version 7.0.2");
assert.equal(version.stderr.trim(), "");
console.log("TYPESCRIPT_MEMO_COMPILER " + JSON.stringify({
  path: compiler, version: version.stdout.trim(), raw_exit: version.status,
  entry_sha256: createHash("sha256").update(readFileSync(compiler)).digest("hex"),
}));
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
  try {
    const result = spawnSync(compiler, ["--pretty", "false", "--project", config], {
      cwd: source, encoding: "utf8", timeout: 120_000, maxBuffer: 8 * 1024 * 1024,
    });
    const stdout = result.stdout ?? "";
    const stderr = result.stderr ?? "";
    const actual = Array.from(stdout.matchAll(/\berror TS(\d+):/g), (match) => Number(match[1]));
    const diagnosticsMatch = JSON.stringify(actual) === JSON.stringify(expected);
    const positive = expected.length === 0;
    const statusMatches = positive ? result.status === 0 : [1, 2].includes(result.status);
    const sourceMatches = positive ? stdout.trim() === "" : stdout.includes(name + "(");
    const accepted = result.error === undefined && result.signal === null
      && stderr.trim() === "" && statusMatches && diagnosticsMatch && sourceMatches;
    console.log("TYPESCRIPT_MEMO_ORACLE " + JSON.stringify({
      id: name, node: process.version, typescript: metadata.version,
      adapter: "pinned native tsc CLI with no emit and a temporary project",
      source_sha256: createHash("sha256").update(text).digest("hex"),
      expected, actual, raw_exit: result.status, signal: result.signal,
      process_error: result.error?.message ?? null, accepted,
      stdout, stderr,
    }));
    if (!accepted) failures += 1;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}
assert.equal(failures, 0);
