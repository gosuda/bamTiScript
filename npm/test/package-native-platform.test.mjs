import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import {
  chmod,
  copyFile as fsCopyFile,
  cp,
  mkdir,
  mkdtemp,
  readFile,
  rm,
  writeFile,
} from "node:fs/promises";
import { dirname, join, resolve, delimiter } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import test from "node:test";

import {
  assembleNativeRecords,
  packageNativeTarget,
} from "../scripts/package-native-platform.mjs";
import { NATIVE_TARGETS } from "../bamti/native-loader.js";
import {
  createNativeBuildPlan,
  NATIVE_RELEASE_TARGETS,
} from "../scripts/native-build-plan.mjs";

const npmRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const packagingScript = join(npmRoot, "scripts", "package-native-platform.mjs");
const SOURCE_COMMIT = "a".repeat(40);
const PROVENANCE = Object.freeze({
  cargoLockSha256: "b".repeat(64),
  workflowRevision: "native-release-build-v1",
  toolchain: "rustc 1.97.1",
  builderRevision: "package-native-platform-v1",
});
const BUILD_SET_ID = createNativeBuildPlan({
  sourceCommit: SOURCE_COMMIT,
  sourceVersion: "0.2.0",
  ...PROVENANCE,
  targets: NATIVE_RELEASE_TARGETS,
}).buildSetId;
const RUNNERS = new Map([
  ["linux-x64-gnu", "depot-ubuntu-24.04"],
  ["linux-arm64-gnu", "depot-ubuntu-24.04-arm"],
  ["darwin-x64", "depot-macos-latest"],
  ["darwin-arm64", "depot-macos-latest"],
  ["win32-x64-msvc", "depot-windows-2025-4"],
]);

function packageOptions(overrides = {}) {
  return {
    buildSetId: BUILD_SET_ID,
    sourceCommit: SOURCE_COMMIT,
    ...PROVENANCE,
    ...overrides,
  };
}

async function withTemporaryDirectory(callback) {
  const directory = await mkdtemp(join(tmpdir(), "bamti-native-test-"));
  try {
    return await callback(directory);
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
}

async function writeJson(path, value) {
  await writeFile(path, `${JSON.stringify(value, null, 2)}\n`);
}

async function readJson(path) {
  return JSON.parse(await readFile(path, "utf8"));
}

function makeRecord(selector, overrides = {}) {
  const fixed = NATIVE_TARGETS.find(({ selector: s }) => s === selector);
  const version = "0.2.0";
  const sourceCommit = SOURCE_COMMIT;
  const buildSetId = BUILD_SET_ID;
  const nativeAbi = 1;
  const cliProtocol = 1;
  const release = {
    packageVersion: version,
    sourceCommit,
    nativeAbi,
    cliProtocol,
    buildSetId,
    releaseId: `bamti/${version}/${sourceCommit}/native-abi-${nativeAbi}/cli-protocol-${cliProtocol}/${buildSetId}`,
  };
  const content = `fake ${selector}`;
  const sha256 = createHash("sha256").update(content).digest("hex");
  return {
    selector: fixed.selector,
    target: fixed.target,
    package: fixed.package,
    entry: fixed.entry,
    os: fixed.os,
    cpu: fixed.cpu,
    libc: fixed.libc,
    artifactKind: fixed.artifactKind,
    version,
    sha256,
    runner: RUNNERS.get(selector),
    ...PROVENANCE,
    release,
    ...overrides,
  };
}

async function writeRecords(directory, mutator) {
  const records = [];
  for (const { selector } of NATIVE_TARGETS) {
    const record = makeRecord(selector);
    if (mutator) {
      mutator(record, selector);
    }
    const path = join(directory, `bamti-${selector}-${record.version}.json`);
    await writeJson(path, record);
    records.push({ path, record });
  }
  return records;
}

function packageNameToTarballName(packageName, version) {
  return `${packageName.replace(/^@/, "").replace(/\//g, "-")}-${version}.tgz`;
}

test("packageNativeTarget builds the target once", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-unknown-linux-gnu", "release");
    await mkdir(releaseDir, { recursive: true });
    await writeFile(join(releaseDir, "libbamts_napi.so"), "fake addon\n");

    let cargoCalls = 0;
    let npmCalls = 0;

    const { record } = await packageNativeTarget("x86_64-unknown-linux-gnu", {
      ...packageOptions(),
      outputDirectory: output,
      env: { CARGO_TARGET_DIR: cargoTarget },
      runCargo: ({ args, env, cwd }) => {
        cargoCalls += 1;
        assert.deepEqual(args, [
          "build",
          "--release",
          "--locked",
          "--package",
          "bamts-napi",
          "--target",
          "x86_64-unknown-linux-gnu",
        ]);
        assert.equal(env.BAMTI_BUILD_SET_ID, BUILD_SET_ID);
        assert.equal(env.BAMTI_RELEASE_PACKAGE_VERSION, "0.2.0");
        assert.equal(env.BAMTI_SOURCE_COMMIT, SOURCE_COMMIT);
        assert.equal(env.BAMTI_CARGO_LOCK_SHA256, PROVENANCE.cargoLockSha256);
        assert.equal(env.BAMTI_WORKFLOW_REVISION, PROVENANCE.workflowRevision);
        assert.equal(env.BAMTI_TOOLCHAIN, PROVENANCE.toolchain);
        assert.equal(env.BAMTI_BUILDER_REVISION, PROVENANCE.builderRevision);
      },
      runNpm: ({ args }) => {
        npmCalls += 1;
        assert.deepEqual(args, ["pack", "--pack-destination", output]);
      },
    });

    assert.equal(cargoCalls, 1);
    assert.equal(npmCalls, 1);
    assert.equal(record.version, "0.2.0");
    assert.equal(record.package, "@bamti/bamti-linux-x64-gnu");
    assert.equal(record.runner, "depot-ubuntu-24.04");
  });
});

test("packageNativeTarget emits correct record and artifact metadata", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-unknown-linux-gnu", "release");
    await mkdir(releaseDir, { recursive: true });
    const addon = Buffer.from("fake addon for linux x64\n");
    await writeFile(join(releaseDir, "libbamts_napi.so"), addon);

    const inspectDir = join(temp, "inspect");

    const { record, recordPath, tarballPath } = await packageNativeTarget(
      "x86_64-unknown-linux-gnu",
      {
        ...packageOptions(),
        outputDirectory: output,
        env: { CARGO_TARGET_DIR: cargoTarget },
        runCargo: () => {},
        runNpm: async ({ args, cwd }) => {
          assert.deepEqual(args, ["pack", "--pack-destination", output]);
          await cp(cwd, inspectDir, { recursive: true });
          await writeFile(
            join(output, packageNameToTarballName("@bamti/bamti-linux-x64-gnu", "0.2.0")),
            "",
          );
        },
      },
    );

    const expectedSha256 = createHash("sha256").update(addon).digest("hex");
    assert.equal(record.sha256, expectedSha256);
    assert.equal(record.version, "0.2.0");
    assert.equal(record.package, "@bamti/bamti-linux-x64-gnu");
    assert.equal(record.target, "x86_64-unknown-linux-gnu");
    assert.equal(record.entry, "bamti.linux-x64-gnu.node");
    assert.equal(record.os, "linux");
    assert.equal(record.cpu, "x64");
    assert.equal(record.libc, "glibc");
    assert.equal(record.artifactKind, "native-addon");
    assert.equal(record.runner, "depot-ubuntu-24.04");
    assert.equal(record.release.packageVersion, "0.2.0");
    assert.equal(record.release.sourceCommit, SOURCE_COMMIT);
    assert.equal(record.release.nativeAbi, 1);
    assert.equal(record.release.cliProtocol, 1);
    assert.equal(record.release.buildSetId, BUILD_SET_ID);
    assert.equal(
      record.release.releaseId,
      `bamti/0.2.0/${SOURCE_COMMIT}/native-abi-1/cli-protocol-1/${BUILD_SET_ID}`,
    );

    const storedRecord = await readJson(recordPath);
    assert.deepEqual(storedRecord, record);

    assert.equal(
      tarballPath,
      join(output, "bamti-bamti-linux-x64-gnu-0.2.0.tgz"),
    );

    const manifest = await readJson(join(inspectDir, "package.json"));
    assert.equal(manifest.name, "@bamti/bamti-linux-x64-gnu");
    assert.equal(manifest.version, "0.2.0");
    assert.equal(manifest.type, "commonjs");
    assert.equal(manifest.main, "bamti.linux-x64-gnu.node");
    assert.deepEqual(manifest.files, ["bamti.linux-x64-gnu.node"]);
    assert.equal(manifest.engines.node, ">=24");
    assert.deepEqual(manifest.os, ["linux"]);
    assert.deepEqual(manifest.cpu, ["x64"]);
    assert.deepEqual(manifest.libc, ["glibc"]);
    assert.equal(manifest.bamtiNative.entry, "bamti.linux-x64-gnu.node");
    assert.equal(manifest.bamtiNative.target, "x86_64-unknown-linux-gnu");
    assert.equal(manifest.bamtiNative.artifactKind, "native-addon");
    assert.equal(manifest.bamtiNative.sha256, expectedSha256);
    assert.equal(manifest.bamtiNative.release.packageVersion, "0.2.0");
    assert.equal(manifest.bamtiNative.release.sourceCommit, SOURCE_COMMIT);
    assert.equal(manifest.bamtiNative.release.nativeAbi, 1);
    assert.equal(manifest.bamtiNative.release.cliProtocol, 1);
    assert.equal(manifest.bamtiNative.release.buildSetId, BUILD_SET_ID);
    assert.equal(
      manifest.bamtiNative.release.releaseId,
      `bamti/0.2.0/${SOURCE_COMMIT}/native-abi-1/cli-protocol-1/${BUILD_SET_ID}`,
    );

    const copiedAddon = await readFile(join(inspectDir, "bamti.linux-x64-gnu.node"));
    const stagedHash = createHash("sha256").update(copiedAddon).digest("hex");
    assert.equal(record.sha256, stagedHash);
    assert.equal(manifest.bamtiNative.sha256, stagedHash);
    assert.deepEqual(copiedAddon, addon);
  });
});

test("packageNativeTarget hashes staged addon bytes after source mutation", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-unknown-linux-gnu", "release");
    await mkdir(releaseDir, { recursive: true });
    const original = Buffer.from("original addon bytes\n");
    const mutated = Buffer.from("mutated addon bytes\n");
    const source = join(releaseDir, "libbamts_napi.so");
    await writeFile(source, original);

    const inspectDir = join(temp, "inspect");

    const { record, recordPath } = await packageNativeTarget(
      "x86_64-unknown-linux-gnu",
      {
        ...packageOptions(),
        outputDirectory: output,
        env: { CARGO_TARGET_DIR: cargoTarget },
        runCargo: () => {},
        copyFile: async (src, dest) => {
          assert.equal(src, source);
          await writeFile(src, mutated);
          await fsCopyFile(src, dest);
        },
        runNpm: async ({ args, cwd }) => {
          assert.deepEqual(args, ["pack", "--pack-destination", output]);
          await cp(cwd, inspectDir, { recursive: true });
          await writeFile(
            join(output, packageNameToTarballName("@bamti/bamti-linux-x64-gnu", "0.2.0")),
            "",
          );
        },
      },
    );

    assert.equal(record.sha256, createHash("sha256").update(mutated).digest("hex"));
    const storedRecord = await readJson(recordPath);
    assert.equal(storedRecord.sha256, record.sha256);

    const stagedAddon = await readFile(join(inspectDir, "bamti.linux-x64-gnu.node"));
    assert.deepEqual(stagedAddon, mutated);

    const manifest = await readJson(join(inspectDir, "package.json"));
    assert.equal(manifest.bamtiNative.sha256, record.sha256);
  });
});

test("packageNativeTarget handles a darwin target without libc", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-apple-darwin", "release");
    await mkdir(releaseDir, { recursive: true });
    await writeFile(join(releaseDir, "libbamts_napi.dylib"), "fake darwin addon\n");

    const inspectDir = join(temp, "inspect");

    const { record } = await packageNativeTarget("x86_64-apple-darwin", {
      ...packageOptions(),
      outputDirectory: output,
      env: { CARGO_TARGET_DIR: cargoTarget },
      runCargo: () => {},
      runNpm: async ({ cwd }) => {
        await cp(cwd, inspectDir, { recursive: true });
      },
    });

    assert.equal(record.package, "@bamti/bamti-darwin-x64");
    assert.equal(record.libc, undefined);
    assert.equal(record.runner, "depot-macos-latest");

    const manifest = await readJson(join(inspectDir, "package.json"));
    assert.equal(manifest.name, "@bamti/bamti-darwin-x64");
    assert.equal(manifest.libc, undefined);
    assert.equal(manifest.bamtiNative.target, "x86_64-apple-darwin");
  });
});

test("packageNativeTarget fails when the cargo output is missing", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    await mkdir(join(cargoTarget, "x86_64-unknown-linux-gnu", "release"), {
      recursive: true,
    });

    await assert.rejects(
      packageNativeTarget("x86_64-unknown-linux-gnu", {
        ...packageOptions(),
        outputDirectory: output,
        env: { CARGO_TARGET_DIR: cargoTarget },
        runCargo: () => {},
        runNpm: () => {},
      }),
      (error) => error.message.includes("cargo completed without"),
    );
  });
});

test("packageNativeTarget fails when there is an extra dynamic library", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-unknown-linux-gnu", "release");
    await mkdir(releaseDir, { recursive: true });
    await writeFile(join(releaseDir, "libbamts_napi.so"), "fake\n");
    await writeFile(join(releaseDir, "libextra.so"), "extra\n");

    await assert.rejects(
      packageNativeTarget("x86_64-unknown-linux-gnu", {
        ...packageOptions(),
        outputDirectory: output,
        env: { CARGO_TARGET_DIR: cargoTarget },
        runCargo: () => {},
        runNpm: () => {},
      }),
      (error) => error.message.includes("expected exactly one .so"),
    );
  });
});

test("assembleNativeRecords writes a complete native release table", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const records = await writeRecords(temp);
    const inspectDir = join(temp, "inspect");
    const { table, tarballPath } = await assembleNativeRecords(
      records.map(({ path }) => path),
      {
        outputDirectory: output,
        runNpm: async ({ args, cwd }) => {
          assert.deepEqual(args, ["pack", "--pack-destination", output]);
          await cp(cwd, inspectDir, { recursive: true });
          await writeFile(
            join(output, packageNameToTarballName("bamti", "0.2.0")),
            "",
          );
        },
      },
    );

    assert.equal(table.version, 1);
    assert.deepEqual(table.release, records[0].record.release);
    assert.equal(table.targets.length, NATIVE_TARGETS.length);
    for (const fixed of NATIVE_TARGETS) {
      const row = table.targets.find(({ selector }) => selector === fixed.selector);
      const record = records.find(({ record: value }) => value.selector === fixed.selector).record;
      const expected = {
        selector: fixed.selector,
        target: fixed.target,
        package: fixed.package,
        entry: fixed.entry,
        os: fixed.os,
        cpu: fixed.cpu,
        artifactKind: fixed.artifactKind,
        version: record.version,
        sha256: record.sha256,
        ...PROVENANCE,
        runner: RUNNERS.get(fixed.selector),
      };
      expected.libc = fixed.libc;
      assert.deepEqual(row, expected);
    }
    const storedTable = await readJson(
      join(inspectDir, "native-release-table.json"),
    );
    assert.deepEqual(storedTable, JSON.parse(JSON.stringify(table)));
    assert.equal(tarballPath, join(output, "bamti-0.2.0.tgz"));
  });
});

test("assembleNativeRecords rejects mixed release tuples", async () => {
  await withTemporaryDirectory(async (temp) => {
    const records = await writeRecords(temp, (record, selector) => {
      if (selector === "linux-x64-gnu") {
        record.release.sourceCommit = "c".repeat(40);
        record.release.releaseId =
          `bamti/0.2.0/${"c".repeat(40)}/native-abi-1/cli-protocol-1/${BUILD_SET_ID}`;
      }
    });
    await assert.rejects(
      assembleNativeRecords(records.map(({ path }) => path), {
        outputDirectory: join(temp, "dist"),
        runNpm: () => {},
      }),
      /different release tuple/,
    );
  });
});

test("assembleNativeRecords rejects missing provenance", async () => {
  await withTemporaryDirectory(async (temp) => {
    const records = await writeRecords(temp, (record, selector) => {
      if (selector === "linux-x64-gnu") delete record.toolchain;
    });
    await assert.rejects(
      assembleNativeRecords(records.map(({ path }) => path), {
        outputDirectory: join(temp, "dist"),
        runNpm: () => {},
      }),
      /invalid toolchain/,
    );
  });
});

test("assembleNativeRecords requires exactly five records", async () => {
  await withTemporaryDirectory(async (temp) => {
    const records = await writeRecords(temp);
    await assert.rejects(
      assembleNativeRecords(records.slice(0, 4).map(({ path }) => path), {
        outputDirectory: join(temp, "dist"),
        runNpm: () => {},
      }),
      /requires exactly 5 records/,
    );
  });
});

test("assembleNativeRecords does not mutate the source bamti package", async () => {
  await withTemporaryDirectory(async (temp) => {
    const fakeNpm = join(temp, "npm");
    await cp(npmRoot, fakeNpm, { recursive: true });
    const manifestPath = join(fakeNpm, "bamti", "package.json");
    const manifest = await readJson(manifestPath);
    manifest.version = "0.1.0-canary";
    for (const packageName of Object.keys(manifest.optionalDependencies)) {
      manifest.optionalDependencies[packageName] = "0.1.0-canary";
    }
    await writeJson(manifestPath, manifest);
    const expectedManifest = JSON.stringify(await readJson(manifestPath));
    const records = await writeRecords(temp);

    await assembleNativeRecords(records.map(({ path }) => path), {
      npmRoot: fakeNpm,
      outputDirectory: join(temp, "dist"),
      runNpm: () => {},
    });

    assert.equal(JSON.stringify(await readJson(manifestPath)), expectedManifest);
    assert.equal(existsSync(join(fakeNpm, "bamti", "native-release-table.json")), false);
  });
});
