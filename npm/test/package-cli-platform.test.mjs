import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  copyFile as fsCopyFile,
  cp,
  mkdir,
  mkdtemp,
  readFile,
  rm,
  writeFile,
} from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { tmpdir } from "node:os";
import test from "node:test";

import { CLI_TARGETS } from "../bamti-cli/index.js";
import { packageCliTarget } from "../scripts/package-platform.mjs";
import { createNativeBuildPlan } from "../scripts/native-build-plan.mjs";

const npmRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const SOURCE_COMMIT = "a".repeat(40);
const PROVENANCE = Object.freeze({
  cargoLockSha256: "b".repeat(64),
  workflowRevision: "cli-release-build-v1",
  toolchain: "rustc 1.97.1",
  builderRevision: "package-platform-v1",
});
const BUILD_SET_ID = createNativeBuildPlan({
  sourceCommit: SOURCE_COMMIT,
  sourceVersion: "0.2.0",
  ...PROVENANCE,
  targets: CLI_TARGETS.map(({ target }) => target),
}).buildSetId;

function packageOptions(overrides = {}) {
  return {
    buildSetId: BUILD_SET_ID,
    sourceCommit: SOURCE_COMMIT,
    ...PROVENANCE,
    ...overrides,
  };
}

async function withTemporaryDirectory(callback) {
  const directory = await mkdtemp(join(tmpdir(), "bamti-cli-test-"));
  try {
    return await callback(directory);
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
}

async function readJson(path) {
  return JSON.parse(await readFile(path, "utf8"));
}

function packageNameToTarballName(packageName, version) {
  return `${packageName.replace(/^@/, "").replace(/\//g, "-")}-${version}.tgz`;
}

test("all CLI artifact templates satisfy packageCliTarget's bamtiCli gate", async () => {
  for (const fixed of CLI_TARGETS) {
    const directory = fixed.package.replace(/^@[^/]+\//, "");
    const manifest = await readJson(join(npmRoot, "artifacts", directory, "package.json"));
    assert.ok(manifest.bamtiCli !== null && typeof manifest.bamtiCli === "object");
    assert.equal(manifest.bamtiCli.entry, fixed.entry);
    assert.equal(manifest.bamtiCli.target, fixed.target);
    assert.equal(manifest.bamtiCli.artifactKind, fixed.artifactKind);
    assert.equal(manifest.bamtiCli.runner, fixed.runner);
  }
});

test("packageCliTarget records staged binary hash after source mutation", async () => {
  await withTemporaryDirectory(async (temp) => {
    const output = join(temp, "dist");
    const cargoTarget = join(temp, "target");
    const releaseDir = join(cargoTarget, "x86_64-unknown-linux-gnu", "release");
    await mkdir(releaseDir, { recursive: true });
    const original = Buffer.from("original binary bytes\n");
    const mutated = Buffer.from("mutated binary bytes\n");
    const source = join(releaseDir, "bamts");
    await writeFile(source, original);

    const inspectDir = join(temp, "inspect");

    const { record, recordPath } = await packageCliTarget(
      "x86_64-unknown-linux-gnu",
      {
        ...packageOptions(),
        outputDirectory: output,
        env: { CARGO_TARGET_DIR: cargoTarget },
        runCargo: ({ args, env }) => {
          assert.deepEqual(args, [
            "build",
            "--release",
            "--locked",
            "--target",
            "x86_64-unknown-linux-gnu",
            "-p",
            "bamts-cli",
          ]);
          assert.equal(env.BAMTI_BUILD_SET_ID, BUILD_SET_ID);
          assert.equal(env.BAMTI_RELEASE_PACKAGE_VERSION, "0.2.0");
          assert.equal(env.BAMTI_SOURCE_COMMIT, SOURCE_COMMIT);
          assert.equal(env.BAMTI_TARGET, "x86_64-unknown-linux-gnu");
          assert.equal(env.BAMTI_ARTIFACT_KIND, "cli-binary");
          assert.equal(env.BAMTI_NATIVE_ABI, "1");
          assert.equal(env.BAMTI_CLI_PROTOCOL, "1");
        },
        copyFile: async (src, dest) => {
          assert.equal(src, source);
          await writeFile(src, mutated);
          await fsCopyFile(src, dest);
        },
        runNpm: async ({ args, cwd }) => {
          assert.deepEqual(args, ["pack", "--pack-destination", output]);
          await cp(cwd, inspectDir, { recursive: true });
          await writeFile(
            join(output, packageNameToTarballName("@bamti/cli-linux-x64", "0.2.0")),
            "",
          );
        },
      },
    );

    const mutatedHash = createHash("sha256").update(mutated).digest("hex");
    assert.equal(record.sha256, mutatedHash);
    const storedRecord = await readJson(recordPath);
    assert.equal(storedRecord.sha256, record.sha256);

    const stagedBinary = await readFile(join(inspectDir, "bin", "bamts"));
    assert.deepEqual(stagedBinary, mutated);

    const manifest = await readJson(join(inspectDir, "package.json"));
    assert.equal(manifest.bamtiCli.sha256, mutatedHash);
    assert.equal(manifest.bamtiCli.entry, "bin/bamts");
    assert.equal(manifest.bamtiCli.target, "x86_64-unknown-linux-gnu");
    assert.equal(manifest.bamtiCli.artifactKind, "cli-binary");
    assert.equal(manifest.bamtiCli.runner, "depot-ubuntu-24.04");
    assert.equal(manifest.bamtiCli.release.packageVersion, "0.2.0");
    assert.equal(manifest.bamtiCli.release.sourceCommit, SOURCE_COMMIT);
    assert.equal(manifest.bamtiCli.release.nativeAbi, 1);
    assert.equal(manifest.bamtiCli.release.cliProtocol, 1);
    assert.equal(manifest.bamtiCli.release.buildSetId, BUILD_SET_ID);
    assert.equal(
      manifest.bamtiCli.release.releaseId,
      `bamti/0.2.0/${SOURCE_COMMIT}/native-abi-1/cli-protocol-1/${BUILD_SET_ID}`,
    );
  });
});
