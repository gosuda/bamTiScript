import { existsSync } from "node:fs";
import {
  cp,
  copyFile as fsCopyFile,
  mkdir,
  mkdtemp,
  readdir,
  readFile,
  rm,
  writeFile,
} from "node:fs/promises";
import { createHash } from "node:crypto";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";

import { NATIVE_TARGETS } from "../bamti/native-loader.js";
import {
  createNativeBuildPlan,
  NATIVE_RELEASE_TARGETS,
} from "./native-build-plan.mjs";

const scriptPath = fileURLToPath(import.meta.url);
const scriptDir = dirname(scriptPath);
const defaultNpmRoot = resolve(scriptDir, "..");
const defaultRepositoryRoot = resolve(defaultNpmRoot, "..");

const CARGO_OUTPUT_FOR_TARGET = new Map([
  ["x86_64-unknown-linux-gnu", { file: "libbamts_napi.so", ext: ".so", runner: "depot-ubuntu-24.04" }],
  ["aarch64-unknown-linux-gnu", { file: "libbamts_napi.so", ext: ".so", runner: "depot-ubuntu-24.04-arm" }],
  ["x86_64-apple-darwin", { file: "libbamts_napi.dylib", ext: ".dylib", runner: "depot-macos-latest" }],
  ["aarch64-apple-darwin", { file: "libbamts_napi.dylib", ext: ".dylib", runner: "depot-macos-latest" }],
  ["x86_64-pc-windows-msvc", { file: "bamts_napi.dll", ext: ".dll", runner: "depot-windows-2025-4" }],
]);

const RELEASE_STRING_KEYS = [
  "packageVersion",
  "sourceCommit",
  "buildSetId",
  "releaseId",
];

const RELEASE_NUMBER_KEYS = ["nativeAbi", "cliProtocol"];
const COMMON_PROVENANCE_KEYS = [
  "cargoLockSha256",
  "workflowRevision",
  "toolchain",
  "builderRevision",
];


function fail(message) {
  throw new Error(`bamti native package build: ${message}`);
}

function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function canonicalReleaseId(release) {
  return `bamti/${release.packageVersion}/${release.sourceCommit}/native-abi-${release.nativeAbi}/cli-protocol-${release.cliProtocol}/${release.buildSetId}`;
}

function validateReleaseTuple(release) {
  if (
    !isRecord(release) ||
    RELEASE_STRING_KEYS.some((key) => typeof release[key] !== "string" || release[key] === "") ||
    RELEASE_NUMBER_KEYS.some((key) => !Number.isSafeInteger(release[key]) || release[key] < 1)
  ) {
    throw new Error("release tuple is incomplete");
  }
  if (release.releaseId !== canonicalReleaseId(release)) {
    throw new Error("release tuple has a non-canonical releaseId");
  }
}
function validateProvenance(value, label) {
  if (!isRecord(value) || !/^[0-9a-f]{64}$/.test(value.cargoLockSha256)) {
    fail(`${label} has an invalid cargoLockSha256`);
  }
  for (const key of ["workflowRevision", "toolchain", "builderRevision", "runner"]) {
    if (typeof value[key] !== "string" || value[key] === "") {
      fail(`${label} has an invalid ${key}`);
    }
  }
}

function expectedBuildSetId(release, provenance) {
  return createNativeBuildPlan({
    sourceCommit: release.sourceCommit,
    sourceVersion: release.packageVersion,
    cargoLockSha256: provenance.cargoLockSha256,
    workflowRevision: provenance.workflowRevision,
    toolchain: provenance.toolchain,
    builderRevision: provenance.builderRevision,
    targets: NATIVE_RELEASE_TARGETS,
  }).buildSetId;
}

function validateBuildPlanIdentity(release, provenance) {
  if (release.buildSetId !== expectedBuildSetId(release, provenance)) {
    fail("buildSetId does not match the canonical native build plan");
  }
}

function requiredProvenance(options, env, runner) {
  const provenance = {
    cargoLockSha256:
      options.cargoLockSha256 ?? env.BAMTI_CARGO_LOCK_SHA256,
    workflowRevision:
      options.workflowRevision ?? env.BAMTI_WORKFLOW_REVISION,
    toolchain: options.toolchain ?? env.BAMTI_TOOLCHAIN,
    builderRevision:
      options.builderRevision ?? env.BAMTI_BUILDER_REVISION,
    runner,
  };
  validateProvenance(provenance, "build provenance");
  return provenance;
}


async function readJson(path) {
  return JSON.parse(await readFile(path, "utf8"));
}

async function writeJson(path, value) {
  await writeFile(path, `${JSON.stringify(value, null, 2)}\n`);
}

function defaultRunCargo({ args, env, cwd }) {
  const command = process.platform === "win32" ? "cargo.cmd" : "cargo";
  const result = spawnSync(command, args, { cwd, env, stdio: "inherit" });
  if (result.error) {
    fail(`could not start ${command}: ${result.error.message}`);
  }
  if (result.status !== 0) {
    fail(`${command} ${args.join(" ")} failed with exit code ${result.status ?? "unknown"}.`);
  }
}

function defaultRunNpm({ args, cwd }) {
  const command = process.platform === "win32" ? "npm.cmd" : "npm";
  const result = spawnSync(command, args, { cwd, stdio: "inherit" });
  if (result.error) {
    fail(`could not start ${command}: ${result.error.message}`);
  }
  if (result.status !== 0) {
    fail(`${command} ${args.join(" ")} failed with exit code ${result.status ?? "unknown"}.`);
  }
}

function artifactDirectoryName(packageName) {
  return packageName.replace(/^@[^/]+\//, "");
}

function packageNameToTarballName(packageName, version) {
  return `${packageName.replace(/^@/, "").replace(/\//g, "-")}-${version}.tgz`;
}

function sha256Hex(bytes) {
  return createHash("sha256").update(bytes).digest("hex");
}

function gitSourceCommit(repositoryRoot) {
  const result = spawnSync("git", ["rev-parse", "HEAD"], {
    cwd: repositoryRoot,
    encoding: "utf8",
  });
  if (result.error || result.status !== 0) {
    const detail = result.stderr?.trim() || result.error?.message || "git failed";
    fail(`could not determine source commit: ${detail}`);
  }
  return result.stdout.trim();
}

export async function packageNativeTarget(targetTriple, options = {}) {
  const fixed = NATIVE_TARGETS.find(({ target }) => target === targetTriple);
  if (!fixed) {
    const supported = NATIVE_TARGETS.map(({ target }) => target).join(", ");
    fail(`unsupported target ${targetTriple}. Supported: ${supported}.`);
  }

  const cargoInfo = CARGO_OUTPUT_FOR_TARGET.get(targetTriple);
  if (!cargoInfo) {
    fail(`no cargo output mapping for target ${targetTriple}`);
  }

  const npmRoot = options.npmRoot ?? defaultNpmRoot;
  const repositoryRoot = options.repositoryRoot ?? defaultRepositoryRoot;
  const outputDirectory = options.outputDirectory ?? join(npmRoot, "dist");
  const runCargo = options.runCargo ?? defaultRunCargo;
  const runNpm = options.runNpm ?? defaultRunNpm;
  const env = options.env ?? process.env;

  const bamtiManifest = await readJson(join(npmRoot, "bamti", "package.json"));
  const version = bamtiManifest.version;
  if (typeof version !== "string" || version === "") {
    fail("bamti/package.json has no version");
  }

  const buildSetId = options.buildSetId ?? env.BAMTI_BUILD_SET_ID;
  if (!buildSetId) {
    fail("--build-set-id or BAMTI_BUILD_SET_ID is required");
  }

  const sourceCommit =
    options.sourceCommit ?? env.BAMTI_SOURCE_COMMIT ?? gitSourceCommit(repositoryRoot);
  const nativeAbi = Number(options.nativeAbi ?? env.BAMTI_NATIVE_ABI ?? 1);
  const cliProtocol = Number(options.cliProtocol ?? env.BAMTI_CLI_PROTOCOL ?? 1);
  const provenance = requiredProvenance(options, env, cargoInfo.runner);

  const release = {
    packageVersion: version,
    sourceCommit,
    nativeAbi,
    cliProtocol,
    buildSetId,
  };
  release.releaseId = canonicalReleaseId(release);
  validateReleaseTuple(release);
  validateBuildPlanIdentity(release, provenance);

  const cargoTargetDir = env.CARGO_TARGET_DIR
    ? resolve(repositoryRoot, env.CARGO_TARGET_DIR)
    : join(repositoryRoot, "target");
  const releaseDir = join(cargoTargetDir, targetTriple, "release");
  const cargoOutputPath = join(releaseDir, cargoInfo.file);
  runCargo({
    args: [
      "build",
      "--release",
      "--locked",
      "--package",
      "bamts-napi",
      "--target",
      targetTriple,
    ],
    env: {
      ...env,
      BAMTI_RELEASE_ID: release.releaseId,
      BAMTI_RELEASE_PACKAGE_VERSION: release.packageVersion,
      BAMTI_BUILD_SET_ID: release.buildSetId,
      BAMTI_SOURCE_COMMIT: release.sourceCommit,
      BAMTI_TARGET: targetTriple,
      BAMTI_ARTIFACT_KIND: fixed.artifactKind,
      BAMTI_NATIVE_ABI: String(release.nativeAbi),
      BAMTI_CLI_PROTOCOL: String(release.cliProtocol),
      BAMTI_CARGO_LOCK_SHA256: provenance.cargoLockSha256,
      BAMTI_WORKFLOW_REVISION: provenance.workflowRevision,
      BAMTI_TOOLCHAIN: provenance.toolchain,
      BAMTI_BUILDER_REVISION: provenance.builderRevision,
    },
    cwd: repositoryRoot,
  });

  if (!existsSync(cargoOutputPath)) {
    fail(`cargo completed without ${cargoOutputPath}`);
  }

  const entries = await readdir(releaseDir, { withFileTypes: true });
  const libs = entries.filter(
    (entry) => entry.isFile() && entry.name.endsWith(cargoInfo.ext),
  );
  if (libs.length !== 1) {
    fail(`expected exactly one ${cargoInfo.ext} in ${releaseDir}, found ${libs.length}`);
  }
  if (libs[0].name !== cargoInfo.file) {
    fail(`expected cargo output ${cargoInfo.file}, found ${libs[0].name}`);
  }

  const stagingRoot = await mkdtemp(join(tmpdir(), "bamti-native-"));
  try {
    const packageDirectory = join(stagingRoot, artifactDirectoryName(fixed.package));
    await cp(
      join(npmRoot, "artifacts", artifactDirectoryName(fixed.package)),
      packageDirectory,
      { recursive: true },
    );

    const entryPath = join(packageDirectory, fixed.entry);
    const copy = options.copyFile ?? fsCopyFile;
    await copy(cargoOutputPath, entryPath);
    const addonBytes = await readFile(entryPath);
    const sha256 = sha256Hex(addonBytes);

    const manifestPath = join(packageDirectory, "package.json");
    const manifest = await readJson(manifestPath);
    manifest.version = version;
    manifest.main = fixed.entry;
    manifest.files = [fixed.entry];
    manifest.engines = { node: ">=24" };
    manifest.os = [fixed.os];
    manifest.cpu = [fixed.cpu];
    if (fixed.libc !== undefined) {
      manifest.libc = [fixed.libc];
    } else {
      delete manifest.libc;
    }
    if (!isRecord(manifest.bamtiNative)) {
      fail(`${artifactDirectoryName(fixed.package)}/package.json is missing bamtiNative`);
    }
    manifest.bamtiNative.entry = fixed.entry;
    manifest.bamtiNative.target = fixed.target;
    manifest.bamtiNative.artifactKind = fixed.artifactKind;
    manifest.bamtiNative.sha256 = sha256;
    manifest.bamtiNative.cargoLockSha256 = provenance.cargoLockSha256;
    manifest.bamtiNative.workflowRevision = provenance.workflowRevision;
    manifest.bamtiNative.toolchain = provenance.toolchain;
    manifest.bamtiNative.builderRevision = provenance.builderRevision;
    manifest.bamtiNative.runner = provenance.runner;
    if (!isRecord(manifest.bamtiNative.release)) {
      manifest.bamtiNative.release = {};
    }
    manifest.bamtiNative.release.packageVersion = version;
    manifest.bamtiNative.release.sourceCommit = sourceCommit;
    manifest.bamtiNative.release.nativeAbi = nativeAbi;
    manifest.bamtiNative.release.cliProtocol = cliProtocol;
    manifest.bamtiNative.release.buildSetId = buildSetId;
    manifest.bamtiNative.release.releaseId = release.releaseId;
    await writeJson(manifestPath, manifest);

    await mkdir(outputDirectory, { recursive: true });
    await runNpm({
      args: ["pack", "--pack-destination", outputDirectory],
      cwd: packageDirectory,
    });

    const record = {
      selector: fixed.selector,
      target: targetTriple,
      package: fixed.package,
      entry: fixed.entry,
      os: fixed.os,
      cpu: fixed.cpu,
      libc: fixed.libc,
      artifactKind: fixed.artifactKind,
      version,
      sha256,
      cargoLockSha256: provenance.cargoLockSha256,
      workflowRevision: provenance.workflowRevision,
      toolchain: provenance.toolchain,
      builderRevision: provenance.builderRevision,
      runner: provenance.runner,
      release,
    };
    const recordFileName = `bamti-${fixed.selector}-${version}.json`;
    const recordPath = join(outputDirectory, recordFileName);
    await writeJson(recordPath, record);

    const tarballName = packageNameToTarballName(fixed.package, version);
    const tarballPath = join(outputDirectory, tarballName);

    return { record, recordPath, tarballPath };
  } finally {
    await rm(stagingRoot, { recursive: true, force: true });
  }
}

export async function assembleNativeRecords(recordPaths, options = {}) {
  if (!Array.isArray(recordPaths)) {
    fail("record paths must be an array");
  }

  const npmRoot = options.npmRoot ?? defaultNpmRoot;
  const outputDirectory = options.outputDirectory ?? join(npmRoot, "dist");
  const runNpm = options.runNpm ?? defaultRunNpm;

  if (recordPaths.length !== NATIVE_TARGETS.length) {
    fail(`assemble requires exactly ${NATIVE_TARGETS.length} records, got ${recordPaths.length}`);
  }

  const records = [];
  for (let i = 0; i < recordPaths.length; i += 1) {
    const recordPath = recordPaths[i];
    const record = await readJson(recordPath);
    if (!isRecord(record)) {
      fail(`record ${recordPath} is not an object`);
    }
    if (!isRecord(record.release)) {
      fail(`record ${recordPath} is missing release`);
    }
    validateReleaseTuple(record.release);
    validateProvenance(record, `record ${recordPath}`);
    records.push(record);
  }

  const firstRelease = records[0].release;
  for (let i = 1; i < records.length; i += 1) {
    const other = records[i].release;
    if (
      RELEASE_STRING_KEYS.some((key) => firstRelease[key] !== other[key]) ||
      RELEASE_NUMBER_KEYS.some((key) => firstRelease[key] !== other[key])
    ) {
      fail(`record ${recordPaths[i]} has a different release tuple`);
    }
  }
  for (let i = 1; i < records.length; i += 1) {
    if (
      COMMON_PROVENANCE_KEYS.some(
        (key) => records[i][key] !== records[0][key],
      )
    ) {
      fail(`record ${recordPaths[i]} has different build provenance`);
    }
  }
  validateBuildPlanIdentity(firstRelease, records[0]);


  const expectedVersion = firstRelease.packageVersion;
  const selectors = new Set();
  const recordBySelector = new Map();
  for (let i = 0; i < records.length; i += 1) {
    const record = records[i];
    if (record.version !== expectedVersion) {
      fail(`record ${recordPaths[i]} has version ${record.version}, expected ${expectedVersion}`);
    }
    if (typeof record.selector !== "string" || record.selector === "") {
      fail(`record ${recordPaths[i]} has an invalid selector`);
    }
    if (selectors.has(record.selector)) {
      fail(`duplicate selector ${record.selector} in records`);
    }
    selectors.add(record.selector);

    const fixed = NATIVE_TARGETS.find(({ selector }) => selector === record.selector);
    if (!fixed) {
      fail(`record ${recordPaths[i]} has unknown selector ${record.selector}`);
    }
    for (const key of ["target", "package", "entry", "os", "cpu", "artifactKind"]) {
      if (record[key] !== fixed[key]) {
        fail(`record ${recordPaths[i]} has wrong ${key}`);
      }
    }
    if (record.libc !== fixed.libc) {
      fail(`record ${recordPaths[i]} has wrong libc`);
    }
    if (record.runner !== CARGO_OUTPUT_FOR_TARGET.get(fixed.target)?.runner) {
      fail(`record ${recordPaths[i]} has wrong runner`);
    }
    if (!/^[0-9a-f]{64}$/.test(record.sha256)) {
      fail(`record ${recordPaths[i]} has invalid sha256`);
    }
    recordBySelector.set(record.selector, record);
  }

  for (const { selector } of NATIVE_TARGETS) {
    if (!selectors.has(selector)) {
      fail(`missing record for selector ${selector}`);
    }
  }

  const targets = NATIVE_TARGETS.map((fixed) => {
    const record = recordBySelector.get(fixed.selector);
    return {
      selector: fixed.selector,
      target: fixed.target,
      package: fixed.package,
      entry: fixed.entry,
      os: fixed.os,
      cpu: fixed.cpu,
      libc: fixed.libc,
      artifactKind: fixed.artifactKind,
      version: record.version,
      sha256: record.sha256,
      cargoLockSha256: record.cargoLockSha256,
      workflowRevision: record.workflowRevision,
      toolchain: record.toolchain,
      builderRevision: record.builderRevision,
      runner: record.runner,
    };
  });

  const table = {
    version: 1,
    release: firstRelease,
    targets,
  };

  const stagingRoot = await mkdtemp(join(tmpdir(), "bamti-facade-"));
  try {
    const packageDirectory = join(stagingRoot, "bamti");
    await cp(join(npmRoot, "bamti"), packageDirectory, { recursive: true });

    const manifestPath = join(packageDirectory, "package.json");
    const manifest = await readJson(manifestPath);
    if (!isRecord(manifest.optionalDependencies)) {
      fail("bamti/package.json is missing optionalDependencies");
    }
    manifest.version = expectedVersion;
    for (const { package: packageName } of NATIVE_TARGETS) {
      if (!(packageName in manifest.optionalDependencies)) {
        fail(`bamti/package.json is missing optional dependency ${packageName}`);
      }
      manifest.optionalDependencies[packageName] = expectedVersion;
    }
    await writeJson(manifestPath, manifest);

    await writeJson(join(packageDirectory, "native-release-table.json"), table);

    await mkdir(outputDirectory, { recursive: true });
    await runNpm({
      args: ["pack", "--pack-destination", outputDirectory],
      cwd: packageDirectory,
    });

    const tarballName = packageNameToTarballName("bamti", expectedVersion);
    const tarballPath = join(outputDirectory, tarballName);

    return { table, tarballPath };
  } finally {
    await rm(stagingRoot, { recursive: true, force: true });
  }
}

export async function main(argv = process.argv.slice(2), options = {}) {
  const npmRoot = options.npmRoot ?? defaultNpmRoot;
  const repositoryRoot = options.repositoryRoot ?? defaultRepositoryRoot;
  const outputDirectory =
    options.outputDirectory ??
    (process.env.BAMTI_DIST_ROOT ? resolve(process.env.BAMTI_DIST_ROOT) : join(npmRoot, "dist"));

  const assembleIndex = argv.indexOf("--assemble");
  if (assembleIndex !== -1) {
    const recordPaths = argv.slice(assembleIndex + 1).map((p) => resolve(p));
    return assembleNativeRecords(recordPaths, { npmRoot, outputDirectory });
  }

  let target;
  let buildSetId = process.env.BAMTI_BUILD_SET_ID;
  let sourceCommit = process.env.BAMTI_SOURCE_COMMIT;
  let nativeAbi = 1;
  let cliProtocol = 1;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--target" && i + 1 < argv.length) {
      target = argv[i + 1];
      i += 1;
    } else if (arg === "--build-set-id" && i + 1 < argv.length) {
      buildSetId = argv[i + 1];
      i += 1;
    } else if (arg === "--source-commit" && i + 1 < argv.length) {
      sourceCommit = argv[i + 1];
      i += 1;
    } else if (arg === "--native-abi" && i + 1 < argv.length) {
      nativeAbi = Number(argv[i + 1]);
      i += 1;
    } else if (arg === "--cli-protocol" && i + 1 < argv.length) {
      cliProtocol = Number(argv[i + 1]);
      i += 1;
    } else {
      fail(`unknown argument ${arg}`);
    }
  }

  if (!target) {
    fail("use --target <rust-target-triple>");
  }
  if (!buildSetId) {
    fail("--build-set-id or BAMTI_BUILD_SET_ID is required");
  }
  if (!sourceCommit) {
    sourceCommit = gitSourceCommit(repositoryRoot);
  }

  return packageNativeTarget(target, {
    npmRoot,
    repositoryRoot,
    outputDirectory,
    buildSetId,
    sourceCommit,
    nativeAbi,
    cliProtocol,
  });
}

if (process.argv[1] && resolve(process.argv[1]) === scriptPath) {
  main().catch((error) => {
    console.error(error.message);
    process.exit(1);
  });
}
