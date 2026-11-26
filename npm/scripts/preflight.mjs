import { createHash } from "node:crypto";
import { mkdtempSync, readdirSync, readFileSync, rmSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { ARTIFACTS } from "../bamti-cli/index.js";
import { NATIVE_TARGETS } from "../bamti/native-loader.js";
import { createNativeBuildPlan, NATIVE_RELEASE_TARGETS } from "./native-build-plan.mjs";
const scriptPath = fileURLToPath(import.meta.url);
const scriptDir = dirname(scriptPath);
const npmRoot = dirname(scriptDir);
const repositoryRoot = dirname(npmRoot);

const TABLE_VERSION = 1;
const NATIVE_NODE_ENGINE = ">=24";
const RELEASE_STRING_KEYS = [
  "packageVersion",
  "sourceCommit",
  "buildSetId",
  "releaseId",
];
const RELEASE_NUMBER_KEYS = ["nativeAbi", "cliProtocol"];

const CLI_TARGETS = Object.freeze([
  Object.freeze({
    selector: "linux-x64",
    target: "x86_64-unknown-linux-gnu",
    package: "@bamti/cli-linux-x64",
    entry: "bin/bamts",
    os: "linux",
    cpu: "x64",
    artifactKind: "cli-binary",
    runner: "depot-ubuntu-24.04",
  }),
  Object.freeze({
    selector: "linux-arm64",
    target: "aarch64-unknown-linux-gnu",
    package: "@bamti/cli-linux-arm64",
    entry: "bin/bamts",
    os: "linux",
    cpu: "arm64",
    artifactKind: "cli-binary",
    runner: "depot-ubuntu-24.04-arm",
  }),
  Object.freeze({
    selector: "darwin-x64",
    target: "x86_64-apple-darwin",
    package: "@bamti/cli-darwin-x64",
    entry: "bin/bamts",
    os: "darwin",
    cpu: "x64",
    artifactKind: "cli-binary",
    runner: "depot-macos-latest",
  }),
  Object.freeze({
    selector: "darwin-arm64",
    target: "aarch64-apple-darwin",
    package: "@bamti/cli-darwin-arm64",
    entry: "bin/bamts",
    os: "darwin",
    cpu: "arm64",
    artifactKind: "cli-binary",
    runner: "depot-macos-latest",
  }),
  Object.freeze({
    selector: "win32-x64",
    target: "x86_64-pc-windows-msvc",
    package: "@bamti/cli-win32-x64",
    entry: "bin/bamts.exe",
    os: "win32",
    cpu: "x64",
    artifactKind: "cli-binary",
    runner: "depot-windows-2025-4",
  }),
]);

function readJson(path) {
  return JSON.parse(readFileSync(path, "utf8"));
}

export function artifactDirectory(packageName) {
  // "@bamti/cli-linux-x64" -> "cli-linux-x64"
  return packageName.replace(/^@[^/]+\//, "");
}

export function artifactBinaryName(platform) {
  return platform === "win32" ? "bamts.exe" : "bamts";
}

export function splitPlatform(key) {
  const lastDash = key.lastIndexOf("-");
  return [key.slice(0, lastDash), key.slice(lastDash + 1)];
}

export function tarballName(packageName, version) {
  // npm pack turns "@scope/name" into "scope-name-version.tgz".
  return `${packageName.replace(/^@/, "").replace(/\//g, "-")}-${version}.tgz`;
}

function readTarballFile(tarballPath, entry, encoding = undefined) {
  const options = encoding ? { encoding } : {};
  const result = spawnSync("tar", ["-xOzf", tarballPath, entry], options);
  if (result.error || result.status !== 0) {
    throw new Error(
      `could not read ${entry} from ${tarballPath}: ${
        result.stderr?.toString?.() || result.error?.message || "tar failed"
      }`,
    );
  }
  return result.stdout;
}

function readTarballPackageJson(tarballPath) {
  return JSON.parse(readTarballFile(tarballPath, "package/package.json", "utf8"));
}

function tarballEntries(tarballPath) {
  const result = spawnSync("tar", ["-tzf", tarballPath], { encoding: "utf8" });
  if (result.error || result.status !== 0) return [];
  return result.stdout.split("\n");
}

function tarballHasFile(tarballPath, file) {
  return tarballEntries(tarballPath).includes(file);
}

function tarballHasBinary(tarballPath, binary) {
  return tarballHasFile(tarballPath, `package/bin/${binary}`);
}

function hashTarballFile(tarballPath, entry) {
  const bytes = readTarballFile(tarballPath, entry);
  return createHash("sha256").update(bytes).digest("hex");
}

function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function sameArray(actual, expected) {
  return Array.isArray(actual) && actual.length === 1 && actual[0] === expected;
}

function canonicalReleaseId(release) {
  return `bamti/${release.packageVersion}/${release.sourceCommit}/native-abi-${release.nativeAbi}/cli-protocol-${release.cliProtocol}/${release.buildSetId}`;
}

function equalRelease(actual, expected) {
  return (
    isRecord(actual) &&
    RELEASE_STRING_KEYS.every((key) => actual[key] === expected[key]) &&
    RELEASE_NUMBER_KEYS.every((key) => actual[key] === expected[key])
  );
}

function equalReleaseIdentity(actual, expected) {
  return (
    isRecord(actual) &&
    actual.packageVersion === expected.packageVersion &&
    actual.sourceCommit === expected.sourceCommit &&
    actual.nativeAbi === expected.nativeAbi &&
    actual.cliProtocol === expected.cliProtocol
  );
}

function validateRelease(release) {
  if (
    !isRecord(release) ||
    RELEASE_STRING_KEYS.some(
      (key) => typeof release[key] !== "string" || release[key] === "",
    ) ||
    RELEASE_NUMBER_KEYS.some(
      (key) => !Number.isSafeInteger(release[key]) || release[key] < 1,
    )
  ) {
    throw new Error("generated release table has an incomplete release tuple");
  }
  if (release.releaseId !== canonicalReleaseId(release)) {
    throw new Error("generated release table has a non-canonical releaseId");
  }
}

function validateReleaseTable(table, expectedVersion) {
  if (!isRecord(table) || table.version !== TABLE_VERSION || !Array.isArray(table.targets)) {
    throw new Error("generated native release table has an unsupported schema");
  }
  validateRelease(table.release);
  if (expectedVersion !== undefined && table.release.packageVersion !== expectedVersion) {
    throw new Error(
      `native release table packageVersion ${table.release.packageVersion} does not match expected ${expectedVersion}`,
    );
  }
  if (table.targets.length !== NATIVE_TARGETS.length) {
    throw new Error("generated native release table must contain exactly five targets");
  }

  const selectors = new Set();
  for (const row of table.targets) {
    if (!isRecord(row) || typeof row.selector !== "string" || selectors.has(row.selector)) {
      throw new Error("generated native release table contains an invalid or duplicate selector");
    }
    selectors.add(row.selector);

    const fixed = NATIVE_TARGETS.find(({ selector }) => selector === row.selector);
    if (!fixed) {
      throw new Error(`generated native release table contains unsupported selector ${row.selector}`);
    }

    for (const key of ["target", "package", "entry", "os", "cpu", "artifactKind"]) {
      if (row[key] !== fixed[key]) {
        throw new Error(`generated native release table has wrong ${key} for ${row.selector}`);
      }
    }
    if (row.libc !== fixed.libc) {
      throw new Error(`generated native release table has wrong libc for ${row.selector}`);
    }
    if (row.version !== table.release.packageVersion) {
      throw new Error(`generated native release table has wrong version for ${row.selector}`);
    }
    if (!/^[0-9a-f]{64}$/.test(row.sha256)) {
      throw new Error(`generated native release table has invalid sha256 for ${row.selector}`);
    }
  }

  if (NATIVE_TARGETS.some(({ selector }) => !selectors.has(selector))) {
    throw new Error("generated native release table is missing a supported selector");
  }
}

function readCargoVersion() {
  const cargoPath = join(repositoryRoot, "Cargo.toml");
  let cargo;
  try {
    cargo = readFileSync(cargoPath, "utf8");
  } catch (error) {
    if (error?.code === "ENOENT") {
      return undefined;
    }
    throw new Error(`could not read Cargo.toml: ${error.message}`, { cause: error });
  }

  const match = cargo.match(/\[workspace\.package\][\s\S]*?^version\s*=\s*"([^"]+)"/m);
  return match?.[1];
}

function validateNativeTemplateManifest(manifest, row, dir, expectedVersion) {
  if (!isRecord(manifest)) {
    throw new Error(`native artifact manifest ${dir}/package.json is not an object`);
  }

  if (manifest.name !== row.package) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has name ${manifest.name}, expected ${row.package}`,
    );
  }
  if (manifest.version !== expectedVersion) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has version ${manifest.version}, expected ${expectedVersion}`,
    );
  }
  if (manifest.type !== "commonjs") {
    throw new Error(
      `native artifact manifest ${dir}/package.json has type ${manifest.type}, expected commonjs`,
    );
  }
  if (manifest.main !== row.entry) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has main ${manifest.main}, expected ${row.entry}`,
    );
  }
  if (!sameArray(manifest.files, row.entry)) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has files ${JSON.stringify(manifest.files)}, expected [${row.entry}]`,
    );
  }
  if (!isRecord(manifest.engines) || manifest.engines.node !== NATIVE_NODE_ENGINE) {
    throw new Error(
      `native artifact manifest ${dir}/package.json must require Node ${NATIVE_NODE_ENGINE}`,
    );
  }
  if (!sameArray(manifest.os, row.os) || !sameArray(manifest.cpu, row.cpu)) {
    throw new Error(
      `native artifact manifest ${dir}/package.json host constraints do not match ${row.selector}`,
    );
  }
  if (row.libc === undefined ? manifest.libc !== undefined : !sameArray(manifest.libc, row.libc)) {
    throw new Error(
      `native artifact manifest ${dir}/package.json libc constraint does not match ${row.selector}`,
    );
  }

  const metadata = manifest.bamtiNative;
  if (!isRecord(metadata)) {
    throw new Error(`native artifact manifest ${dir}/package.json is missing bamtiNative`);
  }

  for (const key of ["entry", "target", "artifactKind"]) {
    if (metadata[key] !== row[key]) {
      throw new Error(
        `native artifact manifest ${dir}/package.json has bamtiNative ${key} ${metadata[key]}, expected ${row[key]}`,
      );
    }
  }
  if (typeof metadata.sha256 !== "string" || metadata.sha256 === "") {
    throw new Error(
      `native artifact manifest ${dir}/package.json has an invalid bamtiNative sha256`,
    );
  }

  if (!isRecord(metadata.release)) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has an invalid bamtiNative release tuple`,
    );
  }
  if (metadata.release.packageVersion !== manifest.version) {
    throw new Error(
      `native artifact manifest ${dir}/package.json has bamtiNative packageVersion ${metadata.release.packageVersion}, which does not match manifest version ${manifest.version}`,
    );
  }
  for (const key of ["sourceCommit", "buildSetId", "releaseId"]) {
    if (typeof metadata.release[key] !== "string" || metadata.release[key] === "") {
      throw new Error(
        `native artifact manifest ${dir}/package.json has an incomplete bamtiNative release ${key}`,
      );
    }
  }
  for (const key of ["nativeAbi", "cliProtocol"]) {
    if (!Number.isSafeInteger(metadata.release[key]) || metadata.release[key] < 1) {
      throw new Error(
        `native artifact manifest ${dir}/package.json has an incomplete bamtiNative release ${key}`,
      );
    }
  }
}
export function assertManifestConsistency(root = npmRoot) {
  const cliManifest = readJson(join(root, "bamti-cli", "package.json"));
  const expectedVersion = cliManifest.version;

  const cargoVersion = readCargoVersion();
  if (cargoVersion !== undefined && cargoVersion !== expectedVersion) {
    throw new Error(
      `Cargo.toml workspace version ${cargoVersion} does not match bamti-cli version ${expectedVersion}`,
    );
  }

  const cliLoaderNames = [...ARTIFACTS.values()].sort();
  const cliOptionalNames = Object.keys(cliManifest.optionalDependencies ?? {}).sort();

  if (JSON.stringify(cliLoaderNames) !== JSON.stringify(cliOptionalNames)) {
    throw new Error(
      `bamti-cli loader and optionalDependencies disagree:\n` +
        `  loader: ${cliLoaderNames.join(", ")}\n` +
        `  optionalDependencies: ${cliOptionalNames.join(", ")}`,
    );
  }

  for (const [packageName, version] of Object.entries(cliManifest.optionalDependencies ?? {})) {
    if (version !== expectedVersion) {
      throw new Error(
        `bamti-cli optionalDependency ${packageName} is pinned to ${version}, expected ${expectedVersion}`,
      );
    }
  }

  for (const [key, packageName] of ARTIFACTS) {
    const dir = artifactDirectory(packageName);
    const manifest = readJson(join(root, "artifacts", dir, "package.json"));
    if (manifest.name !== packageName) {
      throw new Error(
        `artifact manifest ${dir}/package.json has name ${manifest.name}, expected ${packageName}`,
      );
    }
    if (manifest.version !== expectedVersion) {
      throw new Error(
        `artifact manifest ${dir}/package.json has version ${manifest.version}, expected ${expectedVersion}`,
      );
    }
  }

  const bamtiManifest = readJson(join(root, "bamti", "package.json"));
  if (bamtiManifest.version !== expectedVersion) {
    throw new Error(
      `bamti version ${bamtiManifest.version} does not match bamti-cli version ${expectedVersion}`,
    );
  }

  const nativeLoaderPackages = NATIVE_TARGETS.map((row) => row.package).sort();
  const nativeOptionalPackages = Object.keys(bamtiManifest.optionalDependencies ?? {}).sort();

  if (JSON.stringify(nativeLoaderPackages) !== JSON.stringify(nativeOptionalPackages)) {
    throw new Error(
      `bamti loader and optionalDependencies disagree:\n` +
        `  loader: ${nativeLoaderPackages.join(", ")}\n` +
        `  optionalDependencies: ${nativeOptionalPackages.join(", ")}`,
    );
  }

  for (const row of NATIVE_TARGETS) {
    const pin = bamtiManifest.optionalDependencies?.[row.package];
    if (pin !== expectedVersion) {
      throw new Error(
        `bamti optionalDependency ${row.package} is pinned to ${pin}, expected ${expectedVersion}`,
      );
    }
  }

  for (const row of NATIVE_TARGETS) {
    const dir = artifactDirectory(row.package);
    const manifestPath = join(root, "artifacts", dir, "package.json");
    let manifest;
    try {
      manifest = readJson(manifestPath);
    } catch (error) {
      if (error?.code === "ENOENT") {
        throw new Error(
          `missing native artifact manifest ${dir}/package.json for ${row.selector}`,
        );
      }
      throw new Error(`could not read native artifact manifest ${manifestPath}: ${error.message}`, {
        cause: error,
      });
    }
    validateNativeTemplateManifest(manifest, row, dir, expectedVersion);
  }
}

function packRegistryTarball(packageName, version) {
  const spec = `${packageName}@${version}`;
  const tempDir = mkdtempSync(join(tmpdir(), "bamti-registry-"));
  try {
    const result = spawnSync(
      "npm",
      ["pack", spec, "--ignore-scripts", "--pack-destination", tempDir],
      { encoding: "utf8" },
    );
    if (result.error || result.status !== 0) {
      throw new Error(
        `${spec} is unavailable: ${
          result.stderr?.trim() || result.error?.message || `npm pack exited ${result.status}`
        }`,
      );
    }
    const files = readdirSync(tempDir).filter((name) => name.endsWith(".tgz"));
    if (files.length !== 1) {
      throw new Error(`${spec} did not produce exactly one tarball`);
    }
    return join(tempDir, files[0]);
  } catch (error) {
    rmSync(tempDir, { recursive: true, force: true });
    throw error;
  }
}

function inspectRegistryPackage(packageName, version) {
  const tarballPath = packRegistryTarball(packageName, version);
  try {
    const manifest = readTarballPackageJson(tarballPath);

    const cliFixed = CLI_TARGETS.find(({ package: p }) => p === packageName);
    const nativeFixed = NATIVE_TARGETS.find(({ package: p }) => p === packageName);

    if (cliFixed) {
      const metadata = manifest.bamtiCli;
      if (!isRecord(metadata)) {
        throw new Error(`${packageName}@${version} is missing bamtiCli metadata`);
      }
      const row = {
        ...cliFixed,
        version,
        sha256: metadata.sha256,
        cargoLockSha256: metadata.cargoLockSha256,
        workflowRevision: metadata.workflowRevision,
        toolchain: metadata.toolchain,
        builderRevision: metadata.builderRevision,
      };
      validateCliPackageManifest(manifest, row, metadata.release, tarballPath);
      const entryPath = `package/${row.entry}`;
      if (!tarballHasFile(tarballPath, entryPath)) {
        throw new Error(`${packageName}@${version}: missing ${entryPath}`);
      }
      const digest = hashTarballFile(tarballPath, entryPath);
      if (digest !== metadata.sha256) {
        throw new Error(
          `${packageName}@${version}: ${row.entry} digest ${digest} does not match release table ${metadata.sha256}`,
        );
      }

      return {
        package: packageName,
        family: "cli",
        manifest,
        row,
        release: metadata.release,
        provenance: {
          cargoLockSha256: metadata.cargoLockSha256,
          workflowRevision: metadata.workflowRevision,
          toolchain: metadata.toolchain,
          builderRevision: metadata.builderRevision,
        },
      };
    }

    if (nativeFixed) {
      const metadata = manifest.bamtiNative;
      if (!isRecord(metadata)) {
        throw new Error(`${packageName}@${version} is missing bamtiNative metadata`);
      }
      const row = {
        ...nativeFixed,
        version,
        sha256: metadata.sha256,
        cargoLockSha256: metadata.cargoLockSha256,
        workflowRevision: metadata.workflowRevision,
        toolchain: metadata.toolchain,
        builderRevision: metadata.builderRevision,
        runner: metadata.runner,
      };
      validateNativePackageManifest(manifest, row, metadata.release, tarballPath);
      for (const key of ["cargoLockSha256", "workflowRevision", "toolchain", "builderRevision"]) {
        if (typeof metadata[key] !== "string" || metadata[key] === "") {
          throw new Error(`bamtiNative ${key} is incomplete`);
        }
      }
      const entryPath = `package/${row.entry}`;
      if (!tarballHasFile(tarballPath, entryPath)) {
        throw new Error(`${packageName}@${version}: missing ${entryPath}`);
      }
      const digest = hashTarballFile(tarballPath, entryPath);
      if (digest !== metadata.sha256) {
        throw new Error(
          `${packageName}@${version}: ${row.entry} digest ${digest} does not match release table ${metadata.sha256}`,
        );
      }

      return {
        package: packageName,
        family: "native",
        manifest,
        row,
        release: metadata.release,
        provenance: {
          cargoLockSha256: metadata.cargoLockSha256,
          workflowRevision: metadata.workflowRevision,
          toolchain: metadata.toolchain,
          builderRevision: metadata.builderRevision,
        },
      };
    }

    throw new Error(`${packageName}@${version} is not a known bamti release package`);
  } finally {
    rmSync(dirname(tarballPath), { recursive: true, force: true });
  }
}

function validateFamilyRecords(records, expectedPackages, label) {
  if (records.length !== expectedPackages.length) {
    throw new Error(
      `${label} release family is incomplete: expected ${expectedPackages.length} packages, got ${records.length}`,
    );
  }
  const expectedSet = new Set(expectedPackages);
  for (const record of records) {
    if (!expectedSet.has(record.package)) {
      throw new Error(`${label} release family contains unexpected package ${record.package}`);
    }
  }

  const first = records[0];
  for (const record of records) {
    if (!equalRelease(record.release, first.release)) {
      throw new Error(
        `${label} release family: ${record.package} has a different release tuple`,
      );
    }
    if (
      record.provenance.cargoLockSha256 !== first.provenance.cargoLockSha256 ||
      record.provenance.workflowRevision !== first.provenance.workflowRevision ||
      record.provenance.toolchain !== first.provenance.toolchain ||
      record.provenance.builderRevision !== first.provenance.builderRevision
    ) {
      throw new Error(
        `${label} release family: ${record.package} has different build provenance`,
      );
    }
  }

  const { buildSetId } = createNativeBuildPlan({
    sourceCommit: first.release.sourceCommit,
    sourceVersion: first.release.packageVersion,
    cargoLockSha256: first.provenance.cargoLockSha256,
    workflowRevision: first.provenance.workflowRevision,
    toolchain: first.provenance.toolchain,
    builderRevision: first.provenance.builderRevision,
    targets: NATIVE_RELEASE_TARGETS,
  });

  for (const record of records) {
    if (record.release.buildSetId !== buildSetId) {
      throw new Error(
        `${label} release family: ${record.package} buildSetId ${record.release.buildSetId} does not match the canonical build plan ${buildSetId}`,
      );
    }
  }
}

export function assertRegistryAvailability(
  root = npmRoot,
  lookupVersion = inspectRegistryPackage,
) {
  assertManifestConsistency(root);
  const errors = [];

  const cliRecords = [];
  const cliManifest = readJson(join(root, "bamti-cli", "package.json"));
  for (const [packageName, version] of Object.entries(cliManifest.optionalDependencies ?? {})) {
    try {
      const record = lookupVersion(packageName, version);
      if (isRecord(record) && record.family === "cli") {
        cliRecords.push(record);
      }
    } catch (error) {
      errors.push(error.message);
    }
  }

  const nativeRecords = [];
  const bamtiManifest = readJson(join(root, "bamti", "package.json"));
  for (const [packageName, version] of Object.entries(bamtiManifest.optionalDependencies ?? {})) {
    try {
      const record = lookupVersion(packageName, version);
      if (isRecord(record) && record.family === "native") {
        nativeRecords.push(record);
      }
    } catch (error) {
      errors.push(error.message);
    }
  }

  if (errors.length > 0) {
    throw new Error("registry preflight failed:\n  - " + errors.join("\n  - "));
  }

  if (cliRecords.length === Object.keys(cliManifest.optionalDependencies ?? {}).length) {
    validateFamilyRecords(cliRecords, [...ARTIFACTS.values()], "CLI");
  }
  if (nativeRecords.length === Object.keys(bamtiManifest.optionalDependencies ?? {}).length) {
    validateFamilyRecords(
      nativeRecords,
      NATIVE_TARGETS.map(({ package: p }) => p),
      "native",
    );
  }

  if (cliRecords.length > 0 && nativeRecords.length > 0) {
    if (!equalReleaseIdentity(cliRecords[0].release, nativeRecords[0].release)) {
      throw new Error(
        "CLI and native release families have different shared release identities",
      );
    }
    if (
      cliRecords[0].provenance.cargoLockSha256 !== nativeRecords[0].provenance.cargoLockSha256 ||
      cliRecords[0].provenance.toolchain !== nativeRecords[0].provenance.toolchain
    ) {
      throw new Error(
        "CLI and native release families have different shared build provenance",
      );
    }
  }
}

export function preflight(root = npmRoot) {
  // Local, deterministic check that the loader and the artifact manifests agree.
  assertManifestConsistency(root);
}

function bamtiReleaseTarballName(version) {
  return tarballName("bamti", version);
}

function validateNativePackageManifest(manifest, row, release, tarball) {
  if (manifest.name !== row.package) {
    throw new Error(`expected name ${row.package}, got ${manifest.name}`);
  }
  if (manifest.version !== row.version) {
    throw new Error(`expected version ${row.version}, got ${manifest.version}`);
  }
  if (manifest.type !== "commonjs") {
    throw new Error(`expected type commonjs, got ${manifest.type}`);
  }
  if (manifest.main !== row.entry) {
    throw new Error(`expected main ${row.entry}, got ${manifest.main}`);
  }
  if (!sameArray(manifest.files, row.entry)) {
    throw new Error(`expected files [${row.entry}], got ${JSON.stringify(manifest.files)}`);
  }
  if (!isRecord(manifest.engines) || manifest.engines.node !== NATIVE_NODE_ENGINE) {
    throw new Error(`must require Node ${NATIVE_NODE_ENGINE}`);
  }
  if (!sameArray(manifest.os, row.os) || !sameArray(manifest.cpu, row.cpu)) {
    throw new Error("host constraints do not match release table");
  }
  if (row.libc === undefined ? manifest.libc !== undefined : !sameArray(manifest.libc, row.libc)) {
    throw new Error("libc constraint does not match release table");
  }

  const metadata = manifest.bamtiNative;
  if (!isRecord(metadata)) {
    throw new Error("package metadata is missing bamtiNative");
  }

  for (const key of ["entry", "target", "artifactKind"]) {
    if (metadata[key] !== row[key]) {
      throw new Error(`bamtiNative ${key} does not match release table`);
    }
  }
  if (metadata.sha256 !== row.sha256) {
    throw new Error("bamtiNative sha256 does not match release table");
  }
  if (!equalRelease(metadata.release, release)) {
    throw new Error("bamtiNative release tuple does not match release table");
  }
}

function validateCliReleaseTable(table, expectedVersion) {
  if (!isRecord(table) || table.version !== TABLE_VERSION || !Array.isArray(table.targets)) {
    throw new Error("generated CLI release table has an unsupported schema");
  }
  validateRelease(table.release);
  if (expectedVersion !== undefined && table.release.packageVersion !== expectedVersion) {
    throw new Error(
      `CLI release table packageVersion ${table.release.packageVersion} does not match expected ${expectedVersion}`,
    );
  }
  if (table.targets.length !== CLI_TARGETS.length) {
    throw new Error("generated CLI release table must contain exactly five targets");
  }

  const selectors = new Set();
  for (const row of table.targets) {
    if (!isRecord(row) || typeof row.selector !== "string" || selectors.has(row.selector)) {
      throw new Error("generated CLI release table contains an invalid or duplicate selector");
    }
    selectors.add(row.selector);

    const fixed = CLI_TARGETS.find(({ selector }) => selector === row.selector);
    if (!fixed) {
      throw new Error(`generated CLI release table contains unsupported selector ${row.selector}`);
    }

    for (const key of ["target", "package", "entry", "os", "cpu", "artifactKind"]) {
      if (row[key] !== fixed[key]) {
        throw new Error(`generated CLI release table has wrong ${key} for ${row.selector}`);
      }
    }
    if (typeof row.runner !== "string" || row.runner === "") {
      throw new Error(`generated CLI release table has an incomplete runner for ${row.selector}`);
    }
    if (row.version !== table.release.packageVersion) {
      throw new Error(`generated CLI release table has wrong version for ${row.selector}`);
    }
    if (!/^[0-9a-f]{64}$/.test(row.sha256)) {
      throw new Error(`generated CLI release table has invalid sha256 for ${row.selector}`);
    }
    if (!/^[0-9a-f]{64}$/.test(row.cargoLockSha256)) {
      throw new Error(`generated CLI release table has invalid cargoLockSha256 for ${row.selector}`);
    }
    for (const key of ["workflowRevision", "toolchain", "builderRevision"]) {
      if (typeof row[key] !== "string" || row[key] === "") {
        throw new Error(`generated CLI release table has incomplete ${key} for ${row.selector}`);
      }
    }
  }

  if (CLI_TARGETS.some(({ selector }) => !selectors.has(selector))) {
    throw new Error("generated CLI release table is missing a supported selector");
  }
}

function validateCliPackageManifest(manifest, row, release, tarball) {
  if (manifest.name !== row.package) {
    throw new Error(`expected name ${row.package}, got ${manifest.name}`);
  }
  if (manifest.version !== row.version) {
    throw new Error(`expected version ${row.version}, got ${manifest.version}`);
  }
  if (!isRecord(manifest.engines) || manifest.engines.node !== NATIVE_NODE_ENGINE) {
    throw new Error(`must require Node ${NATIVE_NODE_ENGINE}`);
  }
  if (!sameArray(manifest.os, row.os) || !sameArray(manifest.cpu, row.cpu)) {
    throw new Error("host constraints do not match release table");
  }
  if (!Array.isArray(manifest.files) || !manifest.files.includes(row.entry)) {
    throw new Error(`expected files to include ${row.entry}, got ${JSON.stringify(manifest.files)}`);
  }

  const metadata = manifest.bamtiCli;
  if (!isRecord(metadata)) {
    throw new Error("package metadata is missing bamtiCli");
  }

  for (const key of ["entry", "target", "artifactKind"]) {
    if (metadata[key] !== row[key]) {
      throw new Error(`bamtiCli ${key} does not match release table`);
    }
  }
  if (metadata.sha256 !== row.sha256) {
    throw new Error("bamtiCli sha256 does not match release table");
  }
  for (const key of ["cargoLockSha256", "workflowRevision", "toolchain", "builderRevision"]) {
    if (typeof metadata[key] !== "string" || metadata[key] === "") {
      throw new Error(`bamtiCli ${key} is incomplete`);
    }
  }
  if (metadata.runner !== row.runner) {
    throw new Error(`bamtiCli runner does not match release table`);
  }
  if (!equalRelease(metadata.release, release)) {
    throw new Error("bamtiCli release tuple does not match release table");
  }
}

function validateBamtiReleaseManifest(manifest, expectedVersion) {
  if (manifest.name !== "bamti") {
    throw new Error(`expected name bamti, got ${manifest.name}`);
  }
  if (manifest.version !== expectedVersion) {
    throw new Error(`expected version ${expectedVersion}, got ${manifest.version}`);
  }

  const releaseOptional = manifest.optionalDependencies ?? {};
  const expectedPackages = NATIVE_TARGETS.map((row) => row.package).sort();
  const actualPackages = Object.keys(releaseOptional).sort();

  if (JSON.stringify(expectedPackages) !== JSON.stringify(actualPackages)) {
    throw new Error(
      `bamti optionalDependencies do not match native target packages:\n` +
        `  expected: ${expectedPackages.join(", ")}\n` +
        `  actual: ${actualPackages.join(", ")}`,
    );
  }

  for (const row of NATIVE_TARGETS) {
    if (releaseOptional[row.package] !== expectedVersion) {
      throw new Error(
        `bamti optionalDependency ${row.package} is pinned to ${releaseOptional[row.package]}, expected ${expectedVersion}`,
      );
    }
  }
}

function validateCliFacadeReleaseManifest(manifest, expectedVersion) {
  if (manifest.name !== "bamti-cli") {
    throw new Error(`expected name bamti-cli, got ${manifest.name}`);
  }
  if (manifest.version !== expectedVersion) {
    throw new Error(`expected version ${expectedVersion}, got ${manifest.version}`);
  }

  const releaseOptional = manifest.optionalDependencies ?? {};
  const expectedPackages = [...ARTIFACTS.values()].sort();
  const actualPackages = Object.keys(releaseOptional).sort();

  if (JSON.stringify(expectedPackages) !== JSON.stringify(actualPackages)) {
    throw new Error(
      `bamti-cli optionalDependencies do not match CLI target packages:\n` +
        `  expected: ${expectedPackages.join(", ")}\n` +
        `  actual: ${actualPackages.join(", ")}`,
    );
  }

  for (const packageName of expectedPackages) {
    if (releaseOptional[packageName] !== expectedVersion) {
      throw new Error(
        `bamti-cli optionalDependency ${packageName} is pinned to ${releaseOptional[packageName]}, expected ${expectedVersion}`,
      );
    }
  }
}

function validateNativeReleaseArtifacts(distRoot, expectedVersion, errors, entries) {
  if (entries === undefined) {
    try {
      entries = readdirSync(distRoot);
    } catch (cause) {
      errors.push(`dist directory not found: ${distRoot}`);
      return;
    }
  }

  const facade = bamtiReleaseTarballName(expectedVersion);
  const facadePath = join(distRoot, facade);
  let table;

  if (!entries.includes(facade)) {
    errors.push(`missing release artifact: ${facade} (bamti@${expectedVersion})`);
    return;
  }

  let manifest;
  try {
    manifest = readTarballPackageJson(facadePath);
  } catch (cause) {
    errors.push(`${facade}: could not read manifest: ${cause.message}`);
    return;
  }

  try {
    validateBamtiReleaseManifest(manifest, expectedVersion);
  } catch (cause) {
    errors.push(`${facade}: ${cause.message}`);
    return;
  }

  try {
    table = JSON.parse(
      readTarballFile(facadePath, "package/native-release-table.json", "utf8"),
    );
  } catch (cause) {
    errors.push(`${facade}: missing or unreadable native-release-table.json: ${cause.message}`);
    return;
  }

  try {
    validateReleaseTable(table, expectedVersion);
  } catch (cause) {
    errors.push(`${facade}: native release table is invalid: ${cause.message}`);
    return;
  }

  for (const row of table.targets) {
    const tarball = tarballName(row.package, expectedVersion);
    if (!entries.includes(tarball)) {
      errors.push(`missing release artifact: ${tarball} (${row.package}@${expectedVersion})`);
      continue;
    }
    const tarballPath = join(distRoot, tarball);
    let leafManifest;
    try {
      leafManifest = readTarballPackageJson(tarballPath);
    } catch (cause) {
      errors.push(`${tarball}: could not read manifest: ${cause.message}`);
      continue;
    }
    try {
      validateNativePackageManifest(leafManifest, row, table.release, tarball);
    } catch (cause) {
      errors.push(`${tarball}: ${cause.message}`);
    }
    const entryPath = `package/${row.entry}`;
    if (!tarballHasFile(tarballPath, entryPath)) {
      errors.push(`${tarball}: missing ${entryPath}`);
      continue;
    }
    let digest;
    try {
      digest = hashTarballFile(tarballPath, entryPath);
    } catch (cause) {
      errors.push(`${tarball}: could not hash ${row.entry}: ${cause.message}`);
      continue;
    }
    if (digest !== row.sha256) {
      errors.push(
        `${tarball}: ${row.entry} digest ${digest} does not match release table ${row.sha256}`,
      );
    }
  }
}

export function preflightNativeRelease(distRoot, root = npmRoot) {
  assertManifestConsistency(root);
  const bamtiManifest = readJson(join(root, "bamti", "package.json"));
  const expectedVersion = bamtiManifest.version;
  const errors = [];
  validateNativeReleaseArtifacts(distRoot, expectedVersion, errors);
  if (errors.length > 0) {
    throw new Error("native release preflight failed:\n  - " + errors.join("\n  - "));
  }
}

function validateCliReleaseArtifacts(distRoot, expectedVersion, errors, entries) {
  if (entries === undefined) {
    try {
      entries = readdirSync(distRoot);
    } catch (cause) {
      errors.push(`dist directory not found: ${distRoot}`);
      return;
    }
  }

  const cliFacadeTarball = tarballName("bamti-cli", expectedVersion);
  const cliFacadeTarballPath = join(distRoot, cliFacadeTarball);
  let cliTable;

  if (!entries.includes(cliFacadeTarball)) {
    errors.push(`missing release artifact: ${cliFacadeTarball} (bamti-cli@${expectedVersion})`);
    return;
  }

  let cliFacadeManifest;
  try {
    cliFacadeManifest = readTarballPackageJson(cliFacadeTarballPath);
  } catch (cause) {
    errors.push(`${cliFacadeTarball}: could not read manifest: ${cause.message}`);
    return;
  }

  try {
    validateCliFacadeReleaseManifest(cliFacadeManifest, expectedVersion);
  } catch (cause) {
    errors.push(`${cliFacadeTarball}: ${cause.message}`);
    // Continue to read the table so missing or invalid cli-release-table.json is also fatal.
  }

  try {
    cliTable = JSON.parse(
      readTarballFile(cliFacadeTarballPath, "package/cli-release-table.json", "utf8"),
    );
  } catch (cause) {
    errors.push(`${cliFacadeTarball}: missing or unreadable cli-release-table.json: ${cause.message}`);
    return;
  }

  try {
    validateCliReleaseTable(cliTable, expectedVersion);
  } catch (cause) {
    errors.push(`${cliFacadeTarball}: CLI release table is invalid: ${cause.message}`);
    return;
  }

  if (
    !Array.isArray(cliFacadeManifest.files) ||
    !cliFacadeManifest.files.includes("cli-release-table.json")
  ) {
    errors.push(`${cliFacadeTarball}: files list does not include cli-release-table.json`);
  }

  for (const row of cliTable.targets) {
    const packageName = row.package;
    const tarball = tarballName(packageName, expectedVersion);

    if (!entries.includes(tarball)) {
      errors.push(`missing release artifact: ${tarball} (${packageName}@${expectedVersion})`);
      continue;
    }

    const tarballPath = join(distRoot, tarball);
    let manifest;
    try {
      manifest = readTarballPackageJson(tarballPath);
    } catch (cause) {
      errors.push(`${tarball}: could not read manifest: ${cause.message}`);
      continue;
    }

    try {
      validateCliPackageManifest(manifest, row, cliTable.release, tarball);
    } catch (cause) {
      errors.push(`${tarball}: ${cause.message}`);
    }

    const entryPath = `package/${row.entry}`;
    if (!tarballHasFile(tarballPath, entryPath)) {
      errors.push(`${tarball}: missing ${entryPath}`);
      continue;
    }

    let digest;
    try {
      digest = hashTarballFile(tarballPath, entryPath);
    } catch (cause) {
      errors.push(`${tarball}: could not hash ${row.entry}: ${cause.message}`);
      continue;
    }

    if (digest !== row.sha256) {
      errors.push(
        `${tarball}: ${row.entry} digest ${digest} does not match release table ${row.sha256}`,
      );
    }
  }
}

export function preflightCliRelease(distRoot, root = npmRoot) {
  assertManifestConsistency(root);
  const cliManifest = readJson(join(root, "bamti-cli", "package.json"));
  const expectedVersion = cliManifest.version;
  if (distRoot === undefined) {
    distRoot = join(root, "dist");
  }
  const errors = [];
  validateCliReleaseArtifacts(distRoot, expectedVersion, errors);
  if (errors.length > 0) {
    throw new Error("CLI release preflight failed:\n  - " + errors.join("\n  - "));
  }
}

export function preflightRelease(distRoot, root = npmRoot) {
  assertManifestConsistency(root);

  if (distRoot === undefined) {
    distRoot = join(root, "dist");
  }

  const cliManifest = readJson(join(root, "bamti-cli", "package.json"));
  const bamtiManifest = readJson(join(root, "bamti", "package.json"));
  const expectedVersion = cliManifest.version;

  if (bamtiManifest.version !== expectedVersion) {
    throw new Error(
      `bamti version ${bamtiManifest.version} does not match bamti-cli version ${expectedVersion}`,
    );
  }

  let entries;
  try {
    entries = readdirSync(distRoot);
  } catch (cause) {
    throw new Error(`release preflight: dist directory not found: ${distRoot}`, { cause });
  }

  const errors = [];
  const hasBamti = entries.includes(bamtiReleaseTarballName(expectedVersion));
  const hasNative = NATIVE_TARGETS.some((row) =>
    entries.includes(tarballName(row.package, expectedVersion)),
  );
  const isFullRelease = hasBamti || hasNative;

  validateCliReleaseArtifacts(distRoot, expectedVersion, errors, entries);

  if (isFullRelease) {
    validateNativeReleaseArtifacts(distRoot, expectedVersion, errors, entries);
  }

  if (errors.length > 0) {
    throw new Error("release preflight failed:\n  - " + errors.join("\n  - "));
  }
}

if (process.argv[1] === scriptPath) {
  if (process.argv[2] === "--registry-only") {
    assertRegistryAvailability();
  } else if (process.argv[2] === "--release") {
    preflightRelease();
  } else if (process.argv[2] === "--cli-release") {
    preflightCliRelease();
  } else {
    preflight();
  }
}
