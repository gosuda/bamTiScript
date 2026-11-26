import { createHash } from "node:crypto";
import {
  accessSync,
  chmodSync,
  constants,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmdirSync,
  unlinkSync,
  writeFileSync,
} from "node:fs";
import { createRequire } from "node:module";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";
import { spawn } from "node:child_process";
import { tmpdir } from "node:os";

const requireFromHere = createRequire(import.meta.url);
const RELEASE_STRING_KEYS = ["packageVersion", "sourceCommit", "buildSetId", "releaseId"];
const RELEASE_NUMBER_KEYS = ["nativeAbi", "cliProtocol"];

export const CLI_TARGETS = Object.freeze([
  Object.freeze({ selector: "linux-x64", target: "x86_64-unknown-linux-gnu", package: "@bamti/cli-linux-x64", entry: "bin/bamts", os: "linux", cpu: "x64", artifactKind: "cli-binary", runner: "depot-ubuntu-24.04" }),
  Object.freeze({ selector: "linux-arm64", target: "aarch64-unknown-linux-gnu", package: "@bamti/cli-linux-arm64", entry: "bin/bamts", os: "linux", cpu: "arm64", artifactKind: "cli-binary", runner: "depot-ubuntu-24.04-arm" }),
  Object.freeze({ selector: "darwin-x64", target: "x86_64-apple-darwin", package: "@bamti/cli-darwin-x64", entry: "bin/bamts", os: "darwin", cpu: "x64", artifactKind: "cli-binary", runner: "depot-macos-latest" }),
  Object.freeze({ selector: "darwin-arm64", target: "aarch64-apple-darwin", package: "@bamti/cli-darwin-arm64", entry: "bin/bamts", os: "darwin", cpu: "arm64", artifactKind: "cli-binary", runner: "depot-macos-latest" }),
  Object.freeze({ selector: "win32-x64", target: "x86_64-pc-windows-msvc", package: "@bamti/cli-win32-x64", entry: "bin/bamts.exe", os: "win32", cpu: "x64", artifactKind: "cli-binary", runner: "depot-windows-2025-4" }),
]);

export const ARTIFACTS = new Map(
  CLI_TARGETS.map(({ os, cpu, package: packageName }) => [`${os}-${cpu}`, packageName]),
);

export class UnsupportedPlatformError extends Error {
  constructor(platform, arch) {
    super(`bamti-cli does not support ${platform}-${arch}.`);
    this.name = "UnsupportedPlatformError";
  }
}

export class ArtifactNotFoundError extends Error {
  constructor(platform, arch, packageName, cause) {
    super(
      `Could not find ${packageName} for ${platform}-${arch}. Reinstall bamti-cli with optional dependencies enabled, or install ${packageName} explicitly.`,
      { cause },
    );
    this.name = "ArtifactNotFoundError";
  }
}

export class ArtifactLoadError extends Error {
  constructor(packageName, version, cause) {
    super(`Failed to load verified CLI artifact ${packageName}@${version}.`, { cause });
    this.name = "ArtifactLoadError";
  }
}

function isRecord(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function canonicalReleaseId(release) {
  return `bamti/${release.packageVersion}/${release.sourceCommit}/native-abi-${release.nativeAbi}/cli-protocol-${release.cliProtocol}/${release.buildSetId}`;
}

function equalRelease(actual, expected) {
  return isRecord(actual) &&
    RELEASE_STRING_KEYS.every((key) => actual[key] === expected[key]) &&
    RELEASE_NUMBER_KEYS.every((key) => actual[key] === expected[key]);
}

function validateTable(table, packageVersion) {
  if (!isRecord(table) || table.version !== 1 || !Array.isArray(table.targets)) {
    throw new Error("generated CLI release table has an unsupported schema");
  }
  const release = table.release;
  if (
    !isRecord(release) ||
    RELEASE_STRING_KEYS.some((key) => typeof release[key] !== "string" || release[key] === "") ||
    release.nativeAbi !== 1 ||
    release.cliProtocol !== 1 ||
    release.packageVersion !== packageVersion ||
    !/^[0-9a-f]{64}$/.test(release.buildSetId) ||
    release.releaseId !== canonicalReleaseId(release)
  ) {
    throw new Error("generated CLI release table has an invalid release tuple");
  }
  if (table.targets.length !== CLI_TARGETS.length) {
    throw new Error("generated CLI release table must contain exactly five targets");
  }
  const seen = new Set();
  for (const row of table.targets) {
    const fixed = CLI_TARGETS.find(({ selector }) => selector === row?.selector);
    if (!fixed || seen.has(row.selector)) {
      throw new Error("generated CLI release table contains an invalid or duplicate selector");
    }
    seen.add(row.selector);
    for (const key of ["target", "package", "entry", "os", "cpu", "artifactKind", "runner"]) {
      if (row[key] !== fixed[key]) throw new Error(`generated CLI release table has wrong ${key}`);
    }
    if (row.version !== packageVersion || !/^[0-9a-f]{64}$/.test(row.sha256)) {
      throw new Error("generated CLI release table has invalid artifact identity");
    }
    for (const key of ["cargoLockSha256", "workflowRevision", "toolchain", "builderRevision"]) {
      if (typeof row[key] !== "string" || row[key] === "") {
        throw new Error(`generated CLI release table has incomplete ${key}`);
      }
    }
  }
  return table;
}

function containedBinary(packageRoot, entry, realpath) {
  if (typeof entry !== "string" || entry === "" || isAbsolute(entry)) {
    throw new Error("CLI entry must be a non-empty relative path");
  }
  const candidate = resolve(packageRoot, entry);
  const lexical = relative(packageRoot, candidate);
  if (lexical === ".." || lexical.startsWith(`..${sep}`) || isAbsolute(lexical)) {
    throw new Error("CLI entry escapes its package root");
  }
  const realRoot = realpath(packageRoot);
  const realEntry = realpath(candidate);
  const physical = relative(realRoot, realEntry);
  if (physical === ".." || physical.startsWith(`..${sep}`) || isAbsolute(physical)) {
    throw new Error("CLI entry escapes its package root through a symlink");
  }
  return realEntry;
}

function validateFacade(manifest, expectedVersion) {
  if (!isRecord(manifest)) {
    throw new Error("bamti-cli facade manifest is not a record");
  }
  if (manifest.name !== "bamti-cli") {
    throw new Error(`bamti-cli facade manifest has name ${manifest.name}, expected bamti-cli`);
  }
  if (manifest.version !== expectedVersion) {
    throw new Error(
      `bamti-cli facade manifest version ${manifest.version} does not match expected ${expectedVersion}`,
    );
  }
  if (!isRecord(manifest.engines) || manifest.engines.node !== ">=24") {
    throw new Error("bamti-cli facade manifest must require Node >=24");
  }
  const optional = manifest.optionalDependencies;
  if (!isRecord(optional)) {
    throw new Error("bamti-cli facade manifest is missing optionalDependencies");
  }
  const expectedPackages = CLI_TARGETS.map(({ package: p }) => p).sort();
  const actualPackages = Object.keys(optional).sort();
  if (JSON.stringify(expectedPackages) !== JSON.stringify(actualPackages)) {
    throw new Error("bamti-cli facade optionalDependencies do not match CLI target packages");
  }
  for (const packageName of expectedPackages) {
    if (optional[packageName] !== expectedVersion) {
      throw new Error(
        `bamti-cli facade optionalDependency ${packageName} is pinned to ${optional[packageName]}, expected ${expectedVersion}`,
      );
    }
  }
}

function defaultTable() {
  const manifest = JSON.parse(
    readFileSync(new URL("./package.json", import.meta.url), "utf8"),
  );
  const table = JSON.parse(
    readFileSync(new URL("./cli-release-table.json", import.meta.url), "utf8"),
  );
  return { manifest, table };
}

const stagedBinaries = new Map();

function cleanupStaged(stagedPath) {
  const directory = stagedBinaries.get(stagedPath);
  if (directory === undefined) return;
  stagedBinaries.delete(stagedPath);
  try {
    unlinkSync(stagedPath);
  } catch {
    // Best-effort: the child may still hold the file on Windows.
  }
  try {
    rmdirSync(directory);
  } catch {
    // Best-effort cleanup.
  }
}

function stageVerifiedBinary(bytes, platform, options) {
  const mkdtemp = options.mkdtemp ?? mkdtempSync;
  const writeFile = options.writeFile ?? writeFileSync;
  const chmod = options.chmod ?? chmodSync;
  const directory = mkdtemp(join(tmpdir(), "bamti-cli-"));
  if (platform !== "win32") chmod(directory, 0o700);
  const binaryName = platform === "win32" ? "bamts.exe" : "bamts";
  const stagedPath = join(directory, binaryName);
  writeFile(stagedPath, bytes, { flag: "wx", mode: 0o755 });
  if (platform !== "win32") chmod(stagedPath, 0o755);
  return stagedPath;
}

export function artifactPackage(platform = process.platform, arch = process.arch) {
  const packageName = ARTIFACTS.get(`${platform}-${arch}`);
  if (!packageName) throw new UnsupportedPlatformError(platform, arch);
  return packageName;
}

export function resolveBinary(options = {}) {
  const platform = options.platform ?? process.platform;
  const arch = options.arch ?? process.arch;
  const nodeVersion = options.nodeVersion ?? process.versions.node;
  const major = Number.parseInt(nodeVersion.split(".", 1)[0], 10);
  if (!Number.isInteger(major) || major < 24) {
    throw new ArtifactLoadError("bamti-cli", "unknown", new Error("Node >=24 is required"));
  }
  const packageName = artifactPackage(platform, arch);

  let defaults;
  if (options.table === undefined) {
    try {
      defaults = defaultTable();
    } catch (cause) {
      throw new ArtifactLoadError("bamti-cli", "unknown", cause);
    }
  }
  const facadeManifest = options.facadeManifest ?? defaults?.manifest;
  if (!isRecord(facadeManifest)) {
    throw new ArtifactLoadError("bamti-cli", "unknown", new Error("missing bamti-cli facade manifest"));
  }
  const expectedVersion = facadeManifest.version;

  let table;
  try {
    validateFacade(facadeManifest, expectedVersion);
    table = validateTable(options.table ?? defaults?.table, expectedVersion);
  } catch (cause) {
    throw new ArtifactLoadError("bamti-cli", expectedVersion ?? "unknown", cause);
  }

  const row = table.targets.find((target) => target.os === platform && target.cpu === arch);
  if (!row) throw new UnsupportedPlatformError(platform, arch);

  const resolvePackage = options.resolvePackage ?? requireFromHere.resolve;
  let manifestPath;
  try {
    manifestPath = resolvePackage(`${packageName}/package.json`);
  } catch (cause) {
    throw new ArtifactNotFoundError(platform, arch, packageName, cause);
  }
  if (!isAbsolute(manifestPath)) {
    throw new ArtifactLoadError(packageName, row.version, new Error("resolved package manifest path must be absolute"));
  }

  try {
    const manifest = JSON.parse(readFileSync(manifestPath, "utf8"));
    const metadata = manifest.bamtiCli;
    if (
      manifest.name !== row.package ||
      manifest.version !== row.version ||
      manifest.engines?.node !== ">=24" ||
      manifest.os?.length !== 1 || manifest.os[0] !== row.os ||
      manifest.cpu?.length !== 1 || manifest.cpu[0] !== row.cpu ||
      !isRecord(metadata) ||
      metadata.entry !== row.entry || metadata.target !== row.target ||
      metadata.artifactKind !== row.artifactKind || metadata.sha256 !== row.sha256 ||
      metadata.runner !== row.runner || !equalRelease(metadata.release, table.release)
    ) {
      throw new Error("CLI package metadata does not match release table");
    }
    for (const key of ["cargoLockSha256", "workflowRevision", "toolchain", "builderRevision"]) {
      if (metadata[key] !== row[key]) throw new Error(`CLI package ${key} does not match release table`);
    }
    const binary = containedBinary(dirname(manifestPath), row.entry, options.realpath ?? realpathSync);
    const bytes = (options.readFile ?? readFileSync)(binary);
    const digest = createHash("sha256").update(bytes).digest("hex");
    if (digest !== row.sha256) throw new Error("CLI binary SHA-256 does not match release table");
    (options.access ?? accessSync)(binary, platform === "win32" ? constants.F_OK : constants.X_OK);
    const stagedPath = stageVerifiedBinary(bytes, platform, options);
    stagedBinaries.set(stagedPath, dirname(stagedPath));
    return stagedPath;
  } catch (cause) {
    throw new ArtifactLoadError(packageName, row.version, cause);
  }
}

export function run(args = [], options = {}) {
  if (!Array.isArray(args)) {
    throw new TypeError("bamti-cli run() expects an array of command-line arguments.");
  }
  const binary = resolveBinary(options);
  const spawnFn = options.spawn ?? spawn;
  return new Promise((resolveCode, reject) => {
    let child;
    try {
      child = spawnFn(binary, args, {
        cwd: options.cwd,
        env: options.env,
        stdio: options.stdio ?? "inherit",
      });
    } catch (error) {
      cleanupStaged(binary);
      reject(error);
      return;
    }
    const cleanup = () => cleanupStaged(binary);
    child.once("error", (error) => {
      cleanup();
      reject(error);
    });
    child.once("exit", (code) => {
      cleanup();
      resolveCode(code ?? 1);
    });
  });
}
