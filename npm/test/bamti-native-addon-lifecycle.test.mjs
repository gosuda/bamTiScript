import assert from "node:assert/strict";
import { once } from "node:events";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import test from "node:test";
import { Worker } from "node:worker_threads";

const addonPath = process.env.BAMTI_NATIVE_ADDON_PATH;
const expectedSourceCommit = process.env.BAMTI_EXPECTED_SOURCE_COMMIT;
const expectedBuildSetId = process.env.BAMTI_EXPECTED_BUILD_SET_ID;
if (
  addonPath !== undefined &&
  (expectedSourceCommit === undefined || expectedBuildSetId === undefined)
) {
  throw new Error(
    "BAMTI_EXPECTED_SOURCE_COMMIT and BAMTI_EXPECTED_BUILD_SET_ID are required with BAMTI_NATIVE_ADDON_PATH",
  );
}
const nativeTest = { skip: addonPath === undefined };

function request(args) {
  return {
    args: args.map((argument) => Buffer.from(argument)),
    cwd: Buffer.from(process.cwd()),
    env: Object.entries(process.env)
      .filter(([, value]) => value !== undefined)
      .map(([name, value]) => Buffer.from(`${name}=${value}`)),
  };
}

function deadline(promise, milliseconds, label) {
  let timer;
  return Promise.race([
    promise,
    new Promise((_, reject) => {
      timer = setTimeout(
        () => reject(new Error(`${label} exceeded ${milliseconds} ms`)),
        milliseconds,
      );
    }),
  ]).finally(() => clearTimeout(timer));
}

async function runWorker(path) {
  const source = `
    import { createRequire } from "node:module";
    import { parentPort, workerData } from "node:worker_threads";
    const loadAddon = createRequire(workerData.baseUrl);
    const addon = loadAddon(workerData.addonPath);
    const request = {
      args: [Buffer.from("--version")],
      cwd: Buffer.from(workerData.cwd),
      env: workerData.env.map((entry) => Buffer.from(entry)),
    };
    addon.run(request).then(
      (outcome) => parentPort.postMessage({
        exports: Object.keys(addon).sort(),
        metadata: addon.releaseMetadata(),
        outcome: {
          exitCode: outcome.exitCode,
          stdout: Buffer.from(outcome.stdout).toString("utf8"),
          stderr: Buffer.from(outcome.stderr).toString("utf8"),
        },
      }),
      (error) => { throw error; },
    );
  `;
  const worker = new Worker(
    new URL(`data:text/javascript,${encodeURIComponent(source)}`),
    {
      type: "module",
      workerData: {
        addonPath: resolve(path),
        baseUrl: import.meta.url,
        cwd: process.cwd(),
        env: Object.entries(process.env)
          .filter(([, value]) => value !== undefined)
          .map(([name, value]) => `${name}=${value}`),
      },
    },
  );
  const exit = once(worker, "exit");
  const result = await new Promise((resolveMessage, rejectMessage) => {
    worker.once("message", resolveMessage);
    worker.once("error", rejectMessage);
    worker.once("exit", (exitCode) => {
      if (exitCode !== 0) {
        rejectMessage(new Error(`native addon worker exited with code ${exitCode}`));
        return;
      }
      rejectMessage(new Error("native addon worker exited before posting a result"));
    });
  });
  const [exitCode] = await exit;
  assert.equal(exitCode, 0);
  return result;
}

test("actual addon exposes the closed API and executes the buffered CLI", nativeTest, async () => {
  const loadAddon = createRequire(import.meta.url);
  const addon = loadAddon(resolve(addonPath));
  assert.deepEqual(Object.keys(addon).sort(), ["releaseMetadata", "run"]);

  const metadata = addon.releaseMetadata();
  assert.equal(metadata.artifactKind, "native-addon");
  assert.equal(metadata.nativeAbi, 1);
  assert.equal(metadata.cliProtocol, 1);
  assert.equal(metadata.packageVersion, "0.2.0");
  assert.equal(metadata.sourceCommit, expectedSourceCommit);
  assert.equal(metadata.buildSetId, expectedBuildSetId);
  assert.match(metadata.buildSetId, /^[0-9a-f]{64}$/);
  assert.equal(
    metadata.releaseId,
    `bamti/${metadata.packageVersion}/${metadata.sourceCommit}/native-abi-${metadata.nativeAbi}/cli-protocol-${metadata.cliProtocol}/${metadata.buildSetId}`,
  );

  const outcome = await addon.run(request(["--version"]));
  assert.equal(outcome.exitCode, 0);
  assert.equal(Buffer.from(outcome.stdout).toString("utf8"), "bamts 0.2.0\n");
  assert.equal(Buffer.from(outcome.stderr).length, 0);
  assert.equal(outcome.truncation, undefined);

  await assert.rejects(
    addon.run({ ...request([]), env: [Buffer.from("MISSING_EQUALS")] }),
    /environment entry must contain '='/,
  );
});

test("actual Intel macOS addon compiles and executes AOT", {
  skip: addonPath === undefined || process.platform !== "darwin" || process.arch !== "x64",
}, async () => {
  const directory = await mkdtemp(join(tmpdir(), "bamti-napi-aot-"));
  try {
    const entrypoint = join(directory, "main.ts");
    await writeFile(entrypoint, 'process.stdout.write("42\\n");\n');
    const addon = createRequire(import.meta.url)(resolve(addonPath));
    const outcome = await addon.run(request(["run", "--target", "aot", entrypoint]));
    assert.equal(outcome.exitCode, 0, Buffer.from(outcome.stderr).toString("utf8"));
    assert.equal(Buffer.from(outcome.stdout).toString("utf8"), "42\n");
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
});

test("actual addon exports structured truncation for capped JSON diagnostics", nativeTest, async () => {
  const directory = await mkdtemp(join(tmpdir(), "bamti-napi-truncation-"));
  try {
    const entrypoint = join(directory, "main.ts");
    await writeFile(
      entrypoint,
      "const first: string = 1;\nconst second: string = 2;\n",
    );
    const loadAddon = createRequire(import.meta.url);
    const addon = loadAddon(resolve(addonPath));

    const complete = await addon.run(request(["check", "--json", entrypoint]));
    assert.equal(complete.exitCode, 1);
    assert.equal(complete.truncation, undefined);
    const diagnostics = JSON.parse(Buffer.from(complete.stderr).toString("utf8"));
    assert.ok(Array.isArray(diagnostics));
    assert.ok(diagnostics.length > 1);

    const outcome = await addon.run(
      request(["check", "--json", "--error-limit", "1", entrypoint]),
    );

    assert.equal(outcome.exitCode, 1);
    assert.deepEqual(
      JSON.parse(Buffer.from(outcome.stderr).toString("utf8")),
      diagnostics.slice(0, 1),
    );
    assert.deepEqual(outcome.truncation, {
      elided: diagnostics.length - 1,
      limit: 1,
    });

    const exact = await addon.run(
      request(["check", "--json", "--error-limit", String(diagnostics.length), entrypoint]),
    );
    assert.equal(exact.exitCode, 1);
    assert.deepEqual(
      JSON.parse(Buffer.from(exact.stderr).toString("utf8")),
      diagnostics,
    );
    assert.equal(exact.truncation, undefined);
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
});

test("actual addon unloads cleanly across worker environments", nativeTest, async () => {
  for (let index = 0; index < 8; index += 1) {
    const result = await runWorker(addonPath);
    assert.deepEqual(result.exports, ["releaseMetadata", "run"]);
    assert.equal(result.metadata.artifactKind, "native-addon");
    assert.equal(result.metadata.nativeAbi, 1);
    assert.equal(result.metadata.cliProtocol, 1);
    assert.equal(result.outcome.exitCode, 0);
    assert.equal(result.outcome.stdout, "bamts 0.2.0\n");
    assert.equal(result.outcome.stderr, "");
  }
});

test("active native invocation cancels on worker teardown and reloads", {
  ...nativeTest,
  timeout: 10_000,
}, async () => {
  const directory = await mkdtemp(join(tmpdir(), "bamti-napi-active-"));
  const entrypoint = join(directory, "busy.ts");
  await writeFile(entrypoint, "setTimeout(() => {}, 60_000);\n");

  const source = `
    import { createRequire } from "node:module";
    import { parentPort, workerData } from "node:worker_threads";
    const addon = createRequire(workerData.baseUrl)(workerData.addonPath);
    const makeRequest = (args) => ({
      args: args.map((value) => Buffer.from(value)),
      cwd: Buffer.from(workerData.cwd),
      env: workerData.env.map((value) => Buffer.from(value)),
    });

    const active = addon.run(makeRequest(["run", "--target", "jit", workerData.entrypoint]));
    const settled = await Promise.race([
      active.then(
        (outcome) => ({
          exitCode: outcome.exitCode,
          stdout: Buffer.from(outcome.stdout).toString("utf8"),
          stderr: Buffer.from(outcome.stderr).toString("utf8"),
        }),
        (error) => ({ error: String(error?.message) }),
      ),
      new Promise((resolveDelay) => setTimeout(() => resolveDelay(undefined), 100)),
    ]);
    if (settled !== undefined) {
      throw new Error(\`active invocation settled before teardown: \${JSON.stringify(settled)}\`);
    }
    void addon.run(makeRequest(["--version"]));
    void addon.run(makeRequest(["--version"]));
    try {
      await addon.run(makeRequest(["--version"]));
      throw new Error("expected queue saturation");
    } catch (error) {
      if (!/queue is full/i.test(String(error?.message))) throw error;
      parentPort.postMessage("saturated");
    }
    await new Promise(() => {});
  `;
  const worker = new Worker(
    new URL(`data:text/javascript,${encodeURIComponent(source)}`),
    {
      type: "module",
      workerData: {
        addonPath: resolve(addonPath),
        baseUrl: import.meta.url,
        cwd: directory,
        entrypoint,
        env: Object.entries(process.env)
          .filter(([, value]) => value !== undefined)
          .map(([name, value]) => `${name}=${value}`),
      },
    },
  );
  const workerError = once(worker, "error").then(([error]) => Promise.reject(error));
  let terminated = false;

  try {
    await deadline(
      Promise.race([once(worker, "message"), workerError]),
      5_000,
      "native queue saturation",
    );
    await deadline(worker.terminate(), 2_000, "active N-API environment teardown");
    terminated = true;

    const reloaded = await deadline(
      runWorker(addonPath),
      5_000,
      "post-teardown reload",
    );
    assert.deepEqual(reloaded.exports, ["releaseMetadata", "run"]);
    assert.equal(reloaded.outcome.exitCode, 0);
    assert.equal(reloaded.outcome.stdout, "bamts 0.2.0\n");
    assert.equal(reloaded.metadata.sourceCommit, expectedSourceCommit);
    assert.equal(reloaded.metadata.buildSetId, expectedBuildSetId);
  } finally {
    if (!terminated) {
      await deadline(worker.terminate(), 2_000, "failed-test N-API environment teardown");
    }
    await rm(directory, { recursive: true, force: true });
  }
});
