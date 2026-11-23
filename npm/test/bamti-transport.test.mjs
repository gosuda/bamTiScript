import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { EventEmitter } from "node:events";
import { readFile } from "node:fs/promises";
import { registerHooks } from "node:module";
import { PassThrough } from "node:stream";
import test from "node:test";

import { FrameDecoder, encodeFrame } from "../bamti/internal/framing.js";

registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === "bamti-cli") {
      return {
        shortCircuit: true,
        url: new URL("../bamti-cli/index.js", import.meta.url).href,
      };
    }
    return nextResolve(specifier, context);
  },
});

const { Transport } = await import("../bamti/internal/transport.js");
const { runExecutable } = await import("../bamti/native-runner.js");
const api = await import("../bamti/index.js");
const { SERVICE_METHODS } = await import("../bamti/internal/session.js");
const { createAsyncService } = await import("../bamti/unstable/async.js");
const { createSerialService } = await import("../bamti/unstable/sync.js");

const PUBLIC_EXPORTS = [
  ".",
  "./unstable/sync",
  "./unstable/async",
  "./unstable/fs",
  "./unstable/proto",
  "./unstable/ast",
  "./unstable/ast/is",
  "./unstable/ast/factory",
  "./unstable/ast/utils",
  "./unstable/ast/scanner",
  "./unstable/ast/visitor",
  "./unstable/ast/clone",
  "./package.json",
];

class FakeChild extends EventEmitter {
  constructor() {
    super();
    this.stdin = new PassThrough();
    this.stdout = new PassThrough();
    this.stderr = new PassThrough();
    this.exitCode = null;
    this.signalCode = null;
  }

  kill(signal = "SIGTERM") {
    this.signalCode = signal;
    queueMicrotask(() => {
      this.emit("exit", this.exitCode, this.signalCode);
      this.emit("close", this.exitCode, this.signalCode);
    });
    return true;
  }
}

function requestCollector(child) {
  const decoder = new FrameDecoder();
  const requests = [];
  child.stdin.on("data", (chunk) => requests.push(...decoder.push(chunk)));
  return requests;
}

function requestFixture() {
  const children = [];
  const requests = [];
  const decoder = new FrameDecoder();
  const transport = new Transport({
    binary: "/virtual/bamts",
    disposeTimeoutMs: 0,
    spawnChild() {
      const child = new FakeChild();
      child.stdin.on("data", (chunk) => requests.push(...decoder.push(chunk)));
      children.push(child);
      return child;
    },
  });
  return { transport, children, requests };
}

async function awaitRequests(requests, count) {
  while (requests.length < count) {
    await new Promise((resolve) => setImmediate(resolve));
  }
}

test("manifest publishes thirteen subpaths and the tsc executable", async () => {
  const manifest = JSON.parse(
    await readFile(new URL("../bamti/package.json", import.meta.url), "utf8"),
  );
  assert.deepEqual(Object.keys(manifest.exports), PUBLIC_EXPORTS);
  assert.deepEqual(manifest.bin, { tsc: "native-runner.js" });
  assert.ok(manifest.files.includes(manifest.bin.tsc));
  assert.equal(typeof api.createSession, "function");
});

test("persistent transport correlates fragmented out-of-order responses", async () => {
  const children = [];
  const transport = new Transport({
    binary: "/virtual/bamts",
    disposeTimeoutMs: 0,
    spawnChild() {
      const child = new FakeChild();
      children.push(child);
      return child;
    },
  });

  transport.ready();
  assert.equal(children.length, 1);
  const requests = requestCollector(children[0]);

  const first = transport.request("service/snapshot", { label: "first" });
  const second = transport.request("service/snapshot", { label: "second" });
  const third = transport.request("service/snapshot", { label: "third" });
  const fourth = transport.request("service/snapshot", { label: "fourth" });
  await new Promise((resolve) => setImmediate(resolve));
  assert.deepEqual(
    requests.map(({ method }) => method),
    Array(4).fill("service/snapshot"),
  );

  const combined = Buffer.concat([
    encodeFrame({ jsonrpc: "2.0", id: requests[3].id, result: "四" }),
    encodeFrame({ jsonrpc: "2.0", id: requests[2].id, result: "three" }),
  ]);
  children[0].stdout.write(combined.subarray(0, 7));
  children[0].stdout.write(combined.subarray(7, combined.length - 2));
  children[0].stdout.write(combined.subarray(combined.length - 2));

  assert.deepEqual(await Promise.all([third, fourth]), ["three", "四"]);
  assert.equal(transport.inFlight, 2);

  const firstCrash = assert.rejects(first, { name: "TransportCrashError", code: 9 });
  const secondCrash = assert.rejects(second, { name: "TransportCrashError", code: 9 });
  children[0].emit("exit", 9, null);
  children[0].emit("close", 9, null);
  await Promise.all([firstCrash, secondCrash]);
  assert.equal(transport.inFlight, 0);
  await transport.dispose();
});

test("transport accepts the last response after process exit until stdio closes", async () => {
  const { transport, children, requests } = requestFixture();
  const outcome = transport.request("compiler/version").then(
    (value) => ({ value }),
    (error) => ({ error }),
  );
  try {
    children[0].exitCode = 0;
    children[0].emit("exit", 0, null);
    children[0].stdout.write(encodeFrame({ id: requests[0].id, result: "7.0.2" }));
    children[0].emit("close", 0, null);
    assert.deepEqual(await outcome, { value: "7.0.2" });
  } finally {
    await transport.dispose();
  }
});

test("real child output buffered until exit still resolves its request", { timeout: 5000 }, async () => {
  const transport = new Transport({
    binary: process.execPath,
    spawnChild(binary, _args, options) {
      const script = `
        process.stdin.once("data", () => {
          const body = JSON.stringify({ id: 1, result: "final response" });
          process.stdout.write("Content-Length: " + Buffer.byteLength(body) + "\\r\\n\\r\\n" + body);
          process.stdin.destroy();
        });
      `;
      const child = spawn(binary, ["--input-type=module", "-e", script], options);
      child.stdout.pause();
      child.once("exit", () => child.stdout.resume());
      return child;
    },
  });
  try {
    assert.equal(await transport.request("compiler/version"), "final response");
  } finally {
    await transport.dispose();
  }
});

for (const mode of ["crash", "disposal"]) {
  test(`${mode} releases inherited compiler pipes after process exit`, { timeout: 5000 }, async () => {
    let close;
    let exited;
    let timer;
    const transport = new Transport({
      binary: process.execPath,
      disposeTimeoutMs: 20,
      spawnChild(binary, _args, options) {
        const finish = mode === "disposal"
          ? `const body = JSON.stringify({ id: 1, result: "ready" });
             process.stdout.write("Content-Length: " + Buffer.byteLength(body) + "\\r\\n\\r\\n" + body,
               () => process.exit(0));`
          : "process.exit(0);";
        const script = `
          import { spawn } from "node:child_process";
          process.stdin.once("data", () => {
            spawn(process.execPath, ["-e", "setTimeout(() => {}, 2000)"], {
              stdio: "inherit",
            }).unref();
            ${finish}
          });
        `;
        const child = spawn(binary, ["--input-type=module", "-e", script], options);
        close = new Promise((resolve) => child.once("close", resolve));
        exited = new Promise((resolve) => child.once("exit", resolve));
        return child;
      },
    });
    try {
      const request = transport.request("compiler/version");
      if (mode === "disposal") {
        assert.equal(await request, "ready");
      } else {
        await assert.rejects(request, { name: "TransportCrashError" });
      }
      await exited;
      await transport.dispose();
      await Promise.race([
        close,
        new Promise((_, reject) => {
          timer = setTimeout(() => reject(new Error("compiler pipes stayed open")), 500);
        }),
      ]);
    } finally {
      clearTimeout(timer);
      await transport.dispose();
      await close;
    }
  });
}

test("clean stdout EOF rejects pending requests while the child remains alive", { timeout: 5000 }, async () => {
  let child;
  const transport = new Transport({
    binary: process.execPath,
    disposeTimeoutMs: 20,
    spawnChild(binary, _args, options) {
      const script = `
        process.stdin.once("data", () => process.stdout.end());
        setTimeout(() => process.exit(0), 1000);
      `;
      child = spawn(binary, ["--input-type=module", "-e", script], options);
      return child;
    },
  });
  try {
    await assert.rejects(transport.request("compiler/version"), { name: "TransportCrashError" });
    assert.equal(child.killed, true, "a child without a response stream must be terminated");
  } finally {
    await transport.dispose();
    child?.kill("SIGKILL");
  }
});

test("a valid service error keeps the transport available for the next request", async () => {
  const { transport, children, requests } = requestFixture();
  try {
    const rejected = assert.rejects(transport.request("service/rename"), {
      name: "ServiceRequestError",
      code: -32602,
      method: "service/rename",
      data: { position: 2 },
    });
    children[0].stdout.write(encodeFrame({
      id: requests[0].id,
      error: { code: -32602, message: "invalid position", data: { position: 2 } },
    }));
    await rejected;
    const next = transport.request("compiler/version");
    children[0].stdout.write(encodeFrame({ id: requests[1].id, result: "7.0.2" }));
    assert.equal(await next, "7.0.2");
    assert.equal(children.length, 1);
  } finally {
    await transport.dispose();
  }
});

test("truncated stdout rejects pending requests and terminates the broken child", async () => {
  const { transport, children } = requestFixture();
  const outcome = transport.request("compiler/version").catch((error) => error);
  try {
    children[0].stdout.end("Content-Length: 20\r\n\r\n{");
    await new Promise((resolve) => setImmediate(resolve));
    assert.equal(transport.inFlight, 0);
    assert.equal((await outcome).name, "ProtocolError");
    assert.notEqual(children[0].signalCode, null);
  } finally {
    await transport.dispose();
  }
});

test("transport keeps stderr within its process generation", async () => {
  const { transport, children } = requestFixture();
  const first = transport.request("compiler/version").catch((error) => error);
  children[0].stderr.write("first process\n");
  children[0].emit("error", new Error("first process failed"));
  assert.equal((await first).stderr, "first process\n");
  const second = transport.request("compiler/version").catch((error) => error);
  try {
    children[0].stderr.write("late first process\n");
    children[1].stderr.write("second process\n");
    children[1].emit("error", new Error("second process failed"));
    assert.equal((await second).stderr, "second process\n");
    assert.notEqual(children[0].signalCode, null);
    assert.notEqual(children[1].signalCode, null);
  } finally {
    await transport.dispose();
  }
});

test("invalid frame limits fail before a child is spawned", async () => {
  let spawned = 0;
  const transport = new Transport({
    binary: "/virtual/bamts",
    maxFrameBytes: 0,
    disposeTimeoutMs: 0,
    spawnChild() {
      spawned += 1;
      return new FakeChild();
    },
  });
  try {
    await assert.rejects(transport.request("compiler/version"), RangeError);
    assert.equal(spawned, 0);
  } finally {
    await transport.dispose();
  }
});

test("malformed error responses reject requests without escaping a stream listener", async () => {
  for (const error of [
    null,
    false,
    "failure",
    [],
    { code: false, message: "bad" },
    { code: {}, message: "bad" },
    { code: -32004, message: null },
  ]) {
    const { transport, children, requests } = requestFixture();
    const outcome = transport.request("compiler/version").catch((failure) => failure);
    try {
      assert.doesNotThrow(() => {
        children[0].stdout.write(encodeFrame({ id: requests[0].id, error }));
      });
      assert.equal((await outcome).name, "ProtocolError");
    } finally {
      await transport.dispose();
    }
  }
});

test("service error codes preserve their public types and keep the transport usable", async () => {
  for (const code of ["E_SERVICE", -32004, 1.5, null, undefined]) {
    const { transport, children, requests } = requestFixture();
    try {
      const outcome = transport.request("compiler/version").catch((error) => error);
      children[0].stdout.write(encodeFrame({
        id: requests[0].id,
        error: { code, message: "rejected", data: { retry: true } },
      }));
      const error = await outcome;
      assert.ok(error instanceof api.ServiceRequestError);
      assert.equal(error.code, code ?? null);
      assert.equal(error.method, "compiler/version");
      assert.deepEqual(error.data, { retry: true });

      const next = transport.request("compiler/version");
      children[0].stdout.write(encodeFrame({ id: requests[1].id, result: "ready" }));
      assert.equal(await next, "ready");
      assert.equal(children.length, 1);
    } finally {
      await transport.dispose();
    }
  }
});

test("frame headers reject bytes that ASCII decoding would silently change", () => {
  for (const offset of [0, 16]) {
    const frame = encodeFrame({ id: 1, result: true });
    frame[offset] |= 0x80;
    assert.throws(() => new FrameDecoder().push(frame), { name: "ProtocolError" });
  }
});

test("session publishes exactly the ten service methods including quickInfo", () => {
  assert.deepEqual(SERVICE_METHODS, [
    "open",
    "update",
    "close",
    "snapshot",
    "completions",
    "definition",
    "quickInfo",
    "references",
    "rename",
    "diagnostics",
  ]);
});

test("session quickInfo returns the populated symbol description over service/quickInfo", async () => {
  const { transport, children, requests } = requestFixture();
  const session = new api.Session({ transport });
  try {
    const pending = session.quickInfo({ path: "input.ts", position: 6 });
    await awaitRequests(requests, 1);
    children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: requests[0].id,
        result: { root: "/virtual", methods: [...SERVICE_METHODS] },
      }),
    );
    await awaitRequests(requests, 2);
    assert.deepEqual(
      requests.map(({ method }) => method),
      ["initialize", "service/quickInfo"],
    );
    assert.deepEqual(requests[1].params, { path: "input.ts", position: 6 });
    children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: requests[1].id,
        result: {
          name: "answer",
          kind: "const",
          typeDisplay: "42",
          display: "const answer: 42",
          range: { start: 6, end: 12 },
        },
      }),
    );
    assert.deepEqual(await pending, {
      name: "answer",
      kind: "const",
      typeDisplay: "42",
      display: "const answer: 42",
      range: { start: 6, end: 12 },
    });
  } finally {
    await transport.dispose();
  }
});

test("session quickInfo resolves null when no symbol sits under the position", async () => {
  const { transport, children, requests } = requestFixture();
  const session = new api.Session({ transport });
  try {
    const pending = session.quickInfo({ path: "input.ts", position: 0 });
    await awaitRequests(requests, 1);
    children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: requests[0].id,
        result: { root: "/virtual", methods: [...SERVICE_METHODS] },
      }),
    );
    await awaitRequests(requests, 2);
    assert.equal(requests[1].method, "service/quickInfo");
    assert.deepEqual(requests[1].params, { path: "input.ts", position: 0 });
    children[0].stdout.write(
      encodeFrame({ jsonrpc: "2.0", id: requests[1].id, result: null }),
    );
    assert.equal(await pending, null);
  } finally {
    await transport.dispose();
  }
});

test("async and serial services wire quickInfo with the exact method name and request shape", async () => {
  const asyncFixture = requestFixture();
  const serialFixture = requestFixture();
  const asyncService = createAsyncService({ transport: asyncFixture.transport });
  const serialService = createSerialService({ transport: serialFixture.transport });
  try {
    const asyncPending = asyncService.quickInfo({ path: "input.ts", position: 6 });
    const serialPending = serialService.quickInfo({ path: "input.ts", position: 6 });
    await awaitRequests(asyncFixture.requests, 1);
    await awaitRequests(serialFixture.requests, 1);
    asyncFixture.children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: asyncFixture.requests[0].id,
        result: { root: "/virtual", methods: [...SERVICE_METHODS] },
      }),
    );
    serialFixture.children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: serialFixture.requests[0].id,
        result: { root: "/virtual", methods: [...SERVICE_METHODS] },
      }),
    );
    await awaitRequests(asyncFixture.requests, 2);
    await awaitRequests(serialFixture.requests, 2);
    assert.deepEqual(
      asyncFixture.requests.map(({ method }) => method),
      ["initialize", "service/quickInfo"],
    );
    assert.deepEqual(
      serialFixture.requests.map(({ method }) => method),
      ["initialize", "service/quickInfo"],
    );
    assert.deepEqual(asyncFixture.requests[1].params, {
      path: "input.ts",
      position: 6,
      async: true,
    });
    assert.deepEqual(serialFixture.requests[1].params, { path: "input.ts", position: 6 });
    asyncFixture.children[0].stdout.write(
      encodeFrame({
        jsonrpc: "2.0",
        id: asyncFixture.requests[1].id,
        result: {
          name: "answer",
          kind: "const",
          typeDisplay: "42",
          display: "const answer: 42",
          range: { start: 6, end: 12 },
        },
      }),
    );
    serialFixture.children[0].stdout.write(
      encodeFrame({ jsonrpc: "2.0", id: serialFixture.requests[1].id, result: null }),
    );
    assert.deepEqual(await asyncPending, {
      name: "answer",
      kind: "const",
      typeDisplay: "42",
      display: "const answer: 42",
      range: { start: 6, end: 12 },
    });
    assert.equal(await serialPending, null);
  } finally {
    await asyncService.dispose();
    await serialService.dispose();
  }
});

test("tsc executable forwards arguments and records the CLI exit status", async () => {
  const stderr = new PassThrough();
  const processObject = { stderr, exitCode: undefined };
  let invocation;
  const exitCode = await runExecutable(["--version"], {
    process: processObject,
    runCli(args, options) {
      invocation = { args, options };
      return 7;
    },
  });

  assert.equal(exitCode, 7);
  assert.equal(processObject.exitCode, 7);
  assert.deepEqual(invocation, { args: ["--version"], options: { stdio: "inherit" } });
});
