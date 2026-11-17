import assert from "node:assert/strict";
import { EventEmitter } from "node:events";
import { PassThrough } from "node:stream";
import test from "node:test";
import "./oracle-support.mjs";

const proto = await import("../bamti/unstable/proto.js");
const pinnedProto = await import("typescript/unstable/proto");

const ERROR_NAMES = [
  "BamtiError",
  "DisposedError",
  "ProtocolError",
  "RestartLimitError",
  "ServiceRequestError",
  "TransportBusyError",
  "TransportCrashError",
];

function fakeChild() {
  const child = new EventEmitter();
  child.stdin = new PassThrough();
  child.stdout = new PassThrough();
  child.stderr = new PassThrough();
  child.exitCode = null;
  child.signalCode = null;
  child.kill = () => true;
  return child;
}

test("package shape: ./unstable/proto declares the framing, transport, and error surface; the pinned typescript/unstable/proto exports only resolveFileName, resolveDocumentURI, and toUpdateSnapshotRequest, so these names have no pinned runtime counterpart (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(proto).sort(), [
    "BamtiError", "DisposedError", "FrameDecoder", "MAX_FRAME_BYTES", "MAX_HEADER_BYTES",
    "ProtocolError", "RestartLimitError", "ServiceRequestError", "Transport",
    "TransportBusyError", "TransportCrashError", "encodeFrame",
  ]);
  assert.deepStrictEqual(Object.keys(pinnedProto).sort(), [
    "resolveDocumentURI",
    "resolveFileName",
    "toUpdateSnapshotRequest",
  ]);
});

test("proto error classes form the documented BamtiError hierarchy", () => {
  for (const name of ERROR_NAMES) {
    assert.ok(typeof proto[name] === "function" && proto[name].prototype instanceof Error, name);
  }
  for (const name of ERROR_NAMES.slice(1)) {
    assert.ok(proto[name].prototype instanceof proto.BamtiError, `${name} extends BamtiError`);
  }
});

test("proto.MAX_HEADER_BYTES and proto.MAX_FRAME_BYTES carry the documented bounds", () => {
  assert.strictEqual(proto.MAX_HEADER_BYTES, 8 * 1024);
  assert.strictEqual(proto.MAX_FRAME_BYTES, 32 * 1024 * 1024);
});

test("proto.encodeFrame emits the documented Content-Length wire format and FrameDecoder round-trips it", () => {
  const message = { id: 3, method: "service/snapshot", params: { path: "a.ts" } };
  const body = JSON.stringify(message);
  const header = `Content-Length: ${Buffer.byteLength(body)}\r\n\r\n`;
  const bytes = Buffer.from(proto.encodeFrame(message));
  assert.strictEqual(bytes.subarray(0, header.length).toString("latin1"), header);
  assert.deepStrictEqual(JSON.parse(bytes.subarray(header.length).toString("utf8")), message);

  const decoder = new proto.FrameDecoder();
  assert.deepStrictEqual(decoder.push(bytes), [message]);
  assert.strictEqual(decoder.bufferedBytes, 0);
  decoder.end();
});

test("proto framing rejects oversized bodies, split-then-truncated streams, and malformed input", () => {
  assert.throws(
    () => proto.encodeFrame({ data: "x".repeat(64) }, { maxFrameBytes: 16 }),
    proto.ProtocolError,
  );
  const frame = proto.encodeFrame({ id: 1, method: "ping" });
  const decoder = new proto.FrameDecoder();
  assert.deepStrictEqual(decoder.push(frame.subarray(0, 12)), []);
  assert.deepStrictEqual(decoder.push(frame.subarray(12)), [{ id: 1, method: "ping" }]);

  const truncated = new proto.FrameDecoder();
  truncated.push(frame.subarray(0, 10));
  assert.throws(() => truncated.end(), proto.ProtocolError);
  assert.throws(
    () => new proto.FrameDecoder().push(Buffer.from(`Content-Length: 5\r\n\r\n{"a":`)),
    proto.ProtocolError,
  );
  assert.throws(
    () => new proto.FrameDecoder().push(Buffer.from(`X-Pad: ${"y".repeat(9 * 1024)}`)),
    proto.ProtocolError,
  );
});

test("proto.Transport round-trips requests over the framed child protocol and enforces its bounds", async () => {
  const child = fakeChild();
  const serverDecoder = new proto.FrameDecoder();
  const requests = [];
  child.stdin.on("data", (chunk) => {
    for (const message of serverDecoder.push(chunk)) {
      requests.push(message);
      const reply =
        message.id === 2
          ? { id: message.id, error: { code: "E_SERVICE", message: "boom" } }
          : { id: message.id, result: { echo: message.method } };
      queueMicrotask(() => child.stdout.write(proto.encodeFrame(reply)));
    }
  });

  const transport = new proto.Transport({
    binary: "bamts-fake",
    spawnChild: () => child,
    maxInFlight: 1,
    maxRestarts: 0,
    disposeTimeoutMs: 50,
  });

  const first = transport.request("service/one");
  await assert.rejects(transport.request("service/two"), proto.TransportBusyError);
  assert.deepStrictEqual(await first, { echo: "service/one" });
  await assert.rejects(
    transport.request("service/three"),
    (error) =>
      error instanceof proto.ServiceRequestError &&
      error.method === "service/three" &&
      error.code === "E_SERVICE",
  );

  child.stderr.write("compiler stderr tail\n");
  const fourth = transport.request("service/four");
  child.emit("exit", null, "SIGKILL");
  await assert.rejects(
    fourth,
    (error) =>
      error instanceof proto.TransportCrashError &&
      error.signal === "SIGKILL" &&
      error.stderr.includes("compiler stderr tail"),
  );
  await assert.rejects(transport.request("service/five"), proto.RestartLimitError);

  await transport.dispose();
  assert.strictEqual(transport.disposed, true);
  assert.strictEqual(transport.inFlight, 0);
  assert.deepStrictEqual(
    requests.map(({ id, method }) => `${id}:${method}`),
    ["1:service/one", "2:service/three", "3:service/four"],
  );
});
