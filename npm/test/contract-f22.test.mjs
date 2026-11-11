import assert from "node:assert/strict";
import { registerHooks } from "node:module";
import { dirname, join } from "node:path";
import test from "node:test";
import { fileURLToPath, pathToFileURL } from "node:url";

const npmRoot = join(dirname(fileURLToPath(import.meta.url)), "..");

registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === "bamti-cli") {
      return {
        shortCircuit: true,
        url: pathToFileURL(join(npmRoot, "bamti-cli", "index.js")).href,
      };
    }
    return nextResolve(specifier);
  },
});
const sync = await import("../bamti/unstable/sync.js");
test("sync.createSerialService is function", () => {
  assert.ok(typeof sync.createSerialService === "function");
});
test("sync has 10 service methods + request/dispose", () => {
  const svc = sync.createSerialService({ root: "/tmp" });
  const methods = ["open", "update", "close", "snapshot", "completions",
    "definition", "quickInfo", "references", "rename", "diagnostics"];
  for (const m of methods) {
    assert.ok(typeof svc[m] === "function", `sync.${m} missing`);
  }
  assert.ok(typeof svc.request === "function");
  assert.ok(typeof svc.dispose === "function");
  svc.dispose();
});

const asyncMod = await import("../bamti/unstable/async.js");
test("async.createAsyncService is function", () => {
  assert.ok(typeof asyncMod.createAsyncService === "function");
});
test("async has 10 service methods + request/dispose", () => {
  const svc = asyncMod.createAsyncService({ root: "/tmp" });
  const methods = ["open", "update", "close", "snapshot", "completions",
    "definition", "quickInfo", "references", "rename", "diagnostics"];
  for (const m of methods) {
    assert.ok(typeof svc[m] === "function", `async.${m} missing`);
  }
  assert.ok(typeof svc.request === "function");
  assert.ok(typeof svc.dispose === "function");
  svc.dispose();
});

const fs = await import("../bamti/unstable/fs.js");
test("fs.osFileSystem is function", () => {
  assert.ok(typeof fs.osFileSystem === "function");
});
test("fs.osFileSystem returns frozen descriptor", () => {
  const fsys = fs.osFileSystem("/tmp");
  assert.equal(fsys.kind, "os");
  assert.ok(typeof fsys.root === "string");
  assert.ok(Object.isFrozen(fsys));
});

const proto = await import("../bamti/unstable/proto.js");
test("proto.encodeFrame is function", () => {
  assert.ok(typeof proto.encodeFrame === "function");
});
test("proto.FrameDecoder is function", () => {
  assert.ok(typeof proto.FrameDecoder === "function");
});
test("proto.MAX_FRAME_BYTES is number", () => {
  assert.ok(typeof proto.MAX_FRAME_BYTES === "number");
});
test("proto.MAX_HEADER_BYTES is number", () => {
  assert.ok(typeof proto.MAX_HEADER_BYTES === "number");
});
test("proto.Transport is function", () => {
  assert.ok(typeof proto.Transport === "function");
});
test("proto exports 7 error classes", () => {
  for (const e of ["BamtiError", "DisposedError", "ProtocolError",
    "RestartLimitError", "ServiceRequestError", "TransportBusyError",
    "TransportCrashError"]) {
    assert.ok(proto[e], `proto.${e} missing`);
  }
});
test("encodeFrame/FrameDecoder roundtrip", () => {
  const message = { method: "service/open", params: {} };
  const frame = proto.encodeFrame(message);
  assert.ok(frame instanceof Uint8Array);
  assert.ok(frame.length > 0, "frame must be non-empty");

  const decoder = new proto.FrameDecoder();
  const msgs = decoder.push(frame);
  assert.equal(msgs.length, 1, "decoder must yield exactly one message");
  assert.deepEqual(msgs[0], message, "decoded message must match original");
});

test("encodeFrame rejects oversized payload", () => {
  const huge = "x".repeat(proto.MAX_FRAME_BYTES + 1);
  assert.throws(() => proto.encodeFrame({ data: huge }), /frame/);
});
