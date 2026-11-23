import { spawn } from "node:child_process";
import { resolveBinary } from "bamti-cli";
import {
  DisposedError,
  ProtocolError,
  RestartLimitError,
  ServiceRequestError,
  TransportBusyError,
  TransportCrashError,
  abortError,
} from "./errors.js";
import { FrameDecoder, encodeFrame } from "./framing.js";

const DEFAULT_MAX_IN_FLIGHT = 1024;
const DEFAULT_MAX_RESTARTS = 3;
const DEFAULT_STDERR_BYTES = 64 * 1024;
const DEFAULT_DISPOSE_TIMEOUT_MS = 2_000;

function defaultSpawn(binary, args, options) {
  return spawn(binary, args, options);
}

function appendTail(tail, chunk, limit) {
  const next = Buffer.concat([tail, Buffer.from(chunk)]);
  return next.byteLength <= limit ? next : next.subarray(next.byteLength - limit);
}

function destroyChildStreams(child) {
  child.stdin.destroy?.();
  child.stdout.destroy?.();
  child.stderr.destroy?.();
}

async function waitForExit(child, timeoutMs) {
  if (child.exitCode !== null || child.signalCode !== null) return true;
  let timer;
  let onExit;
  const exited = new Promise((resolve) => {
    onExit = () => resolve(true);
    child.once("exit", onExit);
  });
  const timedOut = new Promise((resolve) => {
    timer = setTimeout(resolve, timeoutMs, false);
  });
  const result = await Promise.race([exited, timedOut]);
  clearTimeout(timer);
  child.removeListener("exit", onExit);
  return result;
}

export class Transport {
  #child = null;
  #decoder = null;
  #disposed = false;
  #disposing = null;
  #generation = 0;
  #nextId = 1;
  #pending = new Map();
  #restarts = 0;
  #stderr = Buffer.alloc(0);

  constructor({
    binary,
    binaryOptions,
    cwd,
    env,
    args = [],
    spawnChild = defaultSpawn,
    maxInFlight = DEFAULT_MAX_IN_FLIGHT,
    maxRestarts = DEFAULT_MAX_RESTARTS,
    maxHeaderBytes,
    maxFrameBytes,
    stderrBytes = DEFAULT_STDERR_BYTES,
    disposeTimeoutMs = DEFAULT_DISPOSE_TIMEOUT_MS,
  } = {}) {
    if (!Array.isArray(args) || args.some((argument) => typeof argument !== "string")) {
      throw new TypeError("args must be an array of strings.");
    }
    if (typeof spawnChild !== "function") {
      throw new TypeError("spawnChild must be a function.");
    }
    if (!Number.isSafeInteger(maxInFlight) || maxInFlight < 1) {
      throw new RangeError("maxInFlight must be a positive safe integer.");
    }
    if (!Number.isSafeInteger(maxRestarts) || maxRestarts < 0) {
      throw new RangeError("maxRestarts must be a non-negative safe integer.");
    }
    if (!Number.isSafeInteger(stderrBytes) || stderrBytes < 0) {
      throw new RangeError("stderrBytes must be a non-negative safe integer.");
    }
    if (!Number.isSafeInteger(disposeTimeoutMs) || disposeTimeoutMs < 0) {
      throw new RangeError("disposeTimeoutMs must be a non-negative safe integer.");
    }
    this.options = {
      binary,
      binaryOptions,
      cwd,
      env,
      args: [...args],
      spawnChild,
      maxInFlight,
      maxRestarts,
      maxHeaderBytes,
      maxFrameBytes,
      stderrBytes,
      disposeTimeoutMs,
    };
  }

  get generation() {
    return this.#generation;
  }

  get inFlight() {
    return this.#pending.size;
  }

  get disposed() {
    return this.#disposed;
  }

  stderrTail() {
    return this.#stderr.toString("utf8");
  }

  ready() {
    if (this.#disposed) throw new DisposedError();
    if (this.#child) return this.#generation;
    if (this.#restarts > this.options.maxRestarts) {
      throw new RestartLimitError(this.#restarts, this.options.maxRestarts);
    }

    const decoder = new FrameDecoder({
      maxHeaderBytes: this.options.maxHeaderBytes,
      maxFrameBytes: this.options.maxFrameBytes,
    });
    const binary = this.options.binary ?? resolveBinary(this.options.binaryOptions);
    const child = this.options.spawnChild(binary, ["--api", ...this.options.args], {
      cwd: this.options.cwd,
      env: this.options.env,
      stdio: ["pipe", "pipe", "pipe"],
    });
    if (!child?.stdin || !child?.stdout || !child?.stderr) {
      throw new TypeError("spawnChild must return a child with stdin, stdout, and stderr streams.");
    }

    this.#child = child;
    this.#decoder = decoder;
    this.#stderr = Buffer.alloc(0);
    this.#generation += 1;
    const generation = this.#generation;
    let drainTimer;
    const drain = () => {
      if (this.#child !== child || drainTimer !== undefined) return;
      drainTimer = setTimeout(() => {
        this.#crash(generation, { code: child.exitCode, signal: child.signalCode });
      }, this.options.disposeTimeoutMs);
      drainTimer.unref();
    };

    child.stdout.on("data", (chunk) => this.#receive(generation, chunk));
    child.stdout.on("error", (cause) => this.#crash(generation, { cause }));
    child.stdout.on("end", () => {
      if (generation !== this.#generation || !this.#decoder) return;
      try {
        this.#decoder.end();
        drain();
      } catch (cause) {
        this.#crash(generation, { cause });
      }
    });
    child.stderr.on("data", (chunk) => {
      if (generation !== this.#generation || !this.#child) return;
      this.#stderr = appendTail(this.#stderr, chunk, this.options.stderrBytes);
    });
    child.stderr.on("error", (cause) => this.#crash(generation, { cause }));
    child.stdin.on("error", (cause) => this.#crash(generation, { cause }));
    child.once("error", (cause) => this.#crash(generation, { cause }));
    child.once("exit", drain);
    child.once("close", (code, signal) => {
      clearTimeout(drainTimer);
      this.#crash(generation, { code, signal });
    });
    return generation;
  }

  request(method, params = {}, { signal } = {}) {
    if (typeof method !== "string" || method.length === 0) {
      return Promise.reject(new TypeError("method must be a non-empty string."));
    }
    if (this.#disposed) return Promise.reject(new DisposedError());
    if (signal?.aborted) return Promise.reject(abortError(signal.reason));
    if (this.#pending.size >= this.options.maxInFlight) {
      return Promise.reject(
        new TransportBusyError(this.#pending.size, this.options.maxInFlight),
      );
    }

    try {
      this.ready();
    } catch (error) {
      return Promise.reject(error);
    }

    const id = this.#nextId++;
    return new Promise((resolve, reject) => {
      const abort = () => {
        if (!this.#pending.delete(id)) return;
        signal.removeEventListener("abort", abort);
        try {
          this.#write({ method: "$/cancelRequest", params: { id } });
        } catch {
          // The crash path rejects every still-pending request. This request is
          // already rejected as aborted, so a failed best-effort notification
          // must not replace the caller's cancellation reason.
        }
        reject(abortError(signal.reason));
      };

      this.#pending.set(id, { method, resolve, reject, signal, abort });
      signal?.addEventListener("abort", abort, { once: true });
      try {
        this.#write({ id, method, params });
      } catch (error) {
        this.#settle(id, "reject", error);
      }
    });
  }

  #write(message) {
    if (this.#disposed) throw new DisposedError();
    if (!this.#child) throw new TransportCrashError({ stderr: this.stderrTail() });
    this.#child.stdin.write(
      encodeFrame(message, { maxFrameBytes: this.options.maxFrameBytes }),
    );
  }

  #receive(generation, chunk) {
    if (generation !== this.#generation || !this.#decoder) return;
    let messages;
    try {
      messages = this.#decoder.push(chunk);
    } catch (error) {
      this.#crash(generation, { cause: error });
      return;
    }
    for (const message of messages) {
      if (!message || typeof message !== "object" || !("id" in message)) {
        continue;
      }
      if ("error" in message && message.error !== undefined) {
        const error = message.error;
        if (
          error === null ||
          typeof error !== "object" ||
          Array.isArray(error) ||
          (error.code !== undefined &&
            error.code !== null &&
            typeof error.code !== "string" &&
            !Number.isFinite(error.code)) ||
          typeof error.message !== "string" ||
          "result" in message
        ) {
          this.#crash(generation, {
            cause: new ProtocolError("response has an invalid error payload."),
          });
          return;
        }
        const pending = this.#pending.get(message.id);
        this.#settle(
          message.id,
          "reject",
          new ServiceRequestError(pending?.method ?? "request", error),
        );
      } else if ("result" in message) {
        this.#settle(message.id, "resolve", message.result);
      } else {
        this.#crash(generation, {
          cause: new ProtocolError(`response ${JSON.stringify(message.id)} has neither result nor error.`),
        });
        return;
      }
    }
  }

  #settle(id, action, value) {
    const pending = this.#pending.get(id);
    if (!pending) return;
    this.#pending.delete(id);
    pending.signal?.removeEventListener("abort", pending.abort);
    pending[action](value);
  }

  #crash(generation, details) {
    if (generation !== this.#generation || !this.#child) return;
    const child = this.#child;
    this.#child = null;
    this.#decoder = null;
    if (this.#disposed) return;

    this.#restarts += 1;
    const crash =
      details.cause instanceof ProtocolError
        ? details.cause
        : new TransportCrashError({ ...details, stderr: this.stderrTail() });
    for (const id of [...this.#pending.keys()]) this.#settle(id, "reject", crash);
    if (child.exitCode === null && child.signalCode === null) {
      try {
        child.kill("SIGKILL");
      } catch {
        // The child may have exited before the termination signal arrived.
      }
    }
    destroyChildStreams(child);
  }

  async dispose() {
    if (this.#disposing) return this.#disposing;
    this.#disposed = true;
    const child = this.#child;
    this.#child = null;
    this.#decoder = null;
    for (const id of [...this.#pending.keys()]) {
      this.#settle(id, "reject", new DisposedError());
    }

    this.#disposing = (async () => {
      if (!child) return;
      try {
        try {
          child.stdin.end();
        } catch {
          // The process may have closed stdin before disposal began.
        }
        if (child.exitCode !== null || child.signalCode !== null) return;

        if (await waitForExit(child, this.options.disposeTimeoutMs)) return;
        try {
          child.kill("SIGKILL");
        } catch {
          // The child may have exited before the termination signal arrived.
        }
        await waitForExit(child, 100);
      } finally {
        destroyChildStreams(child);
      }
    })();
    return this.#disposing;
  }

  async [Symbol.asyncDispose]() {
    await this.dispose();
  }
}
