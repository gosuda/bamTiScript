/**
 * Bounded `Content-Length` message framing.
 *
 * The wire format is exactly one ASCII header block terminated by a blank line
 * followed by that many bytes of UTF-8 JSON:
 *
 * ```text
 * Content-Length: 27\r\n
 * \r\n
 * {"id":1,"method":"initialize"}
 * ```
 *
 * Both bounds are enforced before any allocation grows: a peer cannot make this
 * decoder buffer without limit by withholding the header terminator, and it
 * cannot make it allocate a huge body by declaring an enormous length.
 */

import { isAscii } from "node:buffer";
import { ProtocolError } from "./errors.js";

/** Largest permitted header block, terminator included. */
export const MAX_HEADER_BYTES = 8 * 1024;

/** Largest permitted JSON body for one frame. */
export const MAX_FRAME_BYTES = 32 * 1024 * 1024;

const TERMINATOR = Buffer.from("\r\n\r\n", "ascii");
const CONTENT_LENGTH = /^content-length$/i;
const UTF8 = new TextDecoder("utf-8", { fatal: true });

function byteLimit(value, name) {
  if (!Number.isSafeInteger(value) || value < 1) {
    throw new RangeError(`${name} must be a positive safe integer.`);
  }
  return value;
}

/** Encode one message as a single framed buffer. */
export function encodeFrame(message, { maxFrameBytes = MAX_FRAME_BYTES } = {}) {
  byteLimit(maxFrameBytes, "maxFrameBytes");
  const body = Buffer.from(JSON.stringify(message), "utf8");
  if (body.byteLength > maxFrameBytes) {
    throw new ProtocolError(
      `outgoing frame is ${body.byteLength} bytes; the transport permits at most ${maxFrameBytes}.`,
    );
  }
  const header = Buffer.from(`Content-Length: ${body.byteLength}\r\n\r\n`, "ascii");
  return Buffer.concat([header, body]);
}

function parseHeaders(block) {
  if (!isAscii(block)) {
    throw new ProtocolError("frame header is not ASCII.");
  }
  let contentLength;
  for (const line of block.toString("ascii").split("\r\n")) {
    if (line === "") continue;
    const separator = line.indexOf(":");
    if (separator <= 0) {
      throw new ProtocolError(`malformed frame header line ${JSON.stringify(line)}.`);
    }
    const field = line.slice(0, separator).trim();
    const value = line.slice(separator + 1).trim();
    if (!CONTENT_LENGTH.test(field)) continue;
    if (contentLength !== undefined) {
      throw new ProtocolError("frame header declares Content-Length more than once.");
    }
    if (!/^[0-9]+$/.test(value)) {
      throw new ProtocolError(`Content-Length ${JSON.stringify(value)} is not a byte count.`);
    }
    contentLength = Number(value);
  }
  if (contentLength === undefined) {
    throw new ProtocolError("frame header omits Content-Length.");
  }
  return contentLength;
}

/**
 * Incremental decoder. Feed arbitrary chunk boundaries to `push`; it returns the
 * messages that became complete, and throws `ProtocolError` on any violation.
 */
export class FrameDecoder {
  #pending = [];
  #pendingBytes = 0;
  #buffer = null;
  #expected = null;

  constructor({ maxHeaderBytes = MAX_HEADER_BYTES, maxFrameBytes = MAX_FRAME_BYTES } = {}) {
    this.maxHeaderBytes = byteLimit(maxHeaderBytes, "maxHeaderBytes");
    this.maxFrameBytes = byteLimit(maxFrameBytes, "maxFrameBytes");
  }

  /** Bytes buffered but not yet delivered as a message. */
  get bufferedBytes() {
    return this.#buffer ? this.#buffer.byteLength : this.#pendingBytes;
  }

  #materialize() {
    if (this.#pending.length > 0) {
      this.#buffer = this.#buffer
        ? Buffer.concat([this.#buffer, ...this.#pending])
        : this.#pending.length === 1
          ? this.#pending[0]
          : Buffer.concat(this.#pending);
      this.#pending = [];
      this.#pendingBytes = 0;
    }
    return this.#buffer ?? Buffer.alloc(0);
  }

  push(chunk) {
    const bytes = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
    this.#pending.push(bytes);
    this.#pendingBytes += bytes.byteLength;

    const messages = [];
    let buffer = this.#materialize();

    for (;;) {
      if (this.#expected === null) {
        const end = buffer.indexOf(TERMINATOR);
        if (end < 0) {
          if (buffer.byteLength > this.maxHeaderBytes) {
            throw new ProtocolError(
              `frame header exceeded ${this.maxHeaderBytes} bytes without a terminator.`,
            );
          }
          break;
        }
        if (end + TERMINATOR.byteLength > this.maxHeaderBytes) {
          throw new ProtocolError(
            `frame header is ${end + TERMINATOR.byteLength} bytes; the transport permits at most ${this.maxHeaderBytes}.`,
          );
        }
        const length = parseHeaders(buffer.subarray(0, end));
        if (length > this.maxFrameBytes) {
          throw new ProtocolError(
            `frame declares ${length} bytes; the transport permits at most ${this.maxFrameBytes}.`,
          );
        }
        this.#expected = length;
        buffer = buffer.subarray(end + TERMINATOR.byteLength);
      }

      if (buffer.byteLength < this.#expected) break;

      const body = buffer.subarray(0, this.#expected);
      buffer = buffer.subarray(this.#expected);
      this.#expected = null;
      try {
        messages.push(JSON.parse(UTF8.decode(body)));
      } catch (cause) {
        throw new ProtocolError("frame body is not valid JSON.", { cause });
      }
    }

    this.#buffer = buffer.byteLength > 0 ? buffer : null;
    return messages;
  }

  /** Fail if the stream ended mid-frame. */
  end() {
    if (this.bufferedBytes > 0 || this.#expected !== null) {
      throw new ProtocolError("stream ended in the middle of a frame.");
    }
  }
}
