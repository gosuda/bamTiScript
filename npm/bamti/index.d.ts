import type {
  ResolveBinaryOptions as CliResolveBinaryOptions,
  RunOptions as CliRunOptions,
} from "bamti-cli";
import type { Buffer } from "node:buffer";

export {
  ArtifactNotFoundError,
  artifactPackage,
  resolveBinary,
  resolveBinary as resolveArtifact,
} from "bamti-cli";
export type { ResolveBinaryOptions } from "bamti-cli";

export type RunOptions = CliRunOptions;

export function run(
  args?: readonly string[],
  options?: RunOptions,
): Promise<number>;

export interface NativeRunTruncation {
  readonly elided: number;
  readonly limit: number;
}

export interface NativeRunOutcome {
  readonly exitCode: number;
  readonly stdout: Buffer;
  readonly stderr: Buffer;
  readonly truncation?: NativeRunTruncation;
}

export interface NativeRunRequest {
  readonly args: readonly Buffer[];
  readonly cwd: Buffer;
  readonly env: readonly Buffer[];
  readonly signal?: AbortSignal;
}

export interface NativeReleaseMetadata {
  readonly packageVersion: string;
  readonly sourceCommit: string;
  readonly buildSetId: string;
  readonly releaseId: string;
  readonly target: string;
  readonly artifactKind: string;
  readonly nativeAbi: number;
  readonly cliProtocol: number;
}

export interface NativeTarget {
  readonly selector: string;
  readonly target: string;
  readonly package: string;
  readonly entry: string;
  readonly os: string;
  readonly cpu: string;
  readonly libc?: string;
  readonly artifactKind: string;
}

export interface NativeReleaseTableRow extends NativeTarget {
  readonly version: string;
  readonly sha256: string;
}

export interface NativeReleaseTable {
  readonly version: number;
  readonly release: NativeReleaseMetadata;
  readonly targets: readonly NativeReleaseTableRow[];
}

export interface NativeHost {
  readonly platform: string;
  readonly arch: string;
  readonly libc?: string;
  readonly nodeVersion: string;
  readonly napiVersion: string;
}

export interface NativeAddon {
  releaseMetadata(): NativeReleaseMetadata;
  run(request: NativeRunRequest): Promise<NativeRunOutcome>;
}

export interface LoadNativeAddonOptions {
  readonly table?: string | NativeReleaseTable;
  readonly host?: NativeHost;
  readonly resolver?: { resolve(id: string): string };
  readonly readFile?: (path: string) => Buffer;
  readonly realpath?: (path: string) => string;
  readonly requireAddon?: (path: string) => NativeAddon;
  readonly stage?: (bytes: Buffer) => string;
  readonly cache?: {
    get value(): NativeAddon | undefined;
    set value(value: NativeAddon | undefined);
  };
}

export declare class UnsupportedPlatformError extends Error {
  constructor(platform: string, arch: string, libc?: string);
}

export declare class NativeArtifactNotFoundError extends Error {
  constructor(packageName: string, version: string, cause?: Error);
}

export declare class NativeArtifactLoadError extends Error {
  constructor(message: string, cause?: Error);
}

export declare const NATIVE_TARGETS: readonly NativeTarget[];

export declare function selectNativeTarget(host: NativeHost): NativeTarget;

export declare function loadNativeAddon(
  options: LoadNativeAddonOptions & { host: NativeHost },
): NativeAddon;
export declare function loadNativeAddon(options?: undefined): NativeAddon;

/**
 * Executes the BamTS compiler in-process through the verified native Node-API addon.
 * Requires Node.js 24+ with Node-API 10+. The request is forwarded byte-for-byte and
 * the outcome carries `stdout`/`stderr` as `Buffer`s. Addon queue-full and closing
 * failures reject the returned promise unchanged.
 */
export declare function runNative(
  request: NativeRunRequest,
): Promise<NativeRunOutcome>;

export type JsonPrimitive = boolean | number | string | null;
export type JsonValue =
  | JsonPrimitive
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
export type RpcParams = Readonly<Record<string, JsonValue>>;
export interface FileSystemDescriptor {
  readonly kind: "os";
  readonly root: string;
}

export interface RequestOptions {
  signal?: AbortSignal;
}

export interface SpawnOptions {
  cwd?: string;
  env?: Readonly<Record<string, string | undefined>>;
  stdio: readonly ["pipe", "pipe", "pipe"];
}

export interface ReadableStreamLike {
  on(event: "data", listener: (chunk: Uint8Array) => void): this;
  on(event: "error", listener: (error: Error) => void): this;
  on(event: "end", listener: () => void): this;
}

export interface WritableStreamLike {
  write(chunk: Uint8Array): boolean;
  end(): void;
  on(event: "error", listener: (error: Error) => void): this;
}

export interface ChildProcessLike {
  stdin: WritableStreamLike;
  stdout: ReadableStreamLike;
  stderr: ReadableStreamLike;
  exitCode: number | null;
  signalCode: string | null;
  once(event: "error", listener: (error: Error) => void): this;
  once(
    event: "exit" | "close",
    listener: (code: number | null, signal: string | null) => void,
  ): this;
  removeListener(event: "exit", listener: () => void): this;
  kill(signal?: string): boolean;
}

export interface TransportOptions {
  binary?: string;
  binaryOptions?: CliResolveBinaryOptions;
  cwd?: string;
  env?: Readonly<Record<string, string | undefined>>;
  args?: readonly string[];
  spawnChild?: (
    binary: string,
    args: readonly string[],
    options: SpawnOptions,
  ) => ChildProcessLike;
  maxInFlight?: number;
  maxRestarts?: number;
  maxHeaderBytes?: number;
  maxFrameBytes?: number;
  stderrBytes?: number;
  disposeTimeoutMs?: number;
}

export class BamtiError extends Error {}
export class ProtocolError extends BamtiError {}
export class DisposedError extends BamtiError {}
export class TransportBusyError extends BamtiError {
  readonly inFlight: number;
  readonly maxInFlight: number;
}
export class TransportCrashError extends BamtiError {
  readonly code: number | null;
  readonly signal: string | null;
  readonly stderr: string;
}
export class RestartLimitError extends BamtiError {
  readonly restarts: number;
  readonly maxRestarts: number;
}
export class ServiceRequestError extends BamtiError {
  readonly method: string;
  readonly code: string | number | null;
  readonly data?: JsonValue;
}

export class Transport {
  constructor(options?: TransportOptions);
  readonly generation: number;
  readonly inFlight: number;
  readonly disposed: boolean;
  ready(): number;
  stderrTail(): string;
  request<Result extends JsonValue = JsonValue>(
    method: string,
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  dispose(): Promise<void>;
  [Symbol.asyncDispose](): Promise<void>;
}

export interface Service {
  open<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  update<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  close<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  snapshot<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  completions<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  definition<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  quickInfo<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  references<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  rename<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  diagnostics<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
}

export interface SessionOptions {
  root?: string;
  filesystem?: FileSystemDescriptor;
  transport?: Transport;
  transportOptions?: TransportOptions;
}

export class Session implements Service {
  constructor(options?: SessionOptions);
  readonly transport: Transport;
  request<Result extends JsonValue = JsonValue>(
    method: string,
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  open<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  update<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  close<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  snapshot<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  completions<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  definition<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  quickInfo<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  references<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  rename<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  diagnostics<Result extends JsonValue = JsonValue>(
    params?: RpcParams,
    options?: RequestOptions,
  ): Promise<Result>;
  dispose(): Promise<void>;
  [Symbol.asyncDispose](): Promise<void>;
}

export function createSession(options?: SessionOptions): Session;
