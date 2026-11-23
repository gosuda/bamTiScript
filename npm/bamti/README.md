# bamti

`bamti` is the Node.js 24 interface for the BamTS compiler. The root exposes two distinct execution paths: `runNative()` executes the compiler in-process through the verified native Node-API addon, and `run()` invokes the `bamts` binary from `bamti-cli` for classic exit-code semantics. Each default session owns one framed `bamts --api` child process. TypeScript service and public AST requests use that session's child, retaining its project state across requests.

## In-process native execution

`runNative(request)` loads the native addon for the host platform with `loadNativeAddon()` and forwards `request` to the addon's asynchronous `run()`. Requests and outcomes are byte-exact: `args`, `cwd`, and `env` are `Buffer`s in, `stdout` and `stderr` are `Buffer`s out, and neither side re-encodes or copies them.

```js
import { runNative } from "bamti";

const outcome = await runNative({
  args: [Buffer.from("--version")],
  cwd: Buffer.from(process.cwd()),
  env: Object.entries(process.env)
    .filter(([, value]) => value !== undefined)
    .map(([name, value]) => Buffer.from(`${name}=${value}`)),
});

console.log(outcome.exitCode, outcome.stdout.toString("utf8"));
```

`outcome` is `{ exitCode, stdout, stderr, truncation? }`; `truncation` reports `{ elided, limit }` when the addon capped captured output. The request may carry an optional `signal: AbortSignal`: aborting settles queued work immediately and the active invocation at its next cancellation point, with an `AbortError` rejection. Addon queue-full and closing failures reject the returned promise unchanged.

For lower-level control, `loadNativeAddon()` returns the verified addon (`{ releaseMetadata(), run(request) }`) directly, and `selectNativeTarget()` / `NATIVE_TARGETS` expose the platform mapping. Loading requires Node.js 24 or later and Node-API 10 or later, and it fails closed when the host, the release table, or the artifact package does not verify.

## CLI process execution

`run(args, options)` resolves the `bamts` binary from `bamti-cli` and spawns it, resolving to the process exit code:

```js
import { run } from "bamti";

const exitCode = await run(["--noEmit", "input.ts"], {
  cwd: process.cwd(),
  env: process.env,
  stdio: "inherit",
});
```

`stdio` accepts `"inherit"`, `"ignore"`, or `"pipe"`. The public API returns only the exit code, so `"pipe"` captures and discards compiler output.

## Persistent compiler state

For persistent compiler state, create a session and dispose it when finished:

```js
import { createSession } from "bamti";

await using session = createSession({ root: process.cwd() });
await session.open({ path: "input.ts", text: "const answer = 42;", version: 1 });
const diagnostics = await session.diagnostics({ path: "input.ts" });
```

`unstable/sync` exports `createSerialService(options)`, which serializes service requests through one session: every operation returns a `Promise`, and at most one request is in flight at a time. The export path follows the pinned TypeScript 7.0.2 package contract; the API name states that the service is asynchronous and serialized.

The package exports the root, `unstable/sync`, `unstable/async`, `unstable/fs`, `unstable/proto`, `unstable/ast`, six AST operation subpaths, and `package.json` — thirteen entry points.

## Architecture and target design

- **Native execution vs CLI process execution vs persistent service**: `runNative()` uses the direct native addon loader in-process. `run()` spawns the `bamts` binary through `bamti-cli`. Session and unstable service/AST exports use the standalone `bamts --api` protocol; they do not add a second native loader or fall back from native execution.
- **Node.js and Node-API requirement**: Requires Node.js 24 or later and Node-API 10 or later; both are enforced when the native addon loads.
- **Five target platform packages**: Loads optional platform packages (`@bamti/bamti-linux-x64-gnu`, `@bamti/bamti-linux-arm64-gnu`, `@bamti/bamti-darwin-x64`, `@bamti/bamti-darwin-arm64`, `@bamti/bamti-win32-x64-msvc`).
- **Fail-closed native loading**: Inspects host parameters, resolves the target package, and verifies manifest structure, binary SHA-256 digest, and release metadata. If missing or invalid, loading fails closed with `NativeArtifactNotFoundError` or `NativeArtifactLoadError`; an unsupported host raises `UnsupportedPlatformError`. It never downloads binaries, compiles from source, or falls back to the CLI executable.
- **Cancellation and teardown**: Native invocations and persistent requests accept `AbortSignal`. Persistent requests forward cancellation over the API protocol and dispose their child process when the session closes. The addon owns native cancellation and rejects further work with queue-full and closing errors once its executor shuts down.

## Release status note

Native addon artifacts are staged by the release pipeline (`npm/scripts/package-native-platform.mjs`) and are not yet published to npm. The loader fails closed when the artifacts are absent.
