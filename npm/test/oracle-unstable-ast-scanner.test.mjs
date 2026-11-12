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
    return nextResolve(specifier, context);
  },
});

const { createSession } = await import("../bamti/internal/session.js");
const scanner = await import("../bamti/unstable/ast/scanner.js");
const pinnedScanner = await import("../../node_modules/typescript/dist/ast/scanner.js");
const { SyntaxKind } = await import("../../node_modules/typescript/dist/enums/syntaxKind.js");
const { formatSyntaxKind } = await import("typescript/unstable/ast");

const worktreeRoot = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const targetDir = process.env.CARGO_TARGET_DIR ?? join(worktreeRoot, "target");
const BINARY = join(targetDir, "debug", process.platform === "win32" ? "bamts.exe" : "bamts");

const SOURCE = "const alpha = 1;";

const PINNED_TO_BAMTI_TOKEN_KIND = {
  ConstKeyword: "KwConst",
  WhitespaceTrivia: "Whitespace",
  Identifier: "Identifier",
  EqualsToken: "Eq",
  NumericLiteral: "NumericLiteral",
  SemicolonToken: "Semicolon",
  EndOfFileToken: "EndOfFile",
};

function pinnedTokens(text) {
  const result = [];
  const lexer = pinnedScanner.createScanner(false, 0, text);
  for (;;) {
    const kind = lexer.scan();
    result.push({
      pinnedKind: formatSyntaxKind(kind),
      start: lexer.getTokenStart(),
      end: lexer.getTokenEnd(),
      text: lexer.getTokenText(),
    });
    if (kind === SyntaxKind.EndOfFile) {
      break;
    }
  }
  return result;
}

test("scanner subpath exports exactly one operation", () => {
  assert.deepStrictEqual(Object.keys(scanner).sort(), ["scan"]);
});

test("scan token boundaries match pinned createScanner (npm/bamti/unstable/ast/scanner.d.ts:3, typescript/dist/ast/scanner.d.ts:96)", async () => {
  const expected = pinnedTokens(SOURCE);
  const session = createSession({ transportOptions: { binary: BINARY } });
  try {
    await session.open({ path: "a.ts", text: SOURCE, version: 1 });
    const scanned = await scanner.scan(session, { path: "a.ts" });
    assert.strictEqual(scanned.sourceId, 0);
    assert.strictEqual(scanned.scriptKind, "TypeScript");
    assert.strictEqual(scanned.diagnosticCount, 0);
    assert.strictEqual(scanned.tokens.length, expected.length);
    for (const [index, want] of expected.entries()) {
      const got = scanned.tokens[index];
      assert.strictEqual(got.range.start, want.start, `token ${index} start`);
      assert.strictEqual(got.range.end, want.end, `token ${index} end`);
      assert.strictEqual(got.text, want.text, `token ${index} text`);
      assert.ok(
        Object.hasOwn(PINNED_TO_BAMTI_TOKEN_KIND, want.pinnedKind),
        `token ${index} kind ${want.pinnedKind}`,
      );
      assert.strictEqual(got.kind, PINNED_TO_BAMTI_TOKEN_KIND[want.pinnedKind], `token ${index} kind`);
      assert.strictEqual(got.missing, false, `token ${index} missing`);
    }
  } finally {
    await session.dispose();
  }
});
