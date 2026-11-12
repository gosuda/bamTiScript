import assert from "node:assert/strict";
import test from "node:test";
import { BROKEN_SOURCE, SOURCE, nonEmpty, pinnedAst, withPinnedSourceFile, withSession } from "./oracle-support.mjs";

const scanner = await import("../bamti/unstable/ast/scanner.js");
const pinnedScanner = await import("typescript/unstable/ast/scanner");

function pinnedTokens(sf) {
  const tokens = [];
  const lexer = pinnedScanner.createScanner(false, sf.languageVariant, sf.text);
  for (;;) {
    const kind = lexer.scan();
    tokens.push({ range: { start: lexer.getTokenStart(), end: lexer.getTokenEnd() }, text: lexer.getTokenText() });
    if (kind === pinnedAst.SyntaxKind.EndOfFile) {
      return nonEmpty(tokens, "pinned tokens");
    }
  }
}

test("package shape: the scanner subpath declares exactly one operation (bamti package.json, not an oracle comparison)", () => {
  assert.deepStrictEqual(Object.keys(scanner).sort(), ["scan"]);
});

for (const [name, text] of [
  ["a variable statement", SOURCE],
  ["an unterminated string", BROKEN_SOURCE],
]) {
  test(`scanner.scan token ranges and text equal pinned createScanner on ${name}`, async () => {
    await withSession(text, async (session) => {
      await withPinnedSourceFile(text, async ({ sf }) => {
        const scanned = await scanner.scan(session, { path: "a.ts" });
        assert.deepStrictEqual(
          scanned.tokens.map(({ range, text: lexeme }) => ({ range, text: lexeme })),
          pinnedTokens(sf),
        );
      });
    });
  });
}
