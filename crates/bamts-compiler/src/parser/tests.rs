use super::*;

use crate::scanner::scan;

fn parse_text(text: &str, script_kind: ScriptKind) -> Recovered<SourceFile> {
    let source = Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
    let scanned = scan(SourceId::new(0), script_kind, source);
    parse(scanned)
}

fn parse_ts(text: &str) -> Recovered<SourceFile> {
    parse_text(text, ScriptKind::TypeScript)
}

fn errors(recovered: &Recovered<SourceFile>) -> Vec<&Diagnostic> {
    recovered
        .diagnostics()
        .iter()
        .filter(|d| d.severity() == DiagnosticSeverity::Error)
        .collect()
}

/// B3: an argument-bearing yield outside any generator reports the
/// native code that projects onto TS1163; a bare `yield` stays
/// quiet (sloppy identifier reference), and generators stay clean.
#[test]
fn reports_yield_expression_outside_generators() {
    let bad = parse_text("function f() { yield 1; }", ScriptKind::TypeScript);
    assert!(
        errors(&bad)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P017"),
        "yield in plain function must report"
    );
    let nested = parse_text(
        "function* g() { function h() { yield 1; } yield 2; }",
        ScriptKind::TypeScript,
    );
    assert!(
        errors(&nested)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P017"),
        "yield in nested plain function must report"
    );
    let bare = parse_text("function f() { var x = yield; }", ScriptKind::TypeScript);
    assert!(
        !errors(&bare)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P017"),
        "bare yield is a sloppy identifier, not a report"
    );
    assert_clean("function* g() { yield 1; }");
}

/// B3: await inside a non-async function-like (nested function or
/// arrow) reports the native code that projects onto TS1308;
/// async bodies and module top level stay clean.
#[test]
fn reports_await_outside_async_function_likes() {
    let nested = parse_text(
        "async function f() { function g() { return await k; } }",
        ScriptKind::TypeScript,
    );
    assert!(
        errors(&nested)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P018"),
        "await in nested plain function must report"
    );
    let arrow = parse_text(
        "async function f() { var g = () => await k; }",
        ScriptKind::TypeScript,
    );
    assert!(
        errors(&arrow)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P018"),
        "await in non-async arrow must report"
    );
    assert_clean("async function f() { return await k; }");
    assert_clean("await k;");
}

/// B3 follow-ups: the diagnostics anchor at the yield/await keyword
/// (not the token after the operand), sloppy JavaScript stays
/// silent, and class static blocks carry their own context.
#[test]
fn context_diagnostics_anchor_gate_and_static_blocks() {
    let bad = parse_text("function f() { yield 1; }", ScriptKind::TypeScript);
    let diag = errors(&bad)
        .iter()
        .find(|d| d.code().as_str() == "BAMTS-P017")
        .copied()
        .expect("yield diagnostic");
    assert_eq!(
        diag.range().start().get(),
        "function f() { ".len(),
        "range must start at the yield keyword"
    );
    let sloppy = parse_text("function f() { yield(1); }", ScriptKind::JavaScript);
    assert!(
        !errors(&sloppy)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P017"),
        "sloppy js identifier call must stay silent"
    );
    let sloppy_await = parse_text("function f() { await(1); }", ScriptKind::JavaScript);
    assert!(
        !errors(&sloppy_await)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P018"),
        "sloppy js await call must stay silent"
    );
    let static_block = parse_text(
        "async function f() { class C { static { await x; } } }",
        ScriptKind::TypeScript,
    );
    assert!(
        errors(&static_block)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P018"),
        "await in a static block is context-illegal regardless of the enclosing async"
    );
    let static_block_yield = parse_text(
        "function* g() { class C { static { yield x; } } }",
        ScriptKind::TypeScript,
    );
    assert!(
        errors(&static_block_yield)
            .iter()
            .any(|d| d.code().as_str() == "BAMTS-P017"),
        "yield in a static block is context-illegal regardless of the enclosing generator"
    );
}

/// B3: the native codes project onto the TypeScript surface the
/// driver reports - TS1163 and TS1308 with tsc's exact messages.
#[test]
fn projects_context_codes_onto_the_typescript_surface() {
    let bad = parse_text("function f() { yield 1; }", ScriptKind::TypeScript);
    let projected = crate::diagnostics_parser::typescript_parse_code(
        bad.diagnostics()[0].code(),
        bad.diagnostics()[0].message(),
    )
    .expect("yield code projects");
    assert_eq!(projected.as_str(), "TS1163");
    let awaited = parse_text(
        "async function f() { function g() { return await k; } }",
        ScriptKind::TypeScript,
    );
    let await_code = errors(&awaited)
        .iter()
        .find(|d| d.code().as_str() == "BAMTS-P018")
        .copied()
        .expect("await error present");
    let projected =
        crate::diagnostics_parser::typescript_parse_code(await_code.code(), await_code.message())
            .expect("await code projects");
    assert_eq!(projected.as_str(), "TS1308");
    assert_eq!(
        crate::diagnostics_parser::typescript_parse_message(projected),
        Some(
            "'await' expressions are only allowed within async functions and at the top levels of modules."
        )
    );
}

/// The text that `tsc` 7.0.2 prints for each source, from the message that
/// the parser writes.
#[test]
fn parser_messages_project_onto_the_text_of_tsc() {
    for (source, code, message) in [
        (
            "class C { export x = 1; }",
            "TS1031",
            "'export' modifier cannot appear on class elements of this kind.",
        ),
        (
            "const z = -2 ** 2;",
            "TS17006",
            "An unary expression with the '-' operator is not allowed in the left-hand side of an exponentiation expression. Consider enclosing the expression in parentheses.",
        ),
        ("const o = { a: 1;", "TS1005", "',' expected."),
        ("try { }", "TS1472", "'catch' or 'finally' expected."),
        (
            r#"const a = "\101";"#,
            "TS1487",
            r"Octal escape sequences are not allowed. Use the syntax '\x41'.",
        ),
        (
            r#"const b = "\8";"#,
            "TS1488",
            r"Escape sequence '\8' is not allowed.",
        ),
    ] {
        let parsed = parse_ts(source);
        let mapped = crate::diagnostics_parser::map_parse_diagnostic(errors(&parsed)[0]);
        assert_eq!(
            (mapped.code().as_str(), mapped.message()),
            (code, message),
            "{source}"
        );
    }
}

/// `tsc` 7.0.2 reports TS17006 over the unary operand and TS17002 from the
/// end of `</` to the end of the name of the closing tag.
#[test]
fn an_operand_or_a_tag_error_is_where_tsc_reports_it() {
    for (source, script_kind, range) in [
        ("const z = -2 ** 2;", ScriptKind::TypeScript, (10, 12)),
        (
            "async () => { await 1 ** 2; };",
            ScriptKind::TypeScript,
            (14, 21),
        ),
        (
            "const e = <div></span>;",
            ScriptKind::TypeScriptReact,
            (17, 21),
        ),
        (
            "const e = <a.b></a.c>;",
            ScriptKind::TypeScriptReact,
            (17, 20),
        ),
        (
            "const f = <a></ /*c*/ b>;",
            ScriptKind::TypeScriptReact,
            (15, 23),
        ),
        (
            "const f = <é𝑥></  é𝑥y >;",
            ScriptKind::TypeScriptReact,
            (17, 23),
        ),
    ] {
        let parsed = parse_text(source, script_kind);
        let found: Vec<(usize, usize)> = errors(&parsed)
            .iter()
            .map(|d| (d.range().start().get(), d.range().end().get()))
            .collect();
        assert_eq!(found, [range], "{source}");
    }
}

/// `tsc` 7.0.2 reports no parse error at the start of an earlier one, and a
/// lexical error comes first.
#[test]
fn one_parse_error_is_reported_at_a_position() {
    let found_in = |text: &str, script_kind: ScriptKind| -> Vec<(usize, String)> {
        errors(&parse_text(text, script_kind))
            .iter()
            .map(|d| {
                let mapped = crate::diagnostics_parser::map_parse_diagnostic(d);
                (d.range().start().get(), mapped.message().to_owned())
            })
            .collect()
    };
    let found = |text: &str| found_in(text, ScriptKind::TypeScript);
    assert_eq!(
        found("const o = { a: 1;\n"),
        [
            (16, "',' expected.".to_owned()),
            (18, "'}' expected.".to_owned())
        ]
    );
    assert_eq!(
        found(r#"let a = "\x"#),
        [(11, "Hexadecimal digit expected.".to_owned())]
    );
    // At the end of the text, a missing name or expression is reported
    // after the last token, so it does not meet an error at the end.
    assert_eq!(
        found("let x = /* nope"),
        [
            (7, "Expression expected.".to_owned()),
            (15, "'*/' expected.".to_owned())
        ]
    );
    assert_eq!(
        found("let x = 1 +  /* c"),
        [
            (11, "Expression expected.".to_owned()),
            (17, "'*/' expected.".to_owned())
        ]
    );
    assert_eq!(
        found("let x = \n\n"),
        [(7, "Expression expected.".to_owned())]
    );
    assert_eq!(
        found("/* 😀 */ a.  // c"),
        [(11, "Identifier expected.".to_owned())]
    );
    // A missing type is reported there too, but `A[` is an array type that
    // misses its `]`.
    assert_eq!(found("let x:   // c"), [(6, "Type expected.".to_owned())]);
    assert_eq!(
        found("let x: A[   // c"),
        [(16, "']' expected.".to_owned())]
    );
    assert_eq!(
        found("interface I { a:   // c"),
        [
            (16, "Type expected.".to_owned()),
            (23, "'}' expected.".to_owned())
        ]
    );
    // After `?.`, a missing name is reported at the token.
    assert_eq!(
        found("declare let a: any; a?.   // c"),
        [(30, "Identifier expected.".to_owned())]
    );
    // At the end of the text, a class has no missing name, and a heritage
    // list has no missing element.
    for (text, end) in [
        ("class   // c", 12),
        ("class C extends   // c", 22),
        ("class C implements   // c", 25),
        ("class C implements A,   // c", 28),
        ("interface I extends   // c", 26),
        ("interface I extends A,   // c", 29),
    ] {
        assert_eq!(found(text), [(end, "'{' expected.".to_owned())], "{text}");
    }
    // A JSX attribute value is expected at the token, and a tag that does not
    // end with `>` closes itself.
    let attribute: Vec<usize> =
        errors(&parse_text("const e = <a b= ", ScriptKind::TypeScriptReact))
            .iter()
            .map(|d| d.range().start().get())
            .collect();
    assert_eq!(attribute, [16]);
    assert_eq!(
        found_in("const e = <a b   ", ScriptKind::TypeScriptReact),
        [(17, "'/' expected.".to_owned())]
    );
}

/// `tsc` 7.0.2 reads an expression, or in an `import()` type a type, where a
/// module name belongs.
#[test]
fn a_missing_module_name_is_a_missing_expression_or_type() {
    let found = |text: &str| -> Vec<(usize, String)> {
        errors(&parse_ts(text))
            .iter()
            .map(|d| {
                let mapped = crate::diagnostics_parser::map_parse_diagnostic(d);
                (d.range().start().get(), mapped.message().to_owned())
            })
            .collect()
    };
    for (text, at, message) in [
        ("import x from ;", 14, "Expression expected."),
        ("import x from   // c", 13, "Expression expected."),
        ("import x = require();", 19, "Expression expected."),
        ("export * as x from ;", 19, "Expression expected."),
        ("export { a } from 1;", 18, "String literal expected."),
        ("import x from y;", 14, "String literal expected."),
        ("type T = import();", 16, "Type expected."),
    ] {
        assert_eq!(found(text), [(at, message.to_owned())], "{text}");
    }
    assert_eq!(
        found(r#"type T = import("x", { 1 });"#)[0],
        (23, "'with' expected.".to_owned())
    );
}

/// A tag accepts any escape, also in JSX, where the parser scans the template
/// again.
#[test]
fn a_tagged_template_in_jsx_keeps_no_escape_error() {
    for (text, script_kind) in [
        (r"const e = <a b={tag`\1`} />;", ScriptKind::JavaScriptReact),
        (
            r"const e = <a>{tag`${1}\8`}</a>;",
            ScriptKind::JavaScriptReact,
        ),
        (r"const e = <a b={tag`\1`} />;", ScriptKind::TypeScriptReact),
    ] {
        let parsed = parse_text(text, script_kind);
        assert_eq!(errors(&parsed), Vec::<&Diagnostic>::new(), "{text}");
    }
    let plain = parse_text(r"const e = <a b={`\1`} />;", ScriptKind::JavaScriptReact);
    let starts: Vec<usize> = errors(&plain)
        .iter()
        .map(|d| d.range().start().get())
        .collect();
    assert_eq!(starts, [17], "a template with no tag keeps its error");
}

/// `tsc` 7.0.2 reports no escape error in a template literal type with no
/// substitution, and the errors of one with a substitution.
#[test]
fn a_template_literal_type_with_no_substitution_keeps_no_escape_error() {
    for source in [
        r"type T = `\1`;",
        r"type T = `a\01`;",
        r"type T = `\8`;",
        r"type T = `\x`;",
        r"type T = `\u{110000}`;",
    ] {
        let parsed = parse_ts(source);
        assert_eq!(errors(&parsed), Vec::<&Diagnostic>::new(), "{source}");
    }
    for (source, start) in [
        (r"type T = `\1${string}`;", 10),
        (r"type T = `${string}\1`;", 19),
        (r"let a = `\1`;", 9),
    ] {
        let parsed = parse_ts(source);
        let starts: Vec<usize> = errors(&parsed)
            .iter()
            .map(|d| d.range().start().get())
            .collect();
        assert_eq!(starts, [start], "{source}");
    }
}

/// `tsc` 7.0.2 reports a string, a template or a comment that is not closed
/// at the end of its text. The parser still drops one that starts in text
/// that it scans again.
#[test]
fn an_unterminated_literal_is_reported_at_its_end() {
    for (source, start) in [
        ("let a = \"abc\nlet b = 1;", 12),
        ("let a = `ab${1}cd\nlet b = 2;\n", 29),
        ("let a = 1; /* nope\nlet b = 2;\n", 30),
    ] {
        let parsed = parse_ts(source);
        let found: Vec<(usize, usize)> = errors(&parsed)
            .iter()
            .map(|d| (d.range().start().get(), d.range().end().get()))
            .collect();
        assert_eq!(found, [(start, start)], "{source}");
    }
    let jsx = parse_text(
        "const a = <div>don't</div>; const b = 1;\n",
        ScriptKind::TypeScriptReact,
    );
    assert!(errors(&jsx).is_empty(), "{:?}", errors(&jsx));
    // The parser scans a JSX attribute again. A literal there that is not
    // closed is reported at the end of the text too, and alone.
    for (source, start) in [
        ("const e = <a b=\"abc />;\nconst f = 1;\n", 37),
        ("const e = <a b={`abc} />;\nconst f = 1;\n", 39),
    ] {
        let parsed = parse_text(source, ScriptKind::TypeScriptReact);
        let found: Vec<(usize, usize)> = errors(&parsed)
            .iter()
            .map(|d| (d.range().start().get(), d.range().end().get()))
            .collect();
        assert_eq!(found, [(start, start)], "{source}");
    }
}

/// `tsc` 7.0.2 reports a template with no substitution that is not closed
/// before an escape error at its end. A string and a template tail report the
/// escape error there, and a braced escape that reaches the end is TS1126.
#[test]
fn an_escape_at_the_end_of_an_unclosed_literal_is_reported_as_tsc_does() {
    // The errors at one position are in the order of their TypeScript codes,
    // which is the order that a report gives them.
    let found = |text: &str| -> Vec<(usize, String)> {
        let mut found: Vec<(usize, String)> = errors(&parse_ts(text))
            .iter()
            .map(|d| {
                let mapped = crate::diagnostics_parser::map_parse_diagnostic(d);
                (d.range().start().get(), mapped.code().as_str().to_owned())
            })
            .collect();
        found.sort();
        found
    };
    let at = |list: &[(usize, &str)]| -> Vec<(usize, String)> {
        list.iter()
            .map(|(start, code)| (*start, (*code).to_owned()))
            .collect()
    };
    for (source, expected) in [
        (r"let a = `\x", at(&[(11, "TS1160")])),
        (r"let a = `a\x1", at(&[(13, "TS1160")])),
        (r"let a = `\u", at(&[(11, "TS1160")])),
        (r"let a = `\u{12", at(&[(14, "TS1160")])),
        (r"type T = `\x", at(&[(12, "TS1160")])),
        (r"let a = `\1", at(&[(9, "TS1487"), (11, "TS1160")])),
        (r"let a = `${1}\x", at(&[(15, "TS1125")])),
        (r#"let a = "\x"#, at(&[(11, "TS1125")])),
        (r#"let a = "\u{12"#, at(&[(14, "TS1126")])),
        (r"let a = `${1}\u{12", at(&[(18, "TS1126")])),
        (r#"let a = "\u{12x""#, at(&[(14, "TS1199")])),
        (
            r#"let a = "\u{110000"#,
            at(&[(12, "TS1198"), (18, "TS1126")]),
        ),
        // An error at the end of the template is lost only when it is the
        // first error in the text.
        (
            r"let a = `\1\u{12",
            at(&[(9, "TS1487"), (16, "TS1126"), (16, "TS1160")]),
        ),
        (
            r"let a = `\u{110000",
            at(&[(12, "TS1198"), (18, "TS1126"), (18, "TS1160")]),
        ),
        (
            r"let a = `\xZ\u{",
            at(&[(11, "TS1125"), (15, "TS1125"), (15, "TS1160")]),
        ),
        (
            r"let a = `\u{110000}\x",
            at(&[(12, "TS1198"), (21, "TS1125"), (21, "TS1160")]),
        ),
    ] {
        assert_eq!(found(source), expected, "{source}");
    }
}

/// `tsc` 7.0.2 reads an expression where a module name belongs. A malformed one
/// reports its own errors, and one that is not a string literal is TS1141,
/// which a file with a parse error does not get.
#[test]
fn a_module_name_is_read_as_an_expression() {
    let found = |text: &str| -> Vec<(usize, String)> {
        errors(&parse_ts(text))
            .iter()
            .map(|d| {
                let mapped = crate::diagnostics_parser::map_parse_diagnostic(d);
                (d.range().start().get(), mapped.code().as_str().to_owned())
            })
            .collect()
    };
    let at = |list: &[(usize, &str)]| -> Vec<(usize, String)> {
        list.iter()
            .map(|(start, code)| (*start, (*code).to_owned()))
            .collect()
    };
    for (source, expected) in [
        ("import x from y;", at(&[(14, "TS1141")])),
        ("import x from 1;", at(&[(14, "TS1141")])),
        ("import x from (a);", at(&[(14, "TS1141")])),
        ("import x from a, b;", at(&[(14, "TS1141")])),
        ("import x from +;", at(&[(15, "TS1109")])),
        ("import x from *;", at(&[(14, "TS1109"), (15, "TS1109")])),
        ("import x from =;", at(&[(14, "TS1109"), (15, "TS1109")])),
        ("import x from <;", at(&[(15, "TS1110")])),
        ("import x from /;", at(&[(14, "TS1161")])),
        ("export * from +;", at(&[(15, "TS1109")])),
        ("export { a } from +;", at(&[(19, "TS1109")])),
        ("import x = require(y);", at(&[(19, "TS1141")])),
        (
            "import x = require(*);",
            at(&[(19, "TS1109"), (20, "TS1109")]),
        ),
        ("import x from y; let a = ;", at(&[(25, "TS1109")])),
        ("let a = ;\nimport x from y;", at(&[(8, "TS1109")])),
        // An `import()` type reads a type there.
        ("type T = import(y);", at(&[(16, "TS1141")])),
        ("type T = import(1);", at(&[(16, "TS1141")])),
        ("type T = import(`x`);", at(&[(16, "TS1141")])),
        ("type T = import();", at(&[(16, "TS1110")])),
    ] {
        assert_eq!(found(source), expected, "{source}");
    }
}

#[test]
fn pr199_constructor_keyword_context_is_local() {
    for (source, expected, keyword) in [
        (
            "/* 🦀 */ class C { constructor() { await value; } }",
            "BAMTS-P018",
            "await",
        ),
        (
            "async function f() { class C { constructor() { await value; } } await value; }",
            "BAMTS-P018",
            "await",
        ),
        (
            "function* f() { class C { constructor() { yield 1; } } yield 2; }",
            "BAMTS-P017",
            "yield",
        ),
        (
            "async function f() { class C { constructor(x = await value) {} } await value; }",
            "BAMTS-P018",
            "await",
        ),
        (
            "function* f() { class C { constructor(x = yield 1) {} } yield 2; }",
            "BAMTS-P017",
            "yield",
        ),
        (
            "class C { constructor(x = await value); constructor(x) {} }",
            "BAMTS-P018",
            "await",
        ),
    ] {
        let parsed = parse_text(source, ScriptKind::TypeScript);
        let diagnostics = errors(&parsed)
            .into_iter()
            .filter(|diagnostic| matches!(diagnostic.code().as_str(), "BAMTS-P017" | "BAMTS-P018"))
            .collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 1, "{source}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code().as_str(), expected, "{source}");
        let byte_start = source.find(keyword).expect("keyword in fixture");
        let utf16_start = source[..byte_start].encode_utf16().count();
        assert_eq!(
            diagnostics[0].range().start().get(),
            utf16_start,
            "{source}"
        );
    }
    for source in [
        "class C { constructor() { const f = async () => await value; const g = function*() { yield 1; }; } }",
        "async function f() { class C { constructor() {} } await value; }",
        "function* f() { class C { constructor() {} } yield 1; }",
        "class C { constructor() {} } await value;",
    ] {
        let parsed = parse_text(source, ScriptKind::TypeScript);
        assert!(
            errors(&parsed).is_empty(),
            "{source}: {:?}",
            errors(&parsed)
        );
    }
}

fn assert_clean(text: &str) -> Recovered<SourceFile> {
    let recovered = parse_ts(text);
    let errs = errors(&recovered);
    assert!(
        errs.is_empty(),
        "expected no errors for {text:?}, got: {:?}",
        errs.iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
    recovered
}

fn stmt_kind(recovered: &Recovered<SourceFile>, index: usize) -> NodeKind {
    recovered.product().statements()[index].kind()
}

/// Every significant (non-trivia) token in the file must tile the source
/// contiguously, proving rescans preserved the covering property.
fn assert_tokens_tile(recovered: &Recovered<SourceFile>) {
    let file = recovered.product();
    let mut pos = 0usize;
    for token in file.tokens() {
        let range = token.range();
        assert!(
            range.start().get() >= pos,
            "token overlaps or regresses at {}",
            range.start().get()
        );
        assert!(
            range.start().get() <= range.end().get(),
            "token range inverted"
        );
        pos = range.end().get();
    }
    assert!(
        pos <= file.source_text().len_utf16().get(),
        "tokens extend past the source"
    );
}

#[test]
fn parses_variable_declaration() {
    let recovered = assert_clean("const x: number = 1;");
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::VariableDeclaration);
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    assert_eq!(decl.kind, VariableKind::Const);
    assert_eq!(decl.declarations.len(), 1);
    assert!(decl.declarations[0].data().type_annotation.is_some());
}

#[test]
fn preserves_all_scanner_tokens_and_eof() {
    let text = "let a = 1; // trailing\n";
    let source = Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
    let scanned = scan(SourceId::new(0), ScriptKind::TypeScript, source);
    let scanned_token_count = scanned.product().tokens().len();
    let recovered = parse(scanned);
    // No rescans here, so the stored stream matches the scanner's exactly.
    assert_eq!(recovered.product().tokens().len(), scanned_token_count);
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
    assert!(
        recovered
            .product()
            .tokens()
            .iter()
            .any(|t| t.kind() == TokenKind::LineComment)
    );
}

#[test]
fn diagnostics_are_ordered_and_shared() {
    let recovered = parse_ts("const = ;");
    let diagnostics = recovered.diagnostics();
    assert!(!diagnostics.is_empty());
    // The SourceFile carries the identical canonical diagnostic vector.
    assert_eq!(recovered.product().diagnostics(), diagnostics);
    let mut sorted = diagnostics.to_vec();
    sorted.sort();
    assert_eq!(sorted.as_slice(), diagnostics);
}

#[test]
fn escaped_keywords_obey_identifier_context() {
    assert!(!errors(&parse_ts("const \\u0069f = 1;")).is_empty());
    assert!(!errors(&parse_ts("\\u0069f (true) {}")).is_empty());
    assert!(!errors(&parse_ts("function* g() { \\u0079ield; }")).is_empty());
    assert!(!errors(&parse_ts("async function f() { \\u0061wait; }")).is_empty());
    assert!(!errors(&parse_ts("const value = { \\u0069f };")).is_empty());
    assert!(!errors(&parse_ts("import { \\u0069f } from 'm';")).is_empty());
    assert!(!errors(&parse_ts("export { \\u0069f };")).is_empty());

    assert!(errors(&parse_ts("const \\u0061wait = 1; const \\u0079ield = 2;")).is_empty());
    assert!(errors(&parse_ts("const value = { \\u0069f: 1 }; value.\\u0069f;")).is_empty());
    assert!(errors(&parse_ts("import { \\u0069f as value } from 'm';")).is_empty());
    assert!(errors(&parse_ts("const value = 1; export { value as \\u0069f };")).is_empty());
    assert!(errors(&parse_ts("export { \\u0069f } from 'm';")).is_empty());
}

#[test]
fn unions_lexical_and_parse_diagnostics() {
    // Unterminated string is a lexical (L-code) diagnostic; the trailing
    // `+` with no operand is a parse (P-code) diagnostic.
    let recovered = parse_ts("const s = \"oops\n + ;");
    let codes: Vec<&str> = recovered
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(codes.iter().any(|c| c.starts_with("BAMTS-L")));
    assert!(codes.iter().any(|c| c.starts_with("BAMTS-P")));
}

#[test]
fn source_kind_identity_is_preserved() {
    for kind in [
        ScriptKind::JavaScript,
        ScriptKind::TypeScript,
        ScriptKind::TypeScriptReact,
        ScriptKind::Json,
    ] {
        let recovered = parse_text("const x = 1;", kind);
        assert_eq!(recovered.product().script_kind(), kind);
        assert_eq!(recovered.product().source_id(), SourceId::new(0));
    }
}

#[test]
fn a_bare_semicolon_is_a_class_member() {
    for source in [
        "class C { ; }",
        "class C { ;;; }",
        "class C { a() {}; b = 1;; static c() {} ; }",
        "class C { #a() {}; get #b() { return 1; }; }",
    ] {
        assert_clean(source);
    }
    let recovered = assert_clean("class C { a() {}; }");
    let Statement::Class(class) = recovered.product().statements()[0].data() else {
        panic!("expected a class");
    };
    let members: Vec<_> = class.members.iter().map(|member| member.data()).collect();
    assert!(matches!(
        members[..],
        [ClassMember::Method(_), ClassMember::Semicolon]
    ));
}

#[test]
fn jsx_text_that_looks_like_a_regex_stays_text() {
    let source = "const a = <p>, /x</p>;\nconst b = <p>= /'</p>;\n";
    let parsed = parse_text(source, ScriptKind::TypeScriptReact);
    assert!(errors(&parsed).is_empty(), "{:?}", errors(&parsed));
}
#[test]
fn import_phase_syntax_parses() {
    for source in [
        "import defer * as ns from \"x\";",
        "import source x from \"x\";",
        "import source from from \"x\";",
        "import.defer(x);",
        "import.source(x);",
    ] {
        assert_clean(source);
    }
    assert!(!errors(&parse_ts("import defer { a } from \"x\";")).is_empty());
}

#[test]
fn regex_rescan_produces_literal() {
    let recovered = assert_clean("const r = /a[/]b/gi;");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(
        init.data(),
        Expression::Literal(Literal::Regex(_))
    ));
    // The rescan merged the covered tokens into one literal token.
    assert!(
        recovered
            .product()
            .tokens()
            .iter()
            .any(|t| t.kind() == TokenKind::RegularExpressionLiteral)
    );
    assert_tokens_tile(&recovered);
}

#[test]
fn division_is_not_a_regex() {
    let recovered = assert_clean("const q = a / b / c;");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(
        init.data(),
        Expression::Binary(b) if b.operator == BinaryOperator::Divide
    ));
}

#[test]
fn generic_call_versus_comparison() {
    let call = assert_clean("f<number>(1);");
    let Statement::Expression(stmt) = call.product().statements()[0].data() else {
        panic!("expected an expression statement");
    };
    let Expression::Call(c) = stmt.expression.data() else {
        panic!("expected a call, got {:?}", stmt.expression.kind());
    };
    assert!(c.type_arguments.is_some());

    // `a < b > c` is two comparisons, never a call.
    let cmp = assert_clean("const t = a < b > c;");
    let Statement::Variable(decl) = cmp.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(init.data(), Expression::Binary(_)));
}

#[test]
fn greater_than_split_closes_nested_generics() {
    let recovered = assert_clean("let m: Map<string, Array<number>> = x;");
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::VariableDeclaration);
    assert_tokens_tile(&recovered);
}

#[test]
fn parses_arrow_functions() {
    assert_clean("const f = (a: number, b: number): number => a + b;");
    assert_clean("const g = x => x * 2;");
    assert_clean("const h = async (x) => { await x; };");
    let generic = assert_clean("const id = <T>(x: T): T => x;");
    let Statement::Variable(decl) = generic.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(init.data(), Expression::Arrow(_)));
}

#[test]
fn conditional_versus_arrow_return_type() {
    // `(x): T => ...` here would fail arrow speculation because there is
    // no `=>`, so it stays a parenthesized conditional.
    let recovered = assert_clean("const v = cond ? (a) : (b);");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(init.data(), Expression::Conditional(_)));
}

#[test]
fn function_type_parameter_modifiers_keep_the_declaration_intact() {
    // Upstream reports parameter-property modifiers inside function-type
    // parameter lists semantically (TS2369, TS7006), never syntactically,
    // so `function A(): (public B) => C {}` must keep its body and bind
    // `B` as the parameter name instead of derailing into statement
    // recovery. A modifier followed by `:` or `,` stays a parameter name.
    let recovered = assert_clean(
        "function A(): (public B) => C {\n}\
             \nfunction D(): (readonly x: number) => void {\n}\
             \nfunction E(): (public: string) => void {\n}",
    );
    let mut parameter_names = Vec::new();
    for statement in recovered.product().statements() {
        let Statement::Function(function) = statement.data() else {
            panic!("every statement is a function declaration");
        };
        assert!(
            function.function.body.is_some(),
            "the declaration body must survive recovery"
        );
        let TypeNode::Function(function_type) = function
            .function
            .return_type
            .as_ref()
            .expect("annotated return type")
            .data()
            .type_node
            .data()
        else {
            panic!("the return annotation is a function type");
        };
        let [parameter] = function_type.parameters.as_slice() else {
            panic!("one type parameter per signature");
        };
        parameter_names.push(
            recovered
                .product()
                .identifier_text(parameter.name.data().token())
                .map(|name| name.into_owned())
                .unwrap_or_default(),
        );
    }
    assert_eq!(parameter_names, ["B", "x", "public"]);
}

/// Only a tag takes a bad escape, and a tag does not cover the substitutions.
#[test]
fn a_tag_takes_any_escape_in_its_own_text() {
    let escapes = |text: &str| {
        parse_ts(text)
            .diagnostics()
            .iter()
            .filter(|d| is_escape_diagnostic(d.code()))
            .count()
    };
    assert_eq!(escapes(r"tag`\xg \u12 \u{110000} \u{12`;"), 0);
    assert_eq!(escapes(r"tag`\1 \08 \8`;"), 0);
    assert_eq!(escapes(r"tag`${1}\xg${2}\u12`;"), 0);
    assert_eq!(escapes(r"tag<T>`\xg`;"), 0);
    assert_eq!(escapes(r"`\xg`;"), 1);
    assert_eq!(escapes(r"`\1`;"), 1);
    assert_eq!(escapes(r"`\u{110000}`;"), 1);
    assert_eq!(escapes(r"tag`${`\xg`}`;"), 1);
}

#[test]
fn parses_template_and_tagged_template() {
    let recovered = assert_clean("const s = `a${1 + 2}b${x}c`;");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let Expression::Template(template) = init.data() else {
        panic!("expected a template literal");
    };
    assert_eq!(template.elements.len(), 3);
    assert_eq!(template.expressions.len(), 2);
    assert_clean("tag`x${y}z`;");
}

#[test]
fn object_accessor_with_missing_body_recovers_silently() {
    // Upstream accepts `{ get foo() }` with zero diagnostics (its
    // parseFunctionBlockOrSemicolon tolerates a member-ending token), so
    // the parser must recover the accessor with a missing body instead
    // of reporting that a method body is expected.
    let recovered = assert_clean("var v = { get foo() }");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let Expression::Object(object) = init.data() else {
        panic!("expected an object literal");
    };
    let [member] = object.members.as_slice() else {
        panic!("one object member");
    };
    let ObjectMember::Method(method) = member.data() else {
        panic!("expected a method member");
    };
    assert_eq!(method.modifier, PropertyModifier::Get);
    assert!(method.function.body.is_none());
}

#[test]
fn type_member_accessor_signatures_parse_cleanly() {
    for source in [
        "interface I { get foo(): string; set foo(v: string); }",
        "type T = { get foo(): string; set foo(v: string); };",
        "interface I { get [k](): string; set [k](v: string); }",
        "declare const c: { get foo(): typeof c.foo; };",
        "type T = { get foo(): string, set foo(v: string) };",
        "interface I {\n get foo(): number\n set foo(v: number)\n}",
    ] {
        assert_clean(source);
    }
}

#[test]
fn type_member_accessor_signatures_parse_as_methods() {
    let recovered = assert_clean("type T = { get foo(): string; set foo(v: string); };");
    let Statement::TypeAlias(alias) = recovered.product().statements()[0].data() else {
        panic!("expected a type alias");
    };
    let TypeNode::Object(object) = alias.type_node.data() else {
        panic!("expected an object type");
    };
    let [first, second] = object.members.as_slice() else {
        panic!("expected two members");
    };
    assert!(matches!(first.data(), TypeMember::Method(_)));
    assert!(matches!(second.data(), TypeMember::Method(_)));
}

#[test]
fn type_member_plain_get_name_still_parses() {
    for source in [
        "interface I { get: string; }",
        "type T = { get: string; set: number; };",
        "interface I { get(): void; }",
    ] {
        assert_clean(source);
    }
}

#[test]
fn type_member_accessor_with_body_parses_as_method() {
    for source in [
        "type T = { get foo() { return 0 } };",
        "type T = { set foo(v: number) { } };",
    ] {
        let recovered = parse_ts(source);
        let diagnostics = errors(&recovered);
        let codes: Vec<_> = diagnostics.iter().map(|d| d.code().as_str()).collect();
        assert_eq!(codes, ["1183"], "expected exactly TS1183 for {source:?}");
        let Statement::TypeAlias(alias) = recovered.product().statements()[0].data() else {
            panic!("expected a type alias for {source:?}");
        };
        let TypeNode::Object(object) = alias.type_node.data() else {
            panic!("expected an object type for {source:?}");
        };
        assert!(
            matches!(object.members.as_slice(), [member] if matches!(member.data(), TypeMember::Method(_))),
            "expected one method member for {source:?}"
        );
    }
    for source in [
        "type T = { get foo() { return 0 }; bar: string };",
        "interface I { get foo() { return 0 }\nbar: string; }",
    ] {
        let recovered = parse_ts(source);
        let diagnostics = errors(&recovered);
        let codes: Vec<_> = diagnostics.iter().map(|d| d.code().as_str()).collect();
        assert_eq!(codes, ["1183"], "expected exactly TS1183 for {source:?}");
        let (members, len) = match recovered.product().statements()[0].data() {
            Statement::TypeAlias(alias) => {
                let TypeNode::Object(object) = alias.type_node.data() else {
                    panic!("expected an object type for {source:?}");
                };
                (object.members.as_slice(), 2)
            }
            Statement::Interface(declaration) => (declaration.members.as_slice(), 2),
            _ => panic!("expected a type alias or interface for {source:?}"),
        };
        assert_eq!(
            members.len(),
            len,
            "the member after the body must survive for {source:?}"
        );
        assert!(
            matches!(members[0].data(), TypeMember::Method(_)),
            "expected a method member first for {source:?}"
        );
        assert!(
            matches!(members[1].data(), TypeMember::Property(_)),
            "expected a property member after the body for {source:?}"
        );
    }
}

#[test]
fn parses_class_with_members() {
    let recovered = assert_clean(
        "class C<T> extends B implements I {\n\
             #private = 1;\n\
             static count = 0;\n\
             readonly name: string = \"c\";\n\
             constructor(public x: number) { this.x = x; }\n\
             get value(): T { return this.#private as unknown as T; }\n\
             set value(v: T) {}\n\
             method<U>(a: U): void {}\n\
             static { count = 1; }\n\
             [key: string]: unknown;\n\
             }",
    );
    let Statement::Class(class) = recovered.product().statements()[0].data() else {
        panic!("expected a class declaration");
    };
    assert!(class.extends.is_some());
    assert_eq!(class.implements.len(), 1);
    assert!(
        class
            .members
            .iter()
            .any(|m| matches!(m.data(), ClassMember::Constructor(_)))
    );
    assert!(
        class
            .members
            .iter()
            .any(|m| matches!(m.data(), ClassMember::StaticBlock(_)))
    );
    assert!(
        class
            .members
            .iter()
            .any(|m| matches!(m.data(), ClassMember::IndexSignature(_)))
    );
}

#[test]
fn parses_decorated_class() {
    let recovered = assert_clean("@sealed class C {\n@log method(@inject p: string) {}\n}");
    let Statement::Class(class) = recovered.product().statements()[0].data() else {
        panic!("expected a class declaration");
    };
    assert_eq!(class.decorators.len(), 1);
}

#[test]
fn a_bracket_after_a_decorator_starts_the_member_name() {
    let recovered = assert_clean("class C { @dec(2) [\"m\"]() {} }");
    let Statement::Class(class) = recovered.product().statements()[0].data() else {
        panic!("expected a class declaration");
    };
    let ClassMember::Method(method) = class.members[0].data() else {
        panic!("expected a method");
    };
    assert!(matches!(method.name, PropertyName::Computed(_)));
    assert!(method.function.body.is_some());
    let decorator = &method.function.decorators[0];
    assert!(matches!(
        decorator.data().expression.data(),
        Expression::Call(_)
    ));
}

#[test]
fn expression_path_decorated_class_expression_retains_decorator() {
    let recovered = assert_clean("const C = @dec class Named {}");
    let file = recovered.product();
    let Statement::Variable(decl) = file.statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let Expression::Class(class_expr) = init.data() else {
        panic!("expected a class expression, got {:?}", init.kind());
    };
    assert_eq!(class_expr.class.decorators.len(), 1);
    let decorator = &class_expr.class.decorators[0];
    let Expression::Identifier(dec) = decorator.data().expression.data() else {
        panic!("expected the decorator expression to be an identifier");
    };
    assert_eq!(file.token_text(dec.data().token()), Some("dec"));
    let Some(name) = &class_expr.class.name else {
        panic!("expected a named class expression");
    };
    assert_eq!(file.token_text(name.data().token()), Some("Named"));
    assert!(
        class_expr.class.decorators[0].range().start()
            < class_expr.class.name.as_ref().unwrap().range().start()
    );
}

#[test]
fn expression_path_malformed_decorator_recovers() {
    let recovered = parse_ts("const x = @dec 1;");
    assert!(
            errors(&recovered)
                .iter()
                .any(|d| d.code() == EXPECTED_TOKEN
                    && d.message() == "decorators must precede a class"),
            "expected BAMTS-P001 for `@dec` not followed by `class`"
        );
    assert_eq!(
        recovered.product().statements().len(),
        1,
        "malformed decorator recovery must yield one statement, not a trailing `1;`"
    );
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(
        matches!(
            init.data(),
            Expression::Missing(m) if m.expected() == NodeKind::MissingExpression
        ),
        "malformed decorator expression should yield a missing initializer"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
    assert_tokens_tile(&recovered);
}

#[test]
fn expression_path_decorated_class_expression_allows_postfix_member() {
    let recovered = assert_clean("const name = @dec class {}.name;");
    assert_eq!(
        recovered.product().statements().len(),
        1,
        "decorated class postfix must stay one statement"
    );
    let file = recovered.product();
    let Statement::Variable(decl) = file.statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let Expression::Member(member) = init.data() else {
        panic!("expected a member expression, got {:?}", init.kind());
    };
    let Expression::Class(class_expr) = member.object.data() else {
        panic!(
            "expected the member object to be a decorated class expression, got {:?}",
            member.object.kind()
        );
    };
    assert_eq!(class_expr.class.decorators.len(), 1);
    let MemberProperty::Named(prop) = &member.property else {
        panic!("expected a named member property");
    };
    assert_eq!(file.token_text(prop.data().token()), Some("name"));
    assert!(!member.optional);
}

#[test]
fn expression_path_malformed_decorator_consumes_call() {
    let recovered = parse_ts("const x = @dec foo();");
    assert!(
            errors(&recovered)
                .iter()
                .any(|d| d.code() == EXPECTED_TOKEN
                    && d.message() == "decorators must precede a class"),
            "expected BAMTS-P001 for `@dec` not followed by `class`"
        );
    assert_eq!(
        recovered.product().statements().len(),
        1,
        "malformed decorator recovery must consume `foo()` and yield one statement"
    );
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(
        matches!(
            init.data(),
            Expression::Missing(m) if m.expected() == NodeKind::MissingExpression
        ),
        "malformed decorator call recovery should yield a missing initializer"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
    assert_tokens_tile(&recovered);
}

#[test]
fn parses_interface_and_type_alias() {
    assert_clean(
        "interface Shape<T> extends Base {\n\
             readonly id: number;\n\
             name?: string;\n\
             (x: number): T;\n\
             new (x: number): T;\n\
             [key: string]: unknown;\n\
             method(a: T): void;\n\
             }",
    );
    assert_clean("type Alias<T> = { [K in keyof T]?: T[K] };");
    assert_clean("type Cond<T> = T extends string ? true : false;");
    assert_clean("type Tpl = `prefix-${string}`;");
    assert_clean("type U = A | B & C | D[];");
    assert_clean("type Fn = <T>(a: T, ...rest: number[]) => T;");
    assert_clean("type Ctor = abstract new (x: number) => object;");
    assert_clean("type Q = typeof globalThis;");
    assert_clean("type Idx = Array<string>[number];");
}

#[test]
fn type_operators_bind_after_postfix_types() {
    let readonly = assert_clean("type R = readonly Case[];");
    let Statement::TypeAlias(alias) = readonly.product().statements()[0].data() else {
        panic!("expected a type alias");
    };
    let TypeNode::Operator {
        operator: TypeOperator::Readonly,
        operand,
    } = alias.type_node.data()
    else {
        panic!("expected readonly to be the top-level type operator");
    };
    assert!(matches!(operand.data(), TypeNode::Array(_)));

    let keyof = assert_clean("type K = keyof T[];");
    let Statement::TypeAlias(alias) = keyof.product().statements()[0].data() else {
        panic!("expected a type alias");
    };
    let TypeNode::Operator {
        operator: TypeOperator::Keyof,
        operand,
    } = alias.type_node.data()
    else {
        panic!("expected keyof to be the top-level type operator");
    };
    assert!(matches!(operand.data(), TypeNode::Array(_)));

    let parenthesized = assert_clean("type P = (keyof T)[];");
    let Statement::TypeAlias(alias) = parenthesized.product().statements()[0].data() else {
        panic!("expected a type alias");
    };
    let TypeNode::Array(element) = alias.type_node.data() else {
        panic!("expected parentheses to keep the array outside keyof");
    };
    assert!(matches!(
        element.data(),
        TypeNode::Parenthesized(inner)
            if matches!(
                inner.data(),
                TypeNode::Operator {
                    operator: TypeOperator::Keyof,
                    ..
                }
            )
    ));
    let unique = assert_clean("type S = unique symbol;");
    let Statement::TypeAlias(alias) = unique.product().statements()[0].data() else {
        panic!("expected a type alias");
    };
    assert!(matches!(
        alias.type_node.data(),
        TypeNode::Operator {
            operator: TypeOperator::Unique,
            operand,
        } if matches!(operand.data(), TypeNode::Keyword(KeywordType::Symbol))
    ));
}

#[test]
fn parses_enum_and_namespace() {
    let recovered =
        assert_clean("enum Color { Red, Green = 2, Blue }\nnamespace A.B { export const x = 1; }");
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::EnumDeclaration);
    assert_eq!(stmt_kind(&recovered, 1), NodeKind::NamespaceDeclaration);
    // The dotted namespace desugars into a nested single-name namespace.
    let Statement::Namespace(outer) = recovered.product().statements()[1].data() else {
        panic!("expected a namespace");
    };
    assert!(matches!(
        outer.body.data().statements[0].data(),
        Statement::Namespace(_)
    ));
    assert_clean("const enum E { A, B }");
}

#[test]
fn parses_imports_and_exports() {
    assert_clean("import defaultExport, { a, b as c, type T } from \"mod\";");
    assert_clean("import * as ns from \"mod\";");
    assert_clean("import type { Only } from \"mod\";");
    assert_clean("import \"side-effect\";");
    assert_clean("import json from \"./x.json\" with { type: \"json\" };");
    assert_clean("import lib = require(\"lib\");");
    assert_clean("export { a, b as c };");
    assert_clean("export * as ns from \"mod\";");
    assert_clean("export default function () {}");
    assert_clean("export const value = 1;");
    assert_clean("export type { T } from \"mod\";");
    assert_clean("export = someValue;");
}

#[test]
fn parses_control_flow_and_loops() {
    assert_clean(
        "for (let i = 0; i < 10; i++) {}\n\
             for (const x of xs) {}\n\
             for (const k in obj) {}\n\
             for await (const y of gen()) {}\n\
             while (a) {}\n\
             do {} while (b);\n\
             switch (n) { case 1: break; default: break; }\n\
             try { f(); } catch (e) { g(); } finally { h(); }\n\
             label: for (;;) { continue label; }",
    );
}

#[test]
fn parses_destructuring_and_assignment() {
    assert_clean("const { a, b: { c }, d = 1, ...rest } = obj;");
    assert_clean("const [x, , y = 2, ...zs] = arr;");
    assert_clean("({ a, b } = source);");
    assert_clean("[first, second] = pair;");
    assert_clean("obj.prop ??= fallback;");
}

#[test]
fn parses_optional_chaining_and_nonnull() {
    assert_clean("const v = a?.b?.[c]?.(d)!.e;");
    assert_clean("const w = obj!.field;");
}

#[test]
fn parses_as_const_and_satisfies() {
    assert_clean("const config = { a: 1 } as const;");
    assert_clean("const point = { x: 0 } satisfies Point;");
    assert_clean("const n = value as unknown as number;");
    assert_clean("const q = <const>[1, 2, 3];");
    assert_clean("const p = <const>{ x: 1 };");
}

#[test]
fn parses_new_meta_and_import_expressions() {
    assert_clean("const a = new Foo<number>(1, 2);");
    assert_clean("function f() { return new.target; }");
    assert_clean("const m = import.meta.url;");
    assert_clean("const p = import(\"mod\");");
}

#[test]
fn asi_allows_missing_semicolons() {
    let recovered = assert_clean("const a = 1\nconst b = 2\nreturn\na");
    // `return` then `a` on the next line are two statements (ASI).
    assert!(recovered.product().statements().len() >= 3);
}

#[test]
fn typescript_syntax_in_javascript_is_diagnosed() {
    let recovered = parse_text("const x: number = 1;", ScriptKind::JavaScript);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|d| d.code() == TYPESCRIPT_SYNTAX_IN_JAVASCRIPT)
    );
    // Recovery still produced a variable declaration.
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::VariableDeclaration);
}

fn parse_tsx(text: &str) -> Recovered<SourceFile> {
    parse_text(text, ScriptKind::TypeScriptReact)
}

fn jsx_initializer(recovered: &Recovered<SourceFile>) -> &Expr {
    let Statement::Variable(declaration) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    declaration.declarations[0]
        .data()
        .initializer
        .as_deref()
        .expect("the declarator has an initializer")
}

#[test]
fn jsx_self_closing_element() {
    let recovered = parse_tsx("const a = <Foo />;");
    assert!(errors(&recovered).is_empty(), "{:?}", errors(&recovered));
    let Expression::JsxSelfClosingElement(element) = jsx_initializer(&recovered).data() else {
        panic!("expected a self-closing element");
    };
    assert!(matches!(element.name, JsxElementName::Identifier(_)));
    assert!(element.attributes.is_empty());
}

#[test]
fn jsx_balanced_element_with_children() {
    let recovered = parse_tsx("const a = <Foo attr={x}>text{expr}<Child />more</Foo>;");
    assert!(errors(&recovered).is_empty(), "{:?}", errors(&recovered));
    let Expression::JsxElement(element) = jsx_initializer(&recovered).data() else {
        panic!("expected a balanced element");
    };
    assert_eq!(element.opening.data().attributes.len(), 1);
    assert_eq!(element.children.len(), 4);
    assert!(matches!(element.children[0], JsxChild::Text(_)));
    assert!(matches!(
        element.children[1],
        JsxChild::ExpressionContainer(_)
    ));
    assert!(matches!(element.children[2], JsxChild::Element(_)));
    assert!(matches!(element.children[3], JsxChild::Text(_)));
    assert!(matches!(
        element.closing.data().name,
        JsxElementName::Identifier(_)
    ));
}

#[test]
fn jsx_fragment() {
    let recovered = parse_tsx("const a = <>{child}<Foo /></>;");
    assert!(errors(&recovered).is_empty(), "{:?}", errors(&recovered));
    let Expression::JsxFragment(fragment) = jsx_initializer(&recovered).data() else {
        panic!("expected a fragment");
    };
    assert_eq!(fragment.children.len(), 2);
    assert!(matches!(
        fragment.children[0],
        JsxChild::ExpressionContainer(_)
    ));
    assert!(matches!(fragment.children[1], JsxChild::Element(_)));

    let empty = parse_tsx("const a = <></>;");
    assert!(errors(&empty).is_empty(), "{:?}", errors(&empty));
    let Expression::JsxFragment(fragment) = jsx_initializer(&empty).data() else {
        panic!("expected an empty fragment");
    };
    assert!(fragment.children.is_empty());
}

#[test]
fn jsx_member_qualified_names() {
    let recovered = parse_tsx("const a = <Foo.Bar.Baz />;\nconst b = <my:Card />;");
    assert!(errors(&recovered).is_empty(), "{:?}", errors(&recovered));
    let Statement::Variable(first) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let Expression::JsxSelfClosingElement(member) = first.declarations[0]
        .data()
        .initializer
        .as_deref()
        .unwrap()
        .data()
    else {
        panic!("expected a self-closing element");
    };
    let JsxElementName::Member(outer) = &member.name else {
        panic!("expected a member name");
    };
    assert!(matches!(*outer.object, JsxElementName::Member(_)));

    let Statement::Variable(second) = recovered.product().statements()[1].data() else {
        panic!("expected a variable declaration");
    };
    let Expression::JsxSelfClosingElement(namespaced) = second.declarations[0]
        .data()
        .initializer
        .as_deref()
        .unwrap()
        .data()
    else {
        panic!("expected a self-closing element");
    };
    assert!(matches!(namespaced.name, JsxElementName::Namespace(_)));
}

#[test]
fn jsx_attributes_all_forms() {
    let recovered = parse_tsx("const a = <Foo bool str=\"s\" expr={x} {...rest} ns:name />;");
    assert!(errors(&recovered).is_empty(), "{:?}", errors(&recovered));
    let Expression::JsxSelfClosingElement(element) = jsx_initializer(&recovered).data() else {
        panic!("expected a self-closing element");
    };
    assert_eq!(element.attributes.len(), 5);
    assert!(matches!(
        &element.attributes[0],
        JsxAttributeItem::Attribute(attribute) if attribute.data().initializer.is_none()
    ));
    assert!(matches!(
        &element.attributes[1],
        JsxAttributeItem::Attribute(attribute)
            if matches!(attribute.data().initializer, Some(JsxAttributeInitializer::String(_)))
    ));
    assert!(matches!(
        &element.attributes[2],
        JsxAttributeItem::Attribute(attribute)
            if matches!(attribute.data().initializer, Some(JsxAttributeInitializer::Expression(_)))
    ));
    assert!(matches!(
        &element.attributes[3],
        JsxAttributeItem::Spread(_)
    ));
    assert!(matches!(
        &element.attributes[4],
        JsxAttributeItem::Attribute(attribute)
            if matches!(attribute.data().name, JsxAttributeName::Namespace(_))
    ));
}

#[test]
fn jsx_recovery_missing_closing_tag() {
    // A truncated closing tag must recover into a `JsxElement` with
    // diagnostics rather than panic.
    let recovered = parse_tsx("const a = <Foo>hi</Foo");
    assert!(!errors(&recovered).is_empty());
    assert!(matches!(
        jsx_initializer(&recovered).data(),
        Expression::JsxElement(_)
    ));
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);

    // A name mismatch is a diagnostic, not a panic.
    let mismatch = parse_tsx("const a = <Foo>hi</Bar>;");
    assert!(!errors(&mismatch).is_empty());
    assert!(matches!(
        jsx_initializer(&mismatch).data(),
        Expression::JsxElement(_)
    ));
}

#[test]
fn jsx_type_argument_disambiguation_in_ts_vs_tsx() {
    // `.ts`: `<T>x` is a type assertion, never JSX.
    let ts = parse_text("const a = <T>x;", ScriptKind::TypeScript);
    let Statement::Variable(declaration) = ts.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let assertion = declaration.declarations[0]
        .data()
        .initializer
        .as_deref()
        .unwrap();
    assert!(
        matches!(assertion.data(), Expression::TypeAssertion(_)),
        "ts: {:?}",
        assertion.data()
    );

    // `.tsx`: the same leading `<T>` opens a JSX element.
    let tsx = parse_tsx("const a = <T>x</T>;");
    assert!(errors(&tsx).is_empty(), "{:?}", errors(&tsx));
    assert!(
        matches!(jsx_initializer(&tsx).data(), Expression::JsxElement(_)),
        "tsx: {:?}",
        jsx_initializer(&tsx).data()
    );
}

#[test]
fn recovers_from_garbage_with_progress() {
    // Pure garbage must terminate, emit diagnostics, and tile tokens.
    let recovered = parse_ts("@#$%^&");
    assert!(!errors(&recovered).is_empty());
    assert_tokens_tile(&recovered);
    // A missing close brace still yields a block statement.
    let unbalanced = parse_ts("function f() { if (a) {");
    assert!(!errors(&unbalanced).is_empty());
    assert_eq!(unbalanced.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn discarded_jsx_speculation_does_not_suppress_lexical_diagnostics() {
    // `(…): T` makes `paren_arrow_follow` return `Colon`, so
    // `try_parse_arrow_function` speculatively parses a parameter list
    // via `speculate_paren_arrow`. In `.tsx` the parameter default
    // `<div>` triggers a JSX rescan that records a `jsx_spans` entry.
    // With no `=>` after the return type the speculation is rolled back.
    // A rolled-back JSX span must not survive: `rollback()` must truncate
    // `jsx_spans` so the discarded rescan does not suppress the default
    // scanner's lexical diagnostics for that range in the final
    // `parse()` diagnostic filter.
    //
    // This is tested at the parser-method level because the public
    // `parse()` entry point re-parses the same `<div>` as JSX after
    // rollback — in TSX `<` in expression position always triggers
    // `rescan_jsx_span` — which re-commits an identical span and masks
    // the bug. The contract under test (rollback undoes `jsx_spans`
    // growth) is observable only between the speculation rollback and
    // the re-parse, i.e. directly on the `Parser` before `parse()`
    // runs its diagnostic-filtering epilogue.
    let source = Arc::new(
        SourceText::new("(x = <div>\u{1}</div>): T").expect("test source fits the per-file budget"),
    );
    let scanned = scan(SourceId::new(0), ScriptKind::TypeScriptReact, source);
    let (scanned, _lexical) = scanned.into_parts();
    let mut parser = Parser::new(
        scanned.source_id(),
        scanned.script_kind(),
        Arc::clone(scanned.source()),
        scanned.tokens().to_vec(),
        *scanned.eof(),
    );

    // Drives the full speculation path: `paren_arrow_follow` → `Colon`,
    // `speculate_paren_arrow` checkpoints, parses the parameter default
    // `<div>\u{1}</div>` (recording a jsx_span), parses `: T`, finds no
    // `=>`, and rolls back.
    assert!(
        parser.try_parse_arrow_function(false).is_none(),
        "input is not an arrow function"
    );

    // After rollback the discarded JSX span must be gone. If it survives,
    // `parse()` would suppress the L005 diagnostic for the control byte
    // inside the would-be JSX text — the exact bug the fix targets.
    assert!(
        parser.jsx_spans.is_empty(),
        "rolled-back JSX span survived: {:?}",
        parser.jsx_spans,
    );
}

#[test]
fn deeply_nested_input_does_not_overflow() {
    let text = format!("const x = {}1{};", "(".repeat(5000), ")".repeat(5000));
    let recovered = parse_ts(&text);
    // The depth guard converts excessive nesting into diagnostics rather
    // than a stack overflow, and the parser still terminates.
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP)
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn deeply_nested_type_operator_chain_is_iterative_and_bounded() {
    let text = format!("type T = {}number;", "keyof ".repeat(20_000));
    let recovered = parse_ts(&text);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code() == NESTING_TOO_DEEP),
        "the type-operator depth budget must emit BAMTS-P010"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);

    let text = format!(
        "type U = {}{}number{};",
        "keyof ".repeat(200),
        "(".repeat(200),
        ")".repeat(200)
    );
    let recovered = parse_ts(&text);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code() == NESTING_TOO_DEEP),
        "operator and operand nesting must share one depth budget"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn parser_max_depth_boundary() {
    // Drive the depth guard directly: depths 1..=MAX_DEPTH are admitted,
    // the (MAX_DEPTH + 1)-th enter is rejected with the typed BAMTS-P010
    // diagnostic, and the guard unwinds without ever panicking.
    let source = Arc::new(SourceText::new("1").expect("test source fits the per-file budget"));
    let scanned = scan(
        SourceId::new(0),
        ScriptKind::TypeScript,
        Arc::clone(&source),
    );
    let tokens = scanned.product().tokens().to_vec();
    let eof = *scanned.product().eof();
    let mut parser = Parser::new(
        SourceId::new(0),
        ScriptKind::TypeScript,
        source,
        tokens,
        eof,
    );

    for depth in 1..MAX_DEPTH {
        assert!(parser.enter(), "depth {depth} must be admitted");
    }
    assert!(parser.enter(), "depth {MAX_DEPTH} must be admitted");
    let crossed = parser.enter();
    assert!(!crossed, "the {}-th enter must be rejected", MAX_DEPTH + 1);
    assert!(
        parser
            .diagnostics
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "the rejected enter records BAMTS-P010 NESTING_TOO_DEEP"
    );

    // Recovery: the rejected enter did not leak a frame, every admitted
    // frame unwinds back to zero, and the parser still observes the real
    // token stream and its end-of-file.
    for _ in 0..MAX_DEPTH {
        parser.leave();
    }
    assert_eq!(parser.depth, 0);
    assert_eq!(parser.kind(), TokenKind::NumericLiteral);
    parser.bump();
    assert!(parser.at_eof());

    // The same boundary holds end to end. A spaced prefix-minus chain
    // spends one frame per operator on top of the four
    // statement/expression frames, so 251 operators bottom out at exactly
    // MAX_DEPTH live frames and parse cleanly, while 252 operators cross
    // the budget and recover with the typed diagnostic instead of a stack
    // overflow. (Unspaced runs would lex as `--` decrement pairs.)
    let accepted = format!("const a = {}1;", "- ".repeat(251));
    let recovered = parse_ts(&accepted);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .all(|d| d.code() != NESTING_TOO_DEEP),
        "a chain bottoming out at {MAX_DEPTH} frames must parse cleanly"
    );

    let rejected = format!("const b = {}1;", "- ".repeat(252));
    let recovered = parse_ts(&rejected);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "one operator past the budget must be diagnosed, not panicked on"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn deeply_nested_list_is_iterative() {
    // A long flat argument list must not recurse per element.
    let args = "0,".repeat(20000);
    let text = format!("f({args}0);");
    let recovered = parse_ts(&text);
    assert!(
        errors(&recovered).is_empty(),
        "flat list should parse cleanly"
    );
}

#[test]
fn missing_binding_is_diagnosed() {
    let recovered = parse_ts("const = 1;");
    assert!(
        errors(&recovered)
            .iter()
            .any(|d| d.code() == EXPECTED_IDENTIFIER)
    );
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::VariableDeclaration);
}

#[test]
fn empty_source_parses() {
    let recovered = parse_ts("");
    assert!(recovered.product().statements().is_empty());
    assert!(errors(&recovered).is_empty());
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn parses_using_declarations() {
    assert_clean("{ using handle = acquire(); }");
    assert_clean("async function f() { await using h = acquire(); }");
}

#[test]
fn full_range_spans_source() {
    let text = "const x = 1;\nconst y = 2;\n";
    let recovered = parse_ts(text);
    let range = recovered.product().range();
    assert_eq!(range.start(), Utf16Pos::ZERO);
    assert_eq!(range.end(), recovered.product().source_text().len_utf16());
}

#[test]
fn exponentiation_is_right_associative() {
    let recovered = assert_clean("const x = 2 ** 3 ** 2;");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let Expression::Binary(outer) = init.data() else {
        panic!("expected a binary expression, got {:?}", init.kind());
    };
    assert_eq!(outer.operator, BinaryOperator::Exponentiate);
    // Right-associative: the right operand is itself `3 ** 2`, and the left
    // operand is the atom `2`, never a nested exponentiation.
    let Expression::Binary(right) = outer.right.data() else {
        panic!("expected the right operand to be `3 ** 2`");
    };
    assert_eq!(right.operator, BinaryOperator::Exponentiate);
    assert!(!matches!(outer.left.data(), Expression::Binary(_)));
}

#[test]
fn unary_left_operand_of_exponent_is_rejected() {
    // ECMAScript forbids an unparenthesized unary on the left of `**`.
    let neg = parse_ts("const x = -2 ** 2;");
    assert!(
        errors(&neg).iter().any(|d| d.code() == UNEXPECTED_TOKEN),
        "expected a diagnostic for `-2 ** 2`"
    );
    let awaited = parse_ts("async function f() { return await p ** 2; }");
    assert!(
        errors(&awaited)
            .iter()
            .any(|d| d.code() == UNEXPECTED_TOKEN),
        "expected a diagnostic for `await p ** 2`"
    );
    // Parenthesizing restores validity, and a unary on the right is allowed.
    assert_clean("const y = (-2) ** 2;");
    assert_clean("const z = 2 ** -3;");
}

#[test]
fn parses_typed_using_declaration() {
    let recovered = assert_clean("using handle: Disposable = acquire();");
    let Statement::Variable(decl) = recovered.product().statements()[0].data() else {
        panic!(
            "expected a using declaration, got {:?}",
            stmt_kind(&recovered, 0)
        );
    };
    assert_eq!(decl.kind, VariableKind::Using);
    assert!(decl.declarations[0].data().type_annotation.is_some());
    // `await using` with a type annotation, and an object/generic type whose
    // brackets contain a `;` that must not end the disambiguation scan early.
    assert_clean("async function f() { await using h: AsyncDisposable = acquire(); }");
    let nested = assert_clean("using o: { a: number; b: string } = make();");
    let Statement::Variable(decl) = nested.product().statements()[0].data() else {
        panic!("expected a using declaration");
    };
    assert_eq!(decl.kind, VariableKind::Using);
    assert!(decl.declarations[0].data().type_annotation.is_some());
}

#[test]
fn using_as_identifier_is_not_a_declaration() {
    // A non-binding after `using` keeps it an ordinary expression.
    let member = assert_clean("using.dispose = handle;");
    assert!(matches!(
        member.product().statements()[0].data(),
        Statement::Expression(_)
    ));
    let bare = assert_clean("using;");
    assert!(matches!(
        bare.product().statements()[0].data(),
        Statement::Expression(_)
    ));
    // A newline before the binding defeats the contextual keyword (ASI).
    let split = assert_clean("using\nx = 1;");
    assert!(matches!(
        split.product().statements()[0].data(),
        Statement::Expression(_)
    ));
    // A `:` with no top-level `=` is not a typed declaration either.
    let no_init = parse_ts("using x: number;");
    assert!(matches!(
        no_init.product().statements()[0].data(),
        Statement::Expression(_)
    ));
}

#[test]
fn using_declaration_requires_initializer() {
    // Missing initializers are reported by the checker (BAMTS-C035), not the parser.
    let missing = parse_ts("{ using x; }");
    assert!(
        !errors(&missing)
            .iter()
            .any(|d| d.code().as_str().starts_with("BAMTS-P"))
    );
    let Statement::Block(block) = missing.product().statements()[0].data() else {
        panic!("expected a block");
    };
    assert!(matches!(
        block.data().statements[0].data(),
        Statement::Variable(_)
    ));

    let awaited = parse_ts("async function f() { await using h; }");
    assert!(
        !errors(&awaited)
            .iter()
            .any(|d| d.code().as_str().starts_with("BAMTS-P"))
    );
}
#[test]
fn using_declaration_accepts_pattern_binding_for_checker() {
    // Pattern `using` bindings are reported by the checker (BAMTS-C034), not the parser.
    let recovered = parse_ts("{ using a = acquire(), { b } = obj; }");
    assert!(
        !errors(&recovered)
            .iter()
            .any(|d| d.code().as_str().starts_with("BAMTS-P"))
    );
}

#[test]
fn using_for_in_and_classic_heads_are_rejected() {
    let for_in = parse_ts("for (using x in obj) {}");
    assert_eq!(stmt_kind(&for_in, 0), NodeKind::ForInStatement);

    let classic = parse_ts("for (using x = acquire(); false; ) {}");
    assert_eq!(stmt_kind(&classic, 0), NodeKind::ForStatement);

    let await_in = parse_ts("async function f() { for (await using x in obj) {} }");
    assert_eq!(stmt_kind(&await_in, 0), NodeKind::FunctionDeclaration);
}
#[test]
fn sloppy_var_initializer_in_for_in_parses() {
    let recovered = assert_clean("for (var x = 1 in obj) {}");
    let Statement::ForIn(for_in) = recovered.product().statements()[0].data() else {
        panic!("expected for-in");
    };
    let ForBinding::Variable(decl) = &for_in.binding else {
        panic!("expected a variable binding");
    };
    assert_eq!(decl.kind, VariableKind::Var);
    assert!(decl.declarations[0].data().initializer.is_some());

    assert!(!errors(&parse_ts("for (let x = 1 in obj) {}")).is_empty());
    assert!(!errors(&parse_ts("for (var {a} = b in obj) {}")).is_empty());
    assert!(!errors(&parse_ts("for (var x = 1 of y) {}")).is_empty());
}

#[test]
fn async_identifier_cannot_head_a_for_of() {
    assert!(!errors(&parse_ts("for (async of [1]) {}")).is_empty());
    assert!(!errors(&parse_ts("for (/*c*/async of [1]) {}")).is_empty());
    assert!(!errors(&parse_ts("for (async /*c*/ of [1]) {}")).is_empty());
    assert_clean("for (x of [1]) {}");
    assert_clean("for (async in obj) {}");
    assert_clean("for ((async) of [7]) {}");
    assert_clean("for (\\u0061sync of [7]) {}");
    assert_clean("for (async.x of [7]) {}");
    assert_clean("for (async of => {}; ;);");
    assert_clean("async function f() { for await (async of [1]) {} }");
}

#[test]
fn duplicate_switch_default_is_accepted() {
    assert_clean("switch (v) { default: break; default: break; }");
    assert_clean("switch (v) { case 0: break; default: break; }");
}
#[test]
fn heritage_trailing_comma_reports_ts1009() {
    for text in [
        "class C extends A, {\n}",
        "class C extends A, implements B, {\n}",
        "class C implements B, {\n}",
    ] {
        let found = errors(&parse_ts(text))
            .iter()
            .filter(|d| d.message() == "trailing comma is not allowed")
            .map(|d| {
                (
                    d.code(),
                    d.range(),
                    crate::diagnostics_parser::typescript_parse_code(d.code(), d.message()),
                )
            })
            .collect::<Vec<_>>();
        assert!(
            !found.is_empty(),
            "expected a trailing comma diagnostic for {text:?}"
        );
        assert!(
            found
                .iter()
                .all(|(code, _, _)| code.as_str() == "BAMTS-P001"),
            "trailing comma stays BAMTS-P001 for {text:?}"
        );
        assert!(
            found
                .iter()
                .all(|(_, _, ts)| ts.as_ref().is_some_and(|code| code.as_str() == "TS1009")),
            "trailing comma projects to TS1009 for {text:?}"
        );
    }
    assert_eq!(
        errors(&parse_ts("class C extends A, implements B, {\n}"))
            .iter()
            .filter(|d| d.message() == "trailing comma is not allowed")
            .count(),
        2
    );
}

#[test]
fn heritage_list_continues_past_comma() {
    let text = "class C extends A, B {\n}";
    let parsed = parse_ts(text);
    let extra = errors(&parsed);
    assert_eq!(
        extra.len(),
        1,
        "expected exactly the extra-extends diagnostic, got: {:?}",
        extra
            .iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        extra[0].code().as_str(),
        "1174",
        "expected TS1174 for {text:?}"
    );
    assert_eq!(
        extra[0].message(),
        "Classes can only extend a single class.",
        "expected the TS1174 template for {text:?}"
    );
    let at = text.find(", B").expect("extra expression") + 2;
    assert_eq!(
        (extra[0].range().start().get(), extra[0].range().end().get()),
        (at, at + 1),
        "the diagnostic anchors on the extra expression"
    );
    assert_clean("class C implements I, J {\n}");
    assert_clean("interface I extends A, B {\n}");
}

#[test]
fn type_literal_accessors_parse_without_syntax_errors() {
    for text in [
        "type A = {\n    get foo() { return 0 }\n};\n",
        "type B = {\n    set foo(v: any) { }\n};\n",
        "interface X {\n    get foo() { return 0 }\n}\n",
        "interface Y {\n    set foo(v: any) { }\n}\n",
    ] {
        let parsed = parse_ts(text);
        let diagnostics = errors(&parsed);
        let codes: Vec<_> = diagnostics.iter().map(|d| d.code().as_str()).collect();
        assert_eq!(codes, ["1183"], "expected exactly TS1183 for {text:?}");
    }
    assert_clean("interface Z {\n    get foo(): number;\n}\n");
}

#[test]
fn json_data_unit_reports_no_syntax_diagnostics() {
    for text in [
        "{ \"name\": \"foo\", \"version\": \"1.2.3\" }\n",
        "{}\n",
        "[]\n",
        "[\"a\", null, \"string\"]\n",
        "-10\n",
        "{\n    \"a\": true,\n    \"b\": \"hello\",\n}\n",
        "\"just a string\"\n",
        "/* leading */ { \"a\": 1, } // trailing\n",
        "// only a comment\n{ \"a\": [1, 2, { \"b\": null }] }\n",
    ] {
        let recovered = parse_text(text, ScriptKind::Json);
        assert!(
            errors(&recovered).is_empty(),
            "expected no errors for {text:?}, got: {:?}",
            errors(&recovered)
                .iter()
                .map(|d| (d.code().as_str(), d.message()))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn json_malformed_unit_keeps_typescript_diagnostics() {
    for text in [
        "{ \"a\": }\n",
        "{ \"a\" \"b\" }\n",
        "[1 2]\n",
        "{ 'a': 1 }\n",
        "{ \"a\": 1\n",
        "[1, 2\n",
        "{ \"a\": 1 } trailing\n",
    ] {
        assert!(
            !errors(&parse_text(text, ScriptKind::Json)).is_empty(),
            "expected errors for {text:?}"
        );
    }
}

#[test]
fn using_for_of_heads_remain_parseable() {
    let sync = assert_clean("for (using x of items) {}");
    let Statement::ForOf(for_of) = sync.product().statements()[0].data() else {
        panic!("expected for-of");
    };
    let ForBinding::Variable(decl) = &for_of.binding else {
        panic!("expected a variable binding");
    };
    assert_eq!(decl.kind, VariableKind::Using);

    let async_of = assert_clean("async function f() { for await (await using x of items) {} }");
    let Statement::Function(func) = async_of.product().statements()[0].data() else {
        panic!("expected a function");
    };
    let Some(FunctionBody::Block(body)) = func.function.body.as_ref() else {
        panic!("expected a block body");
    };
    let Statement::ForOf(for_of) = body.data().statements[0].data() else {
        panic!("expected for-of inside async function");
    };
    let ForBinding::Variable(decl) = &for_of.binding else {
        panic!("expected a variable binding");
    };
    assert_eq!(decl.kind, VariableKind::AwaitUsing);
    assert_eq!(for_of.mode, ForOfMode::Async);
}

#[test]
fn arrow_requires_no_newline_before_fat_arrow() {
    // Same line is a valid arrow, including the typed and generic forms.
    assert_clean("const f = (a) => a;");
    assert_clean("const g = (a): number => a;");
    assert_clean("const gen = <T>(x: T) => x;");
    // A newline before `=>` breaks the restricted production: `(a)` is a
    // parenthesized expression, not an arrow, and the dangling `=>` errors.
    let broken = parse_ts("const f = (a)\n=> a;");
    assert!(
        !errors(&broken).is_empty(),
        "a newline before `=>` must not parse as an arrow"
    );
    let Statement::Variable(decl) = broken.product().statements()[0].data() else {
        panic!("expected a variable declaration");
    };
    let init = decl.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    assert!(matches!(init.data(), Expression::Parenthesized(_)));
    // The typed and generic speculative paths reject a newline as well.
    assert!(!errors(&parse_ts("const h = (a: number)\n=> a;")).is_empty());
    assert!(!errors(&parse_ts("const i = <T>(x: T)\n=> x;")).is_empty());
    assert!(!errors(&parse_ts("const j = async (x)\n=> x;")).is_empty());
}

#[test]
fn deeply_nested_hostile_expression_recovers() {
    // A prefix-unary chain previously recursed once per operator and would
    // overflow the native stack; the depth budget now bounds it to a stable
    // diagnostic and the parse still terminates at end-of-file.
    let unary = format!("const a = {}1;", "-".repeat(20_000));
    let ru = parse_ts(&unary);
    assert!(
        ru.diagnostics()
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "the depth budget must fire on a deep unary chain"
    );
    assert_eq!(ru.product().eof().kind(), TokenKind::EndOfFile);

    // The right-recursive `**` operator likewise recurses per operator.
    let exp = format!("const b = {}2;", "2 ** ".repeat(20_000));
    let re = parse_ts(&exp);
    assert!(
        re.diagnostics()
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "the depth budget must fire on a deep `**` chain"
    );
    assert_eq!(re.product().eof().kind(), TokenKind::EndOfFile);

    // All guarded edges combined: unary, `**`, and parentheses at once.
    let combo = format!(
        "const c = {}{}{}1{};",
        "-".repeat(5_000),
        "2 ** ".repeat(5_000),
        "(".repeat(5_000),
        ")".repeat(5_000),
    );
    let rc = parse_ts(&combo);
    assert!(
        rc.diagnostics()
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "the depth budget must fire on combined hostile nesting"
    );
    assert_eq!(rc.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn parses_ambient_string_module_with_exact_name_range() {
    let recovered = assert_clean("declare module \"express\" { export interface X {} }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare wrapper");
    };
    let Statement::Namespace(namespace) = inner.data() else {
        panic!("expected namespace");
    };
    let NamespaceName::StringLiteral(name) = &namespace.name else {
        panic!("expected string literal name");
    };
    let text = recovered
        .product()
        .token_text(name.data().token())
        .expect("literal text");
    assert_eq!(text, "\"express\"");
    assert_eq!(
        name.range().start().get(),
        text_start(recovered.product(), "\"express\"")
    );
    assert_eq!(
        name.range().end().get(),
        text_start(recovered.product(), "\"express\"") + "\"express\"".encode_utf16().count()
    );
}

#[test]
fn parses_declare_global_with_keyword_range() {
    let recovered = assert_clean("declare global { interface Window { x: number } }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare wrapper");
    };
    let Statement::Namespace(namespace) = inner.data() else {
        panic!("expected namespace");
    };
    let NamespaceName::Global { range } = &namespace.name else {
        panic!("expected global name");
    };
    assert_eq!(
        range.start().get(),
        text_start(recovered.product(), "global")
    );
    assert_eq!(
        range.end().get(),
        text_start(recovered.product(), "global") + "global".encode_utf16().count()
    );
}

#[test]
fn parses_declare_module_identifier_and_dotted() {
    let ident = assert_clean("declare module Foo {}");
    let Statement::Declare(inner) = ident.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(namespace) = inner.data() else {
        panic!("expected namespace");
    };
    assert!(matches!(
        namespace.name,
        NamespaceName::Identifier {
            keyword: NamespaceKeyword::Module,
            ..
        }
    ));

    let dotted = assert_clean("declare module A.B {}");
    let Statement::Declare(inner) = dotted.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    let NamespaceName::Identifier { name, keyword } = &outer.name else {
        panic!("expected identifier name");
    };
    assert_eq!(*keyword, NamespaceKeyword::Module);
    assert_eq!(
        dotted.product().token_text(name.data().token()).unwrap(),
        "A"
    );
    assert!(matches!(
        outer.body.data().statements[0].data(),
        Statement::Namespace(_)
    ));
}

#[test]
fn parses_deep_identifier_namespace() {
    let recovered = assert_clean("namespace A.B.C {}");
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::NamespaceDeclaration);
    let Statement::Namespace(outer) = recovered.product().statements()[0].data() else {
        panic!("expected namespace");
    };
    let Statement::Namespace(mid) = outer.body.data().statements[0].data() else {
        panic!("expected nested namespace");
    };
    assert!(matches!(
        mid.body.data().statements[0].data(),
        Statement::Namespace(_)
    ));
}

#[test]
fn dotted_namespace_within_depth_parses_cleanly() {
    let names = (0..50)
        .map(|i| format!("N{i}"))
        .collect::<Vec<_>>()
        .join(".");
    let source = format!("namespace {names} {{}}");
    let recovered = assert_clean(&source);
    assert_eq!(stmt_kind(&recovered, 0), NodeKind::NamespaceDeclaration);
    let Statement::Namespace(outer) = recovered.product().statements()[0].data() else {
        panic!("expected a namespace");
    };
    assert!(matches!(
        outer.body.data().statements[0].data(),
        Statement::Namespace(_)
    ));
}

#[test]
fn deep_dotted_namespace_rejects_recursion_with_nesting_diagnostic() {
    let names = (0..260)
        .map(|i| format!("N{i}"))
        .collect::<Vec<_>>()
        .join(".");
    let source = format!("namespace {names} {{}}");
    let recovered = parse_ts(&source);
    assert!(
        errors(&recovered)
            .iter()
            .any(|d| d.code() == NESTING_TOO_DEEP),
        "a 260-segment dotted namespace must emit BAMTS-P010 instead of overflowing"
    );
    assert_eq!(recovered.product().eof().kind(), TokenKind::EndOfFile);
}

#[test]
fn declare_module_non_name_recovers_with_missing_identifier() {
    let recovered = parse_ts("declare module 123 {}");
    assert!(
        errors(&recovered)
            .iter()
            .any(|d| d.code() == EXPECTED_IDENTIFIER)
    );
    assert_tokens_tile(&recovered);
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(namespace) = inner.data() else {
        panic!("expected namespace");
    };
    let NamespaceName::Identifier { name, .. } = &namespace.name else {
        panic!("expected missing identifier recovery");
    };
    assert!(name.data().token().is_missing());
}

#[test]
fn bare_string_module_is_p003() {
    let recovered = parse_ts("module \"pkg\" {}");
    let errs = errors(&recovered);
    assert!(
        errs.iter().any(|d| {
            d.code() == EXPECTED_IDENTIFIER
                && d.message()
                    .contains("only allowed in an ambient declaration")
        }),
        "expected P003 ambient-only message, got: {:?}",
        errs.iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
    let Statement::Namespace(namespace) = recovered.product().statements()[0].data() else {
        panic!("expected namespace");
    };
    assert!(matches!(namespace.name, NamespaceName::StringLiteral(_)));
}

#[test]
fn bare_global_remains_identifier_namespace() {
    let recovered = assert_clean("global {}");
    let Statement::Namespace(namespace) = recovered.product().statements()[0].data() else {
        panic!("expected namespace");
    };
    let NamespaceName::Identifier { name, .. } = &namespace.name else {
        panic!("expected identifier global");
    };
    assert_eq!(
        recovered.product().token_text(name.data().token()).unwrap(),
        "global"
    );
}

#[test]
fn ambient_string_module_preserves_single_quotes() {
    let recovered = assert_clean("declare module 'lib' {}");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(namespace) = inner.data() else {
        panic!("expected namespace");
    };
    let NamespaceName::StringLiteral(name) = &namespace.name else {
        panic!("expected string literal");
    };
    assert_eq!(
        recovered.product().token_text(name.data().token()).unwrap(),
        "'lib'"
    );
}

#[test]
fn ambient_module_in_javascript_is_still_typescript_syntax() {
    let recovered = parse_text("declare module \"x\" {}", ScriptKind::JavaScript);
    assert!(
        recovered
            .diagnostics()
            .iter()
            .any(|d| d.code() == TYPESCRIPT_SYNTAX_IN_JAVASCRIPT)
    );
}

#[test]
fn nested_global_inside_declare_namespace_is_identifier_not_augmentation() {
    let recovered = assert_clean("declare namespace N { global { interface Leaked {} } }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    assert!(matches!(
        outer.name,
        NamespaceName::Identifier {
            keyword: NamespaceKeyword::Namespace,
            ..
        }
    ));
    let Statement::Namespace(nested) = outer.body.data().statements[0].data() else {
        panic!("expected nested namespace");
    };
    assert!(
        matches!(
            nested.name,
            NamespaceName::Identifier {
                keyword: NamespaceKeyword::Namespace,
                ..
            }
        ),
        "nested global must not become Global augmentation under body-scoped declare"
    );
}

#[test]
fn nested_string_module_inside_declare_namespace_is_p003() {
    let recovered = parse_ts("declare namespace N { module \"x\" {} }");
    let errs = errors(&recovered);
    assert!(
        errs.iter().any(|d| {
            d.code() == EXPECTED_IDENTIFIER
                && d.message()
                    .contains("only allowed in an ambient declaration")
        }),
        "nested string module must not inherit declare: {:?}",
        errs.iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    let Statement::Namespace(nested) = outer.body.data().statements[0].data() else {
        panic!("expected nested module");
    };
    assert!(matches!(nested.name, NamespaceName::StringLiteral(_)));
}

#[test]
fn namespace_keyword_is_preserved_on_identifier_names() {
    let recovered = assert_clean("namespace Foo {}");
    let Statement::Namespace(namespace) = recovered.product().statements()[0].data() else {
        panic!("expected namespace");
    };
    assert!(matches!(
        namespace.name,
        NamespaceName::Identifier {
            keyword: NamespaceKeyword::Namespace,
            ..
        }
    ));
}

#[test]
fn ambient_module_body_allows_nested_string_module() {
    // tsc 7.0.2 accepts `declare module "y" { module "x" {} }`.
    let recovered = assert_clean("declare module \"y\" { module \"x\" { export interface I {} } }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    assert!(matches!(outer.name, NamespaceName::StringLiteral(_)));
    let Statement::Namespace(nested) = outer.body.data().statements[0].data() else {
        panic!("expected nested module");
    };
    assert!(matches!(nested.name, NamespaceName::StringLiteral(_)));
}

#[test]
fn ambient_module_body_allows_nested_global_augmentation() {
    // tsc 7.0.2 accepts `declare module "y" { global { ... } }` (TS2669
    // allows global augmentations directly nested in ambient modules).
    let recovered = assert_clean("declare module \"y\" { global { interface G {} } }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    assert!(matches!(outer.name, NamespaceName::StringLiteral(_)));
    let Statement::Namespace(nested) = outer.body.data().statements[0].data() else {
        panic!("expected nested global");
    };
    assert!(matches!(nested.name, NamespaceName::Global { .. }));
}

#[test]
fn nested_string_module_body_is_not_ambient() {
    // tsc 7.0.2 rejects `declare module "y" { module "x" { module "z" {} } }`
    // with TS2435; the innermost string module must not be accepted.
    let recovered = parse_ts("declare module \"y\" { module \"x\" { module \"z\" {} } }");
    let errs = errors(&recovered);
    assert!(
        errs.iter().any(|d| {
            d.code() == EXPECTED_IDENTIFIER
                && d.message()
                    .contains("only allowed in an ambient declaration")
        }),
        "a module nested inside a nested ambient module body must be rejected: {:?}",
        errs.iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn nested_global_inside_nested_string_module_is_identifier() {
    // tsc 7.0.2 rejects `declare module "y" { module "x" { global {} } }`
    // (TS2669); the global must not become an augmentation.
    let recovered = assert_clean("declare module \"y\" { module \"x\" { global {} } }");
    let Statement::Declare(inner) = recovered.product().statements()[0].data() else {
        panic!("expected declare");
    };
    let Statement::Namespace(outer) = inner.data() else {
        panic!("expected namespace");
    };
    let Statement::Namespace(mid) = outer.body.data().statements[0].data() else {
        panic!("expected nested module");
    };
    let Statement::Namespace(nested) = mid.body.data().statements[0].data() else {
        panic!("expected nested global namespace");
    };
    assert!(
        matches!(
            nested.name,
            NamespaceName::Identifier {
                keyword: NamespaceKeyword::Namespace,
                ..
            }
        ),
        "nested global must not become an augmentation"
    );
}

#[test]
fn global_body_is_not_ambient_for_nested_string_module() {
    // tsc 7.0.2 rejects `declare global { module "x" {} }`; the string
    // module inside the global body must not be accepted.
    let recovered = parse_ts("declare global { module \"x\" {} }");
    let errs = errors(&recovered);
    assert!(
        errs.iter().any(|d| {
            d.code() == EXPECTED_IDENTIFIER
                && d.message()
                    .contains("only allowed in an ambient declaration")
        }),
        "a string module inside a global body must be rejected: {:?}",
        errs.iter()
            .map(|d| (d.code().as_str(), d.message()))
            .collect::<Vec<_>>()
    );
}

fn text_start(file: &SourceFile, needle: &str) -> usize {
    let source = file.source_text().as_str();
    let byte = source.find(needle).expect("needle present");
    source[..byte].encode_utf16().count()
}

#[test]
fn parse_cancellation_returns_typed_error() {
    let source =
        Arc::new(SourceText::new("const x = 1;".to_owned()).expect("test source fits budget"));
    let scanned = crate::scanner::scan(SourceId::new(0), ScriptKind::TypeScript, source);
    let cancel = CancellationToken::new();
    cancel.cancel();
    let result = parse_with_cancel(scanned, cancel);
    assert!(
        matches!(result, Err(ParseError::Cancelled(_))),
        "cancelled parse must return ParseError::Cancelled"
    );
}
#[test]
fn parses_static_import_attributes_across_module_forms() {
    let recovered = assert_clean(
        "import 'side' with { 'type': 'json', mode: 'lazy' };\n\
             import data from 'legacy' assert { type: 'json' };\n\
             export { value } from 'named' with { type: 'json' };\n\
             export * as ns from 'all' with { type: 'json' };",
    );
    let statements = recovered.product().statements();
    let Statement::Import(side_effect) = statements[0].data() else {
        panic!("expected side-effect import")
    };
    assert_eq!(side_effect.attributes.as_ref().unwrap().entries.len(), 2);
    let Statement::Import(legacy) = statements[1].data() else {
        panic!("expected legacy asserted import")
    };
    assert_eq!(legacy.attributes.as_ref().unwrap().entries.len(), 1);
    let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
        attributes,
        ..
    })) = statements[2].data()
    else {
        panic!("expected named re-export")
    };
    assert_eq!(attributes.as_ref().unwrap().entries.len(), 1);
    let Statement::Export(ExportDeclaration::All(export_all)) = statements[3].data() else {
        panic!("expected namespace re-export")
    };
    assert_eq!(export_all.attributes.as_ref().unwrap().entries.len(), 1);
}

#[test]
fn static_import_attributes_survive_line_terminators() {
    let recovered = assert_clean(
        "import 'mod'\nwith { type: 'json' };\n\
             import data from 'legacy'\nassert { type: 'json' };\n\
             export { value } from 'out'\nwith { type: 'json' };",
    );
    let statements = recovered.product().statements();
    let Statement::Import(side_effect) = statements[0].data() else {
        panic!("expected side-effect import")
    };
    assert!(side_effect.attributes.is_some());
    let Statement::Import(legacy) = statements[1].data() else {
        panic!("expected asserted import")
    };
    assert!(legacy.attributes.is_some());
    let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
        attributes,
        ..
    })) = statements[2].data()
    else {
        panic!("expected re-export")
    };
    assert!(attributes.is_some());

    let disambiguated = assert_clean("import 'scope'\nwith (scope) { value; }");
    let Statement::Import(import) = disambiguated.product().statements()[0].data() else {
        panic!("expected import declaration")
    };
    assert!(import.attributes.is_none());
    assert_eq!(disambiguated.product().statements().len(), 2);
}

#[test]
fn parses_dynamic_and_import_type_attribute_options() {
    let recovered = assert_clean(
        "const promise = import('mod', { with: { type: 'json' } },);\n\
             type Payload = import('legacy', { assert: { type: 'json' } });",
    );
    let Statement::Variable(declaration) = recovered.product().statements()[0].data() else {
        panic!("expected dynamic import declaration")
    };
    let Expression::Import(import) = declaration.declarations[0]
        .data()
        .initializer
        .as_ref()
        .expect("initializer")
        .data()
    else {
        panic!("expected import expression")
    };
    assert!(import.options.is_some());

    let Statement::TypeAlias(alias) = recovered.product().statements()[1].data() else {
        panic!("expected type alias")
    };
    let TypeNode::Import(import_type) = alias.type_node.data() else {
        panic!("expected import type")
    };
    assert_eq!(import_type.attributes.as_ref().unwrap().entries.len(), 1);
}

#[test]
fn parses_decorated_abstract_default_export() {
    let recovered = assert_clean("export default @sealed abstract class C {}");
    let Statement::Export(ExportDeclaration::Default(export)) =
        recovered.product().statements()[0].data()
    else {
        panic!("expected default export")
    };
    let ExportDefaultValue::Class(class) = &export.value else {
        panic!("expected exported class")
    };
    assert_eq!(class.decorators.len(), 1);
    assert!(class.modifiers.is_abstract);
}

#[test]
fn regex_v_rescan_keeps_slashes_inside_nested_classes() {
    let recovered = assert_clean("const pattern = /[[a]/]/v;");
    let regex = recovered
        .product()
        .tokens()
        .iter()
        .find(|token| token.kind() == TokenKind::RegularExpressionLiteral)
        .expect("regex token");
    assert_eq!(
        regex.range().end().get() - regex.range().start().get(),
        "/[[a]/]/v".len()
    );
    assert_tokens_tile(&recovered);
}
#[test]
fn invalid_assignment_target_retains_the_operand_node() {
    // `++null` – the parser must produce `AssignmentTarget::Invalid`
    // wrapping the `null` literal, not `AssignmentTarget::Missing`.
    let source =
        Arc::new(SourceText::new("var r = ++null;").expect("test source fits the per-file budget"));
    let tokens = scan(SourceId::new(0), ScriptKind::TypeScript, source);
    let parsed = parse(tokens);
    let program = parsed.product();
    let stmt = program.statements().last().expect("at least one statement");
    let crate::syntax::Statement::Variable(decl) = stmt.data() else {
        panic!("expected a variable declaration, got {:?}", stmt.data());
    };
    let init = decl
        .declarations
        .first()
        .expect("one declarator")
        .data()
        .initializer
        .as_ref()
        .expect("initializer");
    let crate::syntax::Expression::Update(update) = init.data() else {
        panic!("expected an update expression, got {:?}", init.data());
    };
    match update.argument.data() {
        crate::syntax::AssignmentTarget::Invalid(operand) => {
            // The operand must be the `null` literal.
            assert!(
                matches!(
                    operand.data(),
                    crate::syntax::Expression::Literal(crate::syntax::Literal::Null(_))
                ),
                "Invalid operand should be the null literal, got {:?}",
                operand.data()
            );
        }
        other => panic!("expected AssignmentTarget::Invalid, got {other:?}"),
    }
}
