    use super::*;
    use std::path::PathBuf;

    fn scan_text(text: &str) -> Recovered<ScannedSource> {
        let source = Arc::new(SourceText::new(text).expect("test source fits the per-file budget"));
        scan(SourceId::new(0), ScriptKind::TypeScript, source)
    }

    fn kinds(text: &str) -> Vec<TokenKind> {
        scan_text(text)
            .into_product()
            .tokens()
            .iter()
            .map(Token::kind)
            .collect()
    }

    fn significant(text: &str) -> Vec<(TokenKind, String)> {
        let product = scan_text(text).into_product();
        product
            .tokens()
            .iter()
            .filter(|token| {
                !matches!(
                    token.kind(),
                    TokenKind::Whitespace
                        | TokenKind::LineComment
                        | TokenKind::BlockComment
                        | TokenKind::Shebang
                )
            })
            .map(|token| {
                (
                    token.kind(),
                    product.token_text(token).unwrap_or_default().to_string(),
                )
            })
            .collect()
    }

    /// The stream must tile the whole source: adjacent, gap-free, and ending
    /// exactly at the source length, which the EOF token also anchors.
    fn assert_tiles(text: &str) {
        let product = scan_text(text).into_product();
        let mut cursor = 0usize;
        for token in product.tokens() {
            assert_eq!(
                token.range().start().get(),
                cursor,
                "token {:?} left a gap in {text:?}",
                token.kind()
            );
            assert!(
                !token.range().is_empty(),
                "token {:?} made no forward progress in {text:?}",
                token.kind()
            );
            cursor = token.range().end().get();
        }
        let len = product.source_text().len_utf16().get();
        assert_eq!(cursor, len, "tokens did not reach end of {text:?}");
        assert_eq!(product.eof().range().start().get(), len);
        assert_eq!(product.eof().range().end().get(), len);
        assert_eq!(product.eof().kind(), TokenKind::EndOfFile);
    }

    #[test]
    fn scanner_accepts_lone_surrogate_escape() {
        let recovered = scan_text("'\\uD800'");
        assert!(recovered.diagnostics().is_empty());
        assert_eq!(kinds("'\\uD800'"), vec![TokenKind::StringLiteral]);
    }

    #[test]
    fn escaped_reserved_word_keeps_identifier_name_context() {
        let recovered = scan_text("\\u0069f");
        assert!(recovered.diagnostics().is_empty());
        assert_eq!(
            recovered.product().tokens()[0].kind(),
            TokenKind::EscapedReservedWord
        );
    }

    #[test]
    fn escaped_await_and_yield_retain_parser_context() {
        assert_eq!(
            kinds("aw\\u0061it"),
            vec![TokenKind::EscapedContextualKeyword]
        );
        assert_eq!(
            kinds("yi\\u0065ld"),
            vec![TokenKind::EscapedContextualKeyword]
        );
    }

    #[test]
    fn empty_source_has_only_eof() {
        let product = scan_text("").into_product();
        assert!(product.tokens().is_empty());
        assert_eq!(product.eof().kind(), TokenKind::EndOfFile);
        assert_eq!(product.eof().range().len(), 0);
    }

    #[test]
    fn whitespace_and_newlines_fold_into_one_trivia_token() {
        assert_eq!(kinds(" \t\n\r\n "), vec![TokenKind::Whitespace]);
        assert_tiles(" \t\n\r\n ");
    }

    #[test]
    fn line_and_block_comments_are_trivia() {
        assert_eq!(
            kinds("// hi\n/* a */"),
            vec![
                TokenKind::LineComment,
                TokenKind::Whitespace,
                TokenKind::BlockComment,
            ]
        );
    }

    #[test]
    fn shebang_only_at_start() {
        assert_eq!(kinds("#!/usr/bin/env node\n"), {
            vec![TokenKind::Shebang, TokenKind::Whitespace]
        });
        // A `#` after the first byte is a private identifier, never a shebang.
        assert_eq!(
            significant("a\n#!x")
                .iter()
                .map(|(kind, _)| *kind)
                .collect::<Vec<_>>(),
            vec![
                TokenKind::Identifier,
                TokenKind::PrivateIdentifier,
                TokenKind::Bang,
                TokenKind::Identifier,
            ]
        );
    }

    #[test]
    fn keywords_are_distinct_from_identifiers() {
        assert_eq!(
            significant("const of asyncish"),
            vec![
                (TokenKind::KwConst, "const".into()),
                (TokenKind::KwOf, "of".into()),
                (TokenKind::Identifier, "asyncish".into()),
            ]
        );
    }

    #[test]
    fn escaped_keyword_preserves_identifier_name_context() {
        let tokens = significant(r"\u{69}f");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].0, TokenKind::EscapedReservedWord);
    }

    #[test]
    fn unicode_identifier_ranges_are_utf16() {
        // `π` occupies two UTF-8 bytes but one UTF-16 unit.
        let product = scan_text("π=1").into_product();
        let ident = &product.tokens()[0];
        assert_eq!(ident.kind(), TokenKind::Identifier);
        assert_eq!(ident.range().start().get(), 0);
        assert_eq!(ident.range().end().get(), 1);
        assert_eq!(product.tokens()[1].kind(), TokenKind::Eq);
        assert_eq!(product.tokens()[1].range().start().get(), 1);
        assert_tiles("π=1");
    }

    #[test]
    fn astral_characters_span_two_utf16_units() {
        // `𝕏` is a single code point of length 2 in UTF-16.
        let text = "\"𝕏\"";
        let product = scan_text(text).into_product();
        let string = &product.tokens()[0];
        assert_eq!(string.kind(), TokenKind::StringLiteral);
        assert_eq!(string.range().len(), 4); // quote + 2 units + quote
        assert_eq!(product.token_text(string), Some(text));
        assert_tiles(text);
    }

    #[test]
    fn strings_handle_escapes_and_report_unterminated() {
        assert_eq!(
            kinds(r#""a\"b\n\u{1F600}""#),
            vec![TokenKind::StringLiteral]
        );
        let recovered = scan_text("\"open\nnext");
        assert_eq!(
            recovered.diagnostics()[0].code(),
            UNTERMINATED_STRING,
            "a raw newline must terminate the string"
        );
        // Recovery still tiles the source and resumes after the break.
        assert_tiles("\"open\nnext");
    }

    /// Each escape fault is where `tsc` 7.0.2 reports it, in UTF-16 units:
    /// TS1125 at the bad character, TS1198 over the digits, TS1199 where the
    /// brace is missing, and TS1127 at the backslash of a name.
    #[test]
    fn escape_faults_are_where_typescript_reports_them() {
        let faults = |text: &str| -> Vec<(DiagnosticCode, usize, usize)> {
            scan_text(text)
                .diagnostics()
                .iter()
                .map(|d| (d.code(), d.range().start().get(), d.range().end().get()))
                .collect()
        };
        assert_eq!(faults(r#""\xg""#), [(INVALID_ESCAPE, 3, 4)]);
        assert_eq!(faults(r#""ab\x1""#), [(INVALID_ESCAPE, 6, 7)]);
        assert_eq!(faults("\"\\x😀\""), [(INVALID_ESCAPE, 3, 5)]);
        assert_eq!(faults(r#""\u12""#), [(INVALID_UNICODE_ESCAPE, 5, 6)]);
        assert_eq!(faults(r#""\u{}""#), [(INVALID_UNICODE_ESCAPE, 4, 5)]);
        assert_eq!(faults(r#""\u{zz}""#), [(INVALID_UNICODE_ESCAPE, 4, 5)]);
        assert_eq!(
            faults(r#""\u{1234567}""#),
            [(UNICODE_ESCAPE_OUT_OF_RANGE, 4, 11)]
        );
        assert_eq!(
            faults(r#""\u{110000""#),
            [
                (UNICODE_ESCAPE_OUT_OF_RANGE, 4, 10),
                (UNTERMINATED_UNICODE_ESCAPE, 10, 11)
            ]
        );
        assert_eq!(faults(r#""\u{10FFFF}""#), []);
        assert_eq!(faults(r#""\0" + "\0x""#), []);
        assert_eq!(faults(r"var \u{30}x"), [(UNEXPECTED_CHARACTER, 4, 5)]);
        assert_eq!(faults(r"a\u{110000}"), [(UNEXPECTED_CHARACTER, 1, 2)]);
    }

    /// `tsc` 7.0.2 rejects `\8`, `\9` and a legacy octal escape in a TypeScript
    /// file, from the backslash to the end of the escape, and suggests the `\x`
    /// form. A JavaScript string keeps them for sloppy code, and its early errors
    /// reject them in strict code. A JavaScript template rejects them in all code.
    #[test]
    fn a_typescript_file_rejects_a_legacy_octal_escape() {
        let found = |text: &str| -> Vec<(DiagnosticCode, usize, usize, String)> {
            scan_text(text)
                .diagnostics()
                .iter()
                .map(|d| {
                    let range = d.range();
                    let (start, end) = (range.start().get(), range.end().get());
                    (d.code(), start, end, d.message().to_owned())
                })
                .collect()
        };
        let octal = |start, end, hex: &str| {
            let message = format!("a legacy octal escape is not allowed; write `\\x{hex}`");
            (LEGACY_OCTAL_ESCAPE, start, end, message)
        };
        assert_eq!(found(r#""\101""#), [octal(1, 5, "41")]);
        assert_eq!(found(r#""\0123""#), [octal(1, 5, "0a")]);
        assert_eq!(found(r#""\400""#), [octal(1, 4, "20")]);
        assert_eq!(found(r#""\377""#), [octal(1, 5, "ff")]);
        assert_eq!(found(r"'a\08b'"), [octal(2, 4, "00")]);
        assert_eq!(found(r"`\1`"), [octal(1, 3, "01")]);
        let message = "the escape `\\9` is not allowed".to_owned();
        assert_eq!(
            found(r#""\9x""#),
            [(NON_OCTAL_DECIMAL_ESCAPE, 1, 3, message)]
        );
        let javascript = |text: &str| -> Vec<DiagnosticCode> {
            let source = SourceText::new(text).expect("test source fits budget");
            scan(SourceId::new(0), ScriptKind::JavaScript, Arc::new(source))
                .diagnostics()
                .iter()
                .map(Diagnostic::code)
                .collect()
        };
        assert_eq!(javascript(r#""\101" + "\8""#), []);
        assert_eq!(javascript(r"`\0` + `a${1}\1`"), [LEGACY_OCTAL_ESCAPE]);
        assert_eq!(javascript(r"`\8`"), [NON_OCTAL_DECIMAL_ESCAPE]);
    }

    #[test]
    fn unterminated_block_comment_is_diagnosed() {
        let recovered = scan_text("/* nope");
        assert_eq!(
            recovered.diagnostics()[0].code(),
            UNTERMINATED_BLOCK_COMMENT
        );
        assert_eq!(
            recovered.product().tokens()[0].kind(),
            TokenKind::BlockComment
        );
    }

    #[test]
    fn numbers_cover_all_bases_and_bigint() {
        assert_eq!(kinds("0xFF"), vec![TokenKind::NumericLiteral]);
        assert_eq!(kinds("0o17"), vec![TokenKind::NumericLiteral]);
        assert_eq!(kinds("0b1010"), vec![TokenKind::NumericLiteral]);
        assert_eq!(kinds("1_000.5e-3"), vec![TokenKind::NumericLiteral]);
        assert_eq!(kinds(".25"), vec![TokenKind::NumericLiteral]);
        assert_eq!(kinds("123n"), vec![TokenKind::BigIntLiteral]);
        assert_eq!(kinds("0xFFn"), vec![TokenKind::BigIntLiteral]);
    }

    #[test]
    fn malformed_numbers_are_diagnosed() {
        assert_eq!(
            scan_text("1__2").diagnostics()[0].code(),
            INVALID_NUMERIC_SEPARATOR
        );
        assert_eq!(
            scan_text("1_").diagnostics()[0].code(),
            INVALID_NUMERIC_SEPARATOR
        );
        assert_eq!(
            scan_text("1e").diagnostics()[0].code(),
            INVALID_NUMERIC_LITERAL
        );
        assert_eq!(
            scan_text("0x").diagnostics()[0].code(),
            INVALID_NUMERIC_LITERAL
        );
        assert_eq!(
            scan_text("0b").diagnostics()[0].code(),
            INVALID_NUMERIC_LITERAL
        );
        assert_eq!(
            scan_text("0b2").diagnostics()[0].code(),
            INVALID_NUMERIC_LITERAL
        );
        // A float or leading-zero integer cannot carry a BigInt suffix.
        assert_eq!(
            scan_text("1.5n").diagnostics()[0].code(),
            INVALID_BIGINT_LITERAL
        );
    }
    #[test]
    fn numeric_literal_followed_by_identifier_is_rejected() {
        for text in ["3in []", "00_0", "01_0", "07_0", "08_0", "09_0"] {
            assert!(!scan_text(text).diagnostics().is_empty(), "{text}");
        }
        for text in ["3 in []", "0", "00", "10_0", "0xFF"] {
            assert!(scan_text(text).diagnostics().is_empty(), "{text}");
        }
    }

    #[test]
    fn operators_take_the_longest_match() {
        assert_eq!(
            kinds(">>>= >>> >>= >> >="),
            vec![
                TokenKind::GreaterGreaterGreaterEq,
                TokenKind::Whitespace,
                TokenKind::GreaterGreaterGreater,
                TokenKind::Whitespace,
                TokenKind::GreaterGreaterEq,
                TokenKind::Whitespace,
                TokenKind::GreaterGreater,
                TokenKind::Whitespace,
                TokenKind::GreaterThanEq,
            ]
        );
        assert_eq!(
            kinds("...a?.b??c"),
            vec![
                TokenKind::DotDotDot,
                TokenKind::Identifier,
                TokenKind::QuestionDot,
                TokenKind::Identifier,
                TokenKind::QuestionQuestion,
                TokenKind::Identifier,
            ]
        );
    }

    #[test]
    fn optional_chain_before_digit_splits() {
        // `x?.5` is `x`, `?`, `.5`, not `x`, `?.`, `5`.
        assert_eq!(
            kinds("x?.5"),
            vec![
                TokenKind::Identifier,
                TokenKind::Question,
                TokenKind::NumericLiteral,
            ]
        );
    }

    #[test]
    fn private_identifier_and_missing_name() {
        assert_eq!(kinds("#field"), vec![TokenKind::PrivateIdentifier]);
        let recovered = scan_text("# ");
        assert_eq!(
            recovered.diagnostics()[0].code(),
            INVALID_PRIVATE_IDENTIFIER
        );
    }

    #[test]
    fn a_regex_holding_a_quote_does_not_break_the_template_around_it() {
        // Read as a division, the `'` opens a string that swallows the `}` and
        // leaves the template unterminated.
        let text = "`${k.replace(/'/g, \"\\\\'\")}`;\n";
        let recovered = scan_text(text);
        assert_eq!(recovered.diagnostics(), &[]);
        let tokens = significant(text);
        assert!(tokens.contains(&(TokenKind::RegularExpressionLiteral, "/'/g".to_owned())));
        assert_eq!(
            tokens.last().map(|token| token.0),
            Some(TokenKind::Semicolon)
        );
    }

    #[test]
    fn a_slash_that_cannot_divide_starts_a_regex() {
        for text in [
            "x = /'/;",
            "f(/'/);",
            "[/'/];",
            "a, /'/;",
            "a ? /'/ : b;",
            "return /'/;",
            "typeof /'/;",
            "x = /=/;",
        ] {
            assert!(
                kinds(text).contains(&TokenKind::RegularExpressionLiteral),
                "{text}"
            );
            assert_eq!(scan_text(text).diagnostics(), &[], "{text}");
        }
    }

    #[test]
    fn a_slash_after_a_keyword_named_property_stays_division() {
        for text in [
            "o.in / 2 / 1",
            "o?.in / 2 / 1",
            "o.typeof / 2 / 1",
            "o.\n  return /* name */ / 2 / 1",
        ] {
            assert!(
                !kinds(text).contains(&TokenKind::RegularExpressionLiteral),
                "{text}"
            );
        }
        assert!(kinds("x in / 2 / 1").contains(&TokenKind::RegularExpressionLiteral));
    }

    #[test]
    fn a_slash_with_an_operand_before_it_stays_division() {
        for text in [
            "a / b / c",
            "1 / 2 / 3",
            "(a) / b / c",
            "a[0] / b / c",
            "x! / 2 / 3",
            "a++ / b / c",
            "a-- / b / c",
            "f<T> / b / c",
            "{} / b / c",
            "this / b / c",
        ] {
            assert!(
                !kinds(text).contains(&TokenKind::RegularExpressionLiteral),
                "{text}"
            );
        }
    }

    #[test]
    fn a_closing_tag_slash_stays_for_the_parser() {
        assert!(!kinds("<a></a>").contains(&TokenKind::RegularExpressionLiteral));
    }

    #[test]
    fn a_slash_that_never_closes_is_left_for_the_parser_to_judge() {
        let text = "x = /abc\n";
        assert!(kinds(text).contains(&TokenKind::Slash));
        assert_eq!(scan_text(text).diagnostics(), &[]);
    }

    #[test]
    fn templates_segment_with_nested_braces() {
        // `${ {a:1} }` nests an object literal whose braces must not close the
        // substitution early.
        let text = "`h${ {a:1} }m${x}t`";
        assert_eq!(
            kinds(text),
            vec![
                TokenKind::TemplateHead,
                TokenKind::Whitespace,
                TokenKind::LBrace,
                TokenKind::Identifier,
                TokenKind::Colon,
                TokenKind::NumericLiteral,
                TokenKind::RBrace,
                TokenKind::Whitespace,
                TokenKind::TemplateMiddle,
                TokenKind::Identifier,
                TokenKind::TemplateTail,
            ]
        );
        assert_tiles(text);
    }

    #[test]
    fn no_substitution_template() {
        assert_eq!(kinds("`plain`"), vec![TokenKind::NoSubstitutionTemplate]);
    }

    #[test]
    fn unterminated_template_recovers() {
        let recovered = scan_text("`open");
        assert_eq!(recovered.diagnostics()[0].code(), UNTERMINATED_TEMPLATE);
        assert_eq!(
            recovered.product().tokens()[0].kind(),
            TokenKind::NoSubstitutionTemplate
        );
    }

    #[test]
    fn default_pass_treats_slash_as_division() {
        assert_eq!(
            kinds("a / b"),
            vec![
                TokenKind::Identifier,
                TokenKind::Whitespace,
                TokenKind::Slash,
                TokenKind::Whitespace,
                TokenKind::Identifier,
            ]
        );
    }

    #[test]
    fn rescan_regex_reinterprets_slash() {
        let source = Arc::new(
            SourceText::new(r"/ab[/]c/gi;").expect("test source fits the per-file budget"),
        );
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::JavaScript, &source);
        let slash = scanner.next_token();
        assert_eq!(slash.kind(), TokenKind::Slash);
        let regex = scanner.rescan_regex();
        assert_eq!(regex.kind(), TokenKind::RegularExpressionLiteral);
        // The character class keeps the interior `/` literal; flags follow.
        assert_eq!(regex.range().start().get(), 0);
        assert_eq!(regex.range().end().get(), r"/ab[/]c/gi".len());
        let next = scanner.next_token();
        assert_eq!(next.kind(), TokenKind::Semicolon);
    }

    #[test]
    fn rescan_regex_reports_unterminated() {
        let source =
            Arc::new(SourceText::new("/ab\nc").expect("test source fits the per-file budget"));
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::JavaScript, &source);
        scanner.next_token();
        let regex = scanner.rescan_regex();
        assert_eq!(regex.kind(), TokenKind::RegularExpressionLiteral);
        assert_eq!(scanner.diagnostics()[0].code(), UNTERMINATED_REGEX);
    }

    #[test]
    fn rescan_greater_than_splits_operator() {
        let source = Arc::new(SourceText::new(">>").expect("test source fits the per-file budget"));
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::TypeScript, &source);
        let shift = scanner.next_token();
        assert_eq!(shift.kind(), TokenKind::GreaterGreater);
        let single = scanner.rescan_greater_than();
        assert_eq!(single.kind(), TokenKind::GreaterThan);
        assert_eq!(single.range().len(), 1);
        let rest = scanner.next_token();
        assert_eq!(rest.kind(), TokenKind::GreaterThan);
    }

    #[test]
    fn jsx_operations_scan_text_names_and_attribute_strings() {
        let source = Arc::new(
            SourceText::new("hello world<").expect("test source fits the per-file budget"),
        );
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::TypeScriptReact, &source);
        let text = scanner.scan_jsx_text();
        assert_eq!(text.kind(), TokenKind::StringLiteral);
        assert_eq!(text.range().end().get(), "hello world".len());
        assert_eq!(scanner.next_token().kind(), TokenKind::LessThan);

        let names =
            Arc::new(SourceText::new("data-role=").expect("test source fits the per-file budget"));
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::TypeScriptReact, &names);
        let name = scanner.scan_jsx_identifier();
        assert_eq!(name.kind(), TokenKind::Identifier);
        assert_eq!(name.range().end().get(), "data-role".len());

        let attr =
            Arc::new(SourceText::new("'a\"b'").expect("test source fits the per-file budget"));
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::TypeScriptReact, &attr);
        let value = scanner.scan_jsx_attribute_string();
        assert_eq!(value.kind(), TokenKind::StringLiteral);
        // The other quote is content, not a terminator.
        assert_eq!(value.range().len(), 5);
    }

    #[test]
    fn jsx_span_tiles_nested_elements_fragments_and_containers() {
        for source in [
            "<div />",
            "<div></div>",
            "<><a/><b/></>",
            "<Foo.Bar ns:attr=\"x\" onClick={() => ({a: 1})}>text</Foo.Bar>",
            "<div>{`x${y}z`}</div>",
            // Malformed: each must terminate and must not corrupt later tokens.
            "<div>",
            "<div>{`x${y",
            "</div>",
            "<div / bar>",
        ] {
            let text = SourceText::new(source).expect("test source fits the per-file budget");
            let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::TypeScriptReact, &text);
            let tokens = scanner.scan_jsx_span();
            let mut cursor = 0usize;
            for token in &tokens {
                assert_eq!(token.range().start().get(), cursor, "gap in {source:?}");
                assert!(!token.range().is_empty(), "no progress in {source:?}");
                cursor = token.range().end().get();
            }
        }
    }

    #[test]
    fn unexpected_character_makes_progress() {
        let recovered = scan_text("\u{7}a");
        assert_eq!(recovered.diagnostics()[0].code(), UNEXPECTED_CHARACTER);
        assert_eq!(recovered.product().tokens()[0].kind(), TokenKind::Unknown);
        assert_eq!(
            recovered.product().tokens()[1].kind(),
            TokenKind::Identifier
        );
        assert_tiles("\u{7}a");
    }

    #[test]
    fn scanner_is_total_over_arbitrary_inputs() {
        // A battery of hostile fragments must never panic and must always tile.
        let fragments = [
            "",
            "\\",
            "\\u",
            "\\u{",
            "\\u{ZZ}",
            "0x",
            "'\\",
            "`${",
            "}",
            "/*",
            "/",
            "#",
            "\u{2028}\u{2029}",
            "𝕏\\u{1F4A9}n",
            "\"\\x1\"",
            "1_2_3n",
            "aaaa",
            "?.?.??=>>>=",
        ];
        for fragment in fragments {
            assert_tiles(fragment);
        }
    }

    #[test]
    fn corpus_cases_lex_totally_and_tile() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpus/cases");
        let mut scanned_any = false;
        for entry in std::fs::read_dir(&root).expect("corpus/cases must be readable") {
            let path = entry.expect("directory entry").path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("ts") {
                continue;
            }
            scanned_any = true;
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_default()
                .to_string();
            let text = std::fs::read_to_string(&path).expect("corpus case is UTF-8");
            let source = Arc::new(
                SourceText::new(text.clone()).expect("test source fits the per-file budget"),
            );
            let recovered = scan(SourceId::new(0), ScriptKind::TypeScript, source);
            let product = recovered.product();

            // Totality invariant: the stream tiles the source with no gaps and
            // the concatenated lexemes reproduce the source byte for byte.
            let mut cursor = 0usize;
            let mut rebuilt = String::with_capacity(text.len());
            for token in product.tokens() {
                assert_eq!(
                    token.range().start().get(),
                    cursor,
                    "{name}: gap before {:?}",
                    token.kind()
                );
                cursor = token.range().end().get();
                rebuilt.push_str(product.token_text(token).expect("token maps to a lexeme"));
            }
            assert_eq!(
                cursor,
                product.source_text().len_utf16().get(),
                "{name}: stream did not reach end of source"
            );
            assert_eq!(
                rebuilt, text,
                "{name}: lexemes did not reproduce the source"
            );

            // Every corpus driver is valid TypeScript and must lex cleanly.
            assert!(
                recovered.diagnostics().is_empty(),
                "{name}: unexpected diagnostics {:?}",
                recovered.diagnostics()
            );
        }
        assert!(scanned_any, "expected at least one corpus case");
    }

    #[test]
    fn scan_cancellation_returns_typed_error() {
        let source =
            Arc::new(SourceText::new("const x = 1;".to_owned()).expect("test source fits budget"));
        let cancel = CancellationToken::new();
        cancel.cancel();
        let result =
            super::scan_with_cancel(SourceId::new(0), ScriptKind::TypeScript, source, cancel);
        assert!(
            matches!(result, Err(ScanError::Cancelled(_))),
            "cancelled scan must return ScanError::Cancelled"
        );
    }
    #[test]
    fn unicode_identifier_continue_uses_the_unicode_property() {
        let source = "const cafe\u{0301} = 1; const join\u{203F} = 2; const escaped\\u0301 = 3;";
        let recovered = scan_text(source);
        assert!(
            recovered.diagnostics().is_empty(),
            "{:?}",
            recovered.diagnostics()
        );
        let identifiers: Vec<&str> = recovered
            .product()
            .tokens()
            .iter()
            .filter(|token| token.kind() == TokenKind::Identifier)
            .filter_map(|token| recovered.product().token_text(token))
            .collect();
        assert!(identifiers.contains(&"cafe\u{0301}"));
        assert!(identifiers.contains(&"join\u{203F}"));
        assert!(identifiers.contains(&"escaped\\u0301"));
    }

    #[test]
    fn ecmascript_whitespace_excludes_next_line() {
        for whitespace in ['\u{00A0}', '\u{1680}', '\u{2007}', '\u{202F}', '\u{FEFF}'] {
            assert_eq!(kinds(&whitespace.to_string()), vec![TokenKind::Whitespace]);
        }
        let recovered = scan_text("\u{0085}");
        assert_eq!(recovered.product().tokens()[0].kind(), TokenKind::Unknown);
        assert_eq!(recovered.diagnostics()[0].code(), UNEXPECTED_CHARACTER);
    }

    #[test]
    fn leading_zero_decimal_separators_are_rejected() {
        for source in ["0_1", "0_1n"] {
            let recovered = scan_text(source);
            assert!(
                recovered
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code() == INVALID_NUMERIC_SEPARATOR),
                "{source} must reject its separator"
            );
            assert_tiles(source);
        }
        assert!(!kinds("0_1n").contains(&TokenKind::BigIntLiteral));
    }

    #[test]
    fn incomplete_radix_bigints_recover_as_numeric_literals() {
        for source in ["0xn", "0on", "0bn"] {
            let recovered = scan_text(source);
            assert_eq!(
                recovered.product().tokens()[0].kind(),
                TokenKind::NumericLiteral
            );
            assert!(
                recovered
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code() == INVALID_NUMERIC_LITERAL)
            );
        }
    }

    #[test]
    fn regex_rescan_tracks_nested_character_classes() {
        let source =
            Arc::new(SourceText::new("/[[a]/]/v;").expect("test source fits the per-file budget"));
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::JavaScript, &source);
        assert_eq!(scanner.next_token().kind(), TokenKind::Slash);
        let regex = scanner.rescan_regex();
        assert_eq!(regex.kind(), TokenKind::RegularExpressionLiteral);
        assert_eq!(regex.range().end().get(), "/[[a]/]/v".len());
        assert_eq!(scanner.next_token().kind(), TokenKind::Semicolon);
    }

    #[test]
    fn astral_code_point_identifier_advances_two_utf16_units() {
        // U+1D627 is a single astral code point: 4 UTF-8 bytes, 2 UTF-16 units.
        // As a standalone identifier it scans as one token whose range is two
        // UTF-16 units wide, never panicking on the 4-byte boundary.
        let standalone = "\u{1D627}";
        let product = scan_text(standalone).into_product();
        let ident = &product.tokens()[0];
        assert_eq!(ident.kind(), TokenKind::Identifier);
        assert_eq!(ident.range().start().get(), 0);
        assert_eq!(ident.range().end().get(), 2);
        assert_eq!(product.token_text(ident), Some(standalone));
        assert_tiles(standalone);

        // Two astral code points inside one identifier span 4 UTF-16 units, and
        // the following `=` begins exactly at unit 4 (not at the 8-byte offset).
        let source = "\u{1D627}\u{1D627}=1";
        let product = scan_text(source).into_product();
        let ident = &product.tokens()[0];
        assert_eq!(ident.kind(), TokenKind::Identifier);
        assert_eq!(ident.range().len(), 4);
        assert_eq!(product.tokens()[1].kind(), TokenKind::Eq);
        assert_eq!(product.tokens()[1].range().start().get(), 4);
        assert_eq!(product.tokens()[2].kind(), TokenKind::NumericLiteral);
        assert_eq!(product.tokens()[2].range().start().get(), 5);
        assert_tiles(source);
    }

    #[test]
    fn astral_regex_pattern_and_flags_do_not_panic() {
        // F14: a 4-byte UTF-8 code point in the pattern body made the flag run
        // slice `text` at a UTF-16 count treated as a byte offset, panicking
        // inside a character. The flag predicate is now decided per code point.
        for body in [
            "/[\u{1D608}-\u{1D621}]/v;",
            "/[\u{1D608}-\u{1D621}][\u{1D621}-\u{1D608}]/v;",
        ] {
            let source =
                Arc::new(SourceText::new(body).expect("test source fits the per-file budget"));
            let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::JavaScript, &source);
            assert_eq!(scanner.next_token().kind(), TokenKind::Slash);
            let regex = scanner.rescan_regex();
            assert_eq!(regex.kind(), TokenKind::RegularExpressionLiteral);
            // The whole literal including the `v` flag is consumed; only `;` remains.
            assert_eq!(scanner.next_token().kind(), TokenKind::Semicolon);
        }

        // Astral flags (the regularExpressionWithNonBMPFlags shape): the flag
        // run is consumed as identifier-continue code points without slicing.
        let with_astral_flags = "/(?foo.)/\u{1D628}\u{1D62E}\u{1D634};";
        let source = Arc::new(
            SourceText::new(with_astral_flags).expect("test source fits the per-file budget"),
        );
        let mut scanner = Scanner::new(SourceId::new(0), ScriptKind::JavaScript, &source);
        assert_eq!(scanner.next_token().kind(), TokenKind::Slash);
        let regex = scanner.rescan_regex();
        assert_eq!(regex.kind(), TokenKind::RegularExpressionLiteral);
        assert_eq!(scanner.next_token().kind(), TokenKind::Semicolon);
    }
