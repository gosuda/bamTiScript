pub mod semantic;

use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};

use crate::{
    checker::{ProgramSemanticModel, SemanticModel},
    diagnostic::Diagnostic,
    lint::{CompilerLintOptions, LintProfile, LintTable, SourceDialect, rule_by_code},
    source::{ScriptKind, SourceId, TextRange, Utf16Pos},
    syntax::{
        ArrayElement, AssignmentArrayElement, AssignmentTarget, CallArgument, ClassDeclaration,
        ClassMember, ExportDeclaration, ExportDefaultValue, Expr, Expression, ForBinding,
        ForInitializer, FunctionBody, FunctionLike, InterfaceDeclaration, JsxAttributeInitializer,
        JsxAttributeItem, JsxChild, KeywordType, MemberProperty, ObjectMember, ParameterNode,
        PropertyName, SourceFile, Statement, Stmt, TokenKind, TypeAnnotationNode, TypeMember,
        TypeNode, TypeParameterList,
    },
};

#[derive(Clone, Copy)]
struct SyntaxToken<'a> {
    kind: TokenKind,
    text: &'a str,
    range: TextRange,
}

impl SyntaxToken<'_> {
    fn is(self, text: &str) -> bool {
        self.text == text
    }

    fn identifier(self) -> bool {
        matches!(
            self.kind,
            TokenKind::Identifier
                | TokenKind::EscapedContextualKeyword
                | TokenKind::PrivateIdentifier
        )
    }
}

/// Runs every syntax-only lint enabled by `levels`.
///
/// Rule identity and severity come exclusively from [`crate::lint::RULES`].
#[must_use]
pub fn analyze(source: &SourceFile, levels: &LintTable) -> Vec<Diagnostic> {
    let cooked_identifiers = source
        .tokens()
        .iter()
        .filter(|token| {
            matches!(
                token.kind(),
                TokenKind::Identifier | TokenKind::EscapedContextualKeyword
            )
        })
        .filter_map(|token| {
            let Cow::Owned(text) = source.identifier_text(token)? else {
                return None;
            };
            let range = token.range();
            Some(((range.start().get(), range.end().get()), text))
        })
        .collect::<BTreeMap<_, _>>();
    let tokens = source
        .tokens()
        .iter()
        .filter(|token| {
            !matches!(
                token.kind(),
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            )
        })
        .filter_map(|token| {
            Some(SyntaxToken {
                kind: token.kind(),
                text: cooked_identifiers
                    .get(&(token.range().start().get(), token.range().end().get()))
                    .map(String::as_str)
                    .or_else(|| source.token_text(token))?,
                range: token.range(),
            })
        })
        .collect::<Vec<_>>();
    let comments = source
        .tokens()
        .iter()
        .filter(|token| {
            matches!(
                token.kind(),
                TokenKind::LineComment | TokenKind::BlockComment
            )
        })
        .filter_map(|token| {
            Some(SyntaxToken {
                kind: token.kind(),
                text: source.token_text(token)?,
                range: token.range(),
            })
        })
        .collect::<Vec<_>>();
    let mut findings = Vec::<(&'static str, TextRange, &'static str)>::new();

    find_escape_hatches(&tokens, &comments, &mut findings);
    find_non_erasable_and_legacy(source.script_kind(), &tokens, &mut findings);
    find_modules(&tokens, &mut findings);
    find_class_fields(&tokens, &mut findings);
    find_enums(&tokens, &mut findings);
    find_declaration_merges(&tokens, &mut findings);
    find_hygiene(&tokens, &mut findings);
    find_syntactic_footguns(&tokens, &mut findings);
    find_catalog_completion(source, &tokens, &comments, &mut findings);

    let dialect = match source.script_kind() {
        ScriptKind::JavaScript | ScriptKind::JavaScriptReact => SourceDialect::JavaScript,
        ScriptKind::TypeScript | ScriptKind::TypeScriptReact | ScriptKind::Json => {
            SourceDialect::TypeScript
        }
    };
    let mut diagnostics = findings
        .into_iter()
        .filter_map(|(code, range, message)| {
            let rule = rule_by_code(code).expect("syntax rule code must be registered");
            Diagnostic::lint(
                levels.level_for_source(rule.id(), dialect),
                rule.id(),
                source.source_id(),
                range,
                message,
            )
        })
        .collect::<Vec<_>>();
    diagnostics.sort();
    diagnostics
}

/// Runs every checker-dependent rule over the frozen semantic model.
#[must_use]
pub fn analyze_semantic(
    source: &SourceFile,
    model: &SemanticModel,
    program: Option<&ProgramSemanticModel>,
    levels: &LintTable,
) -> Vec<Diagnostic> {
    semantic::analyze(source, model, program, levels)
}

/// Runs syntax rules with their settled default levels.
#[must_use]
pub fn analyze_default(source: &SourceFile) -> Vec<Diagnostic> {
    analyze(source, &LintTable::new(LintProfile::Default))
}

/// Runs compiler-option rules at the configuration boundary.
#[must_use]
pub fn analyze_compiler_options(
    options: CompilerLintOptions,
    levels: &LintTable,
    source_id: SourceId,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (enabled, code, message) in [
        (
            options.preserve_const_enums,
            "BAMTS-W082",
            "preserveConstEnums retains runtime enum objects while inlining uses",
        ),
        (
            options.emit_decorator_metadata,
            "BAMTS-W083",
            "emitDecoratorMetadata couples runtime reflection to compiler types",
        ),
        (
            !options.use_define_for_class_fields,
            "BAMTS-W084",
            "useDefineForClassFields=false selects legacy setter-invoking semantics",
        ),
    ] {
        if !enabled {
            continue;
        }
        let rule = rule_by_code(code).expect("configuration rule code must be registered");
        if let Some(diagnostic) = Diagnostic::lint(
            levels.level(rule.id()),
            rule.id(),
            source_id,
            TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("zero range is valid"),
            message,
        ) {
            diagnostics.push(diagnostic);
        }
    }
    diagnostics.sort();
    diagnostics
}

fn push(
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
    code: &'static str,
    token: SyntaxToken<'_>,
    message: &'static str,
) {
    findings.push((code, token.range, message));
}

fn find_escape_hatches(
    tokens: &[SyntaxToken<'_>],
    comments: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (index, token) in tokens.iter().copied().enumerate() {
        if token.kind == TokenKind::KwAny {
            push(
                findings,
                "BAMTS-W017",
                token,
                "explicit any bypasses static checking",
            );
        }
        if token.kind == TokenKind::KwAs
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.is("any") || next.is("unknown"))
            && tokens
                .get(index + 2)
                .is_some_and(|next| next.kind == TokenKind::KwAs)
        {
            push(
                findings,
                "BAMTS-W020",
                token,
                "double assertion bypasses type compatibility",
            );
        }
        if token.kind == TokenKind::Bang
            && index > 0
            && tokens[index - 1].identifier()
            && !tokens
                .get(index + 1)
                .is_some_and(|next| next.kind == TokenKind::Colon)
        {
            push(
                findings,
                "BAMTS-W021",
                token,
                "non-null assertion bypasses nullability proof",
            );
        }
        if token.kind == TokenKind::Bang
            && index > 0
            && tokens[index - 1].identifier()
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.kind == TokenKind::Colon)
        {
            push(
                findings,
                "BAMTS-W022",
                token,
                "definite-assignment assertion bypasses initialization proof",
            );
        }
    }
    for comment in comments {
        if ["@ts-ignore", "@ts-expect-error", "@ts-nocheck"]
            .iter()
            .any(|directive| comment.text.contains(directive))
        {
            push(
                findings,
                "BAMTS-W023",
                *comment,
                "diagnostic suppression directive hides compiler findings",
            );
        }
    }
}

fn find_non_erasable_and_legacy(
    script_kind: ScriptKind,
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (index, token) in tokens.iter().copied().enumerate() {
        if token.kind == TokenKind::KwNamespace
            && let Some((start, end)) =
                delimited_after(tokens, index, TokenKind::LBrace, TokenKind::RBrace)
            && tokens[start + 1..end].iter().any(|inner| {
                matches!(
                    inner.kind,
                    TokenKind::KwConst
                        | TokenKind::KwLet
                        | TokenKind::KwVar
                        | TokenKind::KwFunction
                        | TokenKind::KwClass
                        | TokenKind::KwEnum
                )
            })
        {
            push(
                findings,
                "BAMTS-W024",
                token,
                "runtime namespace requires non-erasable emit",
            );
        }
        if token.kind == TokenKind::KwConstructor
            && let Some((start, end)) =
                delimited_after(tokens, index, TokenKind::LParen, TokenKind::RParen)
            && tokens[start + 1..end].iter().any(|parameter| {
                matches!(
                    parameter.kind,
                    TokenKind::KwPublic
                        | TokenKind::KwPrivate
                        | TokenKind::KwProtected
                        | TokenKind::KwReadonly
                )
            })
        {
            push(
                findings,
                "BAMTS-W025",
                token,
                "parameter property requires runtime field synthesis",
            );
        }
        if token.kind == TokenKind::At {
            push(
                findings,
                "BAMTS-W026",
                token,
                "decorator syntax depends on legacy transform semantics",
            );
        }
        if token.kind == TokenKind::LessThan
            && assertion_can_start_at(tokens, index)
            && tokens.get(index + 1).is_some_and(|next| {
                next.identifier()
                    || matches!(
                        next.kind,
                        TokenKind::KwAny
                            | TokenKind::KwBigint
                            | TokenKind::KwBoolean
                            | TokenKind::KwNever
                            | TokenKind::KwNumber
                            | TokenKind::KwObject
                            | TokenKind::KwString
                            | TokenKind::KwSymbol
                            | TokenKind::KwUnknown
                    )
            })
            && tokens
                .get(index + 2)
                .is_some_and(|next| next.kind == TokenKind::GreaterThan)
            && tokens.get(index + 3).is_some_and(|next| {
                next.identifier()
                    || matches!(
                        next.kind,
                        TokenKind::NumericLiteral | TokenKind::StringLiteral | TokenKind::LParen
                    )
            })
        {
            push(
                findings,
                "BAMTS-W027",
                token,
                "angle-bracket assertion is ambiguous with JSX",
            );
        }
    }
    if matches!(
        script_kind,
        ScriptKind::TypeScriptReact | ScriptKind::JavaScriptReact
    ) {
        for (index, token) in tokens.iter().copied().enumerate() {
            if token.kind == TokenKind::LessThan && looks_like_jsx(tokens, index) {
                push(
                    findings,
                    "BAMTS-W029",
                    token,
                    "JSX syntax requires a runtime transform",
                );
                break;
            }
        }
    }
}

fn find_modules(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    let esm = tokens.iter().enumerate().any(|(index, token)| {
        (token.kind == TokenKind::KwExport
            && !tokens
                .get(index + 1)
                .is_some_and(|next| next.kind == TokenKind::Eq))
            || (token.kind == TokenKind::KwImport
                && !tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::LParen))
    });
    let common_js = tokens.iter().enumerate().find_map(|(index, token)| {
        ((token.is("require")
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.kind == TokenKind::LParen))
            || (token.is("module")
                && tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::Dot)
                && tokens.get(index + 2).is_some_and(|next| next.is("exports")))
            || (token.is("exports")
                && tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::Dot)))
        .then_some(*token)
    });

    for (index, token) in tokens.iter().copied().enumerate() {
        if (token.kind == TokenKind::KwImport
            && tokens[index + 1..tokens.len().min(index + 8)]
                .iter()
                .any(|next| next.kind == TokenKind::Eq))
            || (token.kind == TokenKind::KwExport
                && tokens
                    .get(index + 1)
                    .is_some_and(|next| next.kind == TokenKind::Eq))
        {
            push(
                findings,
                "BAMTS-W030",
                token,
                "import/export equals requires module rewriting",
            );
        }
        if token.kind == TokenKind::StringLiteral
            && is_module_source(tokens, index)
            && extensionless_relative(token.text)
        {
            push(
                findings,
                "BAMTS-W036",
                token,
                "relative ESM import omits its runtime file extension",
            );
        }
    }
    if esm {
        if let Some(token) = common_js {
            push(
                findings,
                "BAMTS-W033",
                token,
                "CommonJS binding appears in an ES module",
            );
        }
    } else if let Some(token) = tokens.first().copied() {
        push(
            findings,
            "BAMTS-W034",
            token,
            "file has implicit script rather than module semantics",
        );
    }
}

fn find_class_fields(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (class_index, class_token) in tokens.iter().copied().enumerate() {
        if class_token.kind != TokenKind::KwClass {
            continue;
        }
        let Some((start, end)) =
            delimited_after(tokens, class_index, TokenKind::LBrace, TokenKind::RBrace)
        else {
            continue;
        };
        let body = &tokens[start + 1..end];
        let mut nested = 0usize;
        for (index, token) in body.iter().copied().enumerate() {
            if matches!(
                token.kind,
                TokenKind::RBrace | TokenKind::RBracket | TokenKind::RParen
            ) {
                nested = nested.saturating_sub(1);
                continue;
            }
            if nested == 0 {
                if token.identifier()
                    && body
                        .get(index + 1)
                        .is_some_and(|next| next.kind == TokenKind::Colon)
                    && field_terminator_without_initializer(body, index + 2)
                {
                    push(
                        findings,
                        "BAMTS-W039",
                        token,
                        "uninitialized field has standard define-time runtime presence",
                    );
                }
                if matches!(token.kind, TokenKind::KwPrivate | TokenKind::KwProtected)
                    && body.get(index + 1).is_some_and(|next| next.identifier())
                    && body.get(index + 2).is_some_and(|next| {
                        matches!(
                            next.kind,
                            TokenKind::Colon | TokenKind::Eq | TokenKind::Semicolon
                        )
                    })
                {
                    push(
                        findings,
                        "BAMTS-W042",
                        token,
                        "TypeScript private field is erased rather than runtime-private",
                    );
                }
            }
            if matches!(
                token.kind,
                TokenKind::LBrace | TokenKind::LBracket | TokenKind::LParen
            ) {
                nested += 1;
            }
        }
    }
}

fn find_enums(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (index, token) in tokens.iter().copied().enumerate() {
        if token.kind != TokenKind::KwEnum {
            continue;
        }
        let is_const = index > 0 && tokens[index - 1].kind == TokenKind::KwConst;
        push(
            findings,
            if is_const { "BAMTS-W044" } else { "BAMTS-W043" },
            token,
            if is_const {
                "const enum requires compile-time use inlining"
            } else {
                "non-const enum creates a runtime object"
            },
        );
        let Some((start, end)) =
            delimited_after(tokens, index, TokenKind::LBrace, TokenKind::RBrace)
        else {
            continue;
        };
        let mut kinds = BTreeSet::new();
        for member in split_top_level(&tokens[start + 1..end], TokenKind::Comma) {
            let Some(equal) = member.iter().position(|item| item.kind == TokenKind::Eq) else {
                continue;
            };
            let initializer = &member[equal + 1..];
            if let Some(first) = initializer.first().copied() {
                if first.kind == TokenKind::StringLiteral {
                    kinds.insert("string");
                } else if first.kind == TokenKind::NumericLiteral
                    || (first.kind == TokenKind::Minus
                        && initializer
                            .get(1)
                            .is_some_and(|next| next.kind == TokenKind::NumericLiteral))
                {
                    kinds.insert("number");
                } else if initializer
                    .iter()
                    .any(|item| item.kind == TokenKind::LParen)
                {
                    push(
                        findings,
                        "BAMTS-W047",
                        first,
                        "computed enum member is not a constant expression",
                    );
                }
            }
        }
        if kinds.len() > 1 {
            push(
                findings,
                "BAMTS-W046",
                token,
                "enum mixes string and numeric members",
            );
        }
    }
}

fn find_declaration_merges(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    let mut interfaces = BTreeMap::<&str, SyntaxToken<'_>>::new();
    let mut values = BTreeMap::<&str, SyntaxToken<'_>>::new();
    let mut namespaces = BTreeMap::<&str, SyntaxToken<'_>>::new();
    for (index, token) in tokens.iter().copied().enumerate() {
        let Some(name) = tokens
            .get(index + 1)
            .copied()
            .filter(|next| next.identifier())
        else {
            continue;
        };
        match token.kind {
            TokenKind::KwInterface => {
                if interfaces.insert(name.text, name).is_some() {
                    push(
                        findings,
                        "BAMTS-W049",
                        name,
                        "same-scope interface declarations merge",
                    );
                }
            }
            TokenKind::KwClass | TokenKind::KwFunction | TokenKind::KwEnum => {
                values.insert(name.text, name);
            }
            TokenKind::KwNamespace => {
                namespaces.insert(name.text, name);
            }
            _ => {}
        }
    }
    for (name, token) in namespaces {
        if values.contains_key(name) {
            push(
                findings,
                "BAMTS-W050",
                token,
                "namespace merges with a runtime value declaration",
            );
        }
    }
    for (index, token) in tokens.iter().copied().enumerate() {
        if token.kind != TokenKind::KwDeclare {
            continue;
        }
        match tokens.get(index + 1).map(|next| next.kind) {
            Some(TokenKind::Identifier) if tokens[index + 1].is("global") => push(
                findings,
                "BAMTS-W051",
                token,
                "global augmentation mutates the global declaration environment",
            ),
            Some(TokenKind::Identifier) if tokens[index + 1].is("module") => push(
                findings,
                "BAMTS-W052",
                token,
                "module augmentation mutates another module's declarations",
            ),
            Some(
                TokenKind::KwConst
                | TokenKind::KwLet
                | TokenKind::KwVar
                | TokenKind::KwFunction
                | TokenKind::KwClass,
            ) => push(
                findings,
                "BAMTS-W053",
                token,
                "ambient value declaration has no locally verifiable runtime provider",
            ),
            _ => {}
        }
    }
}

fn find_hygiene(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (index, token) in tokens.iter().copied().enumerate() {
        if token.identifier()
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.kind == TokenKind::Colon)
            && tokens.get(index + 2).is_some_and(|statement| {
                matches!(
                    statement.kind,
                    TokenKind::KwDo
                        | TokenKind::KwFor
                        | TokenKind::KwIf
                        | TokenKind::KwSwitch
                        | TokenKind::KwTry
                        | TokenKind::KwWhile
                        | TokenKind::KwWith
                )
            })
            && !tokens.iter().enumerate().any(|(use_index, candidate)| {
                matches!(candidate.kind, TokenKind::KwBreak | TokenKind::KwContinue)
                    && tokens
                        .get(use_index + 1)
                        .is_some_and(|label| label.text == token.text)
            })
        {
            push(
                findings,
                "BAMTS-W068",
                token,
                "label is never targeted by break or continue",
            );
        }
    }

    for (index, token) in tokens.iter().copied().enumerate() {
        if matches!(
            token.kind,
            TokenKind::KwConst | TokenKind::KwLet | TokenKind::KwVar
        ) && let Some(name) = tokens
            .get(index + 1)
            .copied()
            .filter(|next| next.identifier())
            && identifier_uses(tokens, name.text) == 1
        {
            push(findings, "BAMTS-W069", name, "local binding is never read");
        }
        if token.kind == TokenKind::KwFunction
            && let Some((start, end)) =
                delimited_after(tokens, index, TokenKind::LParen, TokenKind::RParen)
        {
            for parameter in split_top_level(&tokens[start + 1..end], TokenKind::Comma) {
                if let Some(name) = parameter.iter().copied().find(|item| item.identifier())
                    && identifier_uses(tokens, name.text) == 1
                {
                    push(findings, "BAMTS-W070", name, "parameter is never read");
                }
            }
        }
    }
}

fn find_syntactic_footguns(
    tokens: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for (index, token) in tokens.iter().copied().enumerate() {
        if matches!(token.kind, TokenKind::EqEqEq | TokenKind::BangEqEq)
            && (tokens
                .get(index.wrapping_sub(1))
                .is_some_and(|side| side.is("NaN"))
                || tokens.get(index + 1).is_some_and(|side| side.is("NaN")))
        {
            push(
                findings,
                "BAMTS-W079",
                token,
                "strict comparison with NaN is always false",
            );
        }
    }
}
fn assertion_can_start_at(tokens: &[SyntaxToken<'_>], index: usize) -> bool {
    index == 0
        || tokens.get(index - 1).is_some_and(|previous| {
            matches!(
                previous.kind,
                TokenKind::Arrow
                    | TokenKind::Colon
                    | TokenKind::Comma
                    | TokenKind::Eq
                    | TokenKind::LBracket
                    | TokenKind::LParen
                    | TokenKind::KwReturn
            )
        })
}

fn looks_like_jsx(tokens: &[SyntaxToken<'_>], index: usize) -> bool {
    let Some(next) = tokens.get(index + 1).copied() else {
        return false;
    };
    let fragment = next.kind == TokenKind::GreaterThan;
    if !fragment && !next.identifier() {
        return false;
    }
    let tag = next.text;
    let limit = tokens.len().min(index + 64);
    for cursor in index + 2..limit {
        if tokens[cursor].kind == TokenKind::Semicolon {
            return false;
        }
        if tokens[cursor].kind != TokenKind::GreaterThan {
            continue;
        }
        if tokens
            .get(cursor.wrapping_sub(1))
            .is_some_and(|token| token.kind == TokenKind::Slash)
        {
            return true;
        }
        return tokens[cursor + 1..limit]
            .windows(if fragment { 3 } else { 4 })
            .any(|closing| {
                closing[0].kind == TokenKind::LessThan
                    && closing[1].kind == TokenKind::Slash
                    && if fragment {
                        closing[2].kind == TokenKind::GreaterThan
                    } else {
                        closing[2].text == tag && closing[3].kind == TokenKind::GreaterThan
                    }
            });
    }
    false
}

fn delimited_after(
    tokens: &[SyntaxToken<'_>],
    index: usize,
    open: TokenKind,
    close: TokenKind,
) -> Option<(usize, usize)> {
    let start = tokens[index..]
        .iter()
        .position(|token| token.kind == open)?
        + index;
    let mut depth = 0usize;
    for (offset, token) in tokens[start..].iter().enumerate() {
        if token.kind == open {
            depth += 1;
        } else if token.kind == close {
            depth -= 1;
            if depth == 0 {
                return Some((start, start + offset));
            }
        }
    }
    None
}

fn split_top_level<'tokens, 'source>(
    tokens: &'tokens [SyntaxToken<'source>],
    separator: TokenKind,
) -> Vec<&'tokens [SyntaxToken<'source>]> {
    let mut result = Vec::new();
    let mut start = 0usize;
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1)
            }
            kind if kind == separator && depth == 0 => {
                result.push(&tokens[start..index]);
                start = index + 1;
            }
            _ => {}
        }
    }
    result.push(&tokens[start..]);
    result
}

fn field_terminator_without_initializer(tokens: &[SyntaxToken<'_>], start: usize) -> bool {
    for token in &tokens[start..] {
        match token.kind {
            TokenKind::Eq => return false,
            TokenKind::Semicolon | TokenKind::RBrace => return true,
            _ => {}
        }
    }
    false
}

fn is_module_source(tokens: &[SyntaxToken<'_>], index: usize) -> bool {
    index > 0
        && (tokens[index - 1].kind == TokenKind::KwFrom
            || tokens[index - 1].kind == TokenKind::KwImport
            || (index > 1
                && tokens[index - 2].kind == TokenKind::KwExport
                && tokens[index - 1].kind == TokenKind::Star))
}

fn extensionless_relative(literal: &str) -> bool {
    let value = literal.trim_matches(['\'', '"']);
    if !(value.starts_with("./") || value.starts_with("../")) {
        return false;
    }
    let last = value.rsplit('/').next().unwrap_or(value);
    !last.contains('.')
}

fn identifier_uses(tokens: &[SyntaxToken<'_>], name: &str) -> usize {
    tokens
        .iter()
        .filter(|token| token.identifier() && token.text == name)
        .count()
}

fn find_catalog_completion(
    source: &SourceFile,
    tokens: &[SyntaxToken<'_>],
    comments: &[SyntaxToken<'_>],
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    let anchor = tokens.first().map_or(source.range(), |token| token.range);
    if matches!(
        source.script_kind(),
        ScriptKind::JavaScript | ScriptKind::JavaScriptReact
    ) {
        findings.push((
            "BAMTS-W054",
            anchor,
            "JavaScript source enters the typed program",
        ));
    }
    for comment in comments {
        if comment.text.contains("@type {") || comment.text.contains("@typedef {") {
            push(
                findings,
                "BAMTS-W055",
                *comment,
                "JSDoc comment carries JavaScript type syntax",
            );
        }
        if comment.text.contains("@ts-check") {
            push(
                findings,
                "BAMTS-W057",
                *comment,
                "per-file ts-check directive changes checking policy",
            );
        }
    }
    for window in tokens.windows(7) {
        if window[0].identifier()
            && window[1].kind == TokenKind::Dot
            && window[2].is("prototype")
            && window[3].kind == TokenKind::Dot
            && window[4].identifier()
            && window[5].kind == TokenKind::Eq
            && window[6].is("function")
        {
            push(
                findings,
                "BAMTS-W056",
                window[2],
                "prototype assignment implements class-like behavior",
            );
        }
    }
    visit_statement_list(source.statements(), source.script_kind(), findings);
}

fn visit_statement_list(
    statements: &[Stmt],
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    let mut reachable = true;
    for statement in statements {
        if !reachable {
            findings.push((
                "BAMTS-W067",
                statement.range(),
                "statement is unreachable after an unconditional transfer",
            ));
        }
        visit_statement(statement, script_kind, findings);
        reachable &= can_complete_normally(statement);
    }
}

fn visit_statement(
    statement: &Stmt,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    match statement.data() {
        Statement::Interface(interface) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    statement.range(),
                    "TypeScript-only interface declaration appears in JavaScript",
                ));
            }
            visit_interface(statement.range(), interface, findings);
        }
        Statement::Export(export) => match export {
            ExportDeclaration::All(_) => findings.push((
                "BAMTS-W061",
                statement.range(),
                "wildcard barrel export obscures the public surface",
            )),
            ExportDeclaration::Default(default) => {
                findings.push((
                    "BAMTS-W062",
                    statement.range(),
                    "default export permits arbitrary importer naming",
                ));
                match &default.value {
                    ExportDefaultValue::Function(function) => {
                        visit_function(statement.range(), function, script_kind, findings)
                    }
                    ExportDefaultValue::Class(class) => visit_class(class, script_kind, findings),
                    ExportDefaultValue::Expression(expression) => {
                        visit_expression(expression, script_kind, findings)
                    }
                    ExportDefaultValue::Missing(_) => {}
                    ExportDefaultValue::Interface(interface) => {
                        visit_interface(statement.range(), interface, findings)
                    }
                }
            }
            ExportDeclaration::Named(crate::syntax::ExportNamedDeclaration::Declaration(inner)) => {
                visit_statement(inner, script_kind, findings)
            }
            ExportDeclaration::Assignment(expression) => {
                visit_expression(expression, script_kind, findings)
            }
            _ => {}
        },
        Statement::Function(function) => {
            visit_function(statement.range(), &function.function, script_kind, findings)
        }
        Statement::Class(class) => visit_class(class, script_kind, findings),
        Statement::Variable(variable) => {
            for declaration in &variable.declarations {
                if is_javascript(script_kind)
                    && (declaration.data().type_annotation.is_some() || declaration.data().definite)
                {
                    findings.push((
                        "BAMTS-W085",
                        declaration.range(),
                        "TypeScript-only declaration syntax appears in JavaScript",
                    ));
                }
                if let Some(initializer) = &declaration.data().initializer {
                    visit_expression(initializer, script_kind, findings);
                }
            }
        }
        Statement::Block(block) => {
            visit_statement_list(&block.data().statements, script_kind, findings)
        }
        Statement::Expression(expression) => {
            visit_expression(&expression.expression, script_kind, findings)
        }
        Statement::If(branch) => {
            visit_expression(&branch.test, script_kind, findings);
            visit_statement(&branch.consequent, script_kind, findings);
            if let Some(alternate) = &branch.alternate {
                visit_statement(alternate, script_kind, findings);
            }
        }
        Statement::Switch(switch) => {
            visit_expression(&switch.discriminant, script_kind, findings);
            for (index, case) in switch.cases.iter().enumerate() {
                if let Some(test) = &case.data().test {
                    visit_expression(test, script_kind, findings);
                }
                if index + 1 < switch.cases.len()
                    && !case.data().consequent.is_empty()
                    && case
                        .data()
                        .consequent
                        .last()
                        .is_some_and(can_complete_normally)
                {
                    findings.push((
                        "BAMTS-W066",
                        case.range(),
                        "non-empty switch case falls through",
                    ));
                }
                visit_statement_list(&case.data().consequent, script_kind, findings);
            }
        }
        Statement::For(for_statement) => {
            if let Some(initializer) = &for_statement.initializer {
                match initializer {
                    ForInitializer::Variable(variable) => {
                        for declaration in &variable.declarations {
                            if let Some(initializer) = &declaration.data().initializer {
                                visit_expression(initializer, script_kind, findings);
                            }
                        }
                    }
                    ForInitializer::Expression(expression) => {
                        visit_expression(expression, script_kind, findings)
                    }
                }
            }
            if let Some(test) = &for_statement.test {
                visit_expression(test, script_kind, findings);
            }
            if let Some(update) = &for_statement.update {
                visit_expression(update, script_kind, findings);
            }
            visit_statement(&for_statement.body, script_kind, findings);
        }
        Statement::ForIn(for_statement) => {
            if let ForBinding::Variable(variable) = &for_statement.binding {
                for declaration in &variable.declarations {
                    if let Some(initializer) = &declaration.data().initializer {
                        visit_expression(initializer, script_kind, findings);
                    }
                }
            } else if let ForBinding::Target(target) = &for_statement.binding {
                visit_assignment_target(target, script_kind, findings);
            }
            visit_expression(&for_statement.object, script_kind, findings);
            visit_statement(&for_statement.body, script_kind, findings);
        }
        Statement::ForOf(for_statement) => {
            if let ForBinding::Variable(variable) = &for_statement.binding {
                for declaration in &variable.declarations {
                    if let Some(initializer) = &declaration.data().initializer {
                        visit_expression(initializer, script_kind, findings);
                    }
                }
            } else if let ForBinding::Target(target) = &for_statement.binding {
                visit_assignment_target(target, script_kind, findings);
            }
            visit_expression(&for_statement.iterable, script_kind, findings);
            visit_statement(&for_statement.body, script_kind, findings);
        }
        Statement::While(loop_statement) => {
            visit_expression(&loop_statement.test, script_kind, findings);
            visit_statement(&loop_statement.body, script_kind, findings);
        }
        Statement::DoWhile(loop_statement) => {
            visit_statement(&loop_statement.body, script_kind, findings);
            visit_expression(&loop_statement.test, script_kind, findings);
        }
        Statement::Try(statement) => {
            visit_statement_list(&statement.block.data().statements, script_kind, findings);
            if let Some(handler) = &statement.handler {
                visit_statement_list(
                    &handler.data().body.data().statements,
                    script_kind,
                    findings,
                );
            }
            if let Some(finalizer) = &statement.finalizer {
                visit_statement_list(&finalizer.data().statements, script_kind, findings);
            }
        }
        Statement::With(with_statement) => {
            findings.push((
                "BAMTS-W088",
                statement.range(),
                "with statement changes name resolution based on dynamic scope",
            ));
            visit_expression(&with_statement.object, script_kind, findings);
            visit_statement(&with_statement.body, script_kind, findings);
        }
        Statement::Labeled(statement) => visit_statement(&statement.body, script_kind, findings),
        Statement::Return(statement) => {
            if let Some(argument) = &statement.argument {
                visit_expression(argument, script_kind, findings);
            }
        }
        Statement::Debugger => findings.push((
            "BAMTS-W087",
            statement.range(),
            "debugger statement halts execution when developer tools are attached",
        )),
        Statement::Throw(statement) => visit_expression(&statement.argument, script_kind, findings),
        Statement::Enum(declaration) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    statement.range(),
                    "TypeScript-only declaration appears in JavaScript",
                ));
            }
            for member in &declaration.members {
                if let Some(initializer) = &member.data().initializer {
                    visit_expression(initializer, script_kind, findings);
                }
            }
        }
        Statement::Namespace(namespace) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    statement.range(),
                    "TypeScript-only declaration appears in JavaScript",
                ));
            }
            visit_statement_list(&namespace.body.data().statements, script_kind, findings);
        }
        Statement::TypeAlias(_) if is_javascript(script_kind) => findings.push((
            "BAMTS-W085",
            statement.range(),
            "TypeScript-only declaration appears in JavaScript",
        )),
        Statement::Declare(inner) => visit_statement(inner, script_kind, findings),
        _ => {}
    }
}

fn is_javascript(script_kind: ScriptKind) -> bool {
    matches!(
        script_kind,
        ScriptKind::JavaScript | ScriptKind::JavaScriptReact
    )
}

fn visit_class(
    class: &ClassDeclaration,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    if let Some(extends) = &class.extends {
        visit_expression(&extends.expression, script_kind, findings);
    }
    for decorator in &class.decorators {
        visit_expression(&decorator.data().expression, script_kind, findings);
    }
    for member in &class.members {
        match member.data() {
            ClassMember::Constructor(constructor) => {
                // Constructors share the same signature surface as other callables
                // (parameter count, mutable-array params, JS-only type syntax,
                // decorators, initializers) and must not skip it. A constructor
                // carries no return type or type parameters, so passing `None`
                // for both keeps the JS-only function-type-syntax check (W085)
                // from firing on it — that rule targets syntax a constructor
                // cannot legally have.
                visit_callable_signature(
                    member.range(),
                    &constructor.parameters,
                    None,
                    None,
                    script_kind,
                    findings,
                );
                visit_statement_list(&constructor.body.data().statements, script_kind, findings);
            }
            ClassMember::Method(method) => {
                visit_property_name(&method.name, script_kind, findings);
                visit_function(member.range(), &method.function, script_kind, findings);
            }
            ClassMember::Property(property) => {
                visit_property_name(&property.name, script_kind, findings);
                if let Some(initializer) = &property.initializer {
                    visit_expression(initializer, script_kind, findings);
                }
            }
            ClassMember::AutoAccessor(accessor) => {
                visit_property_name(&accessor.name, script_kind, findings);
                if let Some(initializer) = &accessor.initializer {
                    visit_expression(initializer, script_kind, findings);
                }
            }
            ClassMember::StaticBlock(block) => {
                visit_statement_list(&block.data().statements, script_kind, findings)
            }
            ClassMember::IndexSignature(_) | ClassMember::Missing(_) | ClassMember::Semicolon => {}
        }
    }
}

fn visit_property_name(
    name: &PropertyName,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    if let PropertyName::Computed(expression) = name {
        visit_expression(expression, script_kind, findings);
    }
}

fn visit_jsx_attributes(
    attributes: &[JsxAttributeItem],
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for attribute in attributes {
        match attribute {
            JsxAttributeItem::Attribute(attribute) => {
                if let Some(JsxAttributeInitializer::Expression(container)) =
                    &attribute.data().initializer
                    && let Some(expression) = &container.data().expression
                {
                    visit_expression(expression, script_kind, findings);
                }
            }
            JsxAttributeItem::Spread(spread) => {
                visit_expression(&spread.data().expression, script_kind, findings);
            }
        }
    }
}

fn visit_jsx_children(
    children: &[JsxChild],
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for child in children {
        match child {
            JsxChild::Text(_) => {}
            JsxChild::ExpressionContainer(container) => {
                if let Some(expression) = &container.data().expression {
                    visit_expression(expression, script_kind, findings);
                }
            }
            JsxChild::Spread(spread) => {
                visit_expression(&spread.data().expression, script_kind, findings);
            }
            JsxChild::Element(expression) => {
                visit_expression(expression, script_kind, findings);
            }
        }
    }
}

fn visit_expression(
    expression: &Expr,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    match expression.data() {
        Expression::JsxElement(element) => {
            visit_jsx_attributes(&element.opening.data().attributes, script_kind, findings);
            visit_jsx_children(&element.children, script_kind, findings);
        }
        Expression::JsxFragment(fragment) => {
            visit_jsx_children(&fragment.children, script_kind, findings);
        }
        Expression::JsxSelfClosingElement(element) => {
            visit_jsx_attributes(&element.attributes, script_kind, findings);
        }
        Expression::Template(template) => {
            for expression in &template.expressions {
                visit_expression(expression, script_kind, findings);
            }
        }
        Expression::TaggedTemplate(tagged) => {
            visit_expression(&tagged.tag, script_kind, findings);
            for expression in &tagged.template.expressions {
                visit_expression(expression, script_kind, findings);
            }
        }
        Expression::Array(array) => {
            for element in &array.elements {
                match element {
                    ArrayElement::Expression(expression) => {
                        visit_expression(expression, script_kind, findings)
                    }
                    ArrayElement::Spread(spread) => {
                        visit_expression(&spread.argument, script_kind, findings)
                    }
                    ArrayElement::Elision | ArrayElement::Missing(_) => {}
                }
            }
        }
        Expression::Object(object) => {
            for member in &object.members {
                match member.data() {
                    ObjectMember::Property(property) => {
                        visit_property_name(&property.name, script_kind, findings);
                        visit_expression(&property.value, script_kind, findings);
                    }
                    ObjectMember::Method(method) => {
                        visit_property_name(&method.name, script_kind, findings);
                        visit_function(member.range(), &method.function, script_kind, findings);
                    }
                    ObjectMember::Spread(spread) => {
                        visit_expression(&spread.argument, script_kind, findings)
                    }
                    ObjectMember::Missing(_) => {}
                }
            }
        }
        Expression::Function(function) => visit_function(
            expression.range(),
            &function.function,
            script_kind,
            findings,
        ),
        Expression::Class(class) => visit_class(&class.class, script_kind, findings),
        Expression::Arrow(arrow) => {
            visit_callable_signature(
                expression.range(),
                &arrow.parameters,
                arrow.return_type.as_ref(),
                arrow.type_parameters.as_ref(),
                script_kind,
                findings,
            );
            match &arrow.body {
                FunctionBody::Block(block) => {
                    visit_statement_list(&block.data().statements, script_kind, findings)
                }
                FunctionBody::Expression(expression) => {
                    visit_expression(expression, script_kind, findings)
                }
                FunctionBody::Missing(_) => {}
            }
        }
        Expression::Call(call) => {
            visit_expression(&call.callee, script_kind, findings);
            visit_arguments(&call.arguments, script_kind, findings);
        }
        Expression::New(call) => {
            visit_expression(&call.callee, script_kind, findings);
            visit_arguments(&call.arguments, script_kind, findings);
        }
        Expression::Member(member) => {
            visit_expression(&member.object, script_kind, findings);
            if let MemberProperty::Computed(expression) = &member.property {
                visit_expression(expression, script_kind, findings);
            }
        }
        Expression::Await(await_expression) => {
            visit_expression(&await_expression.argument, script_kind, findings)
        }
        Expression::Yield(yield_expression) => {
            if let Some(argument) = &yield_expression.argument {
                visit_expression(argument, script_kind, findings);
            }
        }
        Expression::Unary(unary) => visit_expression(&unary.argument, script_kind, findings),
        Expression::Update(update) => {
            visit_assignment_target(&update.argument, script_kind, findings)
        }
        Expression::Binary(binary) => {
            visit_expression(&binary.left, script_kind, findings);
            visit_expression(&binary.right, script_kind, findings);
        }
        Expression::Logical(logical) => {
            visit_expression(&logical.left, script_kind, findings);
            visit_expression(&logical.right, script_kind, findings);
        }
        Expression::Conditional(conditional) => {
            visit_expression(&conditional.test, script_kind, findings);
            visit_expression(&conditional.consequent, script_kind, findings);
            visit_expression(&conditional.alternate, script_kind, findings);
        }
        Expression::Assignment(assignment) => {
            visit_assignment_target(&assignment.left, script_kind, findings);
            visit_expression(&assignment.right, script_kind, findings);
        }
        Expression::Sequence(sequence) => {
            for expression in &sequence.expressions {
                visit_expression(expression, script_kind, findings);
            }
        }
        Expression::Parenthesized(expression) => {
            visit_expression(expression, script_kind, findings)
        }
        Expression::As(assertion) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    expression.range(),
                    "TypeScript-only assertion appears in JavaScript",
                ));
            }
            visit_expression(&assertion.expression, script_kind, findings);
        }
        Expression::Satisfies(assertion) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    expression.range(),
                    "TypeScript-only assertion appears in JavaScript",
                ));
            }
            visit_expression(&assertion.expression, script_kind, findings);
        }
        Expression::TypeAssertion(assertion) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    expression.range(),
                    "TypeScript-only assertion appears in JavaScript",
                ));
            }
            visit_expression(&assertion.expression, script_kind, findings);
        }
        Expression::NonNull(assertion) => {
            if is_javascript(script_kind) {
                findings.push((
                    "BAMTS-W085",
                    expression.range(),
                    "TypeScript-only assertion appears in JavaScript",
                ));
            }
            visit_expression(&assertion.expression, script_kind, findings);
        }
        Expression::Import(import) => {
            visit_expression(&import.source, script_kind, findings);
            if let Some(options) = &import.options {
                visit_expression(options, script_kind, findings);
            }
        }
        Expression::Identifier(_)
        | Expression::This
        | Expression::Super
        | Expression::Literal(_)
        | Expression::Meta(_)
        | Expression::Missing(_) => {}
    }
}

fn visit_arguments(
    arguments: &[CallArgument],
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    for argument in arguments {
        match argument {
            CallArgument::Expression(expression) => {
                visit_expression(expression, script_kind, findings)
            }
            CallArgument::Spread(spread) => {
                visit_expression(&spread.argument, script_kind, findings)
            }
            CallArgument::Missing(_) => {}
        }
    }
}

fn visit_assignment_target(
    target: &crate::syntax::AssignmentTargetNode,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    match target.data() {
        AssignmentTarget::Member(member) => {
            visit_expression(&member.object, script_kind, findings);
            if let MemberProperty::Computed(expression) = &member.property {
                visit_expression(expression, script_kind, findings);
            }
        }
        AssignmentTarget::Object(object) => {
            for property in &object.properties {
                visit_property_name(&property.name, script_kind, findings);
                visit_assignment_target(&property.target, script_kind, findings);
                if let Some(initializer) = &property.initializer {
                    visit_expression(initializer, script_kind, findings);
                }
            }
        }
        AssignmentTarget::Array(array) => {
            for element in &array.elements {
                if let AssignmentArrayElement::Target(target) = element {
                    visit_assignment_target(target, script_kind, findings);
                }
            }
        }
        AssignmentTarget::Identifier(_) | AssignmentTarget::Missing(_) => {}
        AssignmentTarget::Invalid(operand) => {
            visit_expression(operand, script_kind, findings);
        }
    }
}

fn visit_interface(
    range: TextRange,
    interface: &InterfaceDeclaration,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    findings.push((
        "BAMTS-W058",
        range,
        "interface leaves the shape open to declaration merging",
    ));
    for member in &interface.members {
        if matches!(member.data(), TypeMember::Method(_)) {
            findings.push((
                "BAMTS-W060",
                member.range(),
                "method signature retains bivariant parameter checking",
            ));
        }
    }
}

/// Returns `true` when the declared return type can represent a missing
/// return value: `undefined`, `void`, `any`, `unknown`, or any union that
/// contains one of them. Parenthesized wrappers are unwrapped.
fn return_type_admits_absence(return_type: Option<&TypeAnnotationNode>) -> bool {
    fn admits_absence(ty: &TypeNode) -> bool {
        match ty {
            TypeNode::Keyword(keyword) => matches!(
                keyword,
                KeywordType::Undefined
                    | KeywordType::Void
                    | KeywordType::Any
                    | KeywordType::Unknown
            ),
            TypeNode::Union(members) => members.iter().any(|member| admits_absence(member.data())),
            TypeNode::Parenthesized(inner) => admits_absence(inner.data()),
            _ => false,
        }
    }
    return_type.is_some_and(|annotation| admits_absence(annotation.data().type_node.data()))
}

fn visit_function(
    range: TextRange,
    function: &FunctionLike,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    visit_callable_signature(
        range,
        &function.parameters,
        function.return_type.as_ref(),
        function.type_parameters.as_ref(),
        script_kind,
        findings,
    );
    for decorator in &function.decorators {
        visit_expression(&decorator.data().expression, script_kind, findings);
    }
    match &function.body {
        Some(FunctionBody::Block(block)) => {
            if block_contains_value_return(&block.data().statements)
                && block
                    .data()
                    .statements
                    .last()
                    .is_none_or(can_complete_normally)
                && !return_type_admits_absence(function.return_type.as_ref())
            {
                findings.push((
                    "BAMTS-W065",
                    range,
                    "function has a reachable path without a returned value",
                ));
            }
            visit_statement_list(&block.data().statements, script_kind, findings);
        }
        Some(FunctionBody::Expression(expression)) => {
            visit_expression(expression, script_kind, findings)
        }
        Some(FunctionBody::Missing(_)) | None => {}
    }
}

/// Signature checks shared by function-like declarations and arrow functions:
/// parameter count, mutable-array parameters, JavaScript-only type syntax,
/// parameter decorators, and parameter initializers. Body traversal stays with
/// each form so it owns its own control-flow handling.
fn visit_callable_signature(
    range: TextRange,
    parameters: &[ParameterNode],
    return_type: Option<&TypeAnnotationNode>,
    type_parameters: Option<&TypeParameterList>,
    script_kind: ScriptKind,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    flag_parameter_count(range, parameters.len(), findings);
    for parameter in parameters {
        let data = parameter.data();
        if data.type_annotation.as_ref().is_some_and(|annotation| {
            matches!(annotation.data().type_node.data(), TypeNode::Array(_))
        }) {
            findings.push((
                "BAMTS-W059",
                parameter.range(),
                "mutable array type crosses a callable boundary",
            ));
        }
        if is_javascript(script_kind) && data.type_annotation.is_some() {
            findings.push((
                "BAMTS-W085",
                parameter.range(),
                "TypeScript-only parameter type appears in JavaScript",
            ));
        }
        for decorator in &data.decorators {
            visit_expression(&decorator.data().expression, script_kind, findings);
        }
        if let Some(initializer) = &data.initializer {
            visit_expression(initializer, script_kind, findings);
        }
    }
    if is_javascript(script_kind) && (return_type.is_some() || type_parameters.is_some()) {
        findings.push((
            "BAMTS-W085",
            range,
            "TypeScript-only function type syntax appears in JavaScript",
        ));
    }
}

fn flag_parameter_count(
    range: TextRange,
    count: usize,
    findings: &mut Vec<(&'static str, TextRange, &'static str)>,
) {
    if count >= 5 {
        findings.push((
            "BAMTS-W064",
            range,
            "callable has five or more positional parameters",
        ));
    }
}

fn block_contains_value_return(statements: &[Stmt]) -> bool {
    statements.iter().any(|statement| match statement.data() {
        Statement::Return(ret) => ret.argument.is_some(),
        Statement::Block(block) => block_contains_value_return(&block.data().statements),
        Statement::If(statement) => {
            block_contains_value_return(std::slice::from_ref(statement.consequent.as_ref()))
                || statement.alternate.as_ref().is_some_and(|alternate| {
                    block_contains_value_return(std::slice::from_ref(alternate.as_ref()))
                })
        }
        Statement::Switch(statement) => statement
            .cases
            .iter()
            .any(|case| block_contains_value_return(&case.data().consequent)),
        _ => false,
    })
}

fn can_complete_normally(statement: &Stmt) -> bool {
    match statement.data() {
        Statement::Return(_)
        | Statement::Throw(_)
        | Statement::Break(_)
        | Statement::Continue(_) => false,
        Statement::Block(block) => block
            .data()
            .statements
            .last()
            .is_none_or(can_complete_normally),
        Statement::If(statement) => statement.alternate.as_ref().is_none_or(|alternate| {
            can_complete_normally(&statement.consequent) || can_complete_normally(alternate)
        }),
        Statement::Try(statement) => {
            if statement.finalizer.as_ref().is_some_and(|block| {
                !block
                    .data()
                    .statements
                    .last()
                    .is_none_or(can_complete_normally)
            }) {
                return false;
            }
            let try_completes = statement
                .block
                .data()
                .statements
                .last()
                .is_none_or(can_complete_normally);
            let catch_completes = statement.handler.as_ref().is_some_and(|handler| {
                handler
                    .data()
                    .body
                    .data()
                    .statements
                    .last()
                    .is_none_or(can_complete_normally)
            });
            try_completes || catch_completes
        }
        Statement::Switch(statement) => {
            // Without a default the discriminant may match no case, so the
            // switch always completes normally. With a default it completes
            // normally only if some case can fall out the bottom: it ends in
            // an unlabeled `break` (which exits the switch), or it is the last
            // case and its final statement completes normally (control drops
            // out the bottom). An empty consequent is fall-through to the next
            // case and decides nothing on its own — except a trailing empty
            // case, which has nothing to fall through to and so drops out.
            let has_default = statement
                .cases
                .iter()
                .any(|case| case.data().test.is_none());
            if !has_default {
                return true;
            }
            let last_index = statement.cases.len().saturating_sub(1);
            statement.cases.iter().enumerate().any(|(index, case)| {
                let Some(last) = case.data().consequent.last() else {
                    // Empty consequent: falls through to the next case,
                    // unless it is the final case (nothing to fall into).
                    return index == last_index;
                };
                // An unlabeled break exits the switch normally. A labeled
                // break targets an enclosing statement and does not.
                if matches!(last.data(), Statement::Break(jump) if jump.label.is_none()) {
                    return true;
                }
                // Only the final case can drop out the bottom; any other
                // case that completes normally just falls through.
                index == last_index && can_complete_normally(last)
            })
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::analyze;
    use crate::{
        diagnostic::DiagnosticSeverity,
        lint::{LintLevel, LintOverride, LintProfile, LintTable, rule_by_code},
        parser, scanner,
        source::{ScriptKind, SourceId, SourceText},
    };
    use std::sync::Arc;

    fn codes(source: &str, kind: ScriptKind) -> Vec<&'static str> {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            kind,
            Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
        ));
        let mut levels = LintTable::new(LintProfile::Pedantic);
        levels
            .apply_cli(["BAMTS-W033", "BAMTS-W034"].into_iter().map(|code| {
                LintOverride::rule(
                    rule_by_code(code).expect("test rule is registered").id(),
                    LintLevel::Warn,
                    "syntax rule test",
                )
            }))
            .expect("test overrides cannot lower forbid rules");
        analyze(parsed.product(), &levels)
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    fn fires(code: &str, trigger: &str, safe: &str) {
        assert!(
            codes(trigger, ScriptKind::TypeScript).contains(&code),
            "{code} did not fire for {trigger:?}"
        );
        assert!(
            !codes(safe, ScriptKind::TypeScript).contains(&code),
            "{code} fired for {safe:?}"
        );
    }

    macro_rules! rule_test {
        ($name:ident, $code:literal, $trigger:literal, $safe:literal) => {
            #[test]
            fn $name() {
                fires($code, $trigger, $safe);
            }
        };
    }

    rule_test!(
        w017_explicit_any,
        "BAMTS-W017",
        "let value: any = 1; value;",
        "let value: unknown = 1; value;"
    );
    rule_test!(
        w020_double_assertion,
        "BAMTS-W020",
        "value as unknown as number;",
        "value as number;"
    );
    rule_test!(w021_non_null, "BAMTS-W021", "value!.name;", "value.name;");
    rule_test!(
        w022_definite_assignment,
        "BAMTS-W022",
        "class C { value!: string; }",
        "class C { value: string = ''; }"
    );
    rule_test!(
        w023_suppression,
        "BAMTS-W023",
        "// @ts-ignore\nvalue;",
        "// ordinary comment\nvalue;"
    );
    rule_test!(
        w024_runtime_namespace,
        "BAMTS-W024",
        "namespace N { export const x = 1; }",
        "namespace N { export interface X {} }"
    );
    rule_test!(
        w025_parameter_property,
        "BAMTS-W025",
        "class C { constructor(public x: number) {} }",
        "class C { constructor(x: number) {} }"
    );
    rule_test!(
        w026_decorator,
        "BAMTS-W026",
        "@sealed class C {}",
        "class C {}"
    );
    rule_test!(
        w027_angle_assertion,
        "BAMTS-W027",
        "const n = <number>value; n;",
        "const n = value as number; n;"
    );
    rule_test!(
        w030_import_equals,
        "BAMTS-W030",
        "import fs = require('fs'); fs;",
        "import * as fs from 'fs'; fs;"
    );
    rule_test!(
        w033_commonjs_esm,
        "BAMTS-W033",
        "export const x = require('x');",
        "const x = require('x'); x;"
    );
    rule_test!(
        w034_implicit_script,
        "BAMTS-W034",
        "const x = 1; x;",
        "export const x = 1;"
    );
    rule_test!(
        w036_extensionless_import,
        "BAMTS-W036",
        "import { x } from './util'; x;",
        "import { x } from './util.js'; x;"
    );
    rule_test!(
        w039_uninitialized_field,
        "BAMTS-W039",
        "class C { value: string; }",
        "class C { value: string = ''; }"
    );
    rule_test!(
        w042_private_field,
        "BAMTS-W042",
        "class C { private value = 1; }",
        "class C { #value = 1; }"
    );
    rule_test!(
        w043_runtime_enum,
        "BAMTS-W043",
        "enum Color { Red }",
        "const enum Color { Red }"
    );
    rule_test!(
        w044_const_enum,
        "BAMTS-W044",
        "const enum Code { Ok = 200 }",
        "enum Code { Ok = 200 }"
    );
    rule_test!(
        w046_heterogeneous_enum,
        "BAMTS-W046",
        "enum Answer { No = 0, Yes = 'YES' }",
        "enum Answer { No = 0, Yes = 1 }"
    );
    rule_test!(
        w047_computed_enum,
        "BAMTS-W047",
        "enum E { X = getValue() }",
        "enum E { X = 1 }"
    );
    rule_test!(
        w049_interface_merge,
        "BAMTS-W049",
        "interface Box { x: number } interface Box { y: number }",
        "interface Box { x: number } interface Bag { y: number }"
    );
    rule_test!(
        w050_namespace_value_merge,
        "BAMTS-W050",
        "function f() {} namespace f { export const x = 1; }",
        "function f() {} namespace helpers { export const x = 1; }"
    );
    rule_test!(
        w051_global_augmentation,
        "BAMTS-W051",
        "declare global { interface Window { x: number } }",
        "declare namespace Local { interface X {} }"
    );
    rule_test!(
        w052_module_augmentation,
        "BAMTS-W052",
        "declare module 'lib' { interface X { y: number } }",
        "namespace lib { interface X { y: number } }"
    );
    rule_test!(
        w053_ambient_value,
        "BAMTS-W053",
        "declare const injected: string;",
        "declare interface Injected { value: string }"
    );
    rule_test!(
        w068_unused_label,
        "BAMTS-W068",
        "outer: while (true) { break; }",
        "outer: while (true) { break outer; }"
    );
    rule_test!(
        w069_unused_local,
        "BAMTS-W069",
        "function f() { const x = 1; } f();",
        "function f() { const x = 1; return x; } f();"
    );
    rule_test!(
        w070_unused_parameter,
        "BAMTS-W070",
        "function f(value: number) { return 1; } f(1);",
        "function f(value: number) { return value; } f(1);"
    );
    rule_test!(
        w079_nan_comparison,
        "BAMTS-W079",
        "if (value === NaN) {}",
        "if (Number.isNaN(value)) {}"
    );

    #[test]
    fn w029_jsx_transform_requires_react_source_kind() {
        assert!(
            codes("const el = <Widget />;", ScriptKind::TypeScriptReact).contains(&"BAMTS-W029")
        );
        assert!(
            !codes("const n = value as number;", ScriptKind::TypeScript).contains(&"BAMTS-W029")
        );
        assert!(!codes("if (a < b) {}", ScriptKind::TypeScriptReact).contains(&"BAMTS-W029"));
    }

    #[test]
    fn javascript_is_limited_to_footgun_and_hygiene_warnings() {
        let diagnostics = codes("let value: any; value === NaN;", ScriptKind::JavaScript);
        assert!(diagnostics.contains(&"BAMTS-W079"));
        assert!(!diagnostics.contains(&"BAMTS-W017"));
    }

    #[test]
    fn double_assertion_does_not_cross_expression_boundaries() {
        let diagnostics = codes(
            "const a = value as unknown; const b = other as string;",
            ScriptKind::TypeScript,
        );
        assert!(!diagnostics.contains(&"BAMTS-W020"));
    }

    #[test]
    fn typed_local_inside_method_is_not_a_class_field() {
        let diagnostics = codes(
            "class C { method() { let value: string; value = ''; } }",
            ScriptKind::TypeScript,
        );
        assert!(!diagnostics.contains(&"BAMTS-W039"));
    }

    #[test]
    fn strict_denies_runtime_enum_but_keeps_const_enum_as_a_warning() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            Arc::new(
                SourceText::new("enum Runtime { Value } const enum Inlined { Value }")
                    .expect("test source fits the per-file budget"),
            ),
        ));
        let diagnostics = analyze(parsed.product(), &LintTable::new(LintProfile::Strict));
        let runtime = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code().as_str() == "BAMTS-W043")
            .expect("runtime enum must be diagnosed");
        let inlined = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code().as_str() == "BAMTS-W044")
            .expect("const enum must be diagnosed");
        assert_eq!(runtime.severity(), DiagnosticSeverity::Error);
        assert_eq!(inlined.severity(), DiagnosticSeverity::Warning);
    }

    rule_test!(
        w059_mutable_array_function,
        "BAMTS-W059",
        "function f(xs: number[]) { return xs; }",
        "function f(xs: readonly number[]) { return xs; }"
    );

    rule_test!(
        w059_mutable_array_arrow,
        "BAMTS-W059",
        "const f = (xs: number[]) => xs;",
        "const f = (value: number) => value;"
    );

    rule_test!(
        w059_mutable_array_constructor,
        "BAMTS-W059",
        "class C { constructor(xs: number[]) {} }",
        "class C { constructor(value: number) {} }"
    );

    #[test]
    fn arrow_signature_rejects_javascript_type_syntax() {
        let diagnostics = codes("const f = (x: number) => x;", ScriptKind::JavaScript);
        assert!(
            diagnostics.contains(&"BAMTS-W085"),
            "BAMTS-W085 must flag TypeScript-only parameter syntax on arrow functions in JavaScript"
        );
    }

    #[test]
    fn w065_switch_returning_from_every_case_is_not_flagged() {
        let source =
            "function f(x: 1 | 2) { switch (x) { case 1: return 'a'; default: return 'b'; } }";
        assert!(
            !codes(source, ScriptKind::TypeScript).contains(&"BAMTS-W065"),
            "a function that returns from every switch case must not be flagged as missing a return"
        );
    }

    #[test]
    fn w065_switch_grouped_empty_case_labels_are_not_flagged() {
        // `case 1:` has an empty consequent and falls through to `case 2:`.
        // Every reachable path returns, so W065 must not fire. The prior
        // implementation treated the empty consequent as a path that completes
        // normally, producing a false "missing return".
        let source = "function f(x: 1 | 2 | 3): string {\n  switch (x) {\n    case 1:\n    case 2:\n      return 'a';\n    default:\n      return 'b';\n  }\n}";
        assert!(
            !codes(source, ScriptKind::TypeScript).contains(&"BAMTS-W065"),
            "a function whose only empty case label falls through to a returning case must not be flagged as missing a return"
        );
    }

    #[test]
    fn w085_fires_in_jsx_attribute_value() {
        assert!(
            codes(
                "<Foo onClick={(x: number) => x} />",
                ScriptKind::JavaScriptReact,
            )
            .contains(&"BAMTS-W085"),
            "BAMTS-W085 must fire for TypeScript-only arrow parameter syntax in a JSX attribute",
        );
    }

    #[test]
    fn w085_fires_in_jsx_child_expression() {
        assert!(
            codes(
                "<Foo>{(x: number) => x}</Foo>;",
                ScriptKind::JavaScriptReact,
            )
            .contains(&"BAMTS-W085"),
            "BAMTS-W085 must fire for TypeScript-only arrow parameter syntax in a JSX child",
        );
    }

    #[test]
    fn w085_fires_in_jsx_fragment_child() {
        assert!(
            codes("<>{(x: number) => x}</>;", ScriptKind::JavaScriptReact,).contains(&"BAMTS-W085"),
            "BAMTS-W085 must fire for TypeScript-only arrow parameter syntax in a JSX fragment",
        );
    }

    #[test]
    fn w085_fires_in_jsx_spread_attribute() {
        assert!(
            codes(
                "<Foo {...((x: number) => x)} />",
                ScriptKind::JavaScriptReact,
            )
            .contains(&"BAMTS-W085"),
            "BAMTS-W085 must fire for TypeScript-only arrow parameter syntax in a JSX spread attribute",
        );
    }

    #[test]
    fn w085_does_not_fire_in_tsx() {
        assert!(
            !codes(
                "<Foo onClick={(x: number) => x} />",
                ScriptKind::TypeScriptReact,
            )
            .contains(&"BAMTS-W085"),
            "BAMTS-W085 must not fire for TypeScript-only syntax in TSX",
        );
        assert!(
            !codes("<>{x as number}</>;", ScriptKind::TypeScriptReact).contains(&"BAMTS-W085"),
            "BAMTS-W085 must not fire for `as` assertions in TSX",
        );
    }

    #[test]
    fn w087_debugger_in_jsx_attribute() {
        let diagnostics = codes(
            "<Foo onClick={() => { debugger; }} />",
            ScriptKind::TypeScriptReact,
        );
        assert!(
            diagnostics.contains(&"BAMTS-W087"),
            "BAMTS-W087 must fire for a debugger statement inside a JSX attribute arrow body",
        );
    }

    #[test]
    fn w064_six_parameter_arrow_in_jsx_attribute() {
        let diagnostics = codes(
            "<Foo onClick={(a,b,c,d,e,f) => a} />",
            ScriptKind::TypeScriptReact,
        );
        assert!(
            diagnostics.contains(&"BAMTS-W064"),
            "BAMTS-W064 must fire for a six-parameter arrow inside a JSX attribute",
        );
    }

    #[test]
    fn jsx_names_and_text_are_not_traversed_as_expressions() {
        let diagnostics = codes(
            "const el = <My.Component ns:attr=\"value\">text</My.Component>;",
            ScriptKind::TypeScriptReact,
        );
        assert!(
            !diagnostics.contains(&"BAMTS-W085"),
            "JSX names and text must not trigger TypeScript-only syntax rules",
        );
        assert!(
            !diagnostics.contains(&"BAMTS-W064"),
            "JSX names and text must not trigger the long-parameter-list rule",
        );
        assert!(
            !diagnostics.contains(&"BAMTS-W087"),
            "JSX names and text must not trigger the no-debugger rule",
        );
    }

    #[test]
    fn jsx_expressions_are_visited_exactly_once() {
        let attribute = codes(
            "<Foo onClick={(a,b,c,d,e,f) => a} />",
            ScriptKind::TypeScriptReact,
        );
        assert_eq!(
            attribute.iter().filter(|c| **c == "BAMTS-W064").count(),
            1,
            "a single arrow attribute must produce exactly one W064",
        );

        let nested = codes(
            "<Foo>{<Bar onClick={(a,b,c,d,e,f) => a} />}</Foo>;",
            ScriptKind::TypeScriptReact,
        );
        assert_eq!(
            nested.iter().filter(|c| **c == "BAMTS-W064").count(),
            1,
            "a nested JSX element inside a child expression must produce exactly one W064",
        );

        let js = codes(
            "<Foo {...((x: number) => x)} />",
            ScriptKind::JavaScriptReact,
        );
        assert_eq!(
            js.iter().filter(|c| **c == "BAMTS-W085").count(),
            1,
            "a single spread expression must produce exactly one W085",
        );
    }
    #[test]
    fn w065_suppressed_when_return_type_admits_absence() {
        let no_warn = [
            "function f(x: boolean): number | undefined { if (x) return 1; }",
            "function f(x: boolean): undefined | number { if (x) return 1; }",
            "function f(x: boolean): void { if (x) return 1; }",
            "function f(x: boolean): any { if (x) return 1; }",
            "function f(x: boolean): unknown { if (x) return 1; }",
            "function f(x: boolean): (number | undefined) { if (x) return 1; }",
            "function f(x: boolean): number | any { if (x) return 1; }",
        ];
        for source in no_warn {
            assert!(
                !codes(source, ScriptKind::TypeScript).contains(&"BAMTS-W065"),
                "W065 must not fire when the return type admits absence: {source:?}"
            );
        }
        assert!(
            codes(
                "function f(x: boolean): number { if (x) return 1; }",
                ScriptKind::TypeScript,
            )
            .contains(&"BAMTS-W065"),
            "W065 must fire for a non-optional return type"
        );
        assert!(
            codes(
                "function f(x: boolean) { if (x) return 1; }",
                ScriptKind::TypeScript,
            )
            .contains(&"BAMTS-W065"),
            "W065 must fire when no return type is declared"
        );
    }
}
