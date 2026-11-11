//! The lexical scanner: total UTF-8 source text to a UTF-16-ranged token stream.
//!
//! The scanner is *total*: it accepts any `&str`, never panics, and guarantees
//! forward progress, so every call to [`Scanner::next_token`] on a non-empty
//! remainder consumes at least one code point. Trivia (whitespace, comments, a
//! leading shebang) are emitted as tokens because [`crate::syntax::SourceFile`]
//! preserves the full token stream.
//!
//! Token ranges are measured in UTF-16 code units so they line up with the
//! coordinate space of [`SourceText`]. Positions are tracked incrementally as
//! code points are consumed, so no per-token coordinate conversion is required.
//!
//! Two lexical forms cannot be decided by a raw left-to-right pass and are
//! resolved through *explicit* scanner operations rather than guesses:
//!
//! * A `/` is ambiguous between division and a regular-expression literal. The
//!   default pass emits [`TokenKind::Slash`]/[`TokenKind::SlashEq`] unless the
//!   token before it cannot end an expression; a caller with grammar context
//!   calls [`Scanner::rescan_regex`] to reinterpret it as a
//!   [`TokenKind::RegularExpressionLiteral`].
//! * A `>` is ambiguous between a single relational operator and the start of a
//!   shift/compound operator. The default pass greedily forms the longest
//!   operator; a caller closing type arguments or a JSX tag calls
//!   [`Scanner::rescan_greater_than`] to take exactly one `>`.
//!
//! Template literals are segmented in a single pass because the scanner tracks
//! `{`/`}` nesting: a `}` that returns to a `${` boundary continues the template
//! deterministically instead of being guessed. A parser that drives the scanner
//! itself may instead call [`Scanner::rescan_template_continuation`].

use std::borrow::Cow;
use std::sync::Arc;

use crate::diagnostic::{Diagnostic, DiagnosticCode, Recovered};
use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
use crate::syntax::{Token, TokenKind, cook_identifier_text};
use bamts_cancel::{CancellationToken, Cancelled};
use std::error::Error;
use std::fmt;

/// Unterminated string literal.
const UNTERMINATED_STRING: DiagnosticCode = DiagnosticCode::new("BAMTS-L001");
/// Unterminated block comment.
const UNTERMINATED_BLOCK_COMMENT: DiagnosticCode = DiagnosticCode::new("BAMTS-L002");
/// Unterminated template literal.
const UNTERMINATED_TEMPLATE: DiagnosticCode = DiagnosticCode::new("BAMTS-L003");
/// Unterminated regular-expression literal.
const UNTERMINATED_REGEX: DiagnosticCode = DiagnosticCode::new("BAMTS-L004");
/// A character that cannot begin any token.
const UNEXPECTED_CHARACTER: DiagnosticCode = DiagnosticCode::new("BAMTS-L005");
/// A `\x` escape without two hexadecimal digits.
const INVALID_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-L006");
/// A `\u` escape without a hexadecimal digit where one must be.
const INVALID_UNICODE_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-L007");
/// A misplaced numeric separator.
const INVALID_NUMERIC_SEPARATOR: DiagnosticCode = DiagnosticCode::new("BAMTS-L008");
/// A numeric literal with no valid digits.
const INVALID_NUMERIC_LITERAL: DiagnosticCode = DiagnosticCode::new("BAMTS-L009");
/// A `BigInt` suffix on a form that cannot be a `BigInt`.
const INVALID_BIGINT_LITERAL: DiagnosticCode = DiagnosticCode::new("BAMTS-L010");
/// A `#` that does not begin a private identifier.
const INVALID_PRIVATE_IDENTIFIER: DiagnosticCode = DiagnosticCode::new("BAMTS-L011");
/// A `\u{...}` escape whose value is above U+10FFFF.
const UNICODE_ESCAPE_OUT_OF_RANGE: DiagnosticCode = DiagnosticCode::new("BAMTS-L012");
/// A `\u{...}` escape without its closing brace.
const UNTERMINATED_UNICODE_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-L013");
/// A legacy octal escape, such as `\1` or `\08`, in a TypeScript file or in a
/// template.
const LEGACY_OCTAL_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-L014");
/// A `\8` or `\9` escape in a TypeScript file or in a template.
const NON_OCTAL_DECIMAL_ESCAPE: DiagnosticCode = DiagnosticCode::new("BAMTS-L015");
/// A `\u{...}` escape whose digits reach the end of the text.
const UNICODE_ESCAPE_AT_END: DiagnosticCode = DiagnosticCode::new("BAMTS-L016");

/// Whether `code` reports a malformed escape in the text of a literal. A tagged
/// template accepts such an escape, so its text keeps none of these.
pub(crate) fn is_escape_diagnostic(code: DiagnosticCode) -> bool {
    [
        INVALID_ESCAPE,
        INVALID_UNICODE_ESCAPE,
        UNICODE_ESCAPE_OUT_OF_RANGE,
        UNTERMINATED_UNICODE_ESCAPE,
        LEGACY_OCTAL_ESCAPE,
        NON_OCTAL_DECIMAL_ESCAPE,
        UNICODE_ESCAPE_AT_END,
    ]
    .contains(&code)
}

/// A malformed `\u` escape. Each fault names the UTF-16 range and the message
/// that a literal reports for it.
type EscapeFault = (DiagnosticCode, usize, usize, &'static str);

/// Whether `code` reports a string, a template or a comment that is not closed.
pub(crate) fn is_unterminated_diagnostic(code: DiagnosticCode) -> bool {
    [
        UNTERMINATED_STRING,
        UNTERMINATED_BLOCK_COMMENT,
        UNTERMINATED_TEMPLATE,
    ]
    .contains(&code)
}

/// `diagnostic` where TypeScript reports it. The scanner records a literal or
/// a comment that is not closed over its whole text, so that the parser can
/// drop the errors of text that it scans again. TypeScript reports it at the
/// end of that text.
pub(crate) fn at_reported_position(diagnostic: Diagnostic) -> Diagnostic {
    if !is_unterminated_diagnostic(diagnostic.code()) {
        return diagnostic;
    }
    let end = diagnostic.range().end();
    diagnostic.with_range(TextRange::new(end, end).expect("an empty range is ordered"))
}

/// Scans a regular-expression literal starting at `text[0] == '/'`, returning
/// `(consumed_utf16, terminated)`.  This is the single source of truth for
/// both `Scanner::scan_regex` and `Parser::rescan_regex_here`.
pub fn scan_regex_slice(text: &str) -> (usize, bool) {
    // First, try depth scan for `v` flag (unicodeSets) where `[[` is nested.
    // We peek with depth to see if it would produce a `v` flag; if so, use it.
    let mut chars = text.chars();
    let mut consumed = 0usize;
    let take = |chars: &mut std::str::Chars<'_>, consumed: &mut usize| -> Option<char> {
        let c = chars.next()?;
        *consumed += c.len_utf16();
        Some(c)
    };
    let _slash = take(&mut chars, &mut consumed);
    // Depth peek
    let mut p_chars = text.chars();
    let mut p_consumed = 0usize;
    let _ = take(&mut p_chars, &mut p_consumed);
    {
        let mut dc = p_chars.clone();
        let mut dcon = p_consumed;
        let mut dd = 0usize;
        let mut dp: Option<char> = None;
        let mut dpp: Option<char> = None;
        let mut term = false;
        let mut tend = 0usize;
        loop {
            let mut peek = dc.clone();
            match peek.next() {
                None => break,
                Some(c) if is_line_terminator(c) => break,
                Some('\\') => {
                    take(&mut dc, &mut dcon);
                    let mut after = dc.clone();
                    match after.next() {
                        None => {}
                        Some(c) if is_line_terminator(c) => break,
                        Some(ch) => {
                            dpp = dp;
                            dp = Some(ch);
                            take(&mut dc, &mut dcon);
                        }
                    }
                }
                Some('[') => {
                    if dd == 0 {
                        dd = 1;
                    } else {
                        let is_nested = dp == Some('[') || (dp == Some('^') && dpp == Some('['));
                        if is_nested {
                            dd += 1;
                        }
                    }
                    dpp = dp;
                    dp = Some('[');
                    take(&mut dc, &mut dcon);
                }
                Some(']') => {
                    if dd > 0 {
                        dd = dd.saturating_sub(1);
                    }
                    dpp = dp;
                    dp = Some(']');
                    take(&mut dc, &mut dcon);
                }
                Some('/') if dd == 0 => {
                    take(&mut dc, &mut dcon);
                    term = true;
                    tend = dcon;
                    break;
                }
                Some(ch) => {
                    dpp = dp;
                    dp = Some(ch);
                    take(&mut dc, &mut dcon);
                }
            }
        }
        if term {
            // The flag run is consumed in UTF-16 units like the rest of this
            // function, so the `v` predicate is decided per code point rather
            // than by slicing `text`: a UTF-16 count is not a byte offset, and
            // astral pattern characters make the two diverge mid-code-point.
            let mut fc = dc.clone();
            let mut fcon = tend;
            let mut flags_have_v = false;
            while {
                let mut peek = fc.clone();
                match peek.next() {
                    Some(c) if is_id_continue(c) => {
                        flags_have_v |= c == 'v';
                        take(&mut fc, &mut fcon);
                        true
                    }
                    _ => false,
                }
            } {}
            if flags_have_v {
                // Use depth result
                let mut chars2 = text.chars();
                let mut consumed2 = 0usize;
                let _ = take(&mut chars2, &mut consumed2);
                let mut dd2 = 0usize;
                let mut pp2: Option<char> = None;
                let mut ppp2: Option<char> = None;
                let mut term2 = false;
                loop {
                    let mut peek = chars2.clone();
                    match peek.next() {
                        None => break,
                        Some(c) if is_line_terminator(c) => break,
                        Some('\\') => {
                            take(&mut chars2, &mut consumed2);
                            let mut after = chars2.clone();
                            match after.next() {
                                None => {}
                                Some(c) if is_line_terminator(c) => break,
                                Some(ch) => {
                                    ppp2 = pp2;
                                    pp2 = Some(ch);
                                    take(&mut chars2, &mut consumed2);
                                }
                            }
                        }
                        Some('[') => {
                            if dd2 == 0 {
                                dd2 = 1;
                            } else {
                                let is_nested =
                                    pp2 == Some('[') || (pp2 == Some('^') && ppp2 == Some('['));
                                if is_nested {
                                    dd2 += 1;
                                }
                            }
                            ppp2 = pp2;
                            pp2 = Some('[');
                            take(&mut chars2, &mut consumed2);
                        }
                        Some(']') => {
                            if dd2 > 0 {
                                dd2 = dd2.saturating_sub(1);
                            }
                            ppp2 = pp2;
                            pp2 = Some(']');
                            take(&mut chars2, &mut consumed2);
                        }
                        Some('/') if dd2 == 0 => {
                            take(&mut chars2, &mut consumed2);
                            term2 = true;
                            break;
                        }
                        Some(ch) => {
                            ppp2 = pp2;
                            pp2 = Some(ch);
                            take(&mut chars2, &mut consumed2);
                        }
                    }
                }
                if term2 {
                    loop {
                        let mut peek = chars2.clone();
                        match peek.next() {
                            Some(c) if is_id_continue(c) => {
                                take(&mut chars2, &mut consumed2);
                            }
                            _ => break,
                        }
                    }
                }
                return (consumed2, term2);
            }
        }
    }
    // Classic boolean
    let mut in_class = false;
    let mut terminated = false;
    loop {
        let mut peek = chars.clone();
        match peek.next() {
            None => break,
            Some(c) if is_line_terminator(c) => break,
            Some('\\') => {
                take(&mut chars, &mut consumed);
                let mut after = chars.clone();
                match after.next() {
                    None => {}
                    Some(c) if is_line_terminator(c) => break,
                    Some(_) => {
                        take(&mut chars, &mut consumed);
                    }
                }
            }
            Some('[') => {
                if !in_class {
                    in_class = true;
                }
                take(&mut chars, &mut consumed);
            }
            Some(']') => {
                if in_class {
                    in_class = false;
                }
                take(&mut chars, &mut consumed);
            }
            Some('/') if !in_class => {
                take(&mut chars, &mut consumed);
                terminated = true;
                break;
            }
            Some(_) => {
                take(&mut chars, &mut consumed);
            }
        }
    }
    if terminated {
        loop {
            let mut peek = chars.clone();
            match peek.next() {
                Some(c) if is_id_continue(c) => {
                    take(&mut chars, &mut consumed);
                }
                _ => break,
            }
        }
    }
    (consumed, terminated)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScanError {
    /// The caller requested cancellation.
    Cancelled(Cancelled),
}

impl fmt::Display for ScanError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScanError::Cancelled(_) => formatter.write_str("scan cancelled"),
        }
    }
}

impl Error for ScanError {}

impl From<Cancelled> for ScanError {
    fn from(cancelled: Cancelled) -> Self {
        ScanError::Cancelled(cancelled)
    }
}

impl From<ScanError> for Cancelled {
    fn from(error: ScanError) -> Self {
        match error {
            ScanError::Cancelled(cancelled) => cancelled,
        }
    }
}

/// The immutable product of one lexical pass over a source file.
///
/// It retains the file identity, the [`ScriptKind`], the shared source text, the
/// non-EOF tokens in lexical order (including trivia), and the terminal
/// end-of-file token whose empty range anchors the end of the source.
#[derive(Clone, Debug)]
pub struct ScannedSource {
    source_id: SourceId,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
    tokens: Vec<Token>,
    eof: Token,
}

impl ScannedSource {
    /// Returns the source this token stream describes.
    #[must_use]
    pub const fn source_id(&self) -> SourceId {
        self.source_id
    }

    /// Returns the syntax the source was scanned as.
    #[must_use]
    pub const fn script_kind(&self) -> ScriptKind {
        self.script_kind
    }

    /// Returns the shared, immutable source text.
    #[must_use]
    pub fn source(&self) -> &Arc<SourceText> {
        &self.source
    }

    /// Returns the source text mapper directly.
    #[must_use]
    pub fn source_text(&self) -> &SourceText {
        &self.source
    }

    /// Returns the non-EOF tokens in lexical order, including trivia.
    #[must_use]
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// Returns the terminal end-of-file token.
    #[must_use]
    pub const fn eof(&self) -> &Token {
        &self.eof
    }

    /// Returns the zero-copy lexeme for one token of this source.
    ///
    /// `None` identifies a range that is not a valid UTF-16 slice of this file,
    /// which cannot arise from a scanner-produced token.
    #[must_use]
    pub fn token_text(&self, token: &Token) -> Option<&str> {
        if token.is_missing() {
            return Some("");
        }
        let range = token.range();
        let start = self.source.utf16_to_byte(range.start()).ok()?;
        let end = self.source.utf16_to_byte(range.end()).ok()?;
        self.source.as_str().get(start..end)
    }
}

/// Scans a whole source into an ordered token stream with recovery diagnostics.
///
/// This is the default single-pass driver: `>` forms the longest operator and `/`
/// is division unless nothing before it could be divided. A grammar-aware caller
/// can reinterpret either with [`Scanner::rescan_regex`] and
/// [`Scanner::rescan_greater_than`]. Template literals are fully segmented here.
#[must_use]
pub fn scan(
    source_id: SourceId,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
) -> Recovered<ScannedSource> {
    match scan_with_cancel(source_id, script_kind, source, CancellationToken::new()) {
        Ok(recovered) => recovered,
        Err(_) => unreachable!("fresh token is never cancelled"),
    }
}

/// Scans a whole source with cooperative cancellation.
///
/// A caller-supplied [`CancellationToken`] is checked before scanning, at every
/// token boundary, and inside long character loops. Triggering it aborts
/// scanning with [`ScanError::Cancelled`].
pub fn scan_with_cancel(
    source_id: SourceId,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
    cancel: CancellationToken,
) -> Result<Recovered<ScannedSource>, ScanError> {
    if cancel.is_cancelled() {
        return Err(ScanError::Cancelled(Cancelled));
    }

    let (tokens, eof, diagnostics) = {
        let mut scanner = Scanner::new_with_cancel(source_id, script_kind, &source, cancel.clone());
        let mut tokens = Vec::new();
        let mut previous = None;
        let eof = loop {
            if scanner.is_cancelled() {
                break scanner.make(TokenKind::EndOfFile, scanner.position().get());
            }
            let mut token = scanner.next_token();
            if matches!(token.kind(), TokenKind::Slash | TokenKind::SlashEq)
                && previous.is_some_and(cannot_end_expression)
                && scanner.regex_closes_at_last_token()
            {
                token = scanner.rescan_regex();
            }
            if token.kind() == TokenKind::EndOfFile || scanner.is_cancelled() {
                break token;
            }
            if !matches!(
                token.kind(),
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            ) {
                previous = Some(match previous {
                    // A keyword here is a property name, so `o.in / 2` divides.
                    Some(TokenKind::Dot | TokenKind::QuestionDot) => TokenKind::Identifier,
                    _ => token.kind(),
                });
            }
            tokens.push(token);
        };
        (tokens, eof, scanner.into_diagnostics())
    };

    if cancel.is_cancelled() {
        return Err(ScanError::Cancelled(Cancelled));
    }

    let product = ScannedSource {
        source_id,
        script_kind,
        source,
        tokens,
        eof,
    };
    Ok(Recovered::new(product, diagnostics))
}

/// Whether no expression can end with `kind`, so a `/` after it has nothing to
/// divide and can only start a regular expression. This needs no grammar: reading
/// that `/` as division here would let a quote in the regex open a false string.
/// Tokens an expression can end with, such as `)`, `}`, `]`, `!`, and `>`, stay
/// with the parser, which knows what they closed. So does `<`, which opens a
/// closing JSX tag.
const fn cannot_end_expression(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::LParen
            | TokenKind::LBracket
            | TokenKind::LBrace
            | TokenKind::Comma
            | TokenKind::Semicolon
            | TokenKind::Colon
            | TokenKind::Question
            | TokenKind::QuestionQuestion
            | TokenKind::Arrow
            | TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::StarStar
            | TokenKind::Percent
            | TokenKind::Eq
            | TokenKind::EqEq
            | TokenKind::EqEqEq
            | TokenKind::BangEq
            | TokenKind::BangEqEq
            | TokenKind::Amp
            | TokenKind::AmpAmp
            | TokenKind::Pipe
            | TokenKind::PipePipe
            | TokenKind::Caret
            | TokenKind::Tilde
            | TokenKind::PlusEq
            | TokenKind::MinusEq
            | TokenKind::StarEq
            | TokenKind::StarStarEq
            | TokenKind::SlashEq
            | TokenKind::PercentEq
            | TokenKind::LessLessEq
            | TokenKind::GreaterGreaterEq
            | TokenKind::GreaterGreaterGreaterEq
            | TokenKind::AmpEq
            | TokenKind::AmpAmpEq
            | TokenKind::PipeEq
            | TokenKind::PipePipeEq
            | TokenKind::CaretEq
            | TokenKind::QuestionQuestionEq
            | TokenKind::TemplateHead
            | TokenKind::TemplateMiddle
            | TokenKind::KwReturn
            | TokenKind::KwTypeof
            | TokenKind::KwCase
            | TokenKind::KwThrow
            | TokenKind::KwVoid
            | TokenKind::KwDelete
            | TokenKind::KwIn
            | TokenKind::KwInstanceof
            | TokenKind::KwNew
            | TokenKind::KwElse
            | TokenKind::KwDo
    )
}

/// The kind of an open brace the scanner is currently inside, used to segment
/// template literals in one pass without grammar feedback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PendingBrace {
    /// An ordinary `{` block or object literal.
    Normal,
    /// A `${` template substitution; its closing `}` continues the template.
    Template,
}

/// How a JSX tag scanned by [`Scanner::scan_jsx_span`] relates to element
/// nesting: an opening tag (or fragment `<>`) increases depth, a closing tag
/// (or `</>`) decreases it, and a self-closing tag `<Foo />` leaves it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum JsxTagKind {
    Opening,
    Closing,
    SelfClosing,
}

/// A stateful lexical cursor over one immutable source text.
///
/// A caller may drive it token by token with [`Scanner::next_token`] and, at a
/// grammatical decision point, request an explicit reinterpretation with one of
/// the `rescan_*`/`scan_jsx_*` operations.
pub struct Scanner<'a> {
    source_id: SourceId,
    script_kind: ScriptKind,
    text: &'a str,
    byte_pos: usize,
    utf16_pos: usize,
    last_start_byte: usize,
    last_start_utf16: usize,
    braces: Vec<PendingBrace>,
    diagnostics: Vec<Diagnostic>,
    /// Cooperative cancellation signal checked at every token boundary.
    cancel: CancellationToken,
}

impl<'a> Scanner<'a> {
    /// Creates a scanner positioned at the start of `source`.
    #[must_use]
    pub fn new(source_id: SourceId, script_kind: ScriptKind, source: &'a SourceText) -> Self {
        Self::new_with_cancel(source_id, script_kind, source, CancellationToken::new())
    }

    /// Creates a scanner with a caller-supplied cancellation token.
    #[must_use]
    pub fn new_with_cancel(
        source_id: SourceId,
        script_kind: ScriptKind,
        source: &'a SourceText,
        cancel: CancellationToken,
    ) -> Self {
        Self {
            source_id,
            script_kind,
            text: source.as_str(),
            byte_pos: 0,
            utf16_pos: 0,
            last_start_byte: 0,
            last_start_utf16: 0,
            braces: Vec::new(),
            diagnostics: Vec::new(),
            cancel,
        }
    }

    /// Returns whether cancellation has been requested.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        self.cancel.is_cancelled()
    }

    /// Returns the syntax this scanner lexes.
    #[must_use]
    pub const fn script_kind(&self) -> ScriptKind {
        self.script_kind
    }

    /// Returns the current UTF-16 cursor position.
    #[must_use]
    pub const fn position(&self) -> Utf16Pos {
        Utf16Pos::new(self.utf16_pos)
    }

    /// Returns whether the whole source has been consumed.
    #[must_use]
    pub fn is_at_end(&self) -> bool {
        self.byte_pos >= self.text.len()
    }

    /// Returns the diagnostics recorded so far, in emission order.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Consumes the scanner and returns its recorded diagnostics.
    #[must_use]
    pub fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    /// Scans the next token, or an end-of-file token at the end of the source.
    pub fn next_token(&mut self) -> Token {
        if self.is_cancelled() {
            return self.make(TokenKind::EndOfFile, self.position().get());
        }
        let start_b = self.byte_pos;
        let start_u = self.utf16_pos;
        self.last_start_byte = start_b;
        self.last_start_utf16 = start_u;

        let Some(c) = self.first() else {
            return self.make(TokenKind::EndOfFile, start_u);
        };

        let kind = match c {
            _ if is_whitespace(c) => self.scan_whitespace(),
            '/' => match self.second() {
                Some('/') => self.scan_line_comment(),
                Some('*') => self.scan_block_comment(start_u),
                Some('=') => {
                    self.bump();
                    self.bump();
                    TokenKind::SlashEq
                }
                _ => {
                    self.bump();
                    TokenKind::Slash
                }
            },
            '\'' | '"' => self.scan_string(c, start_u),
            '`' => {
                let kind = self.scan_template(start_u, false);
                if kind == TokenKind::TemplateHead {
                    self.braces.push(PendingBrace::Template);
                }
                kind
            }
            '{' => {
                self.bump();
                self.braces.push(PendingBrace::Normal);
                TokenKind::LBrace
            }
            '}' => match self.braces.pop() {
                Some(PendingBrace::Template) => {
                    let kind = self.scan_template(start_u, true);
                    if kind == TokenKind::TemplateMiddle {
                        self.braces.push(PendingBrace::Template);
                    }
                    kind
                }
                _ => {
                    self.bump();
                    TokenKind::RBrace
                }
            },
            '0'..='9' => self.scan_number(start_u),
            '.' if self.second().is_some_and(|d| d.is_ascii_digit()) => self.scan_number(start_u),
            '#' => self.scan_hash(start_b, start_u),
            '\\' if self.second() == Some('u') => self.scan_identifier(start_b),
            _ if is_id_start(c) => self.scan_identifier(start_b),
            _ => self.scan_operator(c, start_u),
        };

        self.make(kind, start_u)
    }

    /// Reinterprets the most recent `/`/`/=` token as a regular-expression
    /// literal starting at the same position, advancing past its body and flags.
    ///
    /// This is the explicit division-versus-regex decision. The caller supplies
    /// the grammatical context; the scanner never guesses it.
    pub fn rescan_regex(&mut self) -> Token {
        self.reset_to_last();
        let start_u = self.utf16_pos;
        let kind = self.scan_regex(start_u);
        self.make(kind, start_u)
    }

    /// Whether a regular expression starting at the most recent token closes on
    /// its own line. One that does not is left for the parser to judge.
    fn regex_closes_at_last_token(&self) -> bool {
        scan_regex_slice(&self.text[self.last_start_byte..]).1
    }

    /// Reinterprets the most recent `>`-family token as a single `>`, advancing
    /// exactly one code unit past the last token's start.
    ///
    /// A caller closing type arguments or a JSX element uses this to split a
    /// greedily formed shift/compound operator.
    pub fn rescan_greater_than(&mut self) -> Token {
        self.reset_to_last();
        let start_u = self.utf16_pos;
        self.bump();
        self.make(TokenKind::GreaterThan, start_u)
    }

    /// Reinterprets the most recent `}` token as a template continuation,
    /// producing [`TokenKind::TemplateMiddle`] or [`TokenKind::TemplateTail`].
    ///
    /// This serves a caller that drives the scanner without relying on the
    /// single-pass brace tracking used by [`scan`].
    pub fn rescan_template_continuation(&mut self) -> Token {
        self.reset_to_last();
        let start_u = self.utf16_pos;
        let kind = self.scan_template(start_u, true);
        self.make(kind, start_u)
    }

    /// Scans a run of JSX character data up to the next `<` or `{`.
    ///
    /// The token kind is [`TokenKind::StringLiteral`]: the fixed token space has
    /// no dedicated JSX kind, and JSX text is uninterpreted character content
    /// whose lexeme the caller reads directly. The run may be empty when the
    /// caller is already positioned at a `<` or `{`.
    pub fn scan_jsx_text(&mut self) -> Token {
        let start_u = self.utf16_pos;
        self.last_start_byte = self.byte_pos;
        self.last_start_utf16 = start_u;
        while let Some(c) = self.first() {
            if self.is_cancelled() {
                break;
            }
            if c == '<' || c == '{' {
                break;
            }
            self.bump();
        }
        self.make(TokenKind::StringLiteral, start_u)
    }

    /// Scans a JSX name, which unlike an ECMAScript identifier admits interior
    /// hyphens (for example `data-role`).
    pub fn scan_jsx_identifier(&mut self) -> Token {
        let start_u = self.utf16_pos;
        self.last_start_byte = self.byte_pos;
        self.last_start_utf16 = start_u;
        if self.first().is_some_and(is_id_start) {
            self.bump();
            while let Some(c) = self.first() {
                if self.is_cancelled() {
                    break;
                }
                if c == '-' || is_id_continue(c) {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        self.make(TokenKind::Identifier, start_u)
    }

    /// Scans a JSX attribute string, which is delimited by matching quotes,
    /// performs no escape processing, and may span line terminators.
    pub fn scan_jsx_attribute_string(&mut self) -> Token {
        let start_u = self.utf16_pos;
        self.last_start_byte = self.byte_pos;
        self.last_start_utf16 = start_u;
        let Some(quote @ ('\'' | '"')) = self.first() else {
            self.error(
                UNEXPECTED_CHARACTER,
                start_u,
                self.utf16_pos,
                "a JSX attribute value must be a quoted string",
            );
            return self.make(TokenKind::StringLiteral, start_u);
        };
        self.bump();
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                None => {
                    self.error(
                        UNTERMINATED_STRING,
                        start_u,
                        self.utf16_pos,
                        "unterminated string literal",
                    );
                    break;
                }
                Some(c) if c == quote => {
                    self.bump();
                    break;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
        self.make(TokenKind::StringLiteral, start_u)
    }

    /// Scans one complete JSX element or fragment beginning at the current
    /// position, returning the tokens that tile it. The scanner is left
    /// positioned immediately after the construct.
    ///
    /// The stream is JSX-aware where the default pass is not: element and
    /// attribute names admit interior hyphens, character data between tags is a
    /// single [`TokenKind::StringLiteral`] run that ignores comment and string
    /// syntax, and expression containers are lexed as ordinary ECMAScript so
    /// the parser can reparse them. Every produced token is emitted so the run
    /// stays contiguous, and malformed input ends the scan without panicking.
    #[must_use]
    pub fn scan_jsx_span(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        // Elements and fragments whose children are still open.
        let mut depth: usize = 0;
        loop {
            if self.is_cancelled() {
                break;
            }
            if depth > 0 {
                let text = self.scan_jsx_text();
                if !text.range().is_empty() {
                    out.push(text);
                }
            }
            match self.first() {
                None => break,
                Some('{') => self.scan_jsx_expression_tokens(&mut out),
                Some('<') => match self.scan_jsx_tag(&mut out) {
                    JsxTagKind::Opening => depth += 1,
                    JsxTagKind::SelfClosing => {
                        if depth == 0 {
                            break;
                        }
                    }
                    JsxTagKind::Closing => {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            break;
                        }
                    }
                },
                Some(_) => break,
            }
        }
        out
    }

    /// Scans one JSX tag (`<name ...>`, `<name ... />`, `</name>`, `<>`, or
    /// `</>`) starting at `<`, classifying it for [`Self::scan_jsx_span`].
    fn scan_jsx_tag(&mut self, out: &mut Vec<Token>) -> JsxTagKind {
        out.push(self.next_token()); // `<`
        self.push_jsx_trivia(out);
        if self.first() == Some('/') {
            out.push(self.next_token()); // `/`
            self.push_jsx_trivia(out);
            if self.first() != Some('>') {
                self.scan_jsx_name(out);
                self.push_jsx_trivia(out);
            }
            self.push_jsx_gt(out);
            return JsxTagKind::Closing;
        }
        if self.first() == Some('>') {
            self.push_jsx_gt(out); // `<>` fragment
            return JsxTagKind::Opening;
        }
        self.scan_jsx_name(out);
        loop {
            if self.is_cancelled() {
                break JsxTagKind::Opening;
            }
            self.push_jsx_trivia(out);
            match self.first() {
                None => return JsxTagKind::Opening,
                Some('>') => {
                    self.push_jsx_gt(out);
                    return JsxTagKind::Opening;
                }
                Some('/') => {
                    out.push(self.next_token()); // `/`
                    self.push_jsx_trivia(out);
                    if self.first() == Some('>') {
                        self.push_jsx_gt(out);
                    }
                    return JsxTagKind::SelfClosing;
                }
                Some('{') => self.scan_jsx_expression_tokens(out),
                Some(c) if is_id_start(c) => self.scan_jsx_attribute(out),
                Some(_) => out.push(self.next_token()),
            }
        }
    }

    /// Emits an element or attribute name, following `.` and `:` separators so
    /// `Foo.Bar` and `ns:Foo` scan into their component identifier tokens.
    fn scan_jsx_name(&mut self, out: &mut Vec<Token>) {
        let name = self.scan_jsx_identifier();
        if name.range().is_empty() {
            return;
        }
        out.push(name);
        while matches!(self.first(), Some('.') | Some(':')) {
            if self.is_cancelled() {
                break;
            }
            out.push(self.next_token()); // `.` or `:`
            let part = self.scan_jsx_identifier();
            if part.range().is_empty() {
                break;
            }
            out.push(part);
        }
    }

    /// Emits one attribute: a name (with optional `:namespace`) and an
    /// optional `=` initializer that is a quoted string or `{expr}`.
    fn scan_jsx_attribute(&mut self, out: &mut Vec<Token>) {
        let name = self.scan_jsx_identifier();
        if name.range().is_empty() {
            out.push(self.next_token());
            return;
        }
        out.push(name);
        if self.first() == Some(':') {
            out.push(self.next_token()); // `:`
            let part = self.scan_jsx_identifier();
            if !part.range().is_empty() {
                out.push(part);
            }
        }
        self.push_jsx_trivia(out);
        if self.first() == Some('=') {
            out.push(self.next_token()); // `=`
            self.push_jsx_trivia(out);
            match self.first() {
                Some('"') | Some('\'') => out.push(self.scan_jsx_attribute_string()),
                Some('{') => self.scan_jsx_expression_tokens(out),
                _ => {}
            }
        }
    }

    /// Emits a `{ ... }` region as ordinary ECMAScript tokens, balancing braces
    /// so the container's own closing `}` ends the run. Template substitution
    /// braces are absorbed by the template tokens and never counted here.
    fn scan_jsx_expression_tokens(&mut self, out: &mut Vec<Token>) {
        out.push(self.next_token()); // `{`
        let mut depth: usize = 1;
        loop {
            if self.is_cancelled() {
                break;
            }
            let token = self.next_token();
            match token.kind() {
                TokenKind::EndOfFile => break,
                TokenKind::LBrace => {
                    depth += 1;
                    out.push(token);
                }
                TokenKind::RBrace => {
                    depth = depth.saturating_sub(1);
                    out.push(token);
                    if depth == 0 {
                        break;
                    }
                }
                _ => out.push(token),
            }
        }
    }

    /// Emits whitespace and comment trivia so a JSX tag stays contiguous.
    fn push_jsx_trivia(&mut self, out: &mut Vec<Token>) {
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                Some(c) if is_whitespace(c) => out.push(self.next_token()),
                Some('/') if matches!(self.second(), Some('/') | Some('*')) => {
                    out.push(self.next_token());
                }
                _ => break,
            }
        }
    }

    /// Emits a single `>` that closes a JSX tag, narrowing a greedily formed
    /// `>>`/`>=`-family operator when the source packed one.
    fn push_jsx_gt(&mut self, out: &mut Vec<Token>) {
        let token = self.next_token();
        match token.kind() {
            TokenKind::GreaterThan => out.push(token),
            TokenKind::GreaterGreater
            | TokenKind::GreaterGreaterGreater
            | TokenKind::GreaterThanEq
            | TokenKind::GreaterGreaterEq
            | TokenKind::GreaterGreaterGreaterEq => out.push(self.rescan_greater_than()),
            TokenKind::EndOfFile => {}
            _ => out.push(token),
        }
    }

    fn scan_whitespace(&mut self) -> TokenKind {
        while self.first().is_some_and(is_whitespace) {
            if self.is_cancelled() {
                break;
            }
            self.bump();
        }
        TokenKind::Whitespace
    }

    fn scan_line_comment(&mut self) -> TokenKind {
        self.bump();
        self.bump();
        while let Some(c) = self.first() {
            if self.is_cancelled() {
                break;
            }
            if is_line_terminator(c) {
                break;
            }
            self.bump();
        }
        TokenKind::LineComment
    }

    fn scan_block_comment(&mut self, start_u: usize) -> TokenKind {
        self.bump();
        self.bump();
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                None => {
                    self.error(
                        UNTERMINATED_BLOCK_COMMENT,
                        start_u,
                        self.utf16_pos,
                        "unterminated block comment",
                    );
                    break;
                }
                Some('*') if self.second() == Some('/') => {
                    self.bump();
                    self.bump();
                    break;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
        TokenKind::BlockComment
    }

    fn scan_string(&mut self, quote: char, start_u: usize) -> TokenKind {
        self.bump();
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                None => {
                    self.error(
                        UNTERMINATED_STRING,
                        start_u,
                        self.utf16_pos,
                        "unterminated string literal",
                    );
                    break;
                }
                Some(c) if c == quote => {
                    self.bump();
                    break;
                }
                // A raw CR or LF terminates a string; LS/PS are permitted.
                Some('\r' | '\n') => {
                    self.error(
                        UNTERMINATED_STRING,
                        start_u,
                        self.utf16_pos,
                        "unterminated string literal",
                    );
                    break;
                }
                Some('\\') => self.scan_escape(false),
                Some(_) => {
                    self.bump();
                }
            }
        }
        TokenKind::StringLiteral
    }

    /// Scans a template segment. With `continuation`, the cursor begins on the
    /// `}` closing a substitution; otherwise it begins on the opening backtick.
    fn scan_template(&mut self, start_u: usize, continuation: bool) -> TokenKind {
        self.bump();
        let closed = if continuation {
            TokenKind::TemplateTail
        } else {
            TokenKind::NoSubstitutionTemplate
        };
        loop {
            if self.is_cancelled() {
                break closed;
            }
            match self.first() {
                None => {
                    self.error(
                        UNTERMINATED_TEMPLATE,
                        start_u,
                        self.utf16_pos,
                        "unterminated template literal",
                    );
                    return closed;
                }
                Some('`') => {
                    self.bump();
                    return closed;
                }
                Some('$') if self.second() == Some('{') => {
                    self.bump();
                    self.bump();
                    return if continuation {
                        TokenKind::TemplateMiddle
                    } else {
                        TokenKind::TemplateHead
                    };
                }
                Some('\\') => self.scan_escape(true),
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    fn scan_regex(&mut self, start_u: usize) -> TokenKind {
        let text = &self.text[self.byte_pos..];
        let (consumed, terminated) = scan_regex_slice(text);
        // consumed is in utf16 units, including initial '/'
        let mut remaining = consumed;
        while remaining > 0 {
            if let Some(c) = self.first() {
                let clen = c.len_utf16();
                if clen <= remaining {
                    self.bump();
                    remaining -= clen;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        if !terminated {
            self.error(
                UNTERMINATED_REGEX,
                start_u,
                self.utf16_pos,
                "unterminated regular expression literal",
            );
        }
        TokenKind::RegularExpressionLiteral
    }

    fn scan_number(&mut self, start_u: usize) -> TokenKind {
        let first = self.first().unwrap_or('0');
        if first == '0' {
            match self.second() {
                Some('x' | 'X') => return self.scan_radix(16, start_u),
                Some('o' | 'O') => return self.scan_radix(8, start_u),
                Some('b' | 'B') => return self.scan_radix(2, start_u),
                _ => {}
            }
        }

        let leading_zero_separator = first == '0' && self.second() == Some('_');
        let legacy_octal_leading_zero = first == '0'
            && self
                .second()
                .is_some_and(|next| next.is_ascii_digit() || next == '_');
        let mut is_integer = true;

        if first == '.' {
            is_integer = false;
            self.bump();
            self.consume_digits(10, start_u);
        } else {
            self.consume_digits(10, start_u);
            if leading_zero_separator {
                self.error(
                    INVALID_NUMERIC_SEPARATOR,
                    start_u,
                    self.utf16_pos,
                    "a decimal integer starting with zero cannot contain a separator",
                );
            }
            if self.first() == Some('.') {
                is_integer = false;
                self.bump();
                self.consume_digits(10, start_u);
            }
        }

        if matches!(self.first(), Some('e' | 'E')) {
            is_integer = false;
            self.bump();
            if matches!(self.first(), Some('+' | '-')) {
                self.bump();
            }
            if !self.consume_digits(10, start_u) {
                self.error(
                    INVALID_NUMERIC_LITERAL,
                    start_u,
                    self.utf16_pos,
                    "an exponent must have at least one digit",
                );
            }
        }

        if self.first() == Some('n') {
            let valid = is_integer && !legacy_octal_leading_zero;
            self.bump();
            if !valid {
                self.error(
                    INVALID_BIGINT_LITERAL,
                    start_u,
                    self.utf16_pos,
                    "a BigInt literal must be an integer without a leading zero",
                );
                return TokenKind::NumericLiteral;
            }
            if self.first().is_some_and(is_id_continue) || self.first() == Some('\\') {
                self.error(
                    INVALID_BIGINT_LITERAL,
                    start_u,
                    self.utf16_pos,
                    "an identifier cannot immediately follow a BigInt literal",
                );
            }
            return TokenKind::BigIntLiteral;
        }

        TokenKind::NumericLiteral
    }

    fn scan_radix(&mut self, radix: u32, start_u: usize) -> TokenKind {
        self.bump();
        self.bump();
        let any = self.consume_digits(radix, start_u);
        if !any {
            self.error(
                INVALID_NUMERIC_LITERAL,
                start_u,
                self.utf16_pos,
                "a numeric literal must have at least one digit",
            );
        }
        if self.first() == Some('n') {
            self.bump();
            if !any {
                return TokenKind::NumericLiteral;
            }
            if self.first().is_some_and(is_id_continue) || self.first() == Some('\\') {
                self.error(
                    INVALID_BIGINT_LITERAL,
                    start_u,
                    self.utf16_pos,
                    "an identifier cannot immediately follow a BigInt literal",
                );
            }
            return TokenKind::BigIntLiteral;
        }
        TokenKind::NumericLiteral
    }

    /// Consumes a run of `radix` digits with ECMAScript numeric separators.
    /// Returns whether at least one digit was consumed.
    fn consume_digits(&mut self, radix: u32, start_u: usize) -> bool {
        let mut any = false;
        let mut last_was_digit = false;
        let mut trailing_separator = false;
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                Some(c) if c.is_digit(radix) => {
                    self.bump();
                    any = true;
                    last_was_digit = true;
                    trailing_separator = false;
                }
                Some('_') => {
                    if !last_was_digit {
                        self.error(
                            INVALID_NUMERIC_SEPARATOR,
                            start_u,
                            self.utf16_pos,
                            "a numeric separator must sit between two digits",
                        );
                    }
                    self.bump();
                    last_was_digit = false;
                    trailing_separator = true;
                }
                _ => break,
            }
        }
        if trailing_separator {
            self.error(
                INVALID_NUMERIC_SEPARATOR,
                start_u,
                self.utf16_pos,
                "a numeric literal must not end with a separator",
            );
        }
        any
    }

    fn scan_identifier(&mut self, start_b: usize) -> TokenKind {
        let mut had_escape = false;
        if self.first() == Some('\\') {
            self.scan_identifier_escape(true);
            had_escape = true;
        } else {
            self.bump();
        }
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                Some('\\') if self.second() == Some('u') => {
                    self.scan_identifier_escape(false);
                    had_escape = true;
                }
                Some(c) if is_id_continue(c) => {
                    self.bump();
                }
                _ => break,
            }
        }

        let word = &self.text[start_b..self.byte_pos];
        if had_escape {
            let Some(cooked) = cook_identifier_text(word) else {
                return TokenKind::Identifier;
            };
            if is_unconditional_reserved_word(&cooked) {
                return TokenKind::EscapedReservedWord;
            }
            if matches!(cooked.as_ref(), "await" | "yield") {
                return TokenKind::EscapedContextualKeyword;
            }
            return TokenKind::Identifier;
        }
        keyword_kind(word).unwrap_or(TokenKind::Identifier)
    }

    /// Scans a `\u` escape in a name. TypeScript reports a bad one as an invalid
    /// character at its backslash.
    fn scan_identifier_escape(&mut self, is_start: bool) {
        let backslash = self.utf16_pos;
        self.bump();
        let valid = self.first() == Some('u') && {
            self.bump();
            self.read_hex_code_point().is_ok_and(|code_point| {
                char::from_u32(code_point).is_some_and(|character| {
                    if is_start {
                        is_id_start(character)
                    } else {
                        is_id_continue(character)
                    }
                })
            })
        };
        if !valid {
            self.error(
                UNEXPECTED_CHARACTER,
                backslash,
                backslash + 1,
                "this escape does not name a character of an identifier",
            );
        }
    }

    fn scan_hash(&mut self, start_b: usize, start_u: usize) -> TokenKind {
        if start_b == 0 && self.second() == Some('!') {
            self.bump();
            self.bump();
            while let Some(c) = self.first() {
                if self.is_cancelled() {
                    break;
                }
                if is_line_terminator(c) {
                    break;
                }
                self.bump();
            }
            return TokenKind::Shebang;
        }

        self.bump();
        let begins_name = match self.first() {
            Some('\\') => self.second() == Some('u'),
            Some(c) => is_id_start(c),
            None => false,
        };
        if begins_name {
            if self.first() == Some('\\') {
                self.scan_identifier_escape(true);
            } else {
                self.bump();
            }
            loop {
                if self.is_cancelled() {
                    break;
                }
                match self.first() {
                    Some('\\') if self.second() == Some('u') => self.scan_identifier_escape(false),
                    Some(c) if is_id_continue(c) => {
                        self.bump();
                    }
                    _ => break,
                }
            }
        } else {
            self.error(
                INVALID_PRIVATE_IDENTIFIER,
                start_u,
                self.utf16_pos,
                "a private identifier must have a name after `#`",
            );
        }
        TokenKind::PrivateIdentifier
    }

    /// Scans an escape in the text of a string or a `template`. TypeScript reports
    /// a bad escape at the character where the escape goes wrong. Sloppy
    /// JavaScript accepts a legacy octal escape in a string, but no JavaScript
    /// accepts one in a template.
    fn scan_escape(&mut self, template: bool) {
        let backslash = self.utf16_pos;
        self.bump();
        match self.first() {
            None => {}
            Some('0'..='9')
                if template
                    || matches!(
                        self.script_kind,
                        ScriptKind::TypeScript | ScriptKind::TypeScriptReact
                    ) =>
            {
                self.scan_digit_escape(backslash);
            }
            // A line continuation consumes the terminator; CRLF counts as one.
            Some('\r') => {
                self.bump();
                if self.first() == Some('\n') {
                    self.bump();
                }
            }
            Some(c) if is_line_terminator(c) => {
                self.bump();
            }
            Some('x') => {
                self.bump();
                if !self.consume_fixed_hex(2) {
                    let fault =
                        self.fault_here(INVALID_ESCAPE, "a hexadecimal escape requires two digits");
                    self.report(fault);
                }
            }
            Some('u') => {
                self.bump();
                if let Err(faults) = self.read_hex_code_point() {
                    for fault in faults {
                        self.report(fault);
                    }
                }
            }
            Some(_) => {
                self.bump();
            }
        }
    }

    /// Scans an escape that begins with a digit. TypeScript rejects `\8`, `\9`
    /// and a legacy octal escape in every file. It accepts `\0` before a
    /// character that is not a digit.
    fn scan_digit_escape(&mut self, backslash: usize) {
        let Some(first) = self.bump() else {
            return;
        };
        if matches!(first, '8' | '9') {
            self.error(
                NON_OCTAL_DECIMAL_ESCAPE,
                backslash,
                self.utf16_pos,
                format!("the escape `\\{first}` is not allowed"),
            );
            return;
        }
        if first == '0' && !self.first().is_some_and(|c| c.is_ascii_digit()) {
            return;
        }
        // An escape that starts with 0 to 3 has up to three octal digits; one
        // that starts with 4 to 7 has up to two.
        let mut value = first.to_digit(8).unwrap_or(0);
        let limit = if value < 4 { 3 } else { 2 };
        for _ in 1..limit {
            match self.first().and_then(|c| c.to_digit(8)) {
                Some(digit) => {
                    self.bump();
                    value = value * 8 + digit;
                }
                None => break,
            }
        }
        self.error(
            LEGACY_OCTAL_ESCAPE,
            backslash,
            self.utf16_pos,
            format!("a legacy octal escape is not allowed; write `\\x{value:02x}`"),
        );
    }

    /// Reads the code point of a `\u` escape after its `u`, in the four-digit
    /// or the braced form.
    fn read_hex_code_point(&mut self) -> Result<u32, Vec<EscapeFault>> {
        if self.first() != Some('{') {
            let mut value: u32 = 0;
            for _ in 0..4 {
                match self.first().and_then(|c| c.to_digit(16)) {
                    Some(digit) if !self.is_cancelled() => {
                        self.bump();
                        value = value * 16 + digit;
                    }
                    _ => {
                        return Err(vec![self.fault_here(
                            INVALID_UNICODE_ESCAPE,
                            "a unicode escape requires four hexadecimal digits",
                        )]);
                    }
                }
            }
            return Ok(value);
        }
        self.bump();
        let digits = self.utf16_pos;
        let mut value: u32 = 0;
        while let Some(digit) = self.first().and_then(|c| c.to_digit(16)) {
            if self.is_cancelled() {
                break;
            }
            self.bump();
            value = value.saturating_mul(16).saturating_add(digit);
        }
        if self.utf16_pos == digits {
            return Err(vec![self.fault_here(
                INVALID_UNICODE_ESCAPE,
                "a unicode escape has no digits",
            )]);
        }
        let mut faults = Vec::new();
        if value > 0x0010_FFFF {
            faults.push((
                UNICODE_ESCAPE_OUT_OF_RANGE,
                digits,
                self.utf16_pos,
                "a unicode escape is greater than the maximum code point",
            ));
        }
        match self.first() {
            Some('}') => {
                self.bump();
            }
            None => faults.push(self.fault_here(
                UNICODE_ESCAPE_AT_END,
                "a unicode escape reaches the end of the text",
            )),
            Some(_) => faults.push(self.fault_here(
                UNTERMINATED_UNICODE_ESCAPE,
                "a unicode escape is missing its closing brace",
            )),
        }
        if faults.is_empty() {
            Ok(value)
        } else {
            Err(faults)
        }
    }

    /// A fault at the next character, or at the end of the text.
    fn fault_here(&self, code: DiagnosticCode, message: &'static str) -> EscapeFault {
        let width = self.first().map_or(0, char::len_utf16);
        (code, self.utf16_pos, self.utf16_pos + width, message)
    }

    fn report(&mut self, (code, start, end, message): EscapeFault) {
        self.error(code, start, end, message);
    }

    /// Consumes exactly `count` hexadecimal digits, or as many as are present,
    /// returning whether the full count was available.
    fn consume_fixed_hex(&mut self, count: usize) -> bool {
        for _ in 0..count {
            if self.is_cancelled() {
                break;
            }
            match self.first() {
                Some(c) if c.is_ascii_hexdigit() => {
                    self.bump();
                }
                _ => return false,
            }
        }
        true
    }

    fn scan_operator(&mut self, c: char, start_u: usize) -> TokenKind {
        match c {
            '(' => self.single(TokenKind::LParen),
            ')' => self.single(TokenKind::RParen),
            '[' => self.single(TokenKind::LBracket),
            ']' => self.single(TokenKind::RBracket),
            ',' => self.single(TokenKind::Comma),
            ';' => self.single(TokenKind::Semicolon),
            ':' => self.single(TokenKind::Colon),
            '~' => self.single(TokenKind::Tilde),
            '@' => self.single(TokenKind::At),
            '.' => {
                if self.second() == Some('.') && self.third() == Some('.') {
                    self.advance(3);
                    TokenKind::DotDotDot
                } else {
                    self.single(TokenKind::Dot)
                }
            }
            '+' => match self.second() {
                Some('+') => self.pair(TokenKind::PlusPlus),
                Some('=') => self.pair(TokenKind::PlusEq),
                _ => self.single(TokenKind::Plus),
            },
            '-' => match self.second() {
                Some('-') => self.pair(TokenKind::MinusMinus),
                Some('=') => self.pair(TokenKind::MinusEq),
                _ => self.single(TokenKind::Minus),
            },
            '*' => match self.second() {
                Some('*') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::StarStarEq
                    } else {
                        self.pair(TokenKind::StarStar)
                    }
                }
                Some('=') => self.pair(TokenKind::StarEq),
                _ => self.single(TokenKind::Star),
            },
            '%' => match self.second() {
                Some('=') => self.pair(TokenKind::PercentEq),
                _ => self.single(TokenKind::Percent),
            },
            '=' => match self.second() {
                Some('=') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::EqEqEq
                    } else {
                        self.pair(TokenKind::EqEq)
                    }
                }
                Some('>') => self.pair(TokenKind::Arrow),
                _ => self.single(TokenKind::Eq),
            },
            '!' => match self.second() {
                Some('=') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::BangEqEq
                    } else {
                        self.pair(TokenKind::BangEq)
                    }
                }
                _ => self.single(TokenKind::Bang),
            },
            '<' => match self.second() {
                Some('<') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::LessLessEq
                    } else {
                        self.pair(TokenKind::LessLess)
                    }
                }
                Some('=') => self.pair(TokenKind::LessThanEq),
                _ => self.single(TokenKind::LessThan),
            },
            '>' => match self.second() {
                Some('>') => match self.third() {
                    Some('>') => {
                        if self.nth(3) == Some('=') {
                            self.advance(4);
                            TokenKind::GreaterGreaterGreaterEq
                        } else {
                            self.advance(3);
                            TokenKind::GreaterGreaterGreater
                        }
                    }
                    Some('=') => {
                        self.advance(3);
                        TokenKind::GreaterGreaterEq
                    }
                    _ => self.pair(TokenKind::GreaterGreater),
                },
                Some('=') => self.pair(TokenKind::GreaterThanEq),
                _ => self.single(TokenKind::GreaterThan),
            },
            '&' => match self.second() {
                Some('&') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::AmpAmpEq
                    } else {
                        self.pair(TokenKind::AmpAmp)
                    }
                }
                Some('=') => self.pair(TokenKind::AmpEq),
                _ => self.single(TokenKind::Amp),
            },
            '|' => match self.second() {
                Some('|') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::PipePipeEq
                    } else {
                        self.pair(TokenKind::PipePipe)
                    }
                }
                Some('=') => self.pair(TokenKind::PipeEq),
                _ => self.single(TokenKind::Pipe),
            },
            '^' => match self.second() {
                Some('=') => self.pair(TokenKind::CaretEq),
                _ => self.single(TokenKind::Caret),
            },
            '?' => match self.second() {
                Some('?') => {
                    if self.third() == Some('=') {
                        self.advance(3);
                        TokenKind::QuestionQuestionEq
                    } else {
                        self.pair(TokenKind::QuestionQuestion)
                    }
                }
                // `?.` is optional chaining only when not followed by a digit,
                // so `x?.5` scans as `?` then `.5`.
                Some('.') if !self.third().is_some_and(|d| d.is_ascii_digit()) => {
                    self.pair(TokenKind::QuestionDot)
                }
                _ => self.single(TokenKind::Question),
            },
            _ => {
                self.bump();
                self.error(
                    UNEXPECTED_CHARACTER,
                    start_u,
                    self.utf16_pos,
                    "this character cannot begin a token",
                );
                TokenKind::Unknown
            }
        }
    }

    fn single(&mut self, kind: TokenKind) -> TokenKind {
        self.bump();
        kind
    }

    fn pair(&mut self, kind: TokenKind) -> TokenKind {
        self.bump();
        self.bump();
        kind
    }

    fn advance(&mut self, count: usize) {
        for _ in 0..count {
            if self.is_cancelled() {
                break;
            }
            if self.bump().is_none() {
                break;
            }
        }
    }

    fn reset_to_last(&mut self) {
        self.byte_pos = self.last_start_byte;
        self.utf16_pos = self.last_start_utf16;
    }

    fn rest(&self) -> &str {
        &self.text[self.byte_pos..]
    }

    fn first(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn second(&self) -> Option<char> {
        self.nth(1)
    }

    fn third(&self) -> Option<char> {
        self.nth(2)
    }

    fn nth(&self, index: usize) -> Option<char> {
        self.rest().chars().nth(index)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.first()?;
        self.byte_pos += c.len_utf8();
        self.utf16_pos += c.len_utf16();
        Some(c)
    }

    fn make(&self, kind: TokenKind, start_u: usize) -> Token {
        let range = TextRange::new(Utf16Pos::new(start_u), Utf16Pos::new(self.utf16_pos))
            .expect("scanner ranges advance monotonically");
        Token::new(kind, range)
    }

    fn error(
        &mut self,
        code: DiagnosticCode,
        start_u: usize,
        end_u: usize,
        message: impl Into<Cow<'static, str>>,
    ) {
        let range = TextRange::new(Utf16Pos::new(start_u), Utf16Pos::new(end_u))
            .expect("diagnostic ranges advance monotonically");
        self.diagnostics
            .push(Diagnostic::error(code, self.source_id, range, message));
    }
}

/// Returns whether a code point is ECMAScript scanner trivia whitespace.
fn is_whitespace(c: char) -> bool {
    matches!(
        c,
        '\u{0009}' | '\u{000B}' | '\u{000C}' | '\u{0020}' | '\u{00A0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}' | '\u{FEFF}'
    ) || is_line_terminator(c)
}

fn is_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn is_id_start(c: char) -> bool {
    c == '$' || c == '_' || unicode_id_start::is_id_start(c)
}

fn is_id_continue(c: char) -> bool {
    c == '$' || c == '\u{200C}' || c == '\u{200D}' || unicode_id_start::is_id_continue(c)
}

/// Returns whether an escaped identifier spells an unconditional reserved word.
fn is_unconditional_reserved_word(word: &str) -> bool {
    matches!(
        word,
        "break"
            | "case"
            | "catch"
            | "class"
            | "const"
            | "continue"
            | "debugger"
            | "default"
            | "delete"
            | "do"
            | "else"
            | "enum"
            | "export"
            | "extends"
            | "false"
            | "finally"
            | "for"
            | "function"
            | "if"
            | "import"
            | "in"
            | "instanceof"
            | "new"
            | "null"
            | "return"
            | "super"
            | "switch"
            | "this"
            | "throw"
            | "true"
            | "try"
            | "typeof"
            | "var"
            | "void"
            | "while"
            | "with"
    )
}

/// Maps a raw, escape-free identifier lexeme to its reserved or contextual
/// keyword token, if any. The parser decides where contextual keywords are used
/// as ordinary identifiers.
fn keyword_kind(word: &str) -> Option<TokenKind> {
    Some(match word {
        "abstract" => TokenKind::KwAbstract,
        "accessor" => TokenKind::KwAccessor,
        "any" => TokenKind::KwAny,
        "as" => TokenKind::KwAs,
        "asserts" => TokenKind::KwAsserts,
        "async" => TokenKind::KwAsync,
        "await" => TokenKind::KwAwait,
        "bigint" => TokenKind::KwBigint,
        "boolean" => TokenKind::KwBoolean,
        "break" => TokenKind::KwBreak,
        "case" => TokenKind::KwCase,
        "catch" => TokenKind::KwCatch,
        "class" => TokenKind::KwClass,
        "const" => TokenKind::KwConst,
        "constructor" => TokenKind::KwConstructor,
        "continue" => TokenKind::KwContinue,
        "declare" => TokenKind::KwDeclare,
        "debugger" => TokenKind::KwDebugger,
        "default" => TokenKind::KwDefault,
        "delete" => TokenKind::KwDelete,
        "do" => TokenKind::KwDo,
        "else" => TokenKind::KwElse,
        "enum" => TokenKind::KwEnum,
        "export" => TokenKind::KwExport,
        "extends" => TokenKind::KwExtends,
        "false" => TokenKind::KwFalse,
        "finally" => TokenKind::KwFinally,
        "for" => TokenKind::KwFor,
        "from" => TokenKind::KwFrom,
        "function" => TokenKind::KwFunction,
        "get" => TokenKind::KwGet,
        "if" => TokenKind::KwIf,
        "implements" => TokenKind::KwImplements,
        "import" => TokenKind::KwImport,
        "in" => TokenKind::KwIn,
        "infer" => TokenKind::KwInfer,
        "instanceof" => TokenKind::KwInstanceof,
        "interface" => TokenKind::KwInterface,
        "is" => TokenKind::KwIs,
        "keyof" => TokenKind::KwKeyof,
        "let" => TokenKind::KwLet,
        "namespace" => TokenKind::KwNamespace,
        "never" => TokenKind::KwNever,
        "new" => TokenKind::KwNew,
        "null" => TokenKind::KwNull,
        "number" => TokenKind::KwNumber,
        "object" => TokenKind::KwObject,
        "of" => TokenKind::KwOf,
        "override" => TokenKind::KwOverride,
        "package" => TokenKind::KwPackage,
        "private" => TokenKind::KwPrivate,
        "protected" => TokenKind::KwProtected,
        "public" => TokenKind::KwPublic,
        "readonly" => TokenKind::KwReadonly,
        "return" => TokenKind::KwReturn,
        "satisfies" => TokenKind::KwSatisfies,
        "set" => TokenKind::KwSet,
        "static" => TokenKind::KwStatic,
        "string" => TokenKind::KwString,
        "super" => TokenKind::KwSuper,
        "switch" => TokenKind::KwSwitch,
        "symbol" => TokenKind::KwSymbol,
        "this" => TokenKind::KwThis,
        "throw" => TokenKind::KwThrow,
        "true" => TokenKind::KwTrue,
        "try" => TokenKind::KwTry,
        "type" => TokenKind::KwType,
        "typeof" => TokenKind::KwTypeof,
        "undefined" => TokenKind::KwUndefined,
        "unique" => TokenKind::KwUnique,
        "unknown" => TokenKind::KwUnknown,
        "var" => TokenKind::KwVar,
        "void" => TokenKind::KwVoid,
        "while" => TokenKind::KwWhile,
        "with" => TokenKind::KwWith,
        "yield" => TokenKind::KwYield,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
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
        // A float or leading-zero integer cannot carry a BigInt suffix.
        assert_eq!(
            scan_text("1.5n").diagnostics()[0].code(),
            INVALID_BIGINT_LITERAL
        );
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
}
