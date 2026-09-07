//! The syntactic parser: a recovered token stream to a recovered [`SourceFile`].
//!
//! The parser is *total*: it accepts any scanned token stream, never panics,
//! and always produces a [`SourceFile`] whose statement list covers the whole
//! source. Grammar errors are represented with [`Token::missing`] tokens and
//! `Missing*` node products instead of aborting, and every list loop carries a
//! forward-progress guard so recovery can never stall.
//!
//! # Rescans
//!
//! Two lexical forms depend on grammar context, and the scanner deliberately
//! refuses to guess them. The parser resolves both with an explicit
//! token-cursor rescan over the already-scanned stream (the design
//! [`crate::scanner::Scanner`] documents as the alternative to driving the
//! scanner directly):
//!
//! * At an expression start, a [`TokenKind::Slash`]/[`TokenKind::SlashEq`]
//!   token is re-lexed as a regular-expression literal directly from the
//!   source text, using the same lexical rules as
//!   [`crate::scanner::Scanner::rescan_regex`]. The tokens covered by the new
//!   literal are replaced so the stored token stream still tiles the source.
//! * When a type-argument, type-parameter, or heritage list closes, a greedily
//!   formed `>>`/`>>>`/`>=`-family token is split into a single
//!   [`TokenKind::GreaterThan`] plus its remainder token, mirroring
//!   [`crate::scanner::Scanner::rescan_greater_than`]. The symmetric split is
//!   applied to `<<` when a type context opens.
//!
//! Template literals never need a parser rescan here: the single-pass scanner
//! already segments them deterministically with brace tracking.
//!
//! # Context sensitivity
//!
//! Contextual keywords are produced by the scanner as dedicated tokens; the
//! parser decides from grammar position whether `type`, `as`, `namespace`,
//! `let`, and the rest act as keywords or ordinary identifiers.
//! [`ScriptKind`] drives the remaining decisions: TypeScript-only syntax in a
//! JavaScript source parses (for recovery) but is diagnosed, `<T>expr` type
//! assertions exist only in non-React TypeScript, and a `<` opening JSX in a
//! React source (`.tsx`/`.jsx`) is parsed into JSX element, fragment, and
//! self-closing-element nodes with `Missing*` recovery for malformed tags.

use std::sync::Arc;

use crate::diagnostic::{Diagnostic, DiagnosticCode, Recovered};
use crate::scanner::ScannedSource;
use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
use crate::syntax::{
    Accessibility, ArrayBindingElement, ArrayBindingPattern, ArrayElement, ArrayLiteral,
    ArrowFunction, AsExpression, AssignmentArrayElement, AssignmentArrayPattern,
    AssignmentBindingPattern, AssignmentExpression, AssignmentMemberTarget,
    AssignmentObjectPattern, AssignmentObjectProperty, AssignmentOperator, AssignmentTarget,
    AssignmentTargetNode, AutoAccessor, AwaitExpression, BigIntLiteral, BinaryExpression,
    BinaryOperator, BindingPattern, Block, BlockNode, BooleanLiteral, CallArgument, CallExpression,
    CallSignature, CatchClause, CatchClauseNode, ClassDeclaration, ClassExpression, ClassHeritage,
    ClassMember, ClassMemberNode, ClassProperty, ConditionalExpression, ConditionalType,
    ConstructSignature, ConstructorDeclaration, ConstructorType, DeclarationModifiers, Decorator,
    DecoratorNode, DoWhileStatement, EntityName, EnumDeclaration, EnumMember, EnumMemberNode,
    ExportAllDeclaration, ExportDeclaration, ExportDefaultDeclaration, ExportDefaultValue,
    ExportNamedDeclaration, ExportSpecifier, ExportSpecifierMode, ExportSpecifierNode, Expr,
    Expression, ExpressionStatement, ExternalModuleReference, ForBinding, ForInStatement,
    ForInitializer, ForOfMode, ForOfStatement, ForStatement, FunctionBody, FunctionDeclaration,
    FunctionExpression, FunctionLike, FunctionType, FunctionTypeParameter, Identifier,
    IdentifierNode, IfStatement, ImportAttribute, ImportAttributes, ImportBinding, ImportClause,
    ImportDeclaration, ImportEqualsDeclaration, ImportExpression, ImportSpecifier,
    ImportSpecifierMode, ImportSpecifierNode, ImportType, IndexSignature, IndexedAccessType,
    InferType, InterfaceDeclaration, JsxAttribute, JsxAttributeInitializer, JsxAttributeItem,
    JsxAttributeName, JsxChild, JsxClosingElement, JsxClosingElementNode, JsxElement,
    JsxElementName, JsxExpressionContainer, JsxExpressionContainerNode, JsxFragment, JsxMemberName,
    JsxNamespacedName, JsxOpeningElement, JsxSelfClosingElement, JsxSpreadAttribute,
    JsxSpreadChild, JsxSpreadChildNode, JsxText, JumpStatement, KeywordType, LabeledStatement,
    Literal, LogicalExpression, LogicalOperator, MappedModifier, MappedType, MemberExpression,
    MemberProperty, MetaProperty, MethodDeclaration, MissingNode, ModuleExportName,
    NamespaceDeclaration, NamespaceKeyword, NamespaceName, NewExpression, Node, NodeId, NodeKind,
    NonNullExpression, NullLiteral, NumericLiteral, ObjectBindingPattern, ObjectBindingProperty,
    ObjectLiteral, ObjectMember, ObjectMemberNode, ObjectMethod, ObjectProperty, ObjectType,
    Parameter, ParameterModifiers, ParameterNode, Pattern, PrivateIdentifier, PropertyModifier,
    PropertyName, RegexLiteral, RestBindingPattern, ReturnStatement, SatisfiesExpression,
    SequenceExpression, SourceFile, SpreadElement, Statement, Stmt, StringLiteral,
    StringLiteralNode, SwitchCase, SwitchCaseNode, SwitchStatement, TaggedTemplateExpression,
    TemplateElement, TemplateLiteral, TemplateLiteralType, ThrowStatement, Token, TokenKind,
    TryStatement, TupleElement, TupleType, Ty, TypeAliasDeclaration, TypeAnnotation,
    TypeAnnotationNode, TypeArgumentList, TypeAssertionExpression, TypeIndexSignature, TypeLiteral,
    TypeMember, TypeMemberNode, TypeMethodSignature, TypeNode, TypeOperator, TypeParameter,
    TypeParameterList, TypeParameterNode, TypePredicate, TypePropertySignature, TypeQuery,
    TypeReference, UnaryExpression, UnaryOperator, UpdateExpression, UpdateOperator,
    VariableDeclaration, VariableDeclarator, VariableDeclaratorNode, VariableKind, Variance,
    WhileStatement, WithStatement, YieldExpression, cook_identifier_text,
};
use bamts_cancel::{CancellationToken, Cancelled};
use std::error::Error;
use std::fmt;

/// A token of one kind was required by the grammar but absent.
const EXPECTED_TOKEN: DiagnosticCode = DiagnosticCode::new("BAMTS-P001");
/// An expression was required but the next token cannot begin one.
const EXPECTED_EXPRESSION: DiagnosticCode = DiagnosticCode::new("BAMTS-P002");
/// An identifier was required but the next token is not identifier-like.
const EXPECTED_IDENTIFIER: DiagnosticCode = DiagnosticCode::new("BAMTS-P003");
/// A type was required but the next token cannot begin one.
const EXPECTED_TYPE: DiagnosticCode = DiagnosticCode::new("BAMTS-P004");
/// A token no grammar production could consume was skipped for recovery.
const UNEXPECTED_TOKEN: DiagnosticCode = DiagnosticCode::new("BAMTS-P005");
/// TypeScript-only syntax appeared in a JavaScript source.
const TYPESCRIPT_SYNTAX_IN_JAVASCRIPT: DiagnosticCode = DiagnosticCode::new("BAMTS-P007");
/// A property name was required but the next token cannot begin one.
const EXPECTED_PROPERTY_NAME: DiagnosticCode = DiagnosticCode::new("BAMTS-P009");
/// A class member used the `export` keyword as a modifier.
const EXPORT_MODIFIER_ON_CLASS_ELEMENT: DiagnosticCode = DiagnosticCode::new("BAMTS-C051");
/// Nesting exceeded the recovery depth bound; the construct was abandoned.
const NESTING_TOO_DEEP: DiagnosticCode = DiagnosticCode::new("BAMTS-P010");
/// A `using` / `await using` declaration violated the resource grammar.
/// A `using` / `await using` declaration binding was not an identifier, or the
/// declaration appeared in a context the resource grammar forbids.
pub const INVALID_USING_DECLARATION: DiagnosticCode = DiagnosticCode::new("BAMTS-P011");
/// A `using` / `await using` declaration required an initializer but none was
/// provided.
pub const USING_DECLARATION_REQUIRES_INITIALIZER: DiagnosticCode =
    DiagnosticCode::new("BAMTS-P012");
const UNTERMINATED_REGEX: DiagnosticCode = DiagnosticCode::new("BAMTS-L004");
/// An argument-bearing yield expression parsed outside any generator.
const YIELD_OUTSIDE_GENERATOR: DiagnosticCode = DiagnosticCode::new("BAMTS-P017");
/// An await expression parsed inside a non-async function-like.
const AWAIT_OUTSIDE_ASYNC: DiagnosticCode = DiagnosticCode::new("BAMTS-P018");

/// A parser operation was interrupted before completion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// The caller requested cancellation.
    Cancelled(Cancelled),
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Cancelled(_) => formatter.write_str("parse cancelled"),
        }
    }
}

impl Error for ParseError {}

impl From<Cancelled> for ParseError {
    fn from(cancelled: Cancelled) -> Self {
        ParseError::Cancelled(cancelled)
    }
}

impl From<ParseError> for Cancelled {
    fn from(error: ParseError) -> Self {
        match error {
            ParseError::Cancelled(cancelled) => cancelled,
        }
    }
}

impl From<crate::scanner::ScanError> for ParseError {
    fn from(error: crate::scanner::ScanError) -> Self {
        match error {
            crate::scanner::ScanError::Cancelled(cancelled) => ParseError::Cancelled(cancelled),
        }
    }
}

/// The maximum expression/type nesting depth before recovery abandons a
/// construct.
///
/// A single depth budget is shared by every recursive grammar edge an attacker
/// can nest without a bracketed list in between: prefix unary operators, the
/// right-recursive `**` operator, conditional, assignment, and parenthesized
/// expressions, plus types. Flat lists (statements, members, arguments,
/// elements) are parsed iteratively, so this bound is reached only through
/// genuinely nested syntax such as `- - - …` or `((((…))))`, keeping
/// attacker-controlled inputs from exhausting the native stack without any
/// process-wide stack workaround.
const MAX_DEPTH: u32 = 256;

/// Parses a scanned source into a recovered [`SourceFile`].
///
/// The scanner's diagnostics are consumed, unioned with the parse diagnostics,
/// canonically ordered, and deduplicated; the identical vector is stored in the
/// [`SourceFile`] and returned in the [`Recovered`] wrapper. The stored token
/// stream is the parser-observed stream: identical to the scanner's except
/// where a grammar-driven rescan merged a regular-expression literal or split
/// a `>`-family operator, so it still tiles the source and retains all trivia
/// and the end-of-file token.
#[must_use]
pub fn parse(scanned: Recovered<ScannedSource>) -> Recovered<SourceFile> {
    match parse_with_cancel(scanned, CancellationToken::new()) {
        Ok(recovered) => recovered,
        Err(_) => unreachable!("fresh token is never cancelled"),
    }
}

/// Parses a scanned source with cooperative cancellation.
///
/// A caller-supplied [`CancellationToken`] is checked before parsing, at every
/// statement boundary, and inside long list/recovery loops. Triggering it
/// aborts parsing with [`ParseError::Cancelled`].
pub fn parse_with_cancel(
    scanned: Recovered<ScannedSource>,
    cancel: CancellationToken,
) -> Result<Recovered<SourceFile>, ParseError> {
    if cancel.is_cancelled() {
        return Err(ParseError::Cancelled(Cancelled));
    }

    let (scanned, lexical) = scanned.into_parts();
    let source_id = scanned.source_id();
    let script_kind = scanned.script_kind();
    let source = Arc::clone(scanned.source());
    let eof = *scanned.eof();
    let tokens = scanned.tokens().to_vec();

    let mut parser = Parser::new_with_cancel(source_id, script_kind, source, tokens, eof, cancel);
    let statements = parser.parse_statements_until(&[]);

    // The default scanner pass emits only `Slash`/`SlashEq`, never a
    // `RegularExpressionLiteral`; every such token in the final stream is a
    // committed parser regex rescan. The lexical diagnostics the default pass
    // recorded inside those spans reflect the wrong (division) interpretation,
    // so they are dropped and superseded by the rescan's own diagnostics.
    let regex_spans: Vec<TextRange> = parser
        .tokens
        .iter()
        .filter(|t| t.kind() == TokenKind::RegularExpressionLiteral)
        .map(|t| t.range())
        .collect();
    // Spans reinterpreted as JSX likewise supersede the default pass's lexical
    // diagnostics: character data and attribute strings were mis-lexed there.
    let jsx_spans = &parser.jsx_spans;
    let mut diagnostics = lexical;
    diagnostics.retain(|diagnostic| {
        let start = diagnostic.range().start().get();
        let in_span = |span: &TextRange| start >= span.start().get() && start < span.end().get();
        !regex_spans.iter().any(in_span) && !jsx_spans.iter().any(in_span)
    });
    diagnostics.extend(parser.diagnostics.iter().cloned());
    diagnostics.sort();
    diagnostics.dedup();

    let full_range = TextRange::new(Utf16Pos::ZERO, parser.source.len_utf16())
        .expect("a source range starts at zero");
    let was_cancelled = parser.is_cancelled();
    let file_id = parser.fresh_id();
    let file = SourceFile::new(
        file_id,
        source_id,
        script_kind,
        full_range,
        parser.source,
        parser.tokens,
        statements,
        eof,
        diagnostics.clone(),
    );

    if was_cancelled {
        return Err(ParseError::Cancelled(Cancelled));
    }

    Ok(Recovered::new(file, diagnostics))
}

/// One reversible token-stream rescan, journaled so speculative parses can
/// undo their lexical reinterpretations on rollback.
struct RescanEdit {
    index: usize,
    removed: Vec<Token>,
    inserted: usize,
}

/// A restorable parser position for speculative parsing.
#[derive(Clone, Copy)]
struct ParserCheckpoint {
    cursor: usize,
    prev_end: usize,
    diagnostics: usize,
    next_node_id: u32,
    journal: usize,
    jsx_spans: usize,
}

#[derive(Clone, Copy, Default)]
struct KeywordContext {
    await_reserved: bool,
    yield_reserved: bool,
    /// Inside any function-like body or parameter list. Top-level await
    /// is legal in modules, so TS1308 fires only when this is set;
    /// yield expressions are illegal outside generators everywhere.
    in_function: bool,
}

/// Whether `global` / string-named module forms are recognized as ambient at
/// the current statement level, matching the TypeScript ambient-context rules.
///
/// Names are ambient only directly under a `declare` keyword or directly
/// inside the body of a string-named ambient module. A nested string module's
/// own body is not ambient, and namespace / `global` bodies are never ambient.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AmbientContext {
    /// Not an ambient name context.
    None,
    /// Parsing the statement directly under a `declare` keyword.
    DeclareTarget,
    /// Parsing the direct body of a string-named ambient module.
    ModuleBody,
}

struct Parser {
    source_id: SourceId,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
    tokens: Vec<Token>,
    eof: Token,
    /// Index of the current significant (non-trivia) token.
    cursor: usize,
    /// UTF-16 end of the most recently consumed significant token.
    prev_end: usize,
    diagnostics: Vec<Diagnostic>,
    next_node_id: u32,
    journal: Vec<RescanEdit>,
    depth: u32,
    keyword_context: KeywordContext,
    /// Ambient name recognition context for the current statement level.
    ambient: AmbientContext,
    /// Source spans reinterpreted as JSX. Lexical diagnostics the default pass
    /// recorded inside them reflect a non-JSX reading and are dropped, mirroring
    /// the regex-rescan span handling.
    jsx_spans: Vec<TextRange>,
    /// Cooperative cancellation signal checked at statement and list boundaries.
    cancel: CancellationToken,
}

fn is_trivia(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace
            | TokenKind::LineComment
            | TokenKind::BlockComment
            | TokenKind::Shebang
            | TokenKind::Unknown
    )
}

fn empty_range(at: Utf16Pos) -> TextRange {
    TextRange::new(at, at).expect("an empty range is ordered")
}

fn is_line_terminator(c: char) -> bool {
    matches!(c, '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

#[allow(dead_code)]
fn is_id_continue(c: char) -> bool {
    c == '$' || c == '\u{200C}' || c == '\u{200D}' || unicode_id_start::is_id_continue(c)
}

/// Returns whether a token may serve as an identifier reference or binding
/// name. This covers the scanner's contextual keywords, which the grammar
/// treats as ordinary identifiers outside their special positions, but not the
/// hard reserved words.
fn is_identifier_like(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Identifier
            | TokenKind::EscapedContextualKeyword
            | TokenKind::KwAbstract
            | TokenKind::KwAccessor
            | TokenKind::KwAny
            | TokenKind::KwAs
            | TokenKind::KwAsserts
            | TokenKind::KwAsync
            | TokenKind::KwAwait
            | TokenKind::KwBigint
            | TokenKind::KwBoolean
            | TokenKind::KwConstructor
            | TokenKind::KwDeclare
            | TokenKind::KwFrom
            | TokenKind::KwGet
            | TokenKind::KwImplements
            | TokenKind::KwInfer
            | TokenKind::KwInterface
            | TokenKind::KwIs
            | TokenKind::KwKeyof
            | TokenKind::KwLet
            | TokenKind::KwNamespace
            | TokenKind::KwNever
            | TokenKind::KwNumber
            | TokenKind::KwObject
            | TokenKind::KwOf
            | TokenKind::KwOverride
            | TokenKind::KwPackage
            | TokenKind::KwPrivate
            | TokenKind::KwProtected
            | TokenKind::KwPublic
            | TokenKind::KwReadonly
            | TokenKind::KwSatisfies
            | TokenKind::KwSet
            | TokenKind::KwStatic
            | TokenKind::KwString
            | TokenKind::KwSymbol
            | TokenKind::KwType
            | TokenKind::KwUndefined
            | TokenKind::KwUnique
            | TokenKind::KwUnknown
            | TokenKind::KwYield
    )
}

/// Returns whether a token can appear as a property name after `.`, in an
/// object literal, or as a class member name. Every keyword qualifies.
fn is_any_word(kind: TokenKind) -> bool {
    is_identifier_like(kind)
        || kind == TokenKind::EscapedReservedWord
        || matches!(
            kind,
            TokenKind::KwBreak
                | TokenKind::KwCase
                | TokenKind::KwCatch
                | TokenKind::KwClass
                | TokenKind::KwConst
                | TokenKind::KwContinue
                | TokenKind::KwDebugger
                | TokenKind::KwDefault
                | TokenKind::KwDelete
                | TokenKind::KwDo
                | TokenKind::KwElse
                | TokenKind::KwEnum
                | TokenKind::KwExport
                | TokenKind::KwExtends
                | TokenKind::KwFalse
                | TokenKind::KwFinally
                | TokenKind::KwFor
                | TokenKind::KwFunction
                | TokenKind::KwIf
                | TokenKind::KwImport
                | TokenKind::KwIn
                | TokenKind::KwInstanceof
                | TokenKind::KwNew
                | TokenKind::KwNull
                | TokenKind::KwReturn
                | TokenKind::KwSuper
                | TokenKind::KwSwitch
                | TokenKind::KwThis
                | TokenKind::KwThrow
                | TokenKind::KwTrue
                | TokenKind::KwTry
                | TokenKind::KwTypeof
                | TokenKind::KwVar
                | TokenKind::KwVoid
                | TokenKind::KwWhile
                | TokenKind::KwWith
        )
}

impl Parser {
    #[cfg(test)]
    fn new(
        source_id: SourceId,
        script_kind: ScriptKind,
        source: Arc<SourceText>,
        tokens: Vec<Token>,
        eof: Token,
    ) -> Self {
        Self::new_with_cancel(
            source_id,
            script_kind,
            source,
            tokens,
            eof,
            CancellationToken::new(),
        )
    }

    fn new_with_cancel(
        source_id: SourceId,
        script_kind: ScriptKind,
        source: Arc<SourceText>,
        tokens: Vec<Token>,
        eof: Token,
        cancel: CancellationToken,
    ) -> Self {
        let mut parser = Self {
            source_id,
            script_kind,
            source,
            tokens,
            eof,
            cursor: 0,
            prev_end: 0,
            diagnostics: Vec::new(),
            next_node_id: 0,
            journal: Vec::new(),
            depth: 0,
            keyword_context: KeywordContext::default(),
            ambient: AmbientContext::None,
            jsx_spans: Vec::new(),
            cancel,
        };
        parser.cursor = parser.next_significant(0);
        parser
    }

    /// Returns whether cancellation has been requested.
    fn is_cancelled(&self) -> bool {
        self.cancel.is_cancelled()
    }

    // ------------------------------------------------------------------
    // Cursor primitives
    // ------------------------------------------------------------------

    fn next_significant(&self, mut index: usize) -> usize {
        while index < self.tokens.len() && is_trivia(self.tokens[index].kind()) {
            index += 1;
        }
        index
    }

    fn cur(&self) -> Token {
        self.tokens.get(self.cursor).copied().unwrap_or(self.eof)
    }

    fn kind(&self) -> TokenKind {
        self.cur().kind()
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.kind() == kind
    }

    fn at_eof(&self) -> bool {
        self.cursor >= self.tokens.len()
    }

    /// Returns the `n`-th significant token after the current one.
    fn nth(&self, n: usize) -> Token {
        let mut index = self.cursor;
        for _ in 0..n {
            index = self.next_significant(index + 1);
        }
        self.tokens.get(index).copied().unwrap_or(self.eof)
    }

    fn nth_kind(&self, n: usize) -> TokenKind {
        self.nth(n).kind()
    }

    fn bump(&mut self) -> Token {
        let token = self.cur();
        if self.cursor < self.tokens.len() {
            self.prev_end = token.range().end().get();
            self.cursor = self.next_significant(self.cursor + 1);
        }
        token
    }

    fn eat(&mut self, kind: TokenKind) -> Option<Token> {
        if self.at(kind) {
            Some(self.bump())
        } else {
            None
        }
    }

    fn cur_start(&self) -> Utf16Pos {
        self.cur().range().start()
    }

    /// The range from `start` to the end of the last consumed token. When no
    /// token was consumed, the range is empty at `start`.
    fn span_from(&self, start: Utf16Pos) -> TextRange {
        let end = self.prev_end.max(start.get());
        TextRange::new(start, Utf16Pos::new(end)).expect("spans grow forward")
    }

    fn fresh_id(&mut self) -> NodeId {
        let id = NodeId::new(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    fn node<T>(&mut self, start: Utf16Pos, data: T) -> Node<T> {
        let range = self.span_from(start);
        let id = self.fresh_id();
        Node::new(id, range, data)
    }

    fn node_at<T>(&mut self, range: TextRange, data: T) -> Node<T> {
        let id = self.fresh_id();
        Node::new(id, range, data)
    }

    fn lexeme(&self, token: Token) -> &str {
        if token.is_missing() {
            return "";
        }
        let range = token.range();
        let (Ok(start), Ok(end)) = (
            self.source.utf16_to_byte(range.start()),
            self.source.utf16_to_byte(range.end()),
        ) else {
            return "";
        };
        self.source.as_str().get(start..end).unwrap_or("")
    }

    fn cur_lexeme(&self) -> &str {
        self.lexeme(self.cur())
    }

    /// Returns whether a line terminator sits between the previous consumed
    /// significant token and the current one.
    fn has_newline_before(&self) -> bool {
        self.newline_in_gap(self.prev_end, self.cur_start().get())
    }

    /// Returns whether a line terminator sits between significant tokens `n-1`
    /// and `n` ahead of the cursor.
    fn has_newline_before_nth(&self, n: usize) -> bool {
        let before = if n == 0 {
            self.prev_end
        } else {
            self.nth(n - 1).range().end().get()
        };
        self.newline_in_gap(before, self.nth(n).range().start().get())
    }

    fn newline_in_gap(&self, from_utf16: usize, to_utf16: usize) -> bool {
        if to_utf16 <= from_utf16 {
            return false;
        }
        let (Ok(start), Ok(end)) = (
            self.source.utf16_to_byte(Utf16Pos::new(from_utf16)),
            self.source.utf16_to_byte(Utf16Pos::new(to_utf16)),
        ) else {
            return false;
        };
        self.source.as_str()[start..end]
            .chars()
            .any(is_line_terminator)
    }

    // ------------------------------------------------------------------
    // Diagnostics and recovery products
    // ------------------------------------------------------------------

    fn error_at(&mut self, code: DiagnosticCode, range: TextRange, message: &'static str) {
        self.diagnostics
            .push(Diagnostic::error(code, self.source_id, range, message));
    }

    fn error_here(&mut self, code: DiagnosticCode, message: &'static str) {
        let range = if self.at_eof() {
            empty_range(self.eof.range().start())
        } else {
            self.cur().range()
        };
        self.error_at(code, range, message);
    }

    /// Consumes `kind` or records a diagnostic and returns a missing token
    /// anchored at the current position.
    fn expect(&mut self, kind: TokenKind, message: &'static str) -> Token {
        if let Some(token) = self.eat(kind) {
            return token;
        }
        self.error_here(EXPECTED_TOKEN, message);
        Token::missing(kind, empty_range(self.cur_start()))
    }

    fn missing_token(&self, kind: TokenKind) -> Token {
        Token::missing(kind, empty_range(self.cur_start()))
    }

    fn missing_expr(&mut self) -> Expr {
        let start = self.cur_start();
        self.node_at(
            empty_range(start),
            Expression::Missing(MissingNode::new(NodeKind::MissingExpression)),
        )
    }

    fn missing_type(&mut self) -> Ty {
        let start = self.cur_start();
        self.node_at(
            empty_range(start),
            TypeNode::Missing(MissingNode::new(NodeKind::MissingType)),
        )
    }

    fn missing_pattern(&mut self) -> Pattern {
        let start = self.cur_start();
        self.node_at(
            empty_range(start),
            BindingPattern::Missing(MissingNode::new(NodeKind::MissingBindingPattern)),
        )
    }

    fn missing_statement(&mut self) -> Stmt {
        let start = self.cur_start();
        self.node_at(
            empty_range(start),
            Statement::Missing(MissingNode::new(NodeKind::MissingStatement)),
        )
    }

    fn missing_ident(&mut self) -> IdentifierNode {
        let token = self.missing_token(TokenKind::Identifier);
        let range = token.range();
        self.node_at(range, Identifier::new(token))
    }
    fn with_keyword_context<T>(
        &mut self,
        context: KeywordContext,
        parse: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = std::mem::replace(&mut self.keyword_context, context);
        let result = parse(self);
        self.keyword_context = previous;
        result
    }

    fn escaped_identifier_is_reserved(&self, token: Token) -> bool {
        match token.kind() {
            TokenKind::EscapedReservedWord => true,
            TokenKind::EscapedContextualKeyword => {
                let cooked = cook_identifier_text(self.lexeme(token));
                matches!(cooked.as_deref(), Some("await")) && self.keyword_context.await_reserved
                    || matches!(cooked.as_deref(), Some("yield"))
                        && self.keyword_context.yield_reserved
            }
            _ => false,
        }
    }

    fn reject_reserved_identifier(&mut self, token: Token) {
        if self.escaped_identifier_is_reserved(token) {
            self.error_at(
                EXPECTED_IDENTIFIER,
                token.range(),
                "an escaped reserved word cannot be used as an identifier",
            );
        }
    }

    fn ident_from(&mut self, token: Token) -> IdentifierNode {
        self.reject_reserved_identifier(token);
        self.identifier_name_from(token)
    }

    fn identifier_name_from(&mut self, token: Token) -> IdentifierNode {
        let range = token.range();
        self.node_at(range, Identifier::new(token))
    }

    fn expect_identifier(&mut self, message: &'static str) -> IdentifierNode {
        if is_identifier_like(self.kind()) {
            let token = self.bump();
            return self.ident_from(token);
        }
        self.error_here(EXPECTED_IDENTIFIER, message);
        self.missing_ident()
    }

    /// Records a TypeScript-only construct when the script kind is JavaScript.
    fn note_typescript_syntax(&mut self, range: TextRange) {
        if matches!(
            self.script_kind,
            ScriptKind::JavaScript | ScriptKind::JavaScriptReact
        ) {
            self.error_at(
                TYPESCRIPT_SYNTAX_IN_JAVASCRIPT,
                range,
                "TypeScript syntax is not allowed in a JavaScript source",
            );
        }
    }

    fn is_typescript(&self) -> bool {
        matches!(
            self.script_kind,
            ScriptKind::TypeScript | ScriptKind::TypeScriptReact | ScriptKind::Json
        )
    }

    // ------------------------------------------------------------------
    // Depth guard
    // ------------------------------------------------------------------

    fn enter(&mut self) -> bool {
        if self.depth >= MAX_DEPTH {
            self.error_here(
                NESTING_TOO_DEEP,
                "this construct is nested too deeply to parse",
            );
            return false;
        }
        self.depth += 1;
        true
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    // ------------------------------------------------------------------
    // Speculation
    // ------------------------------------------------------------------

    fn checkpoint(&self) -> ParserCheckpoint {
        ParserCheckpoint {
            cursor: self.cursor,
            prev_end: self.prev_end,
            diagnostics: self.diagnostics.len(),
            next_node_id: self.next_node_id,
            journal: self.journal.len(),
            jsx_spans: self.jsx_spans.len(),
        }
    }

    fn rollback(&mut self, checkpoint: ParserCheckpoint) {
        while self.journal.len() > checkpoint.journal {
            let edit = self.journal.pop().expect("journal length checked");
            let end = edit.index + edit.inserted;
            self.tokens.splice(edit.index..end, edit.removed);
        }
        self.cursor = checkpoint.cursor;
        self.prev_end = checkpoint.prev_end;
        self.diagnostics.truncate(checkpoint.diagnostics);
        self.next_node_id = checkpoint.next_node_id;
        self.jsx_spans.truncate(checkpoint.jsx_spans);
    }

    // ------------------------------------------------------------------
    // Token-cursor rescans
    // ------------------------------------------------------------------

    /// Replaces `tokens[index..=last]` with `replacement`, journaling the edit.
    fn replace_tokens(&mut self, index: usize, last: usize, replacement: Vec<Token>) {
        let inserted = replacement.len();
        let removed: Vec<Token> = self.tokens.splice(index..=last, replacement).collect();
        self.journal.push(RescanEdit {
            index,
            removed,
            inserted,
        });
    }

    /// Reinterprets the current `/`/`/=` token as a regular-expression
    /// literal, merging the covered tokens. Grammar context (expression start)
    /// is the caller's assertion; the re-lex itself mirrors the scanner rules.
    /// is the caller's assertion; the re-lex itself mirrors the scanner rules.
    fn rescan_regex_here(&mut self) {
        if !matches!(self.kind(), TokenKind::Slash | TokenKind::SlashEq) || self.at_eof() {
            return;
        }
        let index = self.cursor;
        let start = self.tokens[index].range().start();
        let Ok(start_byte) = self.source.utf16_to_byte(start) else {
            return;
        };
        let text = &self.source.as_str()[start_byte..];
        let (consumed, terminated) = crate::scanner::scan_regex_slice(text);
        let mut end = start.get() + consumed;
        if !terminated {
            self.error_at(
                UNTERMINATED_REGEX,
                TextRange::new(start, Utf16Pos::new(end)).expect("regex spans grow forward"),
                "unterminated regular expression literal",
            );
        }

        // Absorb the pre-scanned tokens the literal covers. The default pass
        // can form a token that straddles the grammar-correct regex end: for
        // `/...\/.../` its two adjacent slashes look like a line comment.
        // Never widen the regex to that token's end. Re-scan only the trailing
        // fragment and append its shifted tokens so the final stream remains
        // byte-exact and the parser still sees the code after the literal.
        let mut last = index;
        while last + 1 < self.tokens.len() && self.tokens[last].range().end().get() < end {
            last += 1;
        }
        let covered_end = self.tokens[last].range().end().get();
        if covered_end < end {
            end = covered_end;
        }
        let range = TextRange::new(start, Utf16Pos::new(end)).expect("regex spans grow forward");
        let mut replacement = vec![Token::new(TokenKind::RegularExpressionLiteral, range)];
        if covered_end > end {
            replacement.extend(self.scan_shifted_fragment(end, covered_end));
        }
        self.replace_tokens(index, last, replacement);
    }

    /// Scans `[start, end)` as an isolated fragment and shifts every produced
    /// token and diagnostic back into the owning source's UTF-16 coordinates.
    /// This is used only for a base token's tail after a committed regex
    /// rescan; ordinary parser lexing always reuses the scanner's full stream.
    fn scan_shifted_fragment(&mut self, start: usize, end: usize) -> Vec<Token> {
        let (Ok(start_byte), Ok(end_byte)) = (
            self.source.utf16_to_byte(Utf16Pos::new(start)),
            self.source.utf16_to_byte(Utf16Pos::new(end)),
        ) else {
            return Vec::new();
        };
        // The fragment is a strict substring of an already budget-checked
        // source, so this can never breach the per-file cap; return no tokens
        // rather than panic if that invariant is ever violated.
        let Ok(fragment) =
            SourceText::new(self.source.as_str()[start_byte..end_byte].to_owned()).map(Arc::new)
        else {
            return Vec::new();
        };
        let recovered = crate::scanner::scan(self.source_id, self.script_kind, fragment);
        let (scanned, diagnostics) = recovered.into_parts();
        for diagnostic in diagnostics {
            let range = diagnostic.range();
            let shifted = TextRange::new(
                Utf16Pos::new(start + range.start().get()),
                Utf16Pos::new(start + range.end().get()),
            )
            .expect("shift preserves range ordering");
            self.diagnostics.push(diagnostic.with_range(shifted));
        }
        scanned
            .tokens()
            .iter()
            .map(|token| {
                let range = token.range();
                Token::new(
                    token.kind(),
                    TextRange::new(
                        Utf16Pos::new(start + range.start().get()),
                        Utf16Pos::new(start + range.end().get()),
                    )
                    .expect("shift preserves token ordering"),
                )
            })
            .collect()
    }

    /// Returns whether the current token begins with `>` so a type or heritage
    /// close can split it.
    fn at_greater_like(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::GreaterThan
                | TokenKind::GreaterGreater
                | TokenKind::GreaterGreaterGreater
                | TokenKind::GreaterThanEq
                | TokenKind::GreaterGreaterEq
                | TokenKind::GreaterGreaterGreaterEq
        )
    }

    /// Consumes exactly one `>`, splitting a greedily formed operator when
    /// needed. Mirrors `Scanner::rescan_greater_than` at the token level.
    fn expect_type_close(&mut self, message: &'static str) -> Token {
        if self.at(TokenKind::GreaterThan) {
            return self.bump();
        }
        let remainder = match self.kind() {
            TokenKind::GreaterGreater => Some(TokenKind::GreaterThan),
            TokenKind::GreaterGreaterGreater => Some(TokenKind::GreaterGreater),
            TokenKind::GreaterThanEq => Some(TokenKind::Eq),
            TokenKind::GreaterGreaterEq => Some(TokenKind::GreaterThanEq),
            TokenKind::GreaterGreaterGreaterEq => Some(TokenKind::GreaterGreaterEq),
            _ => None,
        };
        let Some(remainder) = remainder else {
            self.error_here(EXPECTED_TOKEN, message);
            return Token::missing(TokenKind::GreaterThan, empty_range(self.cur_start()));
        };
        let index = self.cursor;
        let range = self.tokens[index].range();
        let split = Utf16Pos::new(range.start().get() + 1);
        let head = Token::new(
            TokenKind::GreaterThan,
            TextRange::new(range.start(), split).expect("split point is inside the token"),
        );
        let tail = Token::new(
            remainder,
            TextRange::new(split, range.end()).expect("split point is inside the token"),
        );
        self.replace_tokens(index, index, vec![head, tail]);
        self.bump()
    }

    /// Returns whether the current token begins with `<` so a type context can
    /// open on it.
    fn at_less_like(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::LessThan | TokenKind::LessLess | TokenKind::LessLessEq
        )
    }

    /// Consumes exactly one `<`, splitting `<<`/`<<=` when a type context
    /// opens inside a greedily formed operator.
    fn expect_type_open(&mut self, message: &'static str) -> Token {
        if self.at(TokenKind::LessThan) {
            return self.bump();
        }
        let remainder = match self.kind() {
            TokenKind::LessLess => Some(TokenKind::LessThan),
            TokenKind::LessLessEq => Some(TokenKind::LessThanEq),
            _ => None,
        };
        let Some(remainder) = remainder else {
            self.error_here(EXPECTED_TOKEN, message);
            return Token::missing(TokenKind::LessThan, empty_range(self.cur_start()));
        };
        let index = self.cursor;
        let range = self.tokens[index].range();
        let split = Utf16Pos::new(range.start().get() + 1);
        let head = Token::new(
            TokenKind::LessThan,
            TextRange::new(range.start(), split).expect("split point is inside the token"),
        );
        let tail = Token::new(
            remainder,
            TextRange::new(split, range.end()).expect("split point is inside the token"),
        );
        self.replace_tokens(index, index, vec![head, tail]);
        self.bump()
    }

    // ------------------------------------------------------------------
    // Automatic semicolon insertion
    // ------------------------------------------------------------------

    /// Consumes a statement terminator: an explicit `;`, or an automatic
    /// semicolon before `}`, at end of file, or after a line terminator.
    fn expect_semicolon(&mut self) {
        if self.eat(TokenKind::Semicolon).is_some() {
            return;
        }
        if self.at(TokenKind::RBrace) || self.at_eof() || self.has_newline_before() {
            return;
        }
        self.error_here(EXPECTED_TOKEN, "expected `;`");
    }
}

// ---------------------------------------------------------------------------
// Statements and declarations
// ---------------------------------------------------------------------------

impl Parser {
    /// Parses statements until one of `stop` (or end of file), with a forward
    /// progress guard: an iteration that consumes nothing skips one token.
    fn parse_statements_until(&mut self, stop: &[TokenKind]) -> Vec<Stmt> {
        let mut statements = Vec::new();
        while !self.at_eof() && !stop.contains(&self.kind()) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let statement = self.parse_statement();
            statements.push(statement);
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped during recovery",
                );
            }
        }
        statements
    }

    fn parse_statement(&mut self) -> Stmt {
        if !self.enter() {
            let skipped = self.bump();
            let statement = self.missing_statement();
            let _ = skipped;
            return statement;
        }
        let statement = self.parse_statement_inner();
        self.leave();
        statement
    }

    fn parse_statement_inner(&mut self) -> Stmt {
        let start = self.cur_start();
        match self.kind() {
            TokenKind::Semicolon => {
                self.bump();
                self.node(start, Statement::Empty)
            }
            TokenKind::LBrace => {
                let block = self.parse_block();
                self.node(start, Statement::Block(block))
            }
            TokenKind::KwConst if self.nth_kind(1) == TokenKind::KwEnum => {
                self.bump();
                self.parse_enum_declaration(start, true)
            }
            TokenKind::KwVar | TokenKind::KwLet | TokenKind::KwConst
                if self.at_variable_declaration() =>
            {
                self.parse_variable_statement(start)
            }
            TokenKind::Identifier
                if self.cur_lexeme() == "using" && self.at_using_declaration(0) =>
            {
                self.parse_variable_statement(start)
            }
            TokenKind::KwAwait
                if self.nth(1).kind() == TokenKind::Identifier
                    && self.lexeme(self.nth(1)) == "using"
                    && self.at_using_declaration(1) =>
            {
                self.parse_variable_statement(start)
            }
            TokenKind::KwFunction => {
                let function = self.parse_function_like(Vec::new(), false, true);
                self.node(start, Statement::Function(FunctionDeclaration { function }))
            }
            TokenKind::KwAsync
                if self.nth_kind(1) == TokenKind::KwFunction && !self.has_newline_before_nth(1) =>
            {
                self.bump();
                let function = self.parse_function_like(Vec::new(), true, true);
                self.node(start, Statement::Function(FunctionDeclaration { function }))
            }
            TokenKind::KwClass => {
                let class = self.parse_class(Vec::new(), DeclarationModifiers::default(), true);
                self.node(start, Statement::Class(class))
            }
            TokenKind::At => self.parse_decorated_statement(start),
            TokenKind::KwAbstract if self.nth_kind(1) == TokenKind::KwClass => {
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                let modifiers = DeclarationModifiers {
                    is_abstract: true,
                    ..DeclarationModifiers::default()
                };
                let class = self.parse_class(Vec::new(), modifiers, true);
                self.node(start, Statement::Class(class))
            }
            TokenKind::KwIf => self.parse_if_statement(start),
            TokenKind::KwSwitch => self.parse_switch_statement(start),
            TokenKind::KwFor => self.parse_for_statement(start),
            TokenKind::KwWhile => self.parse_while_statement(start),
            TokenKind::KwDo => self.parse_do_while_statement(start),
            TokenKind::KwTry => self.parse_try_statement(start),
            TokenKind::KwWith => self.parse_with_statement(start),
            TokenKind::KwReturn => self.parse_return_statement(start),
            TokenKind::KwThrow => self.parse_throw_statement(start),
            TokenKind::KwBreak => self.parse_jump_statement(start, true),
            TokenKind::KwContinue => self.parse_jump_statement(start, false),
            TokenKind::KwDebugger => {
                self.bump();
                self.expect_semicolon();
                self.node(start, Statement::Debugger)
            }
            TokenKind::KwImport
                if !matches!(self.nth_kind(1), TokenKind::LParen | TokenKind::Dot) =>
            {
                self.parse_import_statement(start)
            }
            TokenKind::KwExport => self.parse_export_statement(start),
            TokenKind::KwInterface if is_identifier_like(self.nth_kind(1)) => {
                self.parse_interface_declaration(start)
            }
            TokenKind::KwType
                if is_identifier_like(self.nth_kind(1))
                    && matches!(self.nth_kind(2), TokenKind::Eq | TokenKind::LessThan)
                    && !self.has_newline_before_nth(1) =>
            {
                self.parse_type_alias_declaration(start)
            }
            TokenKind::KwEnum if is_identifier_like(self.nth_kind(1)) => {
                self.parse_enum_declaration(start, false)
            }
            TokenKind::KwNamespace
                if is_identifier_like(self.nth_kind(1))
                    && matches!(self.nth_kind(2), TokenKind::LBrace | TokenKind::Dot) =>
            {
                self.parse_namespace_declaration(start)
            }
            TokenKind::KwDeclare if self.at_declare_statement() => {
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                let inner =
                    self.with_ambient(AmbientContext::DeclareTarget, |this| this.parse_statement());
                self.node(start, Statement::Declare(Box::new(inner)))
            }
            TokenKind::Identifier
                if self.cur_lexeme() == "global" && self.nth_kind(1) == TokenKind::LBrace =>
            {
                self.parse_contextual_namespace(start)
            }
            TokenKind::Identifier
                if self.cur_lexeme() == "module"
                    && (matches!(
                        self.nth_kind(1),
                        TokenKind::LBrace | TokenKind::StringLiteral
                    ) || (self.name_is_ambient()
                        && is_identifier_like(self.nth_kind(1))
                        && matches!(self.nth_kind(2), TokenKind::LBrace | TokenKind::Dot))
                        || (self.name_is_ambient()
                            && !is_identifier_like(self.nth_kind(1))
                            && self.nth_kind(1) != TokenKind::Dot)) =>
            {
                self.parse_contextual_namespace(start)
            }
            kind if is_identifier_like(kind)
                && self.nth_kind(1) == TokenKind::Colon
                && !matches!(kind, TokenKind::KwDefault) =>
            {
                let label_token = self.bump();
                let label = self.ident_from(label_token);
                self.bump();
                let body = self.parse_statement();
                self.node(
                    start,
                    Statement::Labeled(LabeledStatement {
                        label,
                        body: Box::new(body),
                    }),
                )
            }
            _ => self.parse_expression_statement(start),
        }
    }

    /// `var` and `const` are reserved and always begin a declaration; `let` is
    /// contextual, so it starts one only when a binding follows and is
    /// otherwise an ordinary identifier.
    fn at_variable_declaration(&self) -> bool {
        if self.at(TokenKind::KwVar) || self.at(TokenKind::KwConst) {
            return true;
        }
        let next = self.nth_kind(1);
        is_identifier_like(next) || matches!(next, TokenKind::LBracket | TokenKind::LBrace)
    }

    /// A `using` declaration requires an identifier binding on the same line.
    /// The binding may carry a TypeScript type annotation, so a `:` is accepted
    /// only when a top-level `=` initializer follows the annotation. Because an
    /// ordinary expression never starts with two adjacent identifiers, this
    /// never steals a non-declaration.
    fn at_using_declaration(&self, offset: usize) -> bool {
        if !is_identifier_like(self.nth_kind(offset + 1)) || self.has_newline_before_nth(offset + 1)
        {
            return false;
        }
        match self.nth_kind(offset + 2) {
            TokenKind::Eq | TokenKind::Semicolon | TokenKind::KwOf => true,
            TokenKind::Colon => self.type_annotation_precedes_eq(offset + 2),
            _ => false,
        }
    }

    /// Scans from the annotation colon at significant offset `colon_offset` and
    /// reports whether a top-level `=` (the declaration initializer) follows the
    /// type. Parenthesis, array, and object brackets are balanced so a `;` or
    /// `=` inside the type (an object-type member separator, a construct-
    /// signature default) does not end the scan early; type-argument `<>` is not
    /// tracked, which is safe because `using IDENT :` is never an ordinary
    /// expression, so any top-level `=` still means a declaration. A single
    /// linear pass over raw token indices keeps this from becoming quadratic on
    /// hostile input.
    fn type_annotation_precedes_eq(&self, colon_offset: usize) -> bool {
        let mut index = self.cursor;
        for _ in 0..colon_offset {
            index = self.next_significant(index + 1);
        }
        let mut depth = 0i32;
        loop {
            if self.is_cancelled() {
                break false;
            }
            index = self.next_significant(index + 1);
            match self.tokens.get(index).copied().unwrap_or(self.eof).kind() {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    depth = depth.saturating_sub(1);
                    if depth < 0 {
                        return false;
                    }
                }
                TokenKind::Eq if depth == 0 => return true,
                TokenKind::Semicolon if depth == 0 => return false,
                TokenKind::EndOfFile => return false,
                _ => {}
            }
        }
    }

    /// `declare` prefixes a following declaration only when one can start.
    fn at_declare_statement(&self) -> bool {
        if self.has_newline_before_nth(1) {
            return false;
        }
        if self.nth_kind(1) == TokenKind::Identifier
            && matches!(self.lexeme(self.nth(1)), "global" | "module")
        {
            return true;
        }
        matches!(
            self.nth_kind(1),
            TokenKind::KwVar
                | TokenKind::KwLet
                | TokenKind::KwConst
                | TokenKind::KwFunction
                | TokenKind::KwClass
                | TokenKind::KwAbstract
                | TokenKind::KwInterface
                | TokenKind::KwType
                | TokenKind::KwEnum
                | TokenKind::KwNamespace
                | TokenKind::KwAsync
        )
    }

    fn parse_block(&mut self) -> BlockNode {
        let start = self.cur_start();
        self.expect(TokenKind::LBrace, "expected `{`");
        let statements = self.parse_statements_until(&[TokenKind::RBrace]);
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(start, Block { statements })
    }

    fn parse_variable_statement(&mut self, start: Utf16Pos) -> Stmt {
        let declaration = self.parse_variable_declaration(true);
        self.expect_semicolon();
        self.node(start, Statement::Variable(declaration))
    }

    fn variable_kind(&mut self) -> VariableKind {
        match self.kind() {
            TokenKind::KwVar => {
                self.bump();
                VariableKind::Var
            }
            TokenKind::KwLet => {
                self.bump();
                VariableKind::Let
            }
            TokenKind::KwConst => {
                self.bump();
                VariableKind::Const
            }
            TokenKind::KwAwait => {
                self.bump();
                // The caller verified `using` follows.
                self.bump();
                VariableKind::AwaitUsing
            }
            _ => {
                // `using` as a plain identifier token.
                self.bump();
                VariableKind::Using
            }
        }
    }

    /// Parses a `var`/`let`/`const`/`using` declaration. `allow_in` is false
    /// inside a `for (...)` head before the `in`/`of` decision.
    fn parse_variable_declaration(&mut self, allow_in: bool) -> VariableDeclaration {
        let start = self.cur().range().start();
        let kind = self.variable_kind();
        let mut declarations = Vec::new();
        loop {
            if self.is_cancelled() {
                break;
            }
            let declarator = self.parse_variable_declarator(allow_in);
            declarations.push(declarator);
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        let range = self.span_from(start);
        VariableDeclaration {
            range,
            kind,
            declarations,
        }
    }

    fn parse_variable_declarator(&mut self, allow_in: bool) -> VariableDeclaratorNode {
        let start = self.cur_start();
        let binding = self.parse_binding_pattern();
        let mut definite = false;
        if self.at(TokenKind::Bang) && !self.has_newline_before() {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            self.bump();
            definite = true;
        }
        let type_annotation = self.parse_optional_type_annotation();
        let initializer = if self.eat(TokenKind::Eq).is_some() {
            Some(Box::new(self.parse_assignment_expression(!allow_in)))
        } else {
            None
        };
        self.node(
            start,
            VariableDeclarator {
                binding,
                definite,
                type_annotation,
                initializer,
            },
        )
    }

    fn parse_optional_type_annotation(&mut self) -> Option<TypeAnnotationNode> {
        if !self.at(TokenKind::Colon) {
            return None;
        }
        let start = self.cur_start();
        let colon_range = self.cur().range();
        self.note_typescript_syntax(colon_range);
        self.bump();
        let type_node = self.parse_type();
        Some(self.node(
            start,
            TypeAnnotation {
                type_node: Box::new(type_node),
            },
        ))
    }

    fn parse_expression_statement(&mut self, start: Utf16Pos) -> Stmt {
        let before = self.cursor;
        let expression = self.parse_expression(false);
        if self.cursor == before {
            // Nothing could begin an expression: skip one token for progress.
            let skipped = self.bump();
            self.error_at(
                UNEXPECTED_TOKEN,
                skipped.range(),
                "this token cannot begin a statement",
            );
            return self.missing_statement();
        }
        self.expect_semicolon();
        self.node(
            start,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(expression),
            }),
        )
    }

    fn parse_if_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        self.expect(TokenKind::LParen, "expected `(`");
        let test = self.parse_expression(false);
        self.expect(TokenKind::RParen, "expected `)`");
        let consequent = self.parse_statement();
        let alternate = if self.eat(TokenKind::KwElse).is_some() {
            Some(Box::new(self.parse_statement()))
        } else {
            None
        };
        self.node(
            start,
            Statement::If(IfStatement {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate,
            }),
        )
    }

    fn parse_switch_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        self.expect(TokenKind::LParen, "expected `(`");
        let discriminant = self.parse_expression(false);
        self.expect(TokenKind::RParen, "expected `)`");
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut cases = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let case_start = self.cur_start();
            let test = if self.eat(TokenKind::KwCase).is_some() {
                Some(Box::new(self.parse_expression(false)))
            } else if self.eat(TokenKind::KwDefault).is_some() {
                None
            } else {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "expected `case` or `default`",
                );
                continue;
            };
            self.expect(TokenKind::Colon, "expected `:`");
            let consequent = self.parse_statements_until(&[
                TokenKind::KwCase,
                TokenKind::KwDefault,
                TokenKind::RBrace,
            ]);
            let case: SwitchCaseNode = self.node(case_start, SwitchCase { test, consequent });
            cases.push(case);
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(
            start,
            Statement::Switch(SwitchStatement {
                discriminant: Box::new(discriminant),
                cases,
            }),
        )
    }

    fn parse_for_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        let is_await = self.eat(TokenKind::KwAwait).is_some();
        self.expect(TokenKind::LParen, "expected `(`");

        // Empty initializer.
        if self.eat(TokenKind::Semicolon).is_some() {
            return self.finish_classic_for(start, None);
        }

        let decl_start = matches!(
            self.kind(),
            TokenKind::KwVar | TokenKind::KwLet | TokenKind::KwConst
        ) && self.at_variable_declaration()
            || (self.at(TokenKind::Identifier)
                && self.cur_lexeme() == "using"
                && (is_identifier_like(self.nth_kind(1))
                    || matches!(self.nth_kind(1), TokenKind::LBracket | TokenKind::LBrace)))
            || (self.at(TokenKind::KwAwait)
                && self.nth(1).kind() == TokenKind::Identifier
                && self.lexeme(self.nth(1)) == "using"
                && (is_identifier_like(self.nth_kind(2))
                    || matches!(self.nth_kind(2), TokenKind::LBracket | TokenKind::LBrace)));

        if decl_start {
            let kind_start = self.cur().range().start();
            let kind = self.variable_kind();
            let first = self.parse_for_head_declarator();
            match self.kind() {
                TokenKind::KwIn => {
                    self.bump();
                    let object = self.parse_expression(false);
                    let body = self.finish_for_body();
                    let range = TextRange::new(kind_start, first.range().end())
                        .expect("for-in head range is ordered");
                    let binding = ForBinding::Variable(VariableDeclaration {
                        range,
                        kind,
                        declarations: vec![first],
                    });
                    return self.node(
                        start,
                        Statement::ForIn(ForInStatement {
                            binding,
                            object: Box::new(object),
                            body: Box::new(body),
                        }),
                    );
                }
                TokenKind::KwOf => {
                    self.bump();
                    let iterable = self.parse_assignment_expression(false);
                    let body = self.finish_for_body();
                    let range = TextRange::new(kind_start, first.range().end())
                        .expect("for-of head range is ordered");
                    let binding = ForBinding::Variable(VariableDeclaration {
                        range,
                        kind,
                        declarations: vec![first],
                    });
                    let mode = if is_await {
                        ForOfMode::Async
                    } else {
                        ForOfMode::Sync
                    };
                    return self.node(
                        start,
                        Statement::ForOf(ForOfStatement {
                            mode,
                            binding,
                            iterable: Box::new(iterable),
                            body: Box::new(body),
                        }),
                    );
                }
                _ => {
                    // Classic head: finish this declarator's initializer and
                    // any further declarators.
                    let mut declarations = vec![self.finish_for_declarator(first)];
                    while self.eat(TokenKind::Comma).is_some() {
                        if self.is_cancelled() {
                            break;
                        }
                        declarations.push(self.parse_variable_declarator(false));
                    }
                    self.expect(TokenKind::Semicolon, "expected `;`");
                    let end = declarations
                        .last()
                        .map(|declarator| declarator.range().end())
                        .expect("classic for head has at least one declarator");
                    let range =
                        TextRange::new(kind_start, end).expect("classic for head range is ordered");
                    let initializer = Some(ForInitializer::Variable(VariableDeclaration {
                        range,
                        kind,
                        declarations,
                    }));
                    return self.finish_classic_for(start, initializer);
                }
            }
        }

        // Expression head.
        let expression = self.parse_expression(true);
        match self.kind() {
            TokenKind::KwIn => {
                self.bump();
                let target = self.expression_to_target(expression);
                let object = self.parse_expression(false);
                let body = self.finish_for_body();
                self.node(
                    start,
                    Statement::ForIn(ForInStatement {
                        binding: ForBinding::Target(target),
                        object: Box::new(object),
                        body: Box::new(body),
                    }),
                )
            }
            TokenKind::KwOf => {
                self.bump();
                let target = self.expression_to_target(expression);
                let iterable = self.parse_assignment_expression(false);
                let body = self.finish_for_body();
                let mode = if is_await {
                    ForOfMode::Async
                } else {
                    ForOfMode::Sync
                };
                self.node(
                    start,
                    Statement::ForOf(ForOfStatement {
                        mode,
                        binding: ForBinding::Target(target),
                        iterable: Box::new(iterable),
                        body: Box::new(body),
                    }),
                )
            }
            _ => {
                self.expect(TokenKind::Semicolon, "expected `;`");
                self.finish_classic_for(
                    start,
                    Some(ForInitializer::Expression(Box::new(expression))),
                )
            }
        }
    }

    /// Parses a for-head declarator up to (but excluding) any initializer, so
    /// the caller can decide between `in`/`of` and a classic head.
    fn parse_for_head_declarator(&mut self) -> VariableDeclaratorNode {
        let start = self.cur_start();
        let binding = self.parse_binding_pattern();
        let type_annotation = self.parse_optional_type_annotation();
        self.node(
            start,
            VariableDeclarator {
                binding,
                definite: false,
                type_annotation,
                initializer: None,
            },
        )
    }

    /// Attaches an `=` initializer to a for-head declarator in a classic head.
    fn finish_for_declarator(
        &mut self,
        declarator: VariableDeclaratorNode,
    ) -> VariableDeclaratorNode {
        if !self.at(TokenKind::Eq) {
            return declarator;
        }
        self.bump();
        let initializer = self.parse_assignment_expression(true);
        let start = declarator.range().start();
        let id = declarator.id();
        let mut data = declarator.into_data();
        data.initializer = Some(Box::new(initializer));
        Node::new(id, self.span_from(start), data)
    }

    fn finish_classic_for(&mut self, start: Utf16Pos, initializer: Option<ForInitializer>) -> Stmt {
        let test = if self.at(TokenKind::Semicolon) {
            None
        } else {
            Some(Box::new(self.parse_expression(false)))
        };
        self.expect(TokenKind::Semicolon, "expected `;`");
        let update = if self.at(TokenKind::RParen) {
            None
        } else {
            Some(Box::new(self.parse_expression(false)))
        };
        let body = self.finish_for_body();
        self.node(
            start,
            Statement::For(ForStatement {
                initializer,
                test,
                update,
                body: Box::new(body),
            }),
        )
    }

    fn finish_for_body(&mut self) -> Stmt {
        self.expect(TokenKind::RParen, "expected `)`");
        self.parse_statement()
    }

    fn parse_while_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        self.expect(TokenKind::LParen, "expected `(`");
        let test = self.parse_expression(false);
        self.expect(TokenKind::RParen, "expected `)`");
        let body = self.parse_statement();
        self.node(
            start,
            Statement::While(WhileStatement {
                test: Box::new(test),
                body: Box::new(body),
            }),
        )
    }

    fn parse_do_while_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        let body = self.parse_statement();
        self.expect(TokenKind::KwWhile, "expected `while`");
        self.expect(TokenKind::LParen, "expected `(`");
        let test = self.parse_expression(false);
        self.expect(TokenKind::RParen, "expected `)`");
        let _ = self.eat(TokenKind::Semicolon);
        self.node(
            start,
            Statement::DoWhile(DoWhileStatement {
                body: Box::new(body),
                test: Box::new(test),
            }),
        )
    }

    fn parse_try_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        let block = self.parse_block();
        let handler = if self.at(TokenKind::KwCatch) {
            let catch_start = self.cur_start();
            self.bump();
            let binding = if self.eat(TokenKind::LParen).is_some() {
                let pattern = self.parse_binding_pattern();
                // A catch-parameter annotation is type-only syntax the fixed
                // catch clause cannot retain; it is parsed and erased here.
                let _ = self.parse_optional_type_annotation();
                self.expect(TokenKind::RParen, "expected `)`");
                Some(pattern)
            } else {
                None
            };
            let body = self.parse_block();
            let clause: CatchClauseNode = self.node(catch_start, CatchClause { binding, body });
            Some(clause)
        } else {
            None
        };
        let finalizer = if self.eat(TokenKind::KwFinally).is_some() {
            Some(self.parse_block())
        } else {
            None
        };
        if handler.is_none() && finalizer.is_none() {
            self.error_here(EXPECTED_TOKEN, "expected `catch` or `finally`");
        }
        self.node(
            start,
            Statement::Try(TryStatement {
                block,
                handler,
                finalizer,
            }),
        )
    }

    fn parse_with_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        self.expect(TokenKind::LParen, "expected `(`");
        let object = self.parse_expression(false);
        self.expect(TokenKind::RParen, "expected `)`");
        let body = self.parse_statement();
        self.node(
            start,
            Statement::With(WithStatement {
                object: Box::new(object),
                body: Box::new(body),
            }),
        )
    }

    fn parse_return_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        let argument = if self.at(TokenKind::Semicolon)
            || self.at(TokenKind::RBrace)
            || self.at_eof()
            || self.has_newline_before()
        {
            None
        } else {
            Some(Box::new(self.parse_expression(false)))
        };
        self.expect_semicolon();
        self.node(start, Statement::Return(ReturnStatement { argument }))
    }

    fn parse_throw_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();
        let argument = if self.has_newline_before() {
            self.error_here(
                EXPECTED_EXPRESSION,
                "a `throw` argument must start on the same line",
            );
            self.missing_expr()
        } else {
            self.parse_expression(false)
        };
        self.expect_semicolon();
        self.node(
            start,
            Statement::Throw(ThrowStatement {
                argument: Box::new(argument),
            }),
        )
    }

    fn parse_jump_statement(&mut self, start: Utf16Pos, is_break: bool) -> Stmt {
        self.bump();
        let label = if is_identifier_like(self.kind()) && !self.has_newline_before() {
            let token = self.bump();
            Some(self.ident_from(token))
        } else {
            None
        };
        self.expect_semicolon();
        let jump = JumpStatement { label };
        let statement = if is_break {
            Statement::Break(jump)
        } else {
            Statement::Continue(jump)
        };
        self.node(start, statement)
    }

    fn parse_decorated_statement(&mut self, start: Utf16Pos) -> Stmt {
        let decorators = self.parse_decorators();
        let mut modifiers = DeclarationModifiers::default();
        if self.at(TokenKind::KwExport) {
            // `@dec export class` is legal ordering; re-enter export handling
            // with the decorators attached to the exported class.
            let export_start = self.cur_start();
            self.bump();
            let is_default = self.eat(TokenKind::KwDefault).is_some();
            if self.at(TokenKind::KwAbstract) {
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                modifiers.is_abstract = true;
            }
            if !self.at(TokenKind::KwClass) {
                self.error_here(EXPECTED_TOKEN, "decorators must precede a class");
            }
            let class = self.parse_class(decorators, modifiers, !is_default);
            let declaration = if is_default {
                ExportDeclaration::Default(ExportDefaultDeclaration {
                    value: ExportDefaultValue::Class(class),
                })
            } else {
                let class_stmt = self.node(export_start, Statement::Class(class));
                ExportDeclaration::Named(ExportNamedDeclaration::Declaration(Box::new(class_stmt)))
            };
            return self.node(start, Statement::Export(declaration));
        }
        if self.at(TokenKind::KwAbstract) && self.nth_kind(1) == TokenKind::KwClass {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            self.bump();
            modifiers.is_abstract = true;
        }
        if !self.at(TokenKind::KwClass) {
            self.error_here(EXPECTED_TOKEN, "decorators must precede a class");
            return self.missing_statement();
        }
        let class = self.parse_class(decorators, modifiers, true);
        self.node(start, Statement::Class(class))
    }

    fn parse_decorators(&mut self) -> Vec<DecoratorNode> {
        let mut decorators = Vec::new();
        while self.at(TokenKind::At) {
            if self.is_cancelled() {
                break;
            }
            let start = self.cur_start();
            self.bump();
            let expression = self.parse_lhs_expression(LhsContext::Decorator);
            let decorator: DecoratorNode = self.node(
                start,
                Decorator {
                    expression: Box::new(expression),
                },
            );
            decorators.push(decorator);
        }
        decorators
    }
}

// ---------------------------------------------------------------------------
// Classes, interfaces, enums, namespaces
// ---------------------------------------------------------------------------

impl Parser {
    fn parse_class(
        &mut self,
        decorators: Vec<DecoratorNode>,
        modifiers: DeclarationModifiers,
        require_name: bool,
    ) -> ClassDeclaration {
        self.expect(TokenKind::KwClass, "expected `class`");
        let name = if is_identifier_like(self.kind()) {
            let token = self.bump();
            Some(self.ident_from(token))
        } else {
            if require_name && !self.at(TokenKind::LBrace) && !self.at(TokenKind::KwExtends) {
                self.error_here(EXPECTED_IDENTIFIER, "expected a class name");
            }
            None
        };
        let type_parameters = self.parse_optional_type_parameters();

        let mut extends = None;
        let mut implements = Vec::new();
        loop {
            if self.is_cancelled() {
                break;
            }
            if self.at(TokenKind::KwExtends) && extends.is_none() {
                self.bump();
                let expression = self.parse_lhs_expression(LhsContext::Expression);
                let type_arguments = self.try_parse_type_arguments_in_heritage();
                extends = Some(ClassHeritage {
                    expression: Box::new(expression),
                    type_arguments,
                });
            } else if self.at(TokenKind::KwImplements) {
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                loop {
                    if self.is_cancelled() {
                        break;
                    }
                    implements.push(self.parse_type());
                    if self.eat(TokenKind::Comma).is_none() {
                        break;
                    }
                }
            } else {
                break;
            }
        }

        self.expect(TokenKind::LBrace, "expected `{`");
        let mut members = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let member = self.parse_class_member();
            members.push(member);
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a class body",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");

        ClassDeclaration {
            decorators,
            modifiers,
            name,
            type_parameters,
            extends,
            implements,
            members,
        }
    }

    /// Type arguments on a heritage clause (`extends Base<T>`). The `<` here
    /// is unambiguous, so no speculation is required.
    fn try_parse_type_arguments_in_heritage(&mut self) -> Option<TypeArgumentList> {
        if !self.at_less_like() {
            return None;
        }
        Some(self.parse_type_arguments())
    }

    fn parse_class_member(&mut self) -> ClassMemberNode {
        let start = self.cur_start();
        let decorators = self.parse_decorators();
        let mut modifiers = DeclarationModifiers::default();
        let mut is_async = false;
        let mut property_modifier = PropertyModifier::None;
        let mut is_accessor = false;
        let mut typescript_modifier: Option<TextRange> = None;

        loop {
            if self.is_cancelled() {
                break;
            }
            let kind = self.kind();
            if !self.modifier_is_followed_by_member(1) {
                break;
            }
            match kind {
                TokenKind::KwPublic => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.accessibility = Some(Accessibility::Public);
                }
                TokenKind::KwProtected => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.accessibility = Some(Accessibility::Protected);
                }
                TokenKind::KwPrivate => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.accessibility = Some(Accessibility::Private);
                }
                TokenKind::KwStatic => modifiers.is_static = true,
                TokenKind::KwAbstract => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.is_abstract = true;
                }
                TokenKind::KwOverride => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.is_override = true;
                }
                TokenKind::KwReadonly => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.is_readonly = true;
                }
                TokenKind::KwDeclare => {
                    typescript_modifier = Some(self.cur().range());
                    modifiers.is_declare = true;
                }
                TokenKind::KwExport if !self.has_newline_before_nth(1) => {
                    let range = self.cur().range();
                    self.error_at(
                        EXPORT_MODIFIER_ON_CLASS_ELEMENT,
                        range,
                        "'export' modifier cannot appear on class elements.",
                    );
                }
                TokenKind::KwAsync if !self.has_newline_before_nth(1) => is_async = true,
                TokenKind::KwAccessor if !self.has_newline_before_nth(1) => is_accessor = true,
                TokenKind::KwGet => property_modifier = PropertyModifier::Get,
                TokenKind::KwSet => property_modifier = PropertyModifier::Set,
                _ => break,
            }
            self.bump();
            if matches!(kind, TokenKind::KwGet | TokenKind::KwSet) {
                break;
            }
        }

        if let Some(range) = typescript_modifier {
            self.note_typescript_syntax(range);
        }

        // `static { ... }` initializer block.
        if modifiers.is_static
            && self.at(TokenKind::LBrace)
            && property_modifier == PropertyModifier::None
            && !is_async
        {
            // The block's own keyword context: neither the enclosing
            // function's async nor its generator state applies, so both
            // await and yield are context-illegal inside.
            let context = KeywordContext {
                in_function: true,
                await_reserved: false,
                yield_reserved: false,
            };
            let block = self.with_keyword_context(context, Self::parse_block);
            return self.node(start, ClassMember::StaticBlock(block));
        }

        // Index signature `[key: string]: T`.
        if self.at(TokenKind::LBracket) && self.at_index_signature() {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            let parameters = self.parse_parameter_list();
            let type_annotation = match self.parse_optional_type_annotation() {
                Some(annotation) => annotation,
                None => {
                    self.error_here(EXPECTED_TOKEN, "an index signature requires a type");
                    self.missing_type_annotation()
                }
            };
            self.expect_semicolon();
            return self.node(
                start,
                ClassMember::IndexSignature(IndexSignature {
                    readonly: modifiers.is_readonly,
                    parameters,
                    type_annotation,
                }),
            );
        }

        let is_generator = self.eat(TokenKind::Star).is_some();
        let name = self.parse_property_name();
        let optional = self.eat(TokenKind::Question).is_some();
        let definite = if self.at(TokenKind::Bang) && !self.has_newline_before() {
            self.bump();
            true
        } else {
            false
        };

        // Constructor.
        if !is_accessor
            && property_modifier == PropertyModifier::None
            && self.is_constructor_name(&name)
            && self.at(TokenKind::LParen)
        {
            let keyword_context = KeywordContext {
                in_function: true,
                await_reserved: false,
                yield_reserved: false,
            };
            let parameters =
                self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
            let return_type = self.parse_optional_type_annotation();
            if self.at(TokenKind::LBrace) {
                let body = self.with_keyword_context(keyword_context, Self::parse_block);
                let _ = return_type;
                return self.node(
                    start,
                    ClassMember::Constructor(ConstructorDeclaration {
                        decorators,
                        modifiers,
                        parameters,
                        body,
                    }),
                );
            }
            // A bodyless constructor overload signature is retained as a
            // method so no body is fabricated.
            self.expect_semicolon();
            return self.node(
                start,
                ClassMember::Method(MethodDeclaration {
                    modifiers,
                    modifier: PropertyModifier::None,
                    name,
                    optional,
                    function: FunctionLike {
                        decorators,
                        name: None,
                        is_async: false,
                        is_generator: false,
                        type_parameters: None,
                        parameters,
                        return_type,
                        body: None,
                    },
                }),
            );
        }

        // Method, getter, or setter.
        if self.at(TokenKind::LParen) || self.at_less_like() || is_generator {
            let keyword_context = KeywordContext {
                in_function: true,
                await_reserved: is_async,
                yield_reserved: is_generator,
            };
            let type_parameters = self.parse_optional_type_parameters();
            let parameters =
                self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
            let return_type = self.parse_optional_type_annotation();
            let body = if self.at(TokenKind::LBrace) {
                Some(FunctionBody::Block(
                    self.with_keyword_context(keyword_context, Self::parse_block),
                ))
            } else {
                self.expect_semicolon();
                None
            };
            return self.node(
                start,
                ClassMember::Method(MethodDeclaration {
                    modifiers,
                    modifier: property_modifier,
                    name,
                    optional,
                    function: FunctionLike {
                        decorators,
                        name: None,
                        is_async,
                        is_generator,
                        type_parameters,
                        parameters,
                        return_type,
                        body,
                    },
                }),
            );
        }

        // Property or auto-accessor.
        let type_annotation = self.parse_optional_type_annotation();
        let initializer = if self.eat(TokenKind::Eq).is_some() {
            Some(Box::new(self.parse_assignment_expression(false)))
        } else {
            None
        };
        self.expect_semicolon();
        if is_accessor {
            return self.node(
                start,
                ClassMember::AutoAccessor(AutoAccessor {
                    decorators,
                    modifiers,
                    name,
                    type_annotation,
                    initializer,
                }),
            );
        }
        self.node(
            start,
            ClassMember::Property(ClassProperty {
                decorators,
                modifiers,
                name,
                optional,
                definite,
                type_annotation,
                initializer,
            }),
        )
    }

    /// A keyword is a member modifier only when a member can still start after
    /// it; otherwise it is the member's own name.
    fn modifier_is_followed_by_member(&self, offset: usize) -> bool {
        if !matches!(
            self.kind(),
            TokenKind::KwPublic
                | TokenKind::KwProtected
                | TokenKind::KwPrivate
                | TokenKind::KwStatic
                | TokenKind::KwAbstract
                | TokenKind::KwOverride
                | TokenKind::KwReadonly
                | TokenKind::KwDeclare
                | TokenKind::KwAsync
                | TokenKind::KwAccessor
                | TokenKind::KwGet
                | TokenKind::KwSet
                | TokenKind::KwExport
        ) {
            return false;
        }
        let next = self.nth_kind(offset);
        is_any_word(next)
            || matches!(
                next,
                TokenKind::LBracket
                    | TokenKind::StringLiteral
                    | TokenKind::NumericLiteral
                    | TokenKind::PrivateIdentifier
                    | TokenKind::Star
            )
            || (self.at(TokenKind::KwStatic) && next == TokenKind::LBrace)
    }

    /// Returns whether `name` is exactly the `constructor` identifier, so a
    /// method named `constructors` is not misread as a constructor.
    fn is_constructor_name(&self, name: &PropertyName) -> bool {
        let PropertyName::Identifier(node) = name else {
            return false;
        };
        self.lexeme(*node.data().token()) == "constructor"
    }

    /// Distinguishes `[key: string]: T` from a computed member name.
    fn at_index_signature(&self) -> bool {
        is_identifier_like(self.nth_kind(1)) && self.nth_kind(2) == TokenKind::Colon
    }

    fn missing_type_annotation(&mut self) -> TypeAnnotationNode {
        let start = self.cur_start();
        let type_node = self.missing_type();
        self.node_at(
            empty_range(start),
            TypeAnnotation {
                type_node: Box::new(type_node),
            },
        )
    }

    fn parse_interface(&mut self) -> InterfaceDeclaration {
        let keyword_range = self.cur().range();
        self.note_typescript_syntax(keyword_range);
        self.bump();
        let name = self.expect_identifier("expected an interface name");
        let type_parameters = self.parse_optional_type_parameters();
        let mut extends = Vec::new();
        if self.eat(TokenKind::KwExtends).is_some() {
            loop {
                if self.is_cancelled() {
                    break;
                }
                let entity = self.parse_entity_name();
                let type_arguments = if self.at_less_like() {
                    Some(self.parse_type_arguments())
                } else {
                    None
                };
                extends.push(TypeReference {
                    name: entity,
                    type_arguments,
                });
                if self.eat(TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        let members = self.parse_type_members();
        InterfaceDeclaration {
            name,
            type_parameters,
            extends,
            members,
        }
    }

    fn parse_interface_declaration(&mut self, start: Utf16Pos) -> Stmt {
        let interface = self.parse_interface();
        self.node(start, Statement::Interface(interface))
    }

    fn parse_type_alias_declaration(&mut self, start: Utf16Pos) -> Stmt {
        let keyword_range = self.cur().range();
        self.note_typescript_syntax(keyword_range);
        self.bump();
        let name = self.expect_identifier("expected a type alias name");
        let type_parameters = self.parse_optional_type_parameters();
        self.expect(TokenKind::Eq, "expected `=`");
        let type_node = self.parse_type();
        self.expect_semicolon();
        self.node(
            start,
            Statement::TypeAlias(TypeAliasDeclaration {
                name,
                type_parameters,
                type_node: Box::new(type_node),
            }),
        )
    }

    fn parse_enum_declaration(&mut self, start: Utf16Pos, is_const: bool) -> Stmt {
        let keyword_range = self.cur().range();
        self.note_typescript_syntax(keyword_range);
        self.expect(TokenKind::KwEnum, "expected `enum`");
        let name = self.expect_identifier("expected an enum name");
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut members = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let member_start = self.cur_start();
            let name = self.parse_property_name();
            let initializer = if self.eat(TokenKind::Eq).is_some() {
                Some(Box::new(self.parse_assignment_expression(false)))
            } else {
                None
            };
            let member: EnumMemberNode = self.node(member_start, EnumMember { name, initializer });
            members.push(member);
            if self.eat(TokenKind::Comma).is_none() && !self.at(TokenKind::RBrace) {
                self.error_here(EXPECTED_TOKEN, "expected `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an enum body",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(
            start,
            Statement::Enum(EnumDeclaration {
                is_const,
                name,
                members,
            }),
        )
    }

    /// Parses the body of a namespace / ambient module, desugaring a leading
    /// dotted tail into a nested single-name declaration.
    fn parse_namespace_body(&mut self, keyword: NamespaceKeyword) -> BlockNode {
        if self.at(TokenKind::Dot) {
            let inner_start = self.cur_start();
            if !self.enter() {
                // Depth limit reached. Consume the dot so the source advances,
                // then return a block with a missing statement to stop the
                // dotted recursion without exhausting the native stack.
                self.bump();
                let missing = self.node_at(
                    empty_range(inner_start),
                    Statement::Missing(MissingNode::new(NodeKind::MissingStatement)),
                );
                return self.node(
                    inner_start,
                    Block {
                        statements: vec![missing],
                    },
                );
            }
            self.bump();
            let inner = self.parse_namespace_tail(inner_start, keyword);
            self.leave();
            let statements = vec![inner];
            self.node(inner_start, Block { statements })
        } else {
            self.parse_block()
        }
    }

    /// Returns whether `global` / string-module names are ambient here.
    fn name_is_ambient(&self) -> bool {
        !matches!(self.ambient, AmbientContext::None)
    }

    /// Parses with the given ambient context, restoring the previous one.
    fn with_ambient<T>(
        &mut self,
        context: AmbientContext,
        parse: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let saved = self.ambient;
        self.ambient = context;
        let result = parse(self);
        self.ambient = saved;
        result
    }

    /// Parses a namespace/module/global body in a non-ambient name context, so
    /// nested `global` / string-module forms are not treated as ambient.
    fn parse_outside_declare<T>(&mut self, parse: impl FnOnce(&mut Self) -> T) -> T {
        self.with_ambient(AmbientContext::None, parse)
    }

    fn identifier_namespace_name(
        &mut self,
        name: IdentifierNode,
        keyword: NamespaceKeyword,
    ) -> NamespaceName {
        NamespaceName::Identifier { name, keyword }
    }

    /// Parses `namespace A.B.C { ... }`, desugaring the dotted form into
    /// nested single-name declarations because the node carries one name.
    fn parse_namespace_declaration(&mut self, start: Utf16Pos) -> Stmt {
        let keyword_range = self.cur().range();
        self.note_typescript_syntax(keyword_range);
        self.bump();
        let name_node = self.expect_identifier("expected a namespace name");
        let name = self.identifier_namespace_name(name_node, NamespaceKeyword::Namespace);
        let body = self
            .parse_outside_declare(|this| this.parse_namespace_body(NamespaceKeyword::Namespace));
        self.node(
            start,
            Statement::Namespace(NamespaceDeclaration { name, body }),
        )
    }

    fn parse_namespace_tail(&mut self, start: Utf16Pos, keyword: NamespaceKeyword) -> Stmt {
        let name_node = self.expect_identifier("expected a namespace name");
        let name = self.identifier_namespace_name(name_node, keyword);
        let body = self.parse_outside_declare(|this| this.parse_namespace_body(keyword));
        self.node(
            start,
            Statement::Namespace(NamespaceDeclaration { name, body }),
        )
    }

    /// Parses ambient `global { ... }` and `module Name { ... }` forms, including
    /// string-named ambient modules under `declare`.
    fn parse_contextual_namespace(&mut self, start: Utf16Pos) -> Stmt {
        let keyword = self.bump();
        let is_global = self.lexeme(keyword) == "global";
        let ambient = self.name_is_ambient();
        let name = if is_global && ambient {
            NamespaceName::Global {
                range: keyword.range(),
            }
        } else if is_global {
            let name = self.ident_from(keyword);
            self.identifier_namespace_name(name, NamespaceKeyword::Namespace)
        } else if is_identifier_like(self.kind()) {
            let name = self.expect_identifier("expected a module name");
            self.identifier_namespace_name(name, NamespaceKeyword::Module)
        } else if self.at(TokenKind::StringLiteral) {
            let lit = self.parse_string_literal();
            if !ambient {
                self.error_at(
                    EXPECTED_IDENTIFIER,
                    lit.range(),
                    "a string-named module is only allowed in an ambient declaration",
                );
            }
            NamespaceName::StringLiteral(lit)
        } else {
            self.error_here(EXPECTED_IDENTIFIER, "expected a module name");
            let name = self.missing_ident();
            self.identifier_namespace_name(name, NamespaceKeyword::Module)
        };

        // Only the direct body of a string-named ambient module keeps ambient
        // name recognition, and only when that module was itself the direct
        // `declare` target. A nested string module's body is not ambient, so
        // `declare module "a" { module "b" { module "c" {} } }` rejects the
        // inner string module exactly like TypeScript (TS2435).
        let body_context = match (&name, self.ambient) {
            (NamespaceName::StringLiteral(_), AmbientContext::DeclareTarget) => {
                AmbientContext::ModuleBody
            }
            _ => AmbientContext::None,
        };
        let body = self.with_ambient(body_context, |this| match &name {
            NamespaceName::Identifier { keyword, .. } => this.parse_namespace_body(*keyword),
            NamespaceName::StringLiteral(_) | NamespaceName::Global { .. } => this.parse_block(),
        });
        self.node(
            start,
            Statement::Namespace(NamespaceDeclaration { name, body }),
        )
    }
}

// ---------------------------------------------------------------------------
// Modules
// ---------------------------------------------------------------------------

impl Parser {
    fn parse_import_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();

        // `import "module";`
        if self.at(TokenKind::StringLiteral) {
            let source = self.parse_string_literal();
            let attributes = self.parse_optional_import_attributes();
            self.expect_semicolon();
            return self.node(
                start,
                Statement::Import(ImportDeclaration {
                    type_only: false,
                    clause: None,
                    source,
                    attributes,
                }),
            );
        }

        // `import type ...`, unless `type` is itself the imported binding.
        let type_only = self.at(TokenKind::KwType) && self.type_keyword_is_modifier();
        if type_only {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            self.bump();
        }

        // `import x = require("m")` / `import x = A.B`.
        if is_identifier_like(self.kind()) && self.nth_kind(1) == TokenKind::Eq {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            let local = self.expect_identifier("expected an import name");
            self.bump();
            let reference = self.parse_external_module_reference();
            self.expect_semicolon();
            return self.node(
                start,
                Statement::ImportEquals(ImportEqualsDeclaration {
                    is_type_only: type_only,
                    local,
                    reference,
                }),
            );
        }

        let clause = self.parse_import_clause();
        self.expect(TokenKind::KwFrom, "expected `from`");
        let source = self.parse_string_literal();
        let attributes = self.parse_optional_import_attributes();
        self.expect_semicolon();
        self.node(
            start,
            Statement::Import(ImportDeclaration {
                type_only,
                clause: Some(clause),
                source,
                attributes,
            }),
        )
    }

    /// In `import type X from "m"`, `type` is a modifier. In
    /// `import type from "m"` and `import type, {x} from "m"`, it is the
    /// default binding's name.
    fn type_keyword_is_modifier(&self) -> bool {
        !matches!(
            self.nth_kind(1),
            TokenKind::KwFrom | TokenKind::Comma | TokenKind::Eq
        )
    }

    fn parse_external_module_reference(&mut self) -> ExternalModuleReference {
        if is_identifier_like(self.kind())
            && self.cur_lexeme() == "require"
            && self.nth_kind(1) == TokenKind::LParen
        {
            self.bump();
            self.bump();
            let source = self.parse_string_literal();
            self.expect(TokenKind::RParen, "expected `)`");
            return ExternalModuleReference::Require(source);
        }
        if is_identifier_like(self.kind()) {
            return ExternalModuleReference::Qualified(self.parse_entity_name());
        }
        self.error_here(EXPECTED_IDENTIFIER, "expected a module reference");
        ExternalModuleReference::Missing(MissingNode::new(NodeKind::Identifier))
    }

    fn parse_import_clause(&mut self) -> ImportClause {
        // `* as ns`
        if self.at(TokenKind::Star) {
            let binding = self.parse_namespace_import();
            return ImportClause {
                default: None,
                binding: Some(binding),
            };
        }
        // `{ ... }`
        if self.at(TokenKind::LBrace) {
            let specifiers = self.parse_named_imports();
            return ImportClause {
                default: None,
                binding: Some(ImportBinding::Named(specifiers)),
            };
        }
        // `def`, `def, { ... }`, `def, * as ns`
        let default = if is_identifier_like(self.kind()) {
            let token = self.bump();
            Some(self.ident_from(token))
        } else {
            self.error_here(EXPECTED_IDENTIFIER, "expected an import binding");
            None
        };
        let mut binding = None;
        if self.eat(TokenKind::Comma).is_some() {
            if self.at(TokenKind::Star) {
                binding = Some(self.parse_namespace_import());
            } else if self.at(TokenKind::LBrace) {
                binding = Some(ImportBinding::Named(self.parse_named_imports()));
            } else {
                self.error_here(EXPECTED_TOKEN, "expected `{` or `*` after `,`");
            }
        }
        ImportClause { default, binding }
    }

    fn parse_namespace_import(&mut self) -> ImportBinding {
        self.bump();
        self.expect(TokenKind::KwAs, "expected `as`");
        let name = self.expect_identifier("expected a namespace import name");
        ImportBinding::Namespace(name)
    }

    fn parse_named_imports(&mut self) -> Vec<ImportSpecifierNode> {
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut specifiers = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let start = self.cur_start();
            let mode = if self.at(TokenKind::KwType) && self.specifier_type_is_modifier() {
                self.bump();
                ImportSpecifierMode::TypeOnly
            } else {
                ImportSpecifierMode::Value
            };
            let imported = self.parse_module_export_name();
            let local = if self.eat(TokenKind::KwAs).is_some() {
                self.expect_identifier("expected a local import name")
            } else {
                match &imported {
                    ModuleExportName::Identifier(name) => {
                        let token = *name.data().token();
                        self.ident_from(token)
                    }
                    ModuleExportName::String(_) => {
                        self.error_here(
                            EXPECTED_TOKEN,
                            "a string import name requires `as` and a local binding",
                        );
                        self.missing_ident()
                    }
                    ModuleExportName::Missing(_) => self.missing_ident(),
                }
            };
            let specifier: ImportSpecifierNode = self.node(
                start,
                ImportSpecifier {
                    mode,
                    imported,
                    local,
                },
            );
            specifiers.push(specifier);
            if self.eat(TokenKind::Comma).is_none() && !self.at(TokenKind::RBrace) {
                self.error_here(EXPECTED_TOKEN, "expected `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an import list",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        specifiers
    }

    /// In `{ type as x }` the first `type` is the imported name; in
    /// `{ type x }` and `{ type x as y }` it is the type-only modifier.
    fn specifier_type_is_modifier(&self) -> bool {
        match self.nth_kind(1) {
            TokenKind::KwAs => {
                matches!(self.nth_kind(2), TokenKind::KwAs)
                    || is_identifier_like(self.nth_kind(2)) && self.nth_kind(3) == TokenKind::KwAs
            }
            TokenKind::Comma | TokenKind::RBrace => false,
            kind => is_identifier_like(kind) || kind == TokenKind::StringLiteral,
        }
    }

    fn parse_module_export_name(&mut self) -> ModuleExportName {
        if self.at(TokenKind::StringLiteral) {
            return ModuleExportName::String(self.parse_string_literal());
        }
        if is_any_word(self.kind()) {
            let token = self.bump();
            return ModuleExportName::Identifier(self.identifier_name_from(token));
        }
        self.error_here(EXPECTED_IDENTIFIER, "expected a module export name");
        ModuleExportName::Missing(MissingNode::new(NodeKind::Identifier))
    }

    fn parse_optional_import_attributes(&mut self) -> Option<ImportAttributes> {
        let is_with = self.at(TokenKind::KwWith) && self.nth_kind(1) == TokenKind::LBrace;
        let is_assert = is_identifier_like(self.kind())
            && self.cur_lexeme() == "assert"
            && self.nth_kind(1) == TokenKind::LBrace;
        if !is_with && !is_assert {
            return None;
        }
        self.bump();
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut entries = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let name = self.parse_module_export_name();
            self.expect(TokenKind::Colon, "expected `:`");
            let value = self.parse_string_literal();
            entries.push(ImportAttribute { name, value });
            if self.eat(TokenKind::Comma).is_none() && !self.at(TokenKind::RBrace) {
                self.error_here(EXPECTED_TOKEN, "expected `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside import attributes",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        Some(ImportAttributes { entries })
    }

    fn parse_string_literal(&mut self) -> StringLiteralNode {
        if self.at(TokenKind::StringLiteral) {
            let token = self.bump();
            let range = token.range();
            return self.node_at(range, StringLiteral::new(token));
        }
        self.error_here(EXPECTED_TOKEN, "expected a string literal");
        let token = self.missing_token(TokenKind::StringLiteral);
        let range = token.range();
        self.node_at(range, StringLiteral::new(token))
    }

    fn parse_export_statement(&mut self, start: Utf16Pos) -> Stmt {
        self.bump();

        // `export * from "m"` / `export * as ns from "m"`
        if self.at(TokenKind::Star) {
            self.bump();
            let exported = if self.eat(TokenKind::KwAs).is_some() {
                Some(self.parse_module_export_name())
            } else {
                None
            };
            self.expect(TokenKind::KwFrom, "expected `from`");
            let source = self.parse_string_literal();
            let attributes = self.parse_optional_import_attributes();
            self.expect_semicolon();
            return self.node(
                start,
                Statement::Export(ExportDeclaration::All(ExportAllDeclaration {
                    type_only: false,
                    exported,
                    source,
                    attributes,
                })),
            );
        }

        // `export { ... }` / `export { ... } from "m"`
        if self.at(TokenKind::LBrace) {
            return self.parse_export_specifiers(start, false);
        }

        // `export type ...`
        if self.at(TokenKind::KwType) {
            let range = self.cur().range();
            match self.nth_kind(1) {
                TokenKind::LBrace => {
                    self.note_typescript_syntax(range);
                    self.bump();
                    return self.parse_export_specifiers(start, true);
                }
                TokenKind::Star => {
                    self.note_typescript_syntax(range);
                    self.bump();
                    self.bump();
                    let exported = if self.eat(TokenKind::KwAs).is_some() {
                        Some(self.parse_module_export_name())
                    } else {
                        None
                    };
                    self.expect(TokenKind::KwFrom, "expected `from`");
                    let source = self.parse_string_literal();
                    let attributes = self.parse_optional_import_attributes();
                    self.expect_semicolon();
                    return self.node(
                        start,
                        Statement::Export(ExportDeclaration::All(ExportAllDeclaration {
                            type_only: true,
                            exported,
                            source,
                            attributes,
                        })),
                    );
                }
                _ => {}
            }
        }

        // `export = expr`
        if self.at(TokenKind::Eq) {
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            self.bump();
            let expression = self.parse_assignment_expression(false);
            self.expect_semicolon();
            return self.node(
                start,
                Statement::Export(ExportDeclaration::Assignment(Box::new(expression))),
            );
        }

        // `export default ...`
        if self.eat(TokenKind::KwDefault).is_some() {
            let value = self.parse_export_default_value();
            return self.node(
                start,
                Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                    value,
                })),
            );
        }

        // `export <declaration>`
        let declaration_start = self.cur_start();
        if self.can_start_exported_declaration() {
            let declaration = self.parse_statement();
            let _ = declaration_start;
            return self.node(
                start,
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(Box::new(declaration)),
                )),
            );
        }

        self.error_here(UNEXPECTED_TOKEN, "expected an export declaration");
        let specifiers = Vec::new();
        self.node(
            start,
            Statement::Export(ExportDeclaration::Named(
                ExportNamedDeclaration::Specifiers {
                    type_only: false,
                    specifiers,
                    source: None,
                    attributes: None,
                },
            )),
        )
    }

    fn can_start_exported_declaration(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::KwVar
                | TokenKind::KwLet
                | TokenKind::KwConst
                | TokenKind::KwFunction
                | TokenKind::KwClass
                | TokenKind::KwAbstract
                | TokenKind::KwAsync
                | TokenKind::KwEnum
                | TokenKind::KwInterface
                | TokenKind::KwType
                | TokenKind::KwNamespace
                | TokenKind::KwDeclare
                | TokenKind::KwImport
                | TokenKind::At
        ) || (self.at(TokenKind::Identifier) && self.cur_lexeme() == "using")
    }

    fn parse_export_default_value(&mut self) -> ExportDefaultValue {
        match self.kind() {
            TokenKind::KwFunction => {
                let function = self.parse_function_like(Vec::new(), false, false);
                ExportDefaultValue::Function(function)
            }
            TokenKind::KwAsync if self.nth_kind(1) == TokenKind::KwFunction => {
                self.bump();
                let function = self.parse_function_like(Vec::new(), true, false);
                ExportDefaultValue::Function(function)
            }
            TokenKind::KwClass => {
                let class = self.parse_class(Vec::new(), DeclarationModifiers::default(), false);
                ExportDefaultValue::Class(class)
            }
            TokenKind::KwAbstract if self.nth_kind(1) == TokenKind::KwClass => {
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                let modifiers = DeclarationModifiers {
                    is_abstract: true,
                    ..DeclarationModifiers::default()
                };
                let class = self.parse_class(Vec::new(), modifiers, false);
                ExportDefaultValue::Class(class)
            }
            TokenKind::KwInterface => ExportDefaultValue::Interface(self.parse_interface()),
            TokenKind::At => {
                let decorators = self.parse_decorators();
                let modifiers =
                    if self.at(TokenKind::KwAbstract) && self.nth_kind(1) == TokenKind::KwClass {
                        let range = self.cur().range();
                        self.note_typescript_syntax(range);
                        self.bump();
                        DeclarationModifiers {
                            is_abstract: true,
                            ..DeclarationModifiers::default()
                        }
                    } else {
                        DeclarationModifiers::default()
                    };
                if self.at(TokenKind::KwClass) {
                    let class = self.parse_class(decorators, modifiers, false);
                    ExportDefaultValue::Class(class)
                } else {
                    self.error_here(EXPECTED_TOKEN, "decorators must precede a class");
                    ExportDefaultValue::Missing(MissingNode::new(NodeKind::ClassDeclaration))
                }
            }
            _ => {
                let before = self.cursor;
                let expression = self.parse_assignment_expression(false);
                if self.cursor == before {
                    return ExportDefaultValue::Missing(MissingNode::new(
                        NodeKind::MissingExpression,
                    ));
                }
                self.expect_semicolon();
                ExportDefaultValue::Expression(Box::new(expression))
            }
        }
    }

    fn parse_export_specifiers(&mut self, start: Utf16Pos, type_only: bool) -> Stmt {
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut specifiers = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let specifier_start = self.cur_start();
            let mode = if self.at(TokenKind::KwType) && self.specifier_type_is_modifier() {
                self.bump();
                ExportSpecifierMode::TypeOnly
            } else {
                ExportSpecifierMode::Value
            };
            let local = self.parse_module_export_name();
            let exported = if self.eat(TokenKind::KwAs).is_some() {
                self.parse_module_export_name()
            } else {
                local.clone()
            };
            let specifier: ExportSpecifierNode = self.node(
                specifier_start,
                ExportSpecifier {
                    mode,
                    local,
                    exported,
                },
            );
            specifiers.push(specifier);
            if self.eat(TokenKind::Comma).is_none() && !self.at(TokenKind::RBrace) {
                self.error_here(EXPECTED_TOKEN, "expected `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an export list",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        let (source, attributes) = if self.eat(TokenKind::KwFrom).is_some() {
            let source = self.parse_string_literal();
            let attributes = self.parse_optional_import_attributes();
            (Some(source), attributes)
        } else {
            (None, None)
        };
        if source.is_none() {
            for specifier in &specifiers {
                if let ModuleExportName::Identifier(local) = &specifier.data().local {
                    self.reject_reserved_identifier(*local.data().token());
                }
            }
        }
        self.expect_semicolon();
        self.node(
            start,
            Statement::Export(ExportDeclaration::Named(
                ExportNamedDeclaration::Specifiers {
                    type_only,
                    specifiers,
                    source,
                    attributes,
                },
            )),
        )
    }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

/// Binary operator binding power. Higher binds tighter; assignment and the
/// comma operator are handled outside this table.
fn binary_precedence(kind: TokenKind) -> Option<(BinaryOrLogical, u8)> {
    use BinaryOrLogical::{Binary, Logical};
    let entry = match kind {
        TokenKind::PipePipe => (Logical(LogicalOperator::Or), 4),
        TokenKind::QuestionQuestion => (Logical(LogicalOperator::Nullish), 4),
        TokenKind::AmpAmp => (Logical(LogicalOperator::And), 5),
        TokenKind::Pipe => (Binary(BinaryOperator::BitOr), 6),
        TokenKind::Caret => (Binary(BinaryOperator::BitXor), 7),
        TokenKind::Amp => (Binary(BinaryOperator::BitAnd), 8),
        TokenKind::EqEq => (Binary(BinaryOperator::Equal), 9),
        TokenKind::BangEq => (Binary(BinaryOperator::NotEqual), 9),
        TokenKind::EqEqEq => (Binary(BinaryOperator::StrictEqual), 9),
        TokenKind::BangEqEq => (Binary(BinaryOperator::StrictNotEqual), 9),
        TokenKind::LessThan => (Binary(BinaryOperator::LessThan), 10),
        TokenKind::GreaterThan => (Binary(BinaryOperator::GreaterThan), 10),
        TokenKind::LessThanEq => (Binary(BinaryOperator::LessThanOrEqual), 10),
        TokenKind::GreaterThanEq => (Binary(BinaryOperator::GreaterThanOrEqual), 10),
        TokenKind::KwInstanceof => (Binary(BinaryOperator::Instanceof), 10),
        TokenKind::KwIn => (Binary(BinaryOperator::In), 10),
        TokenKind::LessLess => (Binary(BinaryOperator::LeftShift), 11),
        TokenKind::GreaterGreater => (Binary(BinaryOperator::SignedRightShift), 11),
        TokenKind::GreaterGreaterGreater => (Binary(BinaryOperator::UnsignedRightShift), 11),
        TokenKind::Plus => (Binary(BinaryOperator::Add), 12),
        TokenKind::Minus => (Binary(BinaryOperator::Subtract), 12),
        TokenKind::Star => (Binary(BinaryOperator::Multiply), 13),
        TokenKind::Slash => (Binary(BinaryOperator::Divide), 13),
        TokenKind::Percent => (Binary(BinaryOperator::Remainder), 13),
        TokenKind::StarStar => (Binary(BinaryOperator::Exponentiate), 14),
        _ => return None,
    };
    Some(entry)
}

#[derive(Clone, Copy)]
enum BinaryOrLogical {
    Binary(BinaryOperator),
    Logical(LogicalOperator),
}

#[derive(Clone, Copy)]
enum LhsContext {
    Expression,
    Decorator,
}

impl LhsContext {
    fn allows_newline_computed_member(self) -> bool {
        matches!(self, Self::Expression)
    }
}

fn assignment_operator(kind: TokenKind) -> Option<AssignmentOperator> {
    let op = match kind {
        TokenKind::Eq => AssignmentOperator::Assign,
        TokenKind::PlusEq => AssignmentOperator::AddAssign,
        TokenKind::MinusEq => AssignmentOperator::SubtractAssign,
        TokenKind::StarEq => AssignmentOperator::MultiplyAssign,
        TokenKind::SlashEq => AssignmentOperator::DivideAssign,
        TokenKind::PercentEq => AssignmentOperator::RemainderAssign,
        TokenKind::StarStarEq => AssignmentOperator::ExponentiateAssign,
        TokenKind::LessLessEq => AssignmentOperator::LeftShiftAssign,
        TokenKind::GreaterGreaterEq => AssignmentOperator::SignedRightShiftAssign,
        TokenKind::GreaterGreaterGreaterEq => AssignmentOperator::UnsignedRightShiftAssign,
        TokenKind::AmpEq => AssignmentOperator::BitAndAssign,
        TokenKind::CaretEq => AssignmentOperator::BitXorAssign,
        TokenKind::PipeEq => AssignmentOperator::BitOrAssign,
        TokenKind::AmpAmpEq => AssignmentOperator::LogicalAndAssign,
        TokenKind::PipePipeEq => AssignmentOperator::LogicalOrAssign,
        TokenKind::QuestionQuestionEq => AssignmentOperator::NullishAssign,
        _ => return None,
    };
    Some(op)
}

impl Parser {
    /// Parses a full expression, folding a top-level comma into a sequence.
    fn parse_expression(&mut self, no_in: bool) -> Expr {
        let start = self.cur_start();
        let first = self.parse_assignment_expression(no_in);
        if !self.at(TokenKind::Comma) {
            return first;
        }
        let mut expressions = vec![first];
        while self.eat(TokenKind::Comma).is_some() {
            if self.is_cancelled() {
                break;
            }
            expressions.push(self.parse_assignment_expression(no_in));
        }
        self.node(
            start,
            Expression::Sequence(SequenceExpression { expressions }),
        )
    }

    fn parse_assignment_expression(&mut self, no_in: bool) -> Expr {
        if !self.enter() {
            return self.missing_expr();
        }
        let expr = self.parse_assignment_inner(no_in);
        self.leave();
        expr
    }

    fn parse_assignment_inner(&mut self, no_in: bool) -> Expr {
        let start = self.cur_start();

        if self.at(TokenKind::KwYield) {
            return self.parse_yield_expression(start, no_in);
        }

        // Arrow fast paths and speculation.
        if let Some(arrow) = self.try_parse_arrow_function(no_in) {
            return arrow;
        }

        let left = self.parse_conditional_expression(no_in);
        if let Some(op) = assignment_operator(self.kind()) {
            let simple = op == AssignmentOperator::Assign;
            let target = self.expression_to_target_for_assignment(left, simple);
            self.bump();
            let right = self.parse_assignment_expression(no_in);
            return self.node(
                start,
                Expression::Assignment(AssignmentExpression {
                    operator: op,
                    left: target,
                    right: Box::new(right),
                }),
            );
        }
        left
    }

    fn parse_yield_expression(&mut self, start: Utf16Pos, no_in: bool) -> Expr {
        let keyword_range = self.cur().range();
        self.bump();
        let delegate = self.at(TokenKind::Star) && !self.has_newline_before();
        if delegate {
            self.bump();
        }
        let argument = if delegate || (self.can_start_expression() && !self.has_newline_before()) {
            Some(Box::new(self.parse_assignment_expression(no_in)))
        } else {
            None
        };
        // A yield expression is legal only inside a generator; the
        // argument-bearing form is unambiguous, so it reports TS1163
        // wherever it appears outside one. A bare `yield` stays quiet:
        // in sloppy code it is a plain identifier reference.
        if !self.keyword_context.yield_reserved && argument.is_some() && self.is_typescript() {
            // Anchored at the yield keyword; TypeScript sources only,
            // since sloppy scripts may call `yield(1)` as an identifier.
            self.error_at(
                YIELD_OUTSIDE_GENERATOR,
                keyword_range,
                "A 'yield' expression is only allowed in a generator body.",
            );
        }
        self.node(
            start,
            Expression::Yield(YieldExpression { delegate, argument }),
        )
    }

    fn can_start_expression(&self) -> bool {
        match self.kind() {
            TokenKind::Semicolon
            | TokenKind::RParen
            | TokenKind::RBrace
            | TokenKind::RBracket
            | TokenKind::Comma
            | TokenKind::Colon
            | TokenKind::EndOfFile => false,
            _ => !self.at_eof(),
        }
    }

    fn parse_conditional_expression(&mut self, no_in: bool) -> Expr {
        if !self.enter() {
            return self.missing_expr();
        }
        let expr = self.parse_conditional_inner(no_in);
        self.leave();
        expr
    }

    fn parse_conditional_inner(&mut self, no_in: bool) -> Expr {
        let start = self.cur_start();
        let test = self.parse_binary_expression(0, no_in);
        if !self.at(TokenKind::Question) {
            return test;
        }
        self.bump();
        let consequent = self.parse_assignment_expression(false);
        self.expect(TokenKind::Colon, "expected `:`");
        let alternate = self.parse_assignment_expression(no_in);
        self.node(
            start,
            Expression::Conditional(ConditionalExpression {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: Box::new(alternate),
            }),
        )
    }

    fn parse_binary_expression(&mut self, min_precedence: u8, no_in: bool) -> Expr {
        if !self.enter() {
            return self.missing_expr();
        }
        let expr = self.parse_binary_inner(min_precedence, no_in);
        self.leave();
        expr
    }

    fn parse_binary_inner(&mut self, min_precedence: u8, no_in: bool) -> Expr {
        let start = self.cur_start();
        let mut left = self.parse_unary_expression();
        loop {
            if self.is_cancelled() {
                break;
            }
            // TypeScript `as`/`satisfies` postfix type operators (precedence
            // just above relational). Disallowed across a newline.
            if matches!(self.kind(), TokenKind::KwAs | TokenKind::KwSatisfies)
                && !self.has_newline_before()
                && min_precedence <= 10
            {
                let is_satisfies = self.at(TokenKind::KwSatisfies);
                let range = self.cur().range();
                self.note_typescript_syntax(range);
                self.bump();
                if is_satisfies {
                    let type_node = self.parse_type();
                    left = self.node(
                        start,
                        Expression::Satisfies(SatisfiesExpression {
                            expression: Box::new(left),
                            type_node: Box::new(type_node),
                        }),
                    );
                } else {
                    let type_node = if self.at(TokenKind::KwConst) {
                        // `as const` is a language construct, not a type reference.
                        self.bump();
                        None
                    } else {
                        Some(Box::new(self.parse_type()))
                    };
                    left = self.node(
                        start,
                        Expression::As(AsExpression {
                            expression: Box::new(left),
                            type_node,
                        }),
                    );
                }
                continue;
            }

            let Some((op, precedence)) = binary_precedence(self.kind()) else {
                break;
            };
            if precedence < min_precedence {
                break;
            }
            if no_in && self.at(TokenKind::KwIn) {
                break;
            }
            // `**` is right-associative, and ECMAScript forbids an
            // unparenthesized prefix-unary (or `await`) left operand. `self`
            // still points at the operator, so inspect it before consuming.
            let is_exponent = matches!(self.kind(), TokenKind::StarStar);
            if is_exponent && matches!(left.data(), Expression::Unary(_) | Expression::Await(_)) {
                let op_range = self.cur().range();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    op_range,
                    "an unparenthesized unary expression cannot be the left operand of `**`",
                );
            }
            self.bump();
            let next_min = if is_exponent {
                precedence
            } else {
                precedence + 1
            };
            let right = self.parse_binary_expression(next_min, no_in);
            left = match op {
                BinaryOrLogical::Binary(operator) => self.node(
                    start,
                    Expression::Binary(BinaryExpression {
                        operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                ),
                BinaryOrLogical::Logical(operator) => self.node(
                    start,
                    Expression::Logical(LogicalExpression {
                        operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    }),
                ),
            };
        }
        left
    }

    fn parse_unary_expression(&mut self) -> Expr {
        if !self.enter() {
            return self.missing_expr();
        }
        let expr = self.parse_unary_inner();
        self.leave();
        expr
    }

    fn parse_unary_inner(&mut self) -> Expr {
        let start = self.cur_start();
        let unary = match self.kind() {
            TokenKind::Plus => Some(UnaryOperator::Plus),
            TokenKind::Minus => Some(UnaryOperator::Minus),
            TokenKind::Bang => Some(UnaryOperator::Not),
            TokenKind::Tilde => Some(UnaryOperator::BitNot),
            TokenKind::KwTypeof => Some(UnaryOperator::Typeof),
            TokenKind::KwVoid => Some(UnaryOperator::Void),
            TokenKind::KwDelete => Some(UnaryOperator::Delete),
            _ => None,
        };
        if let Some(operator) = unary {
            self.bump();
            let argument = self.parse_unary_expression();
            return self.node(
                start,
                Expression::Unary(UnaryExpression {
                    operator,
                    argument: Box::new(argument),
                }),
            );
        }

        if matches!(self.kind(), TokenKind::PlusPlus | TokenKind::MinusMinus) {
            let operator = if self.at(TokenKind::PlusPlus) {
                UpdateOperator::Increment
            } else {
                UpdateOperator::Decrement
            };
            self.bump();
            let argument = self.parse_unary_expression();
            let target = self.expression_to_target(argument);
            return self.node(
                start,
                Expression::Update(UpdateExpression {
                    operator,
                    argument: Box::new(target),
                    prefix: true,
                }),
            );
        }

        if self.at(TokenKind::KwAwait) && self.can_start_expression_after(1) {
            let keyword_range = self.cur().range();
            self.bump();
            let argument = self.parse_unary_expression();
            // Await belongs to async functions (or module top level,
            // which no function-like context covers); a plain nested
            // function-like parsing one is TS1308. Anchored at the
            // await keyword, TypeScript sources only.
            if !self.keyword_context.await_reserved
                && self.keyword_context.in_function
                && self.is_typescript()
            {
                self.error_at(
                    AWAIT_OUTSIDE_ASYNC,
                    keyword_range,
                    "'await' expressions are only allowed within async functions and at the top levels of modules.",
                );
            }
            return self.node(
                start,
                Expression::Await(AwaitExpression {
                    argument: Box::new(argument),
                }),
            );
        }

        // TypeScript `<Type>expr` assertion (never in a React source, where
        // `<` begins JSX).
        if self.at(TokenKind::LessThan)
            && self.is_typescript()
            && !matches!(self.script_kind, ScriptKind::TypeScriptReact)
        {
            return self.parse_type_assertion(start);
        }

        self.parse_postfix_expression()
    }

    /// Whether the `n`-th token can begin the operand of a prefix operator.
    fn can_start_expression_after(&self, n: usize) -> bool {
        !matches!(
            self.nth_kind(n),
            TokenKind::Semicolon
                | TokenKind::RParen
                | TokenKind::RBrace
                | TokenKind::RBracket
                | TokenKind::Comma
                | TokenKind::Colon
                | TokenKind::EndOfFile
                | TokenKind::Eq
        )
    }

    fn parse_type_assertion(&mut self, start: Utf16Pos) -> Expr {
        let range = self.cur().range();
        self.note_typescript_syntax(range);
        self.expect_type_open("expected `<`");
        if self.at(TokenKind::KwConst) {
            // `<const>expr` is the prefix spelling of `expr as const`.
            self.bump();
            self.expect_type_close("expected `>`");
            let expression = self.parse_unary_expression();
            return self.node(
                start,
                Expression::As(AsExpression {
                    expression: Box::new(expression),
                    type_node: None,
                }),
            );
        }
        let type_node = self.parse_type();
        self.expect_type_close("expected `>`");
        let expression = self.parse_unary_expression();
        self.node(
            start,
            Expression::TypeAssertion(TypeAssertionExpression {
                expression: Box::new(expression),
                type_node: Box::new(type_node),
            }),
        )
    }

    fn parse_postfix_expression(&mut self) -> Expr {
        let start = self.cur_start();
        let expr = self.parse_lhs_expression(LhsContext::Expression);
        if matches!(self.kind(), TokenKind::PlusPlus | TokenKind::MinusMinus)
            && !self.has_newline_before()
        {
            let operator = if self.at(TokenKind::PlusPlus) {
                UpdateOperator::Increment
            } else {
                UpdateOperator::Decrement
            };
            self.bump();
            let target = self.expression_to_target(expr);
            return self.node(
                start,
                Expression::Update(UpdateExpression {
                    operator,
                    argument: Box::new(target),
                    prefix: false,
                }),
            );
        }
        expr
    }

    /// Parses a left-hand-side expression: a primary or `new` expression
    /// followed by member accesses, calls, non-null assertions, and template
    /// tags. Decorators stop before a newline-following computed class member.
    fn parse_lhs_expression(&mut self, ctx: LhsContext) -> Expr {
        let start = self.cur_start();
        let mut expr = if self.at(TokenKind::KwNew) {
            self.parse_new_expression(ctx)
        } else {
            self.parse_primary_expression()
        };
        expr = self.parse_call_and_member_tail(start, expr, ctx);
        expr
    }

    fn parse_new_expression(&mut self, ctx: LhsContext) -> Expr {
        let start = self.cur_start();
        self.bump();
        if self.at(TokenKind::Dot) {
            self.bump();
            // `new.target`
            let _ = self.expect_identifier("expected `target`");
            return self.node(start, Expression::Meta(MetaProperty::NewTarget));
        }
        let callee = if self.at(TokenKind::KwNew) {
            self.parse_new_expression(ctx)
        } else {
            let primary = self.parse_primary_expression();
            self.parse_member_tail(start, primary, ctx)
        };
        let type_arguments = self.try_parse_type_arguments_speculative();
        let arguments = if self.at(TokenKind::LParen) {
            self.parse_arguments()
        } else {
            Vec::new()
        };
        self.node(
            start,
            Expression::New(NewExpression {
                callee: Box::new(callee),
                type_arguments,
                arguments,
            }),
        )
    }

    /// Member-only tail (no calls): used for a `new` callee.
    fn parse_member_tail(&mut self, start: Utf16Pos, mut expr: Expr, ctx: LhsContext) -> Expr {
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.kind() {
                TokenKind::Dot => {
                    self.bump();
                    let property = self.parse_member_property_name();
                    expr = self.node(
                        start,
                        Expression::Member(MemberExpression {
                            object: Box::new(expr),
                            property,
                            optional: false,
                        }),
                    );
                }
                TokenKind::LBracket
                    if ctx.allows_newline_computed_member() || !self.has_newline_before() =>
                {
                    self.bump();
                    let index = self.parse_expression(false);
                    self.expect(TokenKind::RBracket, "expected `]`");
                    expr = self.node(
                        start,
                        Expression::Member(MemberExpression {
                            object: Box::new(expr),
                            property: MemberProperty::Computed(Box::new(index)),
                            optional: false,
                        }),
                    );
                }
                TokenKind::Bang if !self.has_newline_before() => {
                    self.bump();
                    expr = self.node(
                        start,
                        Expression::NonNull(NonNullExpression {
                            expression: Box::new(expr),
                        }),
                    );
                }
                _ => break,
            }
        }
        expr
    }

    fn parse_call_and_member_tail(
        &mut self,
        start: Utf16Pos,
        mut expr: Expr,
        ctx: LhsContext,
    ) -> Expr {
        loop {
            if self.is_cancelled() {
                break;
            }
            match self.kind() {
                TokenKind::Dot => {
                    self.bump();
                    let property = self.parse_member_property_name();
                    expr = self.node(
                        start,
                        Expression::Member(MemberExpression {
                            object: Box::new(expr),
                            property,
                            optional: false,
                        }),
                    );
                }
                TokenKind::QuestionDot => {
                    self.bump();
                    expr = self.parse_optional_chain_link(start, expr, false);
                }
                TokenKind::LBracket
                    if ctx.allows_newline_computed_member() || !self.has_newline_before() =>
                {
                    self.bump();
                    let index = self.parse_expression(false);
                    self.expect(TokenKind::RBracket, "expected `]`");
                    expr = self.node(
                        start,
                        Expression::Member(MemberExpression {
                            object: Box::new(expr),
                            property: MemberProperty::Computed(Box::new(index)),
                            optional: false,
                        }),
                    );
                }
                TokenKind::LParen => {
                    let arguments = self.parse_arguments();
                    expr = self.node(
                        start,
                        Expression::Call(CallExpression {
                            callee: Box::new(expr),
                            optional: false,
                            type_arguments: None,
                            arguments,
                        }),
                    );
                }
                TokenKind::Bang if !self.has_newline_before() => {
                    self.bump();
                    expr = self.node(
                        start,
                        Expression::NonNull(NonNullExpression {
                            expression: Box::new(expr),
                        }),
                    );
                }
                TokenKind::NoSubstitutionTemplate | TokenKind::TemplateHead => {
                    let template = self.parse_template_literal();
                    expr = self.node(
                        start,
                        Expression::TaggedTemplate(TaggedTemplateExpression {
                            tag: Box::new(expr),
                            template,
                        }),
                    );
                }
                _ if self.at_less_like() => {
                    // `f<T>(...)` / `f<T>\`...\``: only a call/tagged-template
                    // if type arguments parse and are followed by `(` or a
                    // template. Otherwise this `<` is a comparison.
                    let Some(type_arguments) = self.try_parse_type_arguments_for_call() else {
                        break;
                    };
                    if self.at(TokenKind::LParen) {
                        let arguments = self.parse_arguments();
                        expr = self.node(
                            start,
                            Expression::Call(CallExpression {
                                callee: Box::new(expr),
                                optional: false,
                                type_arguments: Some(type_arguments),
                                arguments,
                            }),
                        );
                    } else if matches!(
                        self.kind(),
                        TokenKind::NoSubstitutionTemplate | TokenKind::TemplateHead
                    ) {
                        let template = self.parse_template_literal();
                        expr = self.node(
                            start,
                            Expression::TaggedTemplate(TaggedTemplateExpression {
                                tag: Box::new(expr),
                                template,
                            }),
                        );
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        expr
    }

    fn parse_optional_chain_link(&mut self, start: Utf16Pos, expr: Expr, no_call: bool) -> Expr {
        match self.kind() {
            TokenKind::LParen if !no_call => {
                let arguments = self.parse_arguments();
                self.node(
                    start,
                    Expression::Call(CallExpression {
                        callee: Box::new(expr),
                        optional: true,
                        type_arguments: None,
                        arguments,
                    }),
                )
            }
            TokenKind::LBracket => {
                self.bump();
                let index = self.parse_expression(false);
                self.expect(TokenKind::RBracket, "expected `]`");
                self.node(
                    start,
                    Expression::Member(MemberExpression {
                        object: Box::new(expr),
                        property: MemberProperty::Computed(Box::new(index)),
                        optional: true,
                    }),
                )
            }
            _ if self.at_less_like() && !no_call => {
                if let Some(type_arguments) = self.try_parse_type_arguments_for_call() {
                    let arguments = self.parse_arguments();
                    self.node(
                        start,
                        Expression::Call(CallExpression {
                            callee: Box::new(expr),
                            optional: true,
                            type_arguments: Some(type_arguments),
                            arguments,
                        }),
                    )
                } else {
                    let property = self.parse_member_property_name();
                    self.node(
                        start,
                        Expression::Member(MemberExpression {
                            object: Box::new(expr),
                            property,
                            optional: true,
                        }),
                    )
                }
            }
            _ => {
                let property = self.parse_member_property_name();
                self.node(
                    start,
                    Expression::Member(MemberExpression {
                        object: Box::new(expr),
                        property,
                        optional: true,
                    }),
                )
            }
        }
    }

    fn parse_member_property_name(&mut self) -> MemberProperty {
        if self.at(TokenKind::PrivateIdentifier) {
            let token = self.bump();
            let range = token.range();
            let node = self.node_at(range, PrivateIdentifier::new(token));
            return MemberProperty::Private(node);
        }
        if is_any_word(self.kind()) {
            let token = self.bump();
            return MemberProperty::Named(self.identifier_name_from(token));
        }
        self.error_here(EXPECTED_IDENTIFIER, "expected a property name");
        MemberProperty::Named(self.missing_ident())
    }

    fn parse_arguments(&mut self) -> Vec<CallArgument> {
        self.expect(TokenKind::LParen, "expected `(`");
        let mut arguments = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RParen) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            if self.at(TokenKind::DotDotDot) {
                let spread_start = self.cur_start();
                self.bump();
                let argument = self.parse_assignment_expression(false);
                arguments.push(CallArgument::Spread(SpreadElement {
                    argument: Box::new(argument),
                }));
                let _ = spread_start;
            } else {
                let argument = self.parse_assignment_expression(false);
                arguments.push(CallArgument::Expression(Box::new(argument)));
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an argument list",
                );
            }
        }
        self.expect(TokenKind::RParen, "expected `)`");
        arguments
    }

    fn parse_primary_expression(&mut self) -> Expr {
        let start = self.cur_start();
        match self.kind() {
            TokenKind::Slash | TokenKind::SlashEq => {
                self.rescan_regex_here();
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, RegexLiteral::new(token));
                self.node(start, Expression::Literal(Literal::Regex(node)))
            }
            TokenKind::KwThis => {
                self.bump();
                self.node(start, Expression::This)
            }
            TokenKind::KwSuper => {
                self.bump();
                self.node(start, Expression::Super)
            }
            TokenKind::KwTrue | TokenKind::KwFalse => {
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, BooleanLiteral::new(token));
                self.node(start, Expression::Literal(Literal::Boolean(node)))
            }
            TokenKind::KwNull => {
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, NullLiteral::new(token));
                self.node(start, Expression::Literal(Literal::Null(node)))
            }
            TokenKind::NumericLiteral => {
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, NumericLiteral::new(token));
                self.node(start, Expression::Literal(Literal::Number(node)))
            }
            TokenKind::BigIntLiteral => {
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, BigIntLiteral::new(token));
                self.node(start, Expression::Literal(Literal::BigInt(node)))
            }
            TokenKind::StringLiteral => {
                let node = self.parse_string_literal();
                self.node(start, Expression::Literal(Literal::String(node)))
            }
            TokenKind::NoSubstitutionTemplate | TokenKind::TemplateHead => {
                let template = self.parse_template_literal();
                self.node(start, Expression::Template(template))
            }
            TokenKind::LBracket => self.parse_array_literal(),
            TokenKind::LBrace => self.parse_object_literal(),
            TokenKind::LParen => {
                self.bump();
                let inner = self.parse_expression(false);
                self.expect(TokenKind::RParen, "expected `)`");
                self.node(start, Expression::Parenthesized(Box::new(inner)))
            }
            TokenKind::KwFunction => {
                let function = self.parse_function_like(Vec::new(), false, false);
                self.node(start, Expression::Function(FunctionExpression { function }))
            }
            TokenKind::KwAsync if self.nth_kind(1) == TokenKind::KwFunction => {
                self.bump();
                let function = self.parse_function_like(Vec::new(), true, false);
                self.node(start, Expression::Function(FunctionExpression { function }))
            }
            TokenKind::KwClass => {
                let class = self.parse_class(Vec::new(), DeclarationModifiers::default(), false);
                self.node(start, Expression::Class(ClassExpression { class }))
            }
            TokenKind::At => self.parse_decorated_class_expression(start),
            TokenKind::KwImport => self.parse_import_expression(start),
            TokenKind::PrivateIdentifier => {
                // `#field in obj`: represent the private name as an identifier
                // operand, the only expression form the node space provides.
                let token = self.bump();
                let node = self.ident_from(token);
                self.node(start, Expression::Identifier(node))
            }
            TokenKind::LessThan
                if matches!(self.script_kind, ScriptKind::TypeScriptReact)
                    || matches!(self.script_kind, ScriptKind::JavaScriptReact) =>
            {
                self.parse_jsx(start)
            }
            kind if is_identifier_like(kind) => {
                let token = self.bump();
                let node = self.ident_from(token);
                self.node(start, Expression::Identifier(node))
            }
            _ => {
                self.error_here(EXPECTED_EXPRESSION, "expected an expression");
                self.missing_expr()
            }
        }
    }

    /// Expression-path `@decorator class`: a primary, so postfix member/call
    /// and lower-precedence binary/assignment continuations apply exactly as
    /// for an undecorated class expression. Malformed trailing material on the
    /// same line is consumed through its assignment-expression boundary so it
    /// cannot escape as a sibling statement.
    fn parse_decorated_class_expression(&mut self, start: Utf16Pos) -> Expr {
        let decorators = self.parse_decorators();
        if !self.at(TokenKind::KwClass) {
            self.error_here(EXPECTED_TOKEN, "decorators must precede a class");
            if self.can_start_expression() && !self.has_newline_before() {
                let _ = self.parse_assignment_expression(false);
            }
            return self.missing_expr();
        }
        let class = self.parse_class(decorators, DeclarationModifiers::default(), false);
        self.node(start, Expression::Class(ClassExpression { class }))
    }

    fn parse_import_expression(&mut self, start: Utf16Pos) -> Expr {
        self.bump();
        if self.at(TokenKind::Dot) {
            self.bump();
            // `import.meta`
            let _ = self.expect_identifier("expected `meta`");
            return self.node(start, Expression::Meta(MetaProperty::ImportMeta));
        }
        self.expect(TokenKind::LParen, "expected `(`");
        let source = self.parse_assignment_expression(false);
        let options = if self.eat(TokenKind::Comma).is_some() && !self.at(TokenKind::RParen) {
            let opt = self.parse_assignment_expression(false);
            let _ = self.eat(TokenKind::Comma);
            Some(Box::new(opt))
        } else {
            None
        };
        self.expect(TokenKind::RParen, "expected `)`");
        self.node(
            start,
            Expression::Import(ImportExpression {
                source: Box::new(source),
                options,
            }),
        )
    }

    /// Parses a JSX element or fragment. The whole construct is first re-lexed
    /// from the source into JSX-aware tokens spliced over the default pass (see
    /// [`Self::rescan_jsx_span`]), then reparsed structurally so nested
    /// expression containers reuse the ordinary expression grammar.
    fn parse_jsx(&mut self, start: Utf16Pos) -> Expr {
        let _ = start;
        self.rescan_jsx_span();
        self.parse_jsx_element_or_fragment()
    }

    /// Re-lexes the JSX construct starting at the current `<` and splices the
    /// JSX-aware tokens over the default pass's tokens for that span, keeping
    /// the stored stream byte-exact. Mirrors the regex rescan's span handling.
    fn rescan_jsx_span(&mut self) {
        if !self.at(TokenKind::LessThan) || self.at_eof() {
            return;
        }
        let index = self.cursor;
        let start = self.tokens[index].range().start();
        let Ok(start_byte) = self.source.utf16_to_byte(start) else {
            return;
        };
        // Same budget invariant as `scan_shifted_fragment`: a tail of a
        // budget-checked source cannot exceed the per-file cap; bail out
        // instead of panicking if that ever changes.
        let Ok(fragment) =
            SourceText::new(self.source.as_str()[start_byte..].to_owned()).map(Arc::new)
        else {
            return;
        };
        let mut scanner = crate::scanner::Scanner::new(self.source_id, self.script_kind, &fragment);
        let jsx_tokens = scanner.scan_jsx_span();
        let consumed = jsx_tokens
            .last()
            .map_or(0, |token| token.range().end().get());
        if consumed == 0 {
            return;
        }
        let base = start.get();
        let end = base + consumed;
        let shift = |range: TextRange| {
            TextRange::new(
                Utf16Pos::new(base + range.start().get()),
                Utf16Pos::new(base + range.end().get()),
            )
            .expect("shift preserves range ordering")
        };
        let mut replacement: Vec<Token> = jsx_tokens
            .iter()
            .map(|token| Token::new(token.kind(), shift(token.range())))
            .collect();
        for diagnostic in scanner.into_diagnostics() {
            let shifted = shift(diagnostic.range());
            self.diagnostics.push(diagnostic.with_range(shifted));
        }
        // Absorb the pre-scanned tokens the span covers; a default token may
        // straddle the JSX end, so re-lex only its trailing fragment.
        let mut last = index;
        while last + 1 < self.tokens.len() && self.tokens[last].range().end().get() < end {
            last += 1;
        }
        let covered_end = self.tokens[last].range().end().get();
        if covered_end > end {
            replacement.extend(self.scan_shifted_fragment(end, covered_end));
        }
        self.replace_tokens(index, last, replacement);
        self.jsx_spans
            .push(TextRange::new(start, Utf16Pos::new(end)).expect("a JSX span grows forward"));
    }

    fn parse_jsx_element_or_fragment(&mut self) -> Expr {
        let start = self.cur_start();
        if !self.enter() {
            if self.at(TokenKind::LessThan) {
                self.bump();
            }
            return self.node(
                start,
                Expression::Missing(MissingNode::new(NodeKind::MissingExpression)),
            );
        }
        let result = self.parse_jsx_inner(start);
        self.leave();
        result
    }

    fn parse_jsx_inner(&mut self, start: Utf16Pos) -> Expr {
        self.expect(TokenKind::LessThan, "expected `<`");
        // Fragment `<>children</>`.
        if self.at(TokenKind::GreaterThan) {
            self.bump();
            let children = self.parse_jsx_children();
            self.expect(TokenKind::LessThan, "expected `</>`");
            self.expect(TokenKind::Slash, "expected `/`");
            self.expect(TokenKind::GreaterThan, "expected `>`");
            return self.node(start, Expression::JsxFragment(JsxFragment { children }));
        }
        let name = self.parse_jsx_element_name();
        let attributes = self.parse_jsx_attributes();
        if self.at(TokenKind::Slash) {
            self.bump();
            self.expect(TokenKind::GreaterThan, "expected `>`");
            return self.node(
                start,
                Expression::JsxSelfClosingElement(JsxSelfClosingElement { name, attributes }),
            );
        }
        self.expect(TokenKind::GreaterThan, "expected `>`");
        let opening = self.node(start, JsxOpeningElement { name, attributes });
        let children = self.parse_jsx_children();
        let closing = self.parse_jsx_closing_element();
        let open_text = self.jsx_name_text(&opening.data().name);
        let close_text = self.jsx_name_text(&closing.data().name);
        if open_text != close_text {
            self.error_at(
                EXPECTED_TOKEN,
                closing.range(),
                "JSX closing tag does not match the opening tag",
            );
        }
        self.node(
            start,
            Expression::JsxElement(JsxElement {
                opening,
                children,
                closing,
            }),
        )
    }

    fn parse_jsx_closing_element(&mut self) -> JsxClosingElementNode {
        let start = self.cur_start();
        self.expect(TokenKind::LessThan, "expected `</`");
        self.expect(TokenKind::Slash, "expected `/`");
        let name = self.parse_jsx_element_name();
        self.expect(TokenKind::GreaterThan, "expected `>`");
        self.node(start, JsxClosingElement { name })
    }

    /// Parses a JSX name identifier. JSX names are always lexed as
    /// [`TokenKind::Identifier`], so reserved-word rejection does not apply.
    fn parse_jsx_name_identifier(&mut self) -> IdentifierNode {
        if self.at(TokenKind::Identifier) {
            let token = self.bump();
            return self.identifier_name_from(token);
        }
        self.error_here(EXPECTED_IDENTIFIER, "expected a JSX name");
        self.missing_ident()
    }

    /// Element name: bare identifier, namespaced `ns:name`, or a dotted member
    /// chain `A.B.C`.
    fn parse_jsx_element_name(&mut self) -> JsxElementName {
        let first = self.parse_jsx_name_identifier();
        if self.at(TokenKind::Colon) {
            self.bump();
            let name = self.parse_jsx_name_identifier();
            return JsxElementName::Namespace(JsxNamespacedName {
                namespace: first,
                name,
            });
        }
        let mut current = JsxElementName::Identifier(first);
        while self.at(TokenKind::Dot) {
            if self.is_cancelled() {
                break;
            }
            self.bump();
            let property = self.parse_jsx_name_identifier();
            current = JsxElementName::Member(JsxMemberName {
                object: Box::new(current),
                property,
            });
        }
        current
    }

    /// Attribute name: bare identifier or namespaced `ns:name`.
    fn parse_jsx_attribute_name(&mut self) -> JsxAttributeName {
        let first = self.parse_jsx_name_identifier();
        if self.at(TokenKind::Colon) {
            self.bump();
            let name = self.parse_jsx_name_identifier();
            return JsxAttributeName::Namespace(JsxNamespacedName {
                namespace: first,
                name,
            });
        }
        JsxAttributeName::Identifier(first)
    }

    fn parse_jsx_attributes(&mut self) -> Vec<JsxAttributeItem> {
        let mut items = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::GreaterThan) && !self.at(TokenKind::Slash) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            if self.at(TokenKind::LBrace) {
                items.push(self.parse_jsx_spread_attribute());
            } else if self.at(TokenKind::Identifier) {
                items.push(self.parse_jsx_attribute());
            } else {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a JSX tag",
                );
            }
            if self.cursor == before {
                break;
            }
        }
        items
    }

    fn parse_jsx_attribute(&mut self) -> JsxAttributeItem {
        let start = self.cur_start();
        let name = self.parse_jsx_attribute_name();
        let initializer = if self.eat(TokenKind::Eq).is_some() {
            Some(self.parse_jsx_attribute_initializer())
        } else {
            None
        };
        let node = self.node(start, JsxAttribute { name, initializer });
        JsxAttributeItem::Attribute(node)
    }

    fn parse_jsx_attribute_initializer(&mut self) -> JsxAttributeInitializer {
        if self.at(TokenKind::LBrace) {
            return JsxAttributeInitializer::Expression(self.parse_jsx_expression_container());
        }
        if self.at(TokenKind::StringLiteral) {
            return JsxAttributeInitializer::String(self.parse_string_literal());
        }
        self.error_here(EXPECTED_EXPRESSION, "expected a JSX attribute value");
        let start = self.cur_start();
        let container = self.node(start, JsxExpressionContainer { expression: None });
        JsxAttributeInitializer::Expression(container)
    }

    fn parse_jsx_spread_attribute(&mut self) -> JsxAttributeItem {
        let start = self.cur_start();
        self.expect(TokenKind::LBrace, "expected `{`");
        self.expect(TokenKind::DotDotDot, "expected `...`");
        let expression = self.parse_assignment_expression(false);
        self.expect(TokenKind::RBrace, "expected `}`");
        let node = self.node(
            start,
            JsxSpreadAttribute {
                expression: Box::new(expression),
            },
        );
        JsxAttributeItem::Spread(node)
    }

    fn parse_jsx_expression_container(&mut self) -> JsxExpressionContainerNode {
        let start = self.cur_start();
        self.expect(TokenKind::LBrace, "expected `{`");
        let expression = if self.at(TokenKind::RBrace) {
            None
        } else {
            Some(Box::new(self.parse_assignment_expression(false)))
        };
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(start, JsxExpressionContainer { expression })
    }

    fn parse_jsx_spread_child(&mut self) -> JsxSpreadChildNode {
        let start = self.cur_start();
        self.expect(TokenKind::LBrace, "expected `{`");
        self.expect(TokenKind::DotDotDot, "expected `...`");
        let expression = self.parse_assignment_expression(false);
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(
            start,
            JsxSpreadChild {
                expression: Box::new(expression),
            },
        )
    }

    /// Parses children until the parent's closing tag (`</`) or end of file.
    fn parse_jsx_children(&mut self) -> Vec<JsxChild> {
        let mut children = Vec::new();
        while !self.at_eof() {
            if self.is_cancelled() {
                break;
            }
            if self.at(TokenKind::LessThan) {
                if self.nth_kind(1) == TokenKind::Slash {
                    break;
                }
                let child = self.parse_jsx_element_or_fragment();
                children.push(JsxChild::Element(Box::new(child)));
                continue;
            }
            if self.at(TokenKind::LBrace) {
                if self.nth_kind(1) == TokenKind::DotDotDot {
                    children.push(JsxChild::Spread(self.parse_jsx_spread_child()));
                } else {
                    children.push(JsxChild::ExpressionContainer(
                        self.parse_jsx_expression_container(),
                    ));
                }
                continue;
            }
            if self.at(TokenKind::StringLiteral) {
                let token = self.bump();
                let range = token.range();
                let node = self.node_at(range, JsxText::new(token));
                children.push(JsxChild::Text(node));
                continue;
            }
            let skipped = self.bump();
            self.error_at(
                UNEXPECTED_TOKEN,
                skipped.range(),
                "this token was skipped inside JSX children",
            );
        }
        children
    }

    /// Renders a JSX name to its source text for opening/closing tag matching.
    fn jsx_name_text(&self, name: &JsxElementName) -> String {
        match name {
            JsxElementName::Identifier(identifier) => {
                self.lexeme(*identifier.data().token()).to_owned()
            }
            JsxElementName::Namespace(namespaced) => format!(
                "{}:{}",
                self.lexeme(*namespaced.namespace.data().token()),
                self.lexeme(*namespaced.name.data().token())
            ),
            JsxElementName::Member(member) => format!(
                "{}.{}",
                self.jsx_name_text(&member.object),
                self.lexeme(*member.property.data().token())
            ),
        }
    }

    fn parse_array_literal(&mut self) -> Expr {
        let start = self.cur_start();
        self.bump();
        let mut elements = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBracket) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            if self.at(TokenKind::Comma) {
                self.bump();
                elements.push(ArrayElement::Elision);
                continue;
            }
            if self.at(TokenKind::DotDotDot) {
                let spread_start = self.cur_start();
                self.bump();
                let argument = self.parse_assignment_expression(false);
                elements.push(ArrayElement::Spread(SpreadElement {
                    argument: Box::new(argument),
                }));
                let _ = spread_start;
            } else {
                let expr = self.parse_assignment_expression(false);
                elements.push(ArrayElement::Expression(Box::new(expr)));
            }
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an array literal",
                );
            }
        }
        self.expect(TokenKind::RBracket, "expected `]`");
        self.node(start, Expression::Array(ArrayLiteral { elements }))
    }

    fn parse_object_literal(&mut self) -> Expr {
        let start = self.cur_start();
        self.bump();
        let mut members = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let member = self.parse_object_member();
            members.push(member);
            if self.eat(TokenKind::Comma).is_none() && !self.at(TokenKind::RBrace) {
                self.error_here(EXPECTED_TOKEN, "expected `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside an object literal",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(start, Expression::Object(ObjectLiteral { members }))
    }

    fn parse_object_member(&mut self) -> ObjectMemberNode {
        let start = self.cur_start();
        if self.at(TokenKind::DotDotDot) {
            self.bump();
            let argument = self.parse_assignment_expression(false);
            return self.node(
                start,
                ObjectMember::Spread(SpreadElement {
                    argument: Box::new(argument),
                }),
            );
        }

        let mut is_async = false;
        let mut is_generator = false;
        let mut modifier = PropertyModifier::None;

        if self.at(TokenKind::KwAsync)
            && !self.has_newline_before_nth(1)
            && self.object_member_name_follows(1)
        {
            is_async = true;
            self.bump();
        }
        if self.at(TokenKind::Star) {
            is_generator = true;
            self.bump();
        }
        if matches!(self.kind(), TokenKind::KwGet | TokenKind::KwSet)
            && self.object_member_name_follows(1)
            && !is_async
            && !is_generator
        {
            modifier = if self.at(TokenKind::KwGet) {
                PropertyModifier::Get
            } else {
                PropertyModifier::Set
            };
            self.bump();
        }

        let name = self.parse_property_name();

        // Method.
        if self.at(TokenKind::LParen) || self.at_less_like() {
            let keyword_context = KeywordContext {
                in_function: true,
                await_reserved: is_async,
                yield_reserved: is_generator,
            };
            let type_parameters = self.parse_optional_type_parameters();
            let parameters =
                self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
            let return_type = self.parse_optional_type_annotation();
            let body = if self.at(TokenKind::LBrace) {
                Some(FunctionBody::Block(
                    self.with_keyword_context(keyword_context, Self::parse_block),
                ))
            } else if self.at_missing_body_boundary() {
                // Upstream tolerates a missing method or accessor body when
                // the next token can end the member (its
                // parseFunctionBlockOrSemicolon accepts a semicolon-like
                // boundary silently), so `{ get foo() }` recovers without a
                // diagnostic instead of derailing the object literal.
                None
            } else {
                self.error_here(EXPECTED_TOKEN, "expected a method body");
                None
            };
            return self.node(
                start,
                ObjectMember::Method(ObjectMethod {
                    name,
                    modifier,
                    function: FunctionLike {
                        decorators: Vec::new(),
                        name: None,
                        is_async,
                        is_generator,
                        type_parameters,
                        parameters,
                        return_type,
                        body,
                    },
                }),
            );
        }

        // `name: value`
        if self.eat(TokenKind::Colon).is_some() {
            let value = self.parse_assignment_expression(false);
            return self.node(
                start,
                ObjectMember::Property(ObjectProperty {
                    name,
                    value: Box::new(value),
                    modifier: PropertyModifier::None,
                    shorthand: false,
                }),
            );
        }

        // Shorthand `{ name }` or destructuring default `{ name = init }`.
        let value = self.shorthand_value(&name, start);
        self.node(
            start,
            ObjectMember::Property(ObjectProperty {
                name,
                value: Box::new(value),
                modifier: PropertyModifier::None,
                shorthand: true,
            }),
        )
    }

    /// Whether the current token can end a member declaration, so a missing
    /// method or accessor body recovers silently instead of erroring.
    fn at_missing_body_boundary(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::Semicolon
                | TokenKind::Comma
                | TokenKind::RBrace
                | TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::EndOfFile
        )
    }

    /// Builds the value expression of a shorthand property, folding a
    /// destructuring default (`{ a = 1 }`) into an assignment so a later
    /// conversion to a pattern can recover the initializer.
    fn shorthand_value(&mut self, name: &PropertyName, start: Utf16Pos) -> Expr {
        let ident = match name {
            PropertyName::Identifier(node) => {
                let token = *node.data().token();
                self.ident_from(token)
            }
            _ => self.missing_ident(),
        };
        let ident_range = ident.range();
        let ident_expr = self.node_at(ident_range, Expression::Identifier(ident));
        if self.eat(TokenKind::Eq).is_some() {
            let right = self.parse_assignment_expression(false);
            let target = self.expression_to_target(ident_expr);
            return self.node(
                start,
                Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: target,
                    right: Box::new(right),
                }),
            );
        }
        ident_expr
    }

    /// Whether a property name can start at the `n`-th token, used to tell an
    /// `async`/`get`/`set` modifier from a property literally so named.
    fn object_member_name_follows(&self, n: usize) -> bool {
        let kind = self.nth_kind(n);
        is_any_word(kind)
            || matches!(
                kind,
                TokenKind::StringLiteral
                    | TokenKind::NumericLiteral
                    | TokenKind::LBracket
                    | TokenKind::Star
            )
    }

    fn parse_property_name(&mut self) -> PropertyName {
        match self.kind() {
            TokenKind::StringLiteral => PropertyName::String(self.parse_string_literal()),
            TokenKind::NumericLiteral => {
                let token = self.bump();
                let range = token.range();
                PropertyName::Number(self.node_at(range, NumericLiteral::new(token)))
            }
            TokenKind::PrivateIdentifier => {
                let token = self.bump();
                let range = token.range();
                PropertyName::Private(self.node_at(range, PrivateIdentifier::new(token)))
            }
            TokenKind::LBracket => {
                self.bump();
                let expr = self.parse_assignment_expression(false);
                self.expect(TokenKind::RBracket, "expected `]`");
                PropertyName::Computed(Box::new(expr))
            }
            kind if is_any_word(kind) => {
                let token = self.bump();
                PropertyName::Identifier(self.identifier_name_from(token))
            }
            _ => {
                self.error_here(EXPECTED_PROPERTY_NAME, "expected a property name");
                PropertyName::Missing(MissingNode::new(NodeKind::Identifier))
            }
        }
    }

    fn parse_template_literal(&mut self) -> TemplateLiteral {
        let mut elements = Vec::new();
        let mut expressions = Vec::new();
        if self.at(TokenKind::NoSubstitutionTemplate) {
            let token = self.bump();
            let range = token.range();
            elements.push(self.node_at(range, TemplateElement::new(token)));
            return TemplateLiteral {
                elements,
                expressions,
            };
        }
        // Head.
        let head = self.bump();
        let head_range = head.range();
        elements.push(self.node_at(head_range, TemplateElement::new(head)));
        loop {
            if self.is_cancelled() {
                break;
            }
            let expr = self.parse_expression(false);
            expressions.push(expr);
            match self.kind() {
                TokenKind::TemplateMiddle => {
                    let token = self.bump();
                    let range = token.range();
                    elements.push(self.node_at(range, TemplateElement::new(token)));
                }
                TokenKind::TemplateTail => {
                    let token = self.bump();
                    let range = token.range();
                    elements.push(self.node_at(range, TemplateElement::new(token)));
                    break;
                }
                TokenKind::RBrace => {
                    // Recovery: the scanner segmented differently (unbalanced
                    // braces in the substitution). Consume and continue.
                    let token = self.bump();
                    let range = token.range();
                    let tail = Token::new(TokenKind::TemplateTail, range);
                    elements.push(self.node_at(range, TemplateElement::new(tail)));
                    break;
                }
                _ => {
                    self.error_here(EXPECTED_TOKEN, "expected a template continuation");
                    let tail = self.missing_token(TokenKind::TemplateTail);
                    let range = tail.range();
                    elements.push(self.node_at(range, TemplateElement::new(tail)));
                    break;
                }
            }
        }
        TemplateLiteral {
            elements,
            expressions,
        }
    }
}

// ---------------------------------------------------------------------------
// Bindings, functions, parameters, arrows
// ---------------------------------------------------------------------------

impl Parser {
    fn parse_binding_pattern(&mut self) -> Pattern {
        let start = self.cur_start();
        match self.kind() {
            TokenKind::LBrace => self.parse_object_binding_pattern(),
            TokenKind::LBracket => self.parse_array_binding_pattern(),
            kind if is_identifier_like(kind) || kind == TokenKind::KwThis => {
                let token = self.bump();
                let name = self.ident_from(token);
                self.node(start, BindingPattern::Identifier(name))
            }
            _ => {
                self.error_here(EXPECTED_IDENTIFIER, "expected a binding");
                self.missing_pattern()
            }
        }
    }

    fn parse_object_binding_pattern(&mut self) -> Pattern {
        let start = self.cur_start();
        self.bump();
        let mut properties = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            if self.at(TokenKind::DotDotDot) {
                self.bump();
                let arg_start = self.cur_start();
                let inner = self.parse_binding_pattern();
                let rest = self.node(
                    arg_start,
                    BindingPattern::Rest(RestBindingPattern {
                        argument: Box::new(inner),
                    }),
                );
                // The fixed object pattern has no rest slot; carry the rest as
                // a property whose name mirrors its binding for later lowering.
                let name = match rest.data() {
                    BindingPattern::Rest(rest) => match rest.argument.data() {
                        BindingPattern::Identifier(id) => PropertyName::Identifier(id.clone()),
                        _ => PropertyName::Missing(MissingNode::new(NodeKind::Identifier)),
                    },
                    _ => PropertyName::Missing(MissingNode::new(NodeKind::Identifier)),
                };
                properties.push(ObjectBindingProperty {
                    name,
                    binding: rest,
                    initializer: None,
                });
                let _ = self.eat(TokenKind::Comma);
                if self.cursor == before {
                    let skipped = self.bump();
                    self.error_at(
                        UNEXPECTED_TOKEN,
                        skipped.range(),
                        "this token was skipped inside a binding pattern",
                    );
                }
                continue;
            }
            let name = self.parse_property_name();
            let binding = if self.eat(TokenKind::Colon).is_some() {
                self.parse_binding_pattern()
            } else {
                match &name {
                    PropertyName::Identifier(id) => {
                        let range = id.range();
                        self.node_at(range, BindingPattern::Identifier(id.clone()))
                    }
                    _ => {
                        self.error_here(
                            EXPECTED_IDENTIFIER,
                            "a non-identifier binding property needs `:`",
                        );
                        self.missing_pattern()
                    }
                }
            };
            let initializer = if self.eat(TokenKind::Eq).is_some() {
                Some(Box::new(self.parse_assignment_expression(false)))
            } else {
                None
            };
            properties.push(ObjectBindingProperty {
                name,
                binding,
                initializer,
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a binding pattern",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(
            start,
            BindingPattern::Object(ObjectBindingPattern { properties }),
        )
    }

    fn parse_array_binding_pattern(&mut self) -> Pattern {
        let start = self.cur_start();
        self.bump();
        let mut elements = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBracket) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            if self.at(TokenKind::Comma) {
                self.bump();
                elements.push(ArrayBindingElement::Elision);
                continue;
            }
            if self.at(TokenKind::DotDotDot) {
                let rest_start = self.cur_start();
                self.bump();
                let inner = self.parse_binding_pattern();
                let rest = self.node(
                    rest_start,
                    BindingPattern::Rest(RestBindingPattern {
                        argument: Box::new(inner),
                    }),
                );
                elements.push(ArrayBindingElement::Binding(rest));
                let _ = self.eat(TokenKind::Comma);
                if self.cursor == before {
                    let skipped = self.bump();
                    self.error_at(
                        UNEXPECTED_TOKEN,
                        skipped.range(),
                        "this token was skipped inside a binding pattern",
                    );
                }
                continue;
            }
            let element_start = self.cur_start();
            let mut binding = self.parse_binding_pattern();
            if self.eat(TokenKind::Eq).is_some() {
                let right = self.parse_assignment_expression(false);
                binding = self.node(
                    element_start,
                    BindingPattern::Assignment(AssignmentBindingPattern {
                        left: Box::new(binding),
                        right: Box::new(right),
                    }),
                );
            }
            elements.push(ArrayBindingElement::Binding(binding));
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a binding pattern",
                );
            }
        }
        self.expect(TokenKind::RBracket, "expected `]`");
        self.node(
            start,
            BindingPattern::Array(ArrayBindingPattern { elements }),
        )
    }

    /// Parses a function or method: name (optional), type parameters,
    /// parameters, return type, and body.
    fn parse_function_like(
        &mut self,
        decorators: Vec<DecoratorNode>,
        is_async: bool,
        require_name: bool,
    ) -> FunctionLike {
        self.expect(TokenKind::KwFunction, "expected `function`");
        let is_generator = self.eat(TokenKind::Star).is_some();
        let name = if is_identifier_like(self.kind()) {
            let token = self.bump();
            Some(self.ident_from(token))
        } else {
            if require_name && !self.at(TokenKind::LParen) && !self.at_less_like() {
                self.error_here(EXPECTED_IDENTIFIER, "expected a function name");
            }
            None
        };
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: is_async,
            yield_reserved: is_generator,
        };
        let type_parameters = self.parse_optional_type_parameters();
        let parameters =
            self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
        let return_type = self.parse_optional_type_annotation();
        let body = if self.at(TokenKind::LBrace) {
            Some(FunctionBody::Block(
                self.with_keyword_context(keyword_context, Self::parse_block),
            ))
        } else {
            self.expect_semicolon();
            None
        };
        FunctionLike {
            decorators,
            name,
            is_async,
            is_generator,
            type_parameters,
            parameters,
            return_type,
            body,
        }
    }

    fn parse_parameter_list(&mut self) -> Vec<ParameterNode> {
        let open = if self.at(TokenKind::LBracket) {
            TokenKind::LBracket
        } else {
            TokenKind::LParen
        };
        let close = if open == TokenKind::LBracket {
            TokenKind::RBracket
        } else {
            TokenKind::RParen
        };
        self.expect(open, "expected `(`");
        let mut parameters = Vec::new();
        while !self.at_eof() && !self.at(close) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let parameter = self.parse_parameter();
            parameters.push(parameter);
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a parameter list",
                );
            }
        }
        self.expect(close, "expected `)`");
        parameters
    }

    fn parse_parameter(&mut self) -> ParameterNode {
        let start = self.cur_start();
        let decorators = self.parse_decorators();
        let mut modifiers = ParameterModifiers::default();
        loop {
            if self.is_cancelled() {
                break;
            }
            if !self.parameter_modifier_follows() {
                break;
            }
            match self.kind() {
                TokenKind::KwPublic => modifiers.accessibility = Some(Accessibility::Public),
                TokenKind::KwProtected => modifiers.accessibility = Some(Accessibility::Protected),
                TokenKind::KwPrivate => modifiers.accessibility = Some(Accessibility::Private),
                TokenKind::KwReadonly => modifiers.is_readonly = true,
                TokenKind::KwOverride => modifiers.is_override = true,
                _ => break,
            }
            let range = self.cur().range();
            self.note_typescript_syntax(range);
            self.bump();
        }

        if self.at(TokenKind::DotDotDot) {
            let rest_start = self.cur_start();
            self.bump();
            let inner = self.parse_binding_pattern();
            let optional = self.eat(TokenKind::Question).is_some();
            let type_annotation = self.parse_optional_type_annotation();
            let binding = self.node(
                rest_start,
                BindingPattern::Rest(RestBindingPattern {
                    argument: Box::new(inner),
                }),
            );
            return self.node(
                start,
                Parameter {
                    decorators,
                    modifiers,
                    binding,
                    optional,
                    type_annotation,
                    initializer: None,
                },
            );
        }

        let binding = self.parse_binding_pattern();
        let optional = self.eat(TokenKind::Question).is_some();
        let type_annotation = self.parse_optional_type_annotation();
        let initializer = if self.eat(TokenKind::Eq).is_some() {
            Some(Box::new(self.parse_assignment_expression(false)))
        } else {
            None
        };
        self.node(
            start,
            Parameter {
                decorators,
                modifiers,
                binding,
                optional,
                type_annotation,
                initializer,
            },
        )
    }

    fn parameter_modifier_follows(&self) -> bool {
        matches!(
            self.kind(),
            TokenKind::KwPublic
                | TokenKind::KwProtected
                | TokenKind::KwPrivate
                | TokenKind::KwReadonly
                | TokenKind::KwOverride
        ) && (is_identifier_like(self.nth_kind(1))
            || matches!(
                self.nth_kind(1),
                TokenKind::LBrace
                    | TokenKind::LBracket
                    | TokenKind::KwReadonly
                    | TokenKind::KwPublic
                    | TokenKind::KwProtected
                    | TokenKind::KwPrivate
                    | TokenKind::KwOverride
                    | TokenKind::DotDotDot
            ))
    }

    // ------------------------------------------------------------------
    // Arrow functions
    // ------------------------------------------------------------------

    /// Attempts every arrow-function form at an assignment start, returning
    /// `None` when the input is not an arrow so the caller parses a normal
    /// conditional expression.
    fn try_parse_arrow_function(&mut self, no_in: bool) -> Option<Expr> {
        let start = self.cur_start();

        // `ident => body`
        if is_identifier_like(self.kind())
            && self.nth_kind(1) == TokenKind::Arrow
            && !self.has_newline_before_nth(1)
        {
            return Some(self.parse_simple_arrow(start, false, no_in));
        }

        // `async ident => body`
        if self.at(TokenKind::KwAsync)
            && is_identifier_like(self.nth_kind(1))
            && self.nth_kind(2) == TokenKind::Arrow
            && !self.has_newline_before_nth(1)
            && !self.has_newline_before_nth(2)
        {
            self.bump();
            return Some(self.parse_simple_arrow(start, true, no_in));
        }

        // `( ... ) => ...` and `( ... ): T => ...`
        if self.at(TokenKind::LParen) {
            match self.paren_arrow_follow(true) {
                ArrowFollow::Arrow => return Some(self.parse_paren_arrow(start, false, no_in)),
                ArrowFollow::Colon => {
                    if let Some(arrow) = self.speculate_paren_arrow(start, false, no_in) {
                        return Some(arrow);
                    }
                }
                ArrowFollow::No => {}
            }
        }

        // `async ( ... ) => ...`
        if self.at(TokenKind::KwAsync)
            && self.nth_kind(1) == TokenKind::LParen
            && !self.has_newline_before_nth(1)
            && let Some(arrow) = self.speculate_async_paren_arrow(start, no_in)
        {
            return Some(arrow);
        }

        // `<T>( ... ) => ...` generic arrow (non-React TypeScript only).
        if self.at_less_like()
            && self.is_typescript()
            && !matches!(self.script_kind, ScriptKind::TypeScriptReact)
            && let Some(arrow) = self.speculate_generic_arrow(start, false, no_in)
        {
            return Some(arrow);
        }
        if self.at(TokenKind::KwAsync)
            && self.nth(1).kind() == TokenKind::LessThan
            && self.is_typescript()
            && !matches!(self.script_kind, ScriptKind::TypeScriptReact)
            && !self.has_newline_before_nth(1)
            && let Some(arrow) = self.speculate_generic_arrow(start, true, no_in)
        {
            return Some(arrow);
        }

        None
    }

    fn parse_simple_arrow(&mut self, start: Utf16Pos, is_async: bool, no_in: bool) -> Expr {
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: is_async,
            yield_reserved: false,
        };
        let param_start = self.cur_start();
        let token = self.bump();
        let name = self.with_keyword_context(keyword_context, |this| this.ident_from(token));
        let binding = self.node(param_start, BindingPattern::Identifier(name));
        let parameter = self.node(
            param_start,
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers::default(),
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        self.expect(TokenKind::Arrow, "expected `=>`");
        let body = self.parse_arrow_body(no_in, keyword_context);
        self.node(
            start,
            Expression::Arrow(ArrowFunction {
                is_async,
                type_parameters: None,
                parameters: vec![parameter],
                return_type: None,
                body,
            }),
        )
    }

    fn parse_paren_arrow(&mut self, start: Utf16Pos, is_async: bool, no_in: bool) -> Expr {
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: is_async,
            yield_reserved: false,
        };
        let parameters =
            self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
        let return_type = self.parse_optional_type_annotation();
        self.expect(TokenKind::Arrow, "expected `=>`");
        let body = self.parse_arrow_body(no_in, keyword_context);
        self.node(
            start,
            Expression::Arrow(ArrowFunction {
                is_async,
                type_parameters: None,
                parameters,
                return_type,
                body,
            }),
        )
    }

    fn parse_arrow_body(&mut self, no_in: bool, keyword_context: KeywordContext) -> FunctionBody {
        self.with_keyword_context(keyword_context, |this| {
            if this.at(TokenKind::LBrace) {
                FunctionBody::Block(this.parse_block())
            } else {
                FunctionBody::Expression(Box::new(this.parse_assignment_expression(no_in)))
            }
        })
    }

    fn speculate_paren_arrow(
        &mut self,
        start: Utf16Pos,
        is_async: bool,
        no_in: bool,
    ) -> Option<Expr> {
        let checkpoint = self.checkpoint();
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: is_async,
            yield_reserved: false,
        };
        let parameters =
            self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
        let return_type = self.parse_optional_type_annotation();
        if !self.at(TokenKind::Arrow) || self.has_newline_before() {
            self.rollback(checkpoint);
            return None;
        }
        self.bump();
        let body = self.parse_arrow_body(no_in, keyword_context);
        Some(self.node(
            start,
            Expression::Arrow(ArrowFunction {
                is_async,
                type_parameters: None,
                parameters,
                return_type,
                body,
            }),
        ))
    }

    fn speculate_async_paren_arrow(&mut self, start: Utf16Pos, no_in: bool) -> Option<Expr> {
        let checkpoint = self.checkpoint();
        self.bump(); // `async`
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: true,
            yield_reserved: false,
        };
        let parameters =
            self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
        let return_type = self.parse_optional_type_annotation();
        if !self.at(TokenKind::Arrow) || self.has_newline_before() {
            self.rollback(checkpoint);
            return None;
        }
        self.bump();
        let body = self.parse_arrow_body(no_in, keyword_context);
        Some(self.node(
            start,
            Expression::Arrow(ArrowFunction {
                is_async: true,
                type_parameters: None,
                parameters,
                return_type,
                body,
            }),
        ))
    }

    fn speculate_generic_arrow(
        &mut self,
        start: Utf16Pos,
        is_async: bool,
        no_in: bool,
    ) -> Option<Expr> {
        let checkpoint = self.checkpoint();
        if is_async {
            self.bump();
        }
        let type_parameters = self.parse_optional_type_parameters();
        if !self.at(TokenKind::LParen) {
            self.rollback(checkpoint);
            return None;
        }
        let keyword_context = KeywordContext {
            in_function: true,
            await_reserved: is_async,
            yield_reserved: false,
        };
        let parameters =
            self.with_keyword_context(keyword_context, |this| this.parse_parameter_list());
        let return_type = self.parse_optional_type_annotation();
        if !self.at(TokenKind::Arrow) || self.has_newline_before() {
            self.rollback(checkpoint);
            return None;
        }
        self.bump();
        let body = self.parse_arrow_body(no_in, keyword_context);
        Some(self.node(
            start,
            Expression::Arrow(ArrowFunction {
                is_async,
                type_parameters,
                parameters,
                return_type,
                body,
            }),
        ))
    }

    /// Determines whether a `(` begins an arrow by scanning to its matching
    /// `)` at the token level and inspecting what follows.
    fn paren_arrow_follow(&self, restrict_newline: bool) -> ArrowFollow {
        let mut index = self.cursor;
        let mut depth = 0i32;
        loop {
            if self.is_cancelled() {
                break;
            }
            let token = self.tokens.get(index).copied().unwrap_or(self.eof);
            match token.kind() {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        break;
                    }
                }
                TokenKind::EndOfFile => return ArrowFollow::No,
                _ => {}
            }
            index += 1;
            if index >= self.tokens.len() {
                return ArrowFollow::No;
            }
        }
        let close_end = self
            .tokens
            .get(index)
            .copied()
            .unwrap_or(self.eof)
            .range()
            .end()
            .get();
        let after = self.next_significant(index + 1);
        let after_token = self.tokens.get(after).copied().unwrap_or(self.eof);
        match after_token.kind() {
            TokenKind::Arrow => {
                // No LineTerminator may sit between an arrow's parameter list and
                // `=>` (a restricted production). Function types carry no such
                // restriction, so the type-position caller opts out.
                if restrict_newline
                    && self.newline_in_gap(close_end, after_token.range().start().get())
                {
                    ArrowFollow::No
                } else {
                    ArrowFollow::Arrow
                }
            }
            TokenKind::Colon => ArrowFollow::Colon,
            _ => ArrowFollow::No,
        }
    }

    // ------------------------------------------------------------------
    // Expression-to-target conversion
    // ------------------------------------------------------------------

    fn expression_to_target_for_assignment(
        &mut self,
        expr: Expr,
        simple: bool,
    ) -> AssignmentTargetNode {
        if simple {
            self.expression_to_target(expr)
        } else {
            // Compound assignment requires a simple (identifier/member) target.
            match expr.data() {
                Expression::Identifier(_) | Expression::Member(_) => {
                    self.expression_to_target(expr)
                }
                _ => {
                    let id = expr.id();
                    let range = expr.range();
                    Node::new(id, range, AssignmentTarget::Invalid(Box::new(expr)))
                }
            }
        }
    }

    fn expression_to_target(&mut self, expr: Expr) -> AssignmentTargetNode {
        let range = expr.range();
        let id = expr.id();
        let data = expr.into_data();
        match data {
            Expression::Identifier(name) => {
                Node::new(id, range, AssignmentTarget::Identifier(name))
            }
            Expression::Member(member) => {
                if member.optional {
                    let original = Node::new(id, range, Expression::Member(member));
                    return Node::new(id, range, AssignmentTarget::Invalid(Box::new(original)));
                }
                Node::new(
                    id,
                    range,
                    AssignmentTarget::Member(AssignmentMemberTarget {
                        object: member.object,
                        property: member.property,
                    }),
                )
            }
            Expression::Parenthesized(inner) => self.expression_to_target(*inner),
            Expression::Array(array) => {
                let target = self.array_literal_to_target(array, range);
                Node::new(id, range, target)
            }
            Expression::Object(object) => {
                let target = self.object_literal_to_target(object, range);
                Node::new(id, range, target)
            }
            other => {
                let original = Node::new(id, range, other);
                Node::new(id, range, AssignmentTarget::Invalid(Box::new(original)))
            }
        }
    }

    fn array_literal_to_target(
        &mut self,
        array: ArrayLiteral,
        _range: TextRange,
    ) -> AssignmentTarget {
        let mut elements = Vec::new();
        for element in array.elements {
            match element {
                ArrayElement::Elision => elements.push(AssignmentArrayElement::Elision),
                ArrayElement::Expression(expr) => {
                    let target = self.expression_to_target(*expr);
                    elements.push(AssignmentArrayElement::Target(target));
                }
                ArrayElement::Spread(_) => {
                    // A rest element has no array-target slot. Record a missing
                    // element so the checker can report it; the parser stays silent.
                    elements.push(AssignmentArrayElement::Missing(MissingNode::new(
                        NodeKind::MissingAssignmentTarget,
                    )));
                }
                ArrayElement::Missing(node) => {
                    elements.push(AssignmentArrayElement::Missing(node));
                }
            }
        }
        AssignmentTarget::Array(AssignmentArrayPattern { elements })
    }

    fn object_literal_to_target(
        &mut self,
        object: ObjectLiteral,
        range: TextRange,
    ) -> AssignmentTarget {
        let mut properties = Vec::new();
        for member in object.members {
            let (member_range, data) = (member.range(), member.into_data());
            match data {
                ObjectMember::Property(property) => {
                    let (target, initializer) = self.property_value_to_target(*property.value);
                    properties.push(AssignmentObjectProperty {
                        name: property.name,
                        target,
                        initializer,
                    });
                }
                ObjectMember::Spread(_) | ObjectMember::Method(_) | ObjectMember::Missing(_) => {
                    properties.push(AssignmentObjectProperty {
                        name: PropertyName::Missing(MissingNode::new(NodeKind::Identifier)),
                        target: self.node_at(
                            member_range,
                            AssignmentTarget::Missing(MissingNode::new(
                                NodeKind::MissingAssignmentTarget,
                            )),
                        ),
                        initializer: None,
                    });
                }
            }
        }
        let _ = range;
        AssignmentTarget::Object(AssignmentObjectPattern { properties })
    }

    /// Splits a property value into a target and an optional destructuring
    /// default, recovering the initializer folded into a shorthand assignment.
    fn property_value_to_target(
        &mut self,
        value: Expr,
    ) -> (AssignmentTargetNode, Option<Box<Expr>>) {
        if let Expression::Assignment(assignment) = value.data()
            && assignment.operator == AssignmentOperator::Assign
        {
            let id = value.id();
            let range = value.range();
            let Expression::Assignment(assignment) = value.into_data() else {
                unreachable!("assignment matched above");
            };
            let _ = (id, range);
            return (assignment.left, Some(assignment.right));
        }
        (self.expression_to_target(value), None)
    }
}

/// What follows a parenthesized head, deciding arrow disambiguation.
#[derive(Clone, Copy)]
enum ArrowFollow {
    Arrow,
    Colon,
    No,
}

// ---------------------------------------------------------------------------
// TypeScript types
// ---------------------------------------------------------------------------

impl Parser {
    fn parse_type(&mut self) -> Ty {
        if !self.enter() {
            return self.missing_type();
        }
        let type_node = self.parse_conditional_type();
        self.leave();
        type_node
    }

    fn parse_conditional_type(&mut self) -> Ty {
        let start = self.cur_start();
        let check_type = self.parse_union_type();
        if !self.at(TokenKind::KwExtends) {
            return check_type;
        }
        self.bump();
        let extends_type = self.parse_union_type();
        if self.eat(TokenKind::Question).is_none() {
            // A type parameter constraint in a malformed context: retain the
            // check type and leave recovery to the caller.
            self.error_here(EXPECTED_TOKEN, "expected `?` in a conditional type");
            return check_type;
        }
        let true_type = self.parse_type();
        self.expect(TokenKind::Colon, "expected `:`");
        let false_type = self.parse_type();
        self.node(
            start,
            TypeNode::Conditional(ConditionalType {
                check_type: Box::new(check_type),
                extends_type: Box::new(extends_type),
                true_type: Box::new(true_type),
                false_type: Box::new(false_type),
            }),
        )
    }

    fn parse_union_type(&mut self) -> Ty {
        let start = self.cur_start();
        let leading = self.eat(TokenKind::Pipe).is_some();
        let first = self.parse_intersection_type();
        if !leading && !self.at(TokenKind::Pipe) {
            return first;
        }
        let mut types = vec![first];
        while self.eat(TokenKind::Pipe).is_some() {
            if self.is_cancelled() {
                break;
            }
            types.push(self.parse_intersection_type());
        }
        self.node(start, TypeNode::Union(types))
    }

    fn parse_intersection_type(&mut self) -> Ty {
        let start = self.cur_start();
        let leading = self.eat(TokenKind::Amp).is_some();
        let first = self.parse_postfix_type();
        if !leading && !self.at(TokenKind::Amp) {
            return first;
        }
        let mut types = vec![first];
        while self.eat(TokenKind::Amp).is_some() {
            if self.is_cancelled() {
                break;
            }
            types.push(self.parse_postfix_type());
        }
        self.node(start, TypeNode::Intersection(types))
    }

    fn parse_postfix_type(&mut self) -> Ty {
        let operator_budget = MAX_DEPTH.saturating_sub(self.depth) as usize;
        let mut operators = Vec::new();
        let mut overflowed = false;
        while matches!(
            self.kind(),
            TokenKind::KwKeyof | TokenKind::KwUnique | TokenKind::KwReadonly
        ) {
            let start = self.cur_start();
            let operator = match self.kind() {
                TokenKind::KwKeyof => TypeOperator::Keyof,
                TokenKind::KwUnique => TypeOperator::Unique,
                _ => TypeOperator::Readonly,
            };
            if operators.len() < operator_budget {
                operators.push((start, operator));
            } else if !overflowed {
                self.error_here(
                    NESTING_TOO_DEEP,
                    "this construct is nested too deeply to parse",
                );
                overflowed = true;
            }
            self.bump();
        }

        let operator_depth = operators.len() as u32;
        self.depth += operator_depth;

        let start = self.cur_start();
        let mut type_node = self.parse_primary_type();
        loop {
            if self.is_cancelled() {
                break;
            }
            if self.at(TokenKind::LBracket) && !self.has_newline_before() {
                self.bump();
                if self.eat(TokenKind::RBracket).is_some() {
                    type_node = self.node(start, TypeNode::Array(Box::new(type_node)));
                } else {
                    let index_type = self.parse_type();
                    self.expect(TokenKind::RBracket, "expected `]`");
                    type_node = self.node(
                        start,
                        TypeNode::IndexedAccess(IndexedAccessType {
                            object_type: Box::new(type_node),
                            index_type: Box::new(index_type),
                        }),
                    );
                }
            } else {
                break;
            }
        }
        self.depth -= operator_depth;
        for (start, operator) in operators.into_iter().rev() {
            type_node = self.node(
                start,
                TypeNode::Operator {
                    operator,
                    operand: Box::new(type_node),
                },
            );
        }
        type_node
    }

    fn parse_primary_type(&mut self) -> Ty {
        let start = self.cur_start();
        let keyword = match self.kind() {
            TokenKind::KwAny => Some(KeywordType::Any),
            TokenKind::KwUnknown => Some(KeywordType::Unknown),
            TokenKind::KwNever => Some(KeywordType::Never),
            TokenKind::KwVoid => Some(KeywordType::Void),
            TokenKind::KwUndefined => Some(KeywordType::Undefined),
            TokenKind::KwNull => Some(KeywordType::Null),
            TokenKind::KwBoolean => Some(KeywordType::Boolean),
            TokenKind::KwNumber => Some(KeywordType::Number),
            TokenKind::KwBigint => Some(KeywordType::BigInt),
            TokenKind::KwString => Some(KeywordType::String),
            TokenKind::KwSymbol => Some(KeywordType::Symbol),
            TokenKind::KwObject => Some(KeywordType::Object),
            TokenKind::Identifier if self.cur_lexeme() == "intrinsic" => {
                Some(KeywordType::Intrinsic)
            }
            _ => None,
        };
        if let Some(keyword) = keyword {
            self.bump();
            return self.node(start, TypeNode::Keyword(keyword));
        }

        match self.kind() {
            TokenKind::KwThis => {
                self.bump();
                self.node(start, TypeNode::This)
            }
            TokenKind::StringLiteral => {
                let literal = self.parse_string_literal();
                self.node(start, TypeNode::Literal(TypeLiteral::String(literal)))
            }
            TokenKind::NumericLiteral => {
                let token = self.bump();
                let range = token.range();
                let literal = self.node_at(range, NumericLiteral::new(token));
                self.node(start, TypeNode::Literal(TypeLiteral::Number(literal)))
            }
            TokenKind::BigIntLiteral => {
                let token = self.bump();
                let range = token.range();
                let literal = self.node_at(range, BigIntLiteral::new(token));
                self.node(start, TypeNode::Literal(TypeLiteral::BigInt(literal)))
            }
            TokenKind::KwTrue | TokenKind::KwFalse => {
                let token = self.bump();
                let range = token.range();
                let literal = self.node_at(range, BooleanLiteral::new(token));
                self.node(start, TypeNode::Literal(TypeLiteral::Boolean(literal)))
            }
            TokenKind::Minus | TokenKind::Plus => {
                let operator = if self.at(TokenKind::Minus) {
                    UnaryOperator::Minus
                } else {
                    UnaryOperator::Plus
                };
                self.bump();
                let operand = self.parse_primary_type();
                self.node(
                    start,
                    TypeNode::Literal(TypeLiteral::Unary {
                        operator,
                        operand: Box::new(operand),
                    }),
                )
            }
            TokenKind::LBracket => self.parse_tuple_type(),
            TokenKind::LBrace => self.parse_object_or_mapped_type(),
            TokenKind::LParen => self.parse_parenthesized_or_function_type(),
            TokenKind::LessThan | TokenKind::LessLess => self.parse_generic_function_type(),
            TokenKind::KwNew => self.parse_constructor_type(false),
            TokenKind::KwAbstract if self.nth_kind(1) == TokenKind::KwNew => {
                self.bump();
                self.parse_constructor_type(true)
            }
            TokenKind::KwTypeof => {
                self.bump();
                let name = self.parse_entity_name();
                let type_arguments = if self.at_less_like() {
                    Some(self.parse_type_arguments())
                } else {
                    None
                };
                self.node(
                    start,
                    TypeNode::Query(TypeQuery {
                        name,
                        type_arguments,
                    }),
                )
            }
            TokenKind::KwInfer => {
                self.bump();
                let parameter = self.parse_type_parameter();
                self.node(start, TypeNode::Infer(InferType { parameter }))
            }
            TokenKind::KwImport => self.parse_import_type(start),
            TokenKind::NoSubstitutionTemplate | TokenKind::TemplateHead => {
                self.parse_template_literal_type(start)
            }
            TokenKind::KwAsserts => self.parse_asserts_predicate(start),
            kind if is_identifier_like(kind) => {
                let name = self.parse_entity_name();
                // `x is T` predicate in a return type.
                if self.eat(TokenKind::KwIs).is_some() {
                    let type_node = self.parse_type();
                    return self.node(
                        start,
                        TypeNode::Predicate(TypePredicate {
                            asserts: false,
                            parameter_name: name,
                            type_node: Some(Box::new(type_node)),
                        }),
                    );
                }
                let type_arguments = if self.at_less_like() {
                    Some(self.parse_type_arguments())
                } else {
                    None
                };
                self.node(
                    start,
                    TypeNode::Reference(TypeReference {
                        name,
                        type_arguments,
                    }),
                )
            }
            _ => {
                self.error_here(EXPECTED_TYPE, "expected a type");
                self.missing_type()
            }
        }
    }

    fn parse_tuple_type(&mut self) -> Ty {
        let start = self.cur_start();
        self.bump();
        let mut elements = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBracket) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let rest = self.eat(TokenKind::DotDotDot).is_some();
            // Named tuple element `name?: Type`.
            let (name, optional) = if is_identifier_like(self.kind())
                && (self.nth_kind(1) == TokenKind::Colon
                    || (self.nth_kind(1) == TokenKind::Question
                        && self.nth_kind(2) == TokenKind::Colon))
            {
                let token = self.bump();
                let name = Some(self.ident_from(token));
                let optional = self.eat(TokenKind::Question).is_some();
                self.expect(TokenKind::Colon, "expected `:`");
                (name, optional)
            } else {
                (None, false)
            };
            let type_node = self.parse_type();
            let optional = optional || self.eat(TokenKind::Question).is_some();
            elements.push(TupleElement {
                name,
                optional,
                rest,
                type_node: Box::new(type_node),
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a tuple type",
                );
            }
        }
        self.expect(TokenKind::RBracket, "expected `]`");
        self.node(
            start,
            TypeNode::Tuple(TupleType {
                readonly: false,
                elements,
            }),
        )
    }

    fn parse_object_or_mapped_type(&mut self) -> Ty {
        let start = self.cur_start();
        if self.looks_like_mapped_type() {
            return self.parse_mapped_type(start);
        }
        let members = self.parse_type_members();
        self.node(start, TypeNode::Object(ObjectType { members }))
    }

    fn looks_like_mapped_type(&self) -> bool {
        if !self.at(TokenKind::LBrace) {
            return false;
        }
        let mut n = 1;
        if matches!(self.nth_kind(n), TokenKind::Plus | TokenKind::Minus) {
            n += 1;
        }
        if self.nth_kind(n) == TokenKind::KwReadonly {
            n += 1;
        }
        self.nth_kind(n) == TokenKind::LBracket
            && is_identifier_like(self.nth_kind(n + 1))
            && self.nth_kind(n + 2) == TokenKind::KwIn
    }

    fn parse_mapped_type(&mut self, start: Utf16Pos) -> Ty {
        self.bump(); // `{`
        let readonly_modifier = self.parse_mapped_modifier(TokenKind::KwReadonly);
        self.expect(TokenKind::LBracket, "expected `[` in a mapped type");
        let parameter = self.parse_mapped_parameter();
        let name_type = if self.eat(TokenKind::KwAs).is_some() {
            Some(Box::new(self.parse_type()))
        } else {
            None
        };
        self.expect(TokenKind::RBracket, "expected `]`");
        let optional_modifier = self.parse_mapped_modifier(TokenKind::Question);
        let value_type = if self.eat(TokenKind::Colon).is_some() {
            Some(Box::new(self.parse_type()))
        } else {
            None
        };
        let _ = self.eat(TokenKind::Semicolon);
        self.expect(TokenKind::RBrace, "expected `}`");
        self.node(
            start,
            TypeNode::Mapped(MappedType {
                readonly_modifier,
                parameter,
                name_type,
                optional_modifier,
                value_type,
            }),
        )
    }

    fn parse_mapped_modifier(&mut self, marker: TokenKind) -> MappedModifier {
        if self.at(marker) {
            self.bump();
            return MappedModifier::Add;
        }
        if self.at(TokenKind::Plus) && self.nth_kind(1) == marker {
            self.bump();
            self.bump();
            return MappedModifier::Add;
        }
        if self.at(TokenKind::Minus) && self.nth_kind(1) == marker {
            self.bump();
            self.bump();
            return MappedModifier::Remove;
        }
        MappedModifier::Preserve
    }

    fn parse_mapped_parameter(&mut self) -> TypeParameterNode {
        let start = self.cur_start();
        let name = self.expect_identifier("expected a mapped type parameter");
        self.expect(TokenKind::KwIn, "expected `in`");
        let constraint = Some(Box::new(self.parse_type()));
        self.node(
            start,
            TypeParameter {
                name,
                variance: Variance::Invariant,
                constraint,
                default: None,
            },
        )
    }

    fn parse_parenthesized_or_function_type(&mut self) -> Ty {
        let start = self.cur_start();
        if matches!(self.paren_arrow_follow(false), ArrowFollow::Arrow) {
            let parameters = self.parse_function_type_parameters();
            self.expect(TokenKind::Arrow, "expected `=>`");
            let return_type = self.parse_type();
            return self.node(
                start,
                TypeNode::Function(FunctionType {
                    type_parameters: None,
                    parameters,
                    return_type: Box::new(return_type),
                    return_type_missing: false,
                }),
            );
        }
        self.bump();
        let inner = self.parse_type();
        self.expect(TokenKind::RParen, "expected `)`");
        self.node(start, TypeNode::Parenthesized(Box::new(inner)))
    }

    fn parse_generic_function_type(&mut self) -> Ty {
        let start = self.cur_start();
        let type_parameters = self.parse_optional_type_parameters();
        let parameters = self.parse_function_type_parameters();
        self.expect(TokenKind::Arrow, "expected `=>`");
        let return_type = self.parse_type();
        self.node(
            start,
            TypeNode::Function(FunctionType {
                type_parameters,
                parameters,
                return_type: Box::new(return_type),
                return_type_missing: false,
            }),
        )
    }

    fn parse_constructor_type(&mut self, is_abstract: bool) -> Ty {
        let start = self.cur_start();
        self.expect(TokenKind::KwNew, "expected `new`");
        let type_parameters = self.parse_optional_type_parameters();
        let parameters = self.parse_function_type_parameters();
        self.expect(TokenKind::Arrow, "expected `=>`");
        let return_type = self.parse_type();
        self.node(
            start,
            TypeNode::Constructor(ConstructorType {
                is_abstract,
                function: FunctionType {
                    type_parameters,
                    parameters,
                    return_type: Box::new(return_type),
                    return_type_missing: false,
                },
            }),
        )
    }

    fn parse_function_type_parameters(&mut self) -> Vec<FunctionTypeParameter> {
        self.expect(TokenKind::LParen, "expected `(`");
        let mut parameters = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RParen) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            let rest = self.eat(TokenKind::DotDotDot).is_some();
            // TypeScript reports parameter-property modifiers inside a
            // function type's parameter list semantically (TS2369, TS7006),
            // not syntactically, so skip modifier keywords and bind the
            // parameter name to the keyword that follows. This keeps
            // `function f(): (public B) => C {}` a function-type return
            // with an intact body instead of derailing into statement
            // recovery.
            while matches!(
                self.kind(),
                TokenKind::KwPublic
                    | TokenKind::KwPrivate
                    | TokenKind::KwProtected
                    | TokenKind::KwReadonly
                    | TokenKind::KwOverride
            ) && self.next_significant_starts_parameter_name()
            {
                self.bump();
            }
            let name = if is_identifier_like(self.kind()) || self.at(TokenKind::KwThis) {
                let token = self.bump();
                self.ident_from(token)
            } else if matches!(self.kind(), TokenKind::LBrace | TokenKind::LBracket) {
                self.skip_balanced_pattern();
                self.missing_ident()
            } else {
                self.error_here(EXPECTED_IDENTIFIER, "expected a parameter name");
                self.missing_ident()
            };
            let optional = self.eat(TokenKind::Question).is_some();
            let type_annotation = if let Some(annotation) = self.parse_optional_type_annotation() {
                annotation
            } else {
                self.missing_type_annotation()
            };
            parameters.push(FunctionTypeParameter {
                name,
                optional,
                rest,
                type_annotation,
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a function type",
                );
            }
        }
        self.expect(TokenKind::RParen, "expected `)`");
        parameters
    }

    /// Whether the next significant token after the cursor can begin a
    /// function-type parameter name (an identifier, `this`, or a destructuring
    /// pattern). Used to skip parameter-property modifier keywords without
    /// consuming a modifier that is itself the parameter name.
    fn next_significant_starts_parameter_name(&self) -> bool {
        let next = self.next_significant(self.cursor + 1);
        match self.tokens.get(next) {
            Some(token) => {
                matches!(
                    token.kind(),
                    TokenKind::KwThis | TokenKind::LBrace | TokenKind::LBracket
                ) || is_identifier_like(token.kind())
            }
            None => false,
        }
    }

    fn skip_balanced_pattern(&mut self) {
        let open = self.kind();
        let close = if open == TokenKind::LBrace {
            TokenKind::RBrace
        } else {
            TokenKind::RBracket
        };
        let mut depth = 0i32;
        while !self.at_eof() {
            if self.is_cancelled() {
                break;
            }
            if self.kind() == open {
                depth += 1;
            } else if self.kind() == close {
                depth = depth.saturating_sub(1);
                self.bump();
                if depth <= 0 {
                    return;
                }
                continue;
            }
            self.bump();
        }
    }

    fn parse_import_type(&mut self, start: Utf16Pos) -> Ty {
        self.bump();
        self.expect(TokenKind::LParen, "expected `(`");
        let argument = self.parse_string_literal();
        let attributes = if self.eat(TokenKind::Comma).is_some() {
            // `import("x", { with: {...} })`: the AST stores attributes only.
            if self.at(TokenKind::LBrace) {
                self.bump();
                let attrs = if self.at(TokenKind::KwWith)
                    || is_identifier_like(self.kind())
                        && matches!(self.cur_lexeme(), "with" | "assert")
                {
                    self.bump();
                    self.expect(TokenKind::Colon, "expected colon");
                    self.parse_attribute_object()
                } else {
                    self.error_here(EXPECTED_TOKEN, "expected with or assert");
                    ImportAttributes::default()
                };
                while !self.at_eof() && !self.at(TokenKind::RBrace) {
                    if self.is_cancelled() {
                        break;
                    }
                    self.bump();
                }
                self.expect(TokenKind::RBrace, "expected `}`");
                Some(attrs)
            } else {
                None
            }
        } else {
            None
        };
        self.expect(TokenKind::RParen, "expected `)`");
        let qualifier = if self.eat(TokenKind::Dot).is_some() {
            Some(self.parse_entity_name())
        } else {
            None
        };
        let type_arguments = if self.at_less_like() {
            Some(self.parse_type_arguments())
        } else {
            None
        };
        self.node(
            start,
            TypeNode::Import(ImportType {
                argument,
                qualifier,
                type_arguments,
                attributes,
            }),
        )
    }

    fn parse_attribute_object(&mut self) -> ImportAttributes {
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut entries = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let name = self.parse_module_export_name();
            self.expect(TokenKind::Colon, "expected `:`");
            let value = self.parse_string_literal();
            entries.push(ImportAttribute { name, value });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        ImportAttributes { entries }
    }

    fn parse_template_literal_type(&mut self, start: Utf16Pos) -> Ty {
        let mut elements = Vec::new();
        let mut types = Vec::new();
        if self.at(TokenKind::NoSubstitutionTemplate) {
            let token = self.bump();
            let range = token.range();
            elements.push(self.node_at(range, TemplateElement::new(token)));
        } else {
            let head = self.bump();
            let range = head.range();
            elements.push(self.node_at(range, TemplateElement::new(head)));
            loop {
                if self.is_cancelled() {
                    break;
                }
                types.push(self.parse_type());
                if self.at(TokenKind::TemplateMiddle) {
                    let token = self.bump();
                    let range = token.range();
                    elements.push(self.node_at(range, TemplateElement::new(token)));
                } else if self.at(TokenKind::TemplateTail) {
                    let token = self.bump();
                    let range = token.range();
                    elements.push(self.node_at(range, TemplateElement::new(token)));
                    break;
                } else {
                    self.error_here(EXPECTED_TOKEN, "expected a template continuation");
                    break;
                }
            }
        }
        self.node(
            start,
            TypeNode::TemplateLiteral(TemplateLiteralType { elements, types }),
        )
    }

    fn parse_asserts_predicate(&mut self, start: Utf16Pos) -> Ty {
        self.bump();
        let parameter_name = if self.at(TokenKind::KwThis) {
            let token = self.bump();
            EntityName::Identifier(self.ident_from(token))
        } else {
            self.parse_entity_name()
        };
        let type_node = if self.eat(TokenKind::KwIs).is_some() {
            Some(Box::new(self.parse_type()))
        } else {
            None
        };
        self.node(
            start,
            TypeNode::Predicate(TypePredicate {
                asserts: true,
                parameter_name,
                type_node,
            }),
        )
    }

    // ------------------------------------------------------------------
    // Type parameters, arguments, names, members
    // ------------------------------------------------------------------

    fn parse_optional_type_parameters(&mut self) -> Option<TypeParameterList> {
        if !self.at_less_like() {
            return None;
        }
        let range = self.cur().range();
        self.note_typescript_syntax(range);
        self.expect_type_open("expected `<`");
        let mut parameters = Vec::new();
        while !self.at_eof() && !self.at_greater_like() {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            parameters.push(self.parse_type_parameter());
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside type parameters",
                );
            }
        }
        self.expect_type_close("expected `>`");
        Some(TypeParameterList { parameters })
    }

    fn parse_type_parameter(&mut self) -> TypeParameterNode {
        let start = self.cur_start();
        // `in`/`out` are variance modifiers only when a type-parameter name
        // still follows; `out` is a contextual identifier, not a keyword. The
        // combined `in out` form is accepted for recovery even though current
        // TypeScript rejects it.
        let variance = if self.at(TokenKind::KwIn)
            && self.nth(1).kind() == TokenKind::Identifier
            && self.lexeme(self.nth(1)) == "out"
            && is_identifier_like(self.nth_kind(2))
        {
            self.bump();
            self.bump();
            Variance::InOut
        } else if self.at(TokenKind::KwIn) && is_identifier_like(self.nth_kind(1)) {
            self.bump();
            Variance::In
        } else if self.at(TokenKind::Identifier)
            && self.cur_lexeme() == "out"
            && is_identifier_like(self.nth_kind(1))
        {
            self.bump();
            Variance::Out
        } else {
            Variance::Invariant
        };
        let name = self.expect_identifier("expected a type parameter name");
        let constraint = if self.eat(TokenKind::KwExtends).is_some() {
            Some(Box::new(self.parse_type()))
        } else {
            None
        };
        let default = if self.eat(TokenKind::Eq).is_some() {
            Some(Box::new(self.parse_type()))
        } else {
            None
        };
        self.node(
            start,
            TypeParameter {
                name,
                variance,
                constraint,
                default,
            },
        )
    }

    fn parse_type_arguments(&mut self) -> TypeArgumentList {
        self.expect_type_open("expected `<`");
        let mut arguments = Vec::new();
        while !self.at_eof() && !self.at_greater_like() {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            arguments.push(self.parse_type());
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside type arguments",
                );
            }
        }
        self.expect_type_close("expected `>`");
        TypeArgumentList { arguments }
    }

    /// Speculative type arguments for `new`/heritage-like expression sites.
    fn try_parse_type_arguments_speculative(&mut self) -> Option<TypeArgumentList> {
        if !self.at_less_like() {
            return None;
        }
        let checkpoint = self.checkpoint();
        let diagnostics = self.diagnostics.len();
        let args = self.parse_type_arguments();
        if self.diagnostics.len() != diagnostics {
            self.rollback(checkpoint);
            return None;
        }
        Some(args)
    }

    /// Speculative type arguments that must be followed by a call or tagged
    /// template to avoid stealing a relational `<` expression.
    fn try_parse_type_arguments_for_call(&mut self) -> Option<TypeArgumentList> {
        if !self.at_less_like() {
            return None;
        }
        let checkpoint = self.checkpoint();
        let diagnostics = self.diagnostics.len();
        let args = self.parse_type_arguments();
        let follows = matches!(
            self.kind(),
            TokenKind::LParen | TokenKind::NoSubstitutionTemplate | TokenKind::TemplateHead
        );
        if !follows || self.diagnostics.len() != diagnostics {
            self.rollback(checkpoint);
            return None;
        }
        Some(args)
    }

    fn parse_entity_name(&mut self) -> EntityName {
        if !is_any_word(self.kind()) {
            self.error_here(EXPECTED_IDENTIFIER, "expected a type name");
            return EntityName::Missing(MissingNode::new(NodeKind::Identifier));
        }
        let token = self.bump();
        let mut name = EntityName::Identifier(self.ident_from(token));
        while self.eat(TokenKind::Dot).is_some() {
            if self.is_cancelled() {
                break;
            }
            let right = self.expect_identifier("expected a qualified name");
            name = EntityName::Qualified {
                left: Box::new(name),
                right,
            };
        }
        name
    }

    fn parse_type_members(&mut self) -> Vec<TypeMemberNode> {
        self.expect(TokenKind::LBrace, "expected `{`");
        let mut members = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBrace) {
            if self.is_cancelled() {
                break;
            }
            let before = self.cursor;
            members.push(self.parse_type_member());
            if self.eat(TokenKind::Semicolon).is_none()
                && self.eat(TokenKind::Comma).is_none()
                && !self.at(TokenKind::RBrace)
                && !self.has_newline_before()
            {
                self.error_here(EXPECTED_TOKEN, "expected `;` or `,`");
            }
            if self.cursor == before {
                let skipped = self.bump();
                self.error_at(
                    UNEXPECTED_TOKEN,
                    skipped.range(),
                    "this token was skipped inside a type body",
                );
            }
        }
        self.expect(TokenKind::RBrace, "expected `}`");
        members
    }

    fn parse_type_member(&mut self) -> TypeMemberNode {
        let start = self.cur_start();
        // Call signature `<T>(...): R` / `(...): R`.
        if self.at(TokenKind::LParen) || self.at_less_like() {
            let function = self.parse_function_type_signature(false);
            return self.node(start, TypeMember::Call(CallSignature { function }));
        }

        // Construct signature `new (...): T`.
        if self.at(TokenKind::KwNew)
            && matches!(self.nth_kind(1), TokenKind::LParen | TokenKind::LessThan)
        {
            self.bump();
            let function = self.parse_function_type_signature(true);
            return self.node(
                start,
                TypeMember::Construct(ConstructSignature {
                    function: ConstructorType {
                        is_abstract: false,
                        function,
                    },
                }),
            );
        }

        let readonly = self.eat(TokenKind::KwReadonly).is_some();
        if readonly {
            self.note_typescript_syntax(self.span_from(start));
        }

        // Index signature.
        if self.at(TokenKind::LBracket) && self.at_index_signature() {
            let parameters = self.parse_function_type_parameters_bracketed();
            let type_annotation = self.parse_optional_type_annotation().unwrap_or_else(|| {
                self.error_here(EXPECTED_TOKEN, "an index signature requires a type");
                self.missing_type_annotation()
            });
            return self.node(
                start,
                TypeMember::Index(TypeIndexSignature {
                    readonly,
                    parameters,
                    type_annotation,
                }),
            );
        }

        let name = self.parse_property_name();
        let optional = self.eat(TokenKind::Question).is_some();
        if self.at(TokenKind::LParen) || self.at_less_like() {
            let function = self.parse_function_type_signature(false);
            return self.node(
                start,
                TypeMember::Method(TypeMethodSignature {
                    name,
                    optional,
                    function,
                }),
            );
        }
        let type_annotation = self.parse_optional_type_annotation();
        self.node(
            start,
            TypeMember::Property(TypePropertySignature {
                readonly,
                name,
                optional,
                type_annotation,
            }),
        )
    }
    fn parse_function_type_signature(&mut self, constructor: bool) -> FunctionType {
        let type_parameters = self.parse_optional_type_parameters();
        let parameters = self.parse_function_type_parameters();
        let (return_type, return_type_missing) = if constructor {
            if self.eat(TokenKind::Colon).is_some() {
                (self.parse_type(), false)
            } else {
                (self.missing_type(), true)
            }
        } else if self.eat(TokenKind::Colon).is_some() || self.eat(TokenKind::Arrow).is_some() {
            (self.parse_type(), false)
        } else {
            (self.missing_type(), true)
        };
        FunctionType {
            type_parameters,
            parameters,
            return_type: Box::new(return_type),
            return_type_missing,
        }
    }

    fn parse_function_type_parameters_bracketed(&mut self) -> Vec<FunctionTypeParameter> {
        self.expect(TokenKind::LBracket, "expected `[` ");
        let mut parameters = Vec::new();
        while !self.at_eof() && !self.at(TokenKind::RBracket) {
            if self.is_cancelled() {
                break;
            }
            let rest = self.eat(TokenKind::DotDotDot).is_some();
            let name = self.expect_identifier("expected a parameter name");
            let optional = self.eat(TokenKind::Question).is_some();
            let type_annotation = self.parse_optional_type_annotation().unwrap_or_else(|| {
                self.error_here(EXPECTED_TOKEN, "expected a parameter type");
                self.missing_type_annotation()
            });
            parameters.push(FunctionTypeParameter {
                name,
                optional,
                rest,
                type_annotation,
            });
            if self.eat(TokenKind::Comma).is_none() {
                break;
            }
        }
        self.expect(TokenKind::RBracket, "expected `]`");
        parameters
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::DiagnosticSeverity;
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
        let projected = crate::diagnostics_parser::typescript_parse_code(
            await_code.code(),
            await_code.message(),
        )
        .expect("await code projects");
        assert_eq!(projected.as_str(), "TS1308");
        assert_eq!(
            crate::diagnostics_parser::typescript_parse_message(projected),
            Some(
                "'await' expressions are only allowed within async functions and at the top levels of modules."
            )
        );
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
                .filter(|diagnostic| {
                    matches!(diagnostic.code().as_str(), "BAMTS-P017" | "BAMTS-P018")
                })
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
        // of minting "expected a method body".
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
        let recovered = assert_clean(
            "enum Color { Red, Green = 2, Blue }\nnamespace A.B { export const x = 1; }",
        );
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
            SourceText::new("(x = <div>\u{1}</div>): T")
                .expect("test source fits the per-file budget"),
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
        let recovered =
            assert_clean("declare module \"y\" { module \"x\" { export interface I {} } }");
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
        let source = Arc::new(
            SourceText::new("var r = ++null;").expect("test source fits the per-file budget"),
        );
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
}
