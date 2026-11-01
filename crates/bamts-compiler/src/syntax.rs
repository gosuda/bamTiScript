//! Immutable, parser-owned syntax data.
//!
//! Child edges are owned values and public traversal only exposes shared borrows.
//! There are deliberately no parent links or interior-mutable caches: a parsed
//! [`SourceFile`] can be shared without changing the tree it describes.

use std::{borrow::Cow, sync::Arc};

use crate::diagnostic::Diagnostic;
use crate::source::{ScriptKind, SourceId, SourceText, TextRange};

/// A stable identity assigned by the parser to one AST node.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeId(u32);

impl NodeId {
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    pub const fn get(self) -> u32 {
        self.0
    }
}

/// A lexical token kind. This is intentionally separate from [`NodeKind`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TokenKind {
    EndOfFile,
    Unknown,
    Whitespace,
    LineComment,
    BlockComment,
    Shebang,
    Identifier,
    /// A reserved word spelled with escapes; valid only in IdentifierName contexts.
    EscapedReservedWord,
    /// An escaped `await` or `yield`, whose validity depends on parser context.
    EscapedContextualKeyword,
    PrivateIdentifier,
    NumericLiteral,
    BigIntLiteral,
    StringLiteral,
    RegularExpressionLiteral,
    NoSubstitutionTemplate,
    TemplateHead,
    TemplateMiddle,
    TemplateTail,
    KwAbstract,
    KwAccessor,
    KwAny,
    KwAs,
    KwAsserts,
    KwAsync,
    KwAwait,
    KwBigint,
    KwBoolean,
    KwBreak,
    KwCase,
    KwCatch,
    KwClass,
    KwConst,
    KwConstructor,
    KwContinue,
    KwDeclare,
    KwDebugger,
    KwDefault,
    KwDelete,
    KwDo,
    KwElse,
    KwEnum,
    KwExport,
    KwExtends,
    KwFalse,
    KwFinally,
    KwFor,
    KwFrom,
    KwFunction,
    KwGet,
    KwIf,
    KwImplements,
    KwImport,
    KwIn,
    KwInfer,
    KwInstanceof,
    KwInterface,
    KwIs,
    KwKeyof,
    KwLet,
    KwNamespace,
    KwNever,
    KwNew,
    KwNull,
    KwNumber,
    KwObject,
    KwOf,
    KwOverride,
    KwPackage,
    KwPrivate,
    KwProtected,
    KwPublic,
    KwReadonly,
    KwReturn,
    KwSatisfies,
    KwSet,
    KwStatic,
    KwString,
    KwSuper,
    KwSwitch,
    KwSymbol,
    KwThis,
    KwThrow,
    KwTrue,
    KwTry,
    KwType,
    KwTypeof,
    KwUndefined,
    KwUnique,
    KwUnknown,
    KwVar,
    KwVoid,
    KwWhile,
    KwWith,
    KwYield,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LParen,
    RParen,
    Dot,
    DotDotDot,
    Comma,
    Semicolon,
    Colon,
    Question,
    QuestionDot,
    QuestionQuestion,
    At,
    Arrow,
    Plus,
    Minus,
    Star,
    StarStar,
    Slash,
    Percent,
    PlusPlus,
    MinusMinus,
    LessThan,
    GreaterThan,
    LessThanEq,
    GreaterThanEq,
    LessLess,
    GreaterGreater,
    GreaterGreaterGreater,
    Eq,
    EqEq,
    EqEqEq,
    Bang,
    BangEq,
    BangEqEq,
    Amp,
    AmpAmp,
    Pipe,
    PipePipe,
    Caret,
    Tilde,
    PlusEq,
    MinusEq,
    StarEq,
    StarStarEq,
    SlashEq,
    PercentEq,
    LessLessEq,
    GreaterGreaterEq,
    GreaterGreaterGreaterEq,
    AmpEq,
    AmpAmpEq,
    PipeEq,
    PipePipeEq,
    CaretEq,
    QuestionQuestionEq,
}

/// Returns the StringValue of an identifier token spelling.
///
/// The scanner validates identifier escapes before parser-owned tokens reach
/// this layer. `None` keeps this helper total for synthetic tokens.
pub(crate) fn cook_identifier_text(text: &str) -> Option<Cow<'_, str>> {
    if !text.contains('\\') {
        return Some(Cow::Borrowed(text));
    }

    let mut chars = text.chars();
    let mut cooked = String::with_capacity(text.len());
    while let Some(character) = chars.next() {
        if character != '\\' {
            cooked.push(character);
            continue;
        }
        if chars.next()? != 'u' {
            return None;
        }

        let first = chars.next()?;
        let code_point = if first == '{' {
            let mut value = 0_u32;
            let mut has_digit = false;
            loop {
                let digit = chars.next()?;
                if digit == '}' {
                    break;
                }
                value = value.checked_mul(16)?.checked_add(digit.to_digit(16)?)?;
                has_digit = true;
            }
            if !has_digit {
                return None;
            }
            value
        } else {
            let mut value = first.to_digit(16)?;
            for _ in 1..4 {
                value = value
                    .checked_mul(16)?
                    .checked_add(chars.next()?.to_digit(16)?)?;
            }
            value
        };
        cooked.push(char::from_u32(code_point)?);
    }
    Some(Cow::Owned(cooked))
}

/// A grammar node kind. A value of this type can never name a token.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeKind {
    SourceFile,
    ImportDeclaration,
    ImportEqualsDeclaration,
    ImportSpecifier,
    ExportDeclaration,
    ExportSpecifier,
    VariableDeclaration,
    VariableDeclarator,
    FunctionDeclaration,
    ClassDeclaration,
    InterfaceDeclaration,
    TypeAliasDeclaration,
    EnumDeclaration,
    EnumMember,
    NamespaceDeclaration,
    BlockStatement,
    EmptyStatement,
    ExpressionStatement,
    IfStatement,
    SwitchStatement,
    SwitchCase,
    ForStatement,
    ForInStatement,
    ForOfStatement,
    WhileStatement,
    DoWhileStatement,
    TryStatement,
    CatchClause,
    WithStatement,
    LabeledStatement,
    BreakStatement,
    ContinueStatement,
    ReturnStatement,
    ThrowStatement,
    DebuggerStatement,
    DeclareStatement,
    MissingStatement,
    Identifier,
    PrivateIdentifier,
    StringLiteral,
    NumericLiteral,
    BigIntLiteral,
    BooleanLiteral,
    NullLiteral,
    RegexLiteral,
    TemplateElement,
    IdentifierExpression,
    ThisExpression,
    SuperExpression,
    LiteralExpression,
    ArrayExpression,
    ObjectExpression,
    FunctionExpression,
    ClassExpression,
    ArrowFunction,
    CallExpression,
    MemberExpression,
    NewExpression,
    AwaitExpression,
    YieldExpression,
    UnaryExpression,
    UpdateExpression,
    BinaryExpression,
    LogicalExpression,
    ConditionalExpression,
    AssignmentExpression,
    SequenceExpression,
    ParenthesizedExpression,
    AsExpression,
    SatisfiesExpression,
    TypeAssertionExpression,
    NonNullExpression,
    TaggedTemplateExpression,
    TemplateExpression,
    ImportExpression,
    MetaProperty,
    MissingExpression,
    JsxElement,
    JsxFragment,
    JsxSelfClosingElement,
    JsxOpeningElement,
    JsxClosingElement,
    JsxAttribute,
    JsxSpreadAttribute,
    JsxExpressionContainer,
    JsxSpreadChild,
    JsxText,
    BindingIdentifier,
    ObjectBindingPattern,
    ArrayBindingPattern,
    RestBindingPattern,
    AssignmentBindingPattern,
    MissingBindingPattern,
    MemberAssignmentTarget,
    IdentifierAssignmentTarget,
    ArrayAssignmentTarget,
    ObjectAssignmentTarget,
    MissingAssignmentTarget,
    Parameter,
    TypeAnnotation,
    KeywordType,
    LiteralType,
    TypeReference,
    UnionType,
    IntersectionType,
    ArrayType,
    TupleType,
    ObjectType,
    FunctionType,
    ConstructorType,
    TypeQuery,
    TypeOperator,
    IndexedAccessType,
    ConditionalType,
    MappedType,
    InferType,
    ImportType,
    TemplateLiteralType,
    ParenthesizedType,
    ThisType,
    TypePredicate,
    MissingType,
    TypeParameter,
    TypeMember,
    ClassMember,
    ObjectMember,
    Decorator,
    /// Appended after `Decorator`: `NodeKind` discriminants are append-only.
    InvalidAssignmentTarget,
}

/// The complete syntax-kind space, with token and node categories represented
/// by different variants instead of a shared integer namespace.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SyntaxKind {
    Token(TokenKind),
    Node(NodeKind),
}

impl SyntaxKind {
    pub const fn token(kind: TokenKind) -> Self {
        Self::Token(kind)
    }

    pub const fn node(kind: NodeKind) -> Self {
        Self::Node(kind)
    }

    pub const fn is_token(self) -> bool {
        matches!(self, Self::Token(_))
    }

    pub const fn is_node(self) -> bool {
        matches!(self, Self::Node(_))
    }
}

impl From<TokenKind> for SyntaxKind {
    fn from(kind: TokenKind) -> Self {
        Self::Token(kind)
    }
}

impl From<NodeKind> for SyntaxKind {
    fn from(kind: NodeKind) -> Self {
        Self::Node(kind)
    }
}

/// An immutable lexical token. Its lexeme stays in [`SourceText`], avoiding
/// one allocation and reference-counted handle per scanner token.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Token {
    kind: TokenKind,
    range: TextRange,
    missing: bool,
}

impl Token {
    pub const fn new(kind: TokenKind, range: TextRange) -> Self {
        Self {
            kind,
            range,
            missing: false,
        }
    }

    pub const fn missing(kind: TokenKind, range: TextRange) -> Self {
        Self {
            kind,
            range,
            missing: true,
        }
    }

    pub const fn kind(&self) -> TokenKind {
        self.kind
    }

    pub const fn syntax_kind(&self) -> SyntaxKind {
        SyntaxKind::Token(self.kind)
    }

    pub const fn range(&self) -> TextRange {
        self.range
    }

    pub const fn is_missing(&self) -> bool {
        self.missing
    }
}

/// Data stored in a typed AST node.
///
/// This trait lets [`Node`] derive its syntax kind from its closed payload
/// enum, so callers never supply a potentially mismatched `NodeKind`.
pub trait NodeData {
    fn node_kind(&self) -> NodeKind;
}

/// The common immutable header for every AST node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node<T> {
    id: NodeId,
    range: TextRange,
    data: T,
}

impl<T> Node<T> {
    pub fn new(id: NodeId, range: TextRange, data: T) -> Self {
        Self { id, range, data }
    }

    pub const fn id(&self) -> NodeId {
        self.id
    }

    pub const fn range(&self) -> TextRange {
        self.range
    }

    pub fn data(&self) -> &T {
        &self.data
    }

    pub fn into_data(self) -> T {
        self.data
    }
}

impl<T: NodeData> Node<T> {
    pub fn kind(&self) -> NodeKind {
        self.data.node_kind()
    }

    pub fn syntax_kind(&self) -> SyntaxKind {
        SyntaxKind::Node(self.kind())
    }
}

pub type StatementNode = Node<Statement>;
pub type Stmt = StatementNode;
pub type ExpressionNode = Node<Expression>;
pub type Expr = ExpressionNode;
pub type TypeNodeRef = Node<TypeNode>;
pub type Ty = TypeNodeRef;
pub type BindingPatternNode = Node<BindingPattern>;
pub type Pattern = BindingPatternNode;
pub type AssignmentTargetNode = Node<AssignmentTarget>;
pub type ParameterNode = Node<Parameter>;
pub type VariableDeclaratorNode = Node<VariableDeclarator>;
pub type BlockNode = Node<Block>;
pub type ClassMemberNode = Node<ClassMember>;
pub type ObjectMemberNode = Node<ObjectMember>;
pub type ImportSpecifierNode = Node<ImportSpecifier>;
pub type ExportSpecifierNode = Node<ExportSpecifier>;
pub type TypeAnnotationNode = Node<TypeAnnotation>;
pub type TypeParameterNode = Node<TypeParameter>;
pub type TypeMemberNode = Node<TypeMember>;
pub type CatchClauseNode = Node<CatchClause>;
pub type SwitchCaseNode = Node<SwitchCase>;
pub type EnumMemberNode = Node<EnumMember>;
pub type DecoratorNode = Node<Decorator>;

macro_rules! token_leaf {
    ($name:ident, $alias:ident, $kind:ident) => {
        #[derive(Clone, Debug, Eq, PartialEq)]
        pub struct $name {
            token: Token,
        }

        impl $name {
            pub fn new(token: Token) -> Self {
                Self { token }
            }

            pub fn token(&self) -> &Token {
                &self.token
            }
        }

        impl NodeData for $name {
            fn node_kind(&self) -> NodeKind {
                NodeKind::$kind
            }
        }

        pub type $alias = Node<$name>;
    };
}

token_leaf!(Identifier, IdentifierNode, Identifier);
token_leaf!(PrivateIdentifier, PrivateIdentifierNode, PrivateIdentifier);
token_leaf!(StringLiteral, StringLiteralNode, StringLiteral);
token_leaf!(NumericLiteral, NumericLiteralNode, NumericLiteral);
token_leaf!(BigIntLiteral, BigIntLiteralNode, BigIntLiteral);
token_leaf!(BooleanLiteral, BooleanLiteralNode, BooleanLiteral);
token_leaf!(NullLiteral, NullLiteralNode, NullLiteral);
token_leaf!(RegexLiteral, RegexLiteralNode, RegexLiteral);
token_leaf!(TemplateElement, TemplateElementNode, TemplateElement);
token_leaf!(JsxText, JsxTextNode, JsxText);

/// Recovery payload for an omitted grammar node. Its enclosing [`Node`] still
/// carries the insertion range and identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MissingNode {
    expected: NodeKind,
}

impl MissingNode {
    pub const fn new(expected: NodeKind) -> Self {
        Self { expected }
    }

    pub const fn expected(&self) -> NodeKind {
        self.expected
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Accessibility {
    Public,
    Protected,
    Private,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum Variance {
    In,
    Out,
    InOut,
    #[default]
    Invariant,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum VariableKind {
    Var,
    Let,
    Const,
    Using,
    AwaitUsing,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ImportSpecifierMode {
    Value,
    TypeOnly,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExportSpecifierMode {
    Value,
    TypeOnly,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnaryOperator {
    Plus,
    Minus,
    Not,
    BitNot,
    Typeof,
    Void,
    Delete,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UpdateOperator {
    Increment,
    Decrement,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponentiate,
    LeftShift,
    SignedRightShift,
    UnsignedRightShift,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    In,
    Instanceof,
    Equal,
    NotEqual,
    StrictEqual,
    StrictNotEqual,
    BitAnd,
    BitXor,
    BitOr,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LogicalOperator {
    And,
    Or,
    Nullish,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AssignmentOperator {
    Assign,
    AddAssign,
    SubtractAssign,
    MultiplyAssign,
    DivideAssign,
    RemainderAssign,
    ExponentiateAssign,
    LeftShiftAssign,
    SignedRightShiftAssign,
    UnsignedRightShiftAssign,
    BitAndAssign,
    BitXorAssign,
    BitOrAssign,
    LogicalAndAssign,
    LogicalOrAssign,
    NullishAssign,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum KeywordType {
    Any,
    Unknown,
    Never,
    Void,
    Undefined,
    Null,
    Boolean,
    Number,
    BigInt,
    String,
    Symbol,
    Object,
    Intrinsic,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TypeOperator {
    Keyof,
    Unique,
    Readonly,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MappedModifier {
    Preserve,
    Add,
    Remove,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ForOfMode {
    Sync,
    Async,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PropertyModifier {
    None,
    Get,
    Set,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DeclarationModifiers {
    pub accessibility: Option<Accessibility>,
    pub is_abstract: bool,
    pub is_declare: bool,
    pub is_override: bool,
    pub is_readonly: bool,
    pub is_static: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeParameter {
    pub name: IdentifierNode,
    pub variance: Variance,
    pub constraint: Option<Box<Ty>>,
    pub default: Option<Box<Ty>>,
}

impl NodeData for TypeParameter {
    fn node_kind(&self) -> NodeKind {
        NodeKind::TypeParameter
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeParameterList {
    pub parameters: Vec<TypeParameterNode>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeArgumentList {
    pub arguments: Vec<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAnnotation {
    pub type_node: Box<Ty>,
}

impl NodeData for TypeAnnotation {
    fn node_kind(&self) -> NodeKind {
        NodeKind::TypeAnnotation
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Decorator {
    pub expression: Box<Expr>,
}

impl NodeData for Decorator {
    fn node_kind(&self) -> NodeKind {
        NodeKind::Decorator
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ParameterModifiers {
    pub accessibility: Option<Accessibility>,
    pub is_readonly: bool,
    pub is_override: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    pub decorators: Vec<DecoratorNode>,
    pub modifiers: ParameterModifiers,
    pub binding: Pattern,
    pub optional: bool,
    pub type_annotation: Option<TypeAnnotationNode>,
    pub initializer: Option<Box<Expr>>,
}

impl NodeData for Parameter {
    fn node_kind(&self) -> NodeKind {
        NodeKind::Parameter
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PropertyName {
    Identifier(IdentifierNode),
    Private(PrivateIdentifierNode),
    String(StringLiteralNode),
    Number(NumericLiteralNode),
    Computed(Box<Expr>),
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModuleExportName {
    Identifier(IdentifierNode),
    String(StringLiteralNode),
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectBindingProperty {
    pub name: PropertyName,
    pub binding: Pattern,
    pub initializer: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectBindingPattern {
    pub properties: Vec<ObjectBindingProperty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArrayBindingElement {
    Binding(Pattern),
    Elision,
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayBindingPattern {
    pub elements: Vec<ArrayBindingElement>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RestBindingPattern {
    pub argument: Box<Pattern>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentBindingPattern {
    pub left: Box<Pattern>,
    pub right: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BindingPattern {
    Identifier(IdentifierNode),
    Object(ObjectBindingPattern),
    Array(ArrayBindingPattern),
    Rest(RestBindingPattern),
    Assignment(AssignmentBindingPattern),
    Missing(MissingNode),
}

impl NodeData for BindingPattern {
    fn node_kind(&self) -> NodeKind {
        match self {
            Self::Identifier(_) => NodeKind::BindingIdentifier,
            Self::Object(_) => NodeKind::ObjectBindingPattern,
            Self::Array(_) => NodeKind::ArrayBindingPattern,
            Self::Rest(_) => NodeKind::RestBindingPattern,
            Self::Assignment(_) => NodeKind::AssignmentBindingPattern,
            Self::Missing(_) => NodeKind::MissingBindingPattern,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MemberProperty {
    Named(IdentifierNode),
    Private(PrivateIdentifierNode),
    Computed(Box<Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemberExpression {
    pub object: Box<Expr>,
    pub property: MemberProperty,
    pub optional: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentMemberTarget {
    pub object: Box<Expr>,
    pub property: MemberProperty,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentObjectProperty {
    pub name: PropertyName,
    pub target: AssignmentTargetNode,
    pub initializer: Option<Box<Expr>>,
    /// `...target`, which collects the properties the others left. It has no
    /// name, and kept here it is visited with the targets around it.
    pub rest: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentObjectPattern {
    pub properties: Vec<AssignmentObjectProperty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssignmentArrayElement {
    Target(AssignmentTargetNode),
    Elision,
    Missing(MissingNode),
    /// `...target`, which collects what the iterator has left.
    Rest(AssignmentTargetNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentArrayPattern {
    pub elements: Vec<AssignmentArrayElement>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssignmentTarget {
    Identifier(IdentifierNode),
    Member(AssignmentMemberTarget),
    Object(AssignmentObjectPattern),
    Array(AssignmentArrayPattern),
    Missing(MissingNode),
    /// A parsed-but-invalid assignment target (e.g. `++null`, `null *= x`).
    /// The operand is retained so the checker can report TS18050 on a nullish
    /// value alongside the invalid-target diagnostic.
    Invalid(Box<Expr>),
}

impl NodeData for AssignmentTarget {
    fn node_kind(&self) -> NodeKind {
        match self {
            Self::Identifier(_) => NodeKind::IdentifierAssignmentTarget,
            Self::Member(_) => NodeKind::MemberAssignmentTarget,
            Self::Object(_) => NodeKind::ObjectAssignmentTarget,
            Self::Array(_) => NodeKind::ArrayAssignmentTarget,
            Self::Missing(_) => NodeKind::MissingAssignmentTarget,
            Self::Invalid(_) => NodeKind::InvalidAssignmentTarget,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VariableDeclarator {
    pub binding: Pattern,
    pub definite: bool,
    pub type_annotation: Option<TypeAnnotationNode>,
    pub initializer: Option<Box<Expr>>,
}

impl NodeData for VariableDeclarator {
    fn node_kind(&self) -> NodeKind {
        NodeKind::VariableDeclarator
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VariableDeclaration {
    pub range: TextRange,
    pub kind: VariableKind,
    pub declarations: Vec<VariableDeclaratorNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionLike {
    pub decorators: Vec<DecoratorNode>,
    pub name: Option<IdentifierNode>,
    pub is_async: bool,
    pub is_generator: bool,
    pub type_parameters: Option<TypeParameterList>,
    pub parameters: Vec<ParameterNode>,
    pub return_type: Option<TypeAnnotationNode>,
    pub body: Option<FunctionBody>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FunctionBody {
    Block(BlockNode),
    Expression(Box<Expr>),
    Missing(MissingNode),
}

impl FunctionBody {
    pub fn id(&self) -> Option<NodeId> {
        match self {
            Self::Block(block) => Some(block.id()),
            Self::Expression(expression) => Some(expression.id()),
            Self::Missing(_) => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionDeclaration {
    pub function: FunctionLike,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionExpression {
    pub function: FunctionLike,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrowFunction {
    pub is_async: bool,
    pub type_parameters: Option<TypeParameterList>,
    pub parameters: Vec<ParameterNode>,
    pub return_type: Option<TypeAnnotationNode>,
    pub body: FunctionBody,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructorDeclaration {
    pub decorators: Vec<DecoratorNode>,
    pub modifiers: DeclarationModifiers,
    pub parameters: Vec<ParameterNode>,
    pub body: BlockNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MethodDeclaration {
    pub modifiers: DeclarationModifiers,
    pub modifier: PropertyModifier,
    pub name: PropertyName,
    pub optional: bool,
    pub function: FunctionLike,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassProperty {
    pub decorators: Vec<DecoratorNode>,
    pub modifiers: DeclarationModifiers,
    pub name: PropertyName,
    pub optional: bool,
    pub definite: bool,
    pub type_annotation: Option<TypeAnnotationNode>,
    pub initializer: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AutoAccessor {
    pub decorators: Vec<DecoratorNode>,
    pub modifiers: DeclarationModifiers,
    pub name: PropertyName,
    pub type_annotation: Option<TypeAnnotationNode>,
    pub initializer: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexSignature {
    pub readonly: bool,
    pub parameters: Vec<ParameterNode>,
    pub type_annotation: TypeAnnotationNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClassMember {
    Constructor(ConstructorDeclaration),
    Method(MethodDeclaration),
    Property(ClassProperty),
    AutoAccessor(AutoAccessor),
    StaticBlock(BlockNode),
    IndexSignature(IndexSignature),
    Missing(MissingNode),
    /// A bare `;` between members. It declares nothing, and emit keeps it.
    Semicolon,
}

impl NodeData for ClassMember {
    fn node_kind(&self) -> NodeKind {
        NodeKind::ClassMember
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassHeritage {
    pub expression: Box<Expr>,
    pub type_arguments: Option<TypeArgumentList>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassDeclaration {
    pub decorators: Vec<DecoratorNode>,
    pub modifiers: DeclarationModifiers,
    pub name: Option<IdentifierNode>,
    pub type_parameters: Option<TypeParameterList>,
    pub extends: Option<ClassHeritage>,
    pub implements: Vec<Ty>,
    pub members: Vec<ClassMemberNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassExpression {
    pub class: ClassDeclaration,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceDeclaration {
    pub name: IdentifierNode,
    pub type_parameters: Option<TypeParameterList>,
    pub extends: Vec<TypeReference>,
    pub members: Vec<TypeMemberNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAliasDeclaration {
    pub name: IdentifierNode,
    pub type_parameters: Option<TypeParameterList>,
    pub type_node: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumDeclaration {
    pub is_const: bool,
    pub name: IdentifierNode,
    pub members: Vec<EnumMemberNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumMember {
    pub name: PropertyName,
    pub initializer: Option<Box<Expr>>,
}

impl NodeData for EnumMember {
    fn node_kind(&self) -> NodeKind {
        NodeKind::EnumMember
    }
}

/// Which keyword introduced an identifier-named namespace or module declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NamespaceKeyword {
    Namespace,
    Module,
}

impl NamespaceKeyword {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Namespace => "namespace",
            Self::Module => "module",
        }
    }
}

/// The name of a namespace or ambient module declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NamespaceName {
    /// `namespace A` / `module A` / dotted segments. Preserves the originating keyword.
    Identifier {
        name: IdentifierNode,
        keyword: NamespaceKeyword,
    },
    /// `declare module "pkg"` — ambient external module, type-only.
    StringLiteral(StringLiteralNode),
    /// `declare global` — global augmentation, type-only.
    Global { range: TextRange },
}

impl NamespaceName {
    #[must_use]
    pub fn range(&self) -> TextRange {
        match self {
            Self::Identifier { name, .. } => name.range(),
            Self::StringLiteral(literal) => literal.range(),
            Self::Global { range } => *range,
        }
    }

    #[must_use]
    pub fn as_identifier(&self) -> Option<&IdentifierNode> {
        match self {
            Self::Identifier { name, .. } => Some(name),
            Self::StringLiteral(_) | Self::Global { .. } => None,
        }
    }

    #[must_use]
    pub fn keyword(&self) -> Option<NamespaceKeyword> {
        match self {
            Self::Identifier { keyword, .. } => Some(*keyword),
            Self::StringLiteral(_) | Self::Global { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamespaceDeclaration {
    pub name: NamespaceName,
    pub body: BlockNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportClause {
    pub default: Option<IdentifierNode>,
    pub binding: Option<ImportBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImportBinding {
    Namespace(IdentifierNode),
    Named(Vec<ImportSpecifierNode>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportSpecifier {
    pub mode: ImportSpecifierMode,
    pub imported: ModuleExportName,
    pub local: IdentifierNode,
}

impl NodeData for ImportSpecifier {
    fn node_kind(&self) -> NodeKind {
        NodeKind::ImportSpecifier
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportAttribute {
    pub name: ModuleExportName,
    pub value: StringLiteralNode,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ImportAttributes {
    pub entries: Vec<ImportAttribute>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportDeclaration {
    pub type_only: bool,
    pub clause: Option<ImportClause>,
    pub source: StringLiteralNode,
    pub attributes: Option<ImportAttributes>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExternalModuleReference {
    Require(StringLiteralNode),
    Qualified(EntityName),
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportEqualsDeclaration {
    pub is_type_only: bool,
    pub local: IdentifierNode,
    pub reference: ExternalModuleReference,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExportDeclaration {
    Named(ExportNamedDeclaration),
    All(ExportAllDeclaration),
    Default(ExportDefaultDeclaration),
    Assignment(Box<Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExportNamedDeclaration {
    Declaration(Box<Stmt>),
    Specifiers {
        type_only: bool,
        specifiers: Vec<ExportSpecifierNode>,
        source: Option<StringLiteralNode>,
        attributes: Option<ImportAttributes>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExportAllDeclaration {
    pub type_only: bool,
    pub exported: Option<ModuleExportName>,
    pub source: StringLiteralNode,
    pub attributes: Option<ImportAttributes>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExportDefaultValue {
    Function(FunctionLike),
    Class(ClassDeclaration),
    Interface(InterfaceDeclaration),
    Expression(Box<Expr>),
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExportDefaultDeclaration {
    pub value: ExportDefaultValue,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExportSpecifier {
    pub mode: ExportSpecifierMode,
    pub local: ModuleExportName,
    pub exported: ModuleExportName,
}

impl NodeData for ExportSpecifier {
    fn node_kind(&self) -> NodeKind {
        NodeKind::ExportSpecifier
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub statements: Vec<Stmt>,
}

impl NodeData for Block {
    fn node_kind(&self) -> NodeKind {
        NodeKind::BlockStatement
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionStatement {
    pub expression: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IfStatement {
    pub test: Box<Expr>,
    pub consequent: Box<Stmt>,
    pub alternate: Option<Box<Stmt>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SwitchStatement {
    pub discriminant: Box<Expr>,
    pub cases: Vec<SwitchCaseNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SwitchCase {
    pub test: Option<Box<Expr>>,
    pub consequent: Vec<Stmt>,
}

impl NodeData for SwitchCase {
    fn node_kind(&self) -> NodeKind {
        NodeKind::SwitchCase
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForInitializer {
    Variable(VariableDeclaration),
    Expression(Box<Expr>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForStatement {
    pub initializer: Option<ForInitializer>,
    pub test: Option<Box<Expr>>,
    pub update: Option<Box<Expr>>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForBinding {
    Variable(VariableDeclaration),
    Target(AssignmentTargetNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForInStatement {
    pub binding: ForBinding,
    pub object: Box<Expr>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForOfStatement {
    pub mode: ForOfMode,
    pub binding: ForBinding,
    pub iterable: Box<Expr>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WhileStatement {
    pub test: Box<Expr>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DoWhileStatement {
    pub body: Box<Stmt>,
    pub test: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatchClause {
    pub binding: Option<Pattern>,
    pub body: BlockNode,
}

impl NodeData for CatchClause {
    fn node_kind(&self) -> NodeKind {
        NodeKind::CatchClause
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TryStatement {
    pub block: BlockNode,
    pub handler: Option<CatchClauseNode>,
    pub finalizer: Option<BlockNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WithStatement {
    pub object: Box<Expr>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabeledStatement {
    pub label: IdentifierNode,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JumpStatement {
    pub label: Option<IdentifierNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReturnStatement {
    pub argument: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ThrowStatement {
    pub argument: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Import(ImportDeclaration),
    ImportEquals(ImportEqualsDeclaration),
    Export(ExportDeclaration),
    Variable(VariableDeclaration),
    Function(FunctionDeclaration),
    Class(ClassDeclaration),
    Interface(InterfaceDeclaration),
    TypeAlias(TypeAliasDeclaration),
    Enum(EnumDeclaration),
    Namespace(NamespaceDeclaration),
    Declare(Box<Stmt>),
    Block(BlockNode),
    Empty,
    Expression(ExpressionStatement),
    If(IfStatement),
    Switch(SwitchStatement),
    For(ForStatement),
    ForIn(ForInStatement),
    ForOf(ForOfStatement),
    While(WhileStatement),
    DoWhile(DoWhileStatement),
    Try(TryStatement),
    With(WithStatement),
    Labeled(LabeledStatement),
    Break(JumpStatement),
    Continue(JumpStatement),
    Return(ReturnStatement),
    Throw(ThrowStatement),
    Debugger,
    Missing(MissingNode),
}

impl Statement {
    /// Type-only declarations are erasable without inspecting runtime syntax.
    pub const fn is_erasable(&self) -> bool {
        matches!(
            self,
            Self::Interface(_) | Self::TypeAlias(_) | Self::Declare(_)
        )
    }
}

impl NodeData for Statement {
    fn node_kind(&self) -> NodeKind {
        match self {
            Self::Import(_) => NodeKind::ImportDeclaration,
            Self::ImportEquals(_) => NodeKind::ImportEqualsDeclaration,
            Self::Export(_) => NodeKind::ExportDeclaration,
            Self::Variable(_) => NodeKind::VariableDeclaration,
            Self::Function(_) => NodeKind::FunctionDeclaration,
            Self::Class(_) => NodeKind::ClassDeclaration,
            Self::Interface(_) => NodeKind::InterfaceDeclaration,
            Self::TypeAlias(_) => NodeKind::TypeAliasDeclaration,
            Self::Enum(_) => NodeKind::EnumDeclaration,
            Self::Namespace(_) => NodeKind::NamespaceDeclaration,
            Self::Declare(_) => NodeKind::DeclareStatement,
            Self::Block(_) => NodeKind::BlockStatement,
            Self::Empty => NodeKind::EmptyStatement,
            Self::Expression(_) => NodeKind::ExpressionStatement,
            Self::If(_) => NodeKind::IfStatement,
            Self::Switch(_) => NodeKind::SwitchStatement,
            Self::For(_) => NodeKind::ForStatement,
            Self::ForIn(_) => NodeKind::ForInStatement,
            Self::ForOf(_) => NodeKind::ForOfStatement,
            Self::While(_) => NodeKind::WhileStatement,
            Self::DoWhile(_) => NodeKind::DoWhileStatement,
            Self::Try(_) => NodeKind::TryStatement,
            Self::With(_) => NodeKind::WithStatement,
            Self::Labeled(_) => NodeKind::LabeledStatement,
            Self::Break(_) => NodeKind::BreakStatement,
            Self::Continue(_) => NodeKind::ContinueStatement,
            Self::Return(_) => NodeKind::ReturnStatement,
            Self::Throw(_) => NodeKind::ThrowStatement,
            Self::Debugger => NodeKind::DebuggerStatement,
            Self::Missing(_) => NodeKind::MissingStatement,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Literal {
    String(StringLiteralNode),
    Number(NumericLiteralNode),
    BigInt(BigIntLiteralNode),
    Boolean(BooleanLiteralNode),
    Null(NullLiteralNode),
    Regex(RegexLiteralNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateLiteral {
    pub elements: Vec<TemplateElementNode>,
    pub expressions: Vec<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TaggedTemplateExpression {
    pub tag: Box<Expr>,
    pub template: TemplateLiteral,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpreadElement {
    pub argument: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArrayElement {
    Expression(Box<Expr>),
    Spread(SpreadElement),
    Elision,
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayLiteral {
    pub elements: Vec<ArrayElement>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectProperty {
    pub name: PropertyName,
    pub value: Box<Expr>,
    pub modifier: PropertyModifier,
    pub shorthand: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectMethod {
    pub name: PropertyName,
    pub modifier: PropertyModifier,
    pub function: FunctionLike,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ObjectMember {
    Property(ObjectProperty),
    Method(ObjectMethod),
    Spread(SpreadElement),
    Missing(MissingNode),
}

impl NodeData for ObjectMember {
    fn node_kind(&self) -> NodeKind {
        NodeKind::ObjectMember
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectLiteral {
    pub members: Vec<ObjectMemberNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallArgument {
    Expression(Box<Expr>),
    Spread(SpreadElement),
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallExpression {
    pub callee: Box<Expr>,
    pub optional: bool,
    pub type_arguments: Option<TypeArgumentList>,
    pub arguments: Vec<CallArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NewExpression {
    pub callee: Box<Expr>,
    pub type_arguments: Option<TypeArgumentList>,
    pub arguments: Vec<CallArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AwaitExpression {
    pub argument: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct YieldExpression {
    pub delegate: bool,
    pub argument: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub argument: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UpdateExpression {
    pub operator: UpdateOperator,
    pub argument: Box<AssignmentTargetNode>,
    pub prefix: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LogicalExpression {
    pub operator: LogicalOperator,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionalExpression {
    pub test: Box<Expr>,
    pub consequent: Box<Expr>,
    pub alternate: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssignmentExpression {
    pub operator: AssignmentOperator,
    pub left: AssignmentTargetNode,
    pub right: Box<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SequenceExpression {
    pub expressions: Vec<Expr>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AsExpression {
    pub expression: Box<Expr>,
    pub type_node: Option<Box<Ty>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SatisfiesExpression {
    pub expression: Box<Expr>,
    pub type_node: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAssertionExpression {
    pub expression: Box<Expr>,
    pub type_node: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonNullExpression {
    pub expression: Box<Expr>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MetaProperty {
    NewTarget,
    ImportMeta,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportExpression {
    pub source: Box<Expr>,
    pub options: Option<Box<Expr>>,
}

// ---------------------------------------------------------------------------
// JSX
// ---------------------------------------------------------------------------

/// A JSX element name: `Foo`, a dotted chain `Foo.Bar`, or a namespaced
/// `ns:Foo`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsxElementName {
    Identifier(IdentifierNode),
    Member(JsxMemberName),
    Namespace(JsxNamespacedName),
}

/// A dotted JSX name `object.property`; `object` is itself a name so chains
/// like `A.B.C` nest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxMemberName {
    pub object: Box<JsxElementName>,
    pub property: IdentifierNode,
}

/// A namespaced JSX name `namespace:name`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxNamespacedName {
    pub namespace: IdentifierNode,
    pub name: IdentifierNode,
}

/// A JSX attribute name: a bare identifier or a namespaced `ns:name`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsxAttributeName {
    Identifier(IdentifierNode),
    Namespace(JsxNamespacedName),
}

/// The value bound to a JSX attribute after `=`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsxAttributeInitializer {
    String(StringLiteralNode),
    Expression(JsxExpressionContainerNode),
}

/// A single JSX attribute: boolean `name`, `name="value"`, or `name={expr}`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxAttribute {
    pub name: JsxAttributeName,
    pub initializer: Option<JsxAttributeInitializer>,
}

impl NodeData for JsxAttribute {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxAttribute
    }
}

pub type JsxAttributeNode = Node<JsxAttribute>;

/// A spread attribute `{...expr}`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxSpreadAttribute {
    pub expression: Box<Expr>,
}

impl NodeData for JsxSpreadAttribute {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxSpreadAttribute
    }
}

pub type JsxSpreadAttributeNode = Node<JsxSpreadAttribute>;

/// One item in a JSX opening tag's attribute list.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsxAttributeItem {
    Attribute(JsxAttributeNode),
    Spread(JsxSpreadAttributeNode),
}

/// A JSX opening tag `<name attrs>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxOpeningElement {
    pub name: JsxElementName,
    pub attributes: Vec<JsxAttributeItem>,
}

impl NodeData for JsxOpeningElement {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxOpeningElement
    }
}

pub type JsxOpeningElementNode = Node<JsxOpeningElement>;

/// A JSX closing tag `</name>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxClosingElement {
    pub name: JsxElementName,
}

impl NodeData for JsxClosingElement {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxClosingElement
    }
}

pub type JsxClosingElementNode = Node<JsxClosingElement>;

/// A `{expr}` expression container used for attribute values and children. The
/// expression is absent for an empty `{}` container.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxExpressionContainer {
    pub expression: Option<Box<Expr>>,
}

impl NodeData for JsxExpressionContainer {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxExpressionContainer
    }
}

pub type JsxExpressionContainerNode = Node<JsxExpressionContainer>;

/// A `{...expr}` spread child.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxSpreadChild {
    pub expression: Box<Expr>,
}

impl NodeData for JsxSpreadChild {
    fn node_kind(&self) -> NodeKind {
        NodeKind::JsxSpreadChild
    }
}

pub type JsxSpreadChildNode = Node<JsxSpreadChild>;

/// A child of a JSX element or fragment. `Element` carries a nested
/// [`Expression::JsxElement`], [`Expression::JsxFragment`], or
/// [`Expression::JsxSelfClosingElement`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JsxChild {
    Text(JsxTextNode),
    ExpressionContainer(JsxExpressionContainerNode),
    Spread(JsxSpreadChildNode),
    Element(Box<Expr>),
}

/// A balanced JSX element `<name>children</name>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxElement {
    pub opening: JsxOpeningElementNode,
    pub children: Vec<JsxChild>,
    pub closing: JsxClosingElementNode,
}

/// A self-closing JSX element `<name attrs />`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxSelfClosingElement {
    pub name: JsxElementName,
    pub attributes: Vec<JsxAttributeItem>,
}

/// A JSX fragment `<>children</>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsxFragment {
    pub children: Vec<JsxChild>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expression {
    Identifier(IdentifierNode),
    This,
    Super,
    Literal(Literal),
    Template(TemplateLiteral),
    TaggedTemplate(TaggedTemplateExpression),
    Array(ArrayLiteral),
    Object(ObjectLiteral),
    Function(FunctionExpression),
    Class(ClassExpression),
    Arrow(ArrowFunction),
    Call(CallExpression),
    Member(MemberExpression),
    New(NewExpression),
    Await(AwaitExpression),
    Yield(YieldExpression),
    Unary(UnaryExpression),
    Update(UpdateExpression),
    Binary(BinaryExpression),
    Logical(LogicalExpression),
    Conditional(ConditionalExpression),
    Assignment(AssignmentExpression),
    Sequence(SequenceExpression),
    Parenthesized(Box<Expr>),
    As(AsExpression),
    Satisfies(SatisfiesExpression),
    TypeAssertion(TypeAssertionExpression),
    NonNull(NonNullExpression),
    Import(ImportExpression),
    Meta(MetaProperty),
    JsxElement(JsxElement),
    JsxFragment(JsxFragment),
    JsxSelfClosingElement(JsxSelfClosingElement),
    Missing(MissingNode),
}

impl NodeData for Expression {
    fn node_kind(&self) -> NodeKind {
        match self {
            Self::Identifier(_) => NodeKind::IdentifierExpression,
            Self::This => NodeKind::ThisExpression,
            Self::Super => NodeKind::SuperExpression,
            Self::Literal(_) => NodeKind::LiteralExpression,
            Self::Template(_) => NodeKind::TemplateExpression,
            Self::TaggedTemplate(_) => NodeKind::TaggedTemplateExpression,
            Self::Array(_) => NodeKind::ArrayExpression,
            Self::Object(_) => NodeKind::ObjectExpression,
            Self::Function(_) => NodeKind::FunctionExpression,
            Self::Class(_) => NodeKind::ClassExpression,
            Self::Arrow(_) => NodeKind::ArrowFunction,
            Self::Call(_) => NodeKind::CallExpression,
            Self::Member(_) => NodeKind::MemberExpression,
            Self::New(_) => NodeKind::NewExpression,
            Self::Await(_) => NodeKind::AwaitExpression,
            Self::Yield(_) => NodeKind::YieldExpression,
            Self::Unary(_) => NodeKind::UnaryExpression,
            Self::Update(_) => NodeKind::UpdateExpression,
            Self::Binary(_) => NodeKind::BinaryExpression,
            Self::Logical(_) => NodeKind::LogicalExpression,
            Self::Conditional(_) => NodeKind::ConditionalExpression,
            Self::Assignment(_) => NodeKind::AssignmentExpression,
            Self::Sequence(_) => NodeKind::SequenceExpression,
            Self::Parenthesized(_) => NodeKind::ParenthesizedExpression,
            Self::As(_) => NodeKind::AsExpression,
            Self::Satisfies(_) => NodeKind::SatisfiesExpression,
            Self::TypeAssertion(_) => NodeKind::TypeAssertionExpression,
            Self::NonNull(_) => NodeKind::NonNullExpression,
            Self::Import(_) => NodeKind::ImportExpression,
            Self::Meta(_) => NodeKind::MetaProperty,
            Self::JsxElement(_) => NodeKind::JsxElement,
            Self::JsxFragment(_) => NodeKind::JsxFragment,
            Self::JsxSelfClosingElement(_) => NodeKind::JsxSelfClosingElement,
            Self::Missing(_) => NodeKind::MissingExpression,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EntityName {
    Identifier(IdentifierNode),
    Qualified {
        left: Box<EntityName>,
        right: IdentifierNode,
    },
    Missing(MissingNode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeReference {
    pub name: EntityName,
    pub type_arguments: Option<TypeArgumentList>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeLiteral {
    String(StringLiteralNode),
    Number(NumericLiteralNode),
    BigInt(BigIntLiteralNode),
    Boolean(BooleanLiteralNode),
    Null(NullLiteralNode),
    Unary {
        operator: UnaryOperator,
        operand: Box<Ty>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleElement {
    pub name: Option<IdentifierNode>,
    pub optional: bool,
    pub rest: bool,
    pub type_node: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleType {
    pub readonly: bool,
    pub elements: Vec<TupleElement>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionTypeParameter {
    pub name: IdentifierNode,
    pub optional: bool,
    pub rest: bool,
    pub type_annotation: TypeAnnotationNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionType {
    pub type_parameters: Option<TypeParameterList>,
    pub parameters: Vec<FunctionTypeParameter>,
    pub return_type: Box<Ty>,
    pub return_type_missing: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructorType {
    pub is_abstract: bool,
    pub function: FunctionType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeQuery {
    pub name: EntityName,
    pub type_arguments: Option<TypeArgumentList>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedAccessType {
    pub object_type: Box<Ty>,
    pub index_type: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConditionalType {
    pub check_type: Box<Ty>,
    pub extends_type: Box<Ty>,
    pub true_type: Box<Ty>,
    pub false_type: Box<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MappedType {
    pub readonly_modifier: MappedModifier,
    pub parameter: TypeParameterNode,
    pub name_type: Option<Box<Ty>>,
    pub optional_modifier: MappedModifier,
    pub value_type: Option<Box<Ty>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InferType {
    pub parameter: TypeParameterNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportType {
    pub argument: StringLiteralNode,
    pub qualifier: Option<EntityName>,
    pub type_arguments: Option<TypeArgumentList>,
    pub attributes: Option<ImportAttributes>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateLiteralType {
    pub elements: Vec<TemplateElementNode>,
    pub types: Vec<Ty>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypePredicate {
    pub asserts: bool,
    pub parameter_name: EntityName,
    pub type_node: Option<Box<Ty>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypePropertySignature {
    pub readonly: bool,
    pub name: PropertyName,
    pub optional: bool,
    pub type_annotation: Option<TypeAnnotationNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeMethodSignature {
    pub name: PropertyName,
    pub optional: bool,
    pub function: FunctionType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallSignature {
    pub function: FunctionType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstructSignature {
    pub function: ConstructorType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeIndexSignature {
    pub readonly: bool,
    pub parameters: Vec<FunctionTypeParameter>,
    pub type_annotation: TypeAnnotationNode,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeMember {
    Property(TypePropertySignature),
    Method(TypeMethodSignature),
    Call(CallSignature),
    Construct(ConstructSignature),
    Index(TypeIndexSignature),
    Missing(MissingNode),
}

impl NodeData for TypeMember {
    fn node_kind(&self) -> NodeKind {
        NodeKind::TypeMember
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectType {
    pub members: Vec<TypeMemberNode>,
}

/// Type syntax is kept in this closed enum so erasure never has to inspect a
/// runtime expression variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeNode {
    Keyword(KeywordType),
    Literal(TypeLiteral),
    Reference(TypeReference),
    Union(Vec<Ty>),
    Intersection(Vec<Ty>),
    Array(Box<Ty>),
    Tuple(TupleType),
    Object(ObjectType),
    Function(FunctionType),
    Constructor(ConstructorType),
    Query(TypeQuery),
    Operator {
        operator: TypeOperator,
        operand: Box<Ty>,
    },
    IndexedAccess(IndexedAccessType),
    Conditional(ConditionalType),
    Mapped(MappedType),
    Infer(InferType),
    Import(ImportType),
    TemplateLiteral(TemplateLiteralType),
    Parenthesized(Box<Ty>),
    This,
    Predicate(TypePredicate),
    Missing(MissingNode),
}

impl NodeData for TypeNode {
    fn node_kind(&self) -> NodeKind {
        match self {
            Self::Keyword(_) => NodeKind::KeywordType,
            Self::Literal(_) => NodeKind::LiteralType,
            Self::Reference(_) => NodeKind::TypeReference,
            Self::Union(_) => NodeKind::UnionType,
            Self::Intersection(_) => NodeKind::IntersectionType,
            Self::Array(_) => NodeKind::ArrayType,
            Self::Tuple(_) => NodeKind::TupleType,
            Self::Object(_) => NodeKind::ObjectType,
            Self::Function(_) => NodeKind::FunctionType,
            Self::Constructor(_) => NodeKind::ConstructorType,
            Self::Query(_) => NodeKind::TypeQuery,
            Self::Operator { .. } => NodeKind::TypeOperator,
            Self::IndexedAccess(_) => NodeKind::IndexedAccessType,
            Self::Conditional(_) => NodeKind::ConditionalType,
            Self::Mapped(_) => NodeKind::MappedType,
            Self::Infer(_) => NodeKind::InferType,
            Self::Import(_) => NodeKind::ImportType,
            Self::TemplateLiteral(_) => NodeKind::TemplateLiteralType,
            Self::Parenthesized(_) => NodeKind::ParenthesizedType,
            Self::This => NodeKind::ThisType,
            Self::Predicate(_) => NodeKind::TypePredicate,
            Self::Missing(_) => NodeKind::MissingType,
        }
    }
}

/// The immutable parser product. Diagnostics retain parser order by value;
/// callers cannot mutate the tree, token stream, or diagnostics through this
/// API.
pub struct SourceFile {
    id: NodeId,
    range: TextRange,
    source_id: SourceId,
    script_kind: ScriptKind,
    source: Arc<SourceText>,
    tokens: Vec<Token>,
    statements: Vec<Stmt>,
    eof: Token,
    diagnostics: Vec<Diagnostic>,
}

impl SourceFile {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        id: NodeId,
        source_id: SourceId,
        script_kind: ScriptKind,
        range: TextRange,
        source: Arc<SourceText>,
        tokens: Vec<Token>,
        statements: Vec<Stmt>,
        eof: Token,
        diagnostics: Vec<Diagnostic>,
    ) -> Self {
        Self {
            id,
            range,
            source_id,
            script_kind,
            source,
            tokens,
            statements,
            eof,
            diagnostics,
        }
    }

    pub const fn id(&self) -> NodeId {
        self.id
    }

    pub const fn kind(&self) -> NodeKind {
        NodeKind::SourceFile
    }

    pub const fn syntax_kind(&self) -> SyntaxKind {
        SyntaxKind::Node(NodeKind::SourceFile)
    }

    pub const fn range(&self) -> TextRange {
        self.range
    }

    pub const fn source_id(&self) -> SourceId {
        self.source_id
    }

    pub const fn script_kind(&self) -> ScriptKind {
        self.script_kind
    }

    pub fn source_text(&self) -> &SourceText {
        &self.source
    }

    /// Non-EOF source tokens in lexical order.
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// Returns the zero-copy lexeme for a token range in this source file.
    ///
    /// `None` identifies a range that is not a valid UTF-16 slice of this
    /// file, which cannot arise from a parser-produced token.
    pub fn token_text(&self, token: &Token) -> Option<&str> {
        if token.is_missing() {
            return Some("");
        }

        let range = token.range();
        let start = self.source.utf16_to_byte(range.start()).ok()?;
        let end = self.source.utf16_to_byte(range.end()).ok()?;
        self.source.as_str().get(start..end)
    }

    /// Returns the cooked identity of an identifier token.
    pub fn identifier_text(&self, token: &Token) -> Option<Cow<'_, str>> {
        cook_identifier_text(self.token_text(token)?)
    }

    pub fn eof(&self) -> &Token {
        &self.eof
    }

    pub fn statements(&self) -> &[Stmt] {
        &self.statements
    }

    /// Parser diagnostics in the parser's stable source order.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::source::Utf16Pos;

    #[test]
    fn identifier_text_borrows_plain_and_cooks_escaped_names() {
        assert!(matches!(
            cook_identifier_text("plain"),
            Some(Cow::Borrowed("plain"))
        ));
        assert_eq!(
            cook_identifier_text("\\u0061\\u{62}"),
            Some(Cow::Owned("ab".to_owned()))
        );
        assert_eq!(
            cook_identifier_text("\\u{00000061}"),
            Some(Cow::Owned("a".to_owned()))
        );
        assert_eq!(cook_identifier_text("\\u{}"), None);
        assert_eq!(cook_identifier_text("\\u{110000}"), None);
    }

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered test range")
    }

    #[test]
    fn token_and_node_categories_stay_distinct() {
        let token = Token::new(TokenKind::Identifier, range(0, 1));
        let identifier = Node::new(NodeId::new(1), range(0, 1), Identifier::new(token));
        let expression = Node::new(
            NodeId::new(2),
            range(0, 1),
            Expression::Identifier(identifier),
        );
        let missing = Token::missing(TokenKind::RParen, range(1, 1));

        assert_eq!(
            token.syntax_kind(),
            SyntaxKind::Token(TokenKind::Identifier)
        );
        assert_eq!(
            expression.syntax_kind(),
            SyntaxKind::Node(NodeKind::IdentifierExpression)
        );
        assert!(token.syntax_kind().is_token());
        assert!(expression.syntax_kind().is_node());
        assert!(missing.is_missing());
        assert_eq!(missing.kind(), TokenKind::RParen);
    }

    #[test]
    fn nodes_cover_their_nested_ranges() {
        let name = Node::new(
            NodeId::new(2),
            range(4, 5),
            Identifier::new(Token::new(TokenKind::Identifier, range(4, 5))),
        );
        let binding = Node::new(
            NodeId::new(3),
            range(4, 5),
            BindingPattern::Identifier(name),
        );
        let declarator = Node::new(
            NodeId::new(4),
            range(4, 9),
            VariableDeclarator {
                binding,
                definite: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let statement = Node::new(
            NodeId::new(1),
            range(0, 9),
            Statement::Variable(VariableDeclaration {
                range: range(0, 9),
                kind: VariableKind::Let,
                declarations: vec![declarator],
            }),
        );

        assert_eq!(statement.range().start().get(), 0);
        assert_eq!(statement.range().end().get(), 9);
        assert_eq!(statement.kind(), NodeKind::VariableDeclaration);
    }

    #[test]
    fn source_file_owns_recovered_nodes_and_diagnostics() {
        let missing = Node::new(
            NodeId::new(1),
            range(4, 4),
            Expression::Missing(MissingNode::new(NodeKind::IdentifierExpression)),
        );
        let statement = Node::new(
            NodeId::new(2),
            range(0, 5),
            Statement::Expression(ExpressionStatement {
                expression: Box::new(missing),
            }),
        );
        let source = std::sync::Arc::new(
            SourceText::new("let ;").expect("test source fits the per-file budget"),
        );
        let eof = Token::new(TokenKind::EndOfFile, range(5, 5));
        let file = SourceFile::new(
            NodeId::new(0),
            SourceId::new(7),
            ScriptKind::TypeScript,
            range(0, 5),
            source,
            vec![Token::new(TokenKind::KwLet, range(0, 3))],
            vec![statement],
            eof,
            Vec::new(),
        );

        assert_eq!(file.script_kind(), ScriptKind::TypeScript);
        assert_eq!(file.range().end().get(), 5);
        assert_eq!(file.statements().len(), 1);
        assert!(file.diagnostics().is_empty());
        assert_eq!(file.token_text(&file.tokens()[0]), Some("let"));
        assert_eq!(file.statements()[0].kind(), NodeKind::ExpressionStatement);
    }
}
