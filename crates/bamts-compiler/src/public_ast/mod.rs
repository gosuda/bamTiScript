//! The public AST surface reachable from the `bamti` package's
//! `unstable/ast` export subpaths.
//!
//! This module is a *projection*, not a second tree. Every operation reads the
//! parser-owned [`crate::syntax`] values directly, so a consumer of the public
//! surface and the compiler itself always agree about ranges, kinds, and
//! identities. Nothing here allocates a parallel node representation, keeps a
//! parent link, or caches a derived index: the parser product is immutable and
//! shared, so projections stay borrow-only.
//!
//! The submodules mirror the export subpaths one-to-one:
//!
//! * [`is`] classifies a [`SyntaxKind`] or a node reference.
//! * [`factory`] builds new nodes with caller-assigned identities.
//! * [`utils`] answers position, text, and containment questions.
//! * [`scanner`] exposes the lexical pass as a public token listing.
//! * [`visitor`] walks child edges in source order.
//! * [`clone`] copies a subtree, either preserving or renumbering identities.

pub mod clone;
pub mod factory;
pub mod is;
pub mod scanner;
pub mod utils;
pub mod visitor;

use crate::source::TextRange;
use crate::syntax::{
    AssignmentTargetNode, BlockNode, CatchClauseNode, ClassMemberNode, DecoratorNode,
    EnumMemberNode, ExportSpecifierNode, Expr, IdentifierNode, ImportSpecifierNode,
    JsxAttributeNode, JsxClosingElementNode, JsxExpressionContainerNode, JsxOpeningElementNode,
    JsxSpreadAttributeNode, JsxSpreadChildNode, JsxTextNode, NodeId, NodeKind, ObjectMemberNode,
    ParameterNode, Pattern, PrivateIdentifierNode, SourceFile, Stmt, StringLiteralNode,
    SwitchCaseNode, SyntaxKind, Token,
    Ty, TypeAnnotationNode, TypeMemberNode, TypeParameterNode, VariableDeclaratorNode,
};

/// A borrowed reference to any node of the public AST.
///
/// The variants correspond exactly to the parser's node families. A caller can
/// therefore match a reference back to its concrete typed node without a
/// downcast, and the traversal in [`visitor`] can yield heterogeneous children
/// through one closed type.
#[derive(Clone, Copy)]
pub enum NodeRef<'a> {
    SourceFile(&'a SourceFile),
    Statement(&'a Stmt),
    Expression(&'a Expr),
    Identifier(&'a IdentifierNode),
    PrivateIdentifier(&'a PrivateIdentifierNode),
    StringLiteral(&'a StringLiteralNode),
    TypeNode(&'a Ty),
    BindingPattern(&'a Pattern),
    AssignmentTarget(&'a AssignmentTargetNode),
    Parameter(&'a ParameterNode),
    VariableDeclarator(&'a VariableDeclaratorNode),
    Block(&'a BlockNode),
    ClassMember(&'a ClassMemberNode),
    ObjectMember(&'a ObjectMemberNode),
    ImportSpecifier(&'a ImportSpecifierNode),
    ExportSpecifier(&'a ExportSpecifierNode),
    TypeAnnotation(&'a TypeAnnotationNode),
    TypeParameter(&'a TypeParameterNode),
    TypeMember(&'a TypeMemberNode),
    CatchClause(&'a CatchClauseNode),
    SwitchCase(&'a SwitchCaseNode),
    EnumMember(&'a EnumMemberNode),
    Decorator(&'a DecoratorNode),
    JsxOpeningElement(&'a JsxOpeningElementNode),
    JsxClosingElement(&'a JsxClosingElementNode),
    JsxAttribute(&'a JsxAttributeNode),
    JsxSpreadAttribute(&'a JsxSpreadAttributeNode),
    JsxExpressionContainer(&'a JsxExpressionContainerNode),
    JsxSpreadChild(&'a JsxSpreadChildNode),
    JsxText(&'a JsxTextNode),
    Token(&'a Token),
}

impl NodeRef<'_> {
    /// Returns the node's stable parser-assigned identity.
    ///
    /// A token carries no [`NodeId`]: it is identified by its range within the
    /// source, so this returns `None` rather than inventing an identity.
    #[must_use]
    pub fn id(&self) -> Option<NodeId> {
        match self {
            Self::SourceFile(file) => Some(file.id()),
            Self::Statement(node) => Some(node.id()),
            Self::Expression(node) => Some(node.id()),
            Self::TypeNode(node) => Some(node.id()),
            Self::BindingPattern(node) => Some(node.id()),
            Self::Identifier(node) => Some(node.id()),
            Self::PrivateIdentifier(node) => Some(node.id()),
            Self::StringLiteral(node) => Some(node.id()),
            Self::AssignmentTarget(node) => Some(node.id()),
            Self::Parameter(node) => Some(node.id()),
            Self::VariableDeclarator(node) => Some(node.id()),
            Self::Block(node) => Some(node.id()),
            Self::ClassMember(node) => Some(node.id()),
            Self::ObjectMember(node) => Some(node.id()),
            Self::ImportSpecifier(node) => Some(node.id()),
            Self::ExportSpecifier(node) => Some(node.id()),
            Self::TypeAnnotation(node) => Some(node.id()),
            Self::TypeParameter(node) => Some(node.id()),
            Self::TypeMember(node) => Some(node.id()),
            Self::CatchClause(node) => Some(node.id()),
            Self::SwitchCase(node) => Some(node.id()),
            Self::EnumMember(node) => Some(node.id()),
            Self::Decorator(node) => Some(node.id()),
            Self::JsxOpeningElement(node) => Some(node.id()),
            Self::JsxClosingElement(node) => Some(node.id()),
            Self::JsxAttribute(node) => Some(node.id()),
            Self::JsxSpreadAttribute(node) => Some(node.id()),
            Self::JsxExpressionContainer(node) => Some(node.id()),
            Self::JsxSpreadChild(node) => Some(node.id()),
            Self::JsxText(node) => Some(node.id()),
            Self::Token(_) => None,
        }
    }

    /// Returns the source range this node spans.
    #[must_use]
    pub fn range(&self) -> TextRange {
        match self {
            Self::SourceFile(file) => file.range(),
            Self::Statement(node) => node.range(),
            Self::Expression(node) => node.range(),
            Self::TypeNode(node) => node.range(),
            Self::BindingPattern(node) => node.range(),
            Self::Identifier(node) => node.range(),
            Self::PrivateIdentifier(node) => node.range(),
            Self::StringLiteral(node) => node.range(),
            Self::AssignmentTarget(node) => node.range(),
            Self::Parameter(node) => node.range(),
            Self::VariableDeclarator(node) => node.range(),
            Self::Block(node) => node.range(),
            Self::ClassMember(node) => node.range(),
            Self::ObjectMember(node) => node.range(),
            Self::ImportSpecifier(node) => node.range(),
            Self::ExportSpecifier(node) => node.range(),
            Self::TypeAnnotation(node) => node.range(),
            Self::TypeParameter(node) => node.range(),
            Self::TypeMember(node) => node.range(),
            Self::CatchClause(node) => node.range(),
            Self::SwitchCase(node) => node.range(),
            Self::EnumMember(node) => node.range(),
            Self::Decorator(node) => node.range(),
            Self::JsxOpeningElement(node) => node.range(),
            Self::JsxClosingElement(node) => node.range(),
            Self::JsxAttribute(node) => node.range(),
            Self::JsxSpreadAttribute(node) => node.range(),
            Self::JsxExpressionContainer(node) => node.range(),
            Self::JsxSpreadChild(node) => node.range(),
            Self::JsxText(node) => node.range(),
            Self::Token(token) => token.range(),
        }
    }

    /// Returns the node's full syntax kind, spanning both token and grammar
    /// categories.
    #[must_use]
    pub fn syntax_kind(&self) -> SyntaxKind {
        match self {
            Self::SourceFile(file) => file.syntax_kind(),
            Self::Statement(node) => node.syntax_kind(),
            Self::Expression(node) => node.syntax_kind(),
            Self::TypeNode(node) => node.syntax_kind(),
            Self::BindingPattern(node) => node.syntax_kind(),
            Self::Identifier(node) => node.syntax_kind(),
            Self::PrivateIdentifier(node) => node.syntax_kind(),
            Self::StringLiteral(node) => node.syntax_kind(),
            Self::AssignmentTarget(node) => node.syntax_kind(),
            Self::Parameter(node) => node.syntax_kind(),
            Self::VariableDeclarator(node) => node.syntax_kind(),
            Self::Block(node) => node.syntax_kind(),
            Self::ClassMember(node) => node.syntax_kind(),
            Self::ObjectMember(node) => node.syntax_kind(),
            Self::ImportSpecifier(node) => node.syntax_kind(),
            Self::ExportSpecifier(node) => node.syntax_kind(),
            Self::TypeAnnotation(node) => node.syntax_kind(),
            Self::TypeParameter(node) => node.syntax_kind(),
            Self::TypeMember(node) => node.syntax_kind(),
            Self::CatchClause(node) => node.syntax_kind(),
            Self::SwitchCase(node) => node.syntax_kind(),
            Self::EnumMember(node) => node.syntax_kind(),
            Self::Decorator(node) => node.syntax_kind(),
            Self::JsxOpeningElement(node) => node.syntax_kind(),
            Self::JsxClosingElement(node) => node.syntax_kind(),
            Self::JsxAttribute(node) => node.syntax_kind(),
            Self::JsxSpreadAttribute(node) => node.syntax_kind(),
            Self::JsxExpressionContainer(node) => node.syntax_kind(),
            Self::JsxSpreadChild(node) => node.syntax_kind(),
            Self::JsxText(node) => node.syntax_kind(),
            Self::Token(token) => token.syntax_kind(),
        }
    }

    /// Returns the grammar kind, or `None` when this reference names a token.
    #[must_use]
    pub fn node_kind(&self) -> Option<NodeKind> {
        match self.syntax_kind() {
            SyntaxKind::Node(kind) => Some(kind),
            SyntaxKind::Token(_) => None,
        }
    }
}
