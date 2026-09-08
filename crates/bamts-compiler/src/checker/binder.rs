//! Binder for one parsed [`SourceFile`]: scope-tree construction, symbol-table
//! population, and [`TypeTable`] interning behind the non-mutating
//! `bind_source` / `bind_source_with_environment` contract consumed by
//! `crate::checker`.
//!
//! The [`Binder`] walks declarations, hoists block-scoped bindings, resolves
//! references against the two-namespace scope tree, and freezes the product
//! into an immutable [`SemanticModel`] with canonical diagnostics.

use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use bamts_bytecode::{EcmaString, format_number};

use super::AnalysisFacts;
use super::ProgramCheckOptions;
use super::inference::{
    InferenceContext, InferenceParameter, InferenceProvenance, InferredTypeArgument,
    InferredTypeArguments,
};
use super::intrinsic_environment::GlobalEnvironment;
use super::jsx::{JsxCallable, JsxFactorySignature};
use super::narrowing::{
    FlowFacts, FlowKey, FlowNodeId, GuardResolver, NarrowingContext, NarrowingGuard, flow_key_of,
};
use super::relations::{TypeRelation, TypeRelations};
use super::{
    ABSTRACT_CONSTRUCTOR, ACCESSOR_THIS_PARAMETER, AMBIENT_IMPLEMENTATION, ARGUMENT_COUNT_MISMATCH,
    ARGUMENT_NOT_ASSIGNABLE, ASSIGNMENT_TO_CONST, ASSIGNMENT_TO_FUNCTION, ASSIGNMENT_TO_NAMESPACE,
    ASSIGNMENT_TO_READONLY, AWAIT_USING_DECLARATION_IN_FOR_IN, BARE_SUPER_EXPRESSION,
    CANNOT_FIND_NAME, CANNOT_FIND_NAME_LIB_GATED, CANNOT_FIND_NAMESPACE, CANNOT_FIND_TYPE,
    CONSTRUCTOR_DECORATOR_NOT_SUPPORTED, CONSTRUCTOR_TYPE_PARAMETERS,
    DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL, DERIVED_CONSTRUCTOR_MISSING_SUPER,
    DUPLICATE_DECLARATION, EXCESS_PROPERTY, EXPRESSION_NOT_CALLABLE, EXPRESSION_NOT_CONSTRUCTABLE,
    FOR_IN_LEFT_HAND_SIDE_INVALID, FOR_OF_ITERABLE_REQUIRED,
    FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT, FUNCTION_IMPLEMENTATION_WRONG_NAME,
    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, GET_ACCESSOR_NO_RETURN, GET_ACCESSOR_PARAMETERS,
    IMPORT_CONFLICTS_WITH_LOCAL, INVALID_ASSIGNMENT_TARGET, INVALID_INDEXED_ACCESS_KEY,
    MEMBER_NOT_ACCESSIBLE, MISSING_METHOD_RETURN_TYPE, MIXED_EXPORT_ASSIGNMENT,
    NAMESPACE_NO_EXPORTED_MEMBER, NEW_TARGET_OUTSIDE_FUNCTION, NON_VOID_FUNCTION_MUST_RETURN,
    PARAMETER_DECORATOR_NOT_SUPPORTED, PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR,
    PROPERTY_DOES_NOT_EXIST, PROPERTY_NOT_INITIALIZED, SET_ACCESSOR_PARAMETER_INITIALIZER,
    STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT, STRICT_NULL_MEMBER_ACCESS,
    SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS, SUPER_CALL_OUTSIDE_CONSTRUCTOR,
    SUPER_REFERENCE_NON_DERIVED, TYPE_ALIAS_CIRCULAR, TYPE_NESTING_TOO_DEEP, TYPE_NOT_ASSIGNABLE,
    TYPE_PARAMETER_CIRCULAR_DEFAULT, UNUSED_EXPECT_ERROR, USED_BEFORE_ASSIGNED,
    USING_DECLARATION_BINDING_PATTERN, USING_DECLARATION_IN_FOR_IN,
    USING_DECLARATION_MISSING_INITIALIZER, VALUE_CANNOT_BE_USED_HERE, WITH_STATEMENT_NOT_ALLOWED,
};
use super::{
    ABSTRACT_CONSTRUCTOR_MESSAGE, ACCESSOR_THIS_PARAMETER_MESSAGE, AMBIENT_IMPLEMENTATION_MESSAGE,
    ARGUMENT_COUNT_MISMATCH_MESSAGE, ARGUMENT_NOT_ASSIGNABLE_MESSAGE, ASSIGNMENT_TO_CONST_MESSAGE,
    ASSIGNMENT_TO_FUNCTION_MESSAGE, ASSIGNMENT_TO_NAMESPACE_MESSAGE,
    ASSIGNMENT_TO_READONLY_MESSAGE, AWAIT_USING_DECLARATION_IN_FOR_IN_MESSAGE,
    BARE_SUPER_EXPRESSION_MESSAGE, CANNOT_FIND_NAME_LIB_GATED_MESSAGE, CANNOT_FIND_NAME_MESSAGE,
    CANNOT_FIND_NAMESPACE_MESSAGE, CANNOT_FIND_TYPE_MESSAGE,
    CONSTRUCTOR_DECORATOR_NOT_SUPPORTED_MESSAGE, CONSTRUCTOR_TYPE_PARAMETERS_MESSAGE,
    DERIVED_CONSTRUCTOR_MISSING_SUPER_MESSAGE, DUPLICATE_MESSAGE, EXCESS_PROPERTY_MESSAGE,
    EXPRESSION_NOT_CALLABLE_MESSAGE, EXPRESSION_NOT_CONSTRUCTABLE_MESSAGE,
    FOR_IN_LEFT_HAND_SIDE_INVALID_MESSAGE, FOR_OF_ITERABLE_REQUIRED_MESSAGE,
    FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT_MESSAGE, FUNCTION_IMPLEMENTATION_WRONG_NAME_MESSAGE,
    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE, GET_ACCESSOR_NO_RETURN_MESSAGE,
    GET_ACCESSOR_PARAMETERS_MESSAGE, IMPORT_CONFLICTS_WITH_LOCAL_MESSAGE,
    INVALID_ASSIGNMENT_TARGET_MESSAGE, INVALID_INDEXED_ACCESS_KEY_MESSAGE,
    MEMBER_NOT_ACCESSIBLE_MESSAGE, MISSING_METHOD_RETURN_TYPE_MESSAGE,
    MIXED_EXPORT_ASSIGNMENT_MESSAGE, NEW_TARGET_OUTSIDE_FUNCTION_MESSAGE,
    NON_VOID_FUNCTION_MUST_RETURN_MESSAGE, NOT_ASSIGNABLE_MESSAGE,
    PARAMETER_DECORATOR_NOT_SUPPORTED_MESSAGE, PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR_MESSAGE,
    PROPERTY_DOES_NOT_EXIST_MESSAGE, PROPERTY_NOT_INITIALIZED_MESSAGE,
    SET_ACCESSOR_PARAMETER_INITIALIZER_MESSAGE, STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT_MESSAGE,
    STRICT_NULL_MEMBER_ACCESS_MESSAGE, SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS_MESSAGE,
    SUPER_CALL_OUTSIDE_CONSTRUCTOR_MESSAGE, SUPER_REFERENCE_NON_DERIVED_MESSAGE,
    TYPE_ALIAS_CIRCULAR_MESSAGE, TYPE_NESTING_TOO_DEEP_MESSAGE,
    TYPE_PARAMETER_CIRCULAR_DEFAULT_MESSAGE, UNUSED_EXPECT_ERROR_MESSAGE,
    USED_BEFORE_ASSIGNED_MESSAGE, USING_DECLARATION_BINDING_PATTERN_MESSAGE,
    USING_DECLARATION_IN_FOR_IN_MESSAGE, USING_DECLARATION_MISSING_INITIALIZER_MESSAGE,
    VALUE_CANNOT_BE_USED_HERE_MESSAGE, WITH_STATEMENT_NOT_ALLOWED_MESSAGE,
};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::enum_plan::{self, EnumDeclarationBinding, EnumFacts};
use crate::literal::{number_value, string_value};
use crate::namespace_plan::{self, NamespaceDeclarationBinding, NamespaceFacts};
use crate::source::{ScriptKind, TextRange};
use crate::syntax::{
    Accessibility, ArrayElement, ArrowFunction, AssignmentExpression, AssignmentOperator,
    AssignmentTarget, BinaryExpression, BinaryOperator, BindingPattern, CallArgument,
    CallExpression, ClassDeclaration, ClassMember, ConditionalExpression, DeclarationModifiers,
    EntityName, Expr, Expression, ForBinding, ForInitializer, ForOfMode, FunctionBody,
    FunctionLike, FunctionType, IdentifierNode, ImportBinding, InterfaceDeclaration,
    JsxAttributeInitializer, JsxAttributeItem, JsxChild, KeywordType, Literal, LogicalOperator,
    MemberProperty, MetaProperty, NamespaceName, NewExpression, NodeId, ObjectLiteral,
    ObjectMember, ParameterNode, PropertyModifier, PropertyName, SourceFile, Statement, Stmt,
    Token, TokenKind, Ty, TypeAliasDeclaration, TypeAnnotationNode, TypeLiteral, TypeMember,
    TypeNode, TypeOperator, TypeReference, UnaryOperator, VariableDeclaration, VariableKind,
};

/// Maximum depth of recursive type resolution before the checker emits
/// `TYPE_NESTING_TOO_DEEP` and returns the error type. Set higher than the
/// parser's `MAX_DEPTH` (256) because each parser level can expand into
/// multiple resolution steps (alias expansion, interface `extends`, type
/// argument resolution), but still bounded to prevent stack overflow on
/// pathological inputs.
const MAX_TYPE_DEPTH: u32 = 512;

/// A lexical scope's identity within a [`SemanticModel`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(u32);

impl ScopeId {
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// A bound name's identity within a [`SemanticModel`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SymbolId(u32);

impl SymbolId {
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// An interned structural type's identity within a [`TypeTable`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeId(u32);

impl TypeId {
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// The kind of lexical scope, used only to describe the model to callers.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ScopeKind {
    Global,
    Module,
    Function,
    Block,
    For,
    Catch,
    Class,
    Namespace,
    /// Marks the body of a sloppy-mode `with` statement. Unresolved value
    /// references inside this scope may bind to the runtime object instead.
    With,
}

/// One lexical scope with its two-namespace symbol tables and strict-mode bit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scope {
    kind: ScopeKind,
    parent: Option<ScopeId>,
    values: BTreeMap<String, SymbolId>,
    types: BTreeMap<String, SymbolId>,
    strict: bool,
    /// The container symbol whose members this scope collects — enum member
    /// scopes and class scopes only; namespace export scopes intentionally
    /// have no owner, since upstream renders export declarations bare.
    owner: Option<SymbolId>,
    /// The class or interface that owns polymorphic `this` in this scope.
    /// Interface scopes keep this separate from qualified-name ownership.
    this_owner: Option<SymbolId>,
}

impl Scope {
    #[must_use]
    pub const fn kind(&self) -> ScopeKind {
        self.kind
    }

    #[must_use]
    pub const fn parent(&self) -> Option<ScopeId> {
        self.parent
    }

    /// Returns the container symbol whose member declarations this scope
    /// collects, when this is a member scope (enum body, class body).
    #[must_use]
    pub const fn owner(&self) -> Option<SymbolId> {
        self.owner
    }

    /// Returns whether this scope executes in ECMAScript strict mode.
    #[must_use]
    pub const fn is_strict(&self) -> bool {
        self.strict
    }

    /// Returns the value binding declared directly in this scope, if any.
    #[must_use]
    pub fn value(&self, name: &str) -> Option<SymbolId> {
        self.values.get(name).copied()
    }

    /// Returns the type binding declared directly in this scope, if any.
    #[must_use]
    pub fn type_binding(&self, name: &str) -> Option<SymbolId> {
        self.types.get(name).copied()
    }
}

/// What a bound name declares. This drives namespace membership and whether a
/// redeclaration is a legal merge or a duplicate error.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SymbolKind {
    IntrinsicValue,
    IntrinsicType,
    Variable(VariableKind),
    Function,
    Parameter,
    Class,
    Interface,
    TypeAlias,
    Enum,
    EnumMember,
    TypeParameter,
    Import,
    Namespace,
}

impl SymbolKind {
    const fn occupies_value(self) -> bool {
        matches!(
            self,
            Self::IntrinsicValue
                | Self::Variable(_)
                | Self::Function
                | Self::Parameter
                | Self::Class
                | Self::Enum
                | Self::EnumMember
                | Self::Import
                | Self::Namespace
        )
    }

    const fn occupies_type(self) -> bool {
        matches!(
            self,
            Self::IntrinsicType
                | Self::Class
                | Self::Enum
                | Self::Interface
                | Self::TypeAlias
                | Self::TypeParameter
                | Self::Import
                | Self::Namespace
        )
    }

    /// Returns whether an existing value binding of `self` accepts a merge from
    /// a new declaration of `new`. Namespace merges with function/class/enum are
    /// order-aware: the function/class/enum must already exist.
    const fn accepts_value_merge_from(self, new: Self) -> bool {
        matches!(
            (self, new),
            (
                Self::Variable(VariableKind::Var) | Self::Function,
                Self::Variable(VariableKind::Var) | Self::Function
            ) | (Self::Enum, Self::Enum)
                | (Self::Namespace, Self::Namespace)
                | (Self::Function | Self::Class | Self::Enum, Self::Namespace)
        )
    }

    /// Returns whether an existing type binding of `self` accepts a merge from
    /// a new declaration of `new`. Class/enum + namespace merges are order-aware;
    /// interface + namespace remains bidirectional.
    const fn accepts_type_merge_from(self, new: Self) -> bool {
        matches!(
            (self, new),
            (Self::Interface, Self::Interface)
                | (Self::Enum, Self::Enum)
                | (Self::Namespace, Self::Namespace)
                | (Self::Interface, Self::Namespace)
                | (Self::Namespace, Self::Interface)
                | (Self::Class | Self::Enum, Self::Namespace)
                | (Self::Import, Self::Interface | Self::TypeAlias)
                | (Self::Interface | Self::TypeAlias, Self::Import)
        )
    }
}

/// One immutable bound name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    name: String,
    kind: SymbolKind,
    scope: ScopeId,
    declaration: NodeId,
    range: TextRange,
    /// The owning container symbol, set when this symbol is declared into an
    /// owned member scope (enum body, class body). Drives `qualified_name`.
    parent: Option<SymbolId>,
}

impl Symbol {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn kind(&self) -> SymbolKind {
        self.kind
    }

    #[must_use]
    pub const fn scope(&self) -> ScopeId {
        self.scope
    }

    #[must_use]
    pub const fn declaration(&self) -> NodeId {
        self.declaration
    }

    #[must_use]
    pub const fn range(&self) -> TextRange {
        self.range
    }

    /// Returns the owning container symbol set at declaration time when this
    /// symbol was declared into an owned member scope (enum body, class body).
    #[must_use]
    pub const fn parent(&self) -> Option<SymbolId> {
        self.parent
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct HoistedDeclarationIdentity {
    scope: ScopeId,
    declaration: NodeId,
    range: TextRange,
    kind: SymbolKind,
}

/// One member of an interned object type.
#[derive(Clone, Debug)]
pub struct PropertyType {
    name: Box<str>,
    optional: bool,
    readonly: bool,
    getter_only: bool,
    type_id: TypeId,
    /// Class member accessibility. Plain object/interface properties are
    /// always [`Accessibility::Public`] with no declaring class.
    access: Accessibility,
    /// The class symbol that declared this property. `None` for structural
    /// object/interface properties. This field controls access compatibility.
    declaring_class: Option<SymbolId>,
    /// Class and interface symbols whose polymorphic `this` appears in this
    /// property's type. Access control does not use this provenance.
    declaring_types: Vec<SymbolId>,
    is_method: bool,
    /// Whether this property is spreadable. Ordinary object/interface
    /// members default to `false`; properties that legitimately propagate
    /// through spread keep the flag explicitly.
    spreadable: bool,
}

impl PropertyType {
    #[must_use]
    pub fn new(name: impl Into<Box<str>>, optional: bool, type_id: TypeId) -> Self {
        Self {
            name: name.into(),
            optional,
            readonly: false,
            getter_only: false,
            type_id,
            access: Accessibility::Public,
            declaring_class: None,
            declaring_types: Vec::new(),
            is_method: false,
            spreadable: false,
        }
    }

    #[must_use]
    pub fn with_readonly(mut self, readonly: bool) -> Self {
        self.readonly = readonly;
        self
    }

    #[must_use]
    pub fn with_getter_only(mut self, getter_only: bool) -> Self {
        self.getter_only = getter_only;
        self
    }

    #[must_use]
    pub fn with_accessibility(
        mut self,
        access: Accessibility,
        declaring_class: Option<SymbolId>,
    ) -> Self {
        self.access = access;
        self.declaring_class = declaring_class;
        if let Some(owner) = declaring_class
            && !self.declaring_types.contains(&owner)
        {
            self.declaring_types.push(owner);
        }
        self
    }

    #[must_use]
    pub fn with_declaring_type(mut self, declaring_type: Option<SymbolId>) -> Self {
        if let Some(owner) = declaring_type
            && !self.declaring_types.contains(&owner)
        {
            self.declaring_types.push(owner);
        }
        self
    }

    #[must_use]
    pub fn with_declaring_types(mut self, declaring_types: Vec<SymbolId>) -> Self {
        self.declaring_types = declaring_types;
        self
    }

    #[must_use]
    pub fn with_method(mut self, is_method: bool) -> Self {
        self.is_method = is_method;
        self
    }

    #[must_use]
    pub fn with_spreadable(mut self, spreadable: bool) -> Self {
        self.spreadable = spreadable;
        self
    }

    #[must_use]
    pub const fn is_method(&self) -> bool {
        self.is_method
    }

    #[must_use]
    pub const fn spreadable(&self) -> bool {
        self.spreadable
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn readonly(&self) -> bool {
        self.readonly
    }

    #[must_use]
    pub const fn getter_only(&self) -> bool {
        self.getter_only
    }

    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_id
    }

    #[must_use]
    pub const fn access(&self) -> Accessibility {
        self.access
    }

    #[must_use]
    pub const fn declaring_class(&self) -> Option<SymbolId> {
        self.declaring_class
    }

    #[must_use]
    pub fn declaring_types(&self) -> &[SymbolId] {
        &self.declaring_types
    }
}

impl PartialEq for PropertyType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.optional == other.optional
            && self.readonly == other.readonly
            && self.getter_only == other.getter_only
            && self.type_id == other.type_id
            && self.access == other.access
            && self.declaring_class == other.declaring_class
            && self.declaring_types == other.declaring_types
            && self.is_method == other.is_method
            && self.spreadable == other.spreadable
    }
}

impl Eq for PropertyType {}

impl std::hash::Hash for PropertyType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.optional.hash(state);
        self.readonly.hash(state);
        self.getter_only.hash(state);
        self.type_id.hash(state);
        self.access.hash(state);
        self.declaring_class.hash(state);
        self.declaring_types.hash(state);
        self.is_method.hash(state);
        self.spreadable.hash(state);
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct IteratorProperty {
    type_id: TypeId,
    optional: bool,
    access: Accessibility,
    declaring_class: Option<SymbolId>,
    declaring_types: Vec<SymbolId>,
    is_method: bool,
    spreadable: bool,
}

impl IteratorProperty {
    fn new(type_id: TypeId, optional: bool) -> Self {
        Self {
            type_id,
            optional,
            access: Accessibility::Public,
            declaring_class: None,
            declaring_types: Vec::new(),
            is_method: false,
            spreadable: true,
        }
    }

    #[must_use]
    fn with_accessibility(
        mut self,
        access: Accessibility,
        declaring_class: Option<SymbolId>,
    ) -> Self {
        self.access = access;
        self.declaring_class = declaring_class;
        if let Some(owner) = declaring_class
            && !self.declaring_types.contains(&owner)
        {
            self.declaring_types.push(owner);
        }
        self
    }

    #[must_use]
    fn with_declaring_type(mut self, declaring_type: SymbolId) -> Self {
        if !self.declaring_types.contains(&declaring_type) {
            self.declaring_types.push(declaring_type);
        }
        self
    }

    #[must_use]
    fn with_declaring_types(mut self, declaring_types: Vec<SymbolId>) -> Self {
        self.declaring_types = declaring_types;
        self
    }

    #[must_use]
    fn with_method(mut self, is_method: bool) -> Self {
        self.is_method = is_method;
        self
    }

    #[must_use]
    fn with_spreadable(mut self, spreadable: bool) -> Self {
        self.spreadable = spreadable;
        self
    }

    #[must_use]
    pub(crate) fn with_type_id(&self, type_id: TypeId) -> Self {
        let mut property = self.clone();
        property.type_id = type_id;
        property
    }

    pub(crate) const fn type_id(&self) -> TypeId {
        self.type_id
    }

    pub(crate) const fn optional(&self) -> bool {
        self.optional
    }

    pub(crate) const fn access(&self) -> Accessibility {
        self.access
    }

    pub(crate) const fn declaring_class(&self) -> Option<SymbolId> {
        self.declaring_class
    }

    pub(crate) fn declaring_types(&self) -> &[SymbolId] {
        &self.declaring_types
    }

    pub(crate) const fn is_method(&self) -> bool {
        self.is_method
    }

    pub(crate) const fn spreadable(&self) -> bool {
        self.spreadable
    }
}

/// Owner scope a property belongs to. Anonymous object literals keep one
/// owner per literal expression node, so structurally equal shapes never
/// merge; named declarations anchor to their container symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum PropertyOwner {
    /// Declared container member owner (interface, class, or namespace symbol).
    Member(SymbolId),
    /// Object literal expression node. Each literal mints its own owner.
    Site(NodeId),
}

/// Identifies one interned `(owner, name)` property declaration for rename.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PropertyId(usize);

/// How the property appeared at its bare span. Shorthand anchors expand to
/// `newName: oldName` rather than renaming the value binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PropertyAnchorKind {
    Plain,
    Shorthand,
}

/// One property occurrence recorded for rename support.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PropertyAnchor {
    /// Bare name span (Invariant A): quotes excluded, brackets excluded,
    /// receiver excluded, and the source text at that span is byte-identical
    /// to the interned property name.
    pub(crate) range: TextRange,
    pub(crate) property_id: PropertyId,

    pub(crate) kind: PropertyAnchorKind,
    /// Whether this anchor was recorded at a declaration site (object
    /// literal property, class member, interface member) rather than a
    /// member access.
    pub(crate) declaration: bool,
}

/// The interned declaration-facing name an anchor refers to.
#[derive(Clone, Debug)]
pub(crate) struct PropertySite {
    pub(crate) name: Box<str>,
    pub(crate) owner: PropertyOwner,
}

/// One index signature retained by an interned object type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IndexSignature {
    pub(crate) readonly: bool,
    pub(crate) parameters: Vec<FunctionParameter>,
    pub(crate) value_type: TypeId,
    pub(crate) declaring_types: Vec<SymbolId>,
}

/// The members retained by an interned structural object type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ObjectType {
    pub(crate) properties: Vec<PropertyType>,
    pub(crate) call_signatures: Vec<FunctionSignature>,
    pub(crate) construct_signatures: Vec<ConstructEntry>,
    pub(crate) index_signatures: Vec<IndexSignature>,
    pub(crate) generator_return: Option<TypeId>,
    pub(crate) iterator_property: Option<IteratorProperty>,
    pub(crate) async_iterator_property: Option<IteratorProperty>,
}

impl ObjectType {
    #[must_use]
    pub fn properties(&self) -> &[PropertyType] {
        &self.properties
    }
}

/// One parameter of an interned function signature.
#[derive(Clone, Debug)]
pub struct FunctionParameter {
    name: String,
    type_id: TypeId,
    optional: bool,
    rest: bool,
}

impl PartialEq for FunctionParameter {
    fn eq(&self, other: &Self) -> bool {
        self.type_id == other.type_id && self.optional == other.optional && self.rest == other.rest
    }
}

impl Eq for FunctionParameter {}

impl std::hash::Hash for FunctionParameter {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.type_id.hash(state);
        self.optional.hash(state);
        self.rest.hash(state);
    }
}

impl FunctionParameter {
    #[must_use]
    pub fn new(name: String, type_id: TypeId, optional: bool, rest: bool) -> Self {
        Self {
            name,
            type_id,
            optional,
            rest,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_id
    }

    #[must_use]
    pub const fn optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn rest(&self) -> bool {
        self.rest
    }
}

/// One interned function signature.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TypeParameterBounds {
    constraint: Option<TypeId>,
    default: Option<TypeId>,
}

impl TypeParameterBounds {
    pub(crate) const NONE: Self = Self {
        constraint: None,
        default: None,
    };

    pub(crate) const fn new(constraint: Option<TypeId>, default: Option<TypeId>) -> Self {
        Self {
            constraint,
            default,
        }
    }

    #[must_use]
    pub const fn constraint(self) -> Option<TypeId> {
        self.constraint
    }

    #[must_use]
    pub const fn default(self) -> Option<TypeId> {
        self.default
    }
}

/// Intrinsic value/type symbol pairs captured while binding the standard
/// environment. Every collection special case keys off these identities and
/// never off source-level names, so user declarations keep shadowing the
/// intrinsics.
struct CollectionIntrinsicSymbols {
    set_value: SymbolId,
    map_value: SymbolId,
    set_type: SymbolId,
    readonly_set_type: SymbolId,
    map_type: SymbolId,
    readonly_map_type: SymbolId,
}

#[derive(Clone, Debug)]
pub struct FunctionSignature {
    type_parameters: Vec<SymbolId>,
    type_parameter_bounds: Vec<TypeParameterBounds>,
    parameters: Vec<FunctionParameter>,
    return_type: TypeId,
    declaring_types: Vec<SymbolId>,
    javascript: bool,
}

impl PartialEq for FunctionSignature {
    fn eq(&self, other: &Self) -> bool {
        self.type_parameters == other.type_parameters
            && self.type_parameter_bounds == other.type_parameter_bounds
            && self.parameters == other.parameters
            && self.return_type == other.return_type
            && self.declaring_types == other.declaring_types
            && self.javascript == other.javascript
    }
}

impl Eq for FunctionSignature {}

impl std::hash::Hash for FunctionSignature {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.type_parameters.hash(state);
        self.type_parameter_bounds.hash(state);
        self.parameters.hash(state);
        self.return_type.hash(state);
        self.declaring_types.hash(state);
        self.javascript.hash(state);
    }
}

impl FunctionSignature {
    #[must_use]
    pub fn type_parameters(&self) -> &[SymbolId] {
        &self.type_parameters
    }

    #[must_use]
    pub fn type_parameter_bounds(&self) -> &[TypeParameterBounds] {
        &self.type_parameter_bounds
    }

    #[must_use]
    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    #[must_use]
    pub const fn return_type(&self) -> TypeId {
        self.return_type
    }

    #[must_use]
    pub fn declaring_types(&self) -> &[SymbolId] {
        &self.declaring_types
    }

    #[must_use]
    pub(crate) fn with_declaring_types(mut self, declaring_types: Vec<SymbolId>) -> Self {
        self.declaring_types = declaring_types;
        self
    }

    #[must_use]
    pub const fn javascript(&self) -> bool {
        self.javascript
    }

    /// Returns `(required, total, rest_index)` for this signature.
    /// `total` is `usize::MAX` when the signature ends in a rest parameter.
    /// `required` is the count of fixed parameters that must be supplied; a
    /// required parameter after optional/defaulted parameters still counts and
    /// sets the minimum to its position plus one.
    #[must_use]
    pub fn arity(&self) -> (usize, usize, Option<usize>) {
        let mut required = 0;
        let mut rest_index = None;
        for (index, parameter) in self.parameters.iter().enumerate() {
            if parameter.rest() {
                rest_index = Some(index);
                break;
            }
            if !parameter.optional() {
                required = index + 1;
            }
        }
        let total = if rest_index.is_some() {
            usize::MAX
        } else {
            self.parameters.len()
        };
        (required, total, rest_index)
    }

    /// Returns `(required, total, rest_index)` for this signature adjusted for
    /// tuple-typed rest parameters. Required tuple elements add to the minimum,
    /// optional elements do not, a fixed tuple gives a finite maximum, and a
    /// tuple rest tail stays unbounded. Ordinary and array-rest signatures keep
    /// the behavior of [`arity`].
    #[must_use]
    pub(crate) fn call_arity(&self, types: &TypeTable) -> (usize, usize, Option<usize>) {
        let (required, total, rest_index) = self.arity();
        let Some(rest_index) = rest_index else {
            return (required, total, None);
        };
        let rest_parameter = &self.parameters[rest_index];
        match types.get(rest_parameter.type_id()) {
            Type::Tuple(shape) => {
                let rest_min = shape.min_arity();
                let fixed_before = rest_index;
                let required = if rest_min == 0 {
                    required
                } else {
                    fixed_before + rest_min
                };
                let total = match shape.max_arity() {
                    Some(max) => fixed_before + max,
                    None => usize::MAX,
                };
                (required, total, Some(rest_index))
            }
            _ => (required, total, Some(rest_index)),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ConstructEntry {
    pub(crate) signature: FunctionSignature,
    pub(crate) is_abstract: bool,
}

trait SignatureCandidate {
    fn signature(&self) -> &FunctionSignature;
    fn is_abstract(&self) -> bool;
}

impl SignatureCandidate for FunctionSignature {
    fn signature(&self) -> &FunctionSignature {
        self
    }

    fn is_abstract(&self) -> bool {
        false
    }
}

impl SignatureCandidate for ConstructEntry {
    fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    fn is_abstract(&self) -> bool {
        self.is_abstract
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RecordKeyState {
    Concrete,
    Deferred,
    Invalid,
}

#[derive(Clone, Copy, Debug)]
enum CallMismatch {
    NotCallable,
    ArgumentCount,
    ArgumentType(TextRange),
    ExcessProperty(TextRange),
}

#[derive(Clone, Debug)]
struct CallEvaluation {
    return_type: Option<TypeId>,
    abstract_constructor: bool,
    mismatches: Vec<CallMismatch>,
}

impl CallEvaluation {
    fn success(return_type: TypeId) -> Self {
        Self {
            return_type: Some(return_type),
            abstract_constructor: false,
            mismatches: Vec::new(),
        }
    }

    fn failure(mismatch: CallMismatch) -> Self {
        Self {
            return_type: None,
            abstract_constructor: false,
            mismatches: vec![mismatch],
        }
    }

    fn failure_all(mismatches: Vec<CallMismatch>) -> Self {
        Self {
            return_type: None,
            abstract_constructor: false,
            mismatches,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum ResolvedCallArgument<'src> {
    Fixed {
        type_id: TypeId,
        range: TextRange,
        expression: Option<&'src Expr>,
    },
    Variadic {
        element: TypeId,
        range: TextRange,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassSide {
    Instance,
    Static,
}

impl ClassSide {
    const fn includes(self, is_static: bool) -> bool {
        matches!(
            (self, is_static),
            (Self::Instance, false) | (Self::Static, true)
        )
    }
}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TupleShape {
    /// Fixed elements before the rest element, in source order.
    pub prefix: Vec<TypeId>,
    /// Count of leading prefix entries that are required.
    pub required: u32,
    /// Element type (not the array type) of the rest element.
    pub rest: Option<TypeId>,
    /// Fixed, always-required elements after the rest element.
    pub suffix: Vec<TypeId>,
}

impl TupleShape {
    #[must_use]
    pub fn fixed(elements: Vec<TypeId>) -> Self {
        Self {
            required: u32::try_from(elements.len()).expect("tuple element count fits in u32"),
            prefix: elements,
            rest: None,
            suffix: Vec::new(),
        }
    }

    #[must_use]
    pub fn min_arity(&self) -> usize {
        self.required as usize + self.suffix.len()
    }

    #[must_use]
    pub fn max_arity(&self) -> Option<usize> {
        self.rest
            .is_none()
            .then(|| self.prefix.len() + self.suffix.len())
    }

    /// Returns every element type that can occupy `index` at runtime.
    #[must_use]
    pub fn element_types_at(&self, index: usize) -> Vec<TypeId> {
        let mut elements = Vec::new();
        if let Some(&element) = self.prefix.get(index) {
            Self::push_unique(&mut elements, element);
        }

        if let Some(rest) = self.rest {
            if index >= self.required as usize {
                Self::push_unique(&mut elements, rest);
            }
            for (suffix_index, &element) in self.suffix.iter().enumerate() {
                if index >= self.required as usize + suffix_index {
                    Self::push_unique(&mut elements, element);
                }
            }
        } else {
            for (suffix_index, &element) in self.suffix.iter().enumerate() {
                let Some(prefix_len) = index.checked_sub(suffix_index) else {
                    continue;
                };
                if prefix_len >= self.required as usize && prefix_len <= self.prefix.len() {
                    Self::push_unique(&mut elements, element);
                }
            }
        }
        elements
    }

    /// Returns every element type that can occupy an offset from the end.
    #[must_use]
    pub fn element_types_from_end(&self, offset: usize) -> Vec<TypeId> {
        if offset == 0 {
            return Vec::new();
        }
        if offset <= self.suffix.len() {
            return vec![self.suffix[self.suffix.len() - offset]];
        }

        let prefix_offset = offset - self.suffix.len();
        let mut elements = Vec::new();
        if let Some(rest) = self.rest {
            Self::push_unique(&mut elements, rest);
            let start = (self.required as usize).saturating_sub(prefix_offset);
            for &element in &self.prefix[start..] {
                Self::push_unique(&mut elements, element);
            }
        } else {
            let first_present = (self.required as usize).max(prefix_offset);
            for present in first_present..=self.prefix.len() {
                Self::push_unique(&mut elements, self.prefix[present - prefix_offset]);
            }
        }
        elements
    }

    /// Returns every element type that can occupy `index` at one valid runtime length.
    #[must_use]
    pub fn element_types_at_length(&self, index: usize, length: usize) -> Vec<TypeId> {
        if index >= length {
            return Vec::new();
        }
        let mut elements = Vec::new();
        for prefix_len in self.prefix_lengths_at_length(length) {
            Self::push_unique(
                &mut elements,
                self.element_at_layout(index, length, prefix_len),
            );
        }
        elements
    }

    pub(crate) fn prefix_lengths_at_length(&self, length: usize) -> Vec<usize> {
        if length < self.min_arity() || self.max_arity().is_some_and(|maximum| length > maximum) {
            return Vec::new();
        }
        let available = length - self.suffix.len();
        if self.rest.is_some() {
            return (self.required as usize..=self.prefix.len().min(available)).collect();
        }
        (available >= self.required as usize && available <= self.prefix.len())
            .then_some(available)
            .into_iter()
            .collect()
    }

    pub(crate) fn element_at_layout(
        &self,
        index: usize,
        length: usize,
        prefix_len: usize,
    ) -> TypeId {
        debug_assert!(index < length);
        debug_assert!(prefix_len >= self.required as usize);
        debug_assert!(prefix_len <= self.prefix.len());
        debug_assert!(length >= prefix_len + self.suffix.len());
        debug_assert!(self.rest.is_some() || length == prefix_len + self.suffix.len());
        let rest_len = length - prefix_len - self.suffix.len();
        if index < prefix_len {
            self.prefix[index]
        } else if index < prefix_len + rest_len {
            self.rest
                .expect("positive rest length requires a rest element")
        } else {
            self.suffix[index - prefix_len - rest_len]
        }
    }

    fn push_unique(elements: &mut Vec<TypeId>, element: TypeId) {
        if !elements.contains(&element) {
            elements.push(element);
        }
    }

    #[must_use]
    pub fn all_element_types(&self) -> Vec<TypeId> {
        let mut elements = Vec::with_capacity(
            self.prefix.len() + usize::from(self.rest.is_some()) + self.suffix.len(),
        );
        elements.extend_from_slice(&self.prefix);
        elements.extend(self.rest);
        elements.extend_from_slice(&self.suffix);
        elements
    }

    #[must_use]
    pub fn is_fixed(&self) -> bool {
        self.rest.is_none() && self.required as usize == self.prefix.len()
    }
}

/// The closed space of structural types the first checker slice models.
///
/// `Error` is a recovery type produced for unresolved or unsupported syntax; it
/// behaves like `Any` in assignability so one upstream mistake never cascades.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    Error,
    Any,
    Unknown,
    Never,
    Void,
    Null,
    Undefined,
    Boolean,
    Number,
    BigInt,
    String,
    Symbol,
    Object,
    BooleanLiteral(bool),
    NumberLiteral(Box<str>),
    StringLiteral(EcmaString),
    BigIntLiteral(Box<str>),
    Array(TypeId),
    Tuple(TupleShape),
    Union(Vec<TypeId>),
    Intersection(Vec<TypeId>),
    ObjectType(ObjectType),
    Function(FunctionSignature),
    /// A nominal type-parameter or interface head compared by identity. During
    /// alias resolution it also serves as the inert head before application.
    Named(SymbolId),
    /// The canonical semantic identity of a class instance or generic interface
    /// application. The argument vector is complete, including defaults.
    AppliedClass {
        symbol: SymbolId,
        arguments: Vec<TypeId>,
    },
    /// The canonical identity of a recursive generic type-alias application.
    /// Only occurrences resolved while the declaration is in progress are
    /// interned; its finite structural view is stored separately.
    AppliedAlias {
        symbol: SymbolId,
        arguments: Vec<TypeId>,
    },
    /// A numeric enum value, distinct from both its runtime enum object and number.
    NumericEnum(SymbolId),
    /// A literal enum member type like `E.A`. The enum symbol identifies the
    /// widened enum type; the member symbol identifies the member for display.
    /// `string_value` is `Some` for string enum members, carrying the cooked
    /// string literal value for assignability with `string` and the specific
    /// literal; `None` for numeric enum members.
    EnumMember {
        enum_symbol: SymbolId,
        member_symbol: SymbolId,
        string_value: Option<EcmaString>,
    },
    /// A deferred `keyof T` type, reduced when the operand becomes concrete.
    Keyof(TypeId),
    /// A deferred indexed access type `T[K]`, reduced when the object and key
    /// become concrete enough to resolve a property or index signature.
    IndexedAccess {
        object: TypeId,
        index: TypeId,
    },
    /// A deferred `Record<K, V>` mapped type. Concrete keys reduce to an
    /// ordinary object type at construction or generic instantiation.
    Record {
        key: TypeId,
        value: TypeId,
    },
    /// A receiver-bound `this` type. The owner isolates markers from nested
    /// foreign types; the constraint names its declaring class or interface.
    This {
        owner: SymbolId,
        constraint: TypeId,
    },
    /// The constructor (static) side of a class — `typeof C`. Carries the
    /// class symbol for nominal display, the type arguments for generic
    /// classes (`typeof C<T>`), and the structural `ObjectType` view built
    /// by `class_static_type` so property/construct lookup can delegate
    /// without pattern-detecting a shape in the display layer.
    ConstructorType {
        symbol: SymbolId,
        arguments: Vec<TypeId>,
        structural: TypeId,
    },
}

#[derive(Debug)]
pub(super) enum ConstraintTypeExpr {
    Id(TypeId),
    Opaque,
    Union(Box<[ConstraintTypeExpr]>),
    Intersection(Box<[ConstraintTypeExpr]>),
}

#[derive(Debug)]
pub(super) enum IndexedAccessConstraint {
    Reduced(ConstraintTypeExpr),
    Invalid,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClassState {
    Provisional,
    Final,
}

#[derive(Clone, Debug)]
struct ClassTemplate {
    raw: TypeId,
    revision: u32,
    state: ClassState,
}

#[derive(Clone, Debug)]
struct ClassMetadata {
    parameters: Vec<SymbolId>,
    bounds: Vec<TypeParameterBounds>,
    bounds_resolving: bool,
    bounds_ready: bool,
    template: Option<ClassTemplate>,
}

#[derive(Clone, Debug)]
struct AliasMetadata {
    parameters: Vec<SymbolId>,
    bounds: Vec<TypeParameterBounds>,
    bounds_resolving: bool,
    bounds_ready: bool,
    template: Option<TypeId>,
}

#[derive(Clone, Copy, Debug)]
struct AppliedClassView {
    revision: u32,
    type_id: TypeId,
}

#[derive(Default)]
struct ImportedTypeMap {
    types: HashMap<TypeId, TypeId>,
    symbols: HashMap<SymbolId, SymbolId>,
    synthesized: Vec<(SymbolId, SymbolId)>,
}

/// An interning table for structural types plus the assignability relation.
///
/// The table is append-only while checking and frozen into the immutable
/// [`SemanticModel`]. It is also a standalone reusable value: [`TypeTable::new`]
/// yields the primitive types so the algebra can be exercised directly.
#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<Type>,
    index: HashMap<Type, TypeId>,
    error: TypeId,
    any: TypeId,
    unknown: TypeId,
    never: TypeId,
    void: TypeId,
    null: TypeId,
    undefined: TypeId,
    boolean: TypeId,
    number: TypeId,
    bigint: TypeId,
    string: TypeId,
    symbol: TypeId,
    object: TypeId,
    object_symbol: Option<SymbolId>,
    collection_symbols: [Option<SymbolId>; 4],
    record_symbol: Option<SymbolId>,
    property_key_symbol: Option<SymbolId>,
    /// The `ConcatArray<T>` interface head backing the synthesized `concat`
    /// member on array types.
    concat_array_symbol: Option<SymbolId>,
    /// Declared constraint per type-parameter symbol. Class and interface names
    /// never enter this map, so nominal named types remain nominal.
    type_parameter_constraints: HashMap<SymbolId, TypeId>,
    type_parameter_defaults: HashMap<SymbolId, TypeId>,
    /// Canonical application metadata. Raw class and generic-interface object
    /// types live as revisioned templates; applied identities are `AppliedClass`.
    classes: HashMap<SymbolId, ClassMetadata>,
    /// Finite shallow structural views keyed by their canonical applied head.
    applied_class_views: HashMap<TypeId, AppliedClassView>,
    /// Class heads whose shallow views are being materialized. Per-head
    /// recursion permits finite A-to-B expansion without unrolling A<T[]> forever.
    materializing_class_views: HashSet<SymbolId>,
    /// Same-symbol heads deferred by the current top-level materialization.
    /// One snapshot retries; descendants created by that retry are discarded.
    deferred_class_views: VecDeque<TypeId>,
    aliases: HashMap<SymbolId, AliasMetadata>,
    applied_alias_views: HashMap<TypeId, TypeId>,
    materializing_alias_views: HashSet<SymbolId>,
    deferred_alias_views: VecDeque<TypeId>,
    circular_aliases: HashSet<SymbolId>,
    substituted_alias_heads: Vec<TypeId>,
    preparing_substituted_aliases: HashSet<SymbolId>,
    /// Completed structural body for an interface symbol. Recursive member
    /// references use `Type::Named(symbol)` as an inert head and expand through
    /// this single view after the body has been interned.
    interface_structures: HashMap<SymbolId, TypeId>,
    /// Canonical synchronous iterable view for every array and tuple head.
    iterable_views: HashMap<TypeId, TypeId>,
}

impl Default for TypeTable {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeTable {
    /// Creates a table pre-populated with every primitive type.
    #[must_use]
    pub fn new() -> Self {
        let mut table = Self {
            types: Vec::new(),
            index: HashMap::new(),
            error: TypeId(0),
            any: TypeId(0),
            unknown: TypeId(0),
            never: TypeId(0),
            void: TypeId(0),
            null: TypeId(0),
            undefined: TypeId(0),
            boolean: TypeId(0),
            number: TypeId(0),
            bigint: TypeId(0),
            string: TypeId(0),
            symbol: TypeId(0),
            object: TypeId(0),
            object_symbol: None,
            collection_symbols: [None; 4],
            record_symbol: None,
            property_key_symbol: None,
            concat_array_symbol: None,
            type_parameter_constraints: HashMap::new(),
            type_parameter_defaults: HashMap::new(),
            classes: HashMap::new(),
            applied_class_views: HashMap::new(),
            materializing_class_views: HashSet::new(),
            deferred_class_views: VecDeque::new(),
            aliases: HashMap::new(),
            applied_alias_views: HashMap::new(),
            materializing_alias_views: HashSet::new(),
            deferred_alias_views: VecDeque::new(),
            circular_aliases: HashSet::new(),
            substituted_alias_heads: Vec::new(),
            preparing_substituted_aliases: HashSet::new(),
            interface_structures: HashMap::new(),
            iterable_views: HashMap::new(),
        };
        table.error = table.intern(Type::Error);
        table.any = table.intern(Type::Any);
        table.unknown = table.intern(Type::Unknown);
        table.never = table.intern(Type::Never);
        table.void = table.intern(Type::Void);
        table.null = table.intern(Type::Null);
        table.undefined = table.intern(Type::Undefined);
        table.boolean = table.intern(Type::Boolean);
        table.number = table.intern(Type::Number);
        table.bigint = table.intern(Type::BigInt);
        table.string = table.intern(Type::String);
        table.symbol = table.intern(Type::Symbol);
        table.object = table.intern(Type::Object);
        table
    }

    fn intern(&mut self, ty: Type) -> TypeId {
        if let Some(existing) = self.index.get(&ty) {
            return *existing;
        }
        let id = TypeId(u32::try_from(self.types.len()).expect("type count fits in u32"));
        self.types.push(ty.clone());
        self.index.insert(ty, id);
        id
    }

    /// Returns the interned representation of a type identity.
    #[must_use]
    pub fn get(&self, id: TypeId) -> &Type {
        &self.types[id.0 as usize]
    }

    pub(crate) fn iterable_view(&self, source: TypeId) -> Option<TypeId> {
        self.iterable_views.get(&source).copied()
    }
    /// Returns the type of a named property on a structural type, distributing
    /// over unions. `None` means the property is not present on the type.
    pub fn property_type(&mut self, ty: TypeId, name: &str) -> Option<TypeId> {
        let ty = self.named_structural_view(ty);
        let ty = match self.get(ty) {
            Type::Named(symbol) => self
                .classes
                .get(symbol)
                .and_then(|metadata| metadata.template.as_ref())
                .map_or(ty, |template| template.raw),
            _ => ty,
        };
        match self.get(ty).clone() {
            Type::ObjectType(object) => {
                if let Some(property) = object
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                {
                    return Some(property.type_id());
                }

                let numeric = name.parse::<usize>().is_ok();
                object
                    .index_signatures
                    .iter()
                    .find(|signature| {
                        signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.get(parameter.type_id()), Type::String)
                                || (numeric
                                    && matches!(self.get(parameter.type_id()), Type::Number))
                        })
                    })
                    .map(|signature| signature.value_type)
            }
            Type::Tuple(shape) => {
                if name == "length" {
                    return Some(match shape.max_arity() {
                        Some(max) if max == shape.min_arity() => {
                            self.number_literal(max.to_string().as_str())
                        }
                        _ => self.number(),
                    });
                }
                let index = name.parse::<usize>().ok()?;
                self.tuple_index_type(&shape, index)
            }
            Type::Array(element) => name.parse::<usize>().is_ok().then_some(element),
            Type::Union(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    found.push(self.property_type(member, name)?);
                }
                Some(self.union(&found))
            }
            Type::Intersection(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    if let Some(property) = self.property_type(member, name) {
                        found.push(property);
                    }
                }
                match found.len() {
                    0 => None,
                    1 => Some(found[0]),
                    _ => Some(self.intersection(found)),
                }
            }
            Type::AppliedClass { .. } => self
                .prepare_applied_class_view(ty)
                .and_then(|view| self.property_type(view, name)),
            Type::AppliedAlias { .. } => self
                .prepare_applied_alias_view(ty)
                .and_then(|view| self.property_type(view, name)),
            _ => None,
        }
    }

    pub(crate) fn generator_return_type(&mut self, ty: TypeId) -> Option<TypeId> {
        let ty = self.named_structural_view(ty);
        let ty = match self.get(ty) {
            Type::Named(symbol) => self
                .classes
                .get(symbol)
                .and_then(|metadata| metadata.template.as_ref())
                .map_or(ty, |template| template.raw),
            _ => ty,
        };
        match self.get(ty).clone() {
            Type::ObjectType(object) => object.generator_return,
            Type::Union(members) => {
                let mut returns = Vec::with_capacity(members.len());
                for member in members {
                    returns.push(self.generator_return_type(member)?);
                }
                Some(self.union(&returns))
            }
            Type::Intersection(members) => {
                let returns: Vec<TypeId> = members
                    .iter()
                    .filter_map(|&member| self.generator_return_type(member))
                    .collect();
                match returns.len() {
                    0 => None,
                    1 => Some(returns[0]),
                    _ => Some(self.intersection(returns)),
                }
            }
            Type::AppliedClass { .. } => self
                .prepare_applied_class_view(ty)
                .and_then(|view| self.generator_return_type(view)),
            Type::AppliedAlias { .. } => self
                .prepare_applied_alias_view(ty)
                .and_then(|view| self.generator_return_type(view)),
            _ => None,
        }
    }

    pub(crate) fn iterator_property_of(
        &mut self,
        ty: TypeId,
        protocol: ForOfMode,
    ) -> Option<IteratorProperty> {
        let ty = self.named_structural_view(ty);
        let ty = match self.get(ty) {
            Type::Named(symbol) => self
                .classes
                .get(symbol)
                .and_then(|metadata| metadata.template.as_ref())
                .map_or(ty, |template| template.raw),
            _ => ty,
        };
        match self.get(ty).clone() {
            Type::ObjectType(object) => match protocol {
                ForOfMode::Sync => object.iterator_property,
                ForOfMode::Async => object.async_iterator_property,
            },
            Type::ConstructorType { structural, .. } => {
                self.iterator_property_of(structural, protocol)
            }
            Type::AppliedClass { .. } => self
                .prepare_applied_class_view(ty)
                .and_then(|view| self.iterator_property_of(view, protocol)),
            Type::AppliedAlias { .. } => self
                .prepare_applied_alias_view(ty)
                .and_then(|view| self.iterator_property_of(view, protocol)),
            Type::Intersection(members) => {
                let mut properties = Vec::with_capacity(members.len());
                for member in members {
                    if let Some(property) = self.iterator_property_of(member, protocol) {
                        properties.push(property);
                    }
                }
                if properties.is_empty() {
                    return None;
                }
                let optional = properties.iter().all(IteratorProperty::optional);
                let mut declaring_types = Vec::new();
                for property in &properties {
                    for &owner in property.declaring_types() {
                        if !declaring_types.contains(&owner) {
                            declaring_types.push(owner);
                        }
                    }
                }
                let mut types = properties.iter().map(IteratorProperty::type_id);
                let first = types.next().expect("iterator properties are not empty");
                let type_id = match types.next() {
                    None => first,
                    Some(second) => self.intersection(
                        std::iter::once(first)
                            .chain(std::iter::once(second))
                            .chain(types)
                            .collect(),
                    ),
                };
                Some(IteratorProperty::new(type_id, optional).with_declaring_types(declaring_types))
            }
            _ => None,
        }
    }

    /// Returns the type of a named property when it is *read*, distributing
    /// over unions and intersections. For optional object properties, the
    /// result includes `undefined`. `None` means the property is not present.
    #[must_use]
    pub fn read_property_type(&mut self, ty: TypeId, name: &str) -> Option<TypeId> {
        let ty = self.named_structural_view(ty);
        match self.get(ty).clone() {
            Type::ObjectType(object) => {
                if let Some(property) = object
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                {
                    if property.optional() {
                        let undefined = self.undefined_type();
                        return Some(self.union(&[property.type_id(), undefined]));
                    }
                    return Some(property.type_id());
                }

                let numeric = name.parse::<usize>().is_ok();
                object
                    .index_signatures
                    .iter()
                    .find(|signature| {
                        signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.get(parameter.type_id()), Type::String)
                                || (numeric
                                    && matches!(self.get(parameter.type_id()), Type::Number))
                        })
                    })
                    .map(|signature| signature.value_type)
            }
            Type::Tuple(shape) => {
                if name == "length" {
                    return Some(match shape.max_arity() {
                        Some(max) if max == shape.min_arity() => {
                            self.number_literal(max.to_string().as_str())
                        }
                        _ => self.number(),
                    });
                }
                let index = name.parse::<usize>().ok()?;
                self.tuple_index_type(&shape, index)
            }
            Type::Array(element) => {
                if name.parse::<usize>().is_ok() {
                    return Some(element);
                }
                if name == "concat" {
                    return Some(self.array_concat_member_type(element));
                }
                None
            }
            Type::Union(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    found.push(self.read_property_type(member, name)?);
                }
                Some(self.union(&found))
            }
            Type::Intersection(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    if let Some(property) = self.read_property_type(member, name) {
                        found.push(property);
                    }
                }
                match found.len() {
                    0 => None,
                    1 => Some(found[0]),
                    _ => Some(self.intersection(found)),
                }
            }
            Type::AppliedClass { .. } => self
                .prepare_applied_class_view(ty)
                .and_then(|view| self.read_property_type(view, name)),
            Type::AppliedAlias { .. } => self
                .prepare_applied_alias_view(ty)
                .and_then(|view| self.read_property_type(view, name)),
            _ => None,
        }
    }

    fn tuple_index_type(&mut self, shape: &TupleShape, index: usize) -> Option<TypeId> {
        let mut elements = shape.element_types_at(index);
        if elements.is_empty() {
            return None;
        }
        if index >= shape.min_arity() {
            elements.push(self.undefined_type());
        }
        Some(self.union(&elements))
    }

    #[must_use]
    pub const fn error_type(&self) -> TypeId {
        self.error
    }
    #[must_use]
    pub const fn any(&self) -> TypeId {
        self.any
    }
    #[must_use]
    pub const fn unknown(&self) -> TypeId {
        self.unknown
    }
    #[must_use]
    pub const fn never(&self) -> TypeId {
        self.never
    }
    #[must_use]
    pub const fn void(&self) -> TypeId {
        self.void
    }
    #[must_use]
    pub const fn null_type(&self) -> TypeId {
        self.null
    }
    #[must_use]
    pub const fn undefined_type(&self) -> TypeId {
        self.undefined
    }
    #[must_use]
    pub const fn boolean(&self) -> TypeId {
        self.boolean
    }
    #[must_use]
    pub const fn number(&self) -> TypeId {
        self.number
    }
    #[must_use]
    pub const fn bigint(&self) -> TypeId {
        self.bigint
    }
    #[must_use]
    pub const fn string(&self) -> TypeId {
        self.string
    }
    #[must_use]
    pub const fn symbol_type(&self) -> TypeId {
        self.symbol
    }
    #[must_use]
    pub const fn object(&self) -> TypeId {
        self.object
    }

    #[must_use]
    pub const fn object_symbol(&self) -> Option<SymbolId> {
        self.object_symbol
    }

    #[must_use]
    pub fn is_object_symbol(&self, symbol: SymbolId) -> bool {
        self.object_symbol == Some(symbol)
    }

    fn intrinsic_collection_index(&self, symbol: SymbolId) -> Option<usize> {
        self.collection_symbols
            .iter()
            .position(|candidate| *candidate == Some(symbol))
    }

    fn is_record_symbol(&self, symbol: SymbolId) -> bool {
        self.record_symbol == Some(symbol)
    }

    /// Predeclares a class before its bounds, heritage, or members are resolved.
    pub fn declare_class(&mut self, symbol: SymbolId, parameters: Vec<SymbolId>) {
        self.classes.entry(symbol).or_insert_with(|| ClassMetadata {
            bounds: vec![TypeParameterBounds::NONE; parameters.len()],
            parameters,
            bounds_resolving: false,
            bounds_ready: false,
            template: None,
        });
    }

    #[must_use]
    pub fn has_class(&self, symbol: SymbolId) -> bool {
        self.classes.contains_key(&symbol)
    }

    #[must_use]
    pub fn class_type_parameters(&self, symbol: SymbolId) -> &[SymbolId] {
        self.classes
            .get(&symbol)
            .map_or(&[], |metadata| metadata.parameters.as_slice())
    }

    pub(crate) fn class_template_raw(&self, symbol: SymbolId) -> Option<TypeId> {
        self.classes
            .get(&symbol)?
            .template
            .as_ref()
            .map(|template| template.raw)
    }

    #[must_use]
    pub fn class_type_parameter_bounds(&self, symbol: SymbolId) -> &[TypeParameterBounds] {
        self.classes
            .get(&symbol)
            .map_or(&[], |metadata| metadata.bounds.as_slice())
    }

    #[must_use]
    pub fn class_bounds_ready(&self, symbol: SymbolId) -> bool {
        self.classes
            .get(&symbol)
            .is_some_and(|metadata| metadata.bounds_ready)
    }

    /// Starts resolving class defaults and constraints. Recursive references see
    /// the prebound parameter symbols and do not start a second resolution.
    pub fn begin_class_bounds(&mut self, symbol: SymbolId) -> bool {
        let Some(metadata) = self.classes.get_mut(&symbol) else {
            return false;
        };
        if metadata.bounds_ready || metadata.bounds_resolving {
            return false;
        }
        metadata.bounds_resolving = true;
        true
    }

    pub fn finish_class_bounds(&mut self, symbol: SymbolId, bounds: Vec<TypeParameterBounds>) {
        let Some(metadata) = self.classes.get_mut(&symbol) else {
            return;
        };
        debug_assert_eq!(metadata.parameters.len(), bounds.len());
        metadata.bounds = bounds;
        metadata.bounds_resolving = false;
        metadata.bounds_ready = true;
    }

    /// Sets resolved type-parameter bounds for a class in one step.
    pub fn set_class_bounds(&mut self, symbol: SymbolId, bounds: Vec<TypeParameterBounds>) {
        self.finish_class_bounds(symbol, bounds);
    }

    pub fn declare_alias(&mut self, symbol: SymbolId, parameters: Vec<SymbolId>) {
        self.aliases.entry(symbol).or_insert_with(|| AliasMetadata {
            bounds: vec![TypeParameterBounds::NONE; parameters.len()],
            parameters,
            bounds_resolving: false,
            bounds_ready: false,
            template: None,
        });
    }

    #[must_use]
    pub fn has_alias(&self, symbol: SymbolId) -> bool {
        self.aliases.contains_key(&symbol)
    }

    #[must_use]
    pub fn alias_type_parameters(&self, symbol: SymbolId) -> &[SymbolId] {
        self.aliases
            .get(&symbol)
            .map_or(&[], |metadata| metadata.parameters.as_slice())
    }

    pub(crate) fn alias_template_raw(&self, symbol: SymbolId) -> Option<TypeId> {
        self.aliases.get(&symbol)?.template
    }

    #[must_use]
    pub fn alias_type_parameter_bounds(&self, symbol: SymbolId) -> &[TypeParameterBounds] {
        self.aliases
            .get(&symbol)
            .map_or(&[], |metadata| metadata.bounds.as_slice())
    }

    #[must_use]
    pub fn alias_bounds_ready(&self, symbol: SymbolId) -> bool {
        self.aliases
            .get(&symbol)
            .is_some_and(|metadata| metadata.bounds_ready)
    }

    pub fn begin_alias_bounds(&mut self, symbol: SymbolId) -> bool {
        let Some(metadata) = self.aliases.get_mut(&symbol) else {
            return false;
        };
        if metadata.bounds_ready || metadata.bounds_resolving {
            return false;
        }
        metadata.bounds_resolving = true;
        true
    }

    pub fn finish_alias_bounds(&mut self, symbol: SymbolId, bounds: Vec<TypeParameterBounds>) {
        let Some(metadata) = self.aliases.get_mut(&symbol) else {
            return;
        };
        debug_assert_eq!(metadata.parameters.len(), bounds.len());
        metadata.bounds = bounds;
        metadata.bounds_resolving = false;
        metadata.bounds_ready = true;
    }

    pub(crate) fn intern_applied_alias(
        &mut self,
        symbol: SymbolId,
        arguments: Vec<TypeId>,
    ) -> TypeId {
        debug_assert!(
            self.aliases
                .get(&symbol)
                .is_none_or(|metadata| metadata.parameters.len() == arguments.len())
        );
        self.intern(Type::AppliedAlias { symbol, arguments })
    }

    pub fn applied_alias(&mut self, symbol: SymbolId, arguments: Vec<TypeId>) -> TypeId {
        let type_id = self.intern_applied_alias(symbol, arguments);
        self.materialize_applied_alias_view(type_id);
        type_id
    }

    pub fn publish_alias_template(&mut self, symbol: SymbolId, raw: TypeId) {
        let Some(metadata) = self.aliases.get_mut(&symbol) else {
            return;
        };
        debug_assert!(metadata.template.is_none());
        metadata.template = Some(raw);
        let heads: Vec<TypeId> = self
            .types
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                matches!(ty, Type::AppliedAlias { symbol: head, .. } if *head == symbol).then_some(
                    TypeId(u32::try_from(index).expect("type count fits in u32")),
                )
            })
            .collect();
        for head in heads {
            self.materialize_applied_alias_view(head);
        }
    }

    pub fn prepare_applied_alias_view(&mut self, type_id: TypeId) -> Option<TypeId> {
        self.materialize_applied_alias_view(type_id);
        self.applied_alias_view(type_id)
    }

    pub(crate) fn substituted_alias_marker(&self) -> usize {
        self.substituted_alias_heads.len()
    }

    pub(crate) fn intern_substituted_alias(
        &mut self,
        symbol: SymbolId,
        arguments: Vec<TypeId>,
    ) -> TypeId {
        let type_id = self.intern_applied_alias(symbol, arguments);
        if !self.applied_alias_views.contains_key(&type_id) {
            self.substituted_alias_heads.push(type_id);
        }
        type_id
    }

    pub(crate) fn prepare_substituted_aliases(&mut self, marker: usize) {
        let heads = self.substituted_alias_heads.split_off(marker);
        for type_id in heads {
            let Type::AppliedAlias { symbol, .. } = self.get(type_id) else {
                continue;
            };
            let symbol = *symbol;
            if !self.preparing_substituted_aliases.insert(symbol) {
                continue;
            }
            self.materialize_applied_alias_view(type_id);
            self.preparing_substituted_aliases.remove(&symbol);
        }
    }

    #[must_use]
    pub fn applied_alias_view(&self, type_id: TypeId) -> Option<TypeId> {
        if !matches!(self.get(type_id), Type::AppliedAlias { .. }) {
            return None;
        }
        self.applied_alias_views.get(&type_id).copied()
    }

    fn materialize_applied_alias_view(&mut self, type_id: TypeId) {
        self.materialize_one_applied_alias_view(type_id);
        if !self.materializing_alias_views.is_empty() {
            return;
        }
        let deferred = self.deferred_alias_views.len();
        for _ in 0..deferred {
            let Some(type_id) = self.deferred_alias_views.pop_front() else {
                break;
            };
            self.materialize_one_applied_alias_view(type_id);
        }
    }

    fn materialize_one_applied_alias_view(&mut self, type_id: TypeId) {
        let Type::AppliedAlias { symbol, arguments } = self.get(type_id).clone() else {
            return;
        };
        let Some(metadata) = self.aliases.get(&symbol).cloned() else {
            return;
        };
        let Some(template) = metadata.template else {
            return;
        };
        if self.applied_alias_views.contains_key(&type_id)
            || arguments.len() != metadata.parameters.len()
        {
            return;
        }
        if !self.materializing_alias_views.insert(symbol) {
            if !self.deferred_alias_views.contains(&type_id) {
                self.deferred_alias_views.push_back(type_id);
            }
            return;
        }
        let substitutions = metadata
            .parameters
            .into_iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                InferredTypeArgument::new(parameter, argument, InferenceProvenance::Explicit)
            })
            .collect();
        let view = InferredTypeArguments::new(substitutions).instantiate(self, template);
        let removed = self.materializing_alias_views.remove(&symbol);
        debug_assert!(removed);
        if view == type_id {
            self.circular_aliases.insert(symbol);
        }
        self.applied_alias_views.insert(type_id, view);
    }

    pub fn is_circular_alias(&mut self, symbol: SymbolId) -> bool {
        if self.circular_aliases.contains(&symbol) {
            return true;
        }
        let parameters = self.alias_type_parameters(symbol).to_vec();
        let arguments = parameters
            .into_iter()
            .map(|parameter| self.named(parameter))
            .collect();
        let mut current = self.applied_alias(symbol, arguments);
        let mut path = Vec::new();
        let mut positions = HashMap::new();
        loop {
            let Type::AppliedAlias {
                symbol: current_symbol,
                ..
            } = self.get(current)
            else {
                return false;
            };
            let current_symbol = *current_symbol;
            if self.circular_aliases.contains(&current_symbol) {
                return self.circular_aliases.contains(&symbol);
            }
            if let Some(start) = positions.get(&current_symbol).copied() {
                self.circular_aliases.extend(path[start..].iter().copied());
                return self.circular_aliases.contains(&symbol);
            }
            positions.insert(current_symbol, path.len());
            path.push(current_symbol);
            let Some(view) = self.prepare_applied_alias_view(current) else {
                return false;
            };
            if view == current {
                self.circular_aliases.insert(current_symbol);
                return current_symbol == symbol;
            }
            if !matches!(self.get(view), Type::AppliedAlias { .. }) {
                return false;
            }
            current = view;
        }
    }

    /// Returns the `(symbol, arguments)` identity of an applied class type,
    /// or `None` for any other type.
    #[must_use]
    pub fn class_identity(&self, type_id: TypeId) -> Option<(SymbolId, &[TypeId])> {
        match self.get(type_id) {
            Type::AppliedClass { symbol, arguments } => Some((*symbol, arguments)),
            _ => None,
        }
    }

    pub fn publish_provisional_class_template(&mut self, symbol: SymbolId, raw: TypeId) {
        self.publish_class_template(symbol, raw, ClassState::Provisional);
    }

    pub fn publish_final_class_template(&mut self, symbol: SymbolId, raw: TypeId) {
        self.publish_class_template(symbol, raw, ClassState::Final);
    }

    fn publish_class_template(&mut self, symbol: SymbolId, raw: TypeId, state: ClassState) {
        let Some(metadata) = self.classes.get_mut(&symbol) else {
            return;
        };
        debug_assert!(!matches!(
            metadata.template.as_ref().map(|template| template.state),
            Some(ClassState::Final)
        ));
        let revision = metadata
            .template
            .as_ref()
            .map_or(1, |template| template.revision.saturating_add(1));
        metadata.template = Some(ClassTemplate {
            raw,
            revision,
            state,
        });

        let stale: Vec<TypeId> = self
            .applied_class_views
            .keys()
            .copied()
            .filter(|type_id| matches!(self.get(*type_id), Type::AppliedClass { symbol: head, .. } if *head == symbol))
            .collect();
        for type_id in stale {
            self.applied_class_views.remove(&type_id);
        }
        let heads: Vec<TypeId> = self
            .types
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                matches!(ty, Type::AppliedClass { symbol: head, .. } if *head == symbol).then_some(
                    TypeId(u32::try_from(index).expect("type count fits in u32")),
                )
            })
            .collect();
        for head in heads {
            self.materialize_applied_class_view(head);
        }
    }

    /// Interns one complete class application and prepares its current shallow view.
    ///
    /// Argument completion and constraint checking belong to the binder boundary;
    /// silently padding or truncating here would collapse distinct source programs
    /// onto an invented semantic identity.
    pub fn applied_class(&mut self, symbol: SymbolId, arguments: Vec<TypeId>) -> TypeId {
        debug_assert!(
            self.classes
                .get(&symbol)
                .is_none_or(|metadata| metadata.parameters.len() == arguments.len())
        );
        let type_id = self.intern(Type::AppliedClass { symbol, arguments });
        self.materialize_applied_class_view(type_id);
        type_id
    }

    /// Interns a `typeof C` constructor (static-side) type. The structural
    /// view is the `ObjectType` built by `class_static_type`; property and
    /// construct-signature lookup delegate to it.
    pub fn constructor_type(
        &mut self,
        symbol: SymbolId,
        arguments: Vec<TypeId>,
        structural: TypeId,
    ) -> TypeId {
        self.intern(Type::ConstructorType {
            symbol,
            arguments,
            structural,
        })
    }

    /// Returns the parameter-relative self head used inside a class declaration.
    pub fn declared_class(&mut self, symbol: SymbolId) -> Option<TypeId> {
        let parameters = self.classes.get(&symbol)?.parameters.clone();
        let arguments = parameters
            .into_iter()
            .map(|parameter| self.named(parameter))
            .collect();
        Some(self.applied_class(symbol, arguments))
    }

    /// Ensures and returns the finite shallow view for one applied root.
    pub fn prepare_applied_class_view(&mut self, type_id: TypeId) -> Option<TypeId> {
        self.materialize_applied_class_view(type_id);
        self.applied_class_view(type_id)
    }

    /// Returns a previously prepared shallow view. Nested applications remain
    /// opaque AppliedClass heads and are never expanded by this accessor.
    #[must_use]
    pub fn applied_class_view(&self, type_id: TypeId) -> Option<TypeId> {
        let Type::AppliedClass { symbol, .. } = self.get(type_id) else {
            return None;
        };
        let revision = self.classes.get(symbol)?.template.as_ref()?.revision;
        self.applied_class_views
            .get(&type_id)
            .filter(|view| view.revision == revision)
            .map(|view| view.type_id)
    }

    fn materialize_applied_class_view(&mut self, type_id: TypeId) {
        let top_level = self.materializing_class_views.is_empty();
        if top_level {
            debug_assert!(self.deferred_class_views.is_empty());
        }
        self.materialize_one_applied_class_view(type_id);
        if !top_level {
            return;
        }

        let deferred = self.deferred_class_views.len();
        for _ in 0..deferred {
            let Some(type_id) = self.deferred_class_views.pop_front() else {
                break;
            };
            self.materialize_one_applied_class_view(type_id);
        }
        self.deferred_class_views.clear();
    }

    fn materialize_one_applied_class_view(&mut self, type_id: TypeId) {
        let Type::AppliedClass { symbol, arguments } = self.get(type_id).clone() else {
            return;
        };
        let Some(metadata) = self.classes.get(&symbol).cloned() else {
            return;
        };
        let Some(template) = metadata.template else {
            return;
        };
        if self
            .applied_class_views
            .get(&type_id)
            .is_some_and(|view| view.revision == template.revision)
        {
            return;
        }
        if arguments.len() != metadata.parameters.len() {
            return;
        }
        if !self.materializing_class_views.insert(symbol) {
            if !self.deferred_class_views.contains(&type_id) {
                self.deferred_class_views.push_back(type_id);
            }
            return;
        }
        let substitutions = metadata
            .parameters
            .into_iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                InferredTypeArgument::new(parameter, argument, InferenceProvenance::Explicit)
            })
            .collect();
        let view = InferredTypeArguments::new(substitutions).instantiate(self, template.raw);
        let removed = self.materializing_class_views.remove(&symbol);
        debug_assert!(removed);
        self.applied_class_views.insert(
            type_id,
            AppliedClassView {
                revision: template.revision,
                type_id: view,
            },
        );
    }

    /// Records the completed structural body behind an interface's named head.
    pub fn set_interface_structure(&mut self, symbol: SymbolId, structure: TypeId) {
        self.interface_structures.insert(symbol, structure);
    }

    /// Returns the completed structural body behind an interface symbol.
    #[must_use]
    pub fn interface_structure(&self, symbol: SymbolId) -> Option<TypeId> {
        self.interface_structures.get(&symbol).copied()
    }

    /// Expands one named interface head to its completed structural body.
    /// Other named identities remain inert.
    #[must_use]
    pub fn named_structural_view(&self, type_id: TypeId) -> TypeId {
        match self.get(type_id) {
            Type::Named(symbol) => self.interface_structure(*symbol).unwrap_or(type_id),
            _ => type_id,
        }
    }
    /// Expands one named interface, `this` constraint, or applied class to
    /// its completed structural body for indexed access.
    #[must_use]
    pub fn indexed_access_view(&mut self, type_id: TypeId) -> TypeId {
        let view = self.named_structural_view(type_id);
        if view != type_id {
            return view;
        }
        if let Type::This { constraint, .. } = self.get(type_id) {
            return self.indexed_access_view(*constraint);
        }
        if let Some(view) = self.prepare_applied_alias_view(type_id) {
            return view;
        }
        self.prepare_applied_class_view(type_id).unwrap_or(type_id)
    }

    /// Reduces `keyof T` when `T` is a concrete object, tuple, or array;
    /// otherwise interns a deferred `Type::Keyof`.
    pub fn keyof(&mut self, operand: TypeId) -> TypeId {
        self.try_reduce_keyof(operand)
            .unwrap_or_else(|| self.intern(Type::Keyof(operand)))
    }

    fn try_reduce_keyof(&mut self, operand: TypeId) -> Option<TypeId> {
        let view = self.indexed_access_view(operand);
        self.keyof_view(view)
    }

    fn keyof_view(&mut self, view: TypeId) -> Option<TypeId> {
        match self.get(view).clone() {
            Type::ObjectType(object) => {
                let mut keys =
                    Vec::with_capacity(object.properties.len() + object.index_signatures.len());
                for property in &object.properties {
                    let name = property.name.as_ref();
                    let key = if name.parse::<usize>().is_ok() {
                        self.number_literal(name)
                    } else {
                        self.string_literal(name)
                    };
                    keys.push(key);
                }
                for signature in &object.index_signatures {
                    if let Some(parameter) = signature.parameters.first() {
                        keys.push(parameter.type_id());
                    }
                }
                Some(self.union_or_single(keys))
            }
            Type::Tuple(shape) => {
                if shape.rest.is_some() {
                    Some(self.number())
                } else {
                    let count = shape.prefix.len() + shape.suffix.len();
                    let mut keys = Vec::with_capacity(count);
                    for i in 0..count {
                        keys.push(self.number_literal(i.to_string().as_str()));
                    }
                    Some(self.union_or_single(keys))
                }
            }
            Type::Array(_) => Some(self.number()),
            Type::Record { key, .. } => Some(key),
            Type::Union(members) => {
                // keyof(A | B) = keyof(A) & keyof(B)
                let mut keys = Vec::with_capacity(members.len());
                for &member in &members {
                    let key = self.keyof_view(member)?;
                    keys.push(key);
                }
                Some(self.intersection(keys))
            }
            Type::Intersection(members) => {
                // keyof(A & B) = keyof(A) | keyof(B)
                let mut keys = Vec::new();
                for &member in &members {
                    let key = self.keyof_view(member)?;
                    keys.push(key);
                }
                Some(self.union_or_single(keys))
            }
            _ => None,
        }
    }
    /// Reduces `Record<K, V>` for concrete keys and preserves a mapped type
    /// while `K` still depends on a type parameter.
    pub fn record(&mut self, key: TypeId, value: TypeId) -> TypeId {
        let mut properties = Vec::new();
        let mut index_keys = Vec::new();
        match self.collect_record_members(key, value, &mut properties, &mut index_keys) {
            RecordKeyState::Concrete => {
                index_keys.sort_by_key(|type_id| type_id.get());
                index_keys.dedup();
                let index_signatures = index_keys
                    .into_iter()
                    .map(|key_type| IndexSignature {
                        readonly: false,
                        parameters: vec![FunctionParameter::new(
                            "key".to_owned(),
                            key_type,
                            false,
                            false,
                        )],
                        value_type: value,
                        declaring_types: Vec::new(),
                    })
                    .collect();
                self.object_type_with_members(ObjectType {
                    properties,
                    call_signatures: Vec::new(),
                    construct_signatures: Vec::new(),
                    index_signatures,
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: None,
                })
            }
            RecordKeyState::Deferred => self.intern(Type::Record { key, value }),
            RecordKeyState::Invalid => self.error_type(),
        }
    }

    fn collect_record_members(
        &self,
        key: TypeId,
        value: TypeId,
        properties: &mut Vec<PropertyType>,
        index_keys: &mut Vec<TypeId>,
    ) -> RecordKeyState {
        match self.get(key) {
            Type::String => index_keys.push(self.string()),
            Type::Number => index_keys.push(self.number()),
            Type::Symbol => index_keys.push(self.symbol_type()),
            Type::StringLiteral(name) => {
                let Ok(name) = name.to_utf8_strict() else {
                    return RecordKeyState::Invalid;
                };
                properties.push(PropertyType::new(name, false, value));
            }
            Type::NumberLiteral(name) => {
                properties.push(PropertyType::new(name.clone(), false, value));
            }
            Type::Any => index_keys.extend([self.string(), self.number(), self.symbol_type()]),
            Type::Never => {}
            Type::Union(members) => {
                let mut deferred = false;
                for member in members {
                    match self.collect_record_members(*member, value, properties, index_keys) {
                        RecordKeyState::Concrete => {}
                        RecordKeyState::Deferred => deferred = true,
                        RecordKeyState::Invalid => return RecordKeyState::Invalid,
                    }
                }
                if deferred {
                    return RecordKeyState::Deferred;
                }
            }
            Type::Intersection(members) => {
                let mut domains = Vec::with_capacity(members.len());
                let mut unresolved = false;
                for member in members {
                    let mut member_properties = Vec::new();
                    let mut member_indexes = Vec::new();
                    match self.collect_record_members(
                        *member,
                        value,
                        &mut member_properties,
                        &mut member_indexes,
                    ) {
                        RecordKeyState::Concrete => {
                            domains.push((member_properties, member_indexes));
                        }
                        RecordKeyState::Deferred => unresolved = true,
                        RecordKeyState::Invalid => {}
                    }
                }
                if domains.len() != members.len() {
                    return if unresolved || !domains.is_empty() {
                        RecordKeyState::Deferred
                    } else {
                        RecordKeyState::Invalid
                    };
                }

                let mut literal_keys = domains
                    .iter()
                    .flat_map(|(member_properties, _)| member_properties.iter().cloned())
                    .filter(|property| {
                        members.iter().all(|member| {
                            self.property_name_assignable_to_key(property.name(), *member)
                        })
                    })
                    .collect::<Vec<_>>();
                literal_keys.sort_by(|left, right| left.name().cmp(right.name()));
                literal_keys.dedup_by(|left, right| left.name() == right.name());
                properties.extend(literal_keys);

                for domain in [self.string(), self.number(), self.symbol_type()] {
                    if domains
                        .iter()
                        .all(|(_, member_indexes)| member_indexes.contains(&domain))
                    {
                        index_keys.push(domain);
                    }
                }
            }
            Type::Named(_) | Type::Keyof(_) | Type::IndexedAccess { .. } => {
                return RecordKeyState::Deferred;
            }
            _ => return RecordKeyState::Invalid,
        }
        RecordKeyState::Concrete
    }
    #[must_use]
    pub(crate) fn property_name_assignable_to_key(&self, name: &str, key: TypeId) -> bool {
        match self.get(key) {
            Type::Any | Type::Error | Type::String => true,
            Type::Number => name
                .parse::<f64>()
                .ok()
                .is_some_and(|number| format_number(number) == name),
            Type::StringLiteral(literal) => literal
                .to_utf8_strict()
                .is_ok_and(|literal| literal == name),
            Type::NumberLiteral(literal) => literal.as_ref() == name,
            Type::Union(members) => members
                .iter()
                .any(|member| self.property_name_assignable_to_key(name, *member)),
            Type::Intersection(members) => members
                .iter()
                .all(|member| self.property_name_assignable_to_key(name, *member)),
            Type::Named(_) => false,
            _ => false,
        }
    }

    /// Resolves an indexed access `T[K]` when `T` and `K` are sufficiently
    /// concrete; otherwise interns a deferred `Type::IndexedAccess`.
    pub fn indexed_access(&mut self, object: TypeId, index: TypeId) -> TypeId {
        self.try_reduce_indexed_access(object, index)
            .unwrap_or_else(|| self.intern(Type::IndexedAccess { object, index }))
    }

    pub(super) fn indexed_access_constraint_view(&self, source: TypeId) -> IndexedAccessConstraint {
        let Type::IndexedAccess { object, index } = self.get(source) else {
            return IndexedAccessConstraint::Invalid;
        };
        let mut active = HashSet::new();
        self.indexed_access_constraint(*object, *index, &mut active)
    }

    fn indexed_access_constraint(
        &self,
        object: TypeId,
        index: TypeId,
        active: &mut HashSet<(TypeId, TypeId)>,
    ) -> IndexedAccessConstraint {
        let Ok(index) = self.type_parameter_constraint_view(index) else {
            return IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque);
        };
        let Ok(object) = self.type_parameter_constraint_view(object) else {
            return IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque);
        };
        let pair = (object, index);
        if !active.insert(pair) {
            return IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque);
        }

        let result = self.indexed_access_constraint_inner(object, index, active);
        active.remove(&pair);
        result
    }

    fn type_parameter_constraint_view(&self, type_id: TypeId) -> Result<TypeId, ()> {
        let mut current = type_id;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(current) {
                return Err(());
            }
            let Type::Named(symbol) = self.get(current) else {
                return Ok(current);
            };
            let Some(constraint) = self.type_parameter_constraint(*symbol) else {
                return Ok(current);
            };
            current = constraint;
        }
    }

    fn indexed_access_constraint_inner(
        &self,
        object: TypeId,
        index: TypeId,
        active: &mut HashSet<(TypeId, TypeId)>,
    ) -> IndexedAccessConstraint {
        if let Type::Union(indexes) = self.get(index) {
            let mut members = Vec::with_capacity(indexes.len());
            for &index in indexes {
                match self.indexed_access_constraint(object, index, active) {
                    IndexedAccessConstraint::Reduced(member) => members.push(member),
                    IndexedAccessConstraint::Invalid => {
                        return IndexedAccessConstraint::Invalid;
                    }
                }
            }
            return self.constraint_union(members);
        }

        let object = self.constraint_structural_view(object);
        match self.get(object) {
            Type::Union(objects) => {
                let mut members = Vec::with_capacity(objects.len());
                for &object in objects {
                    match self.indexed_access_constraint(object, index, active) {
                        IndexedAccessConstraint::Reduced(member) => members.push(member),
                        IndexedAccessConstraint::Invalid => {
                            return IndexedAccessConstraint::Invalid;
                        }
                    }
                }
                self.constraint_union(members)
            }
            Type::Intersection(objects) => {
                let mut members = Vec::with_capacity(objects.len());
                for &object in objects {
                    match self.indexed_access_constraint(object, index, active) {
                        IndexedAccessConstraint::Reduced(member) => members.push(member),
                        IndexedAccessConstraint::Invalid => {}
                    }
                }
                if members.is_empty() {
                    return IndexedAccessConstraint::Invalid;
                }
                self.constraint_intersection(members)
            }
            _ => self.indexed_access_constraint_leaf(object, index),
        }
    }

    fn constraint_structural_view(&self, type_id: TypeId) -> TypeId {
        let named = self.named_structural_view(type_id);
        if named != type_id {
            return named;
        }
        match self.get(type_id) {
            Type::AppliedClass { .. } => self.applied_class_view(type_id).unwrap_or(type_id),
            Type::AppliedAlias { .. } => self.applied_alias_view(type_id).unwrap_or(type_id),
            _ => type_id,
        }
    }

    fn constraint_type_expr(&self, type_id: TypeId) -> ConstraintTypeExpr {
        match self.get(type_id) {
            Type::Union(members) => ConstraintTypeExpr::Union(
                members
                    .iter()
                    .map(|member| self.constraint_type_expr(*member))
                    .collect(),
            ),
            Type::Intersection(members) => ConstraintTypeExpr::Intersection(
                members
                    .iter()
                    .map(|member| self.constraint_type_expr(*member))
                    .collect(),
            ),
            _ => ConstraintTypeExpr::Id(type_id),
        }
    }

    fn indexed_access_constraint_leaf(
        &self,
        object: TypeId,
        index: TypeId,
    ) -> IndexedAccessConstraint {
        match self.get(index) {
            Type::StringLiteral(name) => {
                let Ok(name) = name.to_utf8_strict() else {
                    return IndexedAccessConstraint::Invalid;
                };
                let key = name
                    .parse::<f64>()
                    .ok()
                    .filter(|number| format_number(*number) == name)
                    .map_or(self.string(), |_| self.number());
                self.named_index_constraint(object, &name, key)
            }
            Type::NumberLiteral(name) => match self.get(object) {
                Type::String => {
                    IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.string()))
                }
                _ => self.named_index_constraint(object, name, self.number()),
            },
            Type::String => self.index_signature_constraint(object, self.string()),
            Type::Number => self.number_index_constraint(object),
            Type::Symbol => self.index_signature_constraint(object, self.symbol_type()),
            Type::Any => IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.any())),
            Type::Never => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.never()))
            }
            Type::Named(_)
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Intersection(_) => IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque),
            _ => IndexedAccessConstraint::Invalid,
        }
    }

    fn named_index_constraint(
        &self,
        object: TypeId,
        name: &str,
        key: TypeId,
    ) -> IndexedAccessConstraint {
        match self.get(object) {
            Type::ObjectType(object_type) => {
                if let Some(property) = object_type
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                {
                    return IndexedAccessConstraint::Reduced(
                        self.constraint_type_expr(property.type_id()),
                    );
                }
                self.index_signature_constraint(object, key)
            }
            Type::Tuple(shape) => {
                let Ok(index) = name.parse::<usize>() else {
                    return IndexedAccessConstraint::Invalid;
                };
                let mut elements = shape.element_types_at(index);
                if elements.is_empty() {
                    return IndexedAccessConstraint::Invalid;
                }
                if index >= shape.min_arity() {
                    elements.push(self.undefined_type());
                }
                self.constraint_union(
                    elements
                        .into_iter()
                        .map(|element| self.constraint_type_expr(element))
                        .collect(),
                )
            }
            Type::Array(element) if key == self.number() => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(*element))
            }
            Type::Any | Type::Error => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(object))
            }
            Type::Unknown => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.unknown()))
            }
            Type::Never => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.never()))
            }
            Type::Named(_) | Type::AppliedClass { .. } | Type::AppliedAlias { .. } => {
                IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque)
            }
            _ => IndexedAccessConstraint::Invalid,
        }
    }

    fn number_index_constraint(&self, object: TypeId) -> IndexedAccessConstraint {
        match self.get(object) {
            Type::Array(element) => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(*element))
            }
            Type::Tuple(shape) => self.constraint_union(
                shape
                    .all_element_types()
                    .into_iter()
                    .map(|element| self.constraint_type_expr(element))
                    .collect(),
            ),
            Type::ObjectType(_) => self.index_signature_constraint(object, self.number()),
            Type::String => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.string()))
            }
            Type::Any | Type::Error => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(object))
            }
            Type::Unknown => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.unknown()))
            }
            Type::Never => {
                IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.never()))
            }
            Type::Named(_) | Type::AppliedClass { .. } | Type::AppliedAlias { .. } => {
                IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Opaque)
            }
            _ => IndexedAccessConstraint::Invalid,
        }
    }

    fn index_signature_constraint(&self, object: TypeId, key: TypeId) -> IndexedAccessConstraint {
        let Type::ObjectType(object) = self.get(object) else {
            return IndexedAccessConstraint::Invalid;
        };
        let find = |wanted| {
            object.index_signatures.iter().find(|signature| {
                signature
                    .parameters
                    .first()
                    .is_some_and(|parameter| parameter.type_id() == wanted)
            })
        };
        let signature =
            find(key).or_else(|| (key == self.number()).then(|| find(self.string()))?);
        signature.map_or(IndexedAccessConstraint::Invalid, |signature| {
            IndexedAccessConstraint::Reduced(self.constraint_type_expr(signature.value_type))
        })
    }

    fn constraint_union(&self, members: Vec<ConstraintTypeExpr>) -> IndexedAccessConstraint {
        match members.len() {
            0 => IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.never())),
            1 => IndexedAccessConstraint::Reduced(
                members.into_iter().next().expect("one member exists"),
            ),
            _ => IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Union(
                members.into_boxed_slice(),
            )),
        }
    }

    fn constraint_intersection(&self, members: Vec<ConstraintTypeExpr>) -> IndexedAccessConstraint {
        match members.len() {
            0 => IndexedAccessConstraint::Reduced(self.constraint_type_expr(self.unknown())),
            1 => IndexedAccessConstraint::Reduced(
                members.into_iter().next().expect("one member exists"),
            ),
            _ => IndexedAccessConstraint::Reduced(ConstraintTypeExpr::Intersection(
                members.into_boxed_slice(),
            )),
        }
    }

    fn try_reduce_indexed_access(&mut self, object: TypeId, index: TypeId) -> Option<TypeId> {
        match self.get(index).clone() {
            Type::Union(members) => {
                let mut found = Vec::with_capacity(members.len());
                for &member in &members {
                    let reduced = self.indexed_access(object, member);
                    if reduced == self.error_type() {
                        return Some(reduced);
                    }
                    found.push(reduced);
                }
                Some(self.union(&found))
            }
            _ => {
                let view = self.indexed_access_view(object);
                self.try_reduce_indexed_access_by_view(view, object, index)
            }
        }
    }

    fn try_reduce_indexed_access_by_view(
        &mut self,
        view: TypeId,
        object: TypeId,
        index: TypeId,
    ) -> Option<TypeId> {
        if let Type::Keyof(key_source) = self.get(index)
            && *key_source == object
        {
            return self.indexed_access_keyof_view(view);
        }
        match self.get(view).clone() {
            Type::Any => Some(self.any()),
            Type::Unknown => Some(self.unknown()),
            Type::Never => Some(self.never()),
            Type::Error => Some(self.error_type()),
            Type::Null | Type::Undefined => Some(self.error_type()),
            Type::Record { key, value } => {
                let constraint = self.type_parameter_constraint_view(index).unwrap_or(index);
                if self.assignable(index, key)
                    || (constraint != index && self.assignable(constraint, key))
                {
                    Some(value)
                } else {
                    Some(self.error_type())
                }
            }
            Type::ObjectType(_) | Type::Tuple(_) | Type::Array(_) => {
                self.try_resolve_concrete_indexed_access(view, index)
            }
            Type::String | Type::StringLiteral(_) => match self.get(index) {
                Type::Number | Type::NumberLiteral(_) => Some(self.string()),
                _ => None,
            },
            Type::Union(members) => {
                if members
                    .iter()
                    .any(|member| matches!(self.get(*member), Type::Error))
                {
                    return Some(self.error_type());
                }
                let mut found = Vec::with_capacity(members.len());
                for &member in &members {
                    let reduced = self.indexed_access(member, index);
                    if reduced == self.error_type() {
                        return Some(reduced);
                    }
                    found.push(reduced);
                }
                Some(self.union(&found))
            }
            Type::Intersection(members) => {
                let mut found = Vec::new();
                for &member in &members {
                    found.push(self.indexed_access(member, index));
                }
                Some(self.intersection(found))
            }
            _ => None,
        }
    }

    fn try_resolve_concrete_indexed_access(
        &mut self,
        view: TypeId,
        index: TypeId,
    ) -> Option<TypeId> {
        match self.get(index).clone() {
            Type::StringLiteral(name) => {
                let Ok(key) = name.to_utf8_strict() else {
                    return Some(self.error_type());
                };
                self.property_type(view, &key).or(Some(self.error_type()))
            }
            Type::NumberLiteral(name) => self
                .property_type(view, name.as_ref())
                .or(Some(self.error_type())),
            Type::String => {
                if let Type::ObjectType(object) = self.get(view).clone()
                    && let Some(signature) = object.index_signatures.iter().find(|signature| {
                        signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.get(parameter.type_id()), Type::String)
                        })
                    })
                {
                    return Some(signature.value_type);
                }
                Some(self.error_type())
            }
            Type::Number => match self.get(view).clone() {
                Type::Array(element) => Some(element),
                Type::Tuple(shape) => Some(self.union(&shape.all_element_types())),
                Type::ObjectType(object) => object
                    .index_signatures
                    .iter()
                    .find(|signature| {
                        signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.get(parameter.type_id()), Type::Number)
                        })
                    })
                    .or_else(|| {
                        object.index_signatures.iter().find(|signature| {
                            signature.parameters.first().is_some_and(|parameter| {
                                matches!(self.get(parameter.type_id()), Type::String)
                            })
                        })
                    })
                    .map_or_else(
                        || Some(self.error_type()),
                        |signature| Some(signature.value_type),
                    ),
                _ => Some(self.error_type()),
            },
            Type::Symbol => {
                if let Type::ObjectType(object) = self.get(view).clone()
                    && let Some(signature) = object.index_signatures.iter().find(|signature| {
                        signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.get(parameter.type_id()), Type::Symbol)
                        })
                    })
                {
                    return Some(signature.value_type);
                }
                Some(self.error_type())
            }
            Type::Any => Some(self.any()),
            Type::Never => Some(self.never()),
            Type::Named(symbol) => self
                .type_parameter_constraint(symbol)
                .filter(|constraint| *constraint != index)
                .and_then(|constraint| self.try_resolve_concrete_indexed_access(view, constraint)),
            Type::Intersection(members) => {
                let error = self.error_type();
                let found: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| {
                        self.try_resolve_concrete_indexed_access(view, member)
                            .filter(|reduced| *reduced != error)
                    })
                    .collect();
                (!found.is_empty()).then(|| self.union(&found))
            }
            Type::Keyof(_) | Type::IndexedAccess { .. } => None,
            _ => Some(self.error_type()),
        }
    }

    fn contains_error(&self, type_id: TypeId) -> bool {
        match self.get(type_id) {
            Type::Error => true,
            Type::Union(members) | Type::Intersection(members) => {
                members.iter().any(|member| self.contains_error(*member))
            }
            Type::AppliedAlias { .. } => self
                .applied_alias_view(type_id)
                .is_some_and(|view| view != type_id && self.contains_error(view)),
            _ => false,
        }
    }

    fn is_unconstrained_index_key(&self, index: TypeId) -> bool {
        match self.get(index) {
            Type::Any | Type::String | Type::Number | Type::Symbol => true,
            Type::Intersection(members) => members
                .iter()
                .all(|member| self.is_unconstrained_index_key(*member)),
            _ => false,
        }
    }
    fn accepts_any_index(&mut self, object: TypeId) -> bool {
        let constraint = self
            .type_parameter_constraint_view(object)
            .unwrap_or(object);
        if constraint != object {
            return self.accepts_any_index(constraint);
        }
        let view = self.indexed_access_view(object);
        match self.get(view).clone() {
            Type::Any
            | Type::Error
            | Type::String
            | Type::StringLiteral(_)
            | Type::Array(_)
            | Type::Tuple(_) => true,
            Type::Record { .. } => true,
            Type::ObjectType(object) => !object.index_signatures.is_empty(),
            Type::Union(members) => members
                .into_iter()
                .all(|member| self.accepts_any_index(member)),
            Type::Intersection(members) => members
                .into_iter()
                .any(|member| self.accepts_any_index(member)),
            _ => false,
        }
    }

    fn indexed_access_keyof_view(&mut self, view: TypeId) -> Option<TypeId> {
        match self.get(view).clone() {
            Type::ObjectType(object) => {
                let mut members =
                    Vec::with_capacity(object.properties.len() + object.index_signatures.len());
                for property in &object.properties {
                    members.push(property.type_id());
                }
                for signature in &object.index_signatures {
                    members.push(signature.value_type);
                }
                Some(self.union_or_single(members))
            }
            Type::Tuple(shape) => Some(self.union_or_single(shape.all_element_types())),
            Type::Array(element) => Some(element),
            _ => None,
        }
    }

    fn union_or_single(&mut self, members: Vec<TypeId>) -> TypeId {
        match members.len() {
            0 => self.never(),
            1 => members[0],
            _ => self.union(&members),
        }
    }

    pub fn set_type_parameter_constraint(&mut self, symbol: SymbolId, constraint: TypeId) {
        self.type_parameter_constraints.insert(symbol, constraint);
    }

    #[must_use]
    pub fn type_parameter_constraint(&self, symbol: SymbolId) -> Option<TypeId> {
        self.type_parameter_constraints.get(&symbol).copied()
    }

    pub fn set_type_parameter_default(&mut self, symbol: SymbolId, default: TypeId) {
        self.type_parameter_defaults.insert(symbol, default);
    }

    #[must_use]
    pub fn type_parameter_default(&self, symbol: SymbolId) -> Option<TypeId> {
        self.type_parameter_defaults.get(&symbol).copied()
    }

    /// Interns a boolean literal type.
    pub fn boolean_literal(&mut self, value: bool) -> TypeId {
        self.intern(Type::BooleanLiteral(value))
    }

    /// Interns a numeric literal type keyed by its source lexeme.
    pub fn number_literal(&mut self, text: &str) -> TypeId {
        self.intern(Type::NumberLiteral(text.into()))
    }

    /// Interns a string literal type from its semantic value.
    pub fn string_literal(&mut self, value: &str) -> TypeId {
        self.intern(Type::StringLiteral(EcmaString::encode(value)))
    }

    /// Interns a string literal type from a source lexeme.
    pub(crate) fn string_literal_lexeme(&mut self, lexeme: &str) -> TypeId {
        let value = string_value(lexeme).unwrap_or_else(|| EcmaString::encode(lexeme));
        self.intern(Type::StringLiteral(value))
    }

    /// Interns a bigint literal type keyed by its source lexeme.
    pub fn bigint_literal(&mut self, text: &str) -> TypeId {
        self.intern(Type::BigIntLiteral(text.into()))
    }

    /// Interns a nominal named type.
    pub fn named(&mut self, symbol: SymbolId) -> TypeId {
        self.intern(Type::Named(symbol))
    }

    /// Interns a receiver-bound `this` type for one declaring owner.
    pub fn this_type(&mut self, owner: SymbolId, constraint: TypeId) -> TypeId {
        self.intern(Type::This { owner, constraint })
    }

    /// Interns a numeric enum value type.
    pub fn numeric_enum(&mut self, symbol: SymbolId) -> TypeId {
        self.intern(Type::NumericEnum(symbol))
    }

    /// Interns a literal enum member type like `E.A`.
    pub fn enum_member(
        &mut self,
        enum_symbol: SymbolId,
        member_symbol: SymbolId,
        string_value: Option<EcmaString>,
    ) -> TypeId {
        self.intern(Type::EnumMember {
            enum_symbol,
            member_symbol,
            string_value,
        })
    }

    /// Interns an array type over `element`.
    pub fn array(&mut self, element: TypeId) -> TypeId {
        let array = self.intern(Type::Array(element));
        self.ensure_iterable_view(array);
        array
    }

    /// Interns a fixed-length tuple type.
    pub fn tuple(&mut self, elements: Vec<TypeId>) -> TypeId {
        self.tuple_shape(TupleShape::fixed(elements))
    }

    /// Interns a tuple after canonicalizing its positional zones.
    pub fn tuple_shape(&mut self, mut shape: TupleShape) -> TypeId {
        shape.required = shape
            .required
            .min(u32::try_from(shape.prefix.len()).expect("tuple element count fits in u32"));
        if shape
            .rest
            .is_some_and(|rest| matches!(self.get(rest), Type::Never))
        {
            shape.rest = None;
        }
        if shape.rest.is_none() {
            let suffix_len = shape.suffix.len();
            shape.prefix.append(&mut shape.suffix);
            shape.required = shape
                .required
                .saturating_add(u32::try_from(suffix_len).expect("tuple element count fits in u32"))
                .min(u32::try_from(shape.prefix.len()).expect("tuple element count fits in u32"));
        }
        if shape.prefix.is_empty()
            && shape.suffix.is_empty()
            && let Some(rest) = shape.rest
        {
            return self.array(rest);
        }
        let tuple = self.intern(Type::Tuple(shape));
        self.ensure_iterable_view(tuple);
        tuple
    }

    pub(crate) fn array_or_tuple_iteration_element(&mut self, type_id: TypeId) -> Option<TypeId> {
        match self.get(type_id).clone() {
            Type::Array(element) => Some(element),
            Type::Tuple(shape) => {
                let mut elements = shape.all_element_types();
                if (shape.required as usize) < shape.prefix.len() {
                    elements.push(self.undefined_type());
                }
                Some(self.union(&elements))
            }
            _ => None,
        }
    }

    fn ensure_iterable_view(&mut self, source: TypeId) {
        if self.iterable_views.contains_key(&source) {
            return;
        }
        let yield_type = self
            .array_or_tuple_iteration_element(source)
            .expect("iterable view source is an array or tuple");
        let any = self.any();
        let view = self.sync_iterable_type(yield_type, any, any);
        let replaced = self.iterable_views.insert(source, view);
        debug_assert!(replaced.is_none());
    }

    fn sync_iterator_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
    ) -> TypeId {
        let done_false = self.boolean_literal(false);
        let done_true = self.boolean_literal(true);
        let yield_result = self.object_type(vec![
            PropertyType::new("value", false, yield_type),
            PropertyType::new("done", true, done_false),
        ]);
        let return_result = self.object_type(vec![
            PropertyType::new("value", false, return_type),
            PropertyType::new("done", false, done_true),
        ]);
        let result = self.union(&[yield_result, return_result]);
        let next = self.function_with_parameters(
            Vec::new(),
            vec![FunctionParameter::new(
                "value".to_owned(),
                next_type,
                true,
                false,
            )],
            result,
        );
        self.object_type(vec![
            PropertyType::new("next", false, next).with_method(true),
        ])
    }

    fn sync_iterable_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
    ) -> TypeId {
        let iterator = self.sync_iterator_type(yield_type, return_type, next_type);
        let method = self.function(Vec::new(), iterator);
        let property = IteratorProperty::new(method, false).with_method(true);
        self.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: Some(property),
            async_iterator_property: None,
        })
    }

    /// Interns an intersection type without assigning source syntax semantics.
    pub fn intersection(&mut self, mut members: Vec<TypeId>) -> TypeId {
        members.sort_by_key(|member| member.get());
        members.dedup();
        self.intern(Type::Intersection(members))
    }

    /// Interns an intersection type preserving the source order of `members`.
    ///
    /// Overload groups use this instead of [`Self::intersection`] so call
    /// signature resolution can try overloads in declaration order.
    pub fn intersection_ordered(&mut self, members: Vec<TypeId>) -> TypeId {
        self.intern(Type::Intersection(members))
    }

    /// If `type_id` is a function type or an intersection of function types,
    /// returns the ordered function type ids. Otherwise returns `None`.
    fn overload_members(&self, type_id: TypeId) -> Option<Vec<TypeId>> {
        match self.get(type_id) {
            Type::Function(_) => Some(vec![type_id]),
            Type::Intersection(members) => {
                let mut overloads = Vec::new();
                for &member in members {
                    match self.get(member) {
                        Type::Function(_) => overloads.push(member),
                        Type::Intersection(_) => {
                            let nested = self.overload_members(member)?;
                            overloads.extend(nested);
                        }
                        _ => return None,
                    }
                }
                Some(overloads)
            }
            _ => None,
        }
    }

    /// Interns an object type after canonically ordering its members by name.
    pub fn object_type(&mut self, properties: Vec<PropertyType>) -> TypeId {
        self.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        })
    }
    /// Interns an object type after canonically ordering its members by name.
    pub(crate) fn object_type_with_members(&mut self, mut object: ObjectType) -> TypeId {
        object
            .properties
            .sort_by(|left, right| left.name.cmp(&right.name));
        let mut merged = Vec::with_capacity(object.properties.len());
        let mut i = 0;
        while i < object.properties.len() {
            let first = &object.properties[i];
            let mut j = i + 1;
            while j < object.properties.len() && object.properties[j].name() == first.name() {
                j += 1;
            }
            let group = &object.properties[i..j];
            let mut property = group[0].clone();
            if group.len() > 1
                && first.is_method()
                && let Some(mut overloads) = self.overload_members(first.type_id())
            {
                let mut can_merge = true;
                for other in &group[1..] {
                    if !other.is_method() {
                        can_merge = false;
                        break;
                    }
                    if let Some(members) = self.overload_members(other.type_id()) {
                        overloads.extend(members);
                    } else {
                        can_merge = false;
                        break;
                    }
                }
                let mut declaring_types = Vec::new();
                for member in group {
                    for &owner in member.declaring_types() {
                        if !declaring_types.contains(&owner) {
                            declaring_types.push(owner);
                        }
                    }
                }
                if can_merge && !overloads.is_empty() {
                    let type_id = if overloads.len() == 1 {
                        overloads[0]
                    } else {
                        self.intern(Type::Intersection(overloads))
                    };
                    property =
                        PropertyType::new(first.name().to_owned(), first.optional(), type_id)
                            .with_readonly(first.readonly())
                            .with_getter_only(first.getter_only())
                            .with_accessibility(first.access(), first.declaring_class())
                            .with_declaring_types(declaring_types)
                            .with_method(true)
                            .with_spreadable(first.spreadable());
                }
            }
            merged.push(property);
            i = j;
        }
        object.properties = merged;
        self.intern(Type::ObjectType(object))
    }

    /// Interns a function type from bare parameter types.
    pub fn function(&mut self, parameters: Vec<TypeId>, return_type: TypeId) -> TypeId {
        let parameters = parameters
            .into_iter()
            .enumerate()
            .map(|(index, type_id)| {
                FunctionParameter::new(format!("arg{index}"), type_id, false, false)
            })
            .collect();
        self.function_with_parameters(Vec::new(), parameters, return_type)
    }

    /// Interns a function type with full per-parameter metadata.
    pub fn function_with_parameters(
        &mut self,
        type_parameters: Vec<SymbolId>,
        parameters: Vec<FunctionParameter>,
        return_type: TypeId,
    ) -> TypeId {
        let type_parameter_bounds = vec![TypeParameterBounds::NONE; type_parameters.len()];
        self.function_with_parameter_bounds(
            type_parameters,
            type_parameter_bounds,
            parameters,
            return_type,
            false,
        )
    }

    pub fn function_with_parameter_bounds(
        &mut self,
        type_parameters: Vec<SymbolId>,
        type_parameter_bounds: Vec<TypeParameterBounds>,
        parameters: Vec<FunctionParameter>,
        return_type: TypeId,
        javascript: bool,
    ) -> TypeId {
        debug_assert_eq!(type_parameters.len(), type_parameter_bounds.len());
        self.intern(Type::Function(FunctionSignature {
            type_parameters,
            type_parameter_bounds,
            parameters,
            return_type,
            declaring_types: Vec::new(),
            javascript,
        }))
    }

    pub(crate) fn function_signature(&mut self, signature: FunctionSignature) -> TypeId {
        self.intern(Type::Function(signature))
    }

    /// Interns a union, normalizing absorption, `never` removal, and duplicates.
    ///
    /// Identity is order-insensitive: unions with the same members
    /// canonicalize onto one interned type regardless of construction order.
    /// The stored member order is first-creation order, which is what
    /// `render_type` displays — TypeScript renders unions in type-creation
    /// order, and the `.types` baselines pin that order.
    pub fn union(&mut self, members: &[TypeId]) -> TypeId {
        let mut flat = Vec::new();
        for member in members {
            match self.get(*member) {
                Type::Any => return self.any,
                Type::Unknown => return self.unknown,
                Type::Never => {}
                Type::Union(nested) => {
                    for nested_member in nested.iter().copied() {
                        if !flat.contains(&nested_member) {
                            flat.push(nested_member);
                        }
                    }
                }
                _ => {
                    if !flat.contains(member) {
                        flat.push(*member);
                    }
                }
            }
        }
        match flat.len() {
            0 => self.never,
            1 => flat[0],
            _ => {
                let mut canonical = flat.clone();
                canonical.sort_by_key(|id| id.get());
                if let Some(existing) = self.index.get(&Type::Union(canonical.clone())) {
                    return *existing;
                }
                let id = TypeId(u32::try_from(self.types.len()).expect("type count fits in u32"));
                self.types.push(Type::Union(flat));
                self.index.insert(Type::Union(canonical), id);
                id
            }
        }
    }

    /// Removes `null` and `undefined` while preserving every other constituent.
    pub fn non_nullable(&mut self, type_id: TypeId) -> TypeId {
        match self.get(type_id).clone() {
            Type::Null | Type::Undefined => self.never,
            Type::Union(members) => {
                let members: Vec<_> = members
                    .into_iter()
                    .filter(|member| !matches!(self.get(*member), Type::Null | Type::Undefined))
                    .collect();
                self.union(&members)
            }
            _ => type_id,
        }
    }

    /// Whether the type is exactly `null` or exactly `undefined`, rather than a
    /// type that merely carries one as a constituent.
    ///
    /// The exactness is what keeps this rule inside its own diagnostic family.
    /// The authority table splits the two ideas: TS18047 through TS18049 read
    /// `'{0}' is possibly 'null'`, `'possibly 'undefined'`, and `'possibly
    /// 'null' or 'undefined'` and own a value whose type contains a nullable
    /// constituent, while TS18050 reads `The value '{0}' cannot be used here.`
    /// and owns the value being null or undefined. This predicate serves the
    /// TS18050 correspondent, so a union answering true here would emit our
    /// code for a case the authority gives to the possibly-null family.
    ///
    /// The caller's spelling gate does not make that unreachable on its own.
    /// `is_nullable_value_word` matches `undefined` by identifier text, so a
    /// local shadow spells the word while carrying a declared union type. Two
    /// measurements bound how far the corpus speaks. The three cases declaring
    /// a local `undefined` (`undefinedTypeAssignment2`,
    /// `undefinedTypeAssignment3`, `reExportUndefined2`) are all global-scope
    /// `var`, are rejected at the declaration with TS2397, and carry no
    /// TS18050. No case shadows either value word in function scope, so no
    /// baseline exercises a shadowed operand and none can settle the corner by
    /// observation. The choice rests on the family split above, and it is
    /// recorded here as reasoned rather than measured.
    pub fn is_exactly_nullish(&self, type_id: TypeId) -> bool {
        matches!(self.get(type_id), Type::Null | Type::Undefined)
    }
    fn optional_access_view(&mut self, type_id: TypeId) -> TypeId {
        let non_nullable = self.non_nullable(type_id);
        let constrained = self
            .type_parameter_constraint_view(non_nullable)
            .unwrap_or(non_nullable);
        self.non_nullable(constrained)
    }
    /// Removes constituents that can never be the result of the left operand
    /// of `||`.
    pub fn truthy_type(&mut self, type_id: TypeId) -> TypeId {
        match self.get(type_id).clone() {
            Type::Null | Type::Undefined | Type::Void | Type::BooleanLiteral(false) => self.never,
            Type::NumberLiteral(text) if number_value(&text) == Some(0.0) => self.never,
            Type::StringLiteral(text) if text.is_empty() => self.never,
            Type::EnumMember {
                string_value: Some(value),
                ..
            } if value.is_empty() => self.never,
            Type::Union(members) => {
                let members: Vec<_> = members
                    .into_iter()
                    .filter(|member| self.truthy_type(*member) != self.never)
                    .collect();
                self.union(&members)
            }
            _ => type_id,
        }
    }

    /// Returns whether a value of `source` may be assigned where `target` is
    /// expected, using structural rules over the modeled type space.
    ///
    /// The relation algebra lives in [`super::relations`]; this delegates
    /// through a short-lived [`TypeRelations`] so existing callers keep
    /// working. Relation-heavy passes should share one `TypeRelations`
    /// instead, so memoized pairs amortize across queries.
    #[must_use]
    pub fn assignable(&self, source: TypeId, target: TypeId) -> bool {
        TypeRelations::new(self).assignable(source, target)
    }

    /// Synthesizes the `Array<T>.concat` overload pair the standard library
    /// declares:
    /// `(...items: ConcatArray<T>[]): T[]` and
    /// `(...items: (ConcatArray<T> | T)[]): T[]`.
    /// The result is the object type carrying both call signatures so `.types`
    /// rendering matches the library overload set.
    fn array_concat_member_type(&mut self, element: TypeId) -> TypeId {
        let Some(concat_array) = self.concat_array_symbol else {
            return self.any;
        };
        let concat_array_element = self.applied_class(concat_array, vec![element]);
        let array_of_element = self.array(element);
        let items_of_concat_arrays = self.array(concat_array_element);
        let element_or_concat_array = self.union(&[concat_array_element, element]);
        let items_of_elements_or_concat_arrays = self.array(element_or_concat_array);
        let first = self.function_with_parameters(
            Vec::new(),
            vec![FunctionParameter::new(
                "items".to_owned(),
                items_of_concat_arrays,
                false,
                true,
            )],
            array_of_element,
        );
        let second = self.function_with_parameters(
            Vec::new(),
            vec![FunctionParameter::new(
                "items".to_owned(),
                items_of_elements_or_concat_arrays,
                false,
                true,
            )],
            array_of_element,
        );
        let mut call_signatures = Vec::with_capacity(2);
        for signature in [first, second] {
            match self.get(signature).clone() {
                Type::Function(signature) => call_signatures.push(signature),
                _ => unreachable!("synthesized concat member must be a function"),
            }
        }
        self.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures,
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        })
    }
    /// Returns whether a value of `source` may be assigned where `target` is
    /// expected with `strictNullChecks` enabled.
    #[must_use]
    pub fn assignable_with_strict_null(&self, source: TypeId, target: TypeId) -> bool {
        TypeRelations::new(self).assignable_with_strict_null(source, target)
    }

    /// Returns whether two types sufficiently overlap for a TypeScript type
    /// assertion.
    #[must_use]
    pub fn comparable(&self, left: TypeId, right: TypeId) -> bool {
        TypeRelations::new(self).comparable(left, right)
    }

    /// Widens a top-level primitive literal so a mutable binding can accept
    /// other values of the same primitive type. Composite types keep their
    /// declared element and property types.
    pub fn widen(&mut self, type_id: TypeId, keep_primitive_literals: bool) -> TypeId {
        self.widen_with_aliases(type_id, keep_primitive_literals, &mut HashSet::new())
    }

    fn widen_with_aliases(
        &mut self,
        type_id: TypeId,
        keep_primitive_literals: bool,
        active_aliases: &mut HashSet<SymbolId>,
    ) -> TypeId {
        match self.get(type_id).clone() {
            Type::StringLiteral(_) if !keep_primitive_literals => self.string(),
            Type::NumberLiteral(_) if !keep_primitive_literals => self.number(),
            Type::BooleanLiteral(_) if !keep_primitive_literals => self.boolean(),
            Type::BigIntLiteral(_) if !keep_primitive_literals => self.bigint(),
            Type::EnumMember {
                enum_symbol,
                string_value: None,
                ..
            } if !keep_primitive_literals => self.numeric_enum(enum_symbol),
            Type::EnumMember {
                enum_symbol,
                string_value: Some(_),
                ..
            } if !keep_primitive_literals => self.named(enum_symbol),
            Type::Union(members) if !keep_primitive_literals => {
                let widened = members
                    .into_iter()
                    .map(|member| self.widen_with_aliases(member, false, active_aliases))
                    .collect::<Vec<_>>();
                self.union(&widened)
            }
            Type::AppliedAlias { symbol, .. } => {
                if !active_aliases.insert(symbol) {
                    return type_id;
                }
                let widened = match self.prepare_applied_alias_view(type_id) {
                    Some(view) if view != type_id => {
                        self.widen_with_aliases(view, keep_primitive_literals, active_aliases)
                    }
                    _ => type_id,
                };
                active_aliases.remove(&symbol);
                widened
            }
            _ => type_id,
        }
    }

    /// Widens literal leaves while constructing a fresh array or object
    /// literal. Nested object literals already cross this boundary themselves.
    fn widen_fresh_literal(&mut self, type_id: TypeId) -> TypeId {
        match self.get(type_id).clone() {
            Type::StringLiteral(_)
            | Type::NumberLiteral(_)
            | Type::BooleanLiteral(_)
            | Type::BigIntLiteral(_) => self.widen(type_id, false),
            Type::Array(element) => {
                let widened = self.widen_fresh_literal(element);
                self.array(widened)
            }
            Type::Tuple(shape) => {
                let prefix = shape
                    .prefix
                    .iter()
                    .map(|element| self.widen_fresh_literal(*element))
                    .collect();
                let rest = shape.rest.map(|element| self.widen_fresh_literal(element));
                let suffix = shape
                    .suffix
                    .iter()
                    .map(|element| self.widen_fresh_literal(*element))
                    .collect();
                self.tuple_shape(TupleShape {
                    prefix,
                    required: shape.required,
                    rest,
                    suffix,
                })
            }
            Type::Union(members) => {
                let widened: Vec<_> = members
                    .iter()
                    .map(|member| self.widen_fresh_literal(*member))
                    .collect();
                self.union(&widened)
            }
            _ => type_id,
        }
    }

    /// Computes compatibility once while retaining every accepted unsound
    pub fn relation(&self, source: TypeId, target: TypeId) -> TypeRelation {
        TypeRelations::new(self).relation(source, target)
    }

    fn import_type(
        &mut self,
        source: &Self,
        root: TypeId,
        source_parameters: &[SymbolId],
        imported: &mut ImportedTypeMap,
        next_symbol: &mut u32,
    ) -> (TypeId, Vec<SymbolId>) {
        fn copy(
            target: &mut TypeTable,
            source: &TypeTable,
            source_id: TypeId,
            imported: &mut ImportedTypeMap,
            next_symbol: &mut u32,
        ) -> TypeId {
            if let Some(&type_id) = imported.types.get(&source_id) {
                return type_id;
            }
            let source_type = source.get(source_id).clone();
            let type_id = match source_type {
                Type::Error => target.error_type(),
                Type::Any => target.any(),
                Type::Unknown => target.unknown(),
                Type::Never => target.never(),
                Type::Void => target.void(),
                Type::Null => target.null_type(),
                Type::Undefined => target.undefined_type(),
                Type::Boolean => target.boolean(),
                Type::Number => target.number(),
                Type::BigInt => target.bigint(),
                Type::String => target.string(),
                Type::Symbol => target.symbol_type(),
                Type::Object => target.object(),
                Type::BooleanLiteral(value) => target.boolean_literal(value),
                Type::NumberLiteral(value) => target.number_literal(&value),
                Type::StringLiteral(value) => target.intern(Type::StringLiteral(value)),
                Type::BigIntLiteral(value) => target.bigint_literal(&value),
                Type::Array(element) => {
                    let element = copy(target, source, element, imported, next_symbol);
                    target.array(element)
                }
                Type::Tuple(shape) => {
                    let prefix = shape
                        .prefix
                        .into_iter()
                        .map(|item| copy(target, source, item, imported, next_symbol))
                        .collect();
                    let rest = shape
                        .rest
                        .map(|item| copy(target, source, item, imported, next_symbol));
                    let suffix = shape
                        .suffix
                        .into_iter()
                        .map(|item| copy(target, source, item, imported, next_symbol))
                        .collect();
                    target.tuple_shape(TupleShape {
                        prefix,
                        required: shape.required,
                        rest,
                        suffix,
                    })
                }
                Type::Union(members) => {
                    let members = members
                        .into_iter()
                        .map(|item| copy(target, source, item, imported, next_symbol))
                        .collect::<Vec<_>>();
                    target.union(&members)
                }
                Type::Intersection(members) => {
                    let members = members
                        .into_iter()
                        .map(|item| copy(target, source, item, imported, next_symbol))
                        .collect();
                    target.intersection_ordered(members)
                }
                Type::ObjectType(object) => {
                    let properties = object
                        .properties
                        .into_iter()
                        .map(|property| {
                            let declaring_class = property.declaring_class().map(|symbol| {
                                remap_symbol(target, source, symbol, imported, next_symbol)
                            });
                            let declaring_types = property
                                .declaring_types()
                                .iter()
                                .map(|&symbol| {
                                    remap_symbol(target, source, symbol, imported, next_symbol)
                                })
                                .collect();
                            PropertyType::new(
                                property.name.clone(),
                                property.optional,
                                copy(target, source, property.type_id, imported, next_symbol),
                            )
                            .with_readonly(property.readonly)
                            .with_getter_only(property.getter_only)
                            .with_accessibility(property.access(), declaring_class)
                            .with_declaring_types(declaring_types)
                            .with_method(property.is_method)
                            .with_spreadable(property.spreadable)
                        })
                        .collect();
                    let call_signatures = object
                        .call_signatures
                        .into_iter()
                        .map(|signature| {
                            copy_signature(target, source, signature, imported, next_symbol)
                        })
                        .collect();
                    let construct_signatures = object
                        .construct_signatures
                        .into_iter()
                        .map(|entry| ConstructEntry {
                            signature: copy_signature(
                                target,
                                source,
                                entry.signature,
                                imported,
                                next_symbol,
                            ),
                            is_abstract: entry.is_abstract,
                        })
                        .collect();
                    let index_signatures = object
                        .index_signatures
                        .into_iter()
                        .map(|signature| IndexSignature {
                            readonly: signature.readonly,
                            parameters: signature
                                .parameters
                                .into_iter()
                                .map(|parameter| {
                                    copy_parameter(target, source, parameter, imported, next_symbol)
                                })
                                .collect(),
                            value_type: copy(
                                target,
                                source,
                                signature.value_type,
                                imported,
                                next_symbol,
                            ),
                            declaring_types: signature
                                .declaring_types
                                .into_iter()
                                .map(|symbol| {
                                    remap_symbol(target, source, symbol, imported, next_symbol)
                                })
                                .collect(),
                        })
                        .collect();
                    let generator_return = object.generator_return.map(|return_type| {
                        copy(target, source, return_type, imported, next_symbol)
                    });
                    let iterator_property = object.iterator_property.map(|property| {
                        let declaring_class = property.declaring_class().map(|symbol| {
                            remap_symbol(target, source, symbol, imported, next_symbol)
                        });
                        let declaring_types = property
                            .declaring_types()
                            .iter()
                            .map(|&symbol| {
                                remap_symbol(target, source, symbol, imported, next_symbol)
                            })
                            .collect();
                        IteratorProperty::new(
                            copy(target, source, property.type_id(), imported, next_symbol),
                            property.optional(),
                        )
                        .with_accessibility(property.access(), declaring_class)
                        .with_declaring_types(declaring_types)
                        .with_method(property.is_method())
                        .with_spreadable(property.spreadable())
                    });
                    let async_iterator_property = object.async_iterator_property.map(|property| {
                        let declaring_class = property.declaring_class().map(|symbol| {
                            remap_symbol(target, source, symbol, imported, next_symbol)
                        });
                        let declaring_types = property
                            .declaring_types()
                            .iter()
                            .map(|&symbol| {
                                remap_symbol(target, source, symbol, imported, next_symbol)
                            })
                            .collect();
                        IteratorProperty::new(
                            copy(target, source, property.type_id(), imported, next_symbol),
                            property.optional(),
                        )
                        .with_accessibility(property.access(), declaring_class)
                        .with_declaring_types(declaring_types)
                        .with_method(property.is_method())
                        .with_spreadable(property.spreadable())
                    });
                    target.object_type_with_members(ObjectType {
                        properties,
                        call_signatures,
                        construct_signatures,
                        index_signatures,
                        generator_return,
                        iterator_property,
                        async_iterator_property,
                    })
                }
                Type::Function(signature) => {
                    let signature =
                        copy_signature(target, source, signature, imported, next_symbol);
                    target.intern(Type::Function(signature))
                }
                Type::Named(symbol) => {
                    let symbol = remap_symbol(target, source, symbol, imported, next_symbol);
                    target.named(symbol)
                }
                Type::AppliedClass { symbol, arguments } => {
                    let symbol = remap_symbol(target, source, symbol, imported, next_symbol);
                    let arguments = arguments
                        .into_iter()
                        .map(|argument| copy(target, source, argument, imported, next_symbol))
                        .collect();
                    target.applied_class(symbol, arguments)
                }
                Type::AppliedAlias { symbol, arguments } => {
                    let symbol = remap_symbol(target, source, symbol, imported, next_symbol);
                    let arguments = arguments
                        .into_iter()
                        .map(|argument| copy(target, source, argument, imported, next_symbol))
                        .collect();
                    target.applied_alias(symbol, arguments)
                }
                Type::NumericEnum(symbol) => {
                    let symbol = remap_symbol(target, source, symbol, imported, next_symbol);
                    target.numeric_enum(symbol)
                }
                Type::EnumMember {
                    enum_symbol,
                    member_symbol,
                    string_value,
                } => {
                    let enum_symbol =
                        remap_symbol(target, source, enum_symbol, imported, next_symbol);
                    let member_symbol =
                        remap_symbol(target, source, member_symbol, imported, next_symbol);
                    target.enum_member(enum_symbol, member_symbol, string_value)
                }
                Type::Keyof(operand) => {
                    let operand = copy(target, source, operand, imported, next_symbol);
                    target.keyof(operand)
                }
                Type::IndexedAccess { object, index } => {
                    let object = copy(target, source, object, imported, next_symbol);
                    let index = copy(target, source, index, imported, next_symbol);
                    target.indexed_access(object, index)
                }
                Type::Record { key, value } => {
                    let key = copy(target, source, key, imported, next_symbol);
                    let value = copy(target, source, value, imported, next_symbol);
                    target.record(key, value)
                }
                Type::This { owner, constraint } => {
                    let owner = remap_symbol(target, source, owner, imported, next_symbol);
                    let constraint = copy(target, source, constraint, imported, next_symbol);
                    target.this_type(owner, constraint)
                }
                Type::ConstructorType {
                    symbol,
                    arguments,
                    structural,
                } => {
                    let symbol = remap_symbol(target, source, symbol, imported, next_symbol);
                    let arguments = arguments
                        .iter()
                        .map(|&arg| copy(target, source, arg, imported, next_symbol))
                        .collect();
                    let structural = copy(target, source, structural, imported, next_symbol);
                    target.constructor_type(symbol, arguments, structural)
                }
            };
            imported.types.insert(source_id, type_id);
            type_id
        }

        fn remap_symbol(
            target: &mut TypeTable,
            source: &TypeTable,
            source_symbol: SymbolId,
            imported: &mut ImportedTypeMap,
            next_symbol: &mut u32,
        ) -> SymbolId {
            if let Some(&symbol) = imported.symbols.get(&source_symbol) {
                return symbol;
            }
            if source.object_symbol == Some(source_symbol)
                && let Some(symbol) = target.object_symbol
            {
                imported.symbols.insert(source_symbol, symbol);
                return symbol;
            }
            if let Some(index) = source.intrinsic_collection_index(source_symbol)
                && let Some(symbol) = target.collection_symbols[index]
            {
                imported.symbols.insert(source_symbol, symbol);
                return symbol;
            }

            let symbol = SymbolId(*next_symbol);
            *next_symbol = next_symbol
                .checked_add(1)
                .expect("imported symbol count fits in u32");
            imported.symbols.insert(source_symbol, symbol);
            imported.synthesized.push((source_symbol, symbol));

            if let Some(metadata) = source.classes.get(&source_symbol).cloned() {
                let parameters = metadata
                    .parameters
                    .into_iter()
                    .map(|parameter| remap_symbol(target, source, parameter, imported, next_symbol))
                    .collect();
                target.declare_class(symbol, parameters);
                if metadata.bounds_ready {
                    let bounds = metadata
                        .bounds
                        .into_iter()
                        .map(|bounds| copy_bounds(target, source, bounds, imported, next_symbol))
                        .collect();
                    target.set_class_bounds(symbol, bounds);
                }
                if let Some(template) = metadata.template {
                    let raw = copy(target, source, template.raw, imported, next_symbol);
                    target.publish_class_template(symbol, raw, template.state);
                }
            }
            if let Some(metadata) = source.aliases.get(&source_symbol).cloned() {
                let parameters = metadata
                    .parameters
                    .into_iter()
                    .map(|parameter| remap_symbol(target, source, parameter, imported, next_symbol))
                    .collect();
                target.declare_alias(symbol, parameters);
                if metadata.bounds_ready {
                    let bounds = metadata
                        .bounds
                        .into_iter()
                        .map(|bounds| copy_bounds(target, source, bounds, imported, next_symbol))
                        .collect();
                    target.finish_alias_bounds(symbol, bounds);
                }
                if let Some(raw) = metadata.template {
                    let raw = copy(target, source, raw, imported, next_symbol);
                    target.publish_alias_template(symbol, raw);
                }
            }
            if let Some(structure) = source.interface_structures.get(&source_symbol).copied() {
                let structure = copy(target, source, structure, imported, next_symbol);
                target.set_interface_structure(symbol, structure);
            }
            if let Some(constraint) = source
                .type_parameter_constraints
                .get(&source_symbol)
                .copied()
            {
                let constraint = copy(target, source, constraint, imported, next_symbol);
                target.set_type_parameter_constraint(symbol, constraint);
            }
            if let Some(default) = source.type_parameter_defaults.get(&source_symbol).copied() {
                let default = copy(target, source, default, imported, next_symbol);
                target.set_type_parameter_default(symbol, default);
            }
            symbol
        }

        fn copy_parameter(
            target: &mut TypeTable,
            source: &TypeTable,
            parameter: FunctionParameter,
            imported: &mut ImportedTypeMap,
            next_symbol: &mut u32,
        ) -> FunctionParameter {
            FunctionParameter::new(
                parameter.name,
                copy(target, source, parameter.type_id, imported, next_symbol),
                parameter.optional,
                parameter.rest,
            )
        }

        fn copy_bounds(
            target: &mut TypeTable,
            source: &TypeTable,
            bounds: TypeParameterBounds,
            imported: &mut ImportedTypeMap,
            next_symbol: &mut u32,
        ) -> TypeParameterBounds {
            TypeParameterBounds {
                constraint: bounds
                    .constraint
                    .map(|type_id| copy(target, source, type_id, imported, next_symbol)),
                default: bounds
                    .default
                    .map(|type_id| copy(target, source, type_id, imported, next_symbol)),
            }
        }

        fn copy_signature(
            target: &mut TypeTable,
            source: &TypeTable,
            signature: FunctionSignature,
            imported: &mut ImportedTypeMap,
            next_symbol: &mut u32,
        ) -> FunctionSignature {
            let javascript = signature.javascript;
            let declaring_types = signature
                .declaring_types
                .iter()
                .map(|&symbol| remap_symbol(target, source, symbol, imported, next_symbol))
                .collect();
            let type_parameters = signature
                .type_parameters
                .into_iter()
                .map(|parameter| remap_symbol(target, source, parameter, imported, next_symbol))
                .collect();
            let type_parameter_bounds = signature
                .type_parameter_bounds
                .into_iter()
                .map(|bounds| copy_bounds(target, source, bounds, imported, next_symbol))
                .collect();
            let parameters = signature
                .parameters
                .into_iter()
                .map(|parameter| copy_parameter(target, source, parameter, imported, next_symbol))
                .collect();
            let return_type = copy(target, source, signature.return_type, imported, next_symbol);
            FunctionSignature {
                type_parameters,
                type_parameter_bounds,
                parameters,
                return_type,
                declaring_types,
                javascript,
            }
        }

        let root = copy(self, source, root, imported, next_symbol);
        let parameters = source_parameters
            .iter()
            .map(|parameter| remap_symbol(self, source, *parameter, imported, next_symbol))
            .collect();
        (root, parameters)
    }
}

/// Lazy resolution state for a type-declaring symbol.
#[derive(Clone, Copy)]
enum TypeState {
    Unresolved,
    InProgress,
    Done(TypeId),
}

enum EntityNameScopeError {
    Unresolved,
    MissingMember(TextRange),
    NotNamespace,
}

/// Separate value and type targets for an `import =` alias when a name occupies
/// both planes. Runtime/value lowering uses `value.or(ty)`; type resolution uses
/// `ty.or(value)`.
#[derive(Clone, Copy, Debug, Default)]
struct ImportEqualsTarget {
    value: Option<SymbolId>,
    ty: Option<SymbolId>,
}

/// One imported binding's resolved value and type facts, carried across module
/// boundaries so a target binder can install both source-table identities and
/// materialize every synthetic symbol before it resolves statements.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ImportedSymbolType<'a> {
    pub symbol: SymbolId,
    pub source_model: &'a SemanticModel,
    pub value_type_id: TypeId,
    pub type_parameters: &'a [SymbolId],
    pub type_plane_id: Option<TypeId>,
}

/// A named type definition kept by reference for lazy, memoized resolution.
#[derive(Clone, Copy)]
enum TypeDef<'src> {
    Alias {
        scope: ScopeId,
        type_parameters: Option<&'src crate::syntax::TypeParameterList>,
        node: &'src Ty,
    },
    Interface {
        scope: ScopeId,
        type_parameters: Option<&'src crate::syntax::TypeParameterList>,
    },
    Enum {
        numeric: bool,
    },
}

/// Whether the file is an external module: it carries a top-level `import` or
/// `export` that names a module, or an `import =` whose reference is an
/// external module reference (`import I = require("m")`). A qualified alias
/// (`import I = A.B.C`) leaves the file a script.
pub(crate) fn source_is_module(source: &SourceFile) -> bool {
    source
        .statements()
        .iter()
        .any(|statement| match statement.data() {
            Statement::Import(_) | Statement::Export(_) => true,
            Statement::ImportEquals(import) => matches!(
                import.reference,
                crate::syntax::ExternalModuleReference::Require(_)
            ),
            _ => false,
        })
}

/// Returns whether the directive prologue of a statement list contains
/// a `"use strict"` directive before any non-directive statement.
fn directive_prologue_is_strict(source: &SourceFile, statements: &[Stmt]) -> bool {
    for statement in statements {
        if let Statement::Expression(expression) = statement.data()
            && let Expression::Literal(Literal::String(literal)) = expression.expression.data()
        {
            let value = source
                .token_text(literal.data().token())
                .map(|text| text.trim_matches(['\'', '"']))
                .unwrap_or("");
            if value == "use strict" {
                return true;
            }
            continue;
        }
        break;
    }
    false
}

struct ExpectedDiagnostic {
    directive_range: TextRange,
    used: bool,
}

enum DiagnosticSuppression {
    Ignore,
    Expect(usize),
}

struct DiagnosticSuppressions {
    lines: HashMap<usize, Vec<DiagnosticSuppression>>,
    expectations: Vec<ExpectedDiagnostic>,
}

fn consume_diagnostic_suppression(
    lines: &HashMap<usize, Vec<DiagnosticSuppression>>,
    expectations: &mut [ExpectedDiagnostic],
    line: usize,
) -> bool {
    let Some(suppression) = lines.get(&line).and_then(|directives| directives.last()) else {
        return false;
    };
    if let DiagnosticSuppression::Expect(expectation) = suppression {
        expectations[*expectation].used = true;
    }
    true
}

fn diagnostic_suppressions(source: &SourceFile) -> DiagnosticSuppressions {
    let source_text = source.source_text();
    let tokens = source.tokens();
    let mut lines: HashMap<usize, Vec<DiagnosticSuppression>> = HashMap::new();
    let mut expectations = Vec::new();

    for (index, token) in tokens.iter().enumerate() {
        if !matches!(
            token.kind(),
            TokenKind::LineComment | TokenKind::BlockComment
        ) {
            continue;
        }
        let text = source.token_text(token).unwrap_or("");
        let directive_line = match token.kind() {
            TokenKind::LineComment => text,
            TokenKind::BlockComment => text
                .rsplit(['\n', '\r', '\u{2028}', '\u{2029}'])
                .next()
                .unwrap_or(""),
            _ => unreachable!("comment token kind checked above"),
        };
        let body = directive_line
            .trim_start()
            .trim_start_matches(['/', '*'])
            .trim_start();
        let expect_error = body.starts_with("@ts-expect-error");
        if !expect_error && !body.starts_with("@ts-ignore") {
            continue;
        }

        let directive_line = source_text
            .line_column(token.range().end())
            .expect("comment token range belongs to its source")
            .0;
        let Some(target) = tokens[index + 1..].iter().find(|candidate| {
            !matches!(
                candidate.kind(),
                TokenKind::Whitespace
                    | TokenKind::LineComment
                    | TokenKind::BlockComment
                    | TokenKind::Shebang
                    | TokenKind::EndOfFile
            )
        }) else {
            if expect_error {
                expectations.push(ExpectedDiagnostic {
                    directive_range: token.range(),
                    used: false,
                });
            }
            continue;
        };
        let target_line = source_text
            .line_column(target.range().start())
            .expect("token range belongs to its source")
            .0;
        if target_line <= directive_line {
            continue;
        }
        if expect_error {
            let expectation = expectations.len();
            expectations.push(ExpectedDiagnostic {
                directive_range: token.range(),
                used: false,
            });
            lines
                .entry(target_line)
                .or_default()
                .push(DiagnosticSuppression::Expect(expectation));
        } else {
            lines
                .entry(target_line)
                .or_default()
                .push(DiagnosticSuppression::Ignore);
        }
    }

    DiagnosticSuppressions {
        lines,
        expectations,
    }
}

/// Returns whether an enum initializer is a numeric literal expression.
pub(crate) fn is_numeric_enum_initializer(expression: &Expr) -> bool {
    match expression.data() {
        Expression::Literal(Literal::Number(_)) => true,
        Expression::Unary(unary)
            if matches!(unary.operator, UnaryOperator::Plus | UnaryOperator::Minus) =>
        {
            matches!(
                unary.argument.data(),
                Expression::Literal(Literal::Number(_))
            )
        }
        _ => false,
    }
}

/// The immutable product of semantic analysis.
#[derive(Clone, Debug)]
pub struct SemanticModel {
    scopes: Vec<Scope>,
    symbols: Vec<Symbol>,
    generic_type_parameters: HashMap<SymbolId, Vec<SymbolId>>,
    symbol_types: Vec<TypeId>,
    #[cfg(test)]
    overload_signatures: Vec<Vec<FunctionSignature>>,
    references: HashMap<NodeId, SymbolId>,
    reference_aliases: HashMap<NodeId, SymbolId>,
    type_nodes: HashMap<NodeId, TypeId>,
    /// Types recorded for expression nodes by the expression-typing walk
    /// (U2.8 S2 types facet), distinct from `type_nodes`, which holds
    /// type-annotation node identities.
    node_types: HashMap<NodeId, TypeId>,
    /// Expression `(range, type)` records in first-seen order, feeding the S2
    /// `.types` baseline emitter.
    typed_expressions: Vec<(TextRange, TypeId)>,
    /// Resolved name occurrences (value and type references) with their source
    /// ranges, in first-seen order, feeding the S2 `.symbols` baseline emitter.
    /// This is the range-indexed projection of `references`, which is keyed by
    /// node identity and so cannot itself place records against source lines.
    symbol_references: Vec<(TextRange, SymbolId)>,
    /// Interned property declarations and their recorded occurrences,
    /// feeding the language service's property rename path.
    property_sites: Vec<PropertySite>,
    property_anchors: Vec<PropertyAnchor>,
    types: TypeTable,
    module_scope: ScopeId,
    facts: AnalysisFacts,
    pub(crate) enum_facts: EnumFacts,
    namespace_facts: NamespaceFacts,
    ambient_modules: HashMap<String, SymbolId>,
    /// Constructor (static) types for class symbols, keyed by the class
    /// declaration symbol. `symbol_types` stores the instance type for
    /// class declarations; this map holds the `typeof C` constructor type
    /// needed for value references and `typeof` queries.
    class_constructor_types: HashMap<SymbolId, TypeId>,
    /// Namespace declaration node to the local scope holding its member
    /// bindings, used by declaration emit to resolve unqualified names
    /// inside namespace bodies.
    namespace_local_scopes: HashMap<NodeId, ScopeId>,
}

impl SemanticModel {
    /// Returns every lexical scope, with the module scope first.
    #[must_use]
    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }

    /// Returns a scope by identity.
    #[must_use]
    pub fn scope(&self, id: ScopeId) -> &Scope {
        &self.scopes[id.0 as usize]
    }

    /// Returns the type parameters declared by a generic type symbol.
    #[must_use]
    pub(crate) fn generic_type_parameters(&self, symbol: SymbolId) -> &[SymbolId] {
        self.generic_type_parameters
            .get(&symbol)
            .map_or(&[], Vec::as_slice)
    }

    /// Returns the top-level module scope.
    #[must_use]
    pub const fn module_scope(&self) -> ScopeId {
        self.module_scope
    }

    /// Returns every bound name.
    #[must_use]
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols
    }

    /// Returns a symbol by identity.
    #[must_use]
    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.0 as usize]
    }

    /// Returns the symbol's qualified display name for baseline rendering: the
    /// dot-joined chain of container owners (enum/class symbols owning the
    /// member scope the symbol was declared in) ending in its own name.
    /// Symbols without an owner chain — top-level declarations, namespace
    /// exports, locals, parameters, type parameters — render bare, matching the
    /// upstream `.symbols` contract.
    #[must_use]
    pub fn qualified_name(&self, id: SymbolId) -> String {
        let symbol = self.symbol(id);
        match symbol.parent {
            Some(parent) => format!("{}.{}", self.qualified_name(parent), symbol.name),
            None => symbol.name.clone(),
        }
    }

    /// Returns the declared or inferred type of a bound name.
    #[must_use]
    pub fn symbol_type(&self, id: SymbolId) -> TypeId {
        self.symbol_types[id.0 as usize]
    }

    /// Returns the constructor (static) type for a class symbol, or the
    /// symbol's declared type if no constructor type was recorded.
    #[must_use]
    pub fn constructor_type(&self, id: SymbolId) -> TypeId {
        self.class_constructor_types
            .get(&id)
            .copied()
            .unwrap_or(self.symbol_types[id.0 as usize])
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) fn overload_signatures(&self, id: SymbolId) -> &[FunctionSignature] {
        &self.overload_signatures[id.0 as usize]
    }

    /// Returns the interned type table.
    #[must_use]
    pub const fn types(&self) -> &TypeTable {
        &self.types
    }

    /// Returns the checker's canonical identity for a resolved type node.
    #[must_use]
    pub fn resolved_type(&self, node: NodeId) -> Option<TypeId> {
        self.type_nodes.get(&node).copied()
    }

    /// Returns the type the checker computed for an expression node, when the
    /// expression-typing walk recorded one (U2.8 S2 types facet).
    #[must_use]
    pub fn node_type(&self, node: NodeId) -> Option<TypeId> {
        self.node_types.get(&node).copied()
    }

    /// Returns every recorded expression `(range, type)` in first-seen order.
    #[must_use]
    pub fn typed_expressions(&self) -> &[(TextRange, TypeId)] {
        &self.typed_expressions
    }

    /// Returns every resolved reference occurrence `(range, symbol)` in
    /// first-seen order, feeding the S2 `.symbols` baseline emitter.
    #[must_use]
    pub fn symbol_references(&self) -> &[(TextRange, SymbolId)] {
        &self.symbol_references
    }

    /// Returns every recorded property anchor, in first-seen order.
    #[must_use]
    pub(crate) fn property_anchors(&self) -> &[PropertyAnchor] {
        &self.property_anchors
    }

    /// Returns the interned property site for a rename identity.
    #[must_use]
    pub(crate) fn property_site(&self, id: PropertyId) -> Option<&PropertySite> {
        self.property_sites.get(id.0)
    }

    /// Returns every interned property site, indexed by [`PropertyId`].
    #[must_use]
    pub(crate) fn property_sites(&self) -> &[PropertySite] {
        &self.property_sites
    }

    /// Returns the immutable semantic evidence consumed by lint rules.
    #[must_use]
    pub const fn facts(&self) -> &AnalysisFacts {
        &self.facts
    }

    pub(crate) const fn facts_mut(&mut self) -> &mut AnalysisFacts {
        &mut self.facts
    }

    pub(crate) fn replace_facts(&mut self, facts: AnalysisFacts) {
        self.facts = facts;
    }

    /// Returns immutable enum semantics built by this checker pass.
    #[must_use]
    pub(crate) const fn enum_facts(&self) -> &EnumFacts {
        &self.enum_facts
    }

    /// Returns immutable namespace semantics built by this checker pass.
    #[must_use]
    pub(crate) const fn namespace_facts(&self) -> &NamespaceFacts {
        &self.namespace_facts
    }

    /// Returns the ambient string-module registry for this file.
    #[must_use]
    pub fn ambient_modules(&self) -> &HashMap<String, SymbolId> {
        &self.ambient_modules
    }

    /// Iterates resolved syntax references by their source identity.
    pub(crate) fn references(&self) -> impl Iterator<Item = (NodeId, SymbolId)> + '_ {
        self.references
            .iter()
            .map(|(&node, &symbol)| (node, symbol))
    }

    /// Returns the symbol a reference resolved to, accepting either the
    /// identifier node or its enclosing expression/assignment-target node.
    #[must_use]
    pub fn reference(&self, node: NodeId) -> Option<SymbolId> {
        self.references
            .get(&node)
            .or_else(|| self.reference_aliases.get(&node))
            .copied()
    }

    /// Returns how many syntax references resolved to a local binding.
    #[must_use]
    pub fn resolved_reference_count(&self) -> usize {
        self.references.len()
    }

    /// Resolves a value name from `scope` outward through its ancestors.
    #[must_use]
    pub fn lookup_value(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
        let mut current = Some(scope);
        while let Some(id) = current {
            let scope = &self.scopes[id.0 as usize];
            if let Some(symbol) = scope.values.get(name)
                && (scope.kind != ScopeKind::Class
                    || self.symbols[symbol.get() as usize].kind == SymbolKind::Class)
            {
                return Some(*symbol);
            }
            current = scope.parent;
        }
        None
    }

    /// Resolves a type name from `scope` outward through its ancestors.
    #[must_use]
    pub fn lookup_type(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
        let mut current = Some(scope);
        while let Some(id) = current {
            let scope = &self.scopes[id.0 as usize];
            if let Some(symbol) = scope.types.get(name) {
                return Some(*symbol);
            }
            current = scope.parent;
        }
        None
    }

    /// Returns the local scope holding a namespace body's member bindings,
    /// used by declaration emit to resolve unqualified names inside the body.
    #[must_use]
    pub fn namespace_local_scope(&self, id: NodeId) -> Option<ScopeId> {
        self.namespace_local_scopes.get(&id).copied()
    }
}

/// The innermost function context a `super(...)` call can legally appear in.
///
/// TypeScript permits a `super(...)` call only as a direct expression of a
/// derived class constructor body. Every other position (a base-class
/// constructor, constructor parameter initializers, or any non-constructor
/// function) maps to a distinct TypeScript diagnostic.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SuperCallContext {
    DerivedConstructor,
    BaseConstructor,
    ConstructorParameters { derived: bool },
    NonConstructor,
}

/// The innermost function-like home a `super.x` member access can legally
/// appear in, innermost last.
///
/// TypeScript permits a `super` member access inside class members (methods,
/// accessors, constructors, property initializers, static blocks) and inside
/// object-literal methods; a base class member has no base type to read the
/// member from. Plain functions and the module top level have no member home.
/// Arrow functions push nothing, so the enclosing member home stays visible
/// through them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SuperMemberHome {
    /// Inside a member of a class. `derived` records whether that class has
    /// a base class.
    ClassMember { derived: bool },
    /// Inside an object-literal method or accessor.
    ObjectMember,
    /// Inside any other function, which has no member home.
    NonMemberFunction,
}

/// Answers [`GuardResolver`] from the binder's already-resolved facts.
///
/// It borrows only the fields guard interpretation reads, so the narrowing
/// algebra can hold the type table mutably at the same time.
struct BinderGuardResolver<'a> {
    references: &'a HashMap<NodeId, SymbolId>,
    node_types: &'a HashMap<NodeId, TypeId>,
    source: &'a SourceFile,
    fallback: TypeId,
}

impl GuardResolver for BinderGuardResolver<'_> {
    fn resolve_identifier(&self, identifier: &IdentifierNode) -> Option<SymbolId> {
        self.references.get(&identifier.id()).copied()
    }

    fn expression_type(&self, expression: &Expr) -> TypeId {
        // Only `instanceof` consults this, and its right operand is typed before
        // the guard is read. An untyped operand narrows nothing.
        self.node_types
            .get(&expression.id())
            .copied()
            .unwrap_or(self.fallback)
    }

    fn token_text(&self, token: &Token) -> &str {
        self.source.token_text(token).unwrap_or("")
    }
}

struct WriteInventory {
    root_scope: ScopeId,
    shadow_frames: Vec<HashSet<String>>,
}

impl WriteInventory {
    fn is_shadowed(&self, name: &str) -> bool {
        self.shadow_frames
            .iter()
            .rev()
            .any(|frame| frame.contains(name))
    }
}

enum WriteFunctionBody<'src> {
    Block(&'src [Stmt]),
    Expression(&'src Expr),
    Missing,
}

#[derive(Clone, Copy)]
struct ReturnContext {
    expected: Option<TypeId>,
    await_expression: bool,
    generator_protocol: Option<ForOfMode>,
}

#[derive(Clone)]
struct PendingConstraintCheck {
    argument: TypeId,
    parameter: SymbolId,
    substitution: InferredTypeArguments,
    range: TextRange,
}

#[derive(Clone, Copy)]
enum TypeParameterDefaultState<'src> {
    Unresolved {
        node: &'src crate::syntax::Ty,
        scope: ScopeId,
    },
    Resolving {
        range: TextRange,
    },
    Circular(TypeId),
    Resolved(TypeId),
}

pub(crate) struct Binder<'src> {
    pub(crate) source: &'src SourceFile,
    intrinsics: GlobalEnvironment,
    pub(crate) scopes: Vec<Scope>,
    pub(crate) symbols: Vec<Symbol>,
    pub(crate) symbol_types: Vec<TypeId>,
    overload_signatures: Vec<Vec<FunctionSignature>>,
    type_state: Vec<TypeState>,
    type_defs: HashMap<SymbolId, TypeDef<'src>>,
    /// All interface declarations that share the same symbol through merging,
    /// in source order. The first declaration is also stored in `type_defs`.
    interface_merges: HashMap<SymbolId, Vec<&'src InterfaceDeclaration>>,
    pub(crate) references: HashMap<NodeId, SymbolId>,
    reference_aliases: HashMap<NodeId, SymbolId>,
    type_nodes: HashMap<NodeId, TypeId>,
    node_types: HashMap<NodeId, TypeId>,
    typed_expressions: Vec<(TextRange, TypeId)>,
    symbol_references: Vec<(TextRange, SymbolId)>,
    pub(crate) diagnostics: Vec<Diagnostic>,
    probing_contextual_type: bool,
    pending_constraint_checks: Vec<PendingConstraintCheck>,
    type_parameter_defaults: HashMap<SymbolId, TypeParameterDefaultState<'src>>,
    alias_resolution_stack: Vec<SymbolId>,
    alias_resolution_dependencies: HashSet<SymbolId>,
    pub(crate) types: TypeTable,
    module_scope: ScopeId,
    global_scope: ScopeId,
    ambient_modules: HashMap<String, SymbolId>,
    enum_declarations: Vec<EnumDeclarationBinding<'src>>,
    enum_declaration_symbols: HashMap<NodeId, SymbolId>,
    enum_member_scopes: HashMap<SymbolId, ScopeId>,
    enum_member_symbols: HashMap<NodeId, SymbolId>,
    enum_member_names: HashMap<NodeId, EcmaString>,
    enum_member_symbols_by_name: HashMap<SymbolId, HashMap<EcmaString, SymbolId>>,
    enum_member_identifier_uses: HashSet<NodeId>,
    imported_enum_member_uses: HashMap<NodeId, enum_plan::ImportedEnumMemberUse>,
    local_enum_member_targets: HashMap<NodeId, SymbolId>,
    imported_enum_member_targets: HashSet<NodeId>,
    pub(crate) namespace_declarations: Vec<NamespaceDeclarationBinding<'src>>,
    pub(crate) namespace_export_scopes: HashMap<SymbolId, ScopeId>,
    pub(crate) namespace_local_scopes: HashMap<NodeId, ScopeId>,
    /// Maps a namespace symbol to its companion local (Function) scope,
    /// used for qualified lookup of non-exported members from the same file.
    pub(crate) namespace_local_of_symbol: HashMap<SymbolId, ScopeId>,
    pub(crate) active_namespace_declarations: Vec<NodeId>,
    pub(crate) namespace_reference_blocks: HashMap<NodeId, NodeId>,
    pub(crate) namespace_qualified_type_paths: HashMap<NodeId, Box<[SymbolId]>>,
    /// Class member scopes keyed by their owning class symbol.
    class_member_scopes: HashMap<SymbolId, ScopeId>,
    /// Interface member scopes keyed by their owning interface symbol.
    interface_member_scopes: HashMap<SymbolId, ScopeId>,
    /// Member accesses whose `.symbols` reference rows are already recorded,
    /// so the typing-phase recorder never duplicates resolve-phase rows.
    member_reference_recorded: HashSet<NodeId>,
    /// Interned property declarations for rename anchoring.
    property_sites: Vec<PropertySite>,
    property_site_index: HashMap<(PropertyOwner, Box<str>), PropertyId>,
    property_anchors: Vec<PropertyAnchor>,
    property_anchor_index: HashMap<TextRange, usize>,
    /// Object literal expression node → property owner, seeded before the
    /// literal is typed so declarations anchor under the annotated owner.
    literal_anchor: HashMap<NodeId, PropertyOwner>,
    /// Variable/parameter symbol → property owner, seeded at declaration so
    /// member accesses resolve to the annotated owner.
    symbol_anchor: HashMap<SymbolId, PropertyOwner>,
    import_equals_symbols: HashMap<NodeId, SymbolId>,
    qualified_import_paths: HashMap<NodeId, Box<[SymbolId]>>,
    import_equals_targets: HashMap<SymbolId, ImportEqualsTarget>,
    imported_type_parameters: HashMap<SymbolId, Vec<SymbolId>>,
    imported_type_planes: HashMap<SymbolId, TypeId>,
    hoisted_declaration_symbols: HashMap<HoistedDeclarationIdentity, SymbolId>,
    /// JSX expression node → checked element result type, recorded by
    /// [`super::jsx`] during expression resolution.
    pub(crate) jsx_element_types: HashMap<NodeId, TypeId>,
    /// Callable declarations (function declarations, function/arrow
    /// initializers) by symbol, so [`super::jsx`] can factory-check
    /// value-based JSX elements whose symbol type stays `any`.
    pub(crate) jsx_callables: HashMap<SymbolId, JsxCallable<'src>>,
    pub(crate) jsx_factory_signatures: HashMap<SymbolId, JsxFactorySignature>,
    /// Class instance structural types keyed by the class symbol, built lazily
    /// during class-body resolution so `new C()` and member access on class-typed
    /// values can resolve declared instance members.
    pub(crate) class_instance_types: HashMap<SymbolId, TypeId>,
    /// Constructor (static-side) types keyed by the class symbol. For class
    /// declarations, `symbol_types[owner]` stores the instance type and this
    /// map holds the `typeof C` constructor type for value-position references.
    pub(crate) class_constructor_types: HashMap<SymbolId, TypeId>,
    reg_exp_instance_type: Option<TypeId>,
    /// Shared by provisional and final class-shape passes so a generic method's
    /// type parameters keep one semantic identity.
    class_method_signature_scopes: HashMap<NodeId, ScopeId>,
    /// Predeclared scope for each named class declaration.
    class_header_scopes: HashMap<NodeId, ScopeId>,
    /// Declaration symbol for each named class syntax node. Duplicate names keep
    /// distinct recovery symbols while scope lookup keeps the first binding.
    class_declaration_symbols: HashMap<NodeId, SymbolId>,
    /// Enclosing class symbol for member-access authorization, innermost last.
    class_owner_stack: Vec<SymbolId>,
    /// Direct base class symbol for each class symbol, used for protected access.
    class_base_symbols: HashMap<SymbolId, SymbolId>,
    /// Control-flow facts for guard narrowing, and the program point the walk
    /// currently sits at. Constructs the walk does not model contribute no
    /// facts, so a reference there falls back to its declared type.
    flow_facts: FlowFacts,
    flow: FlowNodeId,
    /// Roots written through an identifier assignment or update in the
    /// statement list currently being resolved. Captured narrowing may cross
    /// a function boundary only when the root is immutable or no such write
    /// appears in its enclosing scope.
    reassigned_flow_roots: HashSet<SymbolId>,
    /// Saved `reassigned_flow_roots` for enclosing statement lists, innermost
    /// last. `captured_flow_seed` treats a root as reassigned if any frame on
    /// the stack flags it, so later writes in an enclosing scope are visible.
    reassigned_flow_roots_stack: Vec<HashSet<SymbolId>>,
    /// Enclosing function contexts for `super(...)` call legality, innermost
    /// last. Empty means top level, which behaves as
    /// [`SuperCallContext::NonConstructor`].
    /// Enclosing member homes for `super.x` member access legality, innermost
    /// last. Empty (or [`SuperMemberHome::NonMemberFunction`] at the top)
    /// means the access has no member home. Arrow functions never push, so a
    /// member home stays visible through them.
    super_member_homes: Vec<SuperMemberHome>,
    super_call_contexts: Vec<SuperCallContext>,
    /// Legal `super()` presence for active derived constructor bodies.
    derived_constructor_super_presence: Vec<bool>,
    /// Whether each lexically enclosing class has a base class, innermost last.
    class_derived_stack: Vec<bool>,
    /// Own readonly storage properties for each lexically enclosing class.
    /// Only the active class constructor may initialize these through `this`.
    constructor_writable_readonly_properties: Vec<HashSet<String>>,
    /// Assignment targets that are writes to readonly or getter-only properties
    /// outside the constructor-initialization window. The actual diagnostic is
    /// emitted during `resolve_assignment_target`; the expression resolution
    /// skips the unrelated `TYPE_NOT_ASSIGNABLE` check.
    readonly_assignment_targets: HashSet<NodeId>,
    /// Enclosing `new.target` contexts: `true` when the innermost enclosing
    /// body is a function declaration, function expression, or constructor.
    /// `false` when it is a method, getter, setter, or static block.
    new_target_contexts: Vec<bool>,
    /// Enclosing `declare` contexts. `true` when the current statement is
    /// directly under a `declare` keyword.
    ambient_stack: Vec<bool>,
    /// `strictNullChecks` compiler option: `null` and `undefined` are only
    /// assignable to types that explicitly include them.
    strict_null_checks: bool,
    /// `noImplicitAny` compiler option: missing return types in method signatures
    /// are reported as implicit `any`.
    no_implicit_any: bool,
    /// `strictPropertyInitialization` compiler option: class properties without
    /// an initializer that are not definitely assigned in the constructor are
    /// reported (TS2564).
    strict_property_initialization: bool,
    /// Whether the compilation target is ES5 or earlier.
    es5: bool,
    /// Variable symbols declared without an initializer and not yet assigned.
    uninitialized_variables: HashSet<SymbolId>,
    /// Leaf identifier symbols bound by each declarator. Stored during binding
    /// so resolution can remove initialized variables from `uninitialized_variables`.
    declarator_symbols: HashMap<NodeId, Vec<SymbolId>>,
    /// Suppress BAMTS-C038 for identifiers in unreachable conditional branches.
    /// Resolution still proceeds so cannot-find-name errors in dead code are not lost.
    suppress_used_before_assigned: bool,
    /// Accumulated return expression types per function body node, used to
    /// infer function and getter return types when no annotation is present.
    return_types: HashMap<NodeId, Vec<TypeId>>,
    /// Accumulated yielded element types per generator body node.
    yield_types: HashMap<NodeId, Vec<TypeId>>,
    /// Function and class method bodies whose historical inference result is `void`.
    declaration_function_bodies: HashSet<NodeId>,
    /// Stack of function body node ids currently being resolved, innermost last.
    function_body_stack: Vec<NodeId>,
    /// Return contract for each function body currently being resolved.
    return_contexts: Vec<ReturnContext>,
    /// One directive that suppresses diagnostics on each target source line.
    diagnostic_suppressions: HashMap<usize, Vec<DiagnosticSuppression>>,
    /// `@ts-expect-error` directives in source order, with exact consumption state.
    expected_diagnostics: Vec<ExpectedDiagnostic>,
    /// Enclosing `this` types for `this` expressions, innermost last.
    this_context: Vec<TypeId>,
    /// Whether the current binding context is inside a `declare` directive.
    /// Ambient declarations are not uninitialized.
    ambient_binding: bool,
    /// Whether the source file is a `.d.ts`/`.d.mts`/`.d.cts` declaration file.
    /// Top-level statements in such files must be declarations.
    is_declaration_file: bool,
    /// Whether the source file is an external module. Script files expose
    /// top-level declarations to the global scope, where they can collide with
    /// built-in global identifiers (`globalThis`, `undefined`) per TS2397.
    is_module: bool,
    /// Cooperative cancellation signal. `None` for the non-cancellable path;
    /// set by `_with_cancel` entry points so long loops and recursive
    /// entrypoints can poll it.
    pub(crate) cancel: Option<bamts_cancel::CancellationToken>,
    /// Current depth of recursive type resolution (`resolve_type` and its
    /// callees). Guarded against `MAX_TYPE_DEPTH` to prevent stack overflow
    /// on pathological inputs, mirroring the parser's `enter()`/`leave()`.
    type_resolution_depth: u32,
}

impl<'src> Binder<'src> {
    pub(crate) fn with_environment(
        source: &'src SourceFile,
        intrinsics: GlobalEnvironment,
        is_module: bool,
        options: ProgramCheckOptions,
    ) -> Self {
        let DiagnosticSuppressions {
            lines: diagnostic_suppressions,
            expectations: expected_diagnostics,
        } = diagnostic_suppressions(source);
        let mut checker = Self {
            source,
            intrinsics,
            scopes: Vec::new(),
            symbols: Vec::new(),
            symbol_types: Vec::new(),
            overload_signatures: Vec::new(),
            type_state: Vec::new(),
            type_defs: HashMap::new(),
            interface_merges: HashMap::new(),
            references: HashMap::new(),
            reference_aliases: HashMap::new(),
            type_nodes: HashMap::new(),
            node_types: HashMap::new(),
            typed_expressions: Vec::new(),
            symbol_references: Vec::new(),
            diagnostics: Vec::new(),
            probing_contextual_type: false,
            pending_constraint_checks: Vec::new(),
            type_parameter_defaults: HashMap::new(),
            alias_resolution_stack: Vec::new(),
            alias_resolution_dependencies: HashSet::new(),
            types: TypeTable::new(),
            module_scope: ScopeId(0),
            global_scope: ScopeId(0),
            ambient_modules: HashMap::new(),
            enum_declarations: Vec::new(),
            enum_declaration_symbols: HashMap::new(),
            enum_member_scopes: HashMap::new(),
            enum_member_symbols: HashMap::new(),
            enum_member_names: HashMap::new(),
            enum_member_symbols_by_name: HashMap::new(),
            enum_member_identifier_uses: HashSet::new(),
            imported_enum_member_uses: HashMap::new(),
            local_enum_member_targets: HashMap::new(),
            imported_enum_member_targets: HashSet::new(),
            namespace_declarations: Vec::new(),
            namespace_export_scopes: HashMap::new(),
            namespace_local_scopes: HashMap::new(),
            namespace_local_of_symbol: HashMap::new(),
            active_namespace_declarations: Vec::new(),
            namespace_reference_blocks: HashMap::new(),
            namespace_qualified_type_paths: HashMap::new(),
            class_member_scopes: HashMap::new(),
            interface_member_scopes: HashMap::new(),
            member_reference_recorded: HashSet::new(),
            property_sites: Vec::new(),
            property_site_index: HashMap::new(),
            property_anchors: Vec::new(),
            property_anchor_index: HashMap::new(),
            literal_anchor: HashMap::new(),
            symbol_anchor: HashMap::new(),
            import_equals_symbols: HashMap::new(),
            qualified_import_paths: HashMap::new(),
            import_equals_targets: HashMap::new(),
            class_constructor_types: HashMap::new(),
            imported_type_parameters: HashMap::new(),
            imported_type_planes: HashMap::new(),
            hoisted_declaration_symbols: HashMap::new(),
            class_instance_types: HashMap::new(),
            reg_exp_instance_type: None,
            class_method_signature_scopes: HashMap::new(),
            class_header_scopes: HashMap::new(),
            class_declaration_symbols: HashMap::new(),
            class_owner_stack: Vec::new(),
            class_base_symbols: HashMap::new(),
            super_member_homes: Vec::new(),
            jsx_element_types: HashMap::new(),
            jsx_callables: HashMap::new(),
            jsx_factory_signatures: HashMap::new(),
            reassigned_flow_roots: HashSet::new(),
            reassigned_flow_roots_stack: Vec::new(),
            super_call_contexts: Vec::new(),
            derived_constructor_super_presence: Vec::new(),
            class_derived_stack: Vec::new(),
            constructor_writable_readonly_properties: Vec::new(),
            readonly_assignment_targets: HashSet::new(),
            new_target_contexts: Vec::new(),
            flow_facts: FlowFacts::new(),
            flow: FlowNodeId::ROOT,
            ambient_stack: Vec::new(),
            strict_null_checks: options.strict_null_checks(),
            no_implicit_any: options.no_implicit_any(),
            strict_property_initialization: options.strict_property_initialization(),
            es5: options.es5(),
            uninitialized_variables: HashSet::new(),
            declarator_symbols: HashMap::new(),
            suppress_used_before_assigned: false,
            diagnostic_suppressions,
            expected_diagnostics,
            return_types: HashMap::new(),
            yield_types: HashMap::new(),
            declaration_function_bodies: HashSet::new(),
            function_body_stack: Vec::new(),
            return_contexts: Vec::new(),
            this_context: Vec::new(),
            type_resolution_depth: 0,
            ambient_binding: false,
            is_declaration_file: source.source_text().is_declaration_file(),
            is_module,
            cancel: None,
        };
        let global_scope = checker.new_scope(ScopeKind::Global, None);
        checker.global_scope = global_scope;
        checker.module_scope = checker.new_scope(ScopeKind::Module, Some(global_scope));
        checker.scopes[checker.module_scope.0 as usize].strict = is_module
            || options.always_strict()
            || directive_prologue_is_strict(source, source.statements());
        checker.bind_intrinsic_environment(global_scope);
        checker
    }

    /// Constructs a binder that polls `cancel` during long loops and
    /// recursive entrypoints. The token is also threaded into relation,
    /// inference, and narrowing sub-engines.
    pub(crate) fn with_environment_and_cancel(
        source: &'src SourceFile,
        intrinsics: GlobalEnvironment,
        is_module: bool,
        options: ProgramCheckOptions,
        cancel: bamts_cancel::CancellationToken,
    ) -> Self {
        let mut binder = Self::with_environment(source, intrinsics, is_module, options);
        binder.cancel = Some(cancel);
        binder
    }

    /// Returns `Err(CheckCancelled)` when the cancellation token has been
    /// triggered, `Ok(())` otherwise. No-op when no token is installed.
    fn check_cancel(&self) -> Result<(), super::CheckCancelled> {
        match &self.cancel {
            Some(token) => token.check().map_err(super::CheckCancelled::from),
            None => Ok(()),
        }
    }

    fn types_assignable(&self, source: TypeId, target: TypeId) -> bool {
        if self.strict_null_checks {
            self.types.assignable_with_strict_null(source, target)
        } else {
            self.types.assignable(source, target)
        }
    }

    /// Resolves a `Type::Named` type-parameter symbol to its effective
    /// (non-type-parameter) constraint, following chains and terminating on cycles.
    /// Returns `None` for an unconstrained type parameter or for a named type that
    /// is not a type parameter.
    fn type_parameter_effective_constraint(&self, type_id: TypeId) -> Option<TypeId> {
        let Type::Named(symbol) = self.types.get(type_id) else {
            return None;
        };
        if self.symbols[symbol.get() as usize].kind() != SymbolKind::TypeParameter {
            return None;
        }
        let mut current = *symbol;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            let constraint = self.types.type_parameter_constraint(current)?;
            match self.types.get(constraint) {
                Type::Named(next)
                    if self.symbols[next.get() as usize].kind() == SymbolKind::TypeParameter =>
                {
                    current = *next;
                    continue;
                }
                _ => return Some(constraint),
            }
        }
        None
    }

    /// Returns the type to use for assertion overlap when `type_id` is a
    /// type parameter: its constraint if present, or `unknown` when unconstrained.
    /// Non-type-parameters are returned unchanged.
    fn effective_overlap_type(&self, type_id: TypeId) -> TypeId {
        self.type_parameter_effective_constraint(type_id)
            .unwrap_or_else(|| {
                if let Type::Named(symbol) = self.types.get(type_id)
                    && self.symbols[symbol.get() as usize].kind() == SymbolKind::TypeParameter
                {
                    return self.types.unknown();
                }
                type_id
            })
    }

    fn is_valid_rest_parameter_type(&self, type_id: TypeId) -> bool {
        let resolved = self
            .type_parameter_effective_constraint(type_id)
            .unwrap_or(type_id);
        matches!(
            self.types.get(resolved),
            Type::Any | Type::Error | Type::Array(_) | Type::Tuple(_)
        )
    }

    /// Whether a type assertion is valid in either the source-to-target or
    /// target-to-source direction, allowing both narrowing and widening casts
    /// while still rejecting unrelated types.
    fn is_assertion_compatible(&self, source: TypeId, target: TypeId) -> bool {
        let source = self.effective_overlap_type(source);
        let target = self.effective_overlap_type(target);
        self.types.comparable(source, target)
    }

    fn is_typescript(&self) -> bool {
        matches!(
            self.source.script_kind(),
            ScriptKind::TypeScript | ScriptKind::TypeScriptReact
        )
    }

    fn bind_intrinsic_environment(&mut self, scope: ScopeId) {
        // The Error family are constructor functions whose `prototype` carries
        // `name`/`message`/`stack`/`cause`. Registering the instance type lets
        // `class X extends Error` inherit those members (so `X.prototype.name`
        // resolves) and lets `Error.prototype.name` resolve, while the
        // constructor-side fallthrough in `property_type_for_member` stays
        // permissive for intrinsics so `Error.<static>` does not newly C057.
        let error_instance = self.types.object_type(vec![
            PropertyType::new("name", false, self.types.string()),
            PropertyType::new("message", false, self.types.string()),
            PropertyType::new("stack", true, self.types.string()),
            PropertyType::new("cause", true, self.types.unknown()),
        ]);
        let any = self.types.any();
        let global_this_type = self.types.object_type(
            self.intrinsics
                .values()
                .iter()
                .map(|name| PropertyType::new(*name, false, any))
                .collect(),
        );
        let mut set_value = None;
        let mut map_value = None;
        for name in self
            .intrinsics
            .values()
            .iter()
            .chain(self.intrinsics.module_values().iter())
        {
            let id = self.declare(
                name,
                SymbolKind::IntrinsicValue,
                scope,
                NodeId::default(),
                NodeId::default_range(),
            );
            if *name == "Set" {
                set_value = Some(id);
            }
            if *name == "Map" {
                map_value = Some(id);
            }
            if *name == "undefined" {
                self.symbol_types[id.get() as usize] = self.types.undefined_type();
            }
            if *name == "globalThis" {
                self.symbol_types[id.get() as usize] = global_this_type;
            }
            if matches!(
                *name,
                "Error"
                    | "AggregateError"
                    | "EvalError"
                    | "RangeError"
                    | "ReferenceError"
                    | "SyntaxError"
                    | "TypeError"
                    | "URIError"
            ) {
                self.types.declare_class(id, Vec::new());
                self.types.publish_final_class_template(id, error_instance);
                let applied = self.types.applied_class(id, Vec::new());
                self.class_instance_types.insert(id, applied);
            }
        }
        for name in self.intrinsics.types().iter() {
            let id = self.declare(
                name,
                SymbolKind::IntrinsicType,
                scope,
                NodeId::default(),
                NodeId::default_range(),
            );
            if *name == "Object" {
                self.types.object_symbol = Some(id);
            }
            // Slot order: [Set, ReadonlySet, Map, ReadonlyMap].
            match *name {
                "Set" => self.types.collection_symbols[0] = Some(id),
                "ReadonlySet" => self.types.collection_symbols[1] = Some(id),
                "Map" => self.types.collection_symbols[2] = Some(id),
                "ReadonlyMap" => self.types.collection_symbols[3] = Some(id),
                "Record" => self.types.record_symbol = Some(id),
                "PropertyKey" => self.types.property_key_symbol = Some(id),
                "ConcatArray" => self.types.concat_array_symbol = Some(id),
                _ => {}
            }
            if *name == "RegExp" {
                self.types.declare_class(id, Vec::new());
                let string = self.types.string();
                let boolean = self.types.boolean();
                let array_of_string = self.types.array(string);
                let exec_return = self.types.union(&[array_of_string, self.types.null_type()]);
                let exec = self.types.function_with_parameters(
                    Vec::new(),
                    vec![FunctionParameter::new(
                        "string".to_owned(),
                        string,
                        false,
                        false,
                    )],
                    exec_return,
                );
                let test = self.types.function_with_parameters(
                    Vec::new(),
                    vec![FunctionParameter::new(
                        "string".to_owned(),
                        string,
                        false,
                        false,
                    )],
                    boolean,
                );
                let reg_exp_instance = self.types.object_type(vec![
                    PropertyType::new("source", false, string),
                    PropertyType::new("flags", false, string),
                    PropertyType::new("exec", false, exec).with_method(true),
                    PropertyType::new("test", false, test).with_method(true),
                ]);
                self.types
                    .publish_final_class_template(id, reg_exp_instance);
                let applied = self.types.applied_class(id, Vec::new());
                self.class_instance_types.insert(id, applied);
                self.reg_exp_instance_type = Some(applied);
            }
        }
        if let (
            Some(set_value),
            Some(map_value),
            [
                Some(set_type),
                Some(readonly_set_type),
                Some(map_type),
                Some(readonly_map_type),
            ],
        ) = (set_value, map_value, self.types.collection_symbols)
        {
            self.bind_collection_intrinsics(CollectionIntrinsicSymbols {
                set_value,
                map_value,
                set_type,
                readonly_set_type,
                map_type,
                readonly_map_type,
            });
        }
    }

    fn bind_collection_intrinsics(&mut self, symbols: CollectionIntrinsicSymbols) {
        let parameter_scope = self.new_scope(ScopeKind::Block, None);
        let set_parameter = self.declare_intrinsic_type_parameter(parameter_scope, "SetT");
        let readonly_set_parameter =
            self.declare_intrinsic_type_parameter(parameter_scope, "ReadonlySetT");
        let map_key = self.declare_intrinsic_type_parameter(parameter_scope, "MapK");
        let map_value = self.declare_intrinsic_type_parameter(parameter_scope, "MapV");
        let readonly_map_key =
            self.declare_intrinsic_type_parameter(parameter_scope, "ReadonlyMapK");
        let readonly_map_value =
            self.declare_intrinsic_type_parameter(parameter_scope, "ReadonlyMapV");

        self.bind_set_intrinsic(symbols.set_type, set_parameter, true);
        self.bind_set_intrinsic(symbols.readonly_set_type, readonly_set_parameter, false);
        self.bind_map_intrinsic(symbols.map_type, map_key, map_value, true);
        self.bind_map_intrinsic(
            symbols.readonly_map_type,
            readonly_map_key,
            readonly_map_value,
            false,
        );

        let set_element = self.types.named(set_parameter);
        let set_constructor = self.collection_constructor(
            symbols.set_type,
            vec![set_parameter],
            "values",
            set_element,
        );
        self.symbol_types[symbols.set_value.get() as usize] = set_constructor;
        let set_instance = self
            .types
            .applied_class(symbols.set_type, vec![self.types.any()]);
        self.class_instance_types
            .insert(symbols.set_value, set_instance);

        let map_key_type = self.types.named(map_key);
        let map_value_type = self.types.named(map_value);
        let map_entry = self.types.tuple(vec![map_key_type, map_value_type]);
        let map_constructor = self.collection_constructor(
            symbols.map_type,
            vec![map_key, map_value],
            "entries",
            map_entry,
        );
        self.symbol_types[symbols.map_value.get() as usize] = map_constructor;
        let map_instance = self
            .types
            .applied_class(symbols.map_type, vec![self.types.any(), self.types.any()]);
        self.class_instance_types
            .insert(symbols.map_value, map_instance);
    }

    fn declare_intrinsic_type_parameter(&mut self, scope: ScopeId, name: &str) -> SymbolId {
        let id = self.declare(
            name,
            SymbolKind::TypeParameter,
            scope,
            NodeId::default(),
            NodeId::default_range(),
        );
        let ty = self.types.named(id);
        self.symbol_types[id.get() as usize] = ty;
        id
    }

    fn bind_set_intrinsic(&mut self, owner: SymbolId, parameter: SymbolId, mutable: bool) {
        self.types.declare_class(owner, vec![parameter]);
        self.types.set_class_bounds(
            owner,
            vec![TypeParameterBounds::new(None, Some(self.types.any()))],
        );
        let element = self.types.named(parameter);
        let instance = self
            .types
            .declared_class(owner)
            .expect("collection class declared");
        let this_type = self.types.this_type(owner, instance);
        let iterator = self.collection_iterator(element);
        let pair = self.types.tuple(vec![element, element]);
        let entries = self.collection_iterator(pair);
        let callback = self.types.function_with_parameters(
            Vec::new(),
            vec![
                FunctionParameter::new("value".to_owned(), element, false, false),
                FunctionParameter::new("value2".to_owned(), element, false, false),
                FunctionParameter::new("set".to_owned(), instance, false, false),
            ],
            self.types.void(),
        );
        let mut properties = vec![
            PropertyType::new("size", false, self.types.number()).with_readonly(true),
            self.collection_method(
                owner,
                "has",
                vec![("value", element, false)],
                self.types.boolean(),
            ),
            self.collection_method(
                owner,
                "forEach",
                vec![
                    ("callbackfn", callback, false),
                    ("thisArg", self.types.any(), true),
                ],
                self.types.void(),
            ),
            self.collection_method(owner, "entries", Vec::new(), entries),
            self.collection_method(owner, "keys", Vec::new(), iterator),
            self.collection_method(owner, "values", Vec::new(), iterator),
        ];
        if mutable {
            properties.extend([
                self.collection_method(owner, "add", vec![("value", element, false)], this_type),
                self.collection_method(owner, "clear", Vec::new(), self.types.void()),
                self.collection_method(
                    owner,
                    "delete",
                    vec![("value", element, false)],
                    self.types.boolean(),
                ),
            ]);
        }
        let iterator_method = self.types.function(Vec::new(), iterator);
        let raw = self.types.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: Some(
                IteratorProperty::new(iterator_method, false)
                    .with_method(true)
                    .with_declaring_type(owner),
            ),
            async_iterator_property: None,
        });
        self.types.publish_final_class_template(owner, raw);
    }

    fn bind_map_intrinsic(
        &mut self,
        owner: SymbolId,
        key_parameter: SymbolId,
        value_parameter: SymbolId,
        mutable: bool,
    ) {
        self.types
            .declare_class(owner, vec![key_parameter, value_parameter]);
        self.types.set_class_bounds(
            owner,
            vec![
                TypeParameterBounds::new(None, Some(self.types.any())),
                TypeParameterBounds::new(None, Some(self.types.any())),
            ],
        );
        let key = self.types.named(key_parameter);
        let value = self.types.named(value_parameter);
        let entry = self.types.tuple(vec![key, value]);
        let instance = self
            .types
            .declared_class(owner)
            .expect("collection class declared");
        let this_type = self.types.this_type(owner, instance);
        let entries = self.collection_iterator(entry);
        let keys = self.collection_iterator(key);
        let values = self.collection_iterator(value);
        let callback = self.types.function_with_parameters(
            Vec::new(),
            vec![
                FunctionParameter::new("value".to_owned(), value, false, false),
                FunctionParameter::new("key".to_owned(), key, false, false),
                FunctionParameter::new("map".to_owned(), instance, false, false),
            ],
            self.types.void(),
        );
        let maybe_value = self.types.union(&[value, self.types.undefined_type()]);
        let mut properties = vec![
            PropertyType::new("size", false, self.types.number()).with_readonly(true),
            self.collection_method(owner, "get", vec![("key", key, false)], maybe_value),
            self.collection_method(
                owner,
                "has",
                vec![("key", key, false)],
                self.types.boolean(),
            ),
            self.collection_method(
                owner,
                "forEach",
                vec![
                    ("callbackfn", callback, false),
                    ("thisArg", self.types.any(), true),
                ],
                self.types.void(),
            ),
            self.collection_method(owner, "entries", Vec::new(), entries),
            self.collection_method(owner, "keys", Vec::new(), keys),
            self.collection_method(owner, "values", Vec::new(), values),
        ];
        if mutable {
            properties.extend([
                self.collection_method(
                    owner,
                    "set",
                    vec![("key", key, false), ("value", value, false)],
                    this_type,
                ),
                self.collection_method(owner, "clear", Vec::new(), self.types.void()),
                self.collection_method(
                    owner,
                    "delete",
                    vec![("key", key, false)],
                    self.types.boolean(),
                ),
            ]);
        }
        let iterator_method = self.types.function(Vec::new(), entries);
        let raw = self.types.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: Some(
                IteratorProperty::new(iterator_method, false)
                    .with_method(true)
                    .with_declaring_type(owner),
            ),
            async_iterator_property: None,
        });
        self.types.publish_final_class_template(owner, raw);
    }

    fn collection_iterator(&mut self, element: TypeId) -> TypeId {
        self.intrinsic_iterable_iterator_type(
            element,
            self.types.undefined_type(),
            self.types.unknown(),
            ForOfMode::Sync,
        )
    }

    fn collection_method(
        &mut self,
        owner: SymbolId,
        name: &str,
        parameters: Vec<(&str, TypeId, bool)>,
        return_type: TypeId,
    ) -> PropertyType {
        let parameters = parameters
            .into_iter()
            .map(|(name, ty, optional)| {
                FunctionParameter::new(name.to_owned(), ty, optional, false)
            })
            .collect();
        let method = self
            .types
            .function_with_parameters(Vec::new(), parameters, return_type);
        PropertyType::new(name, false, method)
            .with_method(true)
            .with_declaring_types(vec![owner])
    }

    fn collection_constructor(
        &mut self,
        owner: SymbolId,
        parameters: Vec<SymbolId>,
        parameter_name: &str,
        element: TypeId,
    ) -> TypeId {
        let iterable = self.intrinsic_iterable_type(
            element,
            self.types.any(),
            self.types.any(),
            ForOfMode::Sync,
        );
        let array = self.types.array(element);
        let null = self.types.null_type();
        let values = self.types.union(&[array, iterable, null]);
        let arguments = parameters
            .iter()
            .map(|parameter| self.types.named(*parameter))
            .collect();
        let result = self.types.applied_class(owner, arguments);
        let bounds = vec![TypeParameterBounds::new(None, Some(self.types.any())); parameters.len()];
        let signature_type = self.types.function_with_parameter_bounds(
            parameters,
            bounds,
            vec![FunctionParameter::new(
                parameter_name.to_owned(),
                values,
                true,
                false,
            )],
            result,
            false,
        );
        let Type::Function(signature) = self.types.get(signature_type).clone() else {
            unreachable!("collection constructor is a function")
        };
        let any_arguments = vec![self.types.any(); self.types.class_type_parameters(owner).len()];
        let prototype = self.types.applied_class(owner, any_arguments);
        self.types.object_type_with_members(ObjectType {
            properties: vec![PropertyType::new("prototype", false, prototype).with_readonly(true)],
            call_signatures: Vec::new(),
            construct_signatures: vec![ConstructEntry {
                signature,
                is_abstract: false,
            }],
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        })
    }

    fn run_with_imported_types_and_cancel(
        &mut self,
        imported_types: &[ImportedSymbolType<'_>],
    ) -> Result<(), super::CheckCancelled> {
        let statements = self.source.statements();
        let scope = self.module_scope;
        if self.is_declaration_file {
            for statement in statements {
                if !Self::is_declaration_statement(statement.data()) {
                    self.emit(
                        STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT,
                        statement.range(),
                        STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT_MESSAGE,
                    );
                }
            }
        }
        self.check_cancel()?;
        self.bind_statement_names_and_class_headers(statements, scope);
        self.check_cancel()?;
        self.bind_hoisted_statements(statements, scope);
        self.check_cancel()?;
        self.build_import_equals_targets(statements, scope);
        let mut imported_by_source = HashMap::<*const TypeTable, ImportedTypeMap>::new();
        let mut models_by_source = HashMap::<*const TypeTable, &SemanticModel>::new();
        let mut next_imported_symbol =
            u32::try_from(self.symbols.len()).expect("symbol count fits in u32");
        for imported in imported_types {
            self.check_cancel()?;
            let source_types = imported.source_model.types();
            let source_key = std::ptr::from_ref(source_types);
            models_by_source
                .entry(source_key)
                .or_insert(imported.source_model);
            let identities = imported_by_source.entry(source_key).or_default();
            let (value_type_id, type_parameters) = self.types.import_type(
                source_types,
                imported.value_type_id,
                imported.type_parameters,
                identities,
                &mut next_imported_symbol,
            );
            if !type_parameters.is_empty() {
                self.imported_type_parameters
                    .insert(imported.symbol, type_parameters);
            }
            if let Some(source_type_id) = imported.type_plane_id {
                let (type_id, _) = self.types.import_type(
                    source_types,
                    source_type_id,
                    imported.type_parameters,
                    identities,
                    &mut next_imported_symbol,
                );
                self.imported_type_planes.insert(imported.symbol, type_id);
            }
            self.symbol_types[imported.symbol.get() as usize] = value_type_id;
            self.type_state[imported.symbol.get() as usize] = TypeState::Done(value_type_id);
        }
        self.materialize_imported_symbols(
            &mut imported_by_source,
            &models_by_source,
            &mut next_imported_symbol,
        )?;
        self.resolve_statement_class_bounds(statements);
        self.check_cancel()?;
        self.resolve_statements(statements, scope);
        self.check_cancel()?;
        self.validate_pending_constraints();
        self.validate_alias_cycles();
        self.check_export_assignment_conflicts();
        Ok(())
    }

    fn materialize_imported_symbols(
        &mut self,
        imported_by_source: &mut HashMap<*const TypeTable, ImportedTypeMap>,
        models_by_source: &HashMap<*const TypeTable, &SemanticModel>,
        next_imported_symbol: &mut u32,
    ) -> Result<(), super::CheckCancelled> {
        let mut cursors = HashMap::<*const TypeTable, usize>::new();
        loop {
            self.check_cancel()?;
            let target = u32::try_from(self.symbols.len()).expect("symbol count fits in u32");
            if target == *next_imported_symbol {
                break;
            }

            let mut located = None;
            for (&source_key, identities) in imported_by_source.iter() {
                let cursor = cursors.get(&source_key).copied().unwrap_or(0);
                if let Some(&(source_symbol, synthesized)) = identities.synthesized.get(cursor)
                    && synthesized.get() == target
                {
                    located = Some((source_key, source_symbol));
                    cursors.insert(source_key, cursor + 1);
                    break;
                }
            }
            let (source_key, source_symbol) =
                located.expect("every synthesized import SymbolId records its source");
            let source_model = models_by_source[&source_key];
            let source_symbol_data = source_model.symbol(source_symbol).clone();
            let source_type = source_model.symbol_type(source_symbol);
            let identities = imported_by_source
                .get_mut(&source_key)
                .expect("located source has an identity map");
            let (copied_type, _) = self.types.import_type(
                source_model.types(),
                source_type,
                &[],
                identities,
                next_imported_symbol,
            );
            let parent = source_symbol_data
                .parent()
                .and_then(|parent| identities.symbols.get(&parent).copied());

            self.symbols.push(Symbol {
                name: source_symbol_data.name().to_owned(),
                kind: source_symbol_data.kind(),
                scope: self.module_scope,
                declaration: NodeId::default(),
                range: NodeId::default_range(),
                parent,
            });
            self.symbol_types.push(copied_type);
            self.overload_signatures.push(Vec::new());
            self.type_state.push(TypeState::Done(copied_type));
        }
        Ok(())
    }

    fn validate_alias_cycles(&mut self) {
        let aliases: Vec<SymbolId> = self
            .type_defs
            .iter()
            .filter_map(|(&symbol, definition)| {
                matches!(definition, TypeDef::Alias { .. }).then_some(symbol)
            })
            .collect();
        for symbol in aliases {
            if self.types.is_circular_alias(symbol) {
                let range = self.symbols[symbol.get() as usize].range();
                self.emit(TYPE_ALIAS_CIRCULAR, range, TYPE_ALIAS_CIRCULAR_MESSAGE);
            }
        }
    }

    fn validate_pending_constraints(&mut self) {
        let pending = std::mem::take(&mut self.pending_constraint_checks);
        let pending: Vec<_> = pending
            .into_iter()
            .filter_map(|check| {
                let constraint = self.types.type_parameter_constraint(check.parameter)?;
                let constraint = check.substitution.instantiate(&mut self.types, constraint);
                Some((check.argument, constraint, check.range))
            })
            .collect();
        let relations = TypeRelations::new_with_cancel(&self.types, self.cancel.clone());
        let failed: Vec<_> = pending
            .into_iter()
            .filter(|(argument, constraint, _)| {
                let compatible = if self.strict_null_checks {
                    relations.assignable_with_strict_null(*argument, *constraint)
                } else {
                    relations.assignable(*argument, *constraint)
                };
                !compatible
            })
            .collect();
        drop(relations);

        for (_, _, range) in failed {
            self.emit(
                ARGUMENT_NOT_ASSIGNABLE,
                range,
                ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
            );
        }
    }

    fn is_declaration_statement(statement: &Statement) -> bool {
        matches!(
            statement,
            Statement::Import(_)
                | Statement::ImportEquals(_)
                | Statement::Export(_)
                | Statement::Variable(_)
                | Statement::Function(_)
                | Statement::Class(_)
                | Statement::Interface(_)
                | Statement::TypeAlias(_)
                | Statement::Enum(_)
                | Statement::Namespace(_)
                | Statement::Declare(_)
                | Statement::Empty
                | Statement::Missing(_)
        )
    }

    pub(crate) fn finish(mut self) -> (SemanticModel, Vec<Diagnostic>) {
        let enum_declarations = std::mem::take(&mut self.enum_declarations);
        let enum_member_symbols = std::mem::take(&mut self.enum_member_symbols);
        let enum_member_names = std::mem::take(&mut self.enum_member_names);
        let enum_member_identifier_uses = std::mem::take(&mut self.enum_member_identifier_uses);
        let imported_enum_member_uses = std::mem::take(&mut self.imported_enum_member_uses);
        let local_enum_member_targets = std::mem::take(&mut self.local_enum_member_targets);
        let imported_enum_member_targets = std::mem::take(&mut self.imported_enum_member_targets);
        let namespace_declarations = std::mem::take(&mut self.namespace_declarations);
        let namespace_reference_blocks = std::mem::take(&mut self.namespace_reference_blocks);
        let namespace_qualified_type_paths =
            std::mem::take(&mut self.namespace_qualified_type_paths);
        let generic_type_parameters = self
            .type_defs
            .iter()
            .filter_map(|(&symbol, definition)| {
                let (scope, list) = match definition {
                    TypeDef::Alias {
                        scope,
                        type_parameters,
                        ..
                    }
                    | TypeDef::Interface {
                        scope,
                        type_parameters,
                    } => (*scope, *type_parameters),
                    TypeDef::Enum { .. } => return None,
                };
                let parameters = list
                    .into_iter()
                    .flat_map(|list| &list.parameters)
                    .filter_map(|parameter| {
                        let name = self.identifier_text(&parameter.data().name);
                        self.lookup_type(scope, &name)
                    })
                    .collect();
                Some((symbol, parameters))
            })
            .collect();
        let qualified_import_paths = std::mem::take(&mut self.qualified_import_paths);
        debug_assert_eq!(self.symbols.len(), self.symbol_types.len());
        debug_assert_eq!(self.symbols.len(), self.type_state.len());
        debug_assert_eq!(self.symbols.len(), self.overload_signatures.len());
        let mut model = SemanticModel {
            scopes: self.scopes,
            symbols: self.symbols,
            symbol_types: self.symbol_types,
            #[cfg(test)]
            overload_signatures: self.overload_signatures,
            references: self.references,
            reference_aliases: self.reference_aliases,
            property_sites: self.property_sites,
            property_anchors: self.property_anchors,
            type_nodes: self.type_nodes,
            node_types: self.node_types,
            typed_expressions: self.typed_expressions,
            symbol_references: self.symbol_references,
            generic_type_parameters,
            types: self.types,
            module_scope: self.module_scope,
            facts: AnalysisFacts::default(),
            enum_facts: EnumFacts::unchecked(),
            namespace_facts: NamespaceFacts::unchecked(),
            ambient_modules: std::mem::take(&mut self.ambient_modules),
            class_constructor_types: std::mem::take(&mut self.class_constructor_types),
            namespace_local_scopes: std::mem::take(&mut self.namespace_local_scopes),
        };
        let (enum_facts, diagnostics) = enum_plan::build(
            &model,
            self.source,
            self.source.source_id(),
            &enum_declarations,
            &enum_member_symbols,
            &enum_member_names,
            &enum_member_identifier_uses,
            &local_enum_member_targets,
            &imported_enum_member_uses,
            &imported_enum_member_targets,
        );
        model.enum_facts = enum_facts;
        let mut namespace_facts = namespace_plan::build(
            &model,
            self.source,
            &namespace_declarations,
            &namespace_reference_blocks,
            namespace_qualified_type_paths,
        );
        namespace_facts.set_qualified_import_paths(qualified_import_paths);
        model.namespace_facts = namespace_facts;
        for diagnostic in diagnostics {
            let line = self
                .source
                .source_text()
                .line_column(diagnostic.range().start())
                .expect("diagnostic range belongs to its source")
                .0;
            if !consume_diagnostic_suppression(
                &self.diagnostic_suppressions,
                &mut self.expected_diagnostics,
                line,
            ) {
                self.diagnostics.push(diagnostic);
            }
        }
        for expectation in &self.expected_diagnostics {
            if !expectation.used {
                self.diagnostics.push(Diagnostic::error(
                    UNUSED_EXPECT_ERROR,
                    self.source.source_id(),
                    expectation.directive_range,
                    UNUSED_EXPECT_ERROR_MESSAGE,
                ));
            }
        }
        (model, self.diagnostics)
    }

    // -- text and scope helpers ------------------------------------------------

    pub(crate) fn text(&self, token: &Token) -> &'src str {
        self.source.token_text(token).unwrap_or("")
    }
    // -- control-flow narrowing ------------------------------------------------

    /// Guards a condition proves at `negated` polarity, with every guarded
    /// symbol's declared type registered so the refinement has a base to narrow.
    fn guards_for(&mut self, condition: &'src Expr, negated: bool) -> Vec<NarrowingGuard> {
        let resolver = BinderGuardResolver {
            references: &self.references,
            node_types: &self.node_types,
            source: self.source,
            fallback: self.types.any(),
        };
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        let guards = narrowing.guards_from(condition, &resolver, negated);
        for guard in &guards {
            let symbol = guard.reference().root_symbol();
            narrowing.declare(symbol, self.symbol_types[symbol.get() as usize]);
        }
        guards
    }

    /// Forks `parent` and refines the fork by `guards`.
    fn branch_guarded(&mut self, parent: FlowNodeId, guards: &[NarrowingGuard]) -> FlowNodeId {
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        let flow = narrowing.branch(parent);
        narrowing.apply_guards(flow, guards);
        flow
    }

    /// Runs `walk` at the program point `parent` refined by `guards`, then
    /// restores the caller's point and reports where the branch ended.
    fn in_branch(
        &mut self,
        parent: FlowNodeId,
        guards: &[NarrowingGuard],
        walk: impl FnOnce(&mut Self),
    ) -> FlowNodeId {
        let outer = self.flow;
        self.flow = self.branch_guarded(parent, guards);
        walk(self);
        let ended = self.flow;
        self.flow = outer;
        ended
    }

    /// Merges forked points back into `parent` and settles the walk there.
    fn join_flow(&mut self, parent: FlowNodeId, branches: &[FlowNodeId]) {
        self.flow = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        )
        .join(parent, branches);
    }

    /// Runs `walk` at a fresh flow root, then restores the caller's program
    /// point. Declared types remain visible, but refinements and exits inside
    /// the walk do not leak into the enclosing flow.
    fn in_isolated_flow<T>(&mut self, flow: FlowNodeId, walk: impl FnOnce(&mut Self) -> T) -> T {
        let outer = self.flow;
        self.flow = flow;
        let result = walk(self);
        self.flow = outer;
        result
    }

    /// Seeds a nested closure with narrowed bare-root facts that are stable
    /// across deferred execution. Property-path facts are deliberately not
    /// copied: a const object does not make its properties immutable.
    fn captured_flow_seed(&mut self) -> FlowNodeId {
        let outer = self.flow;
        let stable_roots: Vec<(SymbolId, TypeId)> = self
            .symbols
            .iter()
            .enumerate()
            .filter_map(|(index, symbol)| {
                let symbol_id = SymbolId::new(index as u32);
                let immutable = matches!(
                    symbol.kind,
                    SymbolKind::Variable(
                        VariableKind::Const | VariableKind::Using | VariableKind::AwaitUsing
                    )
                );
                (immutable || !self.is_reassigned_in_scope(symbol_id))
                    .then_some((symbol_id, self.symbol_types[index]))
            })
            .collect();
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        let seed = narrowing.branch(FlowNodeId::ROOT);
        for (symbol, declared) in stable_roots {
            let key = FlowKey::root(symbol);
            if let Some(narrowed) = narrowing.type_at(outer, &key)
                && narrowed != declared
            {
                narrowing.refine(seed, key, narrowed);
            }
        }
        seed
    }

    /// Effective type of `symbol` at the current program point: the nearest
    /// guard refinement, else `declared`.
    fn narrowed_type(&mut self, symbol: SymbolId, declared: TypeId) -> TypeId {
        let key = FlowKey::root(symbol);
        let flow = self.flow;
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        narrowing.declare(symbol, declared);
        narrowing.type_at(flow, &key).unwrap_or(declared)
    }

    fn assignment_flow_key(
        &self,
        target: &'src crate::syntax::AssignmentTargetNode,
    ) -> Option<FlowKey> {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => self
                .references
                .get(&identifier.id())
                .copied()
                .map(FlowKey::root),
            AssignmentTarget::Member(member) => {
                let resolver = BinderGuardResolver {
                    references: &self.references,
                    node_types: &self.node_types,
                    fallback: self.types.any(),
                    source: self.source,
                };
                let key = flow_key_of(&member.object, &resolver)?;
                let MemberProperty::Named(property) = &member.property else {
                    return None;
                };
                Some(key.child(self.identifier_text(property).as_ref()))
            }
            _ => None,
        }
    }

    fn invalidate_assignment_flow(&mut self, target: &'src crate::syntax::AssignmentTargetNode) {
        match target.data() {
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    self.invalidate_assignment_flow(&property.target);
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::AssignmentArrayElement::Target(target) = element {
                        self.invalidate_assignment_flow(target);
                    }
                }
            }
            AssignmentTarget::Identifier(_) | AssignmentTarget::Member(_) => {
                let Some(key) = self.assignment_flow_key(target) else {
                    return;
                };
                NarrowingContext::new_with_cancel(
                    &mut self.types,
                    &mut self.flow_facts,
                    self.cancel.clone(),
                )
                .invalidate(self.flow, &key);
            }
            AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(_) => {}
        }
    }

    fn record_reassigned_root(&mut self, symbol: SymbolId) {
        self.reassigned_flow_roots.insert(symbol);
    }

    fn inventory_assignment_target_writes(
        &mut self,
        target: &'src crate::syntax::AssignmentTargetNode,
        inventory: &mut WriteInventory,
    ) {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.identifier_text(identifier);
                if inventory.is_shadowed(name.as_ref()) {
                    return;
                }
                if let Some(symbol) = self.lookup_value(inventory.root_scope, name.as_ref()) {
                    self.record_reassigned_root(symbol);
                }
            }
            AssignmentTarget::Member(member) => {
                self.inventory_expression_writes(&member.object, inventory);
                if let MemberProperty::Computed(property) = &member.property {
                    self.inventory_expression_writes(property, inventory);
                }
            }
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    self.inventory_assignment_target_writes(&property.target, inventory);
                    if let Some(initializer) = &property.initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::AssignmentArrayElement::Target(target) = element {
                        self.inventory_assignment_target_writes(target, inventory);
                    }
                }
            }
            AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(_) => {}
        }
    }

    fn inventory_assignment_target_writes_in_scope(
        &mut self,
        target: &'src crate::syntax::AssignmentTargetNode,
        scope: ScopeId,
    ) {
        let mut inventory = WriteInventory {
            root_scope: scope,
            shadow_frames: Vec::new(),
        };
        self.inventory_assignment_target_writes(target, &mut inventory);
    }

    fn inventory_binding_pattern_defaults(
        &mut self,
        pattern: &'src crate::syntax::Pattern,
        inventory: &mut WriteInventory,
    ) {
        match pattern.data() {
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.inventory_binding_pattern_defaults(&property.binding, inventory);
                    if let Some(initializer) = &property.initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::ArrayBindingElement::Binding(binding) = element {
                        self.inventory_binding_pattern_defaults(binding, inventory);
                    }
                }
            }
            BindingPattern::Rest(rest) => {
                self.inventory_binding_pattern_defaults(&rest.argument, inventory);
            }
            BindingPattern::Assignment(assignment) => {
                self.inventory_binding_pattern_defaults(&assignment.left, inventory);
                self.inventory_expression_writes(&assignment.right, inventory);
            }
            BindingPattern::Identifier(_) | BindingPattern::Missing(_) => {}
        }
    }

    fn collect_write_binding_names(
        &self,
        pattern: &'src crate::syntax::Pattern,
        names: &mut HashSet<String>,
    ) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                names.insert(self.identifier_text(identifier).into_owned());
            }
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.collect_write_binding_names(&property.binding, names);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let crate::syntax::ArrayBindingElement::Binding(binding) = element {
                        self.collect_write_binding_names(binding, names);
                    }
                }
            }
            BindingPattern::Rest(rest) => {
                self.collect_write_binding_names(&rest.argument, names);
            }
            BindingPattern::Assignment(assignment) => {
                self.collect_write_binding_names(&assignment.left, names);
            }
            BindingPattern::Missing(_) => {}
        }
    }

    fn collect_direct_write_lexicals(
        &self,
        statements: &'src [crate::syntax::Stmt],
        names: &mut HashSet<String>,
    ) {
        for statement in statements {
            self.collect_direct_write_lexical(statement, names);
        }
    }

    fn collect_direct_write_lexical(
        &self,
        statement: &'src crate::syntax::Stmt,
        names: &mut HashSet<String>,
    ) {
        match statement.data() {
            Statement::Variable(variable) if variable.kind != VariableKind::Var => {
                for declarator in &variable.declarations {
                    self.collect_write_binding_names(&declarator.data().binding, names);
                }
            }
            Statement::Class(class) => {
                if let Some(name) = &class.name {
                    names.insert(self.identifier_text(name).into_owned());
                }
            }
            Statement::Enum(declaration) => {
                names.insert(self.identifier_text(&declaration.name).into_owned());
            }
            Statement::Namespace(namespace) => {
                if let Some(name) = namespace.name.as_identifier() {
                    names.insert(self.identifier_text(name).into_owned());
                }
            }
            Statement::Declare(inner) => self.collect_direct_write_lexical(inner, names),
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => self.collect_direct_write_lexical(inner, names),
            _ => {}
        }
    }

    fn collect_hoisted_write_names(
        &self,
        statements: &'src [crate::syntax::Stmt],
        names: &mut HashSet<String>,
    ) {
        for statement in statements {
            self.collect_hoisted_write_name(statement, names);
        }
    }

    fn collect_hoisted_write_name(
        &self,
        statement: &'src crate::syntax::Stmt,
        names: &mut HashSet<String>,
    ) {
        match statement.data() {
            Statement::Variable(variable) if variable.kind == VariableKind::Var => {
                for declarator in &variable.declarations {
                    self.collect_write_binding_names(&declarator.data().binding, names);
                }
            }
            Statement::Function(function) => {
                if let Some(name) = &function.function.name {
                    names.insert(self.identifier_text(name).into_owned());
                }
            }
            Statement::Block(block) => {
                self.collect_hoisted_write_names(&block.data().statements, names);
            }
            Statement::If(statement) => {
                self.collect_hoisted_write_name(&statement.consequent, names);
                if let Some(alternate) = &statement.alternate {
                    self.collect_hoisted_write_name(alternate, names);
                }
            }
            Statement::Switch(statement) => {
                for case in &statement.cases {
                    self.collect_hoisted_write_names(&case.data().consequent, names);
                }
            }
            Statement::For(statement) => {
                if let Some(ForInitializer::Variable(variable)) = &statement.initializer
                    && variable.kind == VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, names);
                    }
                }
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::ForIn(statement) => {
                if let ForBinding::Variable(variable) = &statement.binding
                    && variable.kind == VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, names);
                    }
                }
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::ForOf(statement) => {
                if let ForBinding::Variable(variable) = &statement.binding
                    && variable.kind == VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, names);
                    }
                }
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::While(statement) => {
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::DoWhile(statement) => {
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::Try(statement) => {
                self.collect_hoisted_write_names(&statement.block.data().statements, names);
                if let Some(handler) = &statement.handler {
                    self.collect_hoisted_write_names(&handler.data().body.data().statements, names);
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.collect_hoisted_write_names(&finalizer.data().statements, names);
                }
            }
            Statement::With(statement) => {
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::Labeled(statement) => {
                self.collect_hoisted_write_name(&statement.body, names);
            }
            Statement::Declare(inner) => self.collect_hoisted_write_name(inner, names),
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => self.collect_hoisted_write_name(inner, names),
            _ => {}
        }
    }

    fn is_reassigned_in_scope(&self, symbol: SymbolId) -> bool {
        if self.reassigned_flow_roots.contains(&symbol) {
            return true;
        }
        self.reassigned_flow_roots_stack
            .iter()
            .any(|frame| frame.contains(&symbol))
    }

    /// Saves the current `reassigned_flow_roots` and starts a fresh frame for
    /// a new statement list (function body, block, branch). Call
    /// `pop_reassigned_scope` when the list ends to merge parent-visible
    /// writes back.
    fn push_reassigned_scope(&mut self) {
        let outer = std::mem::take(&mut self.reassigned_flow_roots);
        self.reassigned_flow_roots_stack.push(outer);
    }

    /// Merges the current frame's writes into the parent frame and restores
    /// the parent as active. Writes in a child scope are visible to the parent
    /// because the assignment has executed by the time control returns.
    fn pop_reassigned_scope(&mut self) {
        let mut child = std::mem::take(&mut self.reassigned_flow_roots);
        if let Some(mut parent) = self.reassigned_flow_roots_stack.pop() {
            parent.extend(child.drain());
            self.reassigned_flow_roots = parent;
        } else {
            self.reassigned_flow_roots = child;
        }
    }

    pub(crate) fn identifier_text(&self, identifier: &IdentifierNode) -> Cow<'src, str> {
        self.source
            .identifier_text(identifier.data().token())
            .unwrap_or_default()
    }

    pub(crate) fn new_scope(&mut self, kind: ScopeKind, parent: Option<ScopeId>) -> ScopeId {
        let strict = parent.is_some_and(|parent| self.scopes[parent.0 as usize].strict);
        let id = ScopeId(u32::try_from(self.scopes.len()).expect("scope count fits in u32"));
        self.scopes.push(Scope {
            kind,
            parent,
            values: BTreeMap::new(),
            types: BTreeMap::new(),
            strict,
            owner: None,
            this_owner: None,
        });
        id
    }

    /// Marks `scope` as the member scope owned by `owner`; symbols declared
    /// afterwards inherit it as their qualified-name parent. Idempotent.
    fn set_scope_owner(&mut self, scope: ScopeId, owner: SymbolId) {
        self.scopes[scope.0 as usize].owner = Some(owner);
    }

    fn set_scope_this_owner(&mut self, scope: ScopeId, owner: SymbolId) {
        self.scopes[scope.0 as usize].this_owner = Some(owner);
    }

    /// Walks outward to the nearest function-like, namespace-export, or module
    /// scope. A namespace's per-block locals use `Function`; exported `var`
    /// declarations bind directly in `Namespace`, so neither can escape.
    fn value_hoist_scope(&self, scope: ScopeId) -> ScopeId {
        let mut current = scope;
        loop {
            let node = &self.scopes[current.0 as usize];
            if matches!(
                node.kind,
                ScopeKind::Class | ScopeKind::Function | ScopeKind::Module | ScopeKind::Namespace
            ) {
                return current;
            }
            match node.parent {
                Some(parent) => current = parent,
                None => return current,
            }
        }
    }

    pub(crate) fn emit(&mut self, code: DiagnosticCode, range: TextRange, message: &'static str) {
        if self.probing_contextual_type {
            return;
        }
        let line = self
            .source
            .source_text()
            .line_column(range.start())
            .expect("diagnostic range belongs to its source")
            .0;
        if consume_diagnostic_suppression(
            &self.diagnostic_suppressions,
            &mut self.expected_diagnostics,
            line,
        ) {
            return;
        }
        self.diagnostics.push(Diagnostic::error(
            code,
            self.source.source_id(),
            range,
            message,
        ));
    }

    /// Like [`emit`](Self::emit) but accepts an owned message for diagnostics
    /// whose wording includes the offending identifier name.
    fn emit_with_message(&mut self, code: DiagnosticCode, range: TextRange, message: String) {
        if self.probing_contextual_type {
            return;
        }
        let line = self
            .source
            .source_text()
            .line_column(range.start())
            .expect("diagnostic range belongs to its source")
            .0;
        if consume_diagnostic_suppression(
            &self.diagnostic_suppressions,
            &mut self.expected_diagnostics,
            line,
        ) {
            return;
        }
        self.diagnostics.push(Diagnostic::error(
            code,
            self.source.source_id(),
            range,
            message,
        ));
    }

    // -- declaration binding ---------------------------------------------------

    fn declare(
        &mut self,
        name: &str,
        kind: SymbolKind,
        scope: ScopeId,
        declaration: NodeId,
        range: TextRange,
    ) -> SymbolId {
        // `var` and function declarations are hoisted to the nearest Function or
        // Module scope, so a binding textually nested in a block, `for`, or
        // `catch` scope is owned by its enclosing function. `let`/`const` and all
        // other kinds stay in the scope they were written in.
        let hoisted = matches!(
            kind,
            SymbolKind::Variable(VariableKind::Var) | SymbolKind::Function
        );
        let scope = if hoisted {
            self.value_hoist_scope(scope)
        } else {
            scope
        };
        let hoisted_identity = hoisted.then_some(HoistedDeclarationIdentity {
            scope,
            declaration,
            range,
            kind,
        });
        if let Some(identity) = hoisted_identity
            && let Some(symbol) = self.hoisted_declaration_symbols.get(&identity)
        {
            return *symbol;
        }
        let merge = self.scopes[scope.0 as usize]
            .values
            .get(name)
            .copied()
            .filter(|existing| {
                kind.occupies_value()
                    && self.symbols[existing.get() as usize]
                        .kind
                        .accepts_value_merge_from(kind)
            })
            .or_else(|| {
                self.scopes[scope.0 as usize]
                    .types
                    .get(name)
                    .copied()
                    .filter(|existing| {
                        kind.occupies_type()
                            && self.symbols[existing.get() as usize]
                                .kind
                                .accepts_type_merge_from(kind)
                    })
            });
        // TS2397: A global declaration in a script whose name collides with a
        // built-in global identifier (`globalThis` or `undefined`). Class and
        // interface declarations named `undefined` are excluded because they
        // carry their own specific diagnostics (TS2414, TS2427); no such
        // special diagnostic exists for `globalThis`, so all declaration kinds
        // are flagged. The check runs before the merge early-return so a
        // namespace named `undefined` or `globalThis` that merges with a
        // preceding class/enum/interface still emits C087 (undefinedTypeAssignment4).
        if !self.is_module
            && scope == self.module_scope
            && !(name == "undefined" && matches!(kind, SymbolKind::Class | SymbolKind::Interface))
            && matches!(name, "globalThis" | "undefined")
        {
            self.emit_with_message(
                DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL,
                range,
                format!("Declaration name conflicts with built-in global identifier '{name}'."),
            );
        }
        if let Some(existing) = merge {
            if kind.occupies_value() {
                self.scopes[scope.0 as usize]
                    .values
                    .entry(name.to_owned())
                    .or_insert(existing);
            }
            if kind.occupies_type() {
                self.scopes[scope.0 as usize]
                    .types
                    .entry(name.to_owned())
                    .or_insert(existing);
            }
            if let Some(identity) = hoisted_identity {
                self.hoisted_declaration_symbols.insert(identity, existing);
            }
            return existing;
        }
        let parent = self.scopes[scope.0 as usize].owner;
        let id = SymbolId(u32::try_from(self.symbols.len()).expect("symbol count fits in u32"));
        self.symbols.push(Symbol {
            name: name.to_owned(),
            kind,
            scope,
            declaration,
            range,
            parent,
        });
        self.symbol_types.push(self.types.any());
        self.overload_signatures.push(Vec::new());
        self.type_state.push(TypeState::Unresolved);

        let value_conflict = if kind.occupies_value() {
            self.insert_value(scope, name, id, kind)
        } else {
            None
        };
        let type_conflict = if kind.occupies_type() {
            self.insert_type(scope, name, id, kind)
        } else {
            None
        };
        if let Some(identity) = hoisted_identity {
            self.hoisted_declaration_symbols.insert(identity, id);
        }
        let conflict = value_conflict.or(type_conflict);
        if let Some(existing) = conflict {
            let existing_kind = self.symbols[existing.get() as usize].kind;
            if existing_kind == SymbolKind::Import && kind != SymbolKind::Import {
                // The local declaration shadows the import; the diagnostic is on the import.
                let import_range = self.symbols[existing.get() as usize].range;
                self.emit(
                    IMPORT_CONFLICTS_WITH_LOCAL,
                    import_range,
                    IMPORT_CONFLICTS_WITH_LOCAL_MESSAGE,
                );
                self.scopes[scope.0 as usize]
                    .values
                    .insert(name.to_owned(), id);
                self.scopes[scope.0 as usize]
                    .types
                    .insert(name.to_owned(), id);
            } else if kind == SymbolKind::Import {
                // A duplicate import conflicts with an existing local declaration.
                self.emit(
                    IMPORT_CONFLICTS_WITH_LOCAL,
                    range,
                    IMPORT_CONFLICTS_WITH_LOCAL_MESSAGE,
                );
            } else {
                self.emit(DUPLICATE_DECLARATION, range, DUPLICATE_MESSAGE);
            }
        }
        id
    }

    fn insert_value(
        &mut self,
        scope: ScopeId,
        name: &str,
        id: SymbolId,
        kind: SymbolKind,
    ) -> Option<SymbolId> {
        match self.scopes[scope.0 as usize].values.get(name) {
            None => {
                self.scopes[scope.0 as usize]
                    .values
                    .insert(name.to_owned(), id);
                None
            }
            Some(existing) => {
                let existing_kind = self.symbols[existing.get() as usize].kind;
                if existing_kind.accepts_value_merge_from(kind) {
                    None
                } else {
                    Some(*existing)
                }
            }
        }
    }

    fn insert_type(
        &mut self,
        scope: ScopeId,
        name: &str,
        id: SymbolId,
        kind: SymbolKind,
    ) -> Option<SymbolId> {
        match self.scopes[scope.0 as usize].types.get(name) {
            None => {
                self.scopes[scope.0 as usize]
                    .types
                    .insert(name.to_owned(), id);
                None
            }
            Some(existing) => {
                let existing_kind = self.symbols[existing.get() as usize].kind;
                if existing_kind.accepts_type_merge_from(kind) {
                    None
                } else {
                    Some(*existing)
                }
            }
        }
    }

    fn bind_statements(&mut self, statements: &'src [crate::syntax::Stmt], scope: ScopeId) {
        self.bind_statement_names_and_class_headers(statements, scope);
        self.resolve_statement_class_bounds(statements);
    }

    fn bind_statement_names_and_class_headers(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        scope: ScopeId,
    ) {
        for statement in statements {
            self.bind_statement(statement, scope);
        }
        for statement in statements {
            if let Some(class) = Self::statement_class(statement) {
                self.predeclare_class_header(class, scope);
            }
        }
    }

    fn resolve_statement_class_bounds(&mut self, statements: &'src [crate::syntax::Stmt]) {
        for statement in statements {
            if let Some(class) = Self::statement_class(statement) {
                self.resolve_predeclared_class_bounds(class);
            }
        }
    }

    fn statement_class(statement: &'src crate::syntax::Stmt) -> Option<&'src ClassDeclaration> {
        match statement.data() {
            Statement::Class(class) => Some(class),
            Statement::Declare(inner) => Self::statement_class(inner),
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => Self::statement_class(inner),
            Statement::Export(crate::syntax::ExportDeclaration::Default(default)) => {
                match &default.value {
                    crate::syntax::ExportDefaultValue::Class(class) => Some(class),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn predeclare_class_header(&mut self, class: &'src ClassDeclaration, parent: ScopeId) {
        let Some(name) = &class.name else {
            return;
        };
        let owner = self
            .class_declaration_symbols
            .get(&name.id())
            .copied()
            .expect("named class declaration has a symbol");
        let scope = self.new_scope(ScopeKind::Class, Some(parent));
        self.scopes[scope.0 as usize].strict = true;
        self.bind_type_parameter_names(class.type_parameters.as_ref(), scope);
        let parameters = self.bound_type_parameter_symbols(class.type_parameters.as_ref(), scope);
        self.types.declare_class(owner, parameters);
        self.set_scope_owner(scope, owner);
        let replaced = self.class_header_scopes.insert(name.id(), scope);
        debug_assert!(replaced.is_none());
    }

    fn resolve_predeclared_class_bounds(&mut self, class: &'src ClassDeclaration) {
        let Some(name) = &class.name else {
            return;
        };
        let Some(scope) = self.class_header_scopes.get(&name.id()).copied() else {
            return;
        };
        let owner = self.scopes[scope.0 as usize]
            .owner
            .expect("predeclared class scope has an owner");
        if !self.types.begin_class_bounds(owner) {
            return;
        }
        let bounds = self
            .signature_type_parameters(class.type_parameters.as_ref(), scope)
            .1;
        self.types.finish_class_bounds(owner, bounds);
    }

    fn bound_type_parameter_symbols(
        &self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        scope: ScopeId,
    ) -> Vec<SymbolId> {
        list.map(|list| {
            list.parameters
                .iter()
                .filter_map(|parameter| {
                    let name = self.identifier_text(&parameter.data().name);
                    self.scopes[scope.0 as usize]
                        .types
                        .get(name.as_ref())
                        .copied()
                })
                .collect()
        })
        .unwrap_or_default()
    }

    /// Pre-binds `var` and function names that occur beneath lexical child
    /// scopes. The traversal never enters a function body: its own call to this
    /// pass supplies the correct function hoist target.
    fn bind_hoisted_statements(&mut self, statements: &'src [crate::syntax::Stmt], scope: ScopeId) {
        for statement in statements {
            self.bind_hoisted_statement(statement, scope);
        }
    }

    fn bind_hoisted_statement(&mut self, statement: &'src crate::syntax::Stmt, scope: ScopeId) {
        match statement.data() {
            Statement::Variable(variable) if variable.kind == VariableKind::Var => {
                self.bind_variable(variable, scope, statement.id());
            }
            Statement::Function(function) => {
                if let Some(name) = &function.function.name {
                    self.declare(
                        &self.identifier_text(name),
                        SymbolKind::Function,
                        scope,
                        name.id(),
                        name.range(),
                    );
                }
            }
            Statement::Block(block) => {
                self.bind_hoisted_statements(&block.data().statements, scope)
            }
            Statement::If(statement) => {
                self.bind_hoisted_statement(&statement.consequent, scope);
                if let Some(alternate) = &statement.alternate {
                    self.bind_hoisted_statement(alternate, scope);
                }
            }
            Statement::Switch(statement) => {
                for case in &statement.cases {
                    self.bind_hoisted_statements(&case.data().consequent, scope);
                }
            }
            Statement::For(for_statement) => {
                if let Some(ForInitializer::Variable(variable)) = &for_statement.initializer
                    && variable.kind == VariableKind::Var
                {
                    self.bind_variable(variable, scope, NodeId::default());
                }
                self.bind_hoisted_statement(&for_statement.body, scope);
            }
            Statement::ForIn(for_statement) => {
                if let ForBinding::Variable(variable) = &for_statement.binding
                    && variable.kind == VariableKind::Var
                {
                    self.bind_variable(variable, scope, NodeId::default());
                }
                self.bind_hoisted_statement(&for_statement.body, scope);
            }
            Statement::ForOf(for_statement) => {
                if let ForBinding::Variable(variable) = &for_statement.binding
                    && variable.kind == VariableKind::Var
                {
                    self.bind_variable(variable, scope, NodeId::default());
                }
                self.bind_hoisted_statement(&for_statement.body, scope);
            }
            Statement::While(statement) => self.bind_hoisted_statement(&statement.body, scope),
            Statement::DoWhile(statement) => self.bind_hoisted_statement(&statement.body, scope),
            Statement::Try(statement) => {
                self.bind_hoisted_statements(&statement.block.data().statements, scope);
                if let Some(handler) = &statement.handler {
                    self.bind_hoisted_statements(&handler.data().body.data().statements, scope);
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.bind_hoisted_statements(&finalizer.data().statements, scope);
                }
            }
            Statement::With(with_statement) => {
                self.bind_hoisted_statement(&with_statement.body, scope)
            }
            Statement::Labeled(statement) => self.bind_hoisted_statement(&statement.body, scope),
            Statement::Namespace(_) => {}
            Statement::Declare(inner) => {
                let saved = self.ambient_binding;
                self.ambient_binding = true;
                self.bind_hoisted_statement(inner, scope);
                self.ambient_binding = saved;
            }
            Statement::Export(export) => match export {
                crate::syntax::ExportDeclaration::Named(
                    crate::syntax::ExportNamedDeclaration::Declaration(inner),
                ) => self.bind_hoisted_statement(inner, scope),
                crate::syntax::ExportDeclaration::Default(default)
                    if let crate::syntax::ExportDefaultValue::Function(function) =
                        &default.value
                        && let Some(name) = &function.name =>
                {
                    self.declare(
                        &self.identifier_text(name),
                        SymbolKind::Function,
                        scope,
                        statement.id(),
                        name.range(),
                    );
                }
                _ => {}
            },

            _ => {}
        }
    }

    fn bind_statement(&mut self, statement: &'src crate::syntax::Stmt, scope: ScopeId) {
        let declaration = statement.id();
        match statement.data() {
            Statement::Variable(variable) => self.bind_variable(variable, scope, declaration),
            Statement::Function(function) => {
                if let Some(name) = &function.function.name {
                    let symbol = self.declare(
                        &self.identifier_text(name),
                        SymbolKind::Function,
                        scope,
                        name.id(),
                        name.range(),
                    );
                    self.jsx_callables
                        .insert(symbol, JsxCallable::Function(&function.function));
                }
            }
            Statement::Class(class) => {
                if let Some(name) = &class.name {
                    let symbol = self.declare(
                        &self.identifier_text(name),
                        SymbolKind::Class,
                        scope,
                        declaration,
                        name.range(),
                    );
                    let replaced = self.class_declaration_symbols.insert(name.id(), symbol);
                    debug_assert!(replaced.is_none());
                }
            }
            Statement::Interface(interface) => self.bind_interface(interface, scope, declaration),
            Statement::TypeAlias(alias) => self.bind_type_alias(alias, scope, declaration),
            Statement::Enum(declaration_node) => {
                self.bind_enum(declaration_node, declaration, scope, false)
            }
            Statement::Namespace(namespace) => {
                self.bind_namespace(namespace, declaration, scope, scope, false, None);
            }
            Statement::Import(import) => self.bind_import(import, scope, declaration),
            Statement::ImportEquals(import) => {
                // The TypeScript baseline places TS2440 at the start of the
                // `import X = ...` statement, not on the local name alone.
                let symbol = self.declare(
                    &self.identifier_text(&import.local),
                    SymbolKind::Import,
                    scope,
                    declaration,
                    statement.range(),
                );
                if let crate::syntax::ExternalModuleReference::Qualified(_) = &import.reference {
                    self.import_equals_symbols.insert(declaration, symbol);
                }
            }
            Statement::Declare(inner) => {
                let saved = self.ambient_binding;
                self.ambient_binding = true;
                if let Some((declaration, declaration_id)) = enum_plan::enum_declaration(statement)
                {
                    self.bind_enum(declaration, declaration_id, scope, true);
                } else if let Statement::Namespace(namespace) = inner.data() {
                    self.bind_namespace(namespace, inner.id(), scope, scope, true, None);
                } else {
                    self.bind_statement(inner, scope);
                }
                self.ambient_binding = saved;
            }
            Statement::Export(export) => match export {
                crate::syntax::ExportDeclaration::Named(
                    crate::syntax::ExportNamedDeclaration::Declaration(inner),
                ) => self.bind_statement(inner, scope),
                crate::syntax::ExportDeclaration::Default(default) => match &default.value {
                    crate::syntax::ExportDefaultValue::Function(function)
                        if let Some(name) = &function.name =>
                    {
                        let symbol = self.declare(
                            &self.identifier_text(name),
                            SymbolKind::Function,
                            scope,
                            declaration,
                            name.range(),
                        );
                        self.jsx_callables
                            .insert(symbol, JsxCallable::Function(function));
                    }
                    crate::syntax::ExportDefaultValue::Class(class)
                        if let Some(name) = &class.name =>
                    {
                        let symbol = self.declare(
                            &self.identifier_text(name),
                            SymbolKind::Class,
                            scope,
                            declaration,
                            name.range(),
                        );
                        let replaced = self.class_declaration_symbols.insert(name.id(), symbol);
                        debug_assert!(replaced.is_none());
                    }
                    crate::syntax::ExportDefaultValue::Interface(interface) => {
                        self.bind_interface(interface, scope, declaration);
                    }
                    _ => {}
                },

                _ => {}
            },
            _ => {}
        }
    }

    fn bind_enum(
        &mut self,
        declaration: &'src crate::syntax::EnumDeclaration,
        declaration_id: NodeId,
        scope: ScopeId,
        ambient: bool,
    ) {
        let symbol = self.declare(
            &self.identifier_text(&declaration.name),
            SymbolKind::Enum,
            scope,
            declaration_id,
            declaration.name.range(),
        );
        let member_scope = if let Some(scope) = self.enum_member_scopes.get(&symbol) {
            *scope
        } else {
            let member_scope = self.new_scope(ScopeKind::Block, Some(scope));
            self.enum_member_scopes.insert(symbol, member_scope);
            member_scope
        };
        self.set_scope_owner(member_scope, symbol);
        for member in &declaration.members {
            let Some(name) = enum_plan::cook_member_name(self.source, &member.data().name) else {
                continue;
            };
            let member_symbol = self.declare(
                &name.to_utf8_lossy(),
                SymbolKind::EnumMember,
                member_scope,
                member.id(),
                member.range(),
            );
            self.enum_member_symbols.insert(member.id(), member_symbol);
            self.enum_member_symbols_by_name
                .entry(symbol)
                .or_default()
                .entry(name.clone())
                .or_insert(member_symbol);
            self.enum_member_names.insert(member.id(), name);
            let string_value = member
                .data()
                .initializer
                .as_deref()
                .and_then(|init| self.enum_member_string_value(init));
            self.symbol_types[member_symbol.get() as usize] =
                self.types.enum_member(symbol, member_symbol, string_value);
            self.type_state[member_symbol.get() as usize] =
                TypeState::Done(self.symbol_types[member_symbol.get() as usize]);
        }
        let numeric = declaration.members.iter().all(|member| {
            member
                .data()
                .initializer
                .as_deref()
                .is_none_or(is_numeric_enum_initializer)
        });
        match self.type_defs.get_mut(&symbol) {
            Some(TypeDef::Enum { numeric: existing }) => *existing &= numeric,
            None => {
                self.type_defs.insert(symbol, TypeDef::Enum { numeric });
            }
            Some(_) => unreachable!("enum symbol has an enum type definition"),
        }
        self.enum_declaration_symbols.insert(declaration_id, symbol);
        self.enum_declarations.push(EnumDeclarationBinding {
            declaration,
            declaration_id,
            symbol,
            ambient,
        });
    }

    fn bind_namespace(
        &mut self,
        declaration: &'src crate::syntax::NamespaceDeclaration,
        declaration_id: NodeId,
        scope: ScopeId,
        scope_parent: ScopeId,
        ambient: bool,
        parent: Option<SymbolId>,
    ) {
        if self.namespace_local_scopes.contains_key(&declaration_id) {
            return;
        }
        let (symbol, export_scope) = match &declaration.name {
            NamespaceName::Identifier { name, .. } => {
                let symbol = self.declare(
                    &self.identifier_text(name),
                    SymbolKind::Namespace,
                    scope,
                    declaration_id,
                    name.range(),
                );
                let export_scope = self
                    .namespace_export_scopes
                    .get(&symbol)
                    .copied()
                    .unwrap_or_else(|| {
                        let export_scope = self.new_scope(ScopeKind::Namespace, Some(scope_parent));
                        self.namespace_export_scopes.insert(symbol, export_scope);
                        export_scope
                    });
                (symbol, export_scope)
            }
            NamespaceName::StringLiteral(lit) => {
                let detached = self.new_scope(ScopeKind::Namespace, Some(scope));
                let key = self
                    .source
                    .token_text(lit.data().token())
                    .and_then(string_value)
                    .map(|value| value.to_utf8_lossy())
                    .unwrap_or_default();
                let symbol = self.declare(
                    &key,
                    SymbolKind::Namespace,
                    detached,
                    declaration_id,
                    lit.range(),
                );
                self.ambient_modules.entry(key).or_insert(symbol);
                let export_scope = self
                    .namespace_export_scopes
                    .get(&symbol)
                    .copied()
                    .unwrap_or_else(|| {
                        let export_scope = self.new_scope(ScopeKind::Namespace, Some(scope_parent));
                        self.namespace_export_scopes.insert(symbol, export_scope);
                        export_scope
                    });
                (symbol, export_scope)
            }
            NamespaceName::Global { range } => {
                let detached = self.new_scope(ScopeKind::Namespace, Some(scope));
                let symbol = self.declare(
                    "global",
                    SymbolKind::Namespace,
                    detached,
                    declaration_id,
                    *range,
                );
                let export_scope = self.global_scope;
                self.namespace_export_scopes.insert(symbol, export_scope);
                (symbol, export_scope)
            }
        };
        let local_scope = self.new_scope(ScopeKind::Function, Some(export_scope));
        self.namespace_local_scopes
            .insert(declaration_id, local_scope);
        self.namespace_local_of_symbol.insert(symbol, local_scope);
        self.namespace_declarations
            .push(NamespaceDeclarationBinding {
                declaration,
                declaration_id,
                symbol,
                export_scope,
                parent,
                ambient,
            });

        for statement in &declaration.body.data().statements {
            let _target =
                self.bind_namespace_member(statement, local_scope, export_scope, symbol, ambient);
            if let Some(class) = Self::statement_class(statement) {
                // Always predeclare the class header with `local_scope` as
                // parent so that both class bounds resolution and class body
                // resolution can see non-exported namespace siblings.  The
                // exported name itself is declared in `export_scope` by
                // `bind_namespace_member`; only the class body's lexical
                // parent must be `local_scope`.
                self.predeclare_class_header(class, local_scope);
            }
        }
        for statement in &declaration.body.data().statements {
            if let Some(class) = Self::statement_class(statement) {
                self.resolve_predeclared_class_bounds(class);
            }
        }
        for statement in &declaration.body.data().statements {
            let target = if ambient
                || matches!(
                    statement.data(),
                    Statement::Export(crate::syntax::ExportDeclaration::Named(
                        crate::syntax::ExportNamedDeclaration::Declaration(_)
                    ))
                )
                || self.is_dotted_namespace_tail(statement)
            {
                export_scope
            } else {
                local_scope
            };
            self.bind_hoisted_statement(statement, target);
        }
    }

    fn bind_namespace_member(
        &mut self,
        statement: &'src crate::syntax::Stmt,
        local_scope: ScopeId,
        export_scope: ScopeId,
        container: SymbolId,
        ambient: bool,
    ) -> ScopeId {
        let target = if ambient
            || matches!(
                statement.data(),
                Statement::Declare(_)
                    | Statement::Export(crate::syntax::ExportDeclaration::Named(
                        crate::syntax::ExportNamedDeclaration::Declaration(_)
                    ))
            )
            || self.is_dotted_namespace_tail(statement)
        {
            export_scope
        } else {
            local_scope
        };
        match statement.data() {
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => match inner.data() {
                Statement::Namespace(namespace) => self.bind_namespace(
                    namespace,
                    inner.id(),
                    target,
                    local_scope,
                    ambient,
                    Some(container),
                ),
                _ => self.bind_statement(inner, target),
            },
            Statement::Namespace(namespace)
                if ambient || self.is_dotted_namespace_tail(statement) =>
            {
                self.bind_namespace(
                    namespace,
                    statement.id(),
                    target,
                    local_scope,
                    ambient,
                    Some(container),
                );
            }
            Statement::Declare(inner) => match inner.data() {
                Statement::Namespace(namespace) => self.bind_namespace(
                    namespace,
                    inner.id(),
                    target,
                    local_scope,
                    true,
                    Some(container),
                ),
                _ => self.bind_statement(statement, target),
            },
            _ => self.bind_statement(statement, target),
        }
        target
    }

    fn is_dotted_namespace_tail(&self, statement: &crate::syntax::Stmt) -> bool {
        self.source.tokens().iter().any(|token| {
            token.kind() == TokenKind::Dot && token.range().start() == statement.range().start()
        })
    }

    fn bind_variable(
        &mut self,
        variable: &'src VariableDeclaration,
        scope: ScopeId,
        declaration: NodeId,
    ) {
        let track_uninit = !self.ambient_binding
            && declaration != NodeId::default()
            && matches!(variable.kind, VariableKind::Let | VariableKind::Var);
        for declarator in &variable.declarations {
            let symbols = self.bind_pattern(
                &declarator.data().binding,
                variable.kind,
                scope,
                declaration,
            );
            self.declarator_symbols
                .insert(declarator.id(), symbols.clone());
            if track_uninit && declarator.data().initializer.is_none() {
                for symbol in symbols {
                    self.uninitialized_variables.insert(symbol);
                }
            }
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &'src crate::syntax::Pattern,
        kind: VariableKind,
        scope: ScopeId,
        declaration: NodeId,
    ) -> Vec<SymbolId> {
        match pattern.data() {
            BindingPattern::Identifier(name) => {
                vec![self.declare(
                    &self.identifier_text(name),
                    SymbolKind::Variable(kind),
                    scope,
                    declaration,
                    name.range(),
                )]
            }
            BindingPattern::Object(object) => {
                let mut result = Vec::new();
                for property in &object.properties {
                    result.extend(self.bind_pattern(&property.binding, kind, scope, declaration));
                }
                result
            }
            BindingPattern::Array(array) => {
                let mut result = Vec::new();
                for element in &array.elements {
                    if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                        result.extend(self.bind_pattern(inner, kind, scope, declaration));
                    }
                }
                result
            }
            BindingPattern::Rest(rest) => {
                self.bind_pattern(&rest.argument, kind, scope, declaration)
            }
            BindingPattern::Assignment(assignment) => {
                self.bind_pattern(&assignment.left, kind, scope, declaration)
            }
            BindingPattern::Missing(_) => Vec::new(),
        }
    }

    fn bind_interface(
        &mut self,
        interface: &'src InterfaceDeclaration,
        scope: ScopeId,
        declaration: NodeId,
    ) {
        let id = self.declare(
            &self.identifier_text(&interface.name),
            SymbolKind::Interface,
            scope,
            declaration,
            interface.name.range(),
        );
        let type_scope = self.new_scope(ScopeKind::Block, Some(scope));
        self.bind_type_parameter_names(interface.type_parameters.as_ref(), type_scope);
        let parameters =
            self.bound_type_parameter_symbols(interface.type_parameters.as_ref(), type_scope);
        match self.type_defs.get(&id).copied() {
            Some(TypeDef::Interface {
                scope: canonical_scope,
                ..
            }) => {
                let canonical_parameters = self.types.class_type_parameters(id).to_vec();
                if canonical_parameters.len() == parameters.len() {
                    self.merge_interface_type_parameter_defaults(
                        interface.type_parameters.as_ref(),
                        canonical_scope,
                        &canonical_parameters,
                    );
                }
            }
            None if !parameters.is_empty() => self.types.declare_class(id, parameters),
            None | Some(_) => {}
        }
        self.set_scope_this_owner(type_scope, id);
        let member_scope = match self.interface_member_scopes.get(&id) {
            Some(existing) => *existing,
            None => {
                let member_scope = self.new_scope(ScopeKind::Class, Some(scope));
                self.interface_member_scopes.insert(id, member_scope);
                member_scope
            }
        };
        self.set_scope_owner(member_scope, id);
        for member in &interface.members {
            self.bind_interface_member(member, member_scope);
        }
        self.interface_merges.entry(id).or_default().push(interface);
        self.type_defs.entry(id).or_insert(TypeDef::Interface {
            scope: type_scope,
            type_parameters: interface.type_parameters.as_ref(),
        });
    }

    /// Declares a container member unless the same name is already bound in the
    /// member scope, in which case the existing symbol is reused. Duplicate
    /// member names therefore contribute one symbol, matching upstream's
    /// multi-declaration symbols, and this path never mints a new duplicate
    /// diagnostic.
    fn declare_member_unique(
        &mut self,
        name: &str,
        kind: SymbolKind,
        scope: ScopeId,
        declaration: NodeId,
        range: TextRange,
    ) -> SymbolId {
        if let Some(existing) = self.scopes[scope.0 as usize].values.get(name).copied() {
            return existing;
        }
        self.declare(name, kind, scope, declaration, range)
    }

    fn bind_interface_member(
        &mut self,
        member: &'src crate::syntax::TypeMemberNode,
        scope: ScopeId,
    ) {
        let range = |name: &crate::syntax::PropertyName| Self::property_name_range(name);
        let owner = self
            .scopes
            .get(scope.0 as usize)
            .and_then(|scope| scope.owner)
            .map(PropertyOwner::Member);
        match member.data() {
            TypeMember::Property(property) => {
                if let Some(name) = self.property_key(&property.name) {
                    self.declare_member_unique(
                        &name,
                        SymbolKind::Variable(VariableKind::Let),
                        scope,
                        member.id(),
                        range(&property.name),
                    );
                    if let (Some(owner), Some(bare)) =
                        (owner, Self::property_bare_range(&property.name))
                    {
                        self.record_property_anchor(
                            owner,
                            &name,
                            bare,
                            PropertyAnchorKind::Plain,
                            true,
                        );
                    }
                }
            }
            TypeMember::Method(method) => {
                if let Some(name) = self.property_key(&method.name) {
                    self.declare_member_unique(
                        &name,
                        SymbolKind::Function,
                        scope,
                        member.id(),
                        range(&method.name),
                    );
                    if let (Some(owner), Some(bare)) =
                        (owner, Self::property_bare_range(&method.name))
                    {
                        self.record_property_anchor(
                            owner,
                            &name,
                            bare,
                            PropertyAnchorKind::Plain,
                            true,
                        );
                    }
                }
                self.bind_signature_parameter_symbols(&method.function, scope);
            }
            TypeMember::Call(call) => {
                self.bind_signature_parameter_symbols(&call.function, scope);
            }
            TypeMember::Construct(construct) => {
                self.bind_signature_parameter_symbols(&construct.function.function, scope);
            }
            TypeMember::Index(index) => {
                let parameter_scope = self.new_scope(ScopeKind::Function, Some(scope));
                for parameter in &index.parameters {
                    let name = self.identifier_text(&parameter.name);
                    if name.as_ref() == "this" {
                        continue;
                    }
                    self.declare(
                        name.as_ref(),
                        SymbolKind::Parameter,
                        parameter_scope,
                        parameter.name.id(),
                        parameter.name.range(),
                    );
                }
            }
            TypeMember::Missing(_) => {}
        }
    }

    /// Binds the named parameters of one type-side signature (method, call,
    /// or construct) as `Parameter` symbols so upstream's bare
    /// `>s : Symbol(s, Decl(...))` rows render. The parameters live in a
    /// fresh function scope with no owner, keeping their rendered names
    /// unqualified under the container's member scope.
    fn bind_signature_parameter_symbols(&mut self, function: &'src FunctionType, parent: ScopeId) {
        let scope = self.new_scope(ScopeKind::Function, Some(parent));
        for parameter in &function.parameters {
            let name = self.identifier_text(&parameter.name);
            if name.as_ref() == "this" {
                continue;
            }
            self.declare(
                name.as_ref(),
                SymbolKind::Parameter,
                scope,
                parameter.name.id(),
                parameter.name.range(),
            );
        }
        self.bind_type_function_parameter_symbols(&function.return_type, scope);
    }

    /// Declares the parameter names of any function or constructor type a
    /// return type directly contains (`b(): (n: number) => void` renders
    /// `>n`), recursing through the containers that preserve function types.
    fn bind_type_function_parameter_symbols(&mut self, ty: &'src Ty, parent: ScopeId) {
        match ty.data() {
            TypeNode::Function(function) => {
                self.bind_signature_parameter_symbols(function, parent);
            }
            TypeNode::Constructor(constructor) => {
                self.bind_signature_parameter_symbols(&constructor.function, parent);
            }
            TypeNode::Parenthesized(inner) => {
                self.bind_type_function_parameter_symbols(inner, parent);
            }
            TypeNode::Union(members) | TypeNode::Intersection(members) => {
                for member in members {
                    self.bind_type_function_parameter_symbols(member, parent);
                }
            }
            TypeNode::Keyword(_)
            | TypeNode::Infer(_)
            | TypeNode::Literal(_)
            | TypeNode::Reference(_)
            | TypeNode::Array(_)
            | TypeNode::Tuple(_)
            | TypeNode::Object(_)
            | TypeNode::Query(_)
            | TypeNode::Operator { .. }
            | TypeNode::IndexedAccess(_)
            | TypeNode::Conditional(_)
            | TypeNode::Mapped(_)
            | TypeNode::Import(_)
            | TypeNode::TemplateLiteral(_)
            | TypeNode::This
            | TypeNode::Predicate(_)
            | TypeNode::Missing(_) => {}
        }
    }

    /// Whether a constructor parameter declares a parameter property: a plain
    /// identifier binding carrying an accessibility modifier or `readonly`.
    fn is_parameter_property(&self, parameter: &'src crate::syntax::ParameterNode) -> bool {
        let data = parameter.data();
        matches!(data.binding.data(), BindingPattern::Identifier(_))
            && (data.modifiers.accessibility.is_some() || data.modifiers.is_readonly)
    }

    /// Binds a constructor parameter property as a class member symbol so its
    /// qualified name and declaration anchor match upstream (`C.x`). The same
    /// symbol backs the `name` binding inside the constructor body, so a bare
    /// use of the property resolves through the member symbol. Plain
    /// parameters keep their unqualified function-scope binding.
    fn resolve_parameter_property(
        &mut self,
        parameter: &'src crate::syntax::ParameterNode,
        ctor_scope: ScopeId,
        class_scope: ScopeId,
    ) {
        let data = parameter.data();
        self.resolve_unsupported_legacy_decorators(
            &data.decorators,
            PARAMETER_DECORATOR_NOT_SUPPORTED,
            PARAMETER_DECORATOR_NOT_SUPPORTED_MESSAGE,
            ctor_scope,
        );
        let Some(owner) = self.scopes[class_scope.0 as usize].owner else {
            self.resolve_parameter(parameter, ctor_scope);
            return;
        };
        let member_scope = match self.class_member_scopes.get(&owner) {
            Some(member_scope) => *member_scope,
            None => {
                self.resolve_parameter(parameter, ctor_scope);
                return;
            }
        };
        let BindingPattern::Identifier(identifier) = data.binding.data() else {
            self.resolve_parameter(parameter, ctor_scope);
            return;
        };
        let name = self.identifier_text(identifier).into_owned();
        let symbol = self.declare_member_unique(
            &name,
            SymbolKind::Variable(VariableKind::Let),
            member_scope,
            parameter.id(),
            identifier.range(),
        );
        self.scopes[ctor_scope.0 as usize]
            .values
            .entry(name)
            .or_insert(symbol);
        if let Some(annotation) = &data.type_annotation {
            self.resolve_type(&annotation.data().type_node, ctor_scope);
        }
        if let Some(initializer) = &data.initializer {
            self.resolve_expr(initializer, ctor_scope);
        }
    }

    fn merge_interface_type_parameter_defaults(
        &mut self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        canonical_scope: ScopeId,
        canonical_parameters: &[SymbolId],
    ) {
        let Some(list) = list else {
            return;
        };
        for (&symbol, parameter) in canonical_parameters.iter().zip(&list.parameters) {
            let Some(node) = parameter.data().default.as_deref() else {
                continue;
            };
            self.type_parameter_defaults.entry(symbol).or_insert(
                TypeParameterDefaultState::Unresolved {
                    node,
                    scope: canonical_scope,
                },
            );
        }
    }

    fn bind_type_alias(
        &mut self,
        alias: &'src TypeAliasDeclaration,
        scope: ScopeId,
        declaration: NodeId,
    ) {
        let id = self.declare(
            &self.identifier_text(&alias.name),
            SymbolKind::TypeAlias,
            scope,
            declaration,
            alias.name.range(),
        );
        let type_scope = self.new_scope(ScopeKind::Block, Some(scope));
        self.bind_type_parameter_names(alias.type_parameters.as_ref(), type_scope);
        let parameters =
            self.bound_type_parameter_symbols(alias.type_parameters.as_ref(), type_scope);
        self.types.declare_alias(id, parameters);
        self.type_defs.insert(
            id,
            TypeDef::Alias {
                scope: type_scope,
                type_parameters: alias.type_parameters.as_ref(),
                node: &alias.type_node,
            },
        );
    }

    fn bind_import(
        &mut self,
        import: &'src crate::syntax::ImportDeclaration,
        scope: ScopeId,
        declaration: NodeId,
    ) {
        let Some(clause) = &import.clause else {
            return;
        };
        if let Some(default) = &clause.default {
            self.declare(
                &self.identifier_text(default),
                SymbolKind::Import,
                scope,
                declaration,
                default.range(),
            );
        }
        match &clause.binding {
            Some(ImportBinding::Namespace(name)) => {
                self.declare(
                    &self.identifier_text(name),
                    SymbolKind::Import,
                    scope,
                    declaration,
                    name.range(),
                );
            }
            Some(ImportBinding::Named(specifiers)) => {
                for specifier in specifiers {
                    let local = &specifier.data().local;
                    self.declare(
                        &self.identifier_text(local),
                        SymbolKind::Import,
                        scope,
                        declaration,
                        local.range(),
                    );
                }
            }
            None => {}
        }
    }

    // -- reference resolution and assignability --------------------------------

    fn build_import_equals_targets(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        scope: ScopeId,
    ) {
        for statement in statements {
            self.build_import_equals_target_statement(statement, scope);
        }
    }

    fn build_import_equals_target_statement(
        &mut self,
        statement: &'src crate::syntax::Stmt,
        scope: ScopeId,
    ) {
        match statement.data() {
            Statement::ImportEquals(import) => {
                if let crate::syntax::ExternalModuleReference::Qualified(name) = &import.reference {
                    self.resolve_qualified_import_equals(statement.id(), name, scope);
                }
            }
            Statement::Namespace(namespace) => {
                let child = self
                    .namespace_local_scopes
                    .get(&statement.id())
                    .copied()
                    .unwrap_or(scope);
                self.build_import_equals_targets(&namespace.body.data().statements, child);
            }
            Statement::Declare(inner) => {
                self.build_import_equals_target_statement(inner, scope);
            }
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => {
                self.build_import_equals_target_statement(inner, scope);
            }
            _ => {}
        }
    }

    fn resolve_statements(&mut self, statements: &'src [crate::syntax::Stmt], scope: ScopeId) {
        self.publish_statement_class_shapes(statements, scope);
        self.check_bound_statements(statements, scope);
    }

    fn publish_statement_class_shapes(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        scope: ScopeId,
    ) {
        for statement in statements {
            if let Some(class) = Self::statement_class(statement) {
                self.publish_predeclared_class_shape(class, scope);
            }
        }
    }

    fn check_bound_statements(&mut self, statements: &'src [crate::syntax::Stmt], scope: ScopeId) {
        self.inventory_statement_writes(statements, scope);
        self.check_function_overload_order(statements, scope);
        for statement in statements {
            self.resolve_statement(statement, scope);
        }
    }

    fn inventory_statement_writes(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        scope: ScopeId,
    ) {
        let mut inventory = WriteInventory {
            root_scope: scope,
            shadow_frames: Vec::new(),
        };
        self.inventory_statement_list_writes(statements, &mut inventory);
    }

    fn inventory_statement_list_writes(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        inventory: &mut WriteInventory,
    ) {
        for statement in statements {
            self.inventory_statement_write(statement, inventory);
        }
    }

    fn inventory_lexical_statement_list_writes(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        inventory: &mut WriteInventory,
    ) {
        let mut names = HashSet::new();
        self.collect_direct_write_lexicals(statements, &mut names);
        inventory.shadow_frames.push(names);
        self.inventory_statement_list_writes(statements, inventory);
        inventory.shadow_frames.pop();
    }

    fn inventory_hoisted_lexical_statement_list_writes(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        inventory: &mut WriteInventory,
    ) {
        let mut names = HashSet::new();
        self.collect_direct_write_lexicals(statements, &mut names);
        self.collect_hoisted_write_names(statements, &mut names);
        inventory.shadow_frames.push(names);
        self.inventory_statement_list_writes(statements, inventory);
        inventory.shadow_frames.pop();
    }

    fn inventory_function_like_writes(
        &mut self,
        function: &'src FunctionLike,
        local_name: Option<&'src IdentifierNode>,
        inventory: &mut WriteInventory,
    ) {
        for decorator in &function.decorators {
            self.inventory_expression_writes(&decorator.data().expression, inventory);
        }
        self.inventory_parameter_decorator_writes(&function.parameters, inventory);
        let body = match &function.body {
            Some(FunctionBody::Block(block)) => WriteFunctionBody::Block(&block.data().statements),
            Some(FunctionBody::Expression(expression)) => WriteFunctionBody::Expression(expression),
            Some(FunctionBody::Missing(_)) | None => WriteFunctionBody::Missing,
        };
        self.inventory_nested_function_writes(&function.parameters, local_name, body, inventory);
    }

    fn inventory_arrow_writes(
        &mut self,
        arrow: &'src ArrowFunction,
        inventory: &mut WriteInventory,
    ) {
        self.inventory_parameter_decorator_writes(&arrow.parameters, inventory);
        let body = match &arrow.body {
            FunctionBody::Block(block) => WriteFunctionBody::Block(&block.data().statements),
            FunctionBody::Expression(expression) => WriteFunctionBody::Expression(expression),
            FunctionBody::Missing(_) => WriteFunctionBody::Missing,
        };
        self.inventory_nested_function_writes(&arrow.parameters, None, body, inventory);
    }

    fn inventory_parameter_decorator_writes(
        &mut self,
        parameters: &'src [ParameterNode],
        inventory: &mut WriteInventory,
    ) {
        for parameter in parameters {
            for decorator in &parameter.data().decorators {
                self.inventory_expression_writes(&decorator.data().expression, inventory);
            }
        }
    }

    fn inventory_nested_function_writes(
        &mut self,
        parameters: &'src [ParameterNode],
        local_name: Option<&'src IdentifierNode>,
        body: WriteFunctionBody<'src>,
        inventory: &mut WriteInventory,
    ) {
        let mut parameter_names = HashSet::new();
        if let Some(name) = local_name {
            parameter_names.insert(self.identifier_text(name).into_owned());
        }
        for parameter in parameters {
            self.collect_write_binding_names(&parameter.data().binding, &mut parameter_names);
        }

        inventory.shadow_frames.push(parameter_names);
        for parameter in parameters {
            let data = parameter.data();
            self.inventory_binding_pattern_defaults(&data.binding, inventory);
            if let Some(initializer) = &data.initializer {
                self.inventory_expression_writes(initializer, inventory);
            }
        }

        match body {
            WriteFunctionBody::Block(statements) => {
                self.inventory_hoisted_lexical_statement_list_writes(statements, inventory);
            }
            WriteFunctionBody::Expression(expression) => {
                self.inventory_expression_writes(expression, inventory);
            }
            WriteFunctionBody::Missing => {}
        }
        inventory.shadow_frames.pop();
    }

    fn inventory_property_name_writes(
        &mut self,
        name: &'src PropertyName,
        inventory: &mut WriteInventory,
    ) {
        if let PropertyName::Computed(expression) = name {
            self.inventory_expression_writes(expression, inventory);
        }
    }

    fn inventory_class_writes(
        &mut self,
        class: &'src ClassDeclaration,
        local_name: Option<&'src IdentifierNode>,
        inventory: &mut WriteInventory,
    ) {
        for decorator in &class.decorators {
            self.inventory_expression_writes(&decorator.data().expression, inventory);
        }
        if let Some(name) = local_name {
            inventory
                .shadow_frames
                .push(HashSet::from([self.identifier_text(name).into_owned()]));
        }
        if let Some(heritage) = &class.extends {
            self.inventory_expression_writes(&heritage.expression, inventory);
        }
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(constructor) => {
                    for decorator in &constructor.decorators {
                        self.inventory_expression_writes(&decorator.data().expression, inventory);
                    }
                    self.inventory_parameter_decorator_writes(&constructor.parameters, inventory);
                    self.inventory_nested_function_writes(
                        &constructor.parameters,
                        None,
                        WriteFunctionBody::Block(&constructor.body.data().statements),
                        inventory,
                    );
                }
                ClassMember::Method(method) => {
                    self.inventory_property_name_writes(&method.name, inventory);
                    self.inventory_function_like_writes(&method.function, None, inventory);
                }
                ClassMember::Property(property) => {
                    for decorator in &property.decorators {
                        self.inventory_expression_writes(&decorator.data().expression, inventory);
                    }
                    self.inventory_property_name_writes(&property.name, inventory);
                    if let Some(initializer) = &property.initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
                ClassMember::AutoAccessor(accessor) => {
                    for decorator in &accessor.decorators {
                        self.inventory_expression_writes(&decorator.data().expression, inventory);
                    }
                    self.inventory_property_name_writes(&accessor.name, inventory);
                    if let Some(initializer) = &accessor.initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
                ClassMember::StaticBlock(block) => {
                    self.inventory_hoisted_lexical_statement_list_writes(
                        &block.data().statements,
                        inventory,
                    );
                }
                ClassMember::IndexSignature(_) | ClassMember::Missing(_) => {}
            }
        }
        if local_name.is_some() {
            inventory.shadow_frames.pop();
        }
    }

    fn inventory_namespace_writes(
        &mut self,
        namespace: &'src crate::syntax::NamespaceDeclaration,
        inventory: &mut WriteInventory,
    ) {
        self.inventory_hoisted_lexical_statement_list_writes(
            &namespace.body.data().statements,
            inventory,
        );
    }

    fn inventory_jsx_attributes_writes(
        &mut self,
        attributes: &'src [JsxAttributeItem],
        inventory: &mut WriteInventory,
    ) {
        for attribute in attributes {
            match attribute {
                JsxAttributeItem::Attribute(attribute) => {
                    if let Some(JsxAttributeInitializer::Expression(container)) =
                        &attribute.data().initializer
                        && let Some(expression) = &container.data().expression
                    {
                        self.inventory_expression_writes(expression, inventory);
                    }
                }
                JsxAttributeItem::Spread(spread) => {
                    self.inventory_expression_writes(&spread.data().expression, inventory);
                }
            }
        }
    }

    fn inventory_jsx_children_writes(
        &mut self,
        children: &'src [JsxChild],
        inventory: &mut WriteInventory,
    ) {
        for child in children {
            match child {
                JsxChild::ExpressionContainer(container) => {
                    if let Some(expression) = &container.data().expression {
                        self.inventory_expression_writes(expression, inventory);
                    }
                }
                JsxChild::Spread(spread) => {
                    self.inventory_expression_writes(&spread.data().expression, inventory);
                }
                JsxChild::Element(expression) => {
                    self.inventory_expression_writes(expression, inventory);
                }
                JsxChild::Text(_) => {}
            }
        }
    }

    fn inventory_statement_write(
        &mut self,
        statement: &'src crate::syntax::Stmt,
        inventory: &mut WriteInventory,
    ) {
        match statement.data() {
            Statement::Variable(variable) => {
                for declarator in &variable.declarations {
                    self.inventory_binding_pattern_defaults(&declarator.data().binding, inventory);
                    if let Some(initializer) = &declarator.data().initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
            }
            Statement::Function(function) => {
                self.inventory_function_like_writes(&function.function, None, inventory);
            }
            Statement::Class(class) => {
                self.inventory_class_writes(class, None, inventory);
            }
            Statement::Enum(declaration) => {
                for member in &declaration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.inventory_expression_writes(initializer, inventory);
                    }
                }
            }
            Statement::Namespace(namespace) => {
                self.inventory_namespace_writes(namespace, inventory);
            }
            Statement::Block(block) => {
                self.inventory_lexical_statement_list_writes(&block.data().statements, inventory);
            }
            Statement::Expression(statement) => {
                self.inventory_expression_writes(&statement.expression, inventory);
            }
            Statement::If(statement) => {
                self.inventory_expression_writes(&statement.test, inventory);
                self.inventory_statement_write(&statement.consequent, inventory);
                if let Some(alternate) = &statement.alternate {
                    self.inventory_statement_write(alternate, inventory);
                }
            }
            Statement::Switch(statement) => {
                self.inventory_expression_writes(&statement.discriminant, inventory);
                let mut names = HashSet::new();
                for case in &statement.cases {
                    self.collect_direct_write_lexicals(&case.data().consequent, &mut names);
                }
                inventory.shadow_frames.push(names);
                for case in &statement.cases {
                    if let Some(test) = &case.data().test {
                        self.inventory_expression_writes(test, inventory);
                    }
                    self.inventory_statement_list_writes(&case.data().consequent, inventory);
                }
                inventory.shadow_frames.pop();
            }
            Statement::For(for_statement) => {
                let mut names = HashSet::new();
                if let Some(ForInitializer::Variable(variable)) = &for_statement.initializer
                    && variable.kind != VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, &mut names);
                    }
                }
                inventory.shadow_frames.push(names);
                if let Some(initializer) = &for_statement.initializer {
                    match initializer {
                        ForInitializer::Variable(variable) => {
                            for declarator in &variable.declarations {
                                self.inventory_binding_pattern_defaults(
                                    &declarator.data().binding,
                                    inventory,
                                );
                                if let Some(initializer) = &declarator.data().initializer {
                                    self.inventory_expression_writes(initializer, inventory);
                                }
                            }
                        }
                        ForInitializer::Expression(expression) => {
                            self.inventory_expression_writes(expression, inventory);
                        }
                    }
                }
                if let Some(test) = &for_statement.test {
                    self.inventory_expression_writes(test, inventory);
                }
                if let Some(update) = &for_statement.update {
                    self.inventory_expression_writes(update, inventory);
                }
                self.inventory_statement_write(&for_statement.body, inventory);
                inventory.shadow_frames.pop();
            }
            Statement::ForIn(for_statement) => {
                let mut names = HashSet::new();
                if let ForBinding::Variable(variable) = &for_statement.binding
                    && variable.kind != VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, &mut names);
                    }
                }
                inventory.shadow_frames.push(names);
                if let ForBinding::Target(target) = &for_statement.binding {
                    self.inventory_assignment_target_writes(target, inventory);
                }
                self.inventory_expression_writes(&for_statement.object, inventory);
                self.inventory_statement_write(&for_statement.body, inventory);
                inventory.shadow_frames.pop();
            }
            Statement::ForOf(for_statement) => {
                let mut names = HashSet::new();
                if let ForBinding::Variable(variable) = &for_statement.binding
                    && variable.kind != VariableKind::Var
                {
                    for declarator in &variable.declarations {
                        self.collect_write_binding_names(&declarator.data().binding, &mut names);
                    }
                }
                inventory.shadow_frames.push(names);
                if let ForBinding::Target(target) = &for_statement.binding {
                    self.inventory_assignment_target_writes(target, inventory);
                }
                self.inventory_expression_writes(&for_statement.iterable, inventory);
                self.inventory_statement_write(&for_statement.body, inventory);
                inventory.shadow_frames.pop();
            }
            Statement::While(statement) => {
                self.inventory_expression_writes(&statement.test, inventory);
                self.inventory_statement_write(&statement.body, inventory);
            }
            Statement::DoWhile(statement) => {
                self.inventory_statement_write(&statement.body, inventory);
                self.inventory_expression_writes(&statement.test, inventory);
            }
            Statement::Try(statement) => {
                self.inventory_lexical_statement_list_writes(
                    &statement.block.data().statements,
                    inventory,
                );
                if let Some(handler) = &statement.handler {
                    let mut names = HashSet::new();
                    if let Some(binding) = &handler.data().binding {
                        self.collect_write_binding_names(binding, &mut names);
                    }
                    inventory.shadow_frames.push(names);
                    self.inventory_lexical_statement_list_writes(
                        &handler.data().body.data().statements,
                        inventory,
                    );
                    inventory.shadow_frames.pop();
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.inventory_lexical_statement_list_writes(
                        &finalizer.data().statements,
                        inventory,
                    );
                }
            }
            Statement::With(with_statement) => {
                self.inventory_expression_writes(&with_statement.object, inventory);
                self.inventory_statement_write(&with_statement.body, inventory);
            }
            Statement::Labeled(statement) => {
                self.inventory_statement_write(&statement.body, inventory);
            }
            Statement::Return(return_statement) => {
                if let Some(argument) = &return_statement.argument {
                    self.inventory_expression_writes(argument, inventory);
                }
            }
            Statement::Throw(statement) => {
                self.inventory_expression_writes(&statement.argument, inventory);
            }
            Statement::Declare(inner) => self.inventory_statement_write(inner, inventory),
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => self.inventory_statement_write(inner, inventory),
            Statement::Export(crate::syntax::ExportDeclaration::Default(default)) => {
                match &default.value {
                    crate::syntax::ExportDefaultValue::Function(function) => {
                        self.inventory_function_like_writes(function, None, inventory);
                    }
                    crate::syntax::ExportDefaultValue::Class(class) => {
                        self.inventory_class_writes(class, None, inventory);
                    }
                    crate::syntax::ExportDefaultValue::Expression(expression) => {
                        self.inventory_expression_writes(expression, inventory);
                    }
                    _ => {}
                }
            }
            Statement::Export(crate::syntax::ExportDeclaration::Assignment(expression)) => {
                self.inventory_expression_writes(expression, inventory);
            }
            _ => {}
        }
    }

    fn inventory_expression_writes(
        &mut self,
        expression: &'src Expr,
        inventory: &mut WriteInventory,
    ) {
        match expression.data() {
            Expression::Template(template) => {
                for expression in &template.expressions {
                    self.inventory_expression_writes(expression, inventory);
                }
            }
            Expression::TaggedTemplate(tagged) => {
                self.inventory_expression_writes(&tagged.tag, inventory);
                for expression in &tagged.template.expressions {
                    self.inventory_expression_writes(expression, inventory);
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(expression) => {
                            self.inventory_expression_writes(expression, inventory)
                        }
                        ArrayElement::Spread(spread) => {
                            self.inventory_expression_writes(&spread.argument, inventory)
                        }
                        _ => {}
                    }
                }
            }
            Expression::Object(object) => {
                for member in &object.members {
                    match member.data() {
                        ObjectMember::Property(property) => {
                            self.inventory_property_name_writes(&property.name, inventory);
                            self.inventory_expression_writes(&property.value, inventory);
                        }
                        ObjectMember::Method(method) => {
                            self.inventory_property_name_writes(&method.name, inventory);
                            self.inventory_function_like_writes(&method.function, None, inventory);
                        }
                        ObjectMember::Spread(spread) => {
                            self.inventory_expression_writes(&spread.argument, inventory)
                        }
                        ObjectMember::Missing(_) => {}
                    }
                }
            }
            Expression::Call(call) => {
                self.inventory_expression_writes(&call.callee, inventory);
                for argument in &call.arguments {
                    match argument {
                        CallArgument::Expression(expression) => {
                            self.inventory_expression_writes(expression, inventory)
                        }
                        CallArgument::Spread(spread) => {
                            self.inventory_expression_writes(&spread.argument, inventory)
                        }
                        CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::Member(member) => {
                self.inventory_expression_writes(&member.object, inventory);
                if let MemberProperty::Computed(property) = &member.property {
                    self.inventory_expression_writes(property, inventory);
                }
            }
            Expression::New(new) => {
                self.inventory_expression_writes(&new.callee, inventory);
                for argument in &new.arguments {
                    match argument {
                        CallArgument::Expression(expression) => {
                            self.inventory_expression_writes(expression, inventory)
                        }
                        CallArgument::Spread(spread) => {
                            self.inventory_expression_writes(&spread.argument, inventory)
                        }
                        CallArgument::Missing(_) => {}
                    }
                }
            }
            Expression::Await(awaited) => {
                self.inventory_expression_writes(&awaited.argument, inventory)
            }
            Expression::Yield(yielded) => {
                if let Some(argument) = &yielded.argument {
                    self.inventory_expression_writes(argument, inventory);
                }
            }
            Expression::Unary(unary) => {
                self.inventory_expression_writes(&unary.argument, inventory);
            }
            Expression::Update(update) => {
                self.inventory_assignment_target_writes(&update.argument, inventory);
            }
            Expression::Binary(binary) => {
                self.inventory_expression_writes(&binary.left, inventory);
                self.inventory_expression_writes(&binary.right, inventory);
            }
            Expression::Logical(logical) => {
                self.inventory_expression_writes(&logical.left, inventory);
                self.inventory_expression_writes(&logical.right, inventory);
            }
            Expression::Conditional(conditional) => {
                self.inventory_expression_writes(&conditional.test, inventory);
                self.inventory_expression_writes(&conditional.consequent, inventory);
                self.inventory_expression_writes(&conditional.alternate, inventory);
            }
            Expression::Assignment(assignment) => {
                self.inventory_assignment_target_writes(&assignment.left, inventory);
                self.inventory_expression_writes(&assignment.right, inventory);
            }
            Expression::Sequence(sequence) => {
                for expression in &sequence.expressions {
                    self.inventory_expression_writes(expression, inventory);
                }
            }
            Expression::Parenthesized(expression) => {
                self.inventory_expression_writes(expression, inventory)
            }
            Expression::As(expression) => {
                self.inventory_expression_writes(&expression.expression, inventory)
            }
            Expression::Satisfies(expression) => {
                self.inventory_expression_writes(&expression.expression, inventory)
            }
            Expression::TypeAssertion(expression) => {
                self.inventory_expression_writes(&expression.expression, inventory)
            }
            Expression::NonNull(expression) => {
                self.inventory_expression_writes(&expression.expression, inventory)
            }
            Expression::Import(import) => {
                self.inventory_expression_writes(&import.source, inventory);
                if let Some(options) = &import.options {
                    self.inventory_expression_writes(options, inventory);
                }
            }
            Expression::Function(function) => {
                self.inventory_function_like_writes(
                    &function.function,
                    function.function.name.as_ref(),
                    inventory,
                );
            }
            Expression::Class(class) => {
                self.inventory_class_writes(&class.class, class.class.name.as_ref(), inventory);
            }
            Expression::Arrow(arrow) => {
                self.inventory_arrow_writes(arrow, inventory);
            }
            Expression::JsxElement(element) => {
                self.inventory_jsx_attributes_writes(&element.opening.data().attributes, inventory);
                self.inventory_jsx_children_writes(&element.children, inventory);
            }
            Expression::JsxSelfClosingElement(element) => {
                self.inventory_jsx_attributes_writes(&element.attributes, inventory);
            }
            Expression::JsxFragment(fragment) => {
                self.inventory_jsx_children_writes(&fragment.children, inventory);
            }
            _ => {}
        }
    }

    fn check_function_overload_order(
        &mut self,
        statements: &'src [crate::syntax::Stmt],
        scope: ScopeId,
    ) {
        if self.is_declaration_file || self.ambient_stack.last().copied().unwrap_or(false) {
            return;
        }
        let kind = self.scopes[scope.0 as usize].kind;
        let is_namespace_body = kind == ScopeKind::Function
            && self
                .active_namespace_declarations
                .last()
                .and_then(|declaration| self.namespace_local_scopes.get(declaration))
                .is_some_and(|namespace_scope| *namespace_scope == scope);
        if !matches!(
            kind,
            ScopeKind::Global | ScopeKind::Module | ScopeKind::Namespace | ScopeKind::Block
        ) && !is_namespace_body
        {
            return;
        }
        for (index, statement) in statements.iter().enumerate() {
            let Some(current) = Self::overload_signature(statement) else {
                continue;
            };
            let Some(current_name) = current.name.as_ref() else {
                continue;
            };
            let missing = |this: &mut Self| {
                this.emit(
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION,
                    current_name.range(),
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE,
                );
                if this.no_implicit_any && current.return_type.is_none() {
                    this.emit(
                        MISSING_METHOD_RETURN_TYPE,
                        current_name.range(),
                        MISSING_METHOD_RETURN_TYPE_MESSAGE,
                    );
                }
            };
            let Some(next) = statements.get(index + 1) else {
                missing(self);
                continue;
            };
            let Some(next_function) = Self::statement_function(next) else {
                missing(self);
                continue;
            };
            let Some(next_name) = next_function.name.as_ref() else {
                missing(self);
                continue;
            };
            if self.identifier_text(current_name) == self.identifier_text(next_name) {
                continue;
            }
            if next_function.body.is_none() {
                missing(self);
                continue;
            }
            if self.no_implicit_any && current.return_type.is_none() {
                self.emit(
                    MISSING_METHOD_RETURN_TYPE,
                    current_name.range(),
                    MISSING_METHOD_RETURN_TYPE_MESSAGE,
                );
            }
            self.emit(
                FUNCTION_IMPLEMENTATION_WRONG_NAME,
                next_name.range(),
                FUNCTION_IMPLEMENTATION_WRONG_NAME_MESSAGE,
            );
        }
    }

    fn overload_signature(statement: &'src crate::syntax::Stmt) -> Option<&'src FunctionLike> {
        let function = match statement.data() {
            Statement::Function(function) => &function.function,
            // `declare function` overloads are ambient and do not require an implementation.
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => match inner.data() {
                Statement::Function(function) => &function.function,
                _ => return None,
            },
            Statement::Export(crate::syntax::ExportDeclaration::Default(export)) => {
                match &export.value {
                    crate::syntax::ExportDefaultValue::Function(function) => function,
                    _ => return None,
                }
            }
            _ => return None,
        };
        (function.body.is_none() && function.name.is_some()).then_some(function)
    }

    fn statement_function(statement: &'src crate::syntax::Stmt) -> Option<&'src FunctionLike> {
        match statement.data() {
            Statement::Function(function) => Some(&function.function),
            Statement::Declare(inner) => match inner.data() {
                Statement::Function(function) => Some(&function.function),
                _ => None,
            },
            Statement::Export(crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            )) => match inner.data() {
                Statement::Function(function) => Some(&function.function),
                _ => None,
            },
            Statement::Export(crate::syntax::ExportDeclaration::Default(export)) => {
                match &export.value {
                    crate::syntax::ExportDefaultValue::Function(function) => Some(function),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn resolve_statement(&mut self, statement: &'src crate::syntax::Stmt, scope: ScopeId) {
        match statement.data() {
            Statement::Variable(variable) => self.resolve_variable(variable, scope, true),
            Statement::Function(function) => {
                if self.es5 && self.scopes[scope.0 as usize].strict {
                    match self.scopes[scope.0 as usize].kind {
                        ScopeKind::Block | ScopeKind::For | ScopeKind::Catch | ScopeKind::With => {
                            let range = function
                                .function
                                .name
                                .as_ref()
                                .map(|name| name.range())
                                .unwrap_or_else(|| statement.range());
                            self.emit(
                                FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT,
                                range,
                                FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT_MESSAGE,
                            );
                        }
                        _ => {}
                    }
                }
                let ambient = self.ambient_stack.last().copied().unwrap_or(false);
                if ambient && function.function.body.is_some() {
                    let range = function
                        .function
                        .body
                        .as_ref()
                        .map(|body| match body {
                            crate::syntax::FunctionBody::Block(block) => block.range(),
                            crate::syntax::FunctionBody::Expression(expression) => {
                                expression.range()
                            }
                            crate::syntax::FunctionBody::Missing(_) => function
                                .function
                                .name
                                .as_ref()
                                .map(|name| name.range())
                                .unwrap_or_else(|| statement.range()),
                        })
                        .unwrap_or_else(|| statement.range());
                    self.emit(
                        AMBIENT_IMPLEMENTATION,
                        range,
                        AMBIENT_IMPLEMENTATION_MESSAGE,
                    );
                }
                self.resolve_function(
                    &function.function,
                    scope,
                    true,
                    true,
                    self.types.any(),
                    SuperMemberHome::NonMemberFunction,
                );
            }
            Statement::Class(class) => self.resolve_class(class, scope),
            Statement::Interface(interface) => {
                if let Some(id) = self.scopes[scope.0 as usize]
                    .types
                    .get(self.identifier_text(&interface.name).as_ref())
                    .copied()
                {
                    let _ = self.resolve_type_symbol(id);
                }
            }
            Statement::TypeAlias(alias) => {
                if let Some(id) = self.scopes[scope.0 as usize]
                    .types
                    .get(self.identifier_text(&alias.name).as_ref())
                    .copied()
                {
                    let _ = self.resolve_type_symbol(id);
                }
            }
            Statement::Block(block) => {
                let child = self.new_scope(ScopeKind::Block, Some(scope));
                self.bind_statements(&block.data().statements, child);
                self.resolve_statements(&block.data().statements, child);
            }
            Statement::Expression(statement) => {
                self.resolve_expr(&statement.expression, scope);
                self.type_of_expr(&statement.expression, scope);
            }
            Statement::If(statement) => {
                self.resolve_expr(&statement.test, scope);
                self.type_of_expr(&statement.test, scope);
                let parent = self.flow;
                let truthy = self.guards_for(&statement.test, false);
                let falsy = self.guards_for(&statement.test, true);
                let then_end = self.in_branch(parent, &truthy, |binder| {
                    binder.resolve_statement(&statement.consequent, scope);
                });
                let else_end = self.in_branch(parent, &falsy, |binder| {
                    if let Some(alternate) = &statement.alternate {
                        binder.resolve_statement(alternate, scope);
                    }
                });
                // Only branches control can fall out of reach the merge, so an
                // `if (guard) { return; }` leaves the negated guard in force after it.
                let mut live = Vec::with_capacity(2);
                if !Self::statement_always_exits(statement.consequent.data()) {
                    live.push(then_end);
                }
                if !statement
                    .alternate
                    .as_ref()
                    .is_some_and(|alt| Self::statement_always_exits(alt.data()))
                {
                    live.push(else_end);
                }
                self.join_flow(parent, &live);
            }
            Statement::Switch(statement) => {
                self.resolve_expr(&statement.discriminant, scope);
                self.type_of_expr(&statement.discriminant, scope);
                let child = self.new_scope(ScopeKind::Block, Some(scope));
                for case in &statement.cases {
                    if let Some(test) = &case.data().test {
                        self.resolve_expr(test, child);
                        self.type_of_expr(test, child);
                    }
                    self.bind_statements(&case.data().consequent, child);
                }
                for case in &statement.cases {
                    self.publish_statement_class_shapes(&case.data().consequent, child);
                }
                for case in &statement.cases {
                    self.check_bound_statements(&case.data().consequent, child);
                }
            }
            Statement::For(for_statement) => {
                let child = self.new_scope(ScopeKind::For, Some(scope));
                if let Some(initializer) = &for_statement.initializer {
                    self.resolve_for_initializer(initializer, child);
                }
                if let Some(test) = &for_statement.test {
                    self.resolve_expr(test, child);
                    self.type_of_expr(test, child);
                }
                let parent = self.flow;
                let truthy = for_statement
                    .test
                    .as_ref()
                    .map_or_else(Vec::new, |test| self.guards_for(test, false));
                let body_end = self.in_branch(parent, &truthy, |binder| {
                    binder.resolve_statement(&for_statement.body, child);
                    if let Some(update) = &for_statement.update {
                        binder.resolve_expr(update, child);
                        binder.type_of_expr(update, child);
                    }
                });
                if let Some(test) = &for_statement.test {
                    let falsy = self.guards_for(test, true);
                    let skipped = self.branch_guarded(parent, &falsy);
                    let body_exit = self.branch_guarded(body_end, &falsy);
                    self.join_flow(parent, &[skipped, body_exit]);
                } else {
                    self.flow = body_end;
                }
            }
            Statement::ForIn(for_statement) => {
                let child = self.new_scope(ScopeKind::For, Some(scope));
                let mut using_diagnostic = None;
                if let ForBinding::Variable(variable) = &for_statement.binding {
                    using_diagnostic = match variable.kind {
                        VariableKind::Using => Some((
                            USING_DECLARATION_IN_FOR_IN,
                            USING_DECLARATION_IN_FOR_IN_MESSAGE,
                        )),
                        VariableKind::AwaitUsing => Some((
                            AWAIT_USING_DECLARATION_IN_FOR_IN,
                            AWAIT_USING_DECLARATION_IN_FOR_IN_MESSAGE,
                        )),
                        _ => None,
                    };
                }
                if let Some((code, message)) = using_diagnostic {
                    if let ForBinding::Variable(variable) = &for_statement.binding {
                        self.emit(code, variable.range, message);
                    }
                } else {
                    self.resolve_for_binding(&for_statement.binding, child, false);
                }
                self.resolve_expr(&for_statement.object, child);
                let object_type = self.type_of_expr(&for_statement.object, child);
                if using_diagnostic.is_none() {
                    self.assign_for_in_binding_type(&for_statement.binding, child, object_type);
                }
                let parent = self.flow;
                let skipped = self.branch_guarded(parent, &[]);
                let body_end = self.in_branch(parent, &[], |binder| {
                    binder.resolve_statement(&for_statement.body, child);
                });
                self.join_flow(parent, &[skipped, body_end]);
            }
            Statement::ForOf(for_statement) => {
                let child = self.new_scope(ScopeKind::For, Some(scope));
                self.resolve_expr(&for_statement.iterable, child);
                // `for-of` reads the iterator protocol off the iterable, so a
                // nullable iterable is rejected before the element type is
                // even computed.
                self.check_non_null_operand(&for_statement.iterable, child);
                let iterable_type = self.type_of_expr(&for_statement.iterable, child);
                let element_type =
                    match self.iteration_element_type(iterable_type, for_statement.mode) {
                        Some(element_type) => element_type,
                        None => {
                            self.emit(
                                FOR_OF_ITERABLE_REQUIRED,
                                for_statement.iterable.range(),
                                FOR_OF_ITERABLE_REQUIRED_MESSAGE,
                            );
                            self.types.error_type()
                        }
                    };
                self.resolve_for_of_binding(&for_statement.binding, child, element_type);
                let parent = self.flow;
                let skipped = self.branch_guarded(parent, &[]);
                let body_end = self.in_branch(parent, &[], |binder| {
                    binder.resolve_statement(&for_statement.body, child);
                });
                self.join_flow(parent, &[skipped, body_end]);
            }
            Statement::While(statement) => {
                self.resolve_expr(&statement.test, scope);
                self.type_of_expr(&statement.test, scope);
                let parent = self.flow;
                let truthy = self.guards_for(&statement.test, false);
                let falsy = self.guards_for(&statement.test, true);
                let body_end = self.in_branch(parent, &truthy, |binder| {
                    binder.resolve_statement(&statement.body, scope);
                });
                let skipped = self.branch_guarded(parent, &falsy);
                let body_exit = self.branch_guarded(body_end, &falsy);
                self.join_flow(parent, &[skipped, body_exit]);
            }
            Statement::DoWhile(statement) => {
                self.resolve_statement(&statement.body, scope);
                self.resolve_expr(&statement.test, scope);
                self.type_of_expr(&statement.test, scope);
            }
            Statement::Try(statement) => {
                let block = &statement.block;
                let try_scope = self.new_scope(ScopeKind::Block, Some(scope));
                self.bind_statements(&block.data().statements, try_scope);
                self.resolve_statements(&block.data().statements, try_scope);
                if let Some(handler) = &statement.handler {
                    let catch_scope = self.new_scope(ScopeKind::Catch, Some(scope));
                    if let Some(binding) = &handler.data().binding {
                        self.bind_pattern(binding, VariableKind::Let, catch_scope, handler.id());
                    }
                    let body = &handler.data().body;
                    self.bind_statements(&body.data().statements, catch_scope);
                    self.resolve_statements(&body.data().statements, catch_scope);
                }
                if let Some(finalizer) = &statement.finalizer {
                    let finally_scope = self.new_scope(ScopeKind::Block, Some(scope));
                    self.bind_statements(&finalizer.data().statements, finally_scope);
                    self.resolve_statements(&finalizer.data().statements, finally_scope);
                }
            }
            Statement::With(with_statement) => {
                let forbidden = self.is_typescript() || self.scopes[scope.0 as usize].is_strict();
                if forbidden {
                    self.emit(
                        WITH_STATEMENT_NOT_ALLOWED,
                        statement.range(),
                        WITH_STATEMENT_NOT_ALLOWED_MESSAGE,
                    );
                }
                self.resolve_expr(&with_statement.object, scope);
                self.type_of_expr(&with_statement.object, scope);
                let body_scope = if forbidden {
                    scope
                } else {
                    self.new_scope(ScopeKind::With, Some(scope))
                };
                self.resolve_statement(&with_statement.body, body_scope);
            }
            Statement::Labeled(statement) => self.resolve_statement(&statement.body, scope),
            Statement::ImportEquals(_) => {}
            Statement::Return(return_statement) => {
                let context = self.return_contexts.last().copied();
                let expected = context.and_then(|context| context.expected);
                let return_type = return_statement
                    .argument
                    .as_ref()
                    .map(|argument| {
                        self.resolve_expr(argument, scope);
                        match expected {
                            Some(target) => self.type_of_expr_with_target(argument, target, scope),
                            None => self.type_of_expr(argument, scope),
                        }
                    })
                    .unwrap_or_else(|| self.types.undefined_type());
                let return_type = if context.is_some_and(|context| context.await_expression) {
                    self.awaited_type(return_type)
                } else {
                    return_type
                };
                let compatible = if return_statement.argument.is_some() {
                    expected.is_none_or(|expected| self.types_assignable(return_type, expected))
                } else if let Some(expected) = expected {
                    self.types
                        .assignable_with_strict_null(return_type, expected)
                } else {
                    true
                };
                if !compatible {
                    let range = return_statement
                        .argument
                        .as_ref()
                        .map_or_else(|| statement.range(), |argument| argument.range());
                    self.emit(TYPE_NOT_ASSIGNABLE, range, NOT_ASSIGNABLE_MESSAGE);
                }
                if let Some(body_id) = self.function_body_stack.last().copied() {
                    self.return_types
                        .entry(body_id)
                        .or_default()
                        .push(return_type);
                }
            }
            Statement::Throw(statement) => {
                self.resolve_expr(&statement.argument, scope);
                self.type_of_expr(&statement.argument, scope);
            }
            Statement::Enum(declaration) => {
                let member_scope = self
                    .enum_declaration_symbols
                    .get(&statement.id())
                    .and_then(|symbol| self.enum_member_scopes.get(symbol))
                    .copied()
                    .unwrap_or(scope);
                for member in &declaration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.resolve_expr(initializer, member_scope);
                        self.type_of_expr(initializer, member_scope);
                    }
                }
            }
            Statement::Namespace(namespace) => {
                let child = self
                    .namespace_local_scopes
                    .get(&statement.id())
                    .copied()
                    .unwrap_or(scope);
                // `declare namespace`, `declare module`, and every namespace
                // body in a declaration file are ambient contexts: only
                // declarations may appear in their statement lists.
                if self.ambient_stack.last().copied().unwrap_or(false) || self.is_declaration_file {
                    for body_statement in &namespace.body.data().statements {
                        if !Self::is_declaration_statement(body_statement.data()) {
                            self.emit(
                                STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT,
                                body_statement.range(),
                                STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT_MESSAGE,
                            );
                        }
                    }
                }
                self.active_namespace_declarations.push(statement.id());
                self.resolve_statements(&namespace.body.data().statements, child);
                let popped = self.active_namespace_declarations.pop();
                debug_assert_eq!(popped, Some(statement.id()));
            }
            Statement::Declare(inner) => {
                self.ambient_stack.push(true);
                self.resolve_statement(inner, scope);
                self.ambient_stack.pop();
            }
            Statement::Export(export) => self.resolve_export(export, scope),
            _ => {}
        }
    }

    fn check_export_assignment_conflicts(&mut self) {
        let mut assignments = Vec::new();
        let mut mixed = false;
        for statement in self.source.statements() {
            let Statement::Export(export) = statement.data() else {
                continue;
            };
            match export {
                crate::syntax::ExportDeclaration::Assignment(expression) => {
                    assignments.push(expression.range());
                }
                crate::syntax::ExportDeclaration::Named(
                    crate::syntax::ExportNamedDeclaration::Specifiers {
                        type_only,
                        specifiers,
                        ..
                    },
                ) if *type_only
                    || (!specifiers.is_empty()
                        && specifiers.iter().all(|specifier| {
                            specifier.data().mode == crate::syntax::ExportSpecifierMode::TypeOnly
                        })) => {}
                crate::syntax::ExportDeclaration::All(all) if all.type_only => {}
                _ => mixed = true,
            }
        }
        if mixed {
            for range in assignments {
                self.emit(
                    MIXED_EXPORT_ASSIGNMENT,
                    range,
                    MIXED_EXPORT_ASSIGNMENT_MESSAGE,
                );
            }
        }
    }

    fn resolve_export(&mut self, export: &'src crate::syntax::ExportDeclaration, scope: ScopeId) {
        match export {
            crate::syntax::ExportDeclaration::Named(
                crate::syntax::ExportNamedDeclaration::Declaration(inner),
            ) => self.resolve_statement(inner, scope),
            crate::syntax::ExportDeclaration::Default(default) => match &default.value {
                crate::syntax::ExportDefaultValue::Function(function) => {
                    self.resolve_function(
                        function,
                        scope,
                        true,
                        true,
                        self.types.any(),
                        SuperMemberHome::NonMemberFunction,
                    );
                }
                crate::syntax::ExportDefaultValue::Class(class) => self.resolve_class(class, scope),
                crate::syntax::ExportDefaultValue::Expression(expression) => {
                    self.resolve_expr(expression, scope);
                }
                crate::syntax::ExportDefaultValue::Missing(_) => {}
                crate::syntax::ExportDefaultValue::Interface(interface) => {
                    let name = self.identifier_text(&interface.name);
                    if let Some(id) = self.scopes[scope.0 as usize]
                        .types
                        .get(name.as_ref())
                        .copied()
                    {
                        let _ = self.resolve_type_symbol(id);
                    }
                }
            },
            crate::syntax::ExportDeclaration::Assignment(expression) => {
                self.resolve_expr(expression, scope);
            }
            _ => {}
        }
    }

    fn resolve_for_initializer(&mut self, initializer: &'src ForInitializer, scope: ScopeId) {
        match initializer {
            ForInitializer::Variable(variable) => {
                self.bind_variable(variable, scope, NodeId::default());
                self.resolve_variable(variable, scope, true);
            }
            ForInitializer::Expression(expression) => self.resolve_expr(expression, scope),
        }
    }

    fn resolve_for_binding(
        &mut self,
        binding: &'src ForBinding,
        scope: ScopeId,
        require_using_initializer: bool,
    ) {
        match binding {
            ForBinding::Variable(variable) => {
                self.bind_variable(variable, scope, NodeId::default());
                self.resolve_variable(variable, scope, require_using_initializer);
            }
            ForBinding::Target(target) => {
                if matches!(
                    target.data(),
                    AssignmentTarget::Missing(_) | AssignmentTarget::Invalid(_)
                ) {
                    self.emit(
                        FOR_IN_LEFT_HAND_SIDE_INVALID,
                        target.range(),
                        FOR_IN_LEFT_HAND_SIDE_INVALID_MESSAGE,
                    );
                } else {
                    self.inventory_assignment_target_writes_in_scope(target, scope);
                    self.resolve_assignment_target(target, scope);
                }
            }
        }
    }

    fn assign_for_in_binding_type(
        &mut self,
        binding: &'src ForBinding,
        scope: ScopeId,
        object_type: TypeId,
    ) {
        let ForBinding::Variable(variable) = binding else {
            return;
        };
        let object_key = self.types.keyof(object_type);
        let string = self.types.string();
        let key_type = self.types.intersection(vec![object_key, string]);
        let keep_literal = variable.kind == VariableKind::Const;
        for declarator in &variable.declarations {
            if declarator.data().type_annotation.is_none() {
                self.assign_binding_pattern_types(
                    &declarator.data().binding,
                    key_type,
                    scope,
                    keep_literal,
                );
            }
        }
    }

    fn resolve_for_of_binding(
        &mut self,
        binding: &'src ForBinding,
        scope: ScopeId,
        element_type: TypeId,
    ) {
        match binding {
            ForBinding::Variable(variable) => {
                self.bind_variable(variable, scope, NodeId::default());
                for declarator_node in &variable.declarations {
                    let declarator = declarator_node.data();
                    if matches!(
                        variable.kind,
                        VariableKind::Using | VariableKind::AwaitUsing
                    ) && !matches!(declarator.binding.data(), BindingPattern::Identifier(_))
                    {
                        self.emit(
                            USING_DECLARATION_BINDING_PATTERN,
                            declarator_node.range(),
                            USING_DECLARATION_BINDING_PATTERN_MESSAGE,
                        );
                    }
                    let annotation = declarator
                        .type_annotation
                        .as_ref()
                        .map(|annotation| self.resolve_type(&annotation.data().type_node, scope));
                    if let Some(target) = annotation
                        && !self.types_assignable(element_type, target)
                    {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            declarator.binding.range(),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                    let declared = annotation.unwrap_or(element_type);
                    let keep_literal = matches!(
                        variable.kind,
                        VariableKind::Const | VariableKind::Using | VariableKind::AwaitUsing
                    );
                    self.assign_binding_pattern_types(
                        &declarator.binding,
                        declared,
                        scope,
                        keep_literal,
                    );
                }
            }
            ForBinding::Target(target) => {
                if matches!(
                    target.data(),
                    AssignmentTarget::Missing(_) | AssignmentTarget::Invalid(_)
                ) {
                    self.emit(
                        FOR_IN_LEFT_HAND_SIDE_INVALID,
                        target.range(),
                        FOR_IN_LEFT_HAND_SIDE_INVALID_MESSAGE,
                    );
                } else {
                    self.inventory_assignment_target_writes_in_scope(target, scope);
                    self.resolve_assignment_target(target, scope);
                    let target_type = self.type_of_assignment_target(target, scope);
                    if !self.types_assignable(element_type, target_type) {
                        self.emit(TYPE_NOT_ASSIGNABLE, target.range(), NOT_ASSIGNABLE_MESSAGE);
                    }
                }
            }
        }
    }

    fn resolve_variable(
        &mut self,
        variable: &'src VariableDeclaration,
        scope: ScopeId,
        require_using_initializer: bool,
    ) {
        for declarator_node in &variable.declarations {
            let declarator = declarator_node.data();
            if let Some(initializer) = &declarator.initializer {
                self.resolve_expr(initializer, scope);
            }
            if let Some(symbols) = self.declarator_symbols.get(&declarator_node.id())
                && declarator.initializer.is_some()
            {
                for symbol in symbols {
                    self.uninitialized_variables.remove(symbol);
                }
            }
            if matches!(
                variable.kind,
                VariableKind::Using | VariableKind::AwaitUsing
            ) {
                if !matches!(declarator.binding.data(), BindingPattern::Identifier(_)) {
                    self.emit(
                        USING_DECLARATION_BINDING_PATTERN,
                        declarator_node.range(),
                        USING_DECLARATION_BINDING_PATTERN_MESSAGE,
                    );
                } else if require_using_initializer && declarator.initializer.is_none() {
                    self.emit(
                        USING_DECLARATION_MISSING_INITIALIZER,
                        declarator_node.range(),
                        USING_DECLARATION_MISSING_INITIALIZER_MESSAGE,
                    );
                }
            }
            let annotation = declarator
                .type_annotation
                .as_ref()
                .map(|annotation| self.resolve_type(&annotation.data().type_node, scope));
            // Seed the object-literal anchor before typing so the literal's
            // declarations anchor under the annotated owner rather than a
            // fresh site owner.
            if let Some(initializer) = &declarator.initializer
                && matches!(initializer.data(), Expression::Object(_))
            {
                let owner = declarator
                    .type_annotation
                    .as_ref()
                    .and_then(|annotation| {
                        self.anchor_of_type_node(&annotation.data().type_node, scope)
                    })
                    .unwrap_or_else(|| PropertyOwner::Site(initializer.id()));
                self.literal_anchor.insert(initializer.id(), owner);
            }
            let initializer_type =
                declarator
                    .initializer
                    .as_ref()
                    .map(|initializer| match annotation {
                        Some(target) => self.type_of_expr_with_target(initializer, target, scope),
                        None => self.type_of_expr(initializer, scope),
                    });

            if let (Some(target), Some(source)) = (annotation, initializer_type)
                && !self.types_assignable(source, target)
            {
                self.emit(
                    TYPE_NOT_ASSIGNABLE,
                    declarator.binding.range(),
                    NOT_ASSIGNABLE_MESSAGE,
                );
            }

            let declared = match (annotation, initializer_type) {
                (Some(annotation), _) => annotation,
                (None, Some(initializer)) => {
                    if declarator
                        .initializer
                        .as_deref()
                        .is_some_and(Self::is_fresh_array_literal)
                    {
                        self.types.widen_fresh_literal(initializer)
                    } else {
                        initializer
                    }
                }
                (None, None) => self.types.any(),
            };
            let initializer_is_as_const =
                declarator.initializer.as_ref().is_some_and(|initializer| {
                    matches!(
                        initializer.data(),
                        Expression::As(cast) if cast.type_node.is_none()
                    )
                });
            let keep_literal = matches!(
                variable.kind,
                VariableKind::Const | VariableKind::Using | VariableKind::AwaitUsing
            );
            let keep_literal = initializer_is_as_const || keep_literal;
            self.assign_binding_pattern_types(&declarator.binding, declared, scope, keep_literal);

            if let BindingPattern::Identifier(name) = declarator.binding.data()
                && let Some(symbol) = self.lookup_value(scope, &self.identifier_text(name))
            {
                // Seed the symbol anchor so member accesses on this variable
                // resolve to the property owner for rename anchoring.
                let owner = declarator
                    .initializer
                    .as_ref()
                    .and_then(|initializer| {
                        if matches!(initializer.data(), Expression::Object(_)) {
                            self.literal_anchor.get(&initializer.id()).copied()
                        } else if matches!(initializer.data(), Expression::Identifier(_)) {
                            self.resolved_expression_reference(initializer)
                                .and_then(|alias| self.symbol_anchor.get(&alias).copied())
                        } else {
                            self.node_types
                                .get(&initializer.id())
                                .copied()
                                .and_then(|ty| self.owner_of_named_type(ty))
                        }
                    })
                    .or_else(|| {
                        declarator.type_annotation.as_ref().and_then(|annotation| {
                            self.anchor_of_type_node(&annotation.data().type_node, scope)
                        })
                    });
                if let Some(owner) = owner {
                    self.symbol_anchor.insert(symbol, owner);
                }
                match declarator
                    .initializer
                    .as_ref()
                    .map(|initializer| initializer.data())
                {
                    Some(Expression::Function(function)) => {
                        self.jsx_callables
                            .insert(symbol, JsxCallable::Function(&function.function));
                    }
                    Some(Expression::Arrow(arrow)) => {
                        self.jsx_callables.insert(symbol, JsxCallable::Arrow(arrow));
                    }
                    _ => {}
                }
            }
        }
    }

    fn is_fresh_array_literal(expression: &Expr) -> bool {
        match expression.data() {
            Expression::Array(_) => true,
            Expression::Parenthesized(parenthesized) => {
                Self::is_fresh_array_literal(parenthesized.as_ref())
            }
            _ => false,
        }
    }

    fn assign_binding_pattern_types(
        &mut self,
        pattern: &'src crate::syntax::Pattern,
        source: TypeId,
        scope: ScopeId,
        keep_literal: bool,
    ) {
        match pattern.data() {
            BindingPattern::Identifier(name) => {
                let declared = self.types.widen(source, keep_literal);
                if let Some(symbol) = self.lookup_value(scope, &self.identifier_text(name)) {
                    self.symbol_types[symbol.get() as usize] = declared;
                }
            }
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    let projected = self
                        .property_key(&property.name)
                        .and_then(|name| self.types.read_property_type(source, &name))
                        .unwrap_or_else(|| self.types.any());
                    self.assign_binding_pattern_types(
                        &property.binding,
                        projected,
                        scope,
                        keep_literal,
                    );
                }
            }
            BindingPattern::Array(array) => {
                for (index, element) in array.elements.iter().enumerate() {
                    if let crate::syntax::ArrayBindingElement::Binding(inner) = element {
                        let projected = self.binding_element_type(source, index);
                        self.assign_binding_pattern_types(inner, projected, scope, keep_literal);
                    }
                }
            }
            BindingPattern::Rest(rest) => {
                self.assign_binding_pattern_types(&rest.argument, source, scope, keep_literal);
            }
            BindingPattern::Assignment(assignment) => {
                self.assign_binding_pattern_types(&assignment.left, source, scope, keep_literal);
            }
            BindingPattern::Missing(_) => {}
        }
    }

    fn binding_element_type(&mut self, source: TypeId, index: usize) -> TypeId {
        match self.types.get(source).clone() {
            Type::Tuple(shape) => self
                .types
                .tuple_index_type(&shape, index)
                .unwrap_or_else(|| self.types.undefined_type()),
            Type::Array(element) => element,
            Type::Union(members) => {
                let projected: Vec<_> = members
                    .into_iter()
                    .map(|member| self.binding_element_type(member, index))
                    .collect();
                self.types.union(&projected)
            }
            _ => self.types.any(),
        }
    }

    fn bind_implicit_function_values(
        &mut self,
        parameters: &'src [crate::syntax::ParameterNode],
        scope: ScopeId,
    ) {
        for name in ["arguments", "this"] {
            let explicitly_bound = parameters.iter().any(|parameter| {
                matches!(
                    parameter.data().binding.data(),
                    BindingPattern::Identifier(identifier)
                        if self.identifier_text(identifier) == name
                )
            });
            if !explicitly_bound {
                self.declare(
                    name,
                    SymbolKind::Parameter,
                    scope,
                    NodeId::default(),
                    NodeId::default_range(),
                );
            }
        }
    }

    fn generator_completion_type(&mut self, annotation: TypeId) -> Option<TypeId> {
        self.types.generator_return_type(annotation)
    }

    fn resolve_function(
        &mut self,
        function: &'src FunctionLike,
        parent: ScopeId,
        new_target_allowed: bool,
        is_declaration: bool,
        this_type: TypeId,
        member_home: SuperMemberHome,
    ) {
        let scope = self.new_scope(ScopeKind::Function, Some(parent));
        let new_target_marker = self.new_target_contexts.len();
        self.new_target_contexts.push(new_target_allowed);
        self.super_call_contexts
            .push(SuperCallContext::NonConstructor);
        self.super_member_homes.push(member_home);
        self.bind_implicit_function_values(&function.parameters, scope);
        let function_symbol = function.name.as_ref().map(|name| {
            let symbol_scope = if is_declaration { parent } else { scope };
            self.declare(
                &self.identifier_text(name),
                SymbolKind::Function,
                symbol_scope,
                name.id(),
                name.range(),
            )
        });
        self.bind_type_parameters(function.type_parameters.as_ref(), scope);
        let this_type = self.this_parameter_type(&function.parameters, scope, this_type);
        for parameter in &function.parameters {
            if self.is_this_parameter(parameter) {
                continue;
            }
            self.resolve_non_constructor_parameter(parameter, scope);
        }
        let annotated_return_type = function
            .return_type
            .as_ref()
            .map(|annotation| self.resolve_type(&annotation.data().type_node, scope));
        let expected_return_type = if function.is_generator {
            annotated_return_type
                .and_then(|return_type| self.generator_completion_type(return_type))
        } else {
            annotated_return_type.map(|return_type| {
                if function.is_async {
                    self.awaited_type(return_type)
                } else {
                    return_type
                }
            })
        };
        self.return_contexts.push(ReturnContext {
            expected: expected_return_type,
            await_expression: function.is_async,
            generator_protocol: function.is_generator.then_some(if function.is_async {
                ForOfMode::Async
            } else {
                ForOfMode::Sync
            }),
        });
        self.this_context.push(this_type);
        if let Some(body_id) = function.body.as_ref().and_then(FunctionBody::id) {
            self.return_types.entry(body_id).or_default();
            self.yield_types.entry(body_id).or_default();
            if is_declaration {
                self.declaration_function_bodies.insert(body_id);
            }
            self.function_body_stack.push(body_id);
        }
        let body_flow = if is_declaration {
            FlowNodeId::ROOT
        } else {
            self.captured_flow_seed()
        };
        if !is_declaration {
            self.push_reassigned_scope();
        }
        self.in_isolated_flow(body_flow, |binder| match &function.body {
            Some(FunctionBody::Block(block)) => {
                if directive_prologue_is_strict(binder.source, &block.data().statements) {
                    binder.scopes[scope.0 as usize].strict = true;
                }
                binder.bind_statements(&block.data().statements, scope);
                binder.bind_hoisted_statements(&block.data().statements, scope);
                binder.resolve_statements(&block.data().statements, scope);
            }
            Some(FunctionBody::Expression(expression)) => binder.resolve_expr(expression, scope),
            _ => {}
        });
        if let Some(body) = function.body.as_ref() {
            let annotation = function
                .return_type
                .as_ref()
                .map(|node| node.data().type_node.range());
            self.check_annotated_return_fallthrough(body, expected_return_type, annotation);
        }
        if !is_declaration {
            self.pop_reassigned_scope();
        }
        if let Some(symbol) = function_symbol {
            let return_type = annotated_return_type
                .unwrap_or_else(|| self.inferred_function_return_type(function, scope));
            let (type_parameters, type_parameter_bounds) =
                self.signature_type_parameters(function.type_parameters.as_ref(), scope);
            let mut function_parameters = Vec::with_capacity(function.parameters.len());
            for (idx, parameter) in function.parameters.iter().enumerate() {
                if let Some(lowered) = self.lower_parameter(idx, parameter, scope) {
                    function_parameters.push(lowered);
                }
            }
            let function_type = self.types.function_with_parameter_bounds(
                type_parameters,
                type_parameter_bounds,
                function_parameters,
                return_type,
                !self.is_typescript(),
            );
            self.symbol_types[symbol.get() as usize] = function_type;
            if is_declaration && function.body.is_none() {
                let Type::Function(signature) = self.types.get(function_type) else {
                    unreachable!("function type constructor must intern a function signature");
                };
                self.overload_signatures[symbol.get() as usize].push(signature.clone());
            }
        }
        if let Some(body_id) = function.body.as_ref().and_then(FunctionBody::id) {
            let popped = self.function_body_stack.pop();
            debug_assert_eq!(popped, Some(body_id));
        }
        self.return_contexts.pop();
        self.this_context.pop();
        self.new_target_contexts.truncate(new_target_marker);
        let popped_context = self.super_call_contexts.pop();
        debug_assert_eq!(popped_context, Some(SuperCallContext::NonConstructor));
        let popped_home = self.super_member_homes.pop();
        debug_assert_eq!(popped_home, Some(member_home));
    }

    pub(crate) fn bind_type_parameters(
        &mut self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        scope: ScopeId,
    ) {
        self.bind_type_parameter_names(list, scope);
        self.resolve_type_parameter_bounds(list, scope);
    }

    fn bind_type_parameter_names(
        &mut self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        scope: ScopeId,
    ) {
        let Some(list) = list else {
            return;
        };
        for parameter in &list.parameters {
            let data = parameter.data();
            let symbol = self.declare(
                &self.identifier_text(&data.name),
                SymbolKind::TypeParameter,
                scope,
                parameter.id(),
                data.name.range(),
            );
            if let Some(node) = data.default.as_deref() {
                let replaced = self.type_parameter_defaults.insert(
                    symbol,
                    TypeParameterDefaultState::Unresolved { node, scope },
                );
                debug_assert!(replaced.is_none());
            }
        }
    }

    fn resolve_type_parameter_default(&mut self, symbol: SymbolId) -> Option<TypeId> {
        let state = self.type_parameter_defaults.get(&symbol).copied()?;
        match state {
            TypeParameterDefaultState::Unresolved { node, scope } => {
                self.type_parameter_defaults.insert(
                    symbol,
                    TypeParameterDefaultState::Resolving {
                        range: node.range(),
                    },
                );
                let resolved = self.resolve_type(node, scope);
                if let Some(TypeParameterDefaultState::Circular(error)) =
                    self.type_parameter_defaults.get(&symbol).copied()
                {
                    return Some(error);
                }
                self.type_parameter_defaults
                    .insert(symbol, TypeParameterDefaultState::Resolved(resolved));
                self.types.set_type_parameter_default(symbol, resolved);
                Some(resolved)
            }
            TypeParameterDefaultState::Resolving { range } => {
                let error = self.types.error_type();
                self.emit(
                    TYPE_PARAMETER_CIRCULAR_DEFAULT,
                    range,
                    TYPE_PARAMETER_CIRCULAR_DEFAULT_MESSAGE,
                );
                self.type_parameter_defaults
                    .insert(symbol, TypeParameterDefaultState::Circular(error));
                self.types.set_type_parameter_default(symbol, error);
                Some(error)
            }
            TypeParameterDefaultState::Circular(error)
            | TypeParameterDefaultState::Resolved(error) => Some(error),
        }
    }

    fn resolve_type_parameter_bounds(
        &mut self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        scope: ScopeId,
    ) {
        let _ = self.signature_type_parameters(list, scope);
    }

    fn signature_type_parameters(
        &mut self,
        list: Option<&'src crate::syntax::TypeParameterList>,
        scope: ScopeId,
    ) -> (Vec<SymbolId>, Vec<TypeParameterBounds>) {
        let Some(list) = list else {
            return (Vec::new(), Vec::new());
        };
        let mut symbols = Vec::with_capacity(list.parameters.len());
        let mut bounds = Vec::with_capacity(list.parameters.len());
        for parameter in &list.parameters {
            let data = parameter.data();
            let name = self.identifier_text(&data.name);
            let Some(symbol) = self.lookup_type(scope, &name) else {
                continue;
            };
            let constraint = data
                .constraint
                .as_ref()
                .map(|constraint| self.resolve_type(constraint, scope));
            if let Some(constraint) = constraint {
                self.types.set_type_parameter_constraint(symbol, constraint);
            }
            let default = self.resolve_type_parameter_default(symbol);
            if let Some(default) = default {
                self.types.set_type_parameter_default(symbol, default);
            }
            symbols.push(symbol);
            bounds.push(TypeParameterBounds {
                constraint,
                default,
            });
        }
        (symbols, bounds)
    }

    fn resolve_unsupported_legacy_decorators(
        &mut self,
        decorators: &'src [crate::syntax::DecoratorNode],
        code: DiagnosticCode,
        message: &'static str,
        scope: ScopeId,
    ) {
        for decorator in decorators {
            self.emit(code, decorator.range(), message);
            self.resolve_expr(&decorator.data().expression, scope);
        }
    }

    fn reject_disallowed_parameter_property(
        &mut self,
        parameter: &'src crate::syntax::ParameterNode,
    ) {
        let modifiers = &parameter.data().modifiers;
        if modifiers.accessibility.is_some() || modifiers.is_readonly || modifiers.is_override {
            self.emit(
                PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR,
                parameter.range(),
                PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR_MESSAGE,
            );
        }
    }

    fn resolve_non_constructor_parameter(
        &mut self,
        parameter: &'src crate::syntax::ParameterNode,
        scope: ScopeId,
    ) {
        self.reject_disallowed_parameter_property(parameter);
        self.resolve_parameter(parameter, scope);
    }

    fn resolve_parameter(&mut self, parameter: &'src crate::syntax::ParameterNode, scope: ScopeId) {
        let data = parameter.data();
        self.resolve_unsupported_legacy_decorators(
            &data.decorators,
            PARAMETER_DECORATOR_NOT_SUPPORTED,
            PARAMETER_DECORATOR_NOT_SUPPORTED_MESSAGE,
            scope,
        );
        self.bind_pattern(&data.binding, VariableKind::Let, scope, parameter.id());
        let annotation = data
            .type_annotation
            .as_ref()
            .map(|annotation| self.resolve_type(&annotation.data().type_node, scope));
        if let Some(initializer) = &data.initializer {
            self.resolve_expr(initializer, scope);
        }
        let initializer_type = data
            .initializer
            .as_ref()
            .map(|initializer| match annotation {
                Some(target) => self.type_of_expr_with_target(initializer, target, scope),
                None => self.type_of_expr(initializer, scope),
            });
        if let (Some(target), Some(source)) = (annotation, initializer_type)
            && !self.types_assignable(source, target)
        {
            self.emit(
                TYPE_NOT_ASSIGNABLE,
                data.initializer
                    .as_ref()
                    .map_or(parameter.range(), |initializer| initializer.range()),
                NOT_ASSIGNABLE_MESSAGE,
            );
        }
        if let BindingPattern::Identifier(name) = data.binding.data()
            && let Some(symbol) = self.scopes[scope.0 as usize]
                .values
                .get(self.identifier_text(name).as_ref())
                .copied()
        {
            // Seed the parameter's symbol anchor from its type annotation
            // so member accesses resolve to the annotated interface/class.
            // Name-first via the annotation node: interface references
            // intern as structural views, so the declaring symbol is only
            // reachable from the node, not from the resolved TypeId.
            if let Some(owner) = data.type_annotation.as_ref().and_then(|annotation| {
                self.anchor_of_type_node(&annotation.data().type_node, scope)
            }) {
                self.symbol_anchor.insert(symbol, owner);
            }
            let type_id = annotation
                .or_else(|| initializer_type.map(|ty| self.types.widen(ty, false)))
                .unwrap_or_else(|| self.types.any());
            self.symbol_types[symbol.get() as usize] = type_id;
        }
    }

    fn resolve_class(&mut self, class: &'src ClassDeclaration, parent: ScopeId) {
        let ambient =
            class.modifiers.is_declare || self.ambient_stack.last().copied().unwrap_or(false);
        let _ = self.resolve_class_body(class, parent, false, ambient);
    }

    fn is_this_parameter(&self, parameter: &'src ParameterNode) -> bool {
        let data = parameter.data();
        matches!(
            data.binding.data(),
            BindingPattern::Identifier(identifier)
                if self.identifier_text(identifier).as_ref() == "this"
        )
    }
    /// Lowers one parsed parameter into an interned [`FunctionParameter`],
    /// skipping `this` parameters. Function declaration binding and signature
    /// construction share this path so parameter lowering cannot diverge.
    fn lower_parameter(
        &mut self,
        index: usize,
        parameter: &'src ParameterNode,
        scope: ScopeId,
    ) -> Option<FunctionParameter> {
        if self.is_this_parameter(parameter) {
            return None;
        }
        let data = parameter.data();
        let type_id = match (&data.type_annotation, &data.initializer) {
            (Some(annotation), _) => self.resolve_type(&annotation.data().type_node, scope),
            (None, Some(initializer)) => {
                let initializer_type = self.type_of_expr(initializer, scope);
                if Self::is_fresh_array_literal(initializer) {
                    self.types.widen_fresh_literal(initializer_type)
                } else {
                    self.types.widen(initializer_type, false)
                }
            }
            (None, None) => self.types.any(),
        };
        let rest = matches!(data.binding.data(), BindingPattern::Rest(_));
        if rest
            && let Some(annotation) = &data.type_annotation
            && !self.is_valid_rest_parameter_type(type_id)
        {
            self.emit(
                TYPE_NOT_ASSIGNABLE,
                annotation.range(),
                NOT_ASSIGNABLE_MESSAGE,
            );
        }
        let optional = data.optional || data.initializer.is_some();
        let name = match data.binding.data() {
            BindingPattern::Identifier(identifier) => self.identifier_text(identifier).into_owned(),
            BindingPattern::Rest(rest) => match rest.argument.data() {
                BindingPattern::Identifier(identifier) => {
                    self.identifier_text(identifier).into_owned()
                }
                _ => format!("arg{index}"),
            },
            BindingPattern::Assignment(assign) => match assign.left.data() {
                BindingPattern::Identifier(identifier) => {
                    self.identifier_text(identifier).into_owned()
                }
                BindingPattern::Rest(rest) => match rest.argument.data() {
                    BindingPattern::Identifier(identifier) => {
                        self.identifier_text(identifier).into_owned()
                    }
                    _ => format!("arg{index}"),
                },
                _ => format!("arg{index}"),
            },
            _ => format!("arg{index}"),
        };
        Some(FunctionParameter::new(name, type_id, optional, rest))
    }

    fn this_parameter_type(
        &mut self,
        parameters: &'src [ParameterNode],
        scope: ScopeId,
        default: TypeId,
    ) -> TypeId {
        let Some(parameter) = parameters.first() else {
            return default;
        };
        if !self.is_this_parameter(parameter) {
            return default;
        }
        let data = parameter.data();
        match (&data.binding.data(), &data.type_annotation) {
            (BindingPattern::Identifier(_), Some(annotation)) => {
                self.resolve_type(&annotation.data().type_node, scope)
            }
            _ => default,
        }
    }

    fn resolve_class_expression(
        &mut self,
        class: &'src ClassDeclaration,
        parent: ScopeId,
    ) -> TypeId {
        self.resolve_class_body(class, parent, true, false)
    }

    fn class_member_method_name(
        &self,
        member: &'src ClassMember,
    ) -> Option<std::borrow::Cow<'src, str>> {
        match member {
            ClassMember::Method(method) if method.modifier == PropertyModifier::None => {
                if let PropertyName::Identifier(identifier) = &method.name {
                    Some(self.identifier_text(identifier))
                } else {
                    None
                }
            }
            ClassMember::Constructor(_) => Some(std::borrow::Cow::Borrowed("constructor")),
            _ => None,
        }
    }

    fn class_member_overload_range(member: &'src ClassMember) -> TextRange {
        match member {
            ClassMember::Method(method) => Self::property_name_range(&method.name),
            ClassMember::Constructor(constructor) => constructor.body.range(),
            _ => TextRange::new(crate::source::Utf16Pos::ZERO, crate::source::Utf16Pos::ZERO)
                .unwrap(),
        }
    }
    /// Pairs TS7010 with TS2391: when a class overload group lacks its
    /// implementation and the leading signature also omits a return type,
    /// upstream reports the missing return at the same member-name range.
    /// Gated on `noImplicitAny` like every TS7010 producer.
    fn emit_missing_overload_return_pair(&mut self, member: &'src ClassMember, range: TextRange) {
        if let ClassMember::Method(method) = member
            && self.no_implicit_any
            && method.modifier == PropertyModifier::None
            && method.function.return_type.is_none()
        {
            self.emit(
                MISSING_METHOD_RETURN_TYPE,
                range,
                MISSING_METHOD_RETURN_TYPE_MESSAGE,
            );
        }
    }

    fn check_class_method_overload_order(
        &mut self,
        members: &'src [crate::syntax::ClassMemberNode],
        ambient: bool,
    ) {
        if self.is_declaration_file || ambient {
            // Ambient classes (declare class, .d.ts, or inside declare namespace)
            // carry signature-only members that do not require implementations.
            return;
        }
        let mut i = 0;
        while i < members.len() {
            let first = members[i].data();
            let Some(name) = self.class_member_method_name(first) else {
                i += 1;
                continue;
            };
            // Only method signatures with no body start an overload group;
            // a constructor or a method with a body is an implementation, not a
            // group start.
            if matches!(first, ClassMember::Constructor(_)) {
                i += 1;
                continue;
            }
            if let ClassMember::Method(method) = first
                && (method.function.body.is_some() || method.modifiers.is_abstract)
            {
                // A method with a body is an implementation, not a group
                // start. An abstract method is a complete declaration with no
                // body by definition — it is not an overload signature and
                // requires no following implementation.
                i += 1;
                continue;
            }
            let start = i;
            i += 1;
            // Consume consecutive overload signatures with the same name.
            while i < members.len() {
                let next = members[i].data();
                let next_name = self.class_member_method_name(next);
                let is_overload_signature = matches!(next, ClassMember::Method(method)
                    if method.modifier == PropertyModifier::None
                        && method.function.body.is_none()
                        && !method.modifiers.is_abstract);
                if is_overload_signature && next_name.as_ref() == Some(&name) {
                    i += 1;
                } else {
                    break;
                }
            }
            // Missing implementation at end of class.
            if i >= members.len() {
                self.emit(
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION,
                    Self::class_member_overload_range(members[start].data()),
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE,
                );
                self.emit_missing_overload_return_pair(
                    members[start].data(),
                    Self::class_member_overload_range(members[start].data()),
                );
                break;
            }
            let implementation = members[i].data();
            let implementation_name = self.class_member_method_name(implementation);
            let matches_name = implementation_name.as_ref() == Some(&name);
            let is_overload_signature = matches!(implementation, ClassMember::Method(method)
                if method.modifier == PropertyModifier::None
                    && method.function.body.is_none()
                    && !method.modifiers.is_abstract);

            if matches!(implementation, ClassMember::Method(method)
                if method.modifier == PropertyModifier::None && method.function.body.is_some() && matches_name)
                || matches!(implementation, ClassMember::Constructor(_)
                    if name == "constructor")
            {
                // Valid implementation follows the overload signature(s).
                i += 1;
            } else if matches!(implementation, ClassMember::Method(_)) && is_overload_signature {
                // Missing implementation: the next member is another overload signature,
                // not the body for this group. Leave it in place for the next iteration.
                self.emit(
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION,
                    Self::class_member_overload_range(members[start].data()),
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE,
                );
                self.emit_missing_overload_return_pair(
                    members[start].data(),
                    Self::class_member_overload_range(members[start].data()),
                );
            } else if matches!(implementation, ClassMember::Method(method)
                if method.modifier == PropertyModifier::None && method.function.body.is_some() && !matches_name)
            {
                // The next member is a method body with the wrong name.
                self.emit(
                    FUNCTION_IMPLEMENTATION_WRONG_NAME,
                    Self::class_member_overload_range(implementation),
                    FUNCTION_IMPLEMENTATION_WRONG_NAME_MESSAGE,
                );
                i += 1;
            } else {
                // Any other member means the implementation is missing.
                self.emit(
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION,
                    Self::class_member_overload_range(members[start].data()),
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE,
                );
                self.emit_missing_overload_return_pair(
                    members[start].data(),
                    Self::class_member_overload_range(members[start].data()),
                );
                // Do not consume this member; it may be a normal class member.
                i = start + 1;
            }
        }
    }

    fn publish_predeclared_class_shape(&mut self, class: &'src ClassDeclaration, _parent: ScopeId) {
        let Some(name) = &class.name else {
            return;
        };
        let scope = self
            .class_header_scopes
            .get(&name.id())
            .copied()
            .expect("named class header was predeclared");
        let owner = self.scopes[scope.0 as usize]
            .owner
            .expect("predeclared class scope has an owner");
        self.prepare_class_shape(class, scope, Some(owner));
    }

    fn prepare_class_shape(
        &mut self,
        class: &'src ClassDeclaration,
        scope: ScopeId,
        owner: Option<SymbolId>,
    ) {
        if let Some(owner) = owner {
            self.class_member_scopes.insert(owner, scope);
        }
        if let Some(heritage) = &class.extends {
            self.resolve_expr(&heritage.expression, scope);
            if let Some(owner) = owner
                && let Some(base_symbol) = self.resolved_expression_reference(&heritage.expression)
            {
                self.class_base_symbols.insert(owner, base_symbol);
            }
        }
        for member in &class.members {
            self.bind_class_member(member, scope);
        }
        let preliminary_instance =
            self.class_instance_type(class, scope, owner, ClassState::Provisional);
        if let Some(owner) = owner {
            self.class_instance_types
                .insert(owner, preliminary_instance);
            let static_type = self.class_static_type(class, scope, preliminary_instance);
            self.class_constructor_types.insert(owner, static_type);
            self.symbol_types[owner.get() as usize] = preliminary_instance;
        }
    }
    fn resolve_class_body(
        &mut self,
        class: &'src ClassDeclaration,
        parent: ScopeId,
        bind_internal_name: bool,
        ambient: bool,
    ) -> TypeId {
        // A class nested inside a constructor does not inherit its super-call
        // legality: only the constructor body itself may call `super(...)`.
        self.super_call_contexts
            .push(SuperCallContext::NonConstructor);
        self.class_derived_stack.push(class.extends.is_some());
        let mut constructor_writable_readonly: HashSet<String> = class
            .members
            .iter()
            .filter_map(|member| match member.data() {
                ClassMember::Property(property)
                    if !property.modifiers.is_static && property.modifiers.is_readonly =>
                {
                    self.property_key(&property.name)
                }
                _ => None,
            })
            .collect();
        if let Some(constructor) = class.members.iter().find_map(|member| {
            let ClassMember::Constructor(constructor) = member.data() else {
                return None;
            };
            Some(constructor)
        }) {
            for parameter in &constructor.parameters {
                let parameter = parameter.data();
                if !parameter.modifiers.is_readonly {
                    continue;
                }
                let BindingPattern::Identifier(identifier) = parameter.binding.data() else {
                    continue;
                };
                constructor_writable_readonly.insert(self.identifier_text(identifier).into_owned());
            }
        }
        self.constructor_writable_readonly_properties
            .push(constructor_writable_readonly);
        let predeclared_scope = if bind_internal_name {
            None
        } else {
            class
                .name
                .as_ref()
                .and_then(|name| self.class_header_scopes.remove(&name.id()))
        };
        let predeclared = predeclared_scope.is_some();
        let bind_local_name = bind_internal_name || (class.name.is_some() && !predeclared);
        let scope = predeclared_scope.unwrap_or_else(|| {
            let scope = self.new_scope(ScopeKind::Class, Some(parent));
            self.scopes[scope.0 as usize].strict = true;
            self.bind_type_parameter_names(class.type_parameters.as_ref(), scope);
            scope
        });
        // Recovery-only class declarations outside a statement list have no
        // outer binding, so keep their name local like a named class expression.
        if bind_local_name && let Some(name) = &class.name {
            self.declare(
                &self.identifier_text(name),
                SymbolKind::Class,
                scope,
                name.id(),
                name.range(),
            );
        }
        let owner = if predeclared {
            self.scopes[scope.0 as usize].owner
        } else {
            let owner_scope = if bind_local_name { scope } else { parent };
            class.name.as_ref().and_then(|name| {
                self.scopes[owner_scope.0 as usize]
                    .values
                    .get(self.identifier_text(name).as_ref())
                    .copied()
            })
        };
        if let Some(owner) = owner {
            if !predeclared {
                let class_parameters =
                    self.bound_type_parameter_symbols(class.type_parameters.as_ref(), scope);
                self.types.declare_class(owner, class_parameters);
                let class_bounds = self
                    .signature_type_parameters(class.type_parameters.as_ref(), scope)
                    .1;
                self.types.set_class_bounds(owner, class_bounds);
                self.set_scope_owner(scope, owner);
            }
            self.class_owner_stack.push(owner);
        }
        // Class decorator expressions evaluate in the enclosing scope, before
        // heritage and members, so they do not see a class-expression name.
        for decorator in &class.decorators {
            self.resolve_expr(&decorator.data().expression, parent);
        }
        if !predeclared {
            self.prepare_class_shape(class, scope, owner);
        }
        self.check_class_method_overload_order(&class.members, ambient);
        let mut implemented_types = Vec::new();
        for implemented in &class.implements {
            let ty = self.resolve_type(implemented, scope);
            implemented_types.push((ty, implemented.range()));
        }
        for member in &class.members {
            self.resolve_class_member(member.data(), scope, ambient);
        }
        let instance_type = self.class_instance_type(class, scope, owner, ClassState::Final);
        let static_type = self.class_static_type(class, scope, instance_type);
        if let Some(owner) = owner {
            self.class_instance_types.insert(owner, instance_type);
            self.class_constructor_types.insert(owner, static_type);
            // Class declarations: the symbol's declared type is the instance
            // type (`>C : C` in .types baselines). Class expressions: the
            // symbol's type is the constructor type (`>C : typeof C`).
            self.symbol_types[owner.get() as usize] = if bind_internal_name {
                static_type
            } else {
                instance_type
            };
        }
        for (implemented_type, range) in implemented_types {
            if !self.types_assignable(instance_type, implemented_type) {
                self.emit(TYPE_NOT_ASSIGNABLE, range, NOT_ASSIGNABLE_MESSAGE);
            }
        }
        self.check_class_property_initialization(&class.members, scope);
        self.constructor_writable_readonly_properties.pop();
        let popped_derived = self.class_derived_stack.pop();
        debug_assert_eq!(popped_derived, Some(class.extends.is_some()));
        if let Some(owner) = owner {
            let popped_owner = self.class_owner_stack.pop();
            debug_assert_eq!(popped_owner, Some(owner));
        }
        static_type
    }
    /// TS2564 (`strictPropertyInitialization`): an uninitialized, non-optional
    /// instance property whose type excludes `undefined` and that no
    /// constructor assignment definitely assigns. The whole check is gated on
    /// the compiler option.
    fn check_class_property_initialization(
        &mut self,
        members: &'src [crate::syntax::ClassMemberNode],
        _scope: ScopeId,
    ) {
        if !self.strict_property_initialization {
            return;
        }
        let assigned = self.constructor_property_assignments(members);
        for member in members {
            let ClassMember::Property(property) = member.data() else {
                continue;
            };
            // TypeScript only reports TS2564 for identifier-named properties.
            // String- and numeric-literal property names are exempt from the
            // strict property initialization check.
            if property.optional
                || property.definite
                || property.initializer.is_some()
                || property.modifiers.is_static
                || property.modifiers.is_declare
                || matches!(
                    property.name,
                    PropertyName::String(_) | PropertyName::Number(_)
                )
            {
                continue;
            }
            let declared = property
                .type_annotation
                .as_ref()
                .and_then(|annotation| {
                    self.type_nodes
                        .get(&annotation.data().type_node.id())
                        .copied()
                })
                .unwrap_or(self.types.any());
            if self.types_assignable(self.types.undefined_type(), declared) {
                continue;
            }
            let Some(name) = self.property_key(&property.name) else {
                continue;
            };
            if assigned.contains(&name) {
                continue;
            }
            self.emit(
                PROPERTY_NOT_INITIALIZED,
                Self::property_name_range(&property.name),
                PROPERTY_NOT_INITIALIZED_MESSAGE,
            );
        }
    }
    fn merge_iterator_properties(
        &mut self,
        left: IteratorProperty,
        right: IteratorProperty,
    ) -> IteratorProperty {
        debug_assert_eq!(left.access(), right.access());
        debug_assert_eq!(left.declaring_class(), right.declaring_class());
        let mut declaring_types = left.declaring_types().to_vec();
        for &owner in right.declaring_types() {
            if !declaring_types.contains(&owner) {
                declaring_types.push(owner);
            }
        }
        let type_id = self
            .types
            .intersection_ordered(vec![left.type_id(), right.type_id()]);
        IteratorProperty::new(type_id, left.optional() && right.optional())
            .with_accessibility(left.access(), left.declaring_class())
            .with_declaring_types(declaring_types)
            .with_method(left.is_method() || right.is_method())
            .with_spreadable(left.spreadable() && right.spreadable())
    }

    fn class_member_properties(
        &mut self,
        class: &'src ClassDeclaration,
        scope: ScopeId,
        side: ClassSide,
    ) -> (
        Vec<PropertyType>,
        HashSet<String>,
        Option<IteratorProperty>,
        Option<IteratorProperty>,
    ) {
        let mut properties = Vec::new();
        let mut seen = HashSet::new();
        let mut iterator_property = None;
        let mut async_iterator_property = None;
        let mut overload_state = HashMap::<String, bool>::new();
        let mut iterator_overload = false;
        let mut async_iterator_overload = false;
        let declaring_class = self.scopes[scope.0 as usize].owner;
        for member in &class.members {
            let intrinsic_iterator = match member.data() {
                ClassMember::Property(property)
                    if side.includes(property.modifiers.is_static)
                        && self
                            .intrinsic_symbol_iterator_protocol(&property.name)
                            .is_some() =>
                {
                    let protocol = self
                        .intrinsic_symbol_iterator_protocol(&property.name)
                        .expect("guard checked iterator protocol");
                    let type_id = self.class_property_type(
                        property.type_annotation.as_ref(),
                        property.initializer.as_deref(),
                        &property.modifiers,
                        scope,
                        false,
                    );
                    Some((
                        protocol,
                        IteratorProperty::new(type_id, property.optional).with_accessibility(
                            property
                                .modifiers
                                .accessibility
                                .unwrap_or(Accessibility::Public),
                            declaring_class,
                        ),
                    ))
                }
                ClassMember::AutoAccessor(accessor)
                    if side.includes(accessor.modifiers.is_static)
                        && self
                            .intrinsic_symbol_iterator_protocol(&accessor.name)
                            .is_some() =>
                {
                    let protocol = self
                        .intrinsic_symbol_iterator_protocol(&accessor.name)
                        .expect("guard checked iterator protocol");
                    let type_id = self.class_property_type(
                        accessor.type_annotation.as_ref(),
                        accessor.initializer.as_deref(),
                        &accessor.modifiers,
                        scope,
                        false,
                    );
                    Some((
                        protocol,
                        IteratorProperty::new(type_id, false)
                            .with_accessibility(
                                accessor
                                    .modifiers
                                    .accessibility
                                    .unwrap_or(Accessibility::Public),
                                declaring_class,
                            )
                            .with_spreadable(false),
                    ))
                }
                ClassMember::Method(method)
                    if side.includes(method.modifiers.is_static)
                        && self
                            .intrinsic_symbol_iterator_protocol(&method.name)
                            .is_some() =>
                {
                    let protocol = self
                        .intrinsic_symbol_iterator_protocol(&method.name)
                        .expect("guard checked iterator protocol");
                    let (type_id, is_method) = match method.modifier {
                        PropertyModifier::None => {
                            let is_overload_signature =
                                method.function.body.is_none() && !method.modifiers.is_abstract;
                            let overload = match protocol {
                                ForOfMode::Sync => &mut iterator_overload,
                                ForOfMode::Async => &mut async_iterator_overload,
                            };
                            if is_overload_signature {
                                *overload = true;
                            } else if *overload {
                                *overload = false;
                                continue;
                            }
                            let signature_scope = self.class_method_signature_scope(
                                member.id(),
                                &method.function,
                                scope,
                            );
                            (
                                self.type_of_function_like_in_scope(
                                    &method.function,
                                    signature_scope,
                                ),
                                true,
                            )
                        }
                        PropertyModifier::Get => {
                            (self.inferred_return_type(&method.function, scope), false)
                        }
                        PropertyModifier::Set => continue,
                    };
                    Some((
                        protocol,
                        IteratorProperty::new(type_id, method.optional)
                            .with_accessibility(
                                method
                                    .modifiers
                                    .accessibility
                                    .unwrap_or(Accessibility::Public),
                                declaring_class,
                            )
                            .with_method(is_method)
                            .with_spreadable(false),
                    ))
                }
                _ => None,
            };
            if let Some((protocol, property)) = intrinsic_iterator {
                let target = match protocol {
                    ForOfMode::Sync => &mut iterator_property,
                    ForOfMode::Async => &mut async_iterator_property,
                };
                *target = Some(match target.take() {
                    None => property,
                    Some(existing) => self.merge_iterator_properties(existing, property),
                });
                continue;
            }
            let (name, type_id, optional, readonly, getter_only, access, is_method) = match member
                .data()
            {
                ClassMember::Property(property) if side.includes(property.modifiers.is_static) => {
                    let Some(name) = self.property_key(&property.name) else {
                        continue;
                    };
                    let type_id = self.class_property_type(
                        property.type_annotation.as_ref(),
                        property.initializer.as_deref(),
                        &property.modifiers,
                        scope,
                        false,
                    );
                    (
                        name,
                        type_id,
                        property.optional,
                        property.modifiers.is_readonly,
                        false,
                        property
                            .modifiers
                            .accessibility
                            .unwrap_or(Accessibility::Public),
                        false,
                    )
                }
                ClassMember::AutoAccessor(accessor)
                    if side.includes(accessor.modifiers.is_static) =>
                {
                    let Some(name) = self.property_key(&accessor.name) else {
                        continue;
                    };
                    let type_id = self.class_property_type(
                        accessor.type_annotation.as_ref(),
                        accessor.initializer.as_deref(),
                        &accessor.modifiers,
                        scope,
                        false,
                    );
                    (
                        name,
                        type_id,
                        false,
                        accessor.modifiers.is_readonly,
                        false,
                        accessor
                            .modifiers
                            .accessibility
                            .unwrap_or(Accessibility::Public),
                        false,
                    )
                }
                ClassMember::Method(method) if side.includes(method.modifiers.is_static) => {
                    match method.modifier {
                        PropertyModifier::None => {
                            let Some(name) = self.property_key(&method.name) else {
                                continue;
                            };
                            if name == "constructor" {
                                continue;
                            }
                            let is_overload_signature =
                                method.function.body.is_none() && !method.modifiers.is_abstract;
                            if is_overload_signature {
                                overload_state.insert(name.clone(), true);
                            } else if overload_state.get(&name).copied().unwrap_or(false) {
                                overload_state.insert(name.clone(), false);
                                continue;
                            }
                            let signature_scope = self.class_method_signature_scope(
                                member.id(),
                                &method.function,
                                scope,
                            );
                            let type_id = self
                                .type_of_function_like_in_scope(&method.function, signature_scope);
                            (
                                name,
                                type_id,
                                method.optional,
                                false,
                                false,
                                method
                                    .modifiers
                                    .accessibility
                                    .unwrap_or(Accessibility::Public),
                                true,
                            )
                        }
                        PropertyModifier::Get => {
                            let Some(name) = self.property_key(&method.name) else {
                                continue;
                            };
                            let type_id = match &method.function.return_type {
                                Some(annotation) => {
                                    self.resolve_type(&annotation.data().type_node, scope)
                                }
                                None => self.types.any(),
                            };
                            let has_setter = class.members.iter().any(|candidate| {
                                let ClassMember::Method(candidate) = candidate.data() else {
                                    return false;
                                };
                                candidate.modifier == PropertyModifier::Set
                                    && side.includes(candidate.modifiers.is_static)
                                    && self.property_key(&candidate.name).as_deref()
                                        == Some(name.as_str())
                            });
                            (
                                name,
                                type_id,
                                method.optional,
                                !has_setter,
                                !has_setter,
                                method
                                    .modifiers
                                    .accessibility
                                    .unwrap_or(Accessibility::Public),
                                false,
                            )
                        }
                        PropertyModifier::Set => continue,
                    }
                }
                _ => continue,
            };
            let _ = seen.insert(name.clone());
            properties.push(
                PropertyType::new(name, optional, type_id)
                    .with_readonly(readonly)
                    .with_getter_only(getter_only)
                    .with_accessibility(access, declaring_class)
                    .with_method(is_method),
            );
        }
        (properties, seen, iterator_property, async_iterator_property)
    }

    fn class_property_type(
        &mut self,
        annotation: Option<&'src TypeAnnotationNode>,
        initializer: Option<&'src Expr>,
        modifiers: &DeclarationModifiers,
        scope: ScopeId,
        diagnose: bool,
    ) -> TypeId {
        if let Some(annotation) = annotation {
            let annotated = self.resolve_type(&annotation.data().type_node, scope);
            if let Some(initializer) = initializer {
                let inferred = if let Some(&cached) = self.node_types.get(&initializer.id()) {
                    cached
                } else if diagnose {
                    self.resolve_expr(initializer, scope);
                    self.type_of_expr_with_target(initializer, annotated, scope)
                } else {
                    return annotated;
                };
                if diagnose && !self.types_assignable(inferred, annotated) {
                    self.emit(
                        TYPE_NOT_ASSIGNABLE,
                        initializer.range(),
                        NOT_ASSIGNABLE_MESSAGE,
                    );
                }
            }
            return annotated;
        }
        let Some(initializer) = initializer else {
            return self.types.any();
        };
        let inferred = if let Some(&cached) = self.node_types.get(&initializer.id()) {
            cached
        } else if diagnose {
            self.resolve_expr(initializer, scope);
            self.type_of_expr(initializer, scope)
        } else if let Expression::Literal(literal) = initializer.data() {
            self.type_of_literal(literal)
        } else {
            return self.types.any();
        };
        if Self::is_fresh_array_literal(initializer) {
            self.types.widen_fresh_literal(inferred)
        } else {
            self.types.widen(inferred, modifiers.is_readonly)
        }
    }

    fn class_instance_type(
        &mut self,
        class: &'src ClassDeclaration,
        scope: ScopeId,
        owner: Option<SymbolId>,
        state: ClassState,
    ) -> TypeId {
        let (mut properties, mut seen, mut iterator_property, mut async_iterator_property) =
            self.class_member_properties(class, scope, ClassSide::Instance);
        for constructor in class.members.iter().filter_map(|member| {
            let ClassMember::Constructor(constructor) = member.data() else {
                return None;
            };
            Some(constructor)
        }) {
            for parameter in &constructor.parameters {
                let parameter = parameter.data();
                if parameter.modifiers.accessibility.is_none() && !parameter.modifiers.is_readonly {
                    continue;
                }
                let BindingPattern::Identifier(identifier) = parameter.binding.data() else {
                    continue;
                };
                let name = self.identifier_text(identifier).into_owned();
                if !seen.insert(name.clone()) {
                    continue;
                }
                let type_id = match &parameter.type_annotation {
                    Some(annotation) => self.resolve_type(&annotation.data().type_node, scope),
                    None => self.types.any(),
                };
                let access = parameter
                    .modifiers
                    .accessibility
                    .unwrap_or(Accessibility::Public);
                let declaring_class = self.scopes[scope.0 as usize].owner;
                properties.push(
                    PropertyType::new(name, parameter.optional, type_id)
                        .with_readonly(parameter.modifiers.is_readonly)
                        .with_accessibility(access, declaring_class),
                );
            }
        }
        // Inherit the base class's instance members. Shape preparation resolves
        // the base expression before this call, so its reference is available.
        // Explicit type arguments in the `extends` clause are resolved
        // and substituted so inherited members use the actual type arguments.
        if let Some(heritage) = &class.extends
            && let Some(base_symbol) = self.resolved_expression_reference(&heritage.expression)
        {
            let explicit: Option<Vec<TypeId>> = heritage.type_arguments.as_ref().map(|list| {
                list.arguments
                    .iter()
                    .map(|argument| self.resolve_type(argument, scope))
                    .collect()
            });
            let base = self.resolve_named_type_symbol(base_symbol);
            let base_instance = self.instantiate_explicit_type_arguments(
                base_symbol,
                explicit.as_deref(),
                base,
                heritage.expression.range(),
            );
            if let Some(base_view) = self.types.prepare_applied_class_view(base_instance)
                && let Type::ObjectType(base_props) = self.types.get(base_view).clone()
            {
                if iterator_property.is_none() {
                    iterator_property = base_props.iterator_property;
                }
                if async_iterator_property.is_none() {
                    async_iterator_property = base_props.async_iterator_property;
                }
                for base_prop in base_props.properties {
                    if seen.insert(base_prop.name().to_string()) {
                        properties.push(base_prop);
                    }
                }
            }
        }
        let raw = self.types.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property,
            async_iterator_property,
        });
        let Some(owner) = owner else {
            return raw;
        };
        match state {
            ClassState::Provisional => self.types.publish_provisional_class_template(owner, raw),
            ClassState::Final => self.types.publish_final_class_template(owner, raw),
        }
        self.types
            .declared_class(owner)
            .unwrap_or_else(|| self.types.applied_class(owner, Vec::new()))
    }

    fn class_static_type(
        &mut self,
        class: &'src ClassDeclaration,
        scope: ScopeId,
        instance_type: TypeId,
    ) -> TypeId {
        let (mut properties, mut seen, mut iterator_property, mut async_iterator_property) =
            self.class_member_properties(class, scope, ClassSide::Static);
        if seen.insert("prototype".to_owned()) {
            let prototype_type = self
                .types
                .prepare_applied_class_view(instance_type)
                .unwrap_or(instance_type);
            properties.push(PropertyType::new("prototype", false, prototype_type));
        }
        let mut base_arguments = Vec::new();
        let base_static = if let Some(heritage) = &class.extends
            && let Some(base_symbol) = self.resolved_expression_reference(&heritage.expression)
        {
            let explicit: Option<Vec<TypeId>> = heritage.type_arguments.as_ref().map(|list| {
                list.arguments
                    .iter()
                    .map(|argument| self.resolve_type(argument, scope))
                    .collect()
            });
            let base = self.resolve_named_type_symbol(base_symbol);
            let base_instance = self.instantiate_explicit_type_arguments(
                base_symbol,
                explicit.as_deref(),
                base,
                heritage.expression.range(),
            );
            if let Type::AppliedClass { arguments, .. } = self.types.get(base_instance).clone() {
                base_arguments = arguments;
            }
            let static_id = self
                .class_constructor_types
                .get(&base_symbol)
                .copied()
                .unwrap_or(self.symbol_types[base_symbol.get() as usize]);
            match self.types.get(static_id).clone() {
                Type::ConstructorType { structural, .. } => {
                    match self.types.get(structural).clone() {
                        Type::ObjectType(object) => Some(object),
                        _ => None,
                    }
                }
                Type::ObjectType(object) => Some(object),
                _ => None,
            }
        } else {
            None
        };
        if let Some(base_static) = &base_static {
            for base_property in &base_static.properties {
                if base_property.name() != "prototype"
                    && seen.insert(base_property.name().to_owned())
                {
                    properties.push(base_property.clone());
                }
            }
        }
        if iterator_property.is_none() {
            iterator_property = base_static
                .as_ref()
                .and_then(|object| object.iterator_property.clone());
        }
        if async_iterator_property.is_none() {
            async_iterator_property = base_static
                .as_ref()
                .and_then(|object| object.async_iterator_property.clone());
        }
        let construct_signatures = self.class_construct_signatures(
            class,
            scope,
            instance_type,
            base_static.as_ref(),
            &base_arguments,
        );
        let structural = self.types.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures,
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property,
            async_iterator_property,
        });
        let owner = self.scopes[scope.0 as usize].owner;
        match owner {
            // tsc renders `typeof C` without type arguments for user-defined
            // generic classes; the type parameters are carried by the
            // structural construct signatures.
            Some(symbol) => self.types.constructor_type(symbol, Vec::new(), structural),
            None => structural,
        }
    }

    fn class_construct_signatures(
        &mut self,
        class: &'src ClassDeclaration,
        scope: ScopeId,
        instance_type: TypeId,
        base_static: Option<&ObjectType>,
        base_arguments: &[TypeId],
    ) -> Vec<ConstructEntry> {
        let overloads: Vec<_> = class
            .members
            .iter()
            .filter_map(|member| {
                let ClassMember::Method(method) = member.data() else {
                    return None;
                };
                if method.modifier != PropertyModifier::None
                    || method.modifiers.is_static
                    || method.function.body.is_some()
                    || self.property_key(&method.name).as_deref() != Some("constructor")
                {
                    return None;
                }
                Some(method.function.parameters.as_slice())
            })
            .collect();
        if !overloads.is_empty() {
            return overloads
                .into_iter()
                .map(|parameters| {
                    self.class_construct_entry(class, parameters, scope, instance_type)
                })
                .collect();
        }
        if let Some(parameters) = class.members.iter().find_map(|member| match member.data() {
            ClassMember::Constructor(constructor) => Some(constructor.parameters.as_slice()),
            _ => None,
        }) {
            return vec![self.class_construct_entry(class, parameters, scope, instance_type)];
        }
        if let Some(base_static) = base_static
            && !base_static.construct_signatures.is_empty()
        {
            let mut inherited = Vec::with_capacity(base_static.construct_signatures.len());
            for entry in &base_static.construct_signatures {
                let javascript = entry.signature.javascript;
                let mut signature =
                    if entry.signature.type_parameters.is_empty() || base_arguments.is_empty() {
                        entry.signature.clone()
                    } else {
                        let arguments = entry
                            .signature
                            .type_parameters
                            .iter()
                            .copied()
                            .zip(base_arguments.iter().copied())
                            .map(|(symbol, type_id)| {
                                InferredTypeArgument::new(
                                    symbol,
                                    type_id,
                                    InferenceProvenance::Explicit,
                                )
                            })
                            .collect();
                        let type_id = InferredTypeArguments::new(arguments)
                            .instantiate_signature(&mut self.types, &entry.signature);
                        let Type::Function(signature) = self.types.get(type_id) else {
                            unreachable!("instantiated constructor must remain a function");
                        };
                        signature.clone()
                    };
                signature.javascript = javascript;
                signature.return_type = instance_type;
                inherited.push(ConstructEntry {
                    signature,
                    is_abstract: class.modifiers.is_abstract,
                });
            }
            return inherited;
        }
        vec![self.class_construct_entry(class, &[], scope, instance_type)]
    }

    fn class_construct_entry(
        &mut self,
        class: &'src ClassDeclaration,
        parameters: &'src [ParameterNode],
        scope: ScopeId,
        instance_type: TypeId,
    ) -> ConstructEntry {
        let signature_type = self.signature_type_with_return(
            class.type_parameters.as_ref(),
            parameters,
            instance_type,
            scope,
        );
        let Type::Function(signature) = self.types.get(signature_type) else {
            unreachable!("class constructor signature must be a function type");
        };
        ConstructEntry {
            signature: signature.clone(),
            is_abstract: class.modifiers.is_abstract,
        }
    }

    fn constructor_property_assignments(
        &self,
        members: &'src [crate::syntax::ClassMemberNode],
    ) -> HashSet<String> {
        let mut assigned = HashSet::new();
        let Some(constructor) = members.iter().find_map(|member| {
            if let ClassMember::Constructor(constructor) = member.data() {
                Some(constructor)
            } else {
                None
            }
        }) else {
            return assigned;
        };
        for parameter in &constructor.parameters {
            let parameter = parameter.data();
            if (parameter.modifiers.accessibility.is_some() || parameter.modifiers.is_readonly)
                && let BindingPattern::Identifier(identifier) = parameter.binding.data()
            {
                assigned.insert(self.identifier_text(identifier).into_owned());
            }
        }
        for statement in &constructor.body.data().statements {
            if let Statement::Expression(expression) = statement.data()
                && let Expression::Assignment(assignment) = expression.expression.data()
                && let AssignmentTarget::Member(member) = assignment.left.data()
                && matches!(member.object.data(), Expression::This)
                && let MemberProperty::Named(ident) = &member.property
            {
                assigned.insert(self.identifier_text(ident).into_owned());
            }
        }
        assigned
    }

    fn property_name_range(name: &crate::syntax::PropertyName) -> crate::source::TextRange {
        match name {
            crate::syntax::PropertyName::Identifier(identifier) => identifier.range(),
            crate::syntax::PropertyName::Private(identifier) => identifier.range(),
            crate::syntax::PropertyName::String(literal) => literal.range(),
            crate::syntax::PropertyName::Number(literal) => literal.range(),
            crate::syntax::PropertyName::Computed(expression) => expression.range(),
            crate::syntax::PropertyName::Missing(_) => crate::source::TextRange::new(
                crate::source::Utf16Pos::ZERO,
                crate::source::Utf16Pos::ZERO,
            )
            .unwrap(),
        }
    }

    /// Returns the bare name span for a renameable property key. Quotes are
    /// stripped from string keys; every other form fails closed.
    fn property_bare_range(name: &PropertyName) -> Option<TextRange> {
        match name {
            PropertyName::Identifier(identifier) => Some(identifier.range()),
            PropertyName::String(literal) => {
                let range = literal.range();
                let start = range.start().get().checked_add(1)?;
                let end = range.end().get().checked_sub(1)?;
                TextRange::new(
                    crate::source::Utf16Pos::new(start),
                    crate::source::Utf16Pos::new(end),
                )
                .ok()
            }
            _ => None,
        }
    }

    /// Returns the bare string-literal interior for a bracket access key.
    fn bracket_bare_range(expression: &Expr) -> Option<TextRange> {
        let Expression::Literal(Literal::String(literal)) = expression.data() else {
            return None;
        };
        let range = literal.range();
        let start = range.start().get().checked_add(1)?;
        let end = range.end().get().checked_sub(1)?;
        TextRange::new(
            crate::source::Utf16Pos::new(start),
            crate::source::Utf16Pos::new(end),
        )
        .ok()
    }

    /// Whether a canonical property name has identifier shape. Numeric and
    /// otherwise non-identifier keys never participate in rename.
    fn is_property_identifier(name: &str) -> bool {
        let mut characters = name.chars();
        let Some(first) = characters.next() else {
            return false;
        };
        (first.is_alphabetic() || first == '_' || first == '$')
            && characters.all(|character| {
                character.is_alphanumeric() || character == '_' || character == '$'
            })
    }

    /// Interns `(owner, name)` and returns its stable [`PropertyId`].
    fn record_property_site(&mut self, owner: PropertyOwner, name: &str) -> PropertyId {
        let key = (owner, Box::<str>::from(name));
        if let Some(&id) = self.property_site_index.get(&key) {
            return id;
        }
        let id = PropertyId(self.property_sites.len());
        self.property_sites.push(PropertySite {
            name: key.1.clone(),
            owner: key.0,
        });
        self.property_site_index.insert(key, id);
        id
    }

    /// Records one property occurrence for rename. Invariant A is enforced
    /// here: the source text at the bare span must equal the canonical name
    /// byte-for-byte, otherwise the anchor is silently dropped (fail-closed
    /// for escaped identifiers, escaped string keys, and numeric keys).
    fn record_property_anchor(
        &mut self,
        owner: PropertyOwner,
        name: &str,
        range: TextRange,
        kind: PropertyAnchorKind,
        declaration: bool,
    ) {
        if !Self::is_property_identifier(name) {
            return;
        }
        let text = self.source.source_text();
        let Some(start) = text.utf16_to_byte(range.start()).ok() else {
            return;
        };
        let Some(end) = text.utf16_to_byte(range.end()).ok() else {
            return;
        };
        if text.as_str().get(start..end) != Some(name) {
            return;
        }
        let property_id = self.record_property_site(owner, name);
        if self.property_anchor_index.contains_key(&range) {
            return;
        }
        let index = self.property_anchors.len();
        self.property_anchor_index.insert(range, index);
        self.property_anchors.push(PropertyAnchor {
            range,
            property_id,

            kind,
            declaration,
        });
    }

    /// Resolves a type annotation node to its named declaration owner.
    fn anchor_of_type_node(&self, node: &Ty, scope: ScopeId) -> Option<PropertyOwner> {
        match node.data() {
            TypeNode::Reference(reference) => {
                let EntityName::Identifier(identifier) = &reference.name else {
                    return None;
                };
                let name = self.identifier_text(identifier);
                let symbol = self.lookup_type(scope, name.as_ref())?;
                let kind = self.symbols[symbol.get() as usize].kind();
                matches!(
                    kind,
                    SymbolKind::Interface | SymbolKind::Class | SymbolKind::Namespace
                )
                .then_some(PropertyOwner::Member(symbol))
            }
            TypeNode::Parenthesized(inner) => self.anchor_of_type_node(inner, scope),
            _ => None,
        }
    }

    /// Resolves an interned type to its declaration owner for member
    /// access anchoring.
    fn owner_of_named_type(&self, type_id: TypeId) -> Option<PropertyOwner> {
        match self.types.get(type_id) {
            Type::Named(symbol)
                if matches!(
                    self.symbols[symbol.get() as usize].kind(),
                    SymbolKind::Interface | SymbolKind::Class | SymbolKind::Namespace
                ) =>
            {
                Some(PropertyOwner::Member(*symbol))
            }
            Type::AppliedClass { symbol, .. } => Some(PropertyOwner::Member(*symbol)),
            Type::This { owner, .. } => Some(PropertyOwner::Member(*owner)),
            _ => None,
        }
    }

    fn check_set_accessor_parameter_initializer(
        &mut self,
        modifier: PropertyModifier,
        parameters: &[ParameterNode],
        name: &PropertyName,
    ) {
        if modifier != PropertyModifier::Set {
            return;
        }
        if parameters
            .iter()
            .any(|parameter| parameter.data().initializer.is_some())
        {
            self.emit(
                SET_ACCESSOR_PARAMETER_INITIALIZER,
                Self::property_name_range(name),
                SET_ACCESSOR_PARAMETER_INITIALIZER_MESSAGE,
            );
        }
    }
    fn check_accessor_this_parameter(
        &mut self,
        modifier: PropertyModifier,
        parameters: &'src [ParameterNode],
        name: &PropertyName,
    ) {
        if !matches!(modifier, PropertyModifier::Get | PropertyModifier::Set) {
            return;
        }
        if parameters
            .iter()
            .any(|parameter| self.is_this_parameter(parameter))
        {
            self.emit(
                ACCESSOR_THIS_PARAMETER,
                Self::property_name_range(name),
                ACCESSOR_THIS_PARAMETER_MESSAGE,
            );
        }
    }

    fn check_get_accessor(
        &mut self,
        modifier: PropertyModifier,
        function: &'src FunctionLike,
        name: &PropertyName,
    ) {
        if modifier != PropertyModifier::Get {
            return;
        }
        let range = Self::property_name_range(name);
        if function
            .parameters
            .iter()
            .any(|parameter| !self.is_this_parameter(parameter))
        {
            self.emit(
                GET_ACCESSOR_PARAMETERS,
                range,
                GET_ACCESSOR_PARAMETERS_MESSAGE,
            );
        }
        // Only a real block body can be inspected for a missing return.
        // Bodyless getters — including the parser's tolerated `get foo()`
        // recovery and missing-body recovery nodes — stay silent, matching
        // upstream's accessorWithoutBody1 expectation of zero diagnostics.
        if !matches!(
            function.body.as_ref(),
            Some(crate::syntax::FunctionBody::Block(_))
        ) {
            return;
        }
        if !Self::function_body_returns_value(function) {
            self.emit(
                GET_ACCESSOR_NO_RETURN,
                range,
                GET_ACCESSOR_NO_RETURN_MESSAGE,
            );
        }
    }

    fn function_body_returns_value(function: &'src FunctionLike) -> bool {
        match function.body.as_ref() {
            Some(crate::syntax::FunctionBody::Block(block)) => {
                Self::block_returns_value(block.data())
            }
            Some(crate::syntax::FunctionBody::Expression(_)) => true,
            _ => false,
        }
    }

    /// Whether control can never fall out of `statement`, so a flow branch
    /// ending in it contributes no facts to the merge after it.
    ///
    /// Conservative by construction: an unmodelled construct answers `false`,
    /// which costs narrowing precision rather than soundness.
    fn statement_always_exits(statement: &'src Statement) -> bool {
        match statement {
            Statement::Return(_)
            | Statement::Throw(_)
            | Statement::Break(_)
            | Statement::Continue(_) => true,
            Statement::Block(block) => block
                .data()
                .statements
                .iter()
                .any(|stmt| Self::statement_always_exits(stmt.data())),
            Statement::Labeled(labeled) => Self::statement_always_exits(labeled.body.data()),
            Statement::If(if_stmt) => {
                Self::statement_always_exits(if_stmt.consequent.data())
                    && if_stmt
                        .alternate
                        .as_ref()
                        .is_some_and(|alt| Self::statement_always_exits(alt.data()))
            }
            Statement::For(for_stmt) => {
                for_stmt
                    .test
                    .as_ref()
                    .is_none_or(|test| Self::is_true_literal(test.data()))
                    && !Self::loop_body_has_unlabeled_break(for_stmt.body.data(), 0)
            }
            Statement::While(while_stmt) => {
                Self::is_true_literal(while_stmt.test.data())
                    && !Self::loop_body_has_unlabeled_break(while_stmt.body.data(), 0)
            }
            Statement::DoWhile(do_while) => {
                Self::is_true_literal(do_while.test.data())
                    && !Self::loop_body_has_unlabeled_break(do_while.body.data(), 0)
            }
            _ => false,
        }
    }

    fn is_true_literal(expression: &Expression) -> bool {
        matches!(
            expression,
            Expression::Literal(Literal::Boolean(literal))
                if literal.data().token().kind() == TokenKind::KwTrue
        )
    }

    fn loop_body_has_unlabeled_break(statement: &'src Statement, depth: usize) -> bool {
        let nested =
            |statement: &'src Statement| Self::loop_body_has_unlabeled_break(statement, depth + 1);
        match statement {
            Statement::Break(jump) => jump.label.is_none() && depth == 0,
            Statement::Block(block) => block
                .data()
                .statements
                .iter()
                .any(|statement| Self::loop_body_has_unlabeled_break(statement.data(), depth)),
            Statement::If(if_stmt) => {
                Self::loop_body_has_unlabeled_break(if_stmt.consequent.data(), depth)
                    || if_stmt.alternate.as_ref().is_some_and(|alternate| {
                        Self::loop_body_has_unlabeled_break(alternate.data(), depth)
                    })
            }
            Statement::Switch(switch_stmt) => switch_stmt.cases.iter().any(|case| {
                case.data()
                    .consequent
                    .iter()
                    .any(|statement| nested(statement.data()))
            }),
            Statement::For(for_stmt) => nested(for_stmt.body.data()),
            Statement::ForIn(for_stmt) => nested(for_stmt.body.data()),
            Statement::ForOf(for_stmt) => nested(for_stmt.body.data()),
            Statement::While(while_stmt) => nested(while_stmt.body.data()),
            Statement::DoWhile(do_while) => nested(do_while.body.data()),
            Statement::Try(try_stmt) => {
                try_stmt
                    .block
                    .data()
                    .statements
                    .iter()
                    .any(|statement| Self::loop_body_has_unlabeled_break(statement.data(), depth))
                    || try_stmt.handler.as_ref().is_some_and(|handler| {
                        handler
                            .data()
                            .body
                            .data()
                            .statements
                            .iter()
                            .any(|statement| {
                                Self::loop_body_has_unlabeled_break(statement.data(), depth)
                            })
                    })
                    || try_stmt.finalizer.as_ref().is_some_and(|finalizer| {
                        finalizer.data().statements.iter().any(|statement| {
                            Self::loop_body_has_unlabeled_break(statement.data(), depth)
                        })
                    })
            }
            Statement::With(with_stmt) => {
                Self::loop_body_has_unlabeled_break(with_stmt.body.data(), depth)
            }
            Statement::Labeled(labeled) => {
                Self::loop_body_has_unlabeled_break(labeled.body.data(), depth)
            }
            _ => false,
        }
    }

    fn block_returns_value(block: &'src crate::syntax::Block) -> bool {
        block
            .statements
            .iter()
            .any(|stmt| Self::statement_returns_value(stmt.data()))
    }

    fn statement_returns_value(statement: &'src Statement) -> bool {
        match statement {
            Statement::Return(ret) => ret.argument.is_some(),
            Statement::Throw(_) => true,
            Statement::Block(block) => Self::block_returns_value(block.data()),
            Statement::Labeled(labeled) => Self::statement_returns_value(labeled.body.data()),
            Statement::If(if_stmt) => {
                Self::statement_returns_value(if_stmt.consequent.data())
                    && if_stmt
                        .alternate
                        .as_ref()
                        .is_some_and(|alt| Self::statement_returns_value(alt.data()))
            }
            Statement::Switch(switch) => {
                let cases = &switch.cases;
                let has_default = cases.iter().any(|case| case.data().test.is_none());
                has_default
                    && cases.iter().all(|case| {
                        case.data()
                            .consequent
                            .iter()
                            .any(|s| Self::statement_returns_value(s.data()))
                    })
            }
            Statement::Try(try_stmt) => {
                let handler_returns = try_stmt
                    .handler
                    .as_ref()
                    .is_some_and(|h| Self::block_returns_value(h.data().body.data()));
                Self::block_returns_value(try_stmt.block.data()) && handler_returns
            }
            Statement::For(_)
            | Statement::ForIn(_)
            | Statement::ForOf(_)
            | Statement::While(_)
            | Statement::DoWhile(_) => false,
            _ => false,
        }
    }
    fn bind_class_member(&mut self, member: &'src crate::syntax::ClassMemberNode, scope: ScopeId) {
        let owner = self
            .scopes
            .get(scope.0 as usize)
            .and_then(|scope| scope.owner)
            .map(PropertyOwner::Member);
        let anchor = |binder: &mut Self, name: &str, property_name: &PropertyName| {
            if let (Some(owner), Some(bare)) = (owner, Self::property_bare_range(property_name)) {
                binder.record_property_anchor(owner, name, bare, PropertyAnchorKind::Plain, true);
            }
        };
        match member.data() {
            ClassMember::Property(property) => {
                if let Some(name) = self.member_symbol_key(&property.name) {
                    self.declare(
                        &name,
                        SymbolKind::Variable(VariableKind::Let),
                        scope,
                        member.id(),
                        Self::property_name_range(&property.name),
                    );
                    anchor(self, &name, &property.name);
                }
            }
            ClassMember::AutoAccessor(accessor) => {
                if let Some(name) = self.member_symbol_key(&accessor.name) {
                    self.declare(
                        &name,
                        SymbolKind::Variable(VariableKind::Let),
                        scope,
                        member.id(),
                        Self::property_name_range(&accessor.name),
                    );
                    anchor(self, &name, &accessor.name);
                }
            }
            ClassMember::Method(method) if method.modifier == PropertyModifier::None => {
                if let Some(name) = self.member_symbol_key(&method.name) {
                    self.declare(
                        &name,
                        SymbolKind::Function,
                        scope,
                        member.id(),
                        Self::property_name_range(&method.name),
                    );
                    anchor(self, &name, &method.name);
                }
            }
            ClassMember::IndexSignature(index) => {
                // Upstream renders index-signature parameters as bare
                // `>s : Symbol(s, Decl(...))` rows (classIndexer.symbols), so
                // each parameter binds in a fresh function scope.
                let parameter_scope = self.new_scope(ScopeKind::Function, Some(scope));
                for parameter in &index.parameters {
                    if self.is_this_parameter(parameter) {
                        continue;
                    }
                    self.bind_pattern(
                        &parameter.data().binding,
                        VariableKind::Let,
                        parameter_scope,
                        parameter.id(),
                    );
                }
            }
            ClassMember::Method(_)
            | ClassMember::Constructor(_)
            | ClassMember::StaticBlock(_)
            | ClassMember::Missing(_) => {}
        }
    }

    fn class_this_type(&mut self, scope: ScopeId, is_static: bool) -> TypeId {
        let Some(owner) = self.scopes[scope.0 as usize].owner else {
            return self.types.any();
        };
        if is_static {
            self.class_constructor_types
                .get(&owner)
                .copied()
                .unwrap_or(self.symbol_types[owner.get() as usize])
        } else {
            let instance = self
                .class_instance_types
                .get(&owner)
                .copied()
                .unwrap_or_else(|| self.types.any());
            self.types.this_type(owner, instance)
        }
    }

    fn resolve_class_member(&mut self, member: &'src ClassMember, scope: ScopeId, ambient: bool) {
        match member {
            ClassMember::Method(method) => {
                self.resolve_property_name(&method.name, scope);
                self.check_set_accessor_parameter_initializer(
                    method.modifier,
                    &method.function.parameters,
                    &method.name,
                );
                self.check_accessor_this_parameter(
                    method.modifier,
                    &method.function.parameters,
                    &method.name,
                );
                self.check_get_accessor(method.modifier, &method.function, &method.name);
                if let PropertyName::Identifier(identifier) = &method.name
                    && self.identifier_text(identifier).as_ref() == "constructor"
                    && let Some(type_parameters) = &method.function.type_parameters
                {
                    let range = type_parameters
                        .parameters
                        .first()
                        .map(|parameter| parameter.range())
                        .unwrap_or_else(|| Self::property_name_range(&method.name));
                    self.emit(
                        CONSTRUCTOR_TYPE_PARAMETERS,
                        range,
                        CONSTRUCTOR_TYPE_PARAMETERS_MESSAGE,
                    );
                }
                if ambient && method.function.body.is_some() {
                    let range = method
                        .function
                        .body
                        .as_ref()
                        .map(|body| match body {
                            crate::syntax::FunctionBody::Block(block) => block.range(),
                            crate::syntax::FunctionBody::Expression(expression) => {
                                expression.range()
                            }
                            crate::syntax::FunctionBody::Missing(_) => {
                                Self::property_name_range(&method.name)
                            }
                        })
                        .unwrap_or_else(|| Self::property_name_range(&method.name));
                    self.emit(
                        AMBIENT_IMPLEMENTATION,
                        range,
                        AMBIENT_IMPLEMENTATION_MESSAGE,
                    );
                }
                let this_type = self.class_this_type(scope, method.modifiers.is_static);
                let derived = self.class_derived_stack.last().copied().unwrap_or(false);
                self.resolve_function(
                    &method.function,
                    scope,
                    false,
                    true,
                    this_type,
                    SuperMemberHome::ClassMember { derived },
                );
            }
            ClassMember::Constructor(constructor) => {
                if ambient {
                    self.emit(
                        AMBIENT_IMPLEMENTATION,
                        constructor.body.range(),
                        AMBIENT_IMPLEMENTATION_MESSAGE,
                    );
                }
                self.resolve_unsupported_legacy_decorators(
                    &constructor.decorators,
                    CONSTRUCTOR_DECORATOR_NOT_SUPPORTED,
                    CONSTRUCTOR_DECORATOR_NOT_SUPPORTED_MESSAGE,
                    scope,
                );
                let derived = self.class_derived_stack.last().copied().unwrap_or(false);
                let child = self.new_scope(ScopeKind::Function, Some(scope));
                let new_target_marker = self.new_target_contexts.len();
                self.new_target_contexts.push(true);
                self.bind_implicit_function_values(&constructor.parameters, child);
                self.super_call_contexts
                    .push(SuperCallContext::ConstructorParameters { derived });
                for parameter in &constructor.parameters {
                    if self.is_parameter_property(parameter) {
                        self.resolve_parameter_property(parameter, child, scope);
                    } else {
                        self.resolve_parameter(parameter, child);
                    }
                }
                let popped_parameters = self.super_call_contexts.pop();
                debug_assert_eq!(
                    popped_parameters,
                    Some(SuperCallContext::ConstructorParameters { derived })
                );
                let track_super = derived && !ambient && !constructor.body.range().is_empty();
                if track_super {
                    self.derived_constructor_super_presence.push(false);
                }
                self.super_member_homes
                    .push(SuperMemberHome::ClassMember { derived });
                self.super_call_contexts.push(if derived {
                    SuperCallContext::DerivedConstructor
                } else {
                    SuperCallContext::BaseConstructor
                });
                let this_type = self.class_this_type(scope, false);
                self.this_context.push(this_type);
                self.push_reassigned_scope();
                self.in_isolated_flow(FlowNodeId::ROOT, |binder| {
                    binder.bind_statements(&constructor.body.data().statements, child);
                    binder.resolve_statements(&constructor.body.data().statements, child);
                });
                if track_super {
                    let called = self
                        .derived_constructor_super_presence
                        .pop()
                        .expect("tracked derived constructor has a presence entry");
                    if !called {
                        self.emit(
                            DERIVED_CONSTRUCTOR_MISSING_SUPER,
                            constructor.body.range(),
                            DERIVED_CONSTRUCTOR_MISSING_SUPER_MESSAGE,
                        );
                    }
                }
                self.pop_reassigned_scope();
                self.this_context.pop();
                self.new_target_contexts.truncate(new_target_marker);
                self.super_call_contexts.pop();
                let popped_home = self.super_member_homes.pop();
                debug_assert_eq!(popped_home, Some(SuperMemberHome::ClassMember { derived }));
            }
            ClassMember::Property(property) => {
                self.resolve_property_name(&property.name, scope);
                let derived = self.class_derived_stack.last().copied().unwrap_or(false);
                self.super_member_homes
                    .push(SuperMemberHome::ClassMember { derived });
                let type_id = self.class_property_type(
                    property.type_annotation.as_ref(),
                    property.initializer.as_deref(),
                    &property.modifiers,
                    scope,
                    true,
                );
                let popped_home = self.super_member_homes.pop();
                debug_assert_eq!(popped_home, Some(SuperMemberHome::ClassMember { derived }));
                if let Some(name) = self.property_key(&property.name)
                    && let Some(&symbol) = self.scopes[scope.0 as usize].values.get(&name)
                {
                    self.symbol_types[symbol.get() as usize] = type_id;
                }
            }
            ClassMember::AutoAccessor(accessor) => {
                self.resolve_property_name(&accessor.name, scope);
                let derived = self.class_derived_stack.last().copied().unwrap_or(false);
                self.super_member_homes
                    .push(SuperMemberHome::ClassMember { derived });
                let type_id = self.class_property_type(
                    accessor.type_annotation.as_ref(),
                    accessor.initializer.as_deref(),
                    &accessor.modifiers,
                    scope,
                    true,
                );
                let popped_home = self.super_member_homes.pop();
                debug_assert_eq!(popped_home, Some(SuperMemberHome::ClassMember { derived }));
                if let Some(name) = self.property_key(&accessor.name)
                    && let Some(&symbol) = self.scopes[scope.0 as usize].values.get(&name)
                {
                    self.symbol_types[symbol.get() as usize] = type_id;
                }
            }
            ClassMember::StaticBlock(block) => {
                let child = self.new_scope(ScopeKind::Block, Some(scope));
                let new_target_marker = self.new_target_contexts.len();
                self.new_target_contexts.push(false);
                let derived = self.class_derived_stack.last().copied().unwrap_or(false);
                self.super_member_homes
                    .push(SuperMemberHome::ClassMember { derived });
                self.bind_statements(&block.data().statements, child);
                self.resolve_statements(&block.data().statements, child);
                let popped_home = self.super_member_homes.pop();
                debug_assert_eq!(popped_home, Some(SuperMemberHome::ClassMember { derived }));
                self.new_target_contexts.truncate(new_target_marker);
            }
            _ => {}
        }
    }

    fn resolve_property_name(&mut self, name: &'src PropertyName, scope: ScopeId) {
        if let PropertyName::Computed(expression) = name {
            self.resolve_expr(expression, scope);
        }
    }

    pub(crate) fn resolve_expr(&mut self, expression: &'src Expr, scope: ScopeId) {
        match expression.data() {
            Expression::Identifier(identifier) => {
                self.resolve_value(identifier, expression.id(), scope);
            }
            Expression::This => {
                let owner =
                    self.this_context
                        .last()
                        .and_then(|type_id| match self.types.get(*type_id) {
                            Type::This { owner, .. } => Some(*owner),
                            _ => None,
                        });
                if let Some(owner) = owner {
                    self.references.insert(expression.id(), owner);
                    self.symbol_references.push((expression.range(), owner));
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(inner) => self.resolve_expr(inner, scope),
                        ArrayElement::Spread(spread) => self.resolve_expr(&spread.argument, scope),
                        _ => {}
                    }
                }
            }
            Expression::Object(object) => {
                for member in &object.members {
                    self.resolve_object_member(member.data(), scope);
                }
            }
            Expression::Function(function) => {
                self.resolve_function(
                    &function.function,
                    scope,
                    true,
                    false,
                    self.types.any(),
                    SuperMemberHome::NonMemberFunction,
                );
                let type_id = self.type_of_function_like(&function.function, scope);
                if self.node_types.insert(expression.id(), type_id).is_none() {
                    self.typed_expressions.push((expression.range(), type_id));
                }
            }
            Expression::Class(class) => {
                let type_id = self.resolve_class_expression(&class.class, scope);
                if self.node_types.insert(expression.id(), type_id).is_none() {
                    self.typed_expressions.push((expression.range(), type_id));
                }
            }
            Expression::Arrow(arrow) => {
                let child = self.new_scope(ScopeKind::Function, Some(scope));
                // Arrows capture `this` but never inherit super-call legality.
                self.super_call_contexts
                    .push(SuperCallContext::NonConstructor);
                self.bind_type_parameters(arrow.type_parameters.as_ref(), child);
                for parameter in &arrow.parameters {
                    self.resolve_non_constructor_parameter(parameter, child);
                }
                let expected_return_type = arrow.return_type.as_ref().map(|annotation| {
                    let return_type = self.resolve_type(&annotation.data().type_node, child);
                    if arrow.is_async {
                        self.awaited_type(return_type)
                    } else {
                        return_type
                    }
                });
                self.return_contexts.push(ReturnContext {
                    expected: expected_return_type,
                    await_expression: arrow.is_async,
                    generator_protocol: None,
                });
                let block_body_id = match &arrow.body {
                    FunctionBody::Block(block) => {
                        let body_id = block.id();
                        self.return_types.entry(body_id).or_default();
                        self.function_body_stack.push(body_id);
                        Some(body_id)
                    }
                    FunctionBody::Expression(_) | FunctionBody::Missing(_) => None,
                };
                let body_flow = self.captured_flow_seed();
                self.push_reassigned_scope();
                self.in_isolated_flow(body_flow, |binder| match &arrow.body {
                    FunctionBody::Block(block) => {
                        if directive_prologue_is_strict(binder.source, &block.data().statements) {
                            binder.scopes[child.0 as usize].strict = true;
                        }
                        binder.bind_statements(&block.data().statements, child);
                        binder.bind_hoisted_statements(&block.data().statements, child);
                        binder.resolve_statements(&block.data().statements, child);
                    }
                    FunctionBody::Expression(inner) => {
                        binder.resolve_expr(inner, child);
                        if let Some(expected) = binder
                            .return_contexts
                            .last()
                            .and_then(|context| context.expected)
                        {
                            let actual = binder.type_of_expr_with_target(inner, expected, child);
                            let actual = if arrow.is_async {
                                binder.awaited_type(actual)
                            } else {
                                actual
                            };
                            if !binder.types_assignable(actual, expected) {
                                binder.emit(
                                    TYPE_NOT_ASSIGNABLE,
                                    inner.range(),
                                    NOT_ASSIGNABLE_MESSAGE,
                                );
                            }
                        }
                    }
                    FunctionBody::Missing(_) => {}
                });
                let annotation = arrow
                    .return_type
                    .as_ref()
                    .map(|node| node.data().type_node.range());
                self.check_annotated_return_fallthrough(
                    &arrow.body,
                    expected_return_type,
                    annotation,
                );
                self.pop_reassigned_scope();
                if let Some(body_id) = block_body_id {
                    let popped = self.function_body_stack.pop();
                    debug_assert_eq!(popped, Some(body_id));
                }
                self.return_contexts.pop();
                let popped_context = self.super_call_contexts.pop();
                debug_assert_eq!(popped_context, Some(SuperCallContext::NonConstructor));
                let type_id = self.type_of_arrow(arrow, scope);
                if self.node_types.insert(expression.id(), type_id).is_none() {
                    self.typed_expressions.push((expression.range(), type_id));
                }
            }
            Expression::Call(call) => {
                if matches!(call.callee.data(), Expression::Super) {
                    self.check_super_call(call.callee.range());
                } else {
                    self.resolve_expr(&call.callee, scope);
                }
                self.resolve_type_arguments(call.type_arguments.as_ref(), scope);
                self.resolve_arguments(&call.arguments, scope);
                self.check_call(call, scope, expression.range());
            }
            Expression::New(new) => {
                self.resolve_expr(&new.callee, scope);
                self.resolve_type_arguments(new.type_arguments.as_ref(), scope);
                self.resolve_arguments(&new.arguments, scope);
                self.check_new(new, scope, expression.range());
            }
            Expression::Member(member) => {
                if matches!(member.object.data(), Expression::Super) {
                    self.check_super_member_access(member.object.range(), member.optional);
                } else {
                    self.resolve_expr(&member.object, scope);
                    // A property read dereferences its object, so a nullable
                    // object is rejected. Optional chaining tests for null
                    // rather than dereferencing, so it accepts one.
                    if !member.optional {
                        self.check_non_null_operand(&member.object, scope);
                    }
                }
                let object_symbol = self.resolved_expression_reference(&member.object);
                if let MemberProperty::Computed(inner) = &member.property {
                    self.resolve_expr(inner, scope);
                }
                if member.optional {
                    return;
                }
                let Some(name) =
                    enum_plan::cook_member_property_name(self.source, &member.property)
                else {
                    return;
                };
                if let Some(enum_symbol) = object_symbol
                    && self.symbols[enum_symbol.get() as usize].kind == SymbolKind::Enum
                    && let Some(member_symbol) = self
                        .enum_member_symbols_by_name
                        .get(&enum_symbol)
                        .and_then(|members| members.get(&name))
                        .copied()
                {
                    self.references.insert(expression.id(), member_symbol);
                    self.enum_member_identifier_uses.insert(expression.id());
                    return;
                }
                // Symbol-direct path only: computing member types here would
                // drag the typing pass ahead of function-body resolution and
                // poison arrow return inference. Instance-typed objects are
                // recorded from the typing phase instead (see
                // `record_member_reference_rows`).
                if let Some(object_symbol) = object_symbol
                    && matches!(
                        self.symbols[object_symbol.get() as usize].kind,
                        SymbolKind::Class | SymbolKind::Interface
                    )
                    && !self.member_reference_recorded.contains(&expression.id())
                {
                    self.record_symbol_member_reference_rows(
                        object_symbol,
                        &member.property,
                        expression.range(),
                    );
                    self.member_reference_recorded.insert(expression.id());
                }
                let base = object_symbol
                    .filter(|symbol| self.symbols[symbol.get() as usize].kind == SymbolKind::Import)
                    .map(enum_plan::ImportedEnumMemberBase::Import)
                    .or_else(|| {
                        self.imported_enum_member_uses
                            .contains_key(&member.object.id())
                            .then_some(enum_plan::ImportedEnumMemberBase::MemberResult(
                                member.object.id(),
                            ))
                    });
                if let Some(base) = base {
                    self.imported_enum_member_uses.insert(
                        expression.id(),
                        enum_plan::ImportedEnumMemberUse::new(base, name, expression.range()),
                    );
                }
            }
            Expression::Await(await_expression) => {
                self.resolve_expr(&await_expression.argument, scope);
            }
            Expression::Yield(yield_expression) => {
                if let Some(argument) = &yield_expression.argument {
                    self.resolve_expr(argument, scope);
                }
                let protocol = self
                    .return_contexts
                    .last()
                    .and_then(|context| context.generator_protocol);
                if let Some(protocol) = protocol
                    && let Some(body_id) = self.function_body_stack.last().copied()
                {
                    let yield_type = if yield_expression.delegate {
                        match &yield_expression.argument {
                            Some(argument) => {
                                let iterable = self.type_of_expr(argument, scope);
                                match self.iteration_element_type(iterable, protocol) {
                                    Some(element) => element,
                                    None => {
                                        self.emit(
                                            FOR_OF_ITERABLE_REQUIRED,
                                            argument.range(),
                                            FOR_OF_ITERABLE_REQUIRED_MESSAGE,
                                        );
                                        self.types.error_type()
                                    }
                                }
                            }
                            None => {
                                self.emit(
                                    FOR_OF_ITERABLE_REQUIRED,
                                    expression.range(),
                                    FOR_OF_ITERABLE_REQUIRED_MESSAGE,
                                );
                                self.types.error_type()
                            }
                        }
                    } else {
                        let value = match &yield_expression.argument {
                            Some(argument) => self.type_of_expr(argument, scope),
                            None => self.types.undefined_type(),
                        };
                        match protocol {
                            ForOfMode::Sync => value,
                            ForOfMode::Async => self.awaited_type(value),
                        }
                    };
                    self.yield_types
                        .entry(body_id)
                        .or_default()
                        .push(yield_type);
                }
            }
            Expression::Unary(unary) => {
                self.resolve_expr(&unary.argument, scope);
                // `-x`, `+x`, and `~x` coerce to a number and so reject a
                // nullable operand. `!x`, `typeof x`, `void x`, and `delete x`
                // all accept one.
                if matches!(
                    unary.operator,
                    UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitNot
                ) {
                    self.check_non_null_operand(&unary.argument, scope);
                }
            }
            Expression::Update(update) => {
                self.inventory_assignment_target_writes_in_scope(&update.argument, scope);
                self.resolve_assignment_target(&update.argument, scope);
                self.invalidate_assignment_flow(&update.argument);
            }
            Expression::Binary(binary) => {
                self.resolve_expr(&binary.left, scope);
                self.resolve_expr(&binary.right, scope);
                self.check_nullable_operands(binary, scope);
            }
            Expression::Logical(logical) => {
                self.resolve_expr(&logical.left, scope);
                if logical.operator == LogicalOperator::Nullish {
                    self.resolve_expr(&logical.right, scope);
                } else {
                    let parent = self.flow;
                    let right_guards =
                        self.guards_for(&logical.left, logical.operator == LogicalOperator::Or);
                    let skipped = self.branch_guarded(parent, &[]);
                    let right_end = self.in_branch(parent, &right_guards, |binder| {
                        binder.resolve_expr(&logical.right, scope);
                    });
                    self.join_flow(parent, &[skipped, right_end]);
                }
            }
            Expression::Conditional(conditional) => {
                self.resolve_expr(&conditional.test, scope);
                let literal_truthy = if let Expression::Literal(Literal::Boolean(literal)) =
                    conditional.test.data()
                {
                    Some(literal.data().token().kind() == TokenKind::KwTrue)
                } else {
                    None
                };
                match literal_truthy {
                    Some(true) => {
                        self.resolve_expr(&conditional.consequent, scope);
                        let saved = self.suppress_used_before_assigned;
                        self.suppress_used_before_assigned = true;
                        self.resolve_expr(&conditional.alternate, scope);
                        self.suppress_used_before_assigned = saved;
                    }
                    Some(false) => {
                        let saved = self.suppress_used_before_assigned;
                        self.suppress_used_before_assigned = true;
                        self.resolve_expr(&conditional.consequent, scope);
                        self.suppress_used_before_assigned = saved;
                        self.resolve_expr(&conditional.alternate, scope);
                    }
                    None => {
                        let parent = self.flow;
                        let truthy = self.guards_for(&conditional.test, false);
                        let falsy = self.guards_for(&conditional.test, true);
                        let consequent_end = self.in_branch(parent, &truthy, |binder| {
                            binder.resolve_expr(&conditional.consequent, scope);
                        });
                        let alternate_end = self.in_branch(parent, &falsy, |binder| {
                            binder.resolve_expr(&conditional.alternate, scope);
                        });
                        self.join_flow(parent, &[consequent_end, alternate_end]);
                    }
                }
            }
            Expression::Assignment(assignment) => {
                self.inventory_assignment_target_writes_in_scope(&assignment.left, scope);
                self.resolve_assignment_target(&assignment.left, scope);
                self.resolve_expr(&assignment.right, scope);
                self.check_nullable_compound_operand(assignment, scope);
                if assignment.operator == AssignmentOperator::Assign && !self.is_typescript() {
                    self.extend_javascript_object_assignment(
                        &assignment.left,
                        &assignment.right,
                        scope,
                    );
                }
                if assignment.operator == AssignmentOperator::Assign
                    && self.is_typescript()
                    && !self
                        .readonly_assignment_targets
                        .contains(&assignment.left.id())
                {
                    let target = self.type_of_assignment_target(&assignment.left, scope);
                    let source = self.type_of_expr_with_target(&assignment.right, target, scope);
                    if !self.types_assignable(source, target) {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            expression.range(),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                }
                self.invalidate_assignment_flow(&assignment.left);
            }
            Expression::Sequence(sequence) => {
                for inner in &sequence.expressions {
                    self.resolve_expr(inner, scope);
                }
            }
            Expression::Parenthesized(inner) => {
                self.resolve_transparent_expression(expression, inner, scope);
            }
            Expression::As(cast) => {
                self.resolve_transparent_expression(expression, &cast.expression, scope);
                if let Some(type_node) = &cast.type_node {
                    let source = self.type_of_expr(&cast.expression, scope);
                    let target = self.resolve_type(type_node, scope);
                    if !self.is_assertion_compatible(source, target) {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            expression.range(),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                }
            }
            Expression::Satisfies(satisfies) => {
                self.resolve_transparent_expression(expression, &satisfies.expression, scope);
                let target = self.resolve_type(&satisfies.type_node, scope);
                let source = self.type_of_expr_with_target(&satisfies.expression, target, scope);
                if !self.types_assignable(source, target) {
                    self.emit(
                        TYPE_NOT_ASSIGNABLE,
                        expression.range(),
                        NOT_ASSIGNABLE_MESSAGE,
                    );
                }
            }
            Expression::TypeAssertion(assertion) => {
                self.resolve_transparent_expression(expression, &assertion.expression, scope);
                let source = self.type_of_expr(&assertion.expression, scope);
                let target = self.resolve_type(&assertion.type_node, scope);
                if !self.is_assertion_compatible(source, target) {
                    self.emit(
                        TYPE_NOT_ASSIGNABLE,
                        expression.range(),
                        NOT_ASSIGNABLE_MESSAGE,
                    );
                }
            }
            Expression::NonNull(non_null) => {
                self.resolve_transparent_expression(expression, &non_null.expression, scope);
            }
            Expression::TaggedTemplate(tagged) => {
                self.resolve_expr(&tagged.tag, scope);
                for inner in &tagged.template.expressions {
                    self.resolve_expr(inner, scope);
                }
                self.check_tagged_template(tagged, scope, expression.range());
            }
            Expression::Template(template) => {
                for inner in &template.expressions {
                    self.resolve_expr(inner, scope);
                }
            }
            Expression::Import(import) => {
                self.resolve_expr(&import.source, scope);
                if let Some(options) = &import.options {
                    self.resolve_expr(options, scope);
                }
            }
            Expression::JsxElement(element) => {
                let _ = self.check_jsx_element(expression, element, scope);
            }
            Expression::JsxSelfClosingElement(element) => {
                let _ = self.check_jsx_self_closing_element(expression, element, scope);
            }
            Expression::JsxFragment(fragment) => {
                let _ = self.check_jsx_fragment(expression, fragment, scope);
            }
            Expression::Meta(MetaProperty::NewTarget) => {
                if !self.new_target_contexts.last().copied().unwrap_or(false) {
                    self.emit(
                        NEW_TARGET_OUTSIDE_FUNCTION,
                        expression.range(),
                        NEW_TARGET_OUTSIDE_FUNCTION_MESSAGE,
                    );
                }
            }
            Expression::Meta(MetaProperty::ImportMeta) => {}
            // A `super` expression that is neither a call callee (handled in
            // `Expression::Call`) nor a member-access object (skipped in
            // `Expression::Member`/`resolve_assignment_target`) has no valid
            // position, matching TS1034.
            Expression::Super => self.emit(
                BARE_SUPER_EXPRESSION,
                expression.range(),
                BARE_SUPER_EXPRESSION_MESSAGE,
            ),
            _ => {}
        }
    }

    /// Checks a `super.x` member access (or `super.x` assignment target)
    /// against the enclosing member home.
    ///
    /// `super?.x` never forms a super property access, so it reports
    /// [`BARE_SUPER_EXPRESSION`]. A base class member has no base type to read
    /// the member from and reports [`SUPER_REFERENCE_NON_DERIVED`]. Derived
    /// classes and object literals are legal. Plain functions and the top
    /// level stay silent: no existing C-band code carries that diagnostic, and
    /// minting one is out of scope.
    fn check_super_member_access(&mut self, range: TextRange, optional: bool) {
        if optional {
            self.emit(BARE_SUPER_EXPRESSION, range, BARE_SUPER_EXPRESSION_MESSAGE);
            return;
        }
        if self.super_member_homes.last() == Some(&SuperMemberHome::ClassMember { derived: false })
        {
            self.emit(
                SUPER_REFERENCE_NON_DERIVED,
                range,
                SUPER_REFERENCE_NON_DERIVED_MESSAGE,
            );
        }
    }

    fn check_super_call(&mut self, range: TextRange) {
        let context = self
            .super_call_contexts
            .last()
            .copied()
            .unwrap_or(SuperCallContext::NonConstructor);
        let (code, message) = match context {
            SuperCallContext::DerivedConstructor => {
                if let Some(called) = self.derived_constructor_super_presence.last_mut() {
                    *called = true;
                }
                return;
            }
            SuperCallContext::BaseConstructor
            | SuperCallContext::ConstructorParameters { derived: false } => (
                SUPER_REFERENCE_NON_DERIVED,
                SUPER_REFERENCE_NON_DERIVED_MESSAGE,
            ),
            SuperCallContext::ConstructorParameters { derived: true } => (
                SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS,
                SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS_MESSAGE,
            ),
            SuperCallContext::NonConstructor => (
                SUPER_CALL_OUTSIDE_CONSTRUCTOR,
                SUPER_CALL_OUTSIDE_CONSTRUCTOR_MESSAGE,
            ),
        };
        self.emit(code, range, message);
    }

    fn resolve_object_member(&mut self, member: &'src ObjectMember, scope: ScopeId) {
        match member {
            ObjectMember::Property(property) => {
                self.resolve_property_name(&property.name, scope);
                self.resolve_expr(&property.value, scope);
            }
            ObjectMember::Method(method) => {
                self.resolve_property_name(&method.name, scope);
                self.check_set_accessor_parameter_initializer(
                    method.modifier,
                    &method.function.parameters,
                    &method.name,
                );
                self.check_accessor_this_parameter(
                    method.modifier,
                    &method.function.parameters,
                    &method.name,
                );
                self.check_get_accessor(method.modifier, &method.function, &method.name);
                self.resolve_function(
                    &method.function,
                    scope,
                    false,
                    false,
                    self.types.any(),
                    SuperMemberHome::ObjectMember,
                );
            }
            ObjectMember::Spread(spread) => self.resolve_expr(&spread.argument, scope),
            ObjectMember::Missing(_) => {}
        }
    }

    fn resolve_transparent_expression(
        &mut self,
        expression: &'src Expr,
        inner: &'src Expr,
        scope: ScopeId,
    ) {
        self.resolve_expr(inner, scope);
        if let Some(symbol) = self.resolved_expression_reference(inner) {
            self.reference_aliases.insert(expression.id(), symbol);
        }
        if let Some(candidate) = self.imported_enum_member_uses.get(&inner.id()).cloned() {
            self.imported_enum_member_uses
                .insert(expression.id(), candidate);
        }
    }

    fn resolve_arguments(&mut self, arguments: &'src [CallArgument], scope: ScopeId) {
        for argument in arguments {
            match argument {
                CallArgument::Expression(inner) => self.resolve_expr(inner, scope),
                CallArgument::Spread(spread) => self.resolve_expr(&spread.argument, scope),
                CallArgument::Missing(_) => {}
            }
        }
    }

    fn resolve_type_arguments(
        &mut self,
        arguments: Option<&'src crate::syntax::TypeArgumentList>,
        scope: ScopeId,
    ) -> Vec<TypeId> {
        let Some(list) = arguments else {
            return Vec::new();
        };
        list.arguments
            .iter()
            .map(|argument| self.resolve_type(argument, scope))
            .collect()
    }

    fn check_call(&mut self, call: &'src CallExpression, scope: ScopeId, call_range: TextRange) {
        if !self.is_typescript() {
            return;
        }
        let not_callable_range = match call.callee.data() {
            Expression::Member(member) => match &member.property {
                MemberProperty::Private(identifier) => identifier.range(),
                MemberProperty::Computed(expression) => expression.range(),
                MemberProperty::Named(identifier) => identifier.range(),
            },
            _ => call.callee.range(),
        };
        let callee_type = self.type_of_expr(&call.callee, scope);
        let evaluation = self.evaluate_call(call, scope, callee_type);
        for mismatch in evaluation.mismatches {
            let (code, range, message) = match mismatch {
                CallMismatch::NotCallable => (
                    EXPRESSION_NOT_CALLABLE,
                    not_callable_range,
                    EXPRESSION_NOT_CALLABLE_MESSAGE,
                ),
                CallMismatch::ArgumentCount => (
                    ARGUMENT_COUNT_MISMATCH,
                    call_range,
                    ARGUMENT_COUNT_MISMATCH_MESSAGE,
                ),
                CallMismatch::ArgumentType(range) => (
                    ARGUMENT_NOT_ASSIGNABLE,
                    range,
                    ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
                ),
                CallMismatch::ExcessProperty(range) => {
                    (EXCESS_PROPERTY, range, EXCESS_PROPERTY_MESSAGE)
                }
            };
            self.emit(code, range, message);
        }
    }

    fn evaluate_call(
        &mut self,
        call: &'src CallExpression,
        scope: ScopeId,
        callee_type: TypeId,
    ) -> CallEvaluation {
        if matches!(self.types.get(callee_type), Type::Any | Type::Error) {
            return CallEvaluation::success(self.types.any());
        }

        let optional = call.optional
            || matches!(
                call.callee.data(),
                Expression::Member(member) if member.optional
            );
        let short_circuits = optional
            && match self.types.get(callee_type) {
                Type::Null | Type::Undefined => true,
                Type::Union(members) => members
                    .iter()
                    .any(|member| matches!(self.types.get(*member), Type::Null | Type::Undefined)),
                _ => false,
            };
        let callable_type = if short_circuits {
            self.types.non_nullable(callee_type)
        } else {
            callee_type
        };

        let arguments = self.resolve_call_arguments(&call.arguments, scope);
        let groups = self.call_signature_groups(&call.callee, callable_type);
        if groups.is_empty() {
            return CallEvaluation::failure(CallMismatch::NotCallable);
        }
        let explicit_types = call
            .type_arguments
            .as_ref()
            .map(|arguments| self.resolve_type_arguments(Some(arguments), scope));
        let mut evaluation = self.evaluate_signature_groups(
            groups,
            &arguments,
            explicit_types.as_deref(),
            call.callee.range(),
            scope,
        );
        if short_circuits && let Some(return_type) = evaluation.return_type {
            evaluation.return_type = Some(
                self.types
                    .union(&[return_type, self.types.undefined_type()]),
            );
        }
        evaluation
    }

    fn check_new(&mut self, new: &'src NewExpression, scope: ScopeId, range: TextRange) {
        if !self.is_typescript() {
            return;
        }
        let callee_type = self.type_of_expr(&new.callee, scope);
        let evaluation = self.evaluate_new(new, scope, callee_type);
        if evaluation.abstract_constructor {
            self.emit(
                ABSTRACT_CONSTRUCTOR,
                new.callee.range(),
                ABSTRACT_CONSTRUCTOR_MESSAGE,
            );
        }
        for mismatch in evaluation.mismatches {
            let (code, diagnostic_range, message) = match mismatch {
                CallMismatch::NotCallable => (
                    EXPRESSION_NOT_CONSTRUCTABLE,
                    new.callee.range(),
                    EXPRESSION_NOT_CONSTRUCTABLE_MESSAGE,
                ),
                CallMismatch::ArgumentCount => (
                    ARGUMENT_COUNT_MISMATCH,
                    range,
                    ARGUMENT_COUNT_MISMATCH_MESSAGE,
                ),
                CallMismatch::ArgumentType(argument_range) => (
                    ARGUMENT_NOT_ASSIGNABLE,
                    argument_range,
                    ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
                ),
                CallMismatch::ExcessProperty(range) => {
                    (EXCESS_PROPERTY, range, EXCESS_PROPERTY_MESSAGE)
                }
            };
            self.emit(code, diagnostic_range, message);
        }
    }

    fn evaluate_new(
        &mut self,
        new: &'src NewExpression,
        scope: ScopeId,
        callee_type: TypeId,
    ) -> CallEvaluation {
        if matches!(self.types.get(callee_type), Type::Any | Type::Error) {
            return CallEvaluation::success(self.types.any());
        }
        let groups = self.construct_signature_groups_for_type(callee_type);
        if groups.is_empty() {
            return CallEvaluation::failure(CallMismatch::NotCallable);
        }
        let arguments = self.resolve_call_arguments(&new.arguments, scope);
        let explicit_types = new
            .type_arguments
            .as_ref()
            .map(|arguments| self.resolve_type_arguments(Some(arguments), scope));
        self.evaluate_signature_groups(
            groups,
            &arguments,
            explicit_types.as_deref(),
            new.callee.range(),
            scope,
        )
    }

    fn evaluate_signature_groups<C: SignatureCandidate>(
        &mut self,
        groups: Vec<Vec<C>>,
        arguments: &[ResolvedCallArgument<'src>],
        explicit_types: Option<&[TypeId]>,
        diagnostic_range: TextRange,
        scope: ScopeId,
    ) -> CallEvaluation {
        let mut inference_types = Vec::with_capacity(arguments.len());
        let mut fresh_literal_sources = Vec::new();
        for argument in arguments {
            if let ResolvedCallArgument::Fixed {
                type_id,
                expression,
                ..
            } = argument
            {
                let source = inference_types.len() as u32;
                inference_types.push(*type_id);
                if expression.is_some_and(Self::is_fresh_array_literal) {
                    fresh_literal_sources.push(source);
                }
            }
        }
        let mut return_types = Vec::with_capacity(groups.len());
        let mut abstract_constructor = false;
        let mut selected_signatures = Vec::with_capacity(groups.len());
        for group in groups {
            let mut group_mismatches = vec![CallMismatch::ArgumentCount];
            let mut selected = None;
            for candidate in group {
                let is_abstract = candidate.is_abstract();
                let signature = candidate.signature();
                let instantiated = match explicit_types {
                    Some(explicit) => {
                        self.explicit_function_signature(signature, explicit, diagnostic_range)
                    }
                    None => self
                        .inferred_function_signature(
                            signature,
                            &inference_types,
                            &fresh_literal_sources,
                        )
                        .ok_or(CallMismatch::ArgumentType(diagnostic_range)),
                };
                let signature = match instantiated {
                    Ok(signature) => signature,
                    Err(mismatch) => {
                        group_mismatches = vec![mismatch];
                        continue;
                    }
                };
                let contextual_arguments =
                    self.probe_contextual_call_arguments(&signature, arguments, scope);
                let mismatches =
                    self.signature_argument_mismatches(&signature, &contextual_arguments);
                if mismatches.is_empty() {
                    selected = Some((signature, is_abstract));
                    break;
                }
                group_mismatches = mismatches;
            }
            let Some((signature, is_abstract)) = selected else {
                return CallEvaluation::failure_all(group_mismatches);
            };
            return_types.push(signature.return_type());
            selected_signatures.push(signature);
            abstract_constructor |= is_abstract;
        }
        self.contextualize_call_arguments(&selected_signatures, arguments, scope);
        let mut evaluation = CallEvaluation::success(self.types.union(&return_types));
        evaluation.abstract_constructor = abstract_constructor;
        evaluation
    }

    fn probe_contextual_call_arguments(
        &mut self,
        signature: &FunctionSignature,
        arguments: &[ResolvedCallArgument<'src>],
        scope: ScopeId,
    ) -> Vec<ResolvedCallArgument<'src>> {
        debug_assert!(!self.probing_contextual_type);
        self.probing_contextual_type = true;
        let contextual =
            self.contextualize_call_arguments(std::slice::from_ref(signature), arguments, scope);
        self.probing_contextual_type = false;
        contextual
    }

    fn contextualize_call_arguments(
        &mut self,
        signatures: &[FunctionSignature],
        arguments: &[ResolvedCallArgument<'src>],
        scope: ScopeId,
    ) -> Vec<ResolvedCallArgument<'src>> {
        arguments
            .iter()
            .enumerate()
            .map(|(position, argument)| {
                let ResolvedCallArgument::Fixed {
                    range,
                    expression: Some(expression),
                    ..
                } = argument
                else {
                    return *argument;
                };
                let targets: Vec<_> = signatures
                    .iter()
                    .filter_map(|signature| self.signature_parameter_target(signature, position))
                    .collect();
                if targets.is_empty() {
                    return *argument;
                }
                let target = self.types.union(&targets);
                ResolvedCallArgument::Fixed {
                    type_id: self.type_of_expr_with_target(expression, target, scope),
                    range: *range,
                    expression: Some(expression),
                }
            })
            .collect()
    }

    fn signature_parameter_target(
        &mut self,
        signature: &FunctionSignature,
        position: usize,
    ) -> Option<TypeId> {
        let rest_index = signature.arity().2;
        let parameter_index = rest_index.map_or(position, |rest| position.min(rest));
        let parameter = signature.parameters().get(parameter_index)?;
        let target = parameter.type_id();
        if rest_index == Some(parameter_index) {
            self.array_element_type(target).or(Some(target))
        } else {
            Some(target)
        }
    }

    fn resolve_call_arguments(
        &mut self,
        arguments: &'src [CallArgument],
        scope: ScopeId,
    ) -> Vec<ResolvedCallArgument<'src>> {
        let mut resolved = Vec::new();
        for argument in arguments {
            match argument {
                CallArgument::Expression(expression) => {
                    resolved.push(ResolvedCallArgument::Fixed {
                        type_id: self.type_of_expr(expression, scope),
                        range: expression.range(),
                        expression: Some(expression),
                    });
                }
                CallArgument::Spread(spread) => {
                    let type_id = self.type_of_expr(&spread.argument, scope);
                    match self.types.get(type_id).clone() {
                        Type::Tuple(shape) => {
                            for (index, &type_id) in shape.prefix.iter().enumerate() {
                                let type_id = if index >= shape.required as usize {
                                    self.types.union(&[type_id, self.types.undefined_type()])
                                } else {
                                    type_id
                                };
                                resolved.push(ResolvedCallArgument::Fixed {
                                    type_id,
                                    range: spread.argument.range(),
                                    expression: None,
                                });
                            }
                            if let Some(rest) = shape.rest {
                                let mut rest_and_suffix =
                                    Vec::with_capacity(1 + shape.suffix.len());
                                rest_and_suffix.push(rest);
                                rest_and_suffix.extend_from_slice(&shape.suffix);
                                let element = self.types.union(&rest_and_suffix);
                                resolved.push(ResolvedCallArgument::Variadic {
                                    element,
                                    range: spread.argument.range(),
                                });
                            }
                        }
                        Type::Array(element) => {
                            resolved.push(ResolvedCallArgument::Variadic {
                                element,
                                range: spread.argument.range(),
                            });
                        }
                        _ => resolved.push(ResolvedCallArgument::Variadic {
                            element: self.types.any(),
                            range: spread.argument.range(),
                        }),
                    }
                }
                CallArgument::Missing(_) => {}
            }
        }
        resolved
    }

    fn check_tagged_template(
        &mut self,
        tagged: &'src crate::syntax::TaggedTemplateExpression,
        scope: ScopeId,
        call_range: TextRange,
    ) {
        if !self.is_typescript() {
            return;
        }
        let not_callable_range = match tagged.tag.data() {
            Expression::Member(member) => match &member.property {
                MemberProperty::Private(identifier) => identifier.range(),
                MemberProperty::Computed(expression) => expression.range(),
                MemberProperty::Named(identifier) => identifier.range(),
            },
            _ => tagged.tag.range(),
        };
        let callee_type = self.type_of_expr(&tagged.tag, scope);
        let arguments = self.resolve_tagged_template_arguments(tagged, scope, call_range);
        let groups = self.call_signature_groups(&tagged.tag, callee_type);
        if groups.is_empty() {
            self.emit(
                EXPRESSION_NOT_CALLABLE,
                not_callable_range,
                EXPRESSION_NOT_CALLABLE_MESSAGE,
            );
            return;
        }
        let evaluation =
            self.evaluate_signature_groups(groups, &arguments, None, tagged.tag.range(), scope);
        for mismatch in evaluation.mismatches {
            let (code, range, message) = match mismatch {
                CallMismatch::NotCallable => (
                    EXPRESSION_NOT_CALLABLE,
                    not_callable_range,
                    EXPRESSION_NOT_CALLABLE_MESSAGE,
                ),
                CallMismatch::ArgumentCount => (
                    ARGUMENT_COUNT_MISMATCH,
                    call_range,
                    ARGUMENT_COUNT_MISMATCH_MESSAGE,
                ),
                CallMismatch::ArgumentType(range) => (
                    ARGUMENT_NOT_ASSIGNABLE,
                    range,
                    ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
                ),
                CallMismatch::ExcessProperty(range) => {
                    (EXCESS_PROPERTY, range, EXCESS_PROPERTY_MESSAGE)
                }
            };
            self.emit(code, range, message);
        }
    }

    fn evaluate_tagged_template(
        &mut self,
        tagged: &'src crate::syntax::TaggedTemplateExpression,
        scope: ScopeId,
        callee_type: TypeId,
        call_range: TextRange,
    ) -> CallEvaluation {
        if matches!(self.types.get(callee_type), Type::Any | Type::Error) {
            return CallEvaluation::success(self.types.any());
        }
        let arguments = self.resolve_tagged_template_arguments(tagged, scope, call_range);
        let groups = self.call_signature_groups(&tagged.tag, callee_type);
        if groups.is_empty() {
            return CallEvaluation::failure(CallMismatch::NotCallable);
        }
        self.evaluate_signature_groups(groups, &arguments, None, tagged.tag.range(), scope)
    }

    fn resolve_tagged_template_arguments(
        &mut self,
        tagged: &'src crate::syntax::TaggedTemplateExpression,
        scope: ScopeId,
        call_range: TextRange,
    ) -> Vec<ResolvedCallArgument<'src>> {
        let strings_range = self
            .template_literal_range(&tagged.template)
            .unwrap_or(call_range);
        let mut resolved = vec![ResolvedCallArgument::Fixed {
            type_id: self.types.array(self.types.string()),
            range: strings_range,
            expression: None,
        }];
        for expression in &tagged.template.expressions {
            resolved.push(ResolvedCallArgument::Fixed {
                type_id: self.type_of_expr(expression, scope),
                range: expression.range(),
                expression: Some(expression),
            });
        }
        resolved
    }

    fn template_literal_range(
        &self,
        template: &'src crate::syntax::TemplateLiteral,
    ) -> Option<TextRange> {
        let first = template.elements.first()?;
        let last = template.elements.last()?;
        TextRange::new(first.range().start(), last.range().end()).ok()
    }

    fn call_signature_groups(
        &mut self,
        callee: &Expr,
        callee_type: TypeId,
    ) -> Vec<Vec<FunctionSignature>> {
        if let Some(symbol) = self.resolved_expression_reference(callee) {
            let overloads = &self.overload_signatures[symbol.get() as usize];
            if !overloads.is_empty() {
                return vec![overloads.clone()];
            }
        }
        self.call_signature_groups_for_type(callee_type)
    }

    fn call_signature_groups_for_type(&mut self, type_id: TypeId) -> Vec<Vec<FunctionSignature>> {
        self.call_signature_groups_for_type_raw(type_id, type_id)
    }

    fn call_signature_groups_for_type_raw(
        &mut self,
        type_id: TypeId,
        receiver: TypeId,
    ) -> Vec<Vec<FunctionSignature>> {
        if let Some(view) = self.types.prepare_applied_alias_view(type_id) {
            return self.call_signature_groups_for_type_raw(view, receiver);
        }
        if let Some(view) = self.types.prepare_applied_class_view(type_id) {
            return self.call_signature_groups_for_type_raw(view, receiver);
        }
        match self.types.get(type_id).clone() {
            Type::Function(signature) => vec![vec![signature]],
            Type::ObjectType(object) if !object.call_signatures.is_empty() => {
                let signatures = object
                    .call_signatures
                    .iter()
                    .map(|signature| self.project_this_signature(signature, receiver))
                    .collect();
                vec![signatures]
            }
            Type::Union(members) => {
                let mut groups = Vec::with_capacity(members.len());
                for member in members {
                    let member_groups = self.call_signature_groups_for_type_raw(member, receiver);
                    if member_groups.is_empty() {
                        return Vec::new();
                    }
                    groups.extend(member_groups);
                }
                groups
            }
            Type::Intersection(members) => {
                let signatures: Vec<_> = members
                    .iter()
                    .flat_map(|member| self.call_signature_groups_for_type_raw(*member, receiver))
                    .flatten()
                    .collect();
                if signatures.is_empty() {
                    Vec::new()
                } else {
                    vec![signatures]
                }
            }
            Type::Named(symbol) if self.types.interface_structure(symbol).is_some() => {
                let view = self.types.named_structural_view(type_id);
                self.call_signature_groups_for_type_raw(view, receiver)
            }
            Type::Named(symbol) => {
                let resolved = self
                    .types
                    .type_parameter_constraint(symbol)
                    .unwrap_or(self.symbol_types[symbol.get() as usize]);
                if resolved == type_id {
                    Vec::new()
                } else {
                    self.call_signature_groups_for_type_raw(resolved, receiver)
                }
            }
            _ => Vec::new(),
        }
    }

    fn construct_signature_groups_for_type(&mut self, type_id: TypeId) -> Vec<Vec<ConstructEntry>> {
        self.construct_signature_groups_for_type_raw(type_id, type_id)
    }

    fn construct_signature_groups_for_type_raw(
        &mut self,
        type_id: TypeId,
        receiver: TypeId,
    ) -> Vec<Vec<ConstructEntry>> {
        if let Some(view) = self.types.prepare_applied_alias_view(type_id) {
            return self.construct_signature_groups_for_type_raw(view, receiver);
        }
        if let Some(view) = self.types.prepare_applied_class_view(type_id) {
            return self.construct_signature_groups_for_type_raw(view, receiver);
        }
        match self.types.get(type_id).clone() {
            Type::ConstructorType { structural, .. } => {
                self.construct_signature_groups_for_type_raw(structural, receiver)
            }
            Type::ObjectType(object) if !object.construct_signatures.is_empty() => {
                let signatures = object
                    .construct_signatures
                    .iter()
                    .map(|entry| ConstructEntry {
                        signature: self.project_this_signature(&entry.signature, receiver),
                        is_abstract: entry.is_abstract,
                    })
                    .collect();
                vec![signatures]
            }
            Type::Union(members) => {
                let mut groups = Vec::with_capacity(members.len());
                for member in members {
                    let member_groups =
                        self.construct_signature_groups_for_type_raw(member, receiver);
                    if member_groups.is_empty() {
                        return Vec::new();
                    }
                    groups.extend(member_groups);
                }
                groups
            }
            Type::Intersection(members) => {
                let signatures: Vec<_> = members
                    .iter()
                    .flat_map(|member| {
                        self.construct_signature_groups_for_type_raw(*member, receiver)
                    })
                    .flatten()
                    .collect();
                if signatures.is_empty() {
                    Vec::new()
                } else {
                    vec![signatures]
                }
            }
            Type::Named(symbol) if self.types.interface_structure(symbol).is_some() => {
                let view = self.types.named_structural_view(type_id);
                self.construct_signature_groups_for_type_raw(view, receiver)
            }
            Type::Named(symbol) => {
                let resolved = self
                    .types
                    .type_parameter_constraint(symbol)
                    .unwrap_or(self.symbol_types[symbol.get() as usize]);
                if resolved == type_id {
                    Vec::new()
                } else {
                    self.construct_signature_groups_for_type_raw(resolved, receiver)
                }
            }
            _ => Vec::new(),
        }
    }

    fn signature_argument_mismatches(
        &mut self,
        signature: &FunctionSignature,
        arguments: &[ResolvedCallArgument<'src>],
    ) -> Vec<CallMismatch> {
        let fixed_count = arguments
            .iter()
            .filter(|argument| matches!(argument, ResolvedCallArgument::Fixed { .. }))
            .count();
        let has_variadic = arguments
            .iter()
            .any(|argument| matches!(argument, ResolvedCallArgument::Variadic { .. }));
        let (required, total, rest_index) = if signature.javascript() {
            (0, usize::MAX, signature.arity().2)
        } else {
            signature.call_arity(&self.types)
        };
        if !has_variadic && (fixed_count < required || fixed_count > total) {
            return vec![CallMismatch::ArgumentCount];
        }

        let mut mismatches = Vec::new();
        for (position, argument) in arguments.iter().enumerate() {
            let parameter_index = rest_index.map_or(position, |rest| position.min(rest));
            let Some(parameter) = signature.parameters().get(parameter_index) else {
                if signature.javascript() {
                    continue;
                }
                return vec![CallMismatch::ArgumentCount];
            };
            let mut target = parameter.type_id();
            if rest_index == Some(parameter_index) {
                target = self.array_element_type(target).unwrap_or(target);
            }
            let (source, range, expression) = match argument {
                ResolvedCallArgument::Fixed {
                    type_id,
                    range,
                    expression,
                } => (*type_id, *range, *expression),
                ResolvedCallArgument::Variadic { element, range } => {
                    if rest_index != Some(parameter_index) {
                        if signature.javascript() {
                            continue;
                        }
                        return vec![CallMismatch::ArgumentCount];
                    }
                    (*element, *range, None)
                }
            };
            let assignable = (matches!(self.types.get(source), Type::Undefined)
                && parameter.optional())
                || self.types_assignable(source, target);
            if !assignable {
                mismatches.push(CallMismatch::ArgumentType(range));
                continue;
            }
            if let Some(expression) = expression {
                mismatches.extend(
                    self.fresh_excess_property_ranges(expression, target, true)
                        .into_iter()
                        .map(CallMismatch::ExcessProperty),
                );
            }
        }
        mismatches
    }

    fn array_element_type(&mut self, array_type: TypeId) -> Option<TypeId> {
        self.types.array_or_tuple_iteration_element(array_type)
    }

    fn zero_argument_return_type(&mut self, callable: TypeId) -> Option<TypeId> {
        let mut returns = Vec::new();
        for group in self.call_signature_groups_for_type(callable) {
            for signature in group {
                let (required, _, _) = signature.call_arity(&self.types);
                if required == 0 {
                    returns.push(signature.return_type());
                    break;
                }
            }
        }
        match returns.len() {
            0 => None,
            1 => Some(returns[0]),
            _ => Some(self.types.union(&returns)),
        }
    }

    fn iterator_object_element_type(
        &mut self,
        iterator: TypeId,
        protocol: ForOfMode,
    ) -> Option<TypeId> {
        match self.types.get(iterator).clone() {
            Type::Any | Type::Never | Type::Error => Some(iterator),
            Type::Array(_) | Type::Tuple(_) => self.array_element_type(iterator),
            Type::Union(members) => {
                let error = self.types.error_type();
                let mut has_error = false;
                let mut elements = Vec::with_capacity(members.len());
                for member in members {
                    let element = self.iterator_object_element_type(member, protocol)?;
                    has_error |= element == error;
                    elements.push(element);
                }
                if has_error {
                    Some(error)
                } else {
                    Some(self.types.union(&elements))
                }
            }
            Type::Named(_) | Type::AppliedClass { .. } | Type::AppliedAlias { .. } => {
                let view = self.types.named_structural_view(iterator);
                let view = self.types.prepare_applied_alias_view(view).unwrap_or(view);
                let view = self.types.prepare_applied_class_view(view).unwrap_or(view);
                (view != iterator)
                    .then(|| self.iterator_object_element_type(view, protocol))
                    .flatten()
            }
            Type::Intersection(members) => {
                let error = self.types.error_type();
                let mut elements = Vec::with_capacity(members.len());
                for member in members {
                    let Some(element) = self.iterator_object_element_type(member, protocol) else {
                        continue;
                    };
                    if element == error {
                        return Some(error);
                    }
                    elements.push(element);
                }
                match elements.len() {
                    0 => None,
                    1 => Some(elements[0]),
                    _ => Some(self.types.intersection(elements)),
                }
            }
            Type::ObjectType(_) => {
                let next = self.types.read_property_type(iterator, "next")?;
                let result = self.zero_argument_return_type(next)?;
                let result = match protocol {
                    ForOfMode::Sync => result,
                    ForOfMode::Async => self.awaited_type(result),
                };
                if matches!(
                    self.types.get(result),
                    Type::Any | Type::Never | Type::Error
                ) {
                    return Some(result);
                }
                self.iterator_result_yield_type(result)
            }
            _ => None,
        }
    }
    fn iterator_result_yield_type(&mut self, result: TypeId) -> Option<TypeId> {
        match self.types.get(result).clone() {
            Type::Any | Type::Never | Type::Error => Some(result),
            Type::Union(members) => {
                let mut yields = Vec::with_capacity(members.len());
                for member in members {
                    yields.push(self.iterator_result_yield_type(member)?);
                }
                Some(self.types.union(&yields))
            }
            Type::ObjectType(object) => {
                let value = self.types.property_type(result, "value")?;
                let returns_only = object.properties.iter().any(|property| {
                    property.name() == "done"
                        && !property.optional()
                        && matches!(
                            self.types.get(property.type_id()),
                            Type::BooleanLiteral(true)
                        )
                });
                Some(if returns_only {
                    self.types.never()
                } else {
                    value
                })
            }
            Type::Intersection(_) => {
                let value = self.types.property_type(result, "value")?;
                let returns_only = self
                    .types
                    .read_property_type(result, "done")
                    .is_some_and(|done| matches!(self.types.get(done), Type::BooleanLiteral(true)));
                Some(if returns_only {
                    self.types.never()
                } else {
                    value
                })
            }
            Type::Named(_) | Type::AppliedClass { .. } | Type::AppliedAlias { .. } => {
                let view = self.types.named_structural_view(result);
                let view = self.types.prepare_applied_alias_view(view).unwrap_or(view);
                let view = self.types.prepare_applied_class_view(view).unwrap_or(view);
                (view != result)
                    .then(|| self.iterator_result_yield_type(view))
                    .flatten()
            }
            _ => None,
        }
    }

    fn structural_iterator_element_type(
        &mut self,
        method: TypeId,
        protocol: ForOfMode,
    ) -> Option<TypeId> {
        if matches!(
            self.types.get(method),
            Type::Any | Type::Never | Type::Error
        ) {
            return Some(method);
        }
        let iterator = self.zero_argument_return_type(method)?;
        self.iterator_object_element_type(iterator, protocol)
    }

    fn iteration_element_type(&mut self, iterable: TypeId, mode: ForOfMode) -> Option<TypeId> {
        let element = self.iteration_element_type_inner(iterable, mode, iterable)?;
        Some(match mode {
            ForOfMode::Sync => element,
            ForOfMode::Async => self.awaited_type(element),
        })
    }

    fn iteration_element_type_inner(
        &mut self,
        iterable: TypeId,
        mode: ForOfMode,
        receiver: TypeId,
    ) -> Option<TypeId> {
        match self.types.get(iterable).clone() {
            Type::Array(_) | Type::Tuple(_) => {
                self.types.array_or_tuple_iteration_element(iterable)
            }
            Type::ObjectType(object) => {
                if mode == ForOfMode::Async
                    && let Some(property) = object.async_iterator_property
                    && !property.optional()
                {
                    let method = self.project_this_type_for_owners(
                        property.type_id(),
                        property.declaring_types(),
                        None,
                        receiver,
                    );
                    let passthrough = matches!(
                        self.types.get(method),
                        Type::Any | Type::Never | Type::Error
                    );
                    if passthrough || self.zero_argument_return_type(method).is_some() {
                        return self.structural_iterator_element_type(method, ForOfMode::Async);
                    }
                }
                let property = object.iterator_property?;
                if property.optional() {
                    return None;
                }
                let method = self.project_this_type_for_owners(
                    property.type_id(),
                    property.declaring_types(),
                    None,
                    receiver,
                );
                self.structural_iterator_element_type(method, ForOfMode::Sync)
            }
            Type::String | Type::StringLiteral(_) => Some(self.types.string()),
            Type::Any | Type::Never | Type::Error => Some(iterable),
            Type::Union(members) => {
                let error = self.types.error_type();
                let mut has_error = false;
                let mut elements = Vec::with_capacity(members.len());
                for member in members {
                    let element = self.iteration_element_type_inner(member, mode, receiver)?;
                    has_error |= element == error;
                    elements.push(element);
                }
                if has_error {
                    Some(error)
                } else {
                    Some(self.types.union(&elements))
                }
            }
            Type::Intersection(members) => {
                if mode == ForOfMode::Async
                    && let Some(property) =
                        self.types.iterator_property_of(iterable, ForOfMode::Async)
                    && !property.optional()
                {
                    let method = self.project_this_type_for_owners(
                        property.type_id(),
                        property.declaring_types(),
                        None,
                        receiver,
                    );
                    let passthrough = matches!(
                        self.types.get(method),
                        Type::Any | Type::Never | Type::Error
                    );
                    if passthrough || self.zero_argument_return_type(method).is_some() {
                        return self.structural_iterator_element_type(method, ForOfMode::Async);
                    }
                }
                if let Some(property) = self.types.iterator_property_of(iterable, ForOfMode::Sync)
                    && !property.optional()
                {
                    let method = self.project_this_type_for_owners(
                        property.type_id(),
                        property.declaring_types(),
                        None,
                        receiver,
                    );
                    return self.structural_iterator_element_type(method, ForOfMode::Sync);
                }
                let error = self.types.error_type();
                let mut elements = Vec::with_capacity(members.len());
                for member in members {
                    let Some(element) =
                        self.iteration_element_type_inner(member, ForOfMode::Sync, receiver)
                    else {
                        continue;
                    };
                    if element == error {
                        return Some(error);
                    }
                    elements.push(element);
                }
                match elements.len() {
                    0 => None,
                    1 => Some(elements[0]),
                    _ => Some(self.types.intersection(elements)),
                }
            }
            Type::Named(symbol) => {
                if let Some(constraint) = self.type_parameter_effective_constraint(iterable) {
                    return self.iteration_element_type_inner(constraint, mode, receiver);
                }
                let resolved = self.resolve_named_type_symbol(symbol);
                let view = self.types.named_structural_view(resolved);
                if view != resolved {
                    self.iteration_element_type_inner(view, mode, receiver)
                } else if resolved != iterable {
                    self.iteration_element_type_inner(resolved, mode, receiver)
                } else {
                    None
                }
            }
            Type::AppliedClass { .. } => {
                let view = self.types.prepare_applied_class_view(iterable)?;
                (view != iterable)
                    .then(|| self.iteration_element_type_inner(view, mode, receiver))
                    .flatten()
            }
            Type::AppliedAlias { .. } => {
                let view = self.types.prepare_applied_alias_view(iterable)?;
                (view != iterable)
                    .then(|| self.iteration_element_type_inner(view, mode, receiver))
                    .flatten()
            }
            Type::ConstructorType { structural, .. } => {
                self.iteration_element_type_inner(structural, mode, receiver)
            }
            _ => None,
        }
    }

    fn type_of_assignment_target(
        &mut self,
        target: &'src crate::syntax::AssignmentTargetNode,
        scope: ScopeId,
    ) -> TypeId {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => self
                .references
                .get(&identifier.id())
                .or_else(|| self.reference_aliases.get(&target.id()))
                .map_or_else(
                    || self.types.any(),
                    |symbol| self.symbol_types[symbol.get() as usize],
                ),
            AssignmentTarget::Member(member) => {
                let object_type = self.type_of_expr(&member.object, scope);
                self.record_member_reference_rows(
                    &member.object,
                    &member.property,
                    false,
                    object_type,
                    target.range(),
                    target.id(),
                );
                self.type_of_member(&member.object, &member.property, false, false, scope)
            }
            _ => self.types.any(),
        }
    }

    fn flow_narrowed_expression_type(&mut self, expression: &'src Expr) -> Option<TypeId> {
        let resolver = BinderGuardResolver {
            references: &self.references,
            node_types: &self.node_types,
            source: self.source,
            fallback: self.types.any(),
        };
        let key = flow_key_of(expression, &resolver)?;
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        narrowing.refined_type_at(self.flow, &key)
    }
    fn flow_narrowed_property_type(
        &mut self,
        object: &'src Expr,
        property_name: &str,
    ) -> Option<TypeId> {
        let resolver = BinderGuardResolver {
            references: &self.references,
            node_types: &self.node_types,
            source: self.source,
            fallback: self.types.any(),
        };
        let key = flow_key_of(object, &resolver)?.child(property_name);
        let mut narrowing = NarrowingContext::new_with_cancel(
            &mut self.types,
            &mut self.flow_facts,
            self.cancel.clone(),
        );
        narrowing.refined_type_at(self.flow, &key)
    }

    fn type_of_member(
        &mut self,
        object: &'src Expr,
        property: &'src MemberProperty,
        optional: bool,
        read: bool,
        scope: ScopeId,
    ) -> TypeId {
        let Some(name) = enum_plan::cook_member_property_name(self.source, property) else {
            let MemberProperty::Computed(expression) = property else {
                return self.types.any();
            };
            let object_type = self.type_of_expr(object, scope);
            let object_type = self
                .flow_narrowed_expression_type(object)
                .unwrap_or(object_type);
            let object_was_nullish = match self.types.get(object_type) {
                Type::Null | Type::Undefined => true,
                Type::Union(members) => members
                    .iter()
                    .any(|member| matches!(self.types.get(*member), Type::Null | Type::Undefined)),
                _ => false,
            };
            let lookup_type = if optional {
                self.types.optional_access_view(object_type)
            } else {
                object_type
            };
            let key_type = self.type_of_expr(expression, scope);
            let typescript = self.is_typescript();
            let rejects_any_key = typescript
                && self.types.is_unconstrained_index_key(key_type)
                && !self.types.accepts_any_index(lookup_type);
            let type_id = if rejects_any_key {
                self.emit(
                    INVALID_INDEXED_ACCESS_KEY,
                    expression.range(),
                    INVALID_INDEXED_ACCESS_KEY_MESSAGE,
                );
                self.types.error_type()
            } else if typescript {
                self.resolve_indexed_access_by_type(lookup_type, key_type, expression.range())
            } else {
                self.types.any()
            };
            return if optional && object_was_nullish {
                self.types.union(&[type_id, self.types.undefined_type()])
            } else {
                type_id
            };
        };
        let name_str = Self::semantic_property_key(&name);
        if let Some(object_symbol) = self.resolved_expression_reference(object) {
            let kind = self.symbols[object_symbol.get() as usize].kind;
            if kind == SymbolKind::Namespace
                && let Some(member_scope) = self.container_member_scope(object_symbol)
                && let Some(member_symbol) = self.scopes[member_scope.0 as usize]
                    .value(name_str.as_str())
                    .or_else(|| {
                        self.scopes[member_scope.0 as usize].type_binding(name_str.as_str())
                    })
            {
                return self.symbol_types[member_symbol.get() as usize];
            } else if kind == SymbolKind::Enum
                && let Some(member_symbol) = self
                    .enum_member_symbols_by_name
                    .get(&object_symbol)
                    .and_then(|members| members.get(&name))
                    .copied()
            {
                return self.symbol_types[member_symbol.get() as usize];
            }
        }
        let object_type = self.type_of_expr(object, scope);
        let object_type = self
            .flow_narrowed_expression_type(object)
            .unwrap_or(object_type);
        let object_was_nullish = match self.types.get(object_type) {
            Type::Null | Type::Undefined => true,
            Type::Union(members) => members
                .iter()
                .any(|member| matches!(self.types.get(*member), Type::Null | Type::Undefined)),
            _ => false,
        };
        let lookup_type = if optional {
            self.types.optional_access_view(object_type)
        } else {
            object_type
        };
        let property_range = match property {
            MemberProperty::Named(identifier) => identifier.range(),
            MemberProperty::Private(identifier) => identifier.range(),
            MemberProperty::Computed(expression) => expression.range(),
        };
        // Record the property access anchor for rename support. Only Named
        // properties and bracket string-literal accesses participate.
        let bare = match property {
            MemberProperty::Named(identifier) => Some(identifier.range()),
            MemberProperty::Computed(expression) => Self::bracket_bare_range(expression),
            _ => None,
        };
        if let Some(bare) = bare {
            let owner = self
                .resolved_expression_reference(object)
                .and_then(|symbol| self.symbol_anchor.get(&symbol).copied())
                .or_else(|| {
                    if matches!(object.data(), Expression::Object(_)) {
                        self.literal_anchor.get(&object.id()).copied()
                    } else {
                        self.owner_of_named_type(object_type)
                    }
                });
            if let Some(owner) = owner {
                self.record_property_anchor(
                    owner,
                    name_str.as_ref(),
                    bare,
                    PropertyAnchorKind::Plain,
                    false,
                );
            }
        }
        if !optional
            && read
            && let Some(narrowed) = self.flow_narrowed_property_type(object, name_str.as_ref())
        {
            return narrowed;
        }
        if let Some(type_id) = self.property_type_for_member_raw(
            lookup_type,
            name_str.as_str(),
            property_range,
            read,
            object_type,
            None,
        ) {
            if optional && object_was_nullish {
                return self.types.union(&[type_id, self.types.undefined_type()]);
            }
            return type_id;
        }
        self.types.any()
    }

    fn is_member_accessible(&self, property: &PropertyType) -> bool {
        if matches!(property.access(), Accessibility::Public) {
            return true;
        }
        let Some(declaring_class) = property.declaring_class() else {
            return true;
        };
        let Some(current) = self.class_owner_stack.last().copied() else {
            return false;
        };
        if declaring_class == current {
            return true;
        }
        if matches!(property.access(), Accessibility::Private) {
            return false;
        }
        self.is_derived_from(current, declaring_class)
    }

    fn is_derived_from(&self, mut derived: SymbolId, base: SymbolId) -> bool {
        let mut visited = HashSet::new();
        visited.insert(derived);
        while let Some(parent) = self.class_base_symbols.get(&derived).copied() {
            if parent == base {
                return true;
            }
            if !visited.insert(parent) {
                break;
            }
            derived = parent;
        }
        false
    }

    fn function_call_member_type(&mut self, signature: &FunctionSignature) -> TypeId {
        let mut parameters = Vec::with_capacity(signature.parameters().len() + 1);
        parameters.push(FunctionParameter::new(
            "thisArg".to_owned(),
            self.types.any(),
            false,
            false,
        ));
        parameters.extend(signature.parameters().iter().cloned());
        self.types.function_with_parameter_bounds(
            signature.type_parameters().to_vec(),
            signature.type_parameter_bounds().to_vec(),
            parameters,
            signature.return_type(),
            signature.javascript(),
        )
    }

    fn project_this_type(
        &mut self,
        type_id: TypeId,
        owner: Option<SymbolId>,
        receiver: TypeId,
    ) -> TypeId {
        owner.map_or(type_id, |owner| {
            InferredTypeArguments::for_this(owner, receiver).instantiate(&mut self.types, type_id)
        })
    }

    fn project_this_type_for_owners(
        &mut self,
        mut type_id: TypeId,
        owners: &[SymbolId],
        fallback: Option<SymbolId>,
        receiver: TypeId,
    ) -> TypeId {
        if owners.is_empty() {
            return self.project_this_type(type_id, fallback, receiver);
        }
        for &owner in owners {
            type_id = self.project_this_type(type_id, Some(owner), receiver);
        }
        type_id
    }

    fn project_this_signature(
        &mut self,
        signature: &FunctionSignature,
        receiver: TypeId,
    ) -> FunctionSignature {
        let mut projected = signature.clone();
        for &owner in signature.declaring_types() {
            let type_id = InferredTypeArguments::for_this(owner, receiver)
                .instantiate_signature(&mut self.types, &projected);
            let Type::Function(next) = self.types.get(type_id) else {
                unreachable!("signature instantiation returns a function");
            };
            projected = next.clone();
        }
        projected
    }

    fn property_type_for_member(
        &mut self,
        object_type: TypeId,
        name: &str,
        range: TextRange,
        read: bool,
    ) -> Option<TypeId> {
        self.property_type_for_member_raw(object_type, name, range, read, object_type, None)
    }

    fn deferred_record_property_type(&mut self, key: TypeId, value: TypeId, name: &str) -> TypeId {
        if self.types.property_name_assignable_to_key(name, key) {
            value
        } else {
            self.types.error_type()
        }
    }

    fn property_type_for_member_raw(
        &mut self,
        object_type: TypeId,
        name: &str,
        range: TextRange,
        read: bool,
        receiver: TypeId,
        owner_hint: Option<SymbolId>,
    ) -> Option<TypeId> {
        if let Some(view) = self.types.prepare_applied_alias_view(object_type) {
            return self
                .property_type_for_member_raw(view, name, range, read, receiver, owner_hint);
        }
        match self.types.get(object_type).clone() {
            Type::Record { key, value } => {
                let property = self.deferred_record_property_type(key, value, name);
                if property == self.types.error_type() && self.is_typescript() {
                    self.emit(
                        PROPERTY_DOES_NOT_EXIST,
                        range,
                        PROPERTY_DOES_NOT_EXIST_MESSAGE,
                    );
                }
                Some(property)
            }
            Type::ObjectType(object) => {
                if let Some(property) = object
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                {
                    if !self.is_member_accessible(property) {
                        self.emit(MEMBER_NOT_ACCESSIBLE, range, MEMBER_NOT_ACCESSIBLE_MESSAGE);
                        return Some(self.types.error_type());
                    }
                    let mut type_id = self.project_this_type_for_owners(
                        property.type_id(),
                        property.declaring_types(),
                        owner_hint,
                        receiver,
                    );
                    if read && property.optional() {
                        let undefined = self.types.undefined_type();
                        type_id = self.types.union(&[type_id, undefined]);
                    }
                    return Some(type_id);
                }
                let numeric = name.parse::<usize>().is_ok();
                if let Some(signature) = object.index_signatures.iter().find(|signature| {
                    signature.parameters.first().is_some_and(|parameter| {
                        matches!(self.types.get(parameter.type_id()), Type::String)
                            || (numeric
                                && matches!(self.types.get(parameter.type_id()), Type::Number))
                    })
                }) {
                    let type_id = self.project_this_type_for_owners(
                        signature.value_type,
                        &signature.declaring_types,
                        owner_hint,
                        receiver,
                    );
                    return Some(type_id);
                }
                if self.is_typescript() {
                    self.emit(
                        PROPERTY_DOES_NOT_EXIST,
                        range,
                        PROPERTY_DOES_NOT_EXIST_MESSAGE,
                    );
                    Some(self.types.error_type())
                } else {
                    Some(self.types.any())
                }
            }
            Type::Named(symbol) => {
                let resolved = self.resolve_named_type_symbol(symbol);
                let view = self.types.named_structural_view(resolved);
                if view == object_type {
                    None
                } else {
                    self.property_type_for_member_raw(
                        view,
                        name,
                        range,
                        read,
                        receiver,
                        Some(symbol),
                    )
                }
            }
            Type::Union(members) => {
                if self.strict_null_checks
                    && members.iter().any(|member| {
                        matches!(self.types.get(*member), Type::Null | Type::Undefined)
                    })
                {
                    self.emit(
                        STRICT_NULL_MEMBER_ACCESS,
                        range,
                        STRICT_NULL_MEMBER_ACCESS_MESSAGE,
                    );
                    return Some(self.types.error_type());
                }
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    let member_property = self.property_type_for_member_raw(
                        member, name, range, read, receiver, owner_hint,
                    )?;
                    if member_property == self.types.error_type() {
                        return Some(self.types.error_type());
                    }
                    found.push(member_property);
                }
                if found.len() == 1 {
                    Some(found[0])
                } else {
                    Some(self.types.union(&found))
                }
            }
            Type::Intersection(members) => {
                let mut found = Vec::with_capacity(members.len());
                for member in members {
                    let member = self
                        .types
                        .prepare_applied_alias_view(member)
                        .unwrap_or(member);
                    let (resolved, member_owner) = match self.types.get(member).clone() {
                        Type::Named(symbol) => {
                            (self.resolve_named_type_symbol(symbol), Some(symbol))
                        }
                        Type::AppliedClass { symbol, .. } => (member, Some(symbol)),
                        _ => (member, owner_hint),
                    };
                    let view = self.types.named_structural_view(resolved);
                    let property = match self.types.get(view).clone() {
                        Type::Function(signature) if name == "call" => {
                            Some(self.function_call_member_type(&signature))
                        }
                        _ if read => self.types.read_property_type(view, name),
                        _ => self.types.property_type(view, name),
                    };
                    if let Some(property) = property {
                        found.push(self.project_this_type(property, member_owner, receiver));
                    }
                }
                match found.len() {
                    0 => {
                        if self.is_typescript() {
                            self.emit(
                                PROPERTY_DOES_NOT_EXIST,
                                range,
                                PROPERTY_DOES_NOT_EXIST_MESSAGE,
                            );
                            Some(self.types.error_type())
                        } else {
                            Some(self.types.any())
                        }
                    }
                    1 => Some(found[0]),
                    _ => Some(self.types.intersection(found)),
                }
            }
            Type::Tuple(_) => {
                let property = if read {
                    self.types.read_property_type(object_type, name)
                } else {
                    self.types.property_type(object_type, name)
                };
                if let Some(type_id) = property {
                    Some(self.project_this_type(type_id, owner_hint, receiver))
                } else if self.is_typescript() {
                    self.emit(
                        PROPERTY_DOES_NOT_EXIST,
                        range,
                        PROPERTY_DOES_NOT_EXIST_MESSAGE,
                    );
                    Some(self.types.error_type())
                } else {
                    Some(self.types.any())
                }
            }
            Type::Array(_) => {
                let property = if read {
                    self.types.read_property_type(object_type, name)
                } else {
                    self.types.property_type(object_type, name)
                };
                Some(
                    property
                        .map(|property| self.project_this_type(property, owner_hint, receiver))
                        .unwrap_or_else(|| self.types.any()),
                )
            }
            Type::AppliedClass { symbol, .. } => {
                if let Some(view) = self.types.prepare_applied_class_view(object_type) {
                    return self.property_type_for_member_raw(
                        view,
                        name,
                        range,
                        read,
                        receiver,
                        Some(symbol),
                    );
                }
                None
            }
            Type::ConstructorType { structural, .. } => self
                .property_type_for_member_raw(structural, name, range, read, receiver, owner_hint),
            Type::This {
                owner, constraint, ..
            } => self.property_type_for_member_raw(
                constraint,
                name,
                range,
                read,
                receiver,
                Some(owner),
            ),
            Type::Function(signature) if name == "call" => {
                let property = self.function_call_member_type(&signature);
                Some(self.project_this_type(property, owner_hint, receiver))
            }
            Type::Error
            | Type::Any
            | Type::Unknown
            | Type::Never
            | Type::Void
            | Type::Null
            | Type::Undefined
            | Type::Boolean
            | Type::Number
            | Type::BigInt
            | Type::String
            | Type::Symbol
            | Type::Object
            | Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_)
            | Type::Function(_)
            | Type::AppliedAlias { .. }
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. } => None,
        }
    }

    fn property_is_readonly(&mut self, object_type: TypeId, name: &str) -> bool {
        match self.types.get(object_type).clone() {
            Type::ObjectType(object) => {
                if let Some(property) = object
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                {
                    return property.readonly();
                }
                let numeric = name.parse::<usize>().is_ok();
                object.index_signatures.iter().any(|signature| {
                    signature.readonly
                        && signature.parameters.first().is_some_and(|parameter| {
                            matches!(self.types.get(parameter.type_id()), Type::String)
                                || (numeric
                                    && matches!(self.types.get(parameter.type_id()), Type::Number))
                        })
                })
            }
            Type::Named(symbol) => {
                let resolved = self.resolve_named_type_symbol(symbol);
                let view = self.types.named_structural_view(resolved);
                view != object_type && self.property_is_readonly(view, name)
            }
            Type::Union(members) | Type::Intersection(members) => members
                .into_iter()
                .any(|member| self.property_is_readonly(member, name)),
            Type::AppliedClass { .. } => {
                if let Some(view) = self.types.prepare_applied_class_view(object_type) {
                    return self.property_is_readonly(view, name);
                }
                false
            }
            Type::ConstructorType { structural, .. } => self.property_is_readonly(structural, name),
            Type::AppliedAlias { .. } => {
                if let Some(view) = self.types.prepare_applied_alias_view(object_type) {
                    return self.property_is_readonly(view, name);
                }
                false
            }
            Type::This { constraint, .. } => self.property_is_readonly(constraint, name),
            _ => false,
        }
    }

    fn resolve_assignment_target(
        &mut self,
        target: &'src crate::syntax::AssignmentTargetNode,
        scope: ScopeId,
    ) {
        match target.data() {
            AssignmentTarget::Identifier(identifier) => {
                let name = self.identifier_text(identifier);
                if let Some(symbol) = self.lookup_value(scope, &name) {
                    self.uninitialized_variables.remove(&symbol);
                }
                self.resolve_value(identifier, target.id(), scope);
                if let Some(symbol) = self.references.get(&identifier.id()).copied() {
                    match self.symbols[symbol.get() as usize].kind {
                        SymbolKind::Function => self.emit(
                            ASSIGNMENT_TO_FUNCTION,
                            identifier.range(),
                            ASSIGNMENT_TO_FUNCTION_MESSAGE,
                        ),
                        SymbolKind::Namespace => self.emit(
                            ASSIGNMENT_TO_NAMESPACE,
                            identifier.range(),
                            ASSIGNMENT_TO_NAMESPACE_MESSAGE,
                        ),
                        SymbolKind::Variable(VariableKind::Const) => self.emit(
                            ASSIGNMENT_TO_CONST,
                            identifier.range(),
                            ASSIGNMENT_TO_CONST_MESSAGE,
                        ),
                        _ => {}
                    }
                }
            }
            AssignmentTarget::Member(member) => {
                if matches!(member.object.data(), Expression::Super) {
                    self.check_super_member_access(member.object.range(), false);
                } else {
                    self.resolve_expr(&member.object, scope);
                }
                let object_symbol = self.resolved_expression_reference(&member.object);
                if let MemberProperty::Computed(inner) = &member.property {
                    self.resolve_expr(inner, scope);
                }
                if let Some(enum_symbol) = object_symbol
                    && self.symbols[enum_symbol.get() as usize].kind == SymbolKind::Enum
                {
                    self.local_enum_member_targets
                        .insert(target.id(), enum_symbol);
                    return;
                }
                // Symbol-direct path: an assignment target whose base resolves
                // to a class or interface symbol records the same reference
                // rows a read access would (`this.connItem = c.item` renders
                // `>this.connItem` and `>connItem`), including private names.
                if let Some(object_symbol) = object_symbol
                    && matches!(
                        self.symbols[object_symbol.get() as usize].kind,
                        SymbolKind::Class | SymbolKind::Interface
                    )
                    && !self.member_reference_recorded.contains(&target.id())
                {
                    self.record_symbol_member_reference_rows(
                        object_symbol,
                        &member.property,
                        target.range(),
                    );
                    self.member_reference_recorded.insert(target.id());
                }
                let Some(name) =
                    enum_plan::cook_member_property_name(self.source, &member.property)
                else {
                    return;
                };
                let name_text = name.to_utf8_lossy();
                let object_type = self.type_of_expr(&member.object, scope);
                let constructor_initialization = matches!(member.object.data(), Expression::This)
                    && matches!(
                        self.super_call_contexts.last(),
                        Some(
                            SuperCallContext::BaseConstructor
                                | SuperCallContext::DerivedConstructor
                        )
                    )
                    && self
                        .constructor_writable_readonly_properties
                        .last()
                        .is_some_and(|properties| properties.contains(name_text.as_str()));
                if self.property_is_readonly(object_type, name_text.as_str())
                    && !constructor_initialization
                {
                    self.readonly_assignment_targets.insert(target.id());
                    let range = match &member.property {
                        MemberProperty::Named(identifier) => identifier.range(),
                        MemberProperty::Private(identifier) => identifier.range(),
                        MemberProperty::Computed(expression) => expression.range(),
                    };
                    self.emit(
                        ASSIGNMENT_TO_READONLY,
                        range,
                        ASSIGNMENT_TO_READONLY_MESSAGE,
                    );
                }
                let base = object_symbol
                    .filter(|symbol| self.symbols[symbol.get() as usize].kind == SymbolKind::Import)
                    .map(enum_plan::ImportedEnumMemberBase::Import)
                    .or_else(|| {
                        self.imported_enum_member_uses
                            .contains_key(&member.object.id())
                            .then_some(enum_plan::ImportedEnumMemberBase::MemberResult(
                                member.object.id(),
                            ))
                    });
                if let Some(base) = base {
                    self.imported_enum_member_uses.insert(
                        target.id(),
                        enum_plan::ImportedEnumMemberUse::new(base, name, target.range()),
                    );
                    self.imported_enum_member_targets.insert(target.id());
                }
            }
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    self.resolve_property_name(&property.name, scope);
                    self.resolve_assignment_target(&property.target, scope);
                    if let Some(initializer) = &property.initializer {
                        self.resolve_expr(initializer, scope);
                    }
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    match element {
                        crate::syntax::AssignmentArrayElement::Target(inner) => {
                            self.resolve_assignment_target(inner, scope);
                        }
                        crate::syntax::AssignmentArrayElement::Missing(_) => {
                            self.emit(
                                INVALID_ASSIGNMENT_TARGET,
                                target.range(),
                                INVALID_ASSIGNMENT_TARGET_MESSAGE,
                            );
                        }
                        _ => {}
                    }
                }
            }
            AssignmentTarget::Missing(_) => {
                self.emit(
                    INVALID_ASSIGNMENT_TARGET,
                    target.range(),
                    INVALID_ASSIGNMENT_TARGET_MESSAGE,
                );
            }
            AssignmentTarget::Invalid(operand) => {
                self.emit(
                    INVALID_ASSIGNMENT_TARGET,
                    target.range(),
                    INVALID_ASSIGNMENT_TARGET_MESSAGE,
                );
                self.resolve_expr(operand, scope);
                self.check_non_null_operand(operand, scope);
            }
        }
    }

    fn extend_javascript_object_assignment(
        &mut self,
        target: &'src crate::syntax::AssignmentTargetNode,
        source: &'src Expr,
        scope: ScopeId,
    ) {
        let AssignmentTarget::Member(member) = target.data() else {
            return;
        };
        let Some(symbol) = self.resolved_expression_reference(&member.object) else {
            return;
        };
        let Some(name) = enum_plan::cook_member_property_name(self.source, &member.property) else {
            return;
        };
        let Type::ObjectType(mut object) = self
            .types
            .get(self.symbol_types[symbol.get() as usize])
            .clone()
        else {
            return;
        };
        let source_type = self.type_of_expr(source, scope);
        let name = name.to_utf8_lossy();
        if let Some(property) = object
            .properties
            .iter_mut()
            .find(|property| property.name() == name)
        {
            property.type_id = self.types.union(&[property.type_id(), source_type]);
        } else {
            object
                .properties
                .push(PropertyType::new(name, false, source_type));
        }
        self.symbol_types[symbol.get() as usize] = self.types.object_type_with_members(object);
    }

    fn resolve_value(&mut self, identifier: &IdentifierNode, reference: NodeId, scope: ScopeId) {
        let name = self.identifier_text(identifier);
        if name.is_empty() {
            return;
        }
        if let Some(symbol) = self.lookup_value(scope, &name) {
            self.references.insert(identifier.id(), symbol);
            self.symbol_references.push((identifier.range(), symbol));
            if reference != identifier.id() {
                self.reference_aliases.insert(reference, symbol);
            }
            if self.symbols[symbol.get() as usize].kind == SymbolKind::EnumMember {
                self.enum_member_identifier_uses.insert(reference);
            }
            if let Some(declaration) = self.active_namespace_declarations.last().copied() {
                self.namespace_reference_blocks
                    .insert(reference, declaration);
            }
            if self.strict_null_checks
                && !self.suppress_used_before_assigned
                && self.uninitialized_variables.contains(&symbol)
                && self.boundary_scope(scope)
                    == self.boundary_scope(self.symbols[symbol.get() as usize].scope())
            {
                self.emit(
                    USED_BEFORE_ASSIGNED,
                    identifier.range(),
                    USED_BEFORE_ASSIGNED_MESSAGE,
                );
            }
        } else if !self.suppresses_unresolved_value(scope) {
            if self.intrinsics.is_lib_gated_value(&name) {
                self.emit(
                    CANNOT_FIND_NAME_LIB_GATED,
                    identifier.range(),
                    CANNOT_FIND_NAME_LIB_GATED_MESSAGE,
                );
            } else {
                self.emit(
                    CANNOT_FIND_NAME,
                    identifier.range(),
                    CANNOT_FIND_NAME_MESSAGE,
                );
            }
        }
    }

    /// Returns whether an unresolved value reference may bind to a sloppy `with`
    /// object at runtime instead of a lexical binding.
    pub(crate) fn suppresses_unresolved_value(&self, scope: ScopeId) -> bool {
        let mut current = Some(scope);
        while let Some(id) = current {
            let scope = &self.scopes[id.0 as usize];
            match scope.kind {
                ScopeKind::With => return true,
                ScopeKind::Module | ScopeKind::Global | ScopeKind::Namespace => return false,
                ScopeKind::Function
                | ScopeKind::Class
                | ScopeKind::Block
                | ScopeKind::For
                | ScopeKind::Catch => {}
            }
            current = scope.parent;
        }
        false
    }
    fn enclosing_this_owner(&self, mut scope: ScopeId) -> Option<SymbolId> {
        loop {
            let lexical = &self.scopes[scope.0 as usize];
            if let Some(owner) = lexical.this_owner.or(lexical.owner)
                && matches!(
                    self.symbols[owner.get() as usize].kind,
                    SymbolKind::Class | SymbolKind::Interface
                )
            {
                return Some(owner);
            }
            scope = lexical.parent?;
        }
    }
    /// Returns the nearest scope that is a function/class boundary or a script
    /// unit (global, module, namespace). Used-before-assigned diagnostics are
    /// only emitted when the declaration and the use share the same boundary.
    fn boundary_scope(&self, mut scope: ScopeId) -> ScopeId {
        loop {
            let kind = self.scopes[scope.0 as usize].kind;
            match kind {
                ScopeKind::Global | ScopeKind::Module | ScopeKind::Namespace => return scope,
                ScopeKind::Function => {
                    if let Some(parent) = self.scopes[scope.0 as usize].parent
                        && self.scopes[parent.0 as usize].kind == ScopeKind::Namespace
                    {
                        scope = parent;
                        continue;
                    }
                    return scope;
                }
                ScopeKind::Class => return scope,
                ScopeKind::Block | ScopeKind::For | ScopeKind::Catch | ScopeKind::With => {
                    scope = self.scopes[scope.0 as usize]
                        .parent
                        .expect("scope chain reaches global");
                }
            }
        }
    }

    fn resolved_expression_reference(&self, expression: &Expr) -> Option<SymbolId> {
        self.references
            .get(&expression.id())
            .or_else(|| self.reference_aliases.get(&expression.id()))
            .copied()
    }

    pub(crate) fn lookup_value(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
        let mut current = Some(scope);
        while let Some(id) = current {
            let scope = &self.scopes[id.0 as usize];
            // Class and interface member scopes collect member declarations
            // for the type layer, but upstream never exposes them as bare
            // lexical bindings: `foo` in a method body does not see the
            // property `foo`. Type parameters live in `types` and the
            // class's own name is a Class binding, so both stay visible.
            if let Some(symbol) = scope.values.get(name)
                && (scope.kind != ScopeKind::Class
                    || self.symbols[symbol.get() as usize].kind == SymbolKind::Class)
            {
                return Some(*symbol);
            }
            current = scope.parent;
        }
        None
    }

    pub(crate) fn lookup_type(&self, scope: ScopeId, name: &str) -> Option<SymbolId> {
        let mut current = Some(scope);
        while let Some(id) = current {
            let scope = &self.scopes[id.0 as usize];
            if let Some(symbol) = scope.types.get(name) {
                return Some(*symbol);
            }
            current = scope.parent;
        }
        None
    }

    // -- the named type algebra ------------------------------------------------

    pub(crate) fn resolve_type(&mut self, node: &'src Ty, scope: ScopeId) -> TypeId {
        if self.type_resolution_depth >= MAX_TYPE_DEPTH {
            self.emit(
                TYPE_NESTING_TOO_DEEP,
                node.range(),
                TYPE_NESTING_TOO_DEEP_MESSAGE,
            );
            return self.types.error_type();
        }
        self.type_resolution_depth += 1;
        let resolved = match node.data() {
            TypeNode::Keyword(keyword) => self.keyword_type(*keyword),
            TypeNode::Literal(literal) => self.literal_type(literal),
            TypeNode::Reference(reference) => {
                self.resolve_type_reference(reference, scope, node.id(), node.range())
            }
            TypeNode::Union(members) => {
                let resolved: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.resolve_type(member, scope))
                    .collect();
                self.types.union(&resolved)
            }
            TypeNode::Intersection(members) => {
                let resolved = members
                    .iter()
                    .map(|member| self.resolve_type(member, scope))
                    .collect();
                self.types.intersection(resolved)
            }
            TypeNode::Array(element) => {
                let element = self.resolve_type(element, scope);
                self.types.array(element)
            }
            TypeNode::Object(object) => self.resolve_object_type(&object.members, scope),
            TypeNode::Function(function) => self.resolve_function_type(function, scope),
            TypeNode::Constructor(constructor) => {
                let signature = self.resolve_function_signature(&constructor.function, scope);
                self.types.object_type_with_members(ObjectType {
                    properties: Vec::new(),
                    call_signatures: Vec::new(),
                    construct_signatures: vec![ConstructEntry {
                        signature,
                        is_abstract: constructor.is_abstract,
                    }],
                    index_signatures: Vec::new(),
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: None,
                })
            }
            TypeNode::This => match self.enclosing_this_owner(scope) {
                None => {
                    let resolved = self.types.error_type();
                    self.type_nodes.insert(node.id(), resolved);
                    self.type_resolution_depth -= 1;
                    return resolved;
                }
                Some(owner) => {
                    let constraint = match self.symbols[owner.get() as usize].kind {
                        SymbolKind::Class => self
                            .class_instance_types
                            .get(&owner)
                            .copied()
                            .unwrap_or_else(|| self.types.error_type()),
                        SymbolKind::Interface => self.types.named(owner),
                        _ => self.types.error_type(),
                    };
                    self.types.this_type(owner, constraint)
                }
            },
            TypeNode::Parenthesized(inner) => self.resolve_type(inner, scope),
            TypeNode::Tuple(tuple) => {
                let mut shape = TupleShape {
                    prefix: Vec::with_capacity(tuple.elements.len()),
                    required: 0,
                    rest: None,
                    suffix: Vec::new(),
                };
                for element in &tuple.elements {
                    let resolved = self.resolve_type(&element.type_node, scope);
                    if element.rest {
                        match self.types.get(resolved).clone() {
                            Type::Array(rest) => shape.rest = Some(rest),
                            Type::Tuple(inner) => {
                                if shape.rest.is_none() {
                                    shape.required = shape.required.saturating_add(inner.required);
                                    shape.prefix.extend(inner.prefix);
                                    shape.rest = inner.rest;
                                    shape.suffix.extend(inner.suffix);
                                } else {
                                    shape.suffix.extend(inner.all_element_types());
                                }
                            }
                            _ => shape.rest = Some(self.types.any()),
                        }
                    } else if shape.rest.is_some() {
                        shape.suffix.push(resolved);
                    } else {
                        if !element.optional {
                            shape.required = shape.required.saturating_add(1);
                        }
                        shape.prefix.push(resolved);
                    }
                }
                self.types.tuple_shape(shape)
            }
            TypeNode::Query(query) => {
                if let Some(arguments) = &query.type_arguments {
                    for argument in &arguments.arguments {
                        let _ = self.resolve_type(argument, scope);
                    }
                }
                self.resolve_type_query(query, scope, node.range())
            }
            TypeNode::IndexedAccess(indexed) => {
                let object_type = self.resolve_type(&indexed.object_type, scope);
                self.resolve_indexed_access(object_type, &indexed.index_type, scope, node.range())
            }
            TypeNode::Operator { operator, operand } => match operator {
                TypeOperator::Keyof => {
                    let resolved = self.resolve_type(operand, scope);
                    self.types.keyof(resolved)
                }
                TypeOperator::Readonly
                    if matches!(operand.data(), TypeNode::Array(_) | TypeNode::Tuple(_)) =>
                {
                    self.resolve_type(operand, scope)
                }
                TypeOperator::Readonly | TypeOperator::Unique => {
                    let _ = self.resolve_type(operand, scope);
                    self.types.error_type()
                }
            },
            _ => self.types.error_type(),
        };
        self.type_resolution_depth -= 1;
        self.type_nodes.insert(node.id(), resolved);
        resolved
    }

    fn resolve_indexed_access(
        &mut self,
        object_type: TypeId,
        index_node: &'src Ty,
        scope: ScopeId,
        range: TextRange,
    ) -> TypeId {
        let index_type = match index_node.data() {
            TypeNode::Operator {
                operator: TypeOperator::Keyof,
                operand,
            } => {
                let key_source = self.resolve_type(operand, scope);
                self.types.keyof(key_source)
            }
            _ => self.resolve_type(index_node, scope),
        };
        self.resolve_indexed_access_by_type(object_type, index_type, range)
    }

    fn resolve_indexed_access_by_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        range: TextRange,
    ) -> TypeId {
        let result = self.types.indexed_access(object_type, index_type);
        if result == self.types.error_type()
            && !self.types.contains_error(object_type)
            && !self.types.contains_error(index_type)
        {
            self.emit(
                INVALID_INDEXED_ACCESS_KEY,
                range,
                INVALID_INDEXED_ACCESS_KEY_MESSAGE,
            );
        }
        result
    }

    fn resolve_type_query(
        &mut self,
        query: &'src crate::syntax::TypeQuery,
        scope: ScopeId,
        _range: TextRange,
    ) -> TypeId {
        self.resolve_type_query_name(&query.name, scope)
    }

    fn resolve_type_query_name(&mut self, name: &EntityName, scope: ScopeId) -> TypeId {
        match name {
            EntityName::Identifier(identifier) => {
                let name = self.identifier_text(identifier);
                let Some(symbol) = self.lookup_value(scope, &name) else {
                    self.emit(
                        CANNOT_FIND_NAME,
                        identifier.range(),
                        CANNOT_FIND_NAME_MESSAGE,
                    );
                    return self.types.any();
                };
                match self.symbols[symbol.get() as usize].kind {
                    SymbolKind::Class => self
                        .class_constructor_types
                        .get(&symbol)
                        .copied()
                        .unwrap_or(self.symbol_types[symbol.get() as usize]),
                    _ => self.symbol_types[symbol.get() as usize],
                }
            }
            EntityName::Qualified { left, right } => {
                // A qualified `typeof A.B` can be a namespace path (the prefix
                // resolves through a namespace/module scope, the final name is a
                // value it exports) or a value property path (the prefix is an
                // expression, each subsequent identifier is a member on it).
                // Try the namespace interpretation first; if the prefix is not a
                // namespace, fall back to type-table member lookup.
                match self.resolve_entity_name_scope(left, scope) {
                    Ok((member_scope, _path)) => {
                        let name = self.identifier_text(right);
                        match self.scopes[member_scope.0 as usize].value(&name) {
                            Some(symbol) => match self.symbols[symbol.get() as usize].kind {
                                SymbolKind::Class => self
                                    .class_constructor_types
                                    .get(&symbol)
                                    .copied()
                                    .unwrap_or(self.symbol_types[symbol.get() as usize]),
                                _ => self.symbol_types[symbol.get() as usize],
                            },
                            None => {
                                self.emit(
                                    CANNOT_FIND_NAME,
                                    right.range(),
                                    CANNOT_FIND_NAME_MESSAGE,
                                );
                                self.types.error_type()
                            }
                        }
                    }
                    Err(_) => {
                        let base_type = self.resolve_type_query_name(left, scope);
                        if base_type == self.types.error_type() || base_type == self.types.any() {
                            return base_type;
                        }
                        let name = self.identifier_text(right);
                        match self.property_type_for_member(
                            base_type,
                            name.as_ref(),
                            right.range(),
                            true,
                        ) {
                            Some(type_id) => type_id,
                            None => {
                                self.emit(
                                    PROPERTY_DOES_NOT_EXIST,
                                    right.range(),
                                    PROPERTY_DOES_NOT_EXIST_MESSAGE,
                                );
                                self.types.error_type()
                            }
                        }
                    }
                }
            }
            EntityName::Missing(_) => self.types.error_type(),
        }
    }

    fn keyword_type(&mut self, keyword: KeywordType) -> TypeId {
        match keyword {
            KeywordType::Any => self.types.any(),
            KeywordType::Unknown => self.types.unknown(),
            KeywordType::Never => self.types.never(),
            KeywordType::Void => self.types.void(),
            KeywordType::Undefined => self.types.undefined_type(),
            KeywordType::Null => self.types.null_type(),
            KeywordType::Boolean => self.types.boolean(),
            KeywordType::Number => self.types.number(),
            KeywordType::BigInt => self.types.bigint(),
            KeywordType::String => self.types.string(),
            KeywordType::Symbol => self.types.symbol_type(),
            KeywordType::Object => self.types.object(),
            KeywordType::Intrinsic => self.types.error_type(),
        }
    }

    fn literal_type(&mut self, literal: &TypeLiteral) -> TypeId {
        match literal {
            TypeLiteral::String(token) => {
                let text = self.text(token.data().token());
                self.types.string_literal_lexeme(text)
            }
            TypeLiteral::Number(token) => {
                let text = self.text(token.data().token());
                self.types.number_literal(text)
            }
            TypeLiteral::BigInt(token) => {
                let text = self.text(token.data().token());
                self.types.bigint_literal(text)
            }
            TypeLiteral::Boolean(token) => {
                let value = self.text(token.data().token()) == "true";
                self.types.boolean_literal(value)
            }
            TypeLiteral::Null(_) => self.types.null_type(),
            TypeLiteral::Unary { .. } => self.types.number(),
        }
    }

    fn resolve_type_reference(
        &mut self,
        reference: &'src TypeReference,
        scope: ScopeId,
        reference_id: NodeId,
        range: TextRange,
    ) -> TypeId {
        let explicit_arguments: Option<Vec<TypeId>> =
            reference.type_arguments.as_ref().map(|list| {
                list.arguments
                    .iter()
                    .map(|argument| self.resolve_type(argument, scope))
                    .collect()
            });
        match &reference.name {
            EntityName::Identifier(identifier) => {
                let name = self.identifier_text(identifier);
                match self.lookup_type(scope, &name) {
                    Some(symbol) => {
                        self.symbol_references.push((identifier.range(), symbol));
                        if name.as_ref() == "Promise"
                            && matches!(
                                self.symbols[symbol.get() as usize].kind,
                                SymbolKind::IntrinsicType
                            )
                        {
                            return self.promise_type(
                                explicit_arguments
                                    .as_deref()
                                    .and_then(|arguments| arguments.first().copied())
                                    .unwrap_or_else(|| self.types.any()),
                            );
                        }
                        if matches!(name.as_ref(), "Array" | "ReadonlyArray" | "ArrayLike")
                            && matches!(
                                self.symbols[symbol.get() as usize].kind,
                                SymbolKind::IntrinsicType
                            )
                        {
                            return self.types.array(
                                explicit_arguments
                                    .as_deref()
                                    .and_then(|arguments| arguments.first().copied())
                                    .unwrap_or_else(|| self.types.any()),
                            );
                        }
                        if matches!(name.as_ref(), "Generator" | "AsyncGenerator")
                            && matches!(
                                self.symbols[symbol.get() as usize].kind,
                                SymbolKind::IntrinsicType
                            )
                        {
                            let yield_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.first().copied())
                                .unwrap_or_else(|| self.types.unknown());
                            let return_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.get(1).copied())
                                .unwrap_or_else(|| self.types.any());
                            let next_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.get(2).copied())
                                .unwrap_or_else(|| self.types.any());
                            let protocol = if name.as_ref() == "AsyncGenerator" {
                                ForOfMode::Async
                            } else {
                                ForOfMode::Sync
                            };
                            return self.intrinsic_generator_type(
                                yield_type,
                                return_type,
                                next_type,
                                protocol,
                            );
                        }
                        if matches!(
                            name.as_ref(),
                            "Iterable"
                                | "Iterator"
                                | "IterableIterator"
                                | "AsyncIterable"
                                | "AsyncIterableIterator"
                                | "AsyncIterator"
                        ) && matches!(
                            self.symbols[symbol.get() as usize].kind,
                            SymbolKind::IntrinsicType
                        ) {
                            let yield_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.first().copied())
                                .unwrap_or_else(|| self.types.any());
                            let return_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.get(1).copied())
                                .unwrap_or_else(|| self.types.any());
                            let next_type = explicit_arguments
                                .as_deref()
                                .and_then(|arguments| arguments.get(2).copied())
                                .unwrap_or_else(|| self.types.any());
                            return match name.as_ref() {
                                "Iterable" => self.intrinsic_iterable_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Sync,
                                ),
                                "Iterator" => self.intrinsic_iterator_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Sync,
                                ),
                                "IterableIterator" => self.intrinsic_iterable_iterator_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Sync,
                                ),
                                "AsyncIterable" => self.intrinsic_iterable_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Async,
                                ),
                                "AsyncIterator" => self.intrinsic_iterator_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Async,
                                ),
                                "AsyncIterableIterator" => self.intrinsic_iterable_iterator_type(
                                    yield_type,
                                    return_type,
                                    next_type,
                                    ForOfMode::Async,
                                ),
                                _ => unreachable!("matched intrinsic iterator name"),
                            };
                        }
                        if self.types.is_record_symbol(symbol) {
                            return self
                                .intrinsic_record_type(explicit_arguments.as_deref(), range);
                        }
                        if name.as_ref() == "Partial"
                            && matches!(
                                self.symbols[symbol.get() as usize].kind,
                                SymbolKind::IntrinsicType
                            )
                        {
                            return self
                                .intrinsic_partial_type(explicit_arguments.as_deref(), range);
                        }
                        let base = self.resolve_named_type_symbol(symbol);
                        self.instantiate_explicit_type_arguments(
                            symbol,
                            explicit_arguments.as_deref(),
                            base,
                            range,
                        )
                    }
                    None => {
                        if self.intrinsics.is_lib_gated_type(name.as_ref()) {
                            self.emit(
                                CANNOT_FIND_NAME_LIB_GATED,
                                range,
                                CANNOT_FIND_NAME_LIB_GATED_MESSAGE,
                            );
                        } else {
                            self.emit(CANNOT_FIND_TYPE, range, CANNOT_FIND_TYPE_MESSAGE);
                        }
                        self.types.error_type()
                    }
                }
            }
            EntityName::Qualified { left, right } => {
                let (member_scope, mut path) = match self.resolve_entity_name_scope(left, scope) {
                    Ok(resolved) => resolved,
                    Err(EntityNameScopeError::NotNamespace) => {
                        self.emit(CANNOT_FIND_NAMESPACE, range, CANNOT_FIND_NAMESPACE_MESSAGE);
                        return self.types.error_type();
                    }
                    Err(EntityNameScopeError::MissingMember(missing_range)) => {
                        self.emit(CANNOT_FIND_TYPE, missing_range, CANNOT_FIND_TYPE_MESSAGE);
                        return self.types.error_type();
                    }
                    Err(EntityNameScopeError::Unresolved) => return self.types.error_type(),
                };
                let name = self.identifier_text(right);
                let Some(symbol) = self.scopes[member_scope.0 as usize]
                    .type_binding(&name)
                    .or_else(|| {
                        // Enum members occupy the value plane but tsc permits
                        // `EnumName.Member` as a type reference resolving to
                        // the member's literal type.
                        let value = self.scopes[member_scope.0 as usize].value(&name)?;
                        (self.symbols[value.get() as usize].kind == SymbolKind::EnumMember)
                            .then_some(value)
                    })
                else {
                    if let Some(&local_scope) = path
                        .last()
                        .and_then(|ns| self.namespace_local_of_symbol.get(ns))
                        && self.scopes[local_scope.0 as usize]
                            .type_binding(&name)
                            .is_some()
                    {
                        let ns_name = self.symbols[path.last().unwrap().get() as usize]
                            .name()
                            .to_owned();
                        self.emit_with_message(
                            NAMESPACE_NO_EXPORTED_MEMBER,
                            right.range(),
                            format!("Namespace '{ns_name}' has no exported member '{name}'."),
                        );
                    } else {
                        self.emit(CANNOT_FIND_TYPE, right.range(), CANNOT_FIND_TYPE_MESSAGE);
                    }
                    return self.types.error_type();
                };
                path.push(symbol);
                if reference_id != NodeId::default() {
                    self.namespace_qualified_type_paths
                        .insert(reference_id, path.into_boxed_slice());
                }
                // Enum members resolved from the value plane already carry
                // their literal type (set at binding time); they take no
                // type arguments, so skip `resolve_named_type_symbol`.
                if self.symbols[symbol.get() as usize].kind == SymbolKind::EnumMember {
                    return self.symbol_types[symbol.get() as usize];
                }
                let base = self.resolve_named_type_symbol(symbol);
                self.instantiate_explicit_type_arguments(
                    symbol,
                    explicit_arguments.as_deref(),
                    base,
                    range,
                )
            }
            EntityName::Missing(_) => {
                self.emit(CANNOT_FIND_TYPE, range, CANNOT_FIND_TYPE_MESSAGE);
                self.types.error_type()
            }
        }
    }

    fn ensure_alias_bounds(&mut self, symbol: SymbolId) {
        if self.types.alias_bounds_ready(symbol) {
            return;
        }
        let Some(TypeDef::Alias {
            scope,
            type_parameters,
            ..
        }) = self.type_defs.get(&symbol).copied()
        else {
            return;
        };
        if !self.types.begin_alias_bounds(symbol) {
            return;
        }
        let bounds = self.signature_type_parameters(type_parameters, scope).1;
        self.types.finish_alias_bounds(symbol, bounds);
    }

    fn instantiate_explicit_type_arguments(
        &mut self,
        symbol: SymbolId,
        arguments: Option<&[TypeId]>,
        base: TypeId,
        diagnostic_range: TextRange,
    ) -> TypeId {
        let definition = self.type_defs.get(&symbol).copied();
        let imported_parameters = self.imported_type_parameters.get(&symbol).cloned();
        let (parameters, bounds) = if self.types.has_class(symbol) {
            (
                self.types.class_type_parameters(symbol).to_vec(),
                self.types.class_type_parameter_bounds(symbol).to_vec(),
            )
        } else if self.types.has_alias(symbol) {
            self.ensure_alias_bounds(symbol);
            (
                self.types.alias_type_parameters(symbol).to_vec(),
                self.types.alias_type_parameter_bounds(symbol).to_vec(),
            )
        } else if let Some(definition) = definition {
            match definition {
                TypeDef::Alias {
                    scope,
                    type_parameters,
                    ..
                }
                | TypeDef::Interface {
                    scope,
                    type_parameters,
                    ..
                } => self.signature_type_parameters(type_parameters, scope),
                TypeDef::Enum { .. } => (Vec::new(), Vec::new()),
            }
        } else if let Some(parameters) = imported_parameters {
            let bounds = parameters
                .iter()
                .map(|parameter| {
                    TypeParameterBounds::new(
                        self.types.type_parameter_constraint(*parameter),
                        self.types.type_parameter_default(*parameter),
                    )
                })
                .collect();
            (parameters, bounds)
        } else if let Some((class_symbol, _)) = self.types.class_identity(base) {
            (
                self.types.class_type_parameters(class_symbol).to_vec(),
                self.types
                    .class_type_parameter_bounds(class_symbol)
                    .to_vec(),
            )
        } else {
            return base;
        };
        let inferred =
            self.resolve_explicit_type_arguments(&parameters, &bounds, arguments, diagnostic_range);
        if self.types.has_alias(symbol)
            && (matches!(
                self.type_state[symbol.get() as usize],
                TypeState::InProgress
            ) || self.alias_resolution_dependencies.contains(&symbol))
        {
            let arguments = inferred
                .into_iter()
                .map(|argument| argument.type_id())
                .collect();
            return self.types.applied_alias(symbol, arguments);
        }
        if inferred.is_empty() {
            return base;
        }
        // A recursive generic interface reference is resolved while its raw
        // structure is still in progress. Preserve the application as an opaque
        // head; publishing the completed template materializes its finite view.
        if matches!(self.types.get(base), Type::Named(_)) && self.types.has_class(symbol) {
            let arguments = inferred
                .into_iter()
                .map(|argument| argument.type_id())
                .collect();
            return self.types.applied_class(symbol, arguments);
        }
        let base = self.types.named_structural_view(base);
        InferredTypeArguments::new(inferred).instantiate(&mut self.types, base)
    }

    fn resolve_explicit_type_arguments(
        &mut self,
        parameters: &[SymbolId],
        bounds: &[TypeParameterBounds],
        arguments: Option<&[TypeId]>,
        diagnostic_range: TextRange,
    ) -> Vec<InferredTypeArgument> {
        let provided = arguments.map_or(0, <[TypeId]>::len);
        let required = parameters
            .iter()
            .zip(bounds)
            .filter(|(parameter, bound)| {
                bound.default().is_none() && !self.type_parameter_defaults.contains_key(*parameter)
            })
            .count();
        if provided < required || provided > parameters.len() {
            self.emit(
                ARGUMENT_COUNT_MISMATCH,
                diagnostic_range,
                ARGUMENT_COUNT_MISMATCH_MESSAGE,
            );
        }

        let inferred = self.complete_explicit_type_arguments(parameters, bounds, arguments);
        let substitution = InferredTypeArguments::new(inferred.clone());
        for argument in &inferred {
            self.pending_constraint_checks.push(PendingConstraintCheck {
                argument: argument.type_id(),
                parameter: argument.symbol(),
                substitution: substitution.clone(),
                range: diagnostic_range,
            });
        }
        inferred
    }

    fn complete_explicit_type_arguments(
        &mut self,
        parameters: &[SymbolId],
        bounds: &[TypeParameterBounds],
        arguments: Option<&[TypeId]>,
    ) -> Vec<InferredTypeArgument> {
        let mut inferred = Vec::with_capacity(parameters.len());
        for (index, &parameter) in parameters.iter().enumerate() {
            let explicit = arguments
                .and_then(|arguments| arguments.get(index))
                .copied();
            let (type_id, provenance) = if let Some(type_id) = explicit {
                (type_id, InferenceProvenance::Explicit)
            } else {
                let default = bounds
                    .get(index)
                    .and_then(|bound| bound.default())
                    .or_else(|| self.resolve_type_parameter_default(parameter));
                let type_id = if let Some(default) = default {
                    InferredTypeArguments::new(inferred.clone())
                        .instantiate(&mut self.types, default)
                } else {
                    self.types.any()
                };
                (type_id, InferenceProvenance::Default)
            };
            inferred.push(InferredTypeArgument::new(parameter, type_id, provenance));
        }
        inferred
    }

    fn resolve_named_type_symbol(&mut self, symbol: SymbolId) -> TypeId {
        match self.symbols[symbol.get() as usize].kind {
            SymbolKind::Interface => {
                let head = self.resolve_type_symbol(symbol);
                self.types.named_structural_view(head)
            }
            SymbolKind::TypeAlias | SymbolKind::Enum => self.resolve_type_symbol(symbol),
            SymbolKind::Class => self
                .types
                .declared_class(symbol)
                .unwrap_or_else(|| self.types.applied_class(symbol, Vec::new())),
            SymbolKind::TypeParameter => self.types.named(symbol),
            // IntrinsicValue symbols that carry a registered class instance
            // type (the Error family registered in `bind_intrinsic_environment`)
            // resolve to their AppliedClass instance so `class E extends Error`
            // inherits `name`/`message`/`stack`/`cause`. Symbols without a
            // registered instance fall through to the permissive error type.
            SymbolKind::IntrinsicValue if self.class_instance_types.contains_key(&symbol) => {
                self.class_instance_types[&symbol]
            }
            // `Object` is the only intrinsic type the table models nominally, because
            // relations knows it is the top object type. The other intrinsics
            // (`Record`, `Promise`, `Iterable`, ...) have no structural definition yet.
            // A nominal target that no structural source can satisfy rejects valid
            // code, so they keep the permissive error type until they are modelled.
            SymbolKind::IntrinsicType if self.types.is_object_symbol(symbol) => {
                self.types.named(symbol)
            }
            SymbolKind::IntrinsicType if self.types.property_key_symbol == Some(symbol) => {
                let string = self.types.string();
                let number = self.types.number();
                let symbol = self.types.symbol_type();
                self.types.union(&[string, number, symbol])
            }
            SymbolKind::IntrinsicType
                if self.types.intrinsic_collection_index(symbol).is_some() =>
            {
                self.types
                    .declared_class(symbol)
                    .expect("intrinsic collection class registered")
            }
            SymbolKind::IntrinsicType if self.class_instance_types.contains_key(&symbol) => {
                self.class_instance_types[&symbol]
            }
            SymbolKind::Import => self
                .imported_type_planes
                .get(&symbol)
                .copied()
                .unwrap_or_else(|| self.resolve_import_equals_type_symbol(symbol)),
            _ => self.types.error_type(),
        }
    }

    fn intrinsic_record_type(&mut self, arguments: Option<&[TypeId]>, range: TextRange) -> TypeId {
        if arguments.is_none_or(|arguments| arguments.len() != 2) {
            self.emit(
                ARGUMENT_COUNT_MISMATCH,
                range,
                ARGUMENT_COUNT_MISMATCH_MESSAGE,
            );
        }
        let key = arguments
            .and_then(|arguments| arguments.first().copied())
            .unwrap_or_else(|| self.types.any());
        let value = arguments
            .and_then(|arguments| arguments.get(1).copied())
            .unwrap_or_else(|| self.types.any());
        let Some(constraint) = self.record_key_constraint(key) else {
            self.emit(
                ARGUMENT_NOT_ASSIGNABLE,
                range,
                ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
            );
            return self.types.error_type();
        };
        if self.record_key_validity(constraint) == RecordKeyState::Invalid {
            self.emit(
                ARGUMENT_NOT_ASSIGNABLE,
                range,
                ARGUMENT_NOT_ASSIGNABLE_MESSAGE,
            );
            return self.types.error_type();
        }
        self.types.record(key, value)
    }

    fn intrinsic_partial_type(&mut self, arguments: Option<&[TypeId]>, range: TextRange) -> TypeId {
        if arguments.is_none_or(|arguments| arguments.len() != 1) {
            self.emit(
                ARGUMENT_COUNT_MISMATCH,
                range,
                ARGUMENT_COUNT_MISMATCH_MESSAGE,
            );
        }
        let input = arguments
            .and_then(|arguments| arguments.first().copied())
            .unwrap_or_else(|| self.types.any());
        let view = self.types.indexed_access_view(input);
        match self.types.get(view).clone() {
            Type::Record { key, value } => {
                let value = self.types.union(&[value, self.types.undefined_type()]);
                self.types.record(key, value)
            }
            Type::ObjectType(mut object) => {
                for property in &mut object.properties {
                    property.optional = true;
                }
                for signature in &mut object.index_signatures {
                    signature.value_type = self
                        .types
                        .union(&[signature.value_type, self.types.undefined_type()]);
                }
                self.types.object_type_with_members(object)
            }
            Type::Any | Type::Error => view,
            _ => self.types.error_type(),
        }
    }

    fn record_key_constraint(&self, key: TypeId) -> Option<TypeId> {
        match self.types.get(key) {
            Type::Named(_) => self.types.type_parameter_constraint_view(key).ok(),
            _ => Some(key),
        }
    }

    fn record_key_validity(&mut self, key: TypeId) -> RecordKeyState {
        self.record_key_validity_inner(key, &mut HashSet::new())
    }

    fn record_key_validity_inner(
        &mut self,
        key: TypeId,
        seen: &mut HashSet<SymbolId>,
    ) -> RecordKeyState {
        match self.types.get(key).clone() {
            Type::String
            | Type::Number
            | Type::Symbol
            | Type::StringLiteral(_)
            | Type::NumberLiteral(_)
            | Type::Any
            | Type::Never => RecordKeyState::Concrete,
            Type::Keyof(_) => RecordKeyState::Deferred,
            Type::IndexedAccess { .. } => RecordKeyState::Invalid,
            Type::Named(symbol) => {
                if !seen.insert(symbol) {
                    return RecordKeyState::Invalid;
                }
                let constraint = self.types.type_parameter_constraint(symbol);
                let state = if let Some(constraint) = constraint {
                    self.record_key_validity_inner(constraint, seen)
                } else {
                    let resolved = self.resolve_named_type_symbol(symbol);
                    if resolved == key {
                        RecordKeyState::Invalid
                    } else {
                        self.record_key_validity_inner(resolved, seen)
                    }
                };
                seen.remove(&symbol);
                state
            }
            Type::Union(members) => {
                let mut state = RecordKeyState::Concrete;
                for member in members {
                    match self.record_key_validity_inner(member, seen) {
                        RecordKeyState::Invalid => return RecordKeyState::Invalid,
                        RecordKeyState::Deferred => state = RecordKeyState::Deferred,
                        RecordKeyState::Concrete => {}
                    }
                }
                state
            }
            Type::Intersection(members) => {
                let mut deferred = false;
                for member in members {
                    match self.record_key_validity_inner(member, seen) {
                        RecordKeyState::Concrete => return RecordKeyState::Concrete,
                        RecordKeyState::Deferred => deferred = true,
                        RecordKeyState::Invalid => {}
                    }
                }
                if deferred {
                    RecordKeyState::Deferred
                } else {
                    RecordKeyState::Invalid
                }
            }
            _ => RecordKeyState::Invalid,
        }
    }

    fn resolve_import_equals_type_symbol(&mut self, symbol: SymbolId) -> TypeId {
        match self.type_state[symbol.get() as usize] {
            TypeState::Done(id) => return id,
            TypeState::InProgress => return self.types.error_type(),
            TypeState::Unresolved => {}
        }
        self.type_state[symbol.get() as usize] = TypeState::InProgress;
        let target = self
            .import_equals_targets
            .get(&symbol)
            .and_then(|target| target.ty.or(target.value));
        let resolved = match target {
            Some(target) => self.resolve_named_type_symbol(target),
            None => self.types.error_type(),
        };
        self.type_state[symbol.get() as usize] = TypeState::Done(resolved);
        resolved
    }

    fn resolve_entity_name_scope(
        &self,
        name: &EntityName,
        scope: ScopeId,
    ) -> Result<(ScopeId, Vec<SymbolId>), EntityNameScopeError> {
        match name {
            EntityName::Identifier(identifier) => {
                let name = self.identifier_text(identifier);
                let Some(symbol) = self
                    .lookup_value(scope, &name)
                    .or_else(|| self.lookup_type(scope, &name))
                else {
                    return Err(EntityNameScopeError::Unresolved);
                };
                let member_scope = self.entity_name_member_scope(symbol)?;
                Ok((member_scope, vec![symbol]))
            }
            EntityName::Qualified { left, right } => {
                let (member_scope, mut path) = self.resolve_entity_name_scope(left, scope)?;
                let name = self.identifier_text(right);
                let Some(symbol) = self.scopes[member_scope.0 as usize]
                    .value(&name)
                    .or_else(|| self.scopes[member_scope.0 as usize].type_binding(&name))
                else {
                    return Err(EntityNameScopeError::MissingMember(right.range()));
                };
                let child_scope = self.entity_name_member_scope(symbol)?;
                path.push(symbol);
                Ok((child_scope, path))
            }
            EntityName::Missing(_) => Err(EntityNameScopeError::Unresolved),
        }
    }

    fn resolve_qualified_import_equals(
        &mut self,
        declaration: NodeId,
        name: &'src EntityName,
        scope: ScopeId,
    ) {
        let alias = self.import_equals_symbols.get(&declaration).copied();
        let range = alias
            .map(|symbol| self.symbols[symbol.get() as usize].range)
            .unwrap_or_else(NodeId::default_range);
        match name {
            EntityName::Identifier(identifier) => {
                let text = self.identifier_text(identifier);
                let value = self.lookup_value(scope, &text);
                let ty = self.lookup_type(scope, &text);
                let Some(member) = value.or(ty) else {
                    self.emit(
                        CANNOT_FIND_NAME,
                        identifier.range(),
                        CANNOT_FIND_NAME_MESSAGE,
                    );
                    return;
                };
                self.qualified_import_paths
                    .insert(declaration, Box::new([member]));
                if let Some(alias) = alias {
                    self.import_equals_targets
                        .insert(alias, ImportEqualsTarget { value, ty });
                }
            }
            EntityName::Qualified { left, right } => {
                let (member_scope, mut path) = match self.resolve_entity_name_scope(left, scope) {
                    Ok(resolved) => resolved,
                    Err(EntityNameScopeError::NotNamespace) => {
                        self.emit(CANNOT_FIND_NAMESPACE, range, CANNOT_FIND_NAMESPACE_MESSAGE);
                        return;
                    }
                    Err(EntityNameScopeError::MissingMember(missing_range)) => {
                        self.emit(CANNOT_FIND_NAME, missing_range, CANNOT_FIND_NAME_MESSAGE);
                        return;
                    }
                    Err(EntityNameScopeError::Unresolved) => {
                        if self.entity_name_identifier_is_unresolved(left, scope) {
                            self.emit(
                                CANNOT_FIND_NAMESPACE,
                                self.entity_name_range(left),
                                CANNOT_FIND_NAMESPACE_MESSAGE,
                            );
                        }
                        return;
                    }
                };
                let member_name = self.identifier_text(right);
                let value = self.scopes[member_scope.0 as usize].value(&member_name);
                let ty = self.scopes[member_scope.0 as usize].type_binding(&member_name);
                let Some(member) = value.or(ty) else {
                    self.emit(CANNOT_FIND_NAME, right.range(), CANNOT_FIND_NAME_MESSAGE);
                    return;
                };
                path.push(member);
                self.qualified_import_paths
                    .insert(declaration, path.into_boxed_slice());
                if let Some(alias) = alias {
                    self.import_equals_targets
                        .insert(alias, ImportEqualsTarget { value, ty });
                }
            }
            EntityName::Missing(_) => {}
        }
    }

    fn entity_name_range(&self, name: &EntityName) -> TextRange {
        match name {
            EntityName::Identifier(identifier) => identifier.range(),
            EntityName::Qualified { left, .. } => self.entity_name_range(left),
            EntityName::Missing(_) => NodeId::default_range(),
        }
    }

    fn entity_name_identifier_is_unresolved(&self, name: &EntityName, scope: ScopeId) -> bool {
        match name {
            EntityName::Identifier(identifier) => {
                let text = self.identifier_text(identifier);
                self.lookup_value(scope, &text).is_none()
                    && self.lookup_type(scope, &text).is_none()
            }
            EntityName::Qualified { left, .. } => {
                self.entity_name_identifier_is_unresolved(left, scope)
            }
            EntityName::Missing(_) => true,
        }
    }

    fn entity_name_member_scope(&self, symbol: SymbolId) -> Result<ScopeId, EntityNameScopeError> {
        let Some(member_scope) = self.container_member_scope(symbol) else {
            return Err(match self.symbols[symbol.get() as usize].kind {
                SymbolKind::Namespace | SymbolKind::Enum => EntityNameScopeError::Unresolved,
                SymbolKind::Import | SymbolKind::IntrinsicValue | SymbolKind::IntrinsicType => {
                    EntityNameScopeError::Unresolved
                }
                _ => EntityNameScopeError::NotNamespace,
            });
        };
        Ok(member_scope)
    }

    fn direct_container_member_scope(&self, symbol: SymbolId) -> Option<ScopeId> {
        self.namespace_export_scopes
            .get(&symbol)
            .or_else(|| self.enum_member_scopes.get(&symbol))
            .copied()
    }

    pub(crate) fn container_member_scope(&self, symbol: SymbolId) -> Option<ScopeId> {
        let mut pending = vec![symbol];
        let mut seen = HashSet::new();
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(member_scope) = self.direct_container_member_scope(current) {
                return Some(member_scope);
            }
            if self.symbols[current.get() as usize].kind != SymbolKind::Import {
                continue;
            }
            let Some(target) = self.import_equals_targets.get(&current) else {
                continue;
            };
            // Push type then value so the value plane is tried first.
            if let Some(ty) = target.ty {
                pending.push(ty);
            }
            if let Some(value) = target.value {
                pending.push(value);
            }
        }
        None
    }

    pub(crate) fn resolve_type_symbol(&mut self, symbol: SymbolId) -> TypeId {
        match self.type_state[symbol.get() as usize] {
            TypeState::Done(id) => return id,
            TypeState::InProgress
                if self.symbols[symbol.get() as usize].kind == SymbolKind::Interface
                    || self.types.has_alias(symbol) =>
            {
                return self.types.named(symbol);
            }
            TypeState::InProgress => return self.types.error_type(),
            TypeState::Unresolved => {}
        }
        let Some(definition) = self.type_defs.get(&symbol).copied() else {
            let id = self.types.error_type();
            self.type_state[symbol.get() as usize] = TypeState::Done(id);
            return id;
        };
        self.type_state[symbol.get() as usize] = TypeState::InProgress;
        let resolved = match definition {
            TypeDef::Alias {
                scope,
                type_parameters,
                node,
            } => {
                let root_resolution = self.alias_resolution_stack.is_empty();
                if root_resolution {
                    self.alias_resolution_dependencies.clear();
                } else {
                    self.alias_resolution_dependencies.insert(symbol);
                }
                self.alias_resolution_stack.push(symbol);
                if self.types.begin_alias_bounds(symbol) {
                    let bounds = self.signature_type_parameters(type_parameters, scope).1;
                    self.types.finish_alias_bounds(symbol, bounds);
                }
                let raw = self.resolve_type(node, scope);
                self.types.publish_alias_template(symbol, raw);
                let popped = self.alias_resolution_stack.pop();
                debug_assert_eq!(popped, Some(symbol));
                if self.alias_resolution_stack.is_empty() {
                    self.alias_resolution_dependencies.clear();
                }
                raw
            }
            TypeDef::Interface {
                scope,
                type_parameters,
            } => {
                let head = self.types.named(symbol);
                let is_generic = self.types.has_class(symbol);
                if is_generic && self.types.begin_class_bounds(symbol) {
                    let bounds = self.signature_type_parameters(type_parameters, scope).1;
                    self.types.finish_class_bounds(symbol, bounds);
                }
                let declarations = self
                    .interface_merges
                    .get(&symbol)
                    .cloned()
                    .unwrap_or_default();
                let mut merged = ObjectType {
                    properties: Vec::new(),
                    call_signatures: Vec::new(),
                    construct_signatures: Vec::new(),
                    index_signatures: Vec::new(),
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: None,
                };
                for interface in declarations {
                    let base =
                        self.resolve_interface_type(scope, &interface.extends, &interface.members);
                    let base = self.types.indexed_access_view(base);
                    if let Type::ObjectType(object) = self.types.get(base).clone() {
                        merged.generator_return =
                            match (merged.generator_return, object.generator_return) {
                                (None, return_type) => return_type,
                                (return_type, None) => return_type,
                                (Some(left), Some(right)) => {
                                    Some(self.types.intersection(vec![left, right]))
                                }
                            };
                        merged.iterator_property =
                            match (merged.iterator_property.take(), object.iterator_property) {
                                (None, property) => property,
                                (property, None) => property,
                                (Some(left), Some(right)) => {
                                    Some(self.merge_iterator_properties(left, right))
                                }
                            };
                        merged.async_iterator_property = match (
                            merged.async_iterator_property.take(),
                            object.async_iterator_property,
                        ) {
                            (None, property) => property,
                            (property, None) => property,
                            (Some(left), Some(right)) => {
                                Some(self.merge_iterator_properties(left, right))
                            }
                        };
                        merged.properties.extend(object.properties);
                        for signature in object.call_signatures {
                            if !merged.call_signatures.contains(&signature) {
                                merged.call_signatures.push(signature);
                            }
                        }
                        for signature in object.construct_signatures {
                            if !merged.construct_signatures.contains(&signature) {
                                merged.construct_signatures.push(signature);
                            }
                        }
                        for signature in object.index_signatures {
                            if !merged.index_signatures.contains(&signature) {
                                merged.index_signatures.push(signature);
                            }
                        }
                    }
                }
                let structure = self.types.object_type_with_members(merged);
                self.types.set_interface_structure(symbol, structure);
                if is_generic {
                    self.types.publish_final_class_template(symbol, structure);
                    self.types.declared_class(symbol).unwrap_or(head)
                } else {
                    head
                }
            }
            TypeDef::Enum { numeric } => {
                if numeric {
                    self.types.numeric_enum(symbol)
                } else {
                    self.types.named(symbol)
                }
            }
        };
        self.symbol_types[symbol.get() as usize] = resolved;
        self.type_state[symbol.get() as usize] = TypeState::Done(resolved);
        resolved
    }

    fn resolve_interface_type(
        &mut self,
        scope: ScopeId,
        extends: &'src [TypeReference],
        members: &'src [crate::syntax::TypeMemberNode],
    ) -> TypeId {
        let mut object = self.resolve_type_members(members, scope);
        if let Some(owner) = self.scopes[scope.0 as usize].this_owner {
            for property in &mut object.properties {
                property.declaring_types.push(owner);
            }
            for signature in &mut object.call_signatures {
                signature.declaring_types.push(owner);
            }
            for entry in &mut object.construct_signatures {
                entry.signature.declaring_types.push(owner);
            }
            for signature in &mut object.index_signatures {
                signature.declaring_types.push(owner);
            }
            if let Some(property) = object.iterator_property.take() {
                object.iterator_property = Some(property.with_declaring_type(owner));
            }
            if let Some(property) = object.async_iterator_property.take() {
                object.async_iterator_property = Some(property.with_declaring_type(owner));
            }
        }
        let declared_properties = object.properties.len();
        let declared_iterator = object.iterator_property.is_some();
        let declared_async_iterator = object.async_iterator_property.is_some();
        for base in extends {
            let base_type = self.resolve_type_reference(
                base,
                scope,
                NodeId::default(),
                NodeId::default_range(),
            );
            if let Some(return_type) = self.types.generator_return_type(base_type) {
                object.generator_return = match object.generator_return {
                    None => Some(return_type),
                    Some(existing) => Some(self.types.intersection(vec![existing, return_type])),
                };
            }
            if let Some(base_property) = self.types.iterator_property_of(base_type, ForOfMode::Sync)
            {
                if let Some(existing) = &object.iterator_property {
                    let incompatible = if declared_iterator {
                        (existing.optional() && !base_property.optional())
                            || !self.types_assignable(existing.type_id(), base_property.type_id())
                    } else {
                        existing.optional() != base_property.optional()
                            || !TypeRelations::new_with_cancel(&self.types, self.cancel.clone())
                                .equivalent(existing.type_id(), base_property.type_id())
                    };
                    if incompatible {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            self.entity_name_range(&base.name),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                }
                object.iterator_property = Some(match object.iterator_property.take() {
                    None => base_property,
                    Some(existing) => self.merge_iterator_properties(existing, base_property),
                });
            }
            if let Some(base_property) =
                self.types.iterator_property_of(base_type, ForOfMode::Async)
            {
                if let Some(existing) = &object.async_iterator_property {
                    let incompatible = if declared_async_iterator {
                        (existing.optional() && !base_property.optional())
                            || !self.types_assignable(existing.type_id(), base_property.type_id())
                    } else {
                        existing.optional() != base_property.optional()
                            || !TypeRelations::new_with_cancel(&self.types, self.cancel.clone())
                                .equivalent(existing.type_id(), base_property.type_id())
                    };
                    if incompatible {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            self.entity_name_range(&base.name),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                }
                object.async_iterator_property =
                    Some(match object.async_iterator_property.take() {
                        None => base_property,
                        Some(existing) => self.merge_iterator_properties(existing, base_property),
                    });
            }
            let base_view = self.types.indexed_access_view(base_type);
            if let Type::ObjectType(base_object) = self.types.get(base_view).clone() {
                for base_property in &base_object.properties {
                    let declared = object.properties[..declared_properties]
                        .iter()
                        .find(|property| property.name() == base_property.name());
                    let inherited = object.properties[declared_properties..]
                        .iter()
                        .find(|property| property.name() == base_property.name());
                    let incompatible = declared.is_some_and(|property| {
                        (property.optional() && !base_property.optional())
                            || !self.types_assignable(property.type_id(), base_property.type_id())
                    }) || inherited.is_some_and(|property| {
                        property.optional() != base_property.optional()
                            || !TypeRelations::new_with_cancel(&self.types, self.cancel.clone())
                                .equivalent(property.type_id(), base_property.type_id())
                    });
                    if incompatible {
                        self.emit(
                            TYPE_NOT_ASSIGNABLE,
                            self.entity_name_range(&base.name),
                            NOT_ASSIGNABLE_MESSAGE,
                        );
                    }
                    object.properties.push(base_property.clone());
                }
                for base_signature in &base_object.call_signatures {
                    if !object.call_signatures.contains(base_signature) {
                        object.call_signatures.push(base_signature.clone());
                    }
                }
                for base_signature in &base_object.construct_signatures {
                    if !object.construct_signatures.contains(base_signature) {
                        object.construct_signatures.push(base_signature.clone());
                    }
                }
                for base_signature in &base_object.index_signatures {
                    if !object.index_signatures.contains(base_signature) {
                        object.index_signatures.push(base_signature.clone());
                    }
                }
            }
        }
        self.types.object_type_with_members(object)
    }

    fn resolve_object_type(
        &mut self,
        members: &'src [crate::syntax::TypeMemberNode],
        scope: ScopeId,
    ) -> TypeId {
        let object = self.resolve_type_members(members, scope);
        self.types.object_type_with_members(object)
    }

    fn resolve_type_members(
        &mut self,
        members: &'src [crate::syntax::TypeMemberNode],
        scope: ScopeId,
    ) -> ObjectType {
        let mut object = ObjectType {
            properties: Vec::new(),
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        };
        for member in members {
            match member.data() {
                TypeMember::Property(property) => {
                    self.resolve_property_name(&property.name, scope);
                    if let Some(protocol) = self.intrinsic_symbol_iterator_protocol(&property.name)
                    {
                        let method = match &property.type_annotation {
                            Some(annotation) => {
                                self.resolve_type(&annotation.data().type_node, scope)
                            }
                            None => self.types.any(),
                        };
                        let property = IteratorProperty::new(method, property.optional);
                        let target = match protocol {
                            ForOfMode::Sync => &mut object.iterator_property,
                            ForOfMode::Async => &mut object.async_iterator_property,
                        };
                        *target = Some(match target.take() {
                            None => property,
                            Some(existing) => self.merge_iterator_properties(existing, property),
                        });
                        continue;
                    }
                    if let Some(name) = self.property_key(&property.name) {
                        let type_id = match &property.type_annotation {
                            Some(annotation) => {
                                self.resolve_type(&annotation.data().type_node, scope)
                            }
                            None => self.types.any(),
                        };
                        object.properties.push(
                            PropertyType::new(name, property.optional, type_id)
                                .with_readonly(property.readonly),
                        );
                    }
                }
                TypeMember::Method(method) => {
                    self.resolve_property_name(&method.name, scope);
                    if let Some(protocol) = self.intrinsic_symbol_iterator_protocol(&method.name) {
                        if self.no_implicit_any && method.function.return_type_missing {
                            self.emit(
                                MISSING_METHOD_RETURN_TYPE,
                                member.range(),
                                MISSING_METHOD_RETURN_TYPE_MESSAGE,
                            );
                        }
                        let method_type = self.resolve_function_type(&method.function, scope);
                        let property =
                            IteratorProperty::new(method_type, method.optional).with_method(true);
                        let target = match protocol {
                            ForOfMode::Sync => &mut object.iterator_property,
                            ForOfMode::Async => &mut object.async_iterator_property,
                        };
                        *target = Some(match target.take() {
                            None => property,
                            Some(existing) => self.merge_iterator_properties(existing, property),
                        });
                        continue;
                    }
                    if let Some(name) = self.property_key(&method.name) {
                        if self.no_implicit_any && method.function.return_type_missing {
                            self.emit(
                                MISSING_METHOD_RETURN_TYPE,
                                member.range(),
                                MISSING_METHOD_RETURN_TYPE_MESSAGE,
                            );
                        }
                        let type_id = self.resolve_function_type(&method.function, scope);
                        object.properties.push(
                            PropertyType::new(name, method.optional, type_id).with_method(true),
                        );
                    }
                }
                TypeMember::Call(call) => {
                    if self.no_implicit_any && call.function.return_type_missing {
                        self.emit(
                            MISSING_METHOD_RETURN_TYPE,
                            member.range(),
                            MISSING_METHOD_RETURN_TYPE_MESSAGE,
                        );
                    }
                    object
                        .call_signatures
                        .push(self.resolve_function_signature(&call.function, scope));
                }
                TypeMember::Construct(construct) => {
                    if self.no_implicit_any && construct.function.function.return_type_missing {
                        self.emit(
                            MISSING_METHOD_RETURN_TYPE,
                            member.range(),
                            MISSING_METHOD_RETURN_TYPE_MESSAGE,
                        );
                    }
                    object.construct_signatures.push(ConstructEntry {
                        signature: self
                            .resolve_function_signature(&construct.function.function, scope),
                        is_abstract: construct.function.is_abstract,
                    });
                }
                TypeMember::Index(index) => {
                    let parameters = index
                        .parameters
                        .iter()
                        .map(|parameter| {
                            FunctionParameter::new(
                                self.identifier_text(&parameter.name).into_owned(),
                                self.resolve_type(
                                    &parameter.type_annotation.data().type_node,
                                    scope,
                                ),
                                parameter.optional,
                                parameter.rest,
                            )
                        })
                        .collect();
                    let value_type =
                        self.resolve_type(&index.type_annotation.data().type_node, scope);
                    object.index_signatures.push(IndexSignature {
                        readonly: index.readonly,
                        parameters,
                        value_type,
                        declaring_types: Vec::new(),
                    });
                }
                TypeMember::Missing(_) => {}
            }
        }
        object
    }

    fn resolve_function_type(&mut self, function: &'src FunctionType, scope: ScopeId) -> TypeId {
        let signature = self.resolve_function_signature(function, scope);
        self.types.intern(Type::Function(signature))
    }

    fn resolve_function_signature(
        &mut self,
        function: &'src FunctionType,
        scope: ScopeId,
    ) -> FunctionSignature {
        let child = self.new_scope(ScopeKind::Function, Some(scope));
        self.bind_type_parameters(function.type_parameters.as_ref(), child);
        let mut parameters: Vec<FunctionParameter> = Vec::with_capacity(function.parameters.len());
        for parameter in &function.parameters {
            if self.identifier_text(&parameter.name).as_ref() == "this" {
                continue;
            }
            let type_id = self.resolve_type(&parameter.type_annotation.data().type_node, child);
            if parameter.rest && !self.is_valid_rest_parameter_type(type_id) {
                self.emit(
                    TYPE_NOT_ASSIGNABLE,
                    parameter.type_annotation.range(),
                    NOT_ASSIGNABLE_MESSAGE,
                );
            }
            parameters.push(FunctionParameter::new(
                self.identifier_text(&parameter.name).into_owned(),
                type_id,
                parameter.optional,
                parameter.rest,
            ));
        }
        let return_type = self.resolve_type(&function.return_type, child);
        let (type_parameters, type_parameter_bounds) =
            self.signature_type_parameters(function.type_parameters.as_ref(), child);
        FunctionSignature {
            type_parameters,
            type_parameter_bounds,
            parameters,
            return_type,
            declaring_types: Vec::new(),
            javascript: false,
        }
    }

    fn semantic_property_key(value: &EcmaString) -> String {
        const HEX: &[u8; 16] = b"0123456789ABCDEF";

        let mut key = String::with_capacity(value.as_units().len());
        for decoded in char::decode_utf16(value.as_units().iter().copied()) {
            match decoded {
                Ok('\0') => key.push_str("\0\0"),
                Ok(character) => key.push(character),
                Err(error) => {
                    let unit = error.unpaired_surrogate();
                    key.push('\0');
                    key.push('u');
                    for shift in [12, 8, 4, 0] {
                        key.push(HEX[usize::from((unit >> shift) & 0xF)] as char);
                    }
                }
            }
        }
        key
    }

    fn intrinsic_symbol_iterator_protocol(&self, name: &PropertyName) -> Option<ForOfMode> {
        let PropertyName::Computed(expression) = name else {
            return None;
        };
        let Expression::Member(member) = expression.data() else {
            return None;
        };
        let Expression::Identifier(object) = member.object.data() else {
            return None;
        };
        let MemberProperty::Named(property) = &member.property else {
            return None;
        };
        if self.identifier_text(object) != "Symbol"
            || !self
                .resolved_expression_reference(&member.object)
                .is_some_and(|symbol| {
                    self.symbols[symbol.get() as usize].kind == SymbolKind::IntrinsicValue
                })
        {
            return None;
        }
        match self.identifier_text(property).as_ref() {
            "iterator" => Some(ForOfMode::Sync),
            "asyncIterator" => Some(ForOfMode::Async),
            _ => None,
        }
    }
    fn property_key(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Identifier(identifier) => {
                Some(self.identifier_text(identifier).into_owned())
            }
            PropertyName::String(string) => string_value(self.text(string.data().token()))
                .map(|value| Self::semantic_property_key(&value)),
            PropertyName::Number(number) => {
                number_value(self.text(number.data().token())).map(format_number)
            }
            PropertyName::Computed(expression) => match expression.data() {
                Expression::Literal(Literal::String(string)) => {
                    string_value(self.text(string.data().token()))
                        .map(|value| Self::semantic_property_key(&value))
                }
                Expression::Literal(Literal::Number(number)) => {
                    number_value(self.text(number.data().token())).map(format_number)
                }
                _ => None,
            },
            PropertyName::Private(_) | PropertyName::Missing(_) => None,
        }
    }

    /// The symbol-table key a container member declaration binds under.
    /// Private names bind under their `#`-prefixed source spelling so
    /// declarations and references render `Foo.#name` upstream; the ordinary
    /// `property_key` keeps excluding them because private names must never
    /// surface as structural properties of the instance type.
    fn member_symbol_key(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Private(identifier) => {
                Some(self.text(identifier.data().token()).to_owned())
            }
            other => self.property_key(other),
        }
    }

    fn fresh_object_candidates(&mut self, target: TypeId) -> Vec<ObjectType> {
        let target = self.types.non_nullable(target);
        let target = self
            .types
            .prepare_applied_alias_view(target)
            .unwrap_or(target);
        let target = self
            .types
            .prepare_applied_class_view(target)
            .unwrap_or(target);
        let target = self.types.named_structural_view(target);
        match self.types.get(target).clone() {
            Type::Union(members) => members
                .into_iter()
                .filter_map(|member| self.fresh_object_candidate(member))
                .collect(),
            _ => self.fresh_object_candidate(target).into_iter().collect(),
        }
    }

    fn fresh_object_candidate(&mut self, target: TypeId) -> Option<ObjectType> {
        let target = self
            .types
            .prepare_applied_alias_view(target)
            .unwrap_or(target);
        let target = self
            .types
            .prepare_applied_class_view(target)
            .unwrap_or(target);
        let structural = self.types.named_structural_view(target);
        if structural != target {
            return self.fresh_object_candidate(structural);
        }
        match self.types.get(target).clone() {
            Type::ObjectType(object) => Some(object),
            Type::Intersection(members) => {
                let mut combined = ObjectType {
                    properties: Vec::new(),
                    call_signatures: Vec::new(),
                    construct_signatures: Vec::new(),
                    index_signatures: Vec::new(),
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: None,
                };
                let mut found = false;
                for member in members {
                    let Some(object) = self.fresh_object_candidate(member) else {
                        continue;
                    };
                    found = true;
                    combined.properties.extend(object.properties);
                    combined.call_signatures.extend(object.call_signatures);
                    combined
                        .construct_signatures
                        .extend(object.construct_signatures);
                    combined.index_signatures.extend(object.index_signatures);
                }
                found.then_some(combined)
            }
            Type::Named(symbol) => {
                let resolved = self
                    .types
                    .type_parameter_constraint(symbol)
                    .unwrap_or(self.symbol_types[symbol.get() as usize]);
                (resolved != target)
                    .then(|| self.fresh_object_candidate(resolved))
                    .flatten()
            }
            _ => None,
        }
    }

    fn object_property_target(&self, object: &ObjectType, key: &str) -> Option<TypeId> {
        if let Some(property) = object
            .properties
            .iter()
            .find(|property| property.name() == key)
        {
            return Some(property.type_id());
        }
        let numeric = key.parse::<usize>().is_ok();
        object.index_signatures.iter().find_map(|signature| {
            let parameter = signature.parameters.first()?;
            match self.types.get(parameter.type_id()) {
                Type::String => Some(signature.value_type),
                Type::Number if numeric => Some(signature.value_type),
                _ => None,
            }
        })
    }

    fn literal_discriminant_type(&self, type_id: TypeId) -> bool {
        match self.types.get(type_id) {
            Type::BooleanLiteral(_)
            | Type::NumberLiteral(_)
            | Type::StringLiteral(_)
            | Type::BigIntLiteral(_) => true,
            Type::Union(members) => members
                .iter()
                .all(|member| self.literal_discriminant_type(*member)),
            _ => false,
        }
    }

    fn filter_discriminated_candidates(
        &mut self,
        object: &'src ObjectLiteral,
        mut candidates: Vec<ObjectType>,
    ) -> Vec<ObjectType> {
        for member in &object.members {
            let ObjectMember::Property(property) = member.data() else {
                continue;
            };
            let Some(name) = self.property_key(&property.name) else {
                continue;
            };
            let Expression::Literal(literal) = property.value.data() else {
                continue;
            };
            let targets: Vec<_> = candidates
                .iter()
                .filter_map(|candidate| {
                    candidate
                        .properties
                        .iter()
                        .find(|property| property.name() == name)
                        .map(PropertyType::type_id)
                })
                .collect();
            if targets.len() != candidates.len()
                || !targets
                    .iter()
                    .all(|target| self.literal_discriminant_type(*target))
            {
                continue;
            }
            let source = self.type_of_literal(literal);
            let filtered: Vec<_> = candidates
                .into_iter()
                .zip(targets)
                .filter_map(|(candidate, target)| {
                    self.types_assignable(source, target).then_some(candidate)
                })
                .collect();
            if filtered.is_empty() {
                return Vec::new();
            }
            candidates = filtered;
        }
        candidates
    }

    fn fresh_excess_property_ranges(
        &mut self,
        expression: &'src Expr,
        target: TypeId,
        recurse: bool,
    ) -> Vec<TextRange> {
        match expression.data() {
            Expression::Object(object) => {
                let candidates = self.fresh_object_candidates(target);
                if candidates.is_empty() {
                    return Vec::new();
                }
                if candidates.iter().any(|candidate| {
                    candidate.properties.is_empty()
                        && candidate.call_signatures.is_empty()
                        && candidate.construct_signatures.is_empty()
                        && candidate.index_signatures.is_empty()
                }) {
                    return Vec::new();
                }
                let candidates = self.filter_discriminated_candidates(object, candidates);
                if candidates.is_empty() {
                    return Vec::new();
                }
                let mut ranges = Vec::new();
                for member in &object.members {
                    let (name, value) = match member.data() {
                        ObjectMember::Property(property) => {
                            (self.property_key(&property.name), Some(&property.value))
                        }
                        ObjectMember::Method(method) => (self.property_key(&method.name), None),
                        ObjectMember::Spread(_) | ObjectMember::Missing(_) => continue,
                    };
                    let Some(name) = name else {
                        continue;
                    };
                    let property_targets: Vec<_> = candidates
                        .iter()
                        .filter_map(|candidate| self.object_property_target(candidate, &name))
                        .collect();
                    if property_targets.is_empty() {
                        ranges.push(member.range());
                        continue;
                    }
                    if recurse && let Some(value) = value {
                        let target = self.types.union(&property_targets);
                        ranges.extend(self.fresh_excess_property_ranges(value, target, true));
                    }
                }
                ranges
            }
            Expression::Array(array) if recurse => {
                let target = self.types.non_nullable(target);
                let (target_shape, array_target) = match self.types.get(target).clone() {
                    Type::Tuple(shape) => (Some(shape), None),
                    Type::Array(element) => (None, Some(element)),
                    _ => return Vec::new(),
                };
                let source_length = array.elements.len();
                let mut ranges = Vec::new();
                for (index, element) in array.elements.iter().enumerate() {
                    let ArrayElement::Expression(inner) = element else {
                        continue;
                    };
                    let element_target = target_shape
                        .as_ref()
                        .and_then(|shape| {
                            let elements = shape.element_types_at_length(index, source_length);
                            (!elements.is_empty()).then(|| self.types.union(&elements))
                        })
                        .or(array_target);
                    if let Some(target) = element_target {
                        ranges.extend(self.fresh_excess_property_ranges(inner, target, true));
                    }
                }
                ranges
            }
            Expression::Conditional(conditional) if recurse => {
                let mut ranges =
                    self.fresh_excess_property_ranges(&conditional.consequent, target, true);
                ranges.extend(self.fresh_excess_property_ranges(
                    &conditional.alternate,
                    target,
                    true,
                ));
                ranges
            }
            _ => Vec::new(),
        }
    }

    fn intrinsic_iterator_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
        protocol: ForOfMode,
    ) -> TypeId {
        match protocol {
            ForOfMode::Sync => self
                .types
                .sync_iterator_type(yield_type, return_type, next_type),
            ForOfMode::Async => {
                let done_false = self.types.boolean_literal(false);
                let done_true = self.types.boolean_literal(true);
                let yield_result = self.types.object_type(vec![
                    PropertyType::new("value", false, yield_type),
                    PropertyType::new("done", true, done_false),
                ]);
                let return_result = self.types.object_type(vec![
                    PropertyType::new("value", false, return_type),
                    PropertyType::new("done", false, done_true),
                ]);
                let result = self.types.union(&[yield_result, return_result]);
                let next_result = self.promise_type(result);
                let next = self.types.function_with_parameters(
                    Vec::new(),
                    vec![FunctionParameter::new(
                        "value".to_owned(),
                        next_type,
                        true,
                        false,
                    )],
                    next_result,
                );
                self.types.object_type(vec![
                    PropertyType::new("next", false, next).with_method(true),
                ])
            }
        }
    }

    fn intrinsic_iterable_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
        protocol: ForOfMode,
    ) -> TypeId {
        match protocol {
            ForOfMode::Sync => self
                .types
                .sync_iterable_type(yield_type, return_type, next_type),
            ForOfMode::Async => {
                let iterator =
                    self.intrinsic_iterator_type(yield_type, return_type, next_type, protocol);
                let method = self.types.function(Vec::new(), iterator);
                let property = IteratorProperty::new(method, false).with_method(true);
                self.types.object_type_with_members(ObjectType {
                    properties: Vec::new(),
                    call_signatures: Vec::new(),
                    construct_signatures: Vec::new(),
                    index_signatures: Vec::new(),
                    generator_return: None,
                    iterator_property: None,
                    async_iterator_property: Some(property),
                })
            }
        }
    }

    fn intrinsic_iterable_iterator_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
        protocol: ForOfMode,
    ) -> TypeId {
        let iterator = self.intrinsic_iterator_type(yield_type, return_type, next_type, protocol);
        let iterable = self.intrinsic_iterable_type(yield_type, return_type, next_type, protocol);
        self.types.intersection(vec![iterator, iterable])
    }

    fn intrinsic_generator_type(
        &mut self,
        yield_type: TypeId,
        return_type: TypeId,
        next_type: TypeId,
        protocol: ForOfMode,
    ) -> TypeId {
        let iterable =
            self.intrinsic_iterable_iterator_type(yield_type, return_type, next_type, protocol);
        let marker = self.types.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: Some(return_type),
            iterator_property: None,
            async_iterator_property: None,
        });
        self.types.intersection(vec![iterable, marker])
    }

    fn promise_type(&mut self, value: TypeId) -> TypeId {
        let any = self.types.any();
        self.types.object_type(vec![
            PropertyType::new("__bamts_promise_value", false, value),
            PropertyType::new("then", false, any),
            PropertyType::new("catch", false, any),
            PropertyType::new("finally", false, any),
        ])
    }

    fn promise_value_type(&mut self, promise: TypeId) -> Option<TypeId> {
        self.types.property_type(promise, "__bamts_promise_value")
    }

    fn awaited_type(&mut self, value: TypeId) -> TypeId {
        self.awaited_type_inner(value, &mut HashSet::new())
    }

    fn awaited_type_inner(&mut self, value: TypeId, visiting: &mut HashSet<TypeId>) -> TypeId {
        if !visiting.insert(value) {
            return value;
        }
        let awaited = match self.types.get(value).clone() {
            Type::Union(members) => {
                let mut awaited = Vec::with_capacity(members.len());
                for member in members {
                    awaited.push(self.awaited_type_inner(member, visiting));
                }
                self.types.union(&awaited)
            }
            _ => match self.promise_value_type(value) {
                Some(payload) => self.awaited_type_inner(payload, visiting),
                None => value,
            },
        };
        visiting.remove(&value);
        awaited
    }

    // -- expression typing (bounded, permissive) -------------------------------

    pub(crate) fn type_of_expr(&mut self, expression: &'src Expr, scope: ScopeId) -> TypeId {
        if let Some(&cached) = self.node_types.get(&expression.id()) {
            return cached;
        }
        let result = self.compute_type_of_expr(expression, scope);
        if !self.probing_contextual_type
            && self.node_types.insert(expression.id(), result).is_none()
        {
            self.typed_expressions.push((expression.range(), result));
        }
        result
    }

    fn type_of_expr_with_target(
        &mut self,
        expression: &'src Expr,
        target: TypeId,
        scope: ScopeId,
    ) -> TypeId {
        let result = match expression.data() {
            Expression::Array(array)
                if !array
                    .elements
                    .iter()
                    .any(|element| matches!(element, ArrayElement::Spread(_))) =>
            {
                let target = self.types.non_nullable(target);
                let (target_shape, array_target) = self.contextual_array_target(target);
                if target_shape.is_none() && array_target.is_none() {
                    return self.type_of_expr(expression, scope);
                }
                let mut element_types = Vec::with_capacity(array.elements.len());
                let source_length = array.elements.len();
                for (index, element) in array.elements.iter().enumerate() {
                    let element_type = match element {
                        ArrayElement::Expression(inner) => {
                            let element_target = target_shape
                                .as_ref()
                                .and_then(|shape| {
                                    let elements =
                                        shape.element_types_at_length(index, source_length);
                                    (!elements.is_empty()).then(|| self.types.union(&elements))
                                })
                                .or(array_target);
                            match element_target {
                                Some(target) => self.type_of_expr_with_target(inner, target, scope),
                                None => self.type_of_expr(inner, scope),
                            }
                        }
                        ArrayElement::Elision => self.types.undefined_type(),
                        ArrayElement::Missing(_) => self.types.any(),
                        ArrayElement::Spread(_) => unreachable!("spread arrays are excluded"),
                    };
                    element_types.push(element_type);
                }
                if target_shape.is_some() {
                    self.types.tuple(element_types)
                } else {
                    let element = self.types.union(&element_types);
                    self.types.array(element)
                }
            }
            Expression::Object(object) => {
                let result =
                    self.type_of_object_literal(object, expression.id(), Some(target), scope);
                for range in self.fresh_excess_property_ranges(expression, target, false) {
                    self.emit(EXCESS_PROPERTY, range, EXCESS_PROPERTY_MESSAGE);
                }
                result
            }
            Expression::Conditional(conditional) => {
                self.type_of_conditional_expr(conditional, Some(target), scope)
            }
            _ => return self.type_of_expr(expression, scope),
        };
        if !self.probing_contextual_type
            && self.node_types.insert(expression.id(), result).is_none()
        {
            self.typed_expressions.push((expression.range(), result));
        }
        result
    }

    fn contextual_array_target(&mut self, target: TypeId) -> (Option<TupleShape>, Option<TypeId>) {
        match self.types.get(target).clone() {
            Type::Tuple(shape) => (Some(shape), None),
            Type::Array(element) => (None, Some(element)),
            Type::Union(members) => {
                let elements: Vec<_> = members
                    .into_iter()
                    .filter_map(|member| match self.types.get(member) {
                        Type::Array(element) => Some(*element),
                        _ => None,
                    })
                    .collect();
                if elements.is_empty() {
                    (None, None)
                } else {
                    (None, Some(self.types.union(&elements)))
                }
            }
            _ => (None, None),
        }
    }

    /// Checks one contextual method against every target overload.
    fn contextual_overload_method_type(&mut self, source: TypeId, target: TypeId) -> TypeId {
        fn erase_signature(types: &mut TypeTable, type_id: TypeId) -> Option<TypeId> {
            let Type::Function(signature) = types.get(type_id).clone() else {
                return None;
            };
            if signature.type_parameters().is_empty() {
                return Some(type_id);
            }
            let any = types.any();
            let arguments = signature
                .type_parameters()
                .iter()
                .copied()
                .map(|symbol| InferredTypeArgument::new(symbol, any, InferenceProvenance::Explicit))
                .collect();
            Some(InferredTypeArguments::new(arguments).instantiate_signature(types, &signature))
        }

        fn constrain_signature(types: &mut TypeTable, type_id: TypeId) -> Option<TypeId> {
            let Type::Function(signature) = types.get(type_id).clone() else {
                return None;
            };
            if signature.type_parameters().is_empty() {
                return Some(type_id);
            }
            let mut arguments = Vec::with_capacity(signature.type_parameters().len());
            for (&symbol, bound) in signature
                .type_parameters()
                .iter()
                .zip(signature.type_parameter_bounds())
            {
                let prior = InferredTypeArguments::new(arguments.clone());
                let (argument, provenance) = if let Some(constraint) = bound.constraint() {
                    (
                        prior.instantiate(types, constraint),
                        InferenceProvenance::Constraint,
                    )
                } else {
                    (types.any(), InferenceProvenance::Unknown)
                };
                arguments.push(InferredTypeArgument::new(symbol, argument, provenance));
            }
            Some(InferredTypeArguments::new(arguments).instantiate_signature(types, &signature))
        }

        let Some(target_overloads) = self.types.overload_members(target) else {
            return source;
        };
        if target_overloads.len() < 2 {
            return source;
        }
        let Some(source_overloads) = self.types.overload_members(source) else {
            return source;
        };
        let mut sources = Vec::with_capacity(source_overloads.len());
        for source_member in source_overloads {
            let (Some(erased), Some(constrained)) = (
                erase_signature(&mut self.types, source_member),
                constrain_signature(&mut self.types, source_member),
            ) else {
                return source;
            };
            sources.push((erased, constrained));
        }
        for target_member in target_overloads {
            let Type::Function(target_signature) = self.types.get(target_member) else {
                return source;
            };
            let target_is_generic = !target_signature.type_parameters().is_empty();
            let target_candidate = if target_is_generic {
                let Some(constrained) = constrain_signature(&mut self.types, target_member) else {
                    return source;
                };
                constrained
            } else {
                target_member
            };
            let compatible = sources.iter().any(|&(erased, constrained)| {
                let candidate = if target_is_generic {
                    constrained
                } else {
                    erased
                };
                self.types_assignable(candidate, target_candidate)
            });
            if !compatible {
                return source;
            }
        }
        target
    }

    fn type_of_object_literal(
        &mut self,
        object: &'src ObjectLiteral,
        literal_node: NodeId,
        contextual_target: Option<TypeId>,
        scope: ScopeId,
    ) -> TypeId {
        let owner = self
            .literal_anchor
            .get(&literal_node)
            .copied()
            .unwrap_or(PropertyOwner::Site(literal_node));
        let contextual_target = contextual_target.map(|target| self.types.non_nullable(target));
        let mut properties = Vec::new();
        let mut index_signatures = Vec::new();
        let mut iterator_property = None;
        let mut async_iterator_property = None;
        let mut accessors: BTreeMap<String, (Option<TypeId>, Option<TypeId>)> = BTreeMap::new();

        fn upsert_property(properties: &mut Vec<PropertyType>, property: PropertyType) {
            if let Some(existing) = properties
                .iter_mut()
                .find(|existing| existing.name() == property.name())
            {
                *existing = property;
            } else {
                properties.push(property);
            }
        }

        for member in &object.members {
            match member.data() {
                ObjectMember::Property(property) => {
                    if let Some(protocol) = self.intrinsic_symbol_iterator_protocol(&property.name)
                    {
                        let method_type = self.type_of_expr(&property.value, scope);
                        let property = IteratorProperty::new(method_type, false);
                        match protocol {
                            ForOfMode::Sync => iterator_property = Some(property),
                            ForOfMode::Async => async_iterator_property = Some(property),
                        }
                        continue;
                    }
                    if let Some(name) = self.property_key(&property.name) {
                        if let Some(bare) = Self::property_bare_range(&property.name) {
                            let kind = if property.shorthand {
                                PropertyAnchorKind::Shorthand
                            } else {
                                PropertyAnchorKind::Plain
                            };
                            self.record_property_anchor(owner, &name, bare, kind, true);
                        }
                        let target = contextual_target
                            .and_then(|target| self.types.read_property_type(target, &name));
                        let value_type = match target {
                            Some(target) => {
                                self.type_of_expr_with_target(&property.value, target, scope)
                            }
                            None => {
                                let inferred = self.type_of_expr(&property.value, scope);
                                self.types.widen_fresh_literal(inferred)
                            }
                        };
                        upsert_property(
                            &mut properties,
                            PropertyType::new(name, false, value_type),
                        );
                    }
                }
                ObjectMember::Method(method) => {
                    if let Some(protocol) = self.intrinsic_symbol_iterator_protocol(&method.name) {
                        let (method_type, is_method) = match method.modifier {
                            PropertyModifier::None => {
                                (self.type_of_function_like(&method.function, scope), true)
                            }
                            PropertyModifier::Get => {
                                (self.inferred_return_type(&method.function, scope), false)
                            }
                            PropertyModifier::Set => continue,
                        };
                        let property =
                            IteratorProperty::new(method_type, false).with_method(is_method);
                        match protocol {
                            ForOfMode::Sync => iterator_property = Some(property),
                            ForOfMode::Async => async_iterator_property = Some(property),
                        }
                        continue;
                    }
                    if let Some(name) = self.property_key(&method.name) {
                        match method.modifier {
                            PropertyModifier::Get => {
                                let return_type =
                                    self.inferred_return_type(&method.function, scope);
                                accessors.entry(name.clone()).or_default().0 = Some(return_type);
                                let (get, set) = accessors.get(&name).copied().unwrap_or_default();
                                let type_id = get.or(set).unwrap_or_else(|| self.types.any());
                                let type_id = if contextual_target.is_some() {
                                    type_id
                                } else {
                                    self.types.widen_fresh_literal(type_id)
                                };
                                let getter_only = get.is_some() && set.is_none();
                                upsert_property(
                                    &mut properties,
                                    PropertyType::new(name, false, type_id)
                                        .with_readonly(getter_only)
                                        .with_getter_only(getter_only),
                                );
                            }
                            PropertyModifier::Set => {
                                let method_type =
                                    self.type_of_function_like(&method.function, scope);
                                let param_type = if let Type::Function(signature) =
                                    self.types.get(method_type)
                                {
                                    signature
                                        .parameters()
                                        .first()
                                        .map(|parameter| parameter.type_id())
                                        .unwrap_or_else(|| self.types.any())
                                } else {
                                    self.types.any()
                                };
                                accessors.entry(name.clone()).or_default().1 = Some(param_type);
                                let (get, set) = accessors.get(&name).copied().unwrap_or_default();
                                let type_id = get.or(set).unwrap_or_else(|| self.types.any());
                                let type_id = if contextual_target.is_some() {
                                    type_id
                                } else {
                                    self.types.widen_fresh_literal(type_id)
                                };
                                upsert_property(
                                    &mut properties,
                                    PropertyType::new(name, false, type_id)
                                        .with_readonly(false)
                                        .with_getter_only(false),
                                );
                            }
                            _ => {
                                let method_type =
                                    self.type_of_function_like(&method.function, scope);
                                let target_type = contextual_target.and_then(|target| {
                                    self.types.read_property_type(target, &name)
                                });
                                let method_type = target_type.map_or(method_type, |target| {
                                    self.contextual_overload_method_type(method_type, target)
                                });
                                upsert_property(
                                    &mut properties,
                                    PropertyType::new(name, false, method_type),
                                );
                            }
                        }
                    }
                }
                ObjectMember::Spread(spread) => {
                    let spread_type = self.type_of_expr(&spread.argument, scope);
                    let spread_type = self
                        .types
                        .type_parameter_constraint_view(spread_type)
                        .unwrap_or(spread_type);
                    let spread_type = self.types.indexed_access_view(spread_type);
                    match self.types.get(spread_type).clone() {
                        Type::ObjectType(object) => {
                            if let Some(source_iterator) = object
                                .iterator_property
                                .filter(IteratorProperty::spreadable)
                            {
                                iterator_property = Some(source_iterator);
                            }
                            if let Some(source_iterator) = object
                                .async_iterator_property
                                .filter(IteratorProperty::spreadable)
                            {
                                async_iterator_property = Some(source_iterator);
                            }
                            for source_property in &object.properties {
                                let fresh = PropertyType::new(
                                    source_property.name.as_ref(),
                                    source_property.optional(),
                                    source_property.type_id(),
                                )
                                .with_spreadable(source_property.spreadable());
                                upsert_property(&mut properties, fresh);
                            }
                            index_signatures.extend(object.index_signatures);
                        }
                        Type::Record { key, value } => {
                            index_signatures.push(IndexSignature {
                                readonly: false,
                                parameters: vec![FunctionParameter::new(
                                    "key".to_owned(),
                                    key,
                                    false,
                                    false,
                                )],
                                value_type: value,
                                declaring_types: Vec::new(),
                            });
                        }
                        _ => {}
                    }
                    // Non-object spread operands add no properties and produce no
                    // diagnostic here because the checker has no boundary for them.
                }
                ObjectMember::Missing(_) => {}
            }
        }
        self.types.object_type_with_members(ObjectType {
            properties,
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures,
            generator_return: None,
            iterator_property,
            async_iterator_property,
        })
    }

    fn type_of_conditional_expr(
        &mut self,
        conditional: &'src ConditionalExpression,
        contextual_target: Option<TypeId>,
        scope: ScopeId,
    ) -> TypeId {
        let literal_truthy =
            if let Expression::Literal(Literal::Boolean(literal)) = conditional.test.data() {
                Some(literal.data().token().kind() == TokenKind::KwTrue)
            } else {
                None
            };
        match literal_truthy {
            Some(true) => match contextual_target {
                Some(target) => {
                    self.type_of_expr_with_target(conditional.consequent.as_ref(), target, scope)
                }
                None => self.type_of_expr(conditional.consequent.as_ref(), scope),
            },
            Some(false) => match contextual_target {
                Some(target) => {
                    self.type_of_expr_with_target(conditional.alternate.as_ref(), target, scope)
                }
                None => self.type_of_expr(conditional.alternate.as_ref(), scope),
            },
            None => {
                let parent = self.flow;
                let truthy = self.guards_for(&conditional.test, false);
                let falsy = self.guards_for(&conditional.test, true);
                let mut consequent = self.types.any();
                self.in_branch(parent, &truthy, |binder| {
                    consequent = match contextual_target {
                        Some(target) => binder.type_of_expr_with_target(
                            conditional.consequent.as_ref(),
                            target,
                            scope,
                        ),
                        None => binder.type_of_expr(conditional.consequent.as_ref(), scope),
                    };
                });
                let mut alternate = self.types.any();
                self.in_branch(parent, &falsy, |binder| {
                    alternate = match contextual_target {
                        Some(target) => binder.type_of_expr_with_target(
                            conditional.alternate.as_ref(),
                            target,
                            scope,
                        ),
                        None => binder.type_of_expr(conditional.alternate.as_ref(), scope),
                    };
                });
                if self.types.assignable(consequent, alternate) {
                    alternate
                } else if self.types.assignable(alternate, consequent) {
                    consequent
                } else {
                    self.types.union(&[consequent, alternate])
                }
            }
        }
    }

    /// Records the `.symbols` reference rows for a member access whose base
    /// resolves directly to a class or interface symbol (`this.n`, `C.s`).
    /// Named members land at the property identifier and the whole access
    /// path; private names (`this.#p`) render the whole path only, matching
    /// upstream, which emits no bare `>#p` row. Members declared on a base
    /// class are looked up through the heritage chain, so `d.foo` with `foo`
    /// on `C` records `Symbol(C.foo, ...)`.
    fn record_symbol_member_reference_rows(
        &mut self,
        owner: SymbolId,
        property: &'src MemberProperty,
        path_range: TextRange,
    ) {
        let identifier_range = match property {
            MemberProperty::Named(identifier) => Some(identifier.range()),
            MemberProperty::Private(_) | MemberProperty::Computed(_) => None,
        };
        let Some(name) = self.member_symbol_name(property) else {
            return;
        };
        let Some(member_symbol) = self.member_symbol(owner, &name) else {
            return;
        };
        if let Some(range) = identifier_range {
            self.symbol_references.push((range, member_symbol));
        }
        self.symbol_references.push((path_range, member_symbol));
    }

    /// The member-scope key a `.symbols` member reference resolves under.
    /// Named and computed keys cook as ordinary properties; private names
    /// keep their `#`-prefixed source spelling (`Foo.#name` upstream).
    fn member_symbol_name(&self, property: &MemberProperty) -> Option<EcmaString> {
        match property {
            MemberProperty::Private(identifier) => {
                Some(EcmaString::encode(self.text(identifier.data().token())))
            }
            other => enum_plan::cook_member_property_name(self.source, other),
        }
    }

    /// Looks a member up in the owner's member scope, walking base classes so
    /// inherited members resolve to the base class's declaring symbol.
    fn member_symbol(&self, owner: SymbolId, name: &EcmaString) -> Option<SymbolId> {
        let mut current = Some(owner);
        let mut visited = HashSet::new();
        while let Some(owner) = current
            && visited.insert(owner)
        {
            if let Some(member_scope) = self.container_member_scope_by_kind(owner)
                && let Some(member) =
                    self.scopes[member_scope.0 as usize].value(&name.to_utf8_lossy())
            {
                return Some(member);
            }
            current = self.class_base_symbols.get(&owner).copied();
        }
        None
    }

    /// Typing-phase counterpart: records rows when the base is typed as an
    /// applied class instance, an interface, or a `this` type, covering
    /// `instance.prop` accesses whose base carries no direct symbol. Nodes the
    /// resolve phase already recorded are skipped. Assignment targets
    /// (`this.x = v`) share this path with `optional` clear.
    fn record_member_reference_rows(
        &mut self,
        object: &'src Expr,
        property: &'src MemberProperty,
        optional: bool,
        object_type: TypeId,
        path_range: TextRange,
        expression_id: NodeId,
    ) {
        if optional || self.member_reference_recorded.contains(&expression_id) {
            return;
        }
        let owner = match self.resolved_expression_reference(object) {
            Some(symbol)
                if matches!(
                    self.symbols[symbol.get() as usize].kind,
                    SymbolKind::Class | SymbolKind::Interface
                ) =>
            {
                Some(symbol)
            }
            _ => match self.types.get(object_type) {
                Type::AppliedClass { symbol, .. } => Some(*symbol),
                Type::Named(symbol)
                    if self.symbols[symbol.get() as usize].kind == SymbolKind::Interface =>
                {
                    Some(*symbol)
                }
                Type::This { owner, .. } => Some(*owner),
                _ => None,
            },
        };
        let Some(owner) = owner else {
            return;
        };
        self.record_symbol_member_reference_rows(owner, property, path_range);
        self.member_reference_recorded.insert(expression_id);
    }

    fn container_member_scope_by_kind(&self, owner: SymbolId) -> Option<ScopeId> {
        match self.symbols[owner.get() as usize].kind {
            SymbolKind::Class => self.class_member_scopes.get(&owner).copied(),
            SymbolKind::Interface => self.interface_member_scopes.get(&owner).copied(),
            _ => None,
        }
    }
    fn compute_type_of_expr(&mut self, expression: &'src Expr, scope: ScopeId) -> TypeId {
        match expression.data() {
            Expression::Identifier(identifier) => {
                let Some(&symbol) = self.references.get(&identifier.id()) else {
                    return self.types.any();
                };
                let declared = match self.symbols[symbol.get() as usize].kind {
                    SymbolKind::Class => self
                        .class_constructor_types
                        .get(&symbol)
                        .copied()
                        .unwrap_or(self.symbol_types[symbol.get() as usize]),
                    _ => self.symbol_types[symbol.get() as usize],
                };
                self.narrowed_type(symbol, declared)
            }
            Expression::Literal(literal) => self.type_of_literal(literal),
            Expression::Unary(unary) => {
                let operand = self.type_of_expr(&unary.argument, scope);
                match unary.operator {
                    UnaryOperator::Not | UnaryOperator::Delete => self.types.boolean(),
                    UnaryOperator::Typeof => self.types.string(),
                    UnaryOperator::Void => self.types.undefined_type(),
                    UnaryOperator::Plus | UnaryOperator::Minus | UnaryOperator::BitNot => {
                        if self.is_bigint_like(operand) {
                            self.types.bigint()
                        } else {
                            self.types.number()
                        }
                    }
                }
            }
            Expression::Update(update) => {
                let target = self.type_of_assignment_target(&update.argument, scope);
                self.types.widen(target, false)
            }
            Expression::Binary(binary) => {
                let left = self.type_of_expr(&binary.left, scope);
                let right = self.type_of_expr(&binary.right, scope);
                match binary.operator {
                    BinaryOperator::LessThan
                    | BinaryOperator::LessThanOrEqual
                    | BinaryOperator::GreaterThan
                    | BinaryOperator::GreaterThanOrEqual
                    | BinaryOperator::In
                    | BinaryOperator::Instanceof
                    | BinaryOperator::Equal
                    | BinaryOperator::NotEqual
                    | BinaryOperator::StrictEqual
                    | BinaryOperator::StrictNotEqual => self.types.boolean(),
                    BinaryOperator::Add
                        if matches!(self.types.get(left), Type::Any)
                            || matches!(self.types.get(right), Type::Any) =>
                    {
                        self.types.any()
                    }
                    BinaryOperator::Add
                        if self.is_string_like(left) || self.is_string_like(right) =>
                    {
                        self.types.string()
                    }
                    BinaryOperator::Add
                    | BinaryOperator::Subtract
                    | BinaryOperator::Multiply
                    | BinaryOperator::Divide
                    | BinaryOperator::Remainder
                    | BinaryOperator::Exponentiate
                    | BinaryOperator::LeftShift
                    | BinaryOperator::SignedRightShift
                    | BinaryOperator::UnsignedRightShift
                    | BinaryOperator::BitAnd
                    | BinaryOperator::BitXor
                    | BinaryOperator::BitOr => {
                        if self.is_bigint_like(left) && self.is_bigint_like(right) {
                            self.types.bigint()
                        } else {
                            self.types.number()
                        }
                    }
                }
            }
            Expression::Logical(logical) => {
                let left = self.type_of_expr(&logical.left, scope);
                let right = if logical.operator == LogicalOperator::Nullish {
                    self.type_of_expr(&logical.right, scope)
                } else {
                    let parent = self.flow;
                    let guards =
                        self.guards_for(&logical.left, logical.operator == LogicalOperator::Or);
                    let mut right = self.types.any();
                    self.in_branch(parent, &guards, |binder| {
                        right = binder.type_of_expr(&logical.right, scope);
                    });
                    right
                };
                let left = match logical.operator {
                    LogicalOperator::Nullish => self.types.non_nullable(left),
                    LogicalOperator::Or => self.types.truthy_type(left),
                    LogicalOperator::And => left,
                };
                if logical.operator != LogicalOperator::And && self.types.assignable(right, left) {
                    left
                } else {
                    self.types.union(&[left, right])
                }
            }
            Expression::Sequence(sequence) => sequence
                .expressions
                .last()
                .map(|last| self.type_of_expr(last, scope))
                .unwrap_or_else(|| self.types.undefined_type()),
            Expression::Parenthesized(inner) => self.type_of_expr(inner, scope),
            Expression::NonNull(non_null) => {
                let operand = self.type_of_expr(&non_null.expression, scope);
                self.types.non_nullable(operand)
            }
            Expression::Assignment(assignment)
                if assignment.operator == AssignmentOperator::Assign =>
            {
                self.type_of_expr(&assignment.right, scope)
            }
            Expression::Assignment(assignment)
                if assignment.operator == AssignmentOperator::NullishAssign =>
            {
                let target = self.type_of_assignment_target(&assignment.left, scope);
                let target = self.types.non_nullable(target);
                let source = self.type_of_expr(&assignment.right, scope);
                self.types.union(&[target, source])
            }
            Expression::Assignment(assignment) => {
                let target = self.type_of_assignment_target(&assignment.left, scope);
                self.types.widen(target, false)
            }
            Expression::As(cast) => match &cast.type_node {
                Some(type_node) => self.resolve_type(type_node, scope),
                None => self.type_of_expr(&cast.expression, scope),
            },
            Expression::Satisfies(satisfies) => self.type_of_expr(&satisfies.expression, scope),
            Expression::TypeAssertion(assertion) => self.resolve_type(&assertion.type_node, scope),
            Expression::Array(array) => {
                let mut element_types = Vec::new();
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(inner) => {
                            element_types.push(self.type_of_expr(inner, scope));
                        }
                        ArrayElement::Spread(spread) => {
                            let spread_type = self.type_of_expr(&spread.argument, scope);
                            let element = self
                                .array_element_type(spread_type)
                                .unwrap_or_else(|| self.types.any());
                            element_types.push(element);
                        }
                        ArrayElement::Elision | ArrayElement::Missing(_) => {}
                    }
                }
                let element = if element_types.is_empty() {
                    self.types.never()
                } else {
                    self.types.union(&element_types)
                };
                self.types.array(element)
            }
            Expression::Object(object) => {
                self.type_of_object_literal(object, expression.id(), None, scope)
            }
            Expression::JsxElement(_)
            | Expression::JsxSelfClosingElement(_)
            | Expression::JsxFragment(_) => self
                .jsx_element_types
                .get(&expression.id())
                .copied()
                .unwrap_or_else(|| self.types.any()),
            Expression::Conditional(conditional) => {
                self.type_of_conditional_expr(conditional, None, scope)
            }
            Expression::Function(function) => self.type_of_function_like(&function.function, scope),
            Expression::Class(class) => self.resolve_class_expression(&class.class, scope),
            Expression::Arrow(arrow) => self.type_of_arrow(arrow, scope),
            Expression::Member(member) => {
                let object_type = self.type_of_expr(&member.object, scope);
                let type_id = self.type_of_member(
                    &member.object,
                    &member.property,
                    member.optional,
                    true,
                    scope,
                );
                self.record_member_reference_rows(
                    &member.object,
                    &member.property,
                    member.optional,
                    object_type,
                    expression.range(),
                    expression.id(),
                );
                type_id
            }

            Expression::New(new) => {
                let callee_type = self.type_of_expr(&new.callee, scope);
                self.new_return_type(new, callee_type, scope)
                    .unwrap_or_else(|| self.types.any())
            }
            Expression::This => self
                .this_context
                .last()
                .copied()
                .unwrap_or_else(|| self.types.any()),
            Expression::Call(call) => {
                let callee_type = self.type_of_expr(&call.callee, scope);
                self.call_return_type(call, callee_type, scope)
                    .unwrap_or_else(|| self.types.any())
            }
            Expression::Await(await_expression) => {
                let operand = self.type_of_expr(&await_expression.argument, scope);
                self.awaited_type(operand)
            }
            Expression::TaggedTemplate(tagged) => {
                let callee_type = self.type_of_expr(&tagged.tag, scope);
                self.evaluate_tagged_template(tagged, scope, callee_type, expression.range())
                    .return_type
                    .unwrap_or_else(|| self.types.any())
            }
            Expression::Template(_) => self.types.string(),
            _ => self.types.any(),
        }
    }

    fn is_string_like(&self, type_id: TypeId) -> bool {
        match self.types.get(type_id) {
            Type::String | Type::StringLiteral(_) => true,
            Type::EnumMember {
                string_value: Some(_),
                ..
            } => true,
            Type::Union(members) => members.iter().any(|member| self.is_string_like(*member)),
            _ => false,
        }
    }

    /// Reports the `null` literal and the `undefined` identifier in an operand
    /// position that rejects a nullable value.
    ///
    /// Grounded on the TypeScript 7.0.2 authority baselines. The arithmetic,
    /// bitwise, relational, and `in` operators check both operands
    /// unconditionally. `+` checks only when neither operand is assignable to
    /// a string-like type, one condition covering three observed behaviors:
    /// `"test" + null` stays clean, `null + anyValue` stays clean, and with
    /// `strictNullChecks` off nothing reports because `null` is then itself
    /// string-assignable (`plusOperatorWithAnyOtherType` gets TS2365 for the
    /// operator instead, with its operand types still printed unnarrowed).
    /// Equality and `instanceof` accept a nullable operand.
    fn check_nullable_operands(&mut self, binary: &'src BinaryExpression, scope: ScopeId) {
        let checks_operands = match binary.operator {
            BinaryOperator::Subtract
            | BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Remainder
            | BinaryOperator::Exponentiate
            | BinaryOperator::LeftShift
            | BinaryOperator::SignedRightShift
            | BinaryOperator::UnsignedRightShift
            | BinaryOperator::BitAnd
            | BinaryOperator::BitXor
            | BinaryOperator::BitOr
            | BinaryOperator::LessThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThan
            | BinaryOperator::GreaterThanOrEqual
            | BinaryOperator::In => true,
            BinaryOperator::Add => {
                let left = self.type_of_expr(&binary.left, scope);
                let right = self.type_of_expr(&binary.right, scope);
                !self.is_assignable_to_string_like(left)
                    && !self.is_assignable_to_string_like(right)
            }
            BinaryOperator::Instanceof
            | BinaryOperator::Equal
            | BinaryOperator::NotEqual
            | BinaryOperator::StrictEqual
            | BinaryOperator::StrictNotEqual => false,
        };
        if !checks_operands {
            return;
        }
        self.check_non_null_operand(&binary.left, scope);
        self.check_non_null_operand(&binary.right, scope);
    }

    /// Reports one operand of an operator that rejects a nullable value.
    fn check_non_null_operand(&mut self, operand: &'src Expr, scope: ScopeId) {
        if !self.is_nullable_value_word(operand) {
            return;
        }
        let operand_type = self.type_of_expr(operand, scope);
        if !self.types.is_exactly_nullish(operand_type) {
            return;
        }
        self.emit(
            VALUE_CANNOT_BE_USED_HERE,
            operand.range(),
            VALUE_CANNOT_BE_USED_HERE_MESSAGE,
        );
    }

    /// Reports a nullable right operand of a compound assignment.
    ///
    /// A compound assignment applies its underlying operator, so it inherits
    /// that operator's operand rule: `+=` skips the check when either side is
    /// string-assignable, the arithmetic and bitwise forms always check, and
    /// the logical forms (`&&=`, `||=`, `??=`) accept a nullable value.
    fn check_nullable_compound_operand(
        &mut self,
        assignment: &'src AssignmentExpression,
        scope: ScopeId,
    ) {
        let checks_operand = match assignment.operator {
            AssignmentOperator::SubtractAssign
            | AssignmentOperator::MultiplyAssign
            | AssignmentOperator::DivideAssign
            | AssignmentOperator::RemainderAssign
            | AssignmentOperator::ExponentiateAssign
            | AssignmentOperator::LeftShiftAssign
            | AssignmentOperator::SignedRightShiftAssign
            | AssignmentOperator::UnsignedRightShiftAssign
            | AssignmentOperator::BitAndAssign
            | AssignmentOperator::BitXorAssign
            | AssignmentOperator::BitOrAssign => true,
            AssignmentOperator::AddAssign => {
                let left = self.type_of_assignment_target(&assignment.left, scope);
                let right = self.type_of_expr(&assignment.right, scope);
                !self.is_assignable_to_string_like(left)
                    && !self.is_assignable_to_string_like(right)
            }
            AssignmentOperator::Assign
            | AssignmentOperator::LogicalAndAssign
            | AssignmentOperator::LogicalOrAssign
            | AssignmentOperator::NullishAssign => false,
        };
        if checks_operand {
            self.check_non_null_operand(&assignment.right, scope);
        }
    }

    /// Whether a value of this type can be assigned to a string, which is what
    /// makes `+` concatenate rather than coerce.
    ///
    /// A union qualifies only when every member does, matching the relations
    /// engine's own rule for a union source: `"a" | 1` and `string | number`
    /// both coerce, so `null + u` reports for them. An any-member test would
    /// wrongly suppress both.
    ///
    /// Deliberately not `types_assignable(type_id, string)`. The engine accepts
    /// the boxed `Number` interface as assignable to `string`, which would
    /// suppress `null + d` where `d: Number` and the authority reports it
    /// (`additionOperatorWithNullValueAndInvalidOperator`). That is a defect in
    /// assignability, not in this rule, and it is not this rule's to inherit.
    fn is_assignable_to_string_like(&self, type_id: TypeId) -> bool {
        match self.types.get(type_id) {
            Type::Any | Type::String | Type::StringLiteral(_) => true,
            Type::EnumMember {
                string_value: Some(_),
                ..
            } => true,
            // Without `strictNullChecks` a nullable value is string-assignable,
            // so `+` concatenates and no operand is rejected.
            Type::Null | Type::Undefined => !self.strict_null_checks,
            Type::Union(members) => members
                .iter()
                .all(|member| self.is_assignable_to_string_like(*member)),
            _ => false,
        }
    }

    /// Whether the expression spells a nullable value directly: the `null`
    /// literal or an identifier reading `undefined`. Upstream reports these two
    /// through TS18050 and every other nullable operand through a different
    /// code, so the spelling decides the diagnostic identity.
    fn is_nullable_value_word(&self, operand: &'src Expr) -> bool {
        match operand.data() {
            Expression::Literal(Literal::Null(_)) => true,
            Expression::Identifier(identifier) => self.identifier_text(identifier) == "undefined",
            _ => false,
        }
    }

    fn is_bigint_like(&self, type_id: TypeId) -> bool {
        match self.types.get(type_id) {
            Type::BigInt | Type::BigIntLiteral(_) => true,
            Type::Union(members) => {
                !members.is_empty() && members.iter().all(|member| self.is_bigint_like(*member))
            }
            _ => false,
        }
    }
    fn class_method_signature_scope(
        &mut self,
        member: NodeId,
        function: &'src FunctionLike,
        parent: ScopeId,
    ) -> ScopeId {
        if let Some(scope) = self.class_method_signature_scopes.get(&member).copied() {
            return scope;
        }
        let scope = self.new_scope(ScopeKind::Function, Some(parent));
        self.bind_type_parameters(function.type_parameters.as_ref(), scope);
        self.class_method_signature_scopes.insert(member, scope);
        scope
    }

    fn type_of_function_like(&mut self, function: &'src FunctionLike, parent: ScopeId) -> TypeId {
        let scope = self.new_scope(ScopeKind::Function, Some(parent));
        self.bind_type_parameters(function.type_parameters.as_ref(), scope);
        self.type_of_function_like_in_scope(function, scope)
    }

    fn type_of_function_like_in_scope(
        &mut self,
        function: &'src FunctionLike,
        scope: ScopeId,
    ) -> TypeId {
        let return_type = match &function.return_type {
            Some(annotation) => self.resolve_type(&annotation.data().type_node, scope),
            None => self.inferred_function_return_type(function, scope),
        };
        self.signature_type_with_return(
            function.type_parameters.as_ref(),
            &function.parameters,
            return_type,
            scope,
        )
    }

    fn type_of_arrow(&mut self, arrow: &'src ArrowFunction, parent: ScopeId) -> TypeId {
        let scope = self.new_scope(ScopeKind::Function, Some(parent));
        self.bind_type_parameters(arrow.type_parameters.as_ref(), scope);
        let return_type = match &arrow.return_type {
            Some(annotation) => self.resolve_type(&annotation.data().type_node, scope),
            None => {
                let inferred = self.inferred_arrow_return_type(arrow, scope);
                if arrow.is_async {
                    self.promise_type(inferred)
                } else {
                    inferred
                }
            }
        };
        self.signature_type_with_return(
            arrow.type_parameters.as_ref(),
            &arrow.parameters,
            return_type,
            scope,
        )
    }

    fn signature_type_with_return(
        &mut self,
        type_parameters: Option<&'src crate::syntax::TypeParameterList>,
        parameters: &'src [ParameterNode],
        return_type: TypeId,
        scope: ScopeId,
    ) -> TypeId {
        let mut function_parameters: Vec<FunctionParameter> = Vec::with_capacity(parameters.len());
        for (idx, parameter) in parameters.iter().enumerate() {
            if let Some(lowered) = self.lower_parameter(idx, parameter, scope) {
                function_parameters.push(lowered);
            }
        }
        let (type_parameters, type_parameter_bounds) =
            self.signature_type_parameters(type_parameters, scope);
        self.types.function_with_parameter_bounds(
            type_parameters,
            type_parameter_bounds,
            function_parameters,
            return_type,
            !self.is_typescript(),
        )
    }

    fn statements_break_to_label(&self, statements: &'src [Stmt], label: &str) -> bool {
        for statement in statements {
            if self.statement_breaks_to_label(statement.data(), label) {
                return true;
            }
            if self.statement_prevents_function_completion(statement.data()) {
                return false;
            }
        }
        false
    }

    fn statement_breaks_to_label(&self, statement: &'src Statement, label: &str) -> bool {
        match statement {
            Statement::Break(jump) => jump
                .label
                .as_ref()
                .is_some_and(|candidate| self.identifier_text(candidate) == label),
            Statement::Block(block) => {
                self.statements_break_to_label(&block.data().statements, label)
            }
            Statement::If(if_stmt) => {
                self.statement_breaks_to_label(if_stmt.consequent.data(), label)
                    || if_stmt.alternate.as_ref().is_some_and(|alternate| {
                        self.statement_breaks_to_label(alternate.data(), label)
                    })
            }
            Statement::Switch(switch_stmt) => switch_stmt
                .cases
                .iter()
                .any(|case| self.statements_break_to_label(&case.data().consequent, label)),
            Statement::For(for_stmt) => self.statement_breaks_to_label(for_stmt.body.data(), label),
            Statement::ForIn(for_stmt) => {
                self.statement_breaks_to_label(for_stmt.body.data(), label)
            }
            Statement::ForOf(for_stmt) => {
                self.statement_breaks_to_label(for_stmt.body.data(), label)
            }
            Statement::While(while_stmt) => {
                self.statement_breaks_to_label(while_stmt.body.data(), label)
            }
            Statement::DoWhile(do_while) => {
                self.statement_breaks_to_label(do_while.body.data(), label)
            }
            Statement::Try(try_stmt) => {
                let finalizer_breaks = try_stmt.finalizer.as_ref().is_some_and(|finalizer| {
                    self.statements_break_to_label(&finalizer.data().statements, label)
                });
                let finalizer_completes = try_stmt
                    .finalizer
                    .as_ref()
                    .is_none_or(|finalizer| self.block_can_complete_normally(finalizer.data()));
                finalizer_breaks
                    || (finalizer_completes
                        && (self
                            .statements_break_to_label(&try_stmt.block.data().statements, label)
                            || try_stmt.handler.as_ref().is_some_and(|handler| {
                                self.statements_break_to_label(
                                    &handler.data().body.data().statements,
                                    label,
                                )
                            })))
            }
            Statement::With(with_stmt) => {
                self.statement_breaks_to_label(with_stmt.body.data(), label)
            }
            Statement::Labeled(labeled) => {
                self.statement_breaks_to_label(labeled.body.data(), label)
            }
            _ => false,
        }
    }

    fn statements_have_reachable_unlabeled_break(&self, statements: &'src [Stmt]) -> bool {
        for statement in statements {
            if Self::loop_body_has_unlabeled_break(statement.data(), 0) {
                return true;
            }
            if self.statement_prevents_function_completion(statement.data()) {
                return false;
            }
        }
        false
    }

    fn statement_prevents_function_completion(&self, statement: &'src Statement) -> bool {
        match statement {
            Statement::Return(_) | Statement::Throw(_) => true,
            Statement::Break(_) | Statement::Continue(_) => false,
            Statement::Block(block) => !self.block_can_complete_normally(block.data()),
            Statement::Labeled(labeled) => {
                let label = self.identifier_text(&labeled.label);
                !self.statement_breaks_to_label(labeled.body.data(), &label)
                    && self.statement_prevents_function_completion(labeled.body.data())
            }
            Statement::If(if_stmt) => {
                self.statement_prevents_function_completion(if_stmt.consequent.data())
                    && if_stmt.alternate.as_ref().is_some_and(|alternate| {
                        self.statement_prevents_function_completion(alternate.data())
                    })
            }
            Statement::For(for_stmt) => {
                for_stmt
                    .test
                    .as_ref()
                    .is_none_or(|test| Self::is_true_literal(test.data()))
                    && !Self::loop_body_has_unlabeled_break(for_stmt.body.data(), 0)
            }
            Statement::While(while_stmt) => {
                Self::is_true_literal(while_stmt.test.data())
                    && !Self::loop_body_has_unlabeled_break(while_stmt.body.data(), 0)
            }
            Statement::Switch(switch_stmt) => {
                let has_default = switch_stmt
                    .cases
                    .iter()
                    .any(|case| case.data().test.is_none());
                let has_break = switch_stmt.cases.iter().any(|case| {
                    self.statements_have_reachable_unlabeled_break(&case.data().consequent)
                });
                has_default
                    && !has_break
                    && switch_stmt.cases.last().is_some_and(|case| {
                        case.data().consequent.iter().any(|statement| {
                            self.statement_prevents_function_completion(statement.data())
                        })
                    })
            }
            Statement::DoWhile(do_while) => {
                Self::is_true_literal(do_while.test.data())
                    && !Self::loop_body_has_unlabeled_break(do_while.body.data(), 0)
            }
            Statement::Try(try_stmt) => {
                let finalizer_prevents = try_stmt
                    .finalizer
                    .as_ref()
                    .is_some_and(|finalizer| !self.block_can_complete_normally(finalizer.data()));
                finalizer_prevents
                    || (!self.block_can_complete_normally(try_stmt.block.data())
                        && try_stmt.handler.as_ref().is_none_or(|handler| {
                            !self.block_can_complete_normally(handler.data().body.data())
                        }))
            }
            Statement::With(with_stmt) => {
                self.statement_prevents_function_completion(with_stmt.body.data())
            }
            _ => false,
        }
    }

    fn block_can_complete_normally(&self, block: &'src crate::syntax::Block) -> bool {
        !block
            .statements
            .iter()
            .any(|statement| self.statement_prevents_function_completion(statement.data()))
    }
    fn check_annotated_return_fallthrough(
        &mut self,
        body: &'src FunctionBody,
        expected: Option<TypeId>,
        annotation: Option<TextRange>,
    ) {
        let (FunctionBody::Block(block), Some(expected)) = (body, expected) else {
            return;
        };
        if !(self.block_can_complete_normally(block.data())
            && !self
                .types
                .assignable_with_strict_null(self.types.undefined_type(), expected))
        {
            return;
        }
        if self.block_contains_return_statement(block.data()) {
            // At least one return exists; a normal completion therefore falls
            // off the end with `undefined` against a value type.
            self.emit(TYPE_NOT_ASSIGNABLE, block.range(), NOT_ASSIGNABLE_MESSAGE);
        } else {
            // No return statement at all: the function never returns a value,
            // which upstream reports as its own diagnostic at the annotation.
            self.emit(
                NON_VOID_FUNCTION_MUST_RETURN,
                annotation.unwrap_or_else(|| block.range()),
                NON_VOID_FUNCTION_MUST_RETURN_MESSAGE,
            );
        }
    }

    /// Whether any return statement is lexically present in the block,
    /// including inside nested blocks, loops, `try`, and `switch`, but never
    /// descending into nested function or arrow bodies (their returns belong
    /// to the nested callable).
    fn block_contains_return_statement(&self, block: &crate::syntax::Block) -> bool {
        self.statements_contain_return(&block.statements)
    }

    fn statements_contain_return(&self, statements: &'src [crate::syntax::Stmt]) -> bool {
        for statement in statements {
            if self.statement_contains_return(statement.data()) {
                return true;
            }
        }
        false
    }

    fn statement_contains_return(&self, statement: &crate::syntax::Statement) -> bool {
        match statement {
            crate::syntax::Statement::Return(_) => true,
            crate::syntax::Statement::Block(block) => {
                self.statements_contain_return(&block.data().statements)
            }
            crate::syntax::Statement::If(statement) => {
                self.statement_contains_return(statement.consequent.data())
                    || statement
                        .alternate
                        .as_ref()
                        .is_some_and(|alternate| self.statement_contains_return(alternate.data()))
            }
            crate::syntax::Statement::While(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::DoWhile(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::For(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::ForIn(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::ForOf(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::Labeled(statement) => {
                self.statement_contains_return(statement.body.data())
            }
            crate::syntax::Statement::Switch(statement) => statement
                .cases
                .iter()
                .any(|case| self.statements_contain_return(&case.data().consequent)),
            crate::syntax::Statement::Try(statement) => {
                self.statements_contain_return(&statement.block.data().statements)
                    || statement.handler.as_ref().is_some_and(|handler| {
                        self.statements_contain_return(&handler.data().body.data().statements)
                    })
                    || statement.finalizer.as_ref().is_some_and(|finalizer| {
                        self.statements_contain_return(&finalizer.data().statements)
                    })
            }
            _ => false,
        }
    }

    fn inferred_block_return_type(
        &mut self,
        block: &'src crate::syntax::Block,
        returns: &[TypeId],
        noncompleting_is_never: bool,
    ) -> TypeId {
        let can_complete_normally = self.block_can_complete_normally(block);
        if returns.is_empty() {
            return if can_complete_normally || !noncompleting_is_never {
                self.types.void()
            } else {
                self.types.never()
            };
        }
        let mut members: Vec<TypeId> = returns.to_vec();
        let has_value = members.iter().any(|&t| t != self.types.undefined_type());
        if can_complete_normally && has_value {
            members.push(self.types.undefined_type());
        }
        let return_type = self.types.union(&members);
        self.types.widen_fresh_literal(return_type)
    }

    fn inferred_function_return_type(
        &mut self,
        function: &'src FunctionLike,
        parent: ScopeId,
    ) -> TypeId {
        let completion = self.inferred_return_type(function, parent);
        if function.is_generator {
            let yields = function
                .body
                .as_ref()
                .and_then(FunctionBody::id)
                .and_then(|body| self.yield_types.get(&body))
                .cloned()
                .unwrap_or_default();
            let yield_type = if yields.is_empty() {
                self.types.never()
            } else {
                let union = self.types.union(&yields);
                self.types.widen_fresh_literal(union)
            };
            let next_type = self.types.unknown();
            let protocol = if function.is_async {
                ForOfMode::Async
            } else {
                ForOfMode::Sync
            };
            self.intrinsic_generator_type(yield_type, completion, next_type, protocol)
        } else if function.is_async {
            self.promise_type(completion)
        } else {
            completion
        }
    }

    fn inferred_return_type(&mut self, function: &'src FunctionLike, parent: ScopeId) -> TypeId {
        if let Some(annotation) = &function.return_type {
            return self.resolve_type(&annotation.data().type_node, parent);
        }
        match &function.body {
            Some(FunctionBody::Expression(expression)) => {
                let return_type = self.type_of_expr(expression, parent);
                if function.is_async {
                    self.awaited_type(return_type)
                } else {
                    return_type
                }
            }
            Some(FunctionBody::Block(block)) => {
                let Some(returns) = self.return_types.get(&block.id()).cloned() else {
                    return self.types.any();
                };
                let noncompleting_is_never =
                    !self.declaration_function_bodies.contains(&block.id());
                self.inferred_block_return_type(block.data(), &returns, noncompleting_is_never)
            }
            Some(FunctionBody::Missing(_)) => self.types.any(),
            None => self.types.void(),
        }
    }

    fn inferred_arrow_return_type(
        &mut self,
        arrow: &'src ArrowFunction,
        parent: ScopeId,
    ) -> TypeId {
        match &arrow.body {
            FunctionBody::Expression(expression) => {
                let return_type = self.type_of_expr(expression, parent);
                if arrow.is_async {
                    self.awaited_type(return_type)
                } else {
                    return_type
                }
            }
            FunctionBody::Block(block) => {
                let Some(returns) = self.return_types.get(&block.id()).cloned() else {
                    return self.types.any();
                };
                self.inferred_block_return_type(block.data(), &returns, true)
            }
            FunctionBody::Missing(_) => self.types.void(),
        }
    }

    fn call_return_type(
        &mut self,
        call: &'src CallExpression,
        callee_type: TypeId,
        scope: ScopeId,
    ) -> Option<TypeId> {
        self.evaluate_call(call, scope, callee_type).return_type
    }

    fn new_return_type(
        &mut self,
        new: &'src NewExpression,
        callee_type: TypeId,
        scope: ScopeId,
    ) -> Option<TypeId> {
        self.evaluate_new(new, scope, callee_type).return_type
    }

    fn explicit_function_signature(
        &mut self,
        signature: &FunctionSignature,
        explicit: &[TypeId],
        diagnostic_range: TextRange,
    ) -> Result<FunctionSignature, CallMismatch> {
        let type_parameters = signature.type_parameters();
        if type_parameters.is_empty() {
            return if explicit.is_empty() || signature.javascript() {
                Ok(signature.clone())
            } else {
                Err(CallMismatch::ArgumentCount)
            };
        }
        let bounds = signature.type_parameter_bounds();
        let required = bounds
            .iter()
            .rposition(|bound| bound.default().is_none())
            .map_or(0, |index| index + 1);
        if explicit.len() < required || explicit.len() > type_parameters.len() {
            return Err(CallMismatch::ArgumentCount);
        }

        let mut arguments = Vec::with_capacity(type_parameters.len());
        for (index, symbol) in type_parameters.iter().copied().enumerate() {
            let prior = InferredTypeArguments::new(arguments.clone());
            let bound = bounds[index];
            let type_id = if let Some(explicit) = explicit.get(index).copied() {
                explicit
            } else {
                let Some(default) = bound.default() else {
                    return Err(CallMismatch::ArgumentCount);
                };
                prior.instantiate(&mut self.types, default)
            };
            if let Some(constraint) = bound.constraint() {
                let constraint = prior.instantiate(&mut self.types, constraint);
                if !self.types_assignable(type_id, constraint) {
                    return Err(CallMismatch::ArgumentType(diagnostic_range));
                }
            }
            arguments.push(InferredTypeArgument::new(
                symbol,
                type_id,
                if index < explicit.len() {
                    InferenceProvenance::Explicit
                } else {
                    InferenceProvenance::Default
                },
            ));
        }
        let inferred = InferredTypeArguments::new(arguments);
        let mut instantiated_parameters = Vec::with_capacity(signature.parameters().len());
        for parameter in signature.parameters() {
            let type_id = inferred.instantiate(&mut self.types, parameter.type_id());
            instantiated_parameters.push(FunctionParameter::new(
                parameter.name().to_owned(),
                type_id,
                parameter.optional(),
                parameter.rest(),
            ));
        }
        let instantiated_return = inferred.instantiate(&mut self.types, signature.return_type());
        Ok(FunctionSignature {
            type_parameters: Vec::new(),
            type_parameter_bounds: Vec::new(),
            parameters: instantiated_parameters,
            return_type: instantiated_return,
            declaring_types: signature.declaring_types().to_vec(),
            javascript: signature.javascript(),
        })
    }

    fn inferred_function_signature(
        &mut self,
        signature: &FunctionSignature,
        argument_types: &[TypeId],
        fresh_literal_sources: &[u32],
    ) -> Option<FunctionSignature> {
        if signature.type_parameters().is_empty() {
            return Some(signature.clone());
        }
        let inference_parameters: Vec<_> = signature
            .type_parameters()
            .iter()
            .copied()
            .zip(signature.type_parameter_bounds().iter().copied())
            .map(|(symbol, bound)| {
                let mut parameter = InferenceParameter::new(symbol);
                if let Some(constraint) = bound.constraint() {
                    parameter = parameter.with_constraint(constraint);
                }
                if let Some(default) = bound.default() {
                    parameter = parameter.with_default(default);
                }
                parameter
            })
            .collect();
        let mut context = InferenceContext::new_with_cancel(
            &mut self.types,
            &inference_parameters,
            self.cancel.clone(),
        );
        for &source in fresh_literal_sources {
            context.mark_fresh_literal_source(source);
        }
        context.infer_from_arguments(signature, argument_types);
        let mut inferred = context.resolve();
        inferred.widen_unconstrained_literals(&mut self.types, &inference_parameters);
        let mut instantiated_parameters = Vec::with_capacity(signature.parameters().len());
        for parameter in signature.parameters() {
            let type_id = inferred.instantiate(&mut self.types, parameter.type_id());
            instantiated_parameters.push(FunctionParameter::new(
                parameter.name().to_owned(),
                type_id,
                parameter.optional(),
                parameter.rest(),
            ));
        }
        let instantiated_return = inferred.instantiate(&mut self.types, signature.return_type());
        Some(FunctionSignature {
            type_parameters: Vec::new(),
            type_parameter_bounds: Vec::new(),
            parameters: instantiated_parameters,
            return_type: instantiated_return,
            declaring_types: signature.declaring_types().to_vec(),
            javascript: signature.javascript(),
        })
    }

    fn type_of_literal(&mut self, literal: &Literal) -> TypeId {
        match literal {
            Literal::String(token) => {
                let text = self.text(token.data().token());
                self.types.string_literal_lexeme(text)
            }
            Literal::Number(token) => {
                let text = self.text(token.data().token());
                self.types.number_literal(text)
            }
            Literal::BigInt(token) => {
                let text = self.text(token.data().token());
                self.types.bigint_literal(text)
            }
            Literal::Boolean(token) => {
                let value = self.text(token.data().token()) == "true";
                self.types.boolean_literal(value)
            }
            Literal::Null(_) => self.types.null_type(),
            Literal::Regex(_) => self
                .reg_exp_instance_type
                .expect("RegExp intrinsic installed before expression resolution"),
        }
    }

    /// Extracts the cooked string value from a string-literal enum member
    /// initializer, returning `None` for numeric or computed initializers.
    fn enum_member_string_value(&self, expression: &Expr) -> Option<EcmaString> {
        match expression.data() {
            Expression::Literal(Literal::String(token)) => {
                let lexeme = self.text(token.data().token());
                crate::literal::string_value(lexeme)
            }
            _ => None,
        }
    }
}

/// A default zero range for synthesized diagnostics anchored on missing syntax.
trait DefaultRange {
    fn default_range() -> TextRange;
}

impl DefaultRange for NodeId {
    fn default_range() -> TextRange {
        use crate::source::Utf16Pos;
        TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("zero range is ordered")
    }
}

/// Binds one parsed source into its immutable semantic model using the
/// standard intrinsic environment.
#[cfg(test)]
pub(crate) fn bind_source(source: &SourceFile) -> (SemanticModel, Vec<Diagnostic>) {
    bind_source_with_cancel(source, bamts_cancel::CancellationToken::new())
        .expect("fresh token is never cancelled")
}

/// Binds one parsed source into its immutable semantic model using the
/// standard intrinsic environment. Fails early when `cancel` is triggered.
pub(crate) fn bind_source_with_cancel(
    source: &SourceFile,
    cancel: bamts_cancel::CancellationToken,
) -> Result<(SemanticModel, Vec<Diagnostic>), super::CheckCancelled> {
    let mut binder = Binder::with_environment_and_cancel(
        source,
        GlobalEnvironment::standard(crate::checker::intrinsic_environment::LibSet::ALL),
        source_is_module(source),
        ProgramCheckOptions::standard(),
        cancel,
    );
    binder.run_with_imported_types_and_cancel(&[])?;
    Ok(binder.finish())
}

/// Binds one parsed source into its immutable semantic model using an
/// explicit intrinsic environment and module/script classification.
#[cfg(test)]
pub(crate) fn bind_source_with_environment(
    source: &SourceFile,
    environment: GlobalEnvironment,
    is_module: bool,
    options: ProgramCheckOptions,
) -> (SemanticModel, Vec<Diagnostic>) {
    bind_source_with_environment_and_imports(source, environment, is_module, options, &[])
}

/// Cancellable variant of [`bind_source_with_environment`].
pub(crate) fn bind_source_with_environment_and_cancel(
    source: &SourceFile,
    environment: GlobalEnvironment,
    is_module: bool,
    options: ProgramCheckOptions,
    cancel: bamts_cancel::CancellationToken,
) -> Result<(SemanticModel, Vec<Diagnostic>), super::CheckCancelled> {
    bind_source_with_environment_and_imports_with_cancel(
        source,
        environment,
        is_module,
        options,
        &[],
        cancel,
    )
}

#[cfg(test)]
pub(crate) fn bind_source_with_environment_and_imports(
    source: &SourceFile,
    environment: GlobalEnvironment,
    is_module: bool,
    options: ProgramCheckOptions,
    imported_types: &[ImportedSymbolType<'_>],
) -> (SemanticModel, Vec<Diagnostic>) {
    bind_source_with_environment_and_imports_with_cancel(
        source,
        environment,
        is_module,
        options,
        imported_types,
        bamts_cancel::CancellationToken::new(),
    )
    .expect("fresh token is never cancelled")
}

pub(crate) fn bind_source_with_environment_and_imports_with_cancel(
    source: &SourceFile,
    environment: GlobalEnvironment,
    is_module: bool,
    options: ProgramCheckOptions,
    imported_types: &[ImportedSymbolType<'_>],
    cancel: bamts_cancel::CancellationToken,
) -> Result<(SemanticModel, Vec<Diagnostic>), super::CheckCancelled> {
    let mut binder =
        Binder::with_environment_and_cancel(source, environment, is_module, options, cancel);
    binder.run_with_imported_types_and_cancel(imported_types)?;
    Ok(binder.finish())
}

#[cfg(test)]
mod tests {
    use super::{
        ACCESSOR_THIS_PARAMETER, AMBIENT_IMPLEMENTATION, ARGUMENT_COUNT_MISMATCH,
        ARGUMENT_NOT_ASSIGNABLE, ASSIGNMENT_TO_READONLY, BARE_SUPER_EXPRESSION, CANNOT_FIND_NAME,
        CANNOT_FIND_TYPE, CONSTRUCTOR_TYPE_PARAMETERS, DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL,
        DUPLICATE_DECLARATION, EXPRESSION_NOT_CALLABLE, FUNCTION_IMPLEMENTATION_WRONG_NAME,
        FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, GET_ACCESSOR_NO_RETURN, GET_ACCESSOR_PARAMETERS,
        MISSING_METHOD_RETURN_TYPE, NAMESPACE_NO_EXPORTED_MEMBER, PROPERTY_NOT_INITIALIZED,
        PropertyType, SET_ACCESSOR_PARAMETER_INITIALIZER, STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT,
        SUPER_REFERENCE_NON_DERIVED, ScopeId, ScopeKind, SymbolId, SymbolKind, TYPE_NOT_ASSIGNABLE,
        TupleShape, Type, TypeParameterBounds, TypeTable, bind_source,
    };
    use crate::diagnostic::Diagnostic;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use crate::syntax::VariableKind;
    use std::sync::Arc;

    fn source(text: &str) -> Arc<SourceText> {
        Arc::new(SourceText::new(text).expect("test source fits the per-file budget"))
    }

    fn declaration_source(text: &str) -> Arc<SourceText> {
        Arc::new(
            SourceText::new(text)
                .expect("test source fits the per-file budget")
                .with_declaration_file(true),
        )
    }

    fn bound(text: &str) -> (super::SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        bind_source(parsed.product())
    }

    fn bound_declaration(text: &str) -> (super::SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            declaration_source(text),
        ));
        bind_source(parsed.product())
    }

    fn bound_js(text: &str) -> (super::SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::JavaScript,
            source(text),
        ));
        bind_source(parsed.product())
    }

    #[test]
    fn transforming_recursive_class_view_is_demand_bounded() {
        let mut table = TypeTable::new();
        let class = SymbolId::new(1);
        let parameter = SymbolId::new(2);
        table.declare_class(class, vec![parameter]);
        table.finish_class_bounds(class, vec![TypeParameterBounds::NONE]);

        let named_parameter = table.named(parameter);
        let nested_argument = table.array(named_parameter);
        let nested = table.intern(Type::AppliedClass {
            symbol: class,
            arguments: vec![nested_argument],
        });
        let raw = table.object_type(vec![PropertyType::new("next", false, nested)]);
        table.publish_final_class_template(class, raw);

        let number = table.number();
        let root = table.applied_class(class, vec![number]);
        let root_view = table
            .applied_class_view(root)
            .expect("root view is prepared");
        let type_count = table.types.len();
        for _ in 0..64 {
            assert_eq!(table.prepare_applied_class_view(root), Some(root_view));
        }
        assert_eq!(table.types.len(), type_count);

        let Type::ObjectType(root_object) = table.get(root_view) else {
            panic!("class view must be structural");
        };
        let next = root_object
            .properties
            .iter()
            .find(|property| property.name() == "next")
            .expect("next property")
            .type_id();
        let next_view = table
            .applied_class_view(next)
            .expect("first recursive layer is prepared");
        let Type::ObjectType(next_object) = table.get(next_view) else {
            panic!("nested class view must be structural");
        };
        let second = next_object
            .properties
            .iter()
            .find(|property| property.name() == "next")
            .expect("second next property")
            .type_id();
        assert!(table.applied_class_view(second).is_none());
        let second_view = table
            .prepare_applied_class_view(second)
            .expect("second recursive layer prepares on demand");
        let type_count = table.types.len();
        assert_eq!(table.prepare_applied_class_view(second), Some(second_view));
        assert_eq!(table.types.len(), type_count);
    }

    #[test]
    fn c052_statement_not_allowed_in_ambient_context() {
        let (_, diagnostics) = bound_declaration("try { } catch (e) { }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c052_declaration_allowed_in_ambient_context() {
        let (_, diagnostics) = bound_declaration("export interface Foo { x: number; }\n");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c052_statement_not_allowed_in_ambient_namespace() {
        let (_, diagnostics) = bound("declare namespace N { if (true) { } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c052_statement_not_allowed_in_ambient_module() {
        let (_, diagnostics) = bound("declare module \"M\" { if (true) { } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c052_statement_not_allowed_in_ambient_declaration_file_namespace() {
        let (_, diagnostics) = bound_declaration("namespace N { if (true) { } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c052_runtime_namespace_allows_statements() {
        let (_, diagnostics) = bound("namespace N { if (true) { } }\n");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_base_class_method() {
        let (_, diagnostics) = bound("class Base { m() { super.x; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_base_constructor() {
        let (_, diagnostics) = bound("class Base { constructor() { super.x; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_base_property_initializer() {
        let (_, diagnostics) = bound("class Base { p = super.x; }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_base_static_block() {
        let (_, diagnostics) = bound("class Base { static { super.x; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_through_arrow_in_base_method() {
        let (_, diagnostics) = bound("class Base { m() { const f = () => super.x; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_assignment_in_base_method() {
        let (_, diagnostics) = bound("class Base { m() { super.x = 1; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_derived_class_is_allowed() {
        let (_, diagnostics) =
            bound("class Base { x = 1; }\nclass Derived extends Base { m() { super.x; } }\n");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_object_method_is_allowed() {
        let (_, diagnostics) = bound("const o = { m() { super.x; } };\n");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c025_super_member_reference_in_nested_function_is_allowed() {
        let (_, diagnostics) = bound("class Base { m() { function f() { super.x; } } }\n");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == SUPER_REFERENCE_NON_DERIVED),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn c024_super_optional_chain_is_bare_super() {
        let (_, diagnostics) = bound("class Base { m() { super?.x; } }\n");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == BARE_SUPER_EXPRESSION),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn node_types_record_initializer_expression_types() {
        let (model, diagnostics) = bound("var a: number = 42;\nvar s: string = 'hi';\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let recorded: Vec<&Type> = model
            .typed_expressions()
            .iter()
            .map(|(_, type_id)| model.types().get(*type_id))
            .collect();
        assert!(
            recorded
                .iter()
                .any(|ty| matches!(ty, Type::NumberLiteral(text) if &**text == "42")),
            "number literal 42 recorded: {recorded:?}"
        );
        assert!(
            recorded
                .iter()
                .any(|ty| matches!(ty, Type::StringLiteral(text) if text.eq_ascii("hi"))),
            "string literal hi recorded: {recorded:?}"
        );
    }

    #[test]
    fn symbol_references_record_resolved_value_and_type_occurrences() {
        let (model, diagnostics) = bound("class C {}\nvar a: C;\nvar b = a;\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        // The value use of `a` and the type use of `C` are resolved references
        // with source ranges; the emitter places records against those ranges.
        let names: Vec<&str> = model
            .symbol_references()
            .iter()
            .map(|(_, symbol)| model.symbol(*symbol).name())
            .collect();
        assert!(
            names.contains(&"a"),
            "value reference `a` recorded: {names:?}"
        );
        assert!(
            names.contains(&"C"),
            "type reference `C` recorded: {names:?}"
        );
        // Every occurrence carries a non-empty range within the source.
        assert!(
            model
                .symbol_references()
                .iter()
                .all(|(range, _)| !range.is_empty()),
            "reference occurrences carry non-empty ranges"
        );
    }

    #[test]
    fn node_type_answers_by_node_id_for_recorded_expression() {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("var a: number = 42;\n"),
        ));
        let file = parsed.product();
        let (model, _diagnostics) = bind_source(file);
        let crate::syntax::Statement::Variable(variable) = file.statements()[0].data() else {
            panic!("first statement is a variable declaration");
        };
        let initializer = variable.declarations[0]
            .data()
            .initializer
            .as_ref()
            .expect("declarator has an initializer");
        let type_id = model
            .node_type(initializer.id())
            .expect("node_type records the initializer expression");
        assert!(
            matches!(model.types().get(type_id), Type::NumberLiteral(text) if &**text == "42"),
            "initializer types as the numeric literal 42"
        );
        // A node the walk never typed has no recorded type.
        assert_eq!(model.node_type(crate::syntax::NodeId::default()), None);
    }

    #[test]
    fn the_scope_tree_roots_a_module_scope_in_a_global_intrinsic_scope() {
        let (model, diagnostics) = bound("const x = 1;");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let global = &model.scopes()[0];
        let module = &model.scopes()[1];
        assert_eq!(global.kind(), ScopeKind::Global);
        assert_eq!(module.kind(), ScopeKind::Module);
        assert_eq!(module.parent(), Some(ScopeId(0)));
        assert_eq!(model.module_scope(), ScopeId(1));
        // Intrinsics bind in the global scope and resolve outward from the module.
        assert!(global.value("Object").is_some());
        assert!(model.lookup_value(model.module_scope(), "Object").is_some());
        // A top-level declaration binds in the module scope.
        let x = module.value("x").expect("x binds in the module scope");
        assert_eq!(
            model.symbol(x).kind,
            SymbolKind::Variable(VariableKind::Const)
        );
    }

    #[test]
    fn duplicate_block_scoped_declarations_are_diagnosed_once_in_their_scope() {
        let (model, diagnostics) = bound("let a = 1; let a = 2;");
        let codes: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code())
            .collect();
        assert_eq!(codes, [DUPLICATE_DECLARATION]);
        // The module scope keeps the first binding; the duplicate does not replace it.
        let a = model
            .scope(model.module_scope())
            .value("a")
            .expect("a binds in the module scope");
        assert_eq!(model.symbol(a).name, "a");
    }

    #[test]
    fn var_hoists_to_the_module_scope_but_let_stays_in_its_block() {
        let (model, diagnostics) = bound("{ var v = 1; let b = 2; }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let block = model
            .scopes()
            .iter()
            .position(|scope| scope.kind() == ScopeKind::Block && scope.value("b").is_some())
            .map(|index| ScopeId(index as u32))
            .expect("block containing b exists");
        let v = model
            .lookup_value(model.module_scope(), "v")
            .expect("var hoists to the module scope");
        assert_eq!(model.symbol(v).scope, model.module_scope());
        let b = model
            .scope(block)
            .value("b")
            .expect("let stays in its block scope");
        assert_eq!(model.symbol(b).scope, block);
        assert!(model.lookup_value(model.module_scope(), "b").is_none());
    }

    #[test]
    fn references_resolve_against_the_two_namespace_scope_tree() {
        let (model, diagnostics) = bound("{ let y = 2; y; }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(model.resolved_reference_count(), 1);
        let unresolved = bound("missing;");
        let codes: Vec<_> = unresolved
            .1
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect();
        assert_eq!(codes, [super::CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn class_members_are_not_visible_as_bare_names_in_static_methods() {
        let (_, diagnostics) = bound("class C { foo: string; static bar() { let k = foo; } }");
        let codes: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect();
        assert_eq!(codes, [super::CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn class_members_are_not_visible_as_bare_names_in_instance_methods() {
        let (_, diagnostics) = bound("class C { foo = 1; bar() { return foo; } }");
        let codes: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect();
        assert_eq!(codes, [super::CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn named_class_expression_name_stays_visible_in_its_body() {
        let (_, diagnostics) = bound("const X = class Inner { m() { return Inner; } };");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn this_member_access_still_resolves() {
        let (_, diagnostics) = bound("class C { foo = 1; bar() { return this.foo; } }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn the_type_table_interns_primitives_literals_and_sorted_object_members() {
        let mut table = TypeTable::new();
        assert_eq!(table.get(table.number()), &Type::Number);
        let one = table.number_literal("1");
        assert_eq!(table.number_literal("1"), one, "interning is stable");
        let object = table.object_type(vec![
            PropertyType::new("b", false, table.string()),
            PropertyType::new("a", true, table.number()),
        ]);
        let Type::ObjectType(object) = table.get(object) else {
            panic!("object_type interns an object type");
        };
        assert_eq!(object.properties[0].name.as_ref(), "a");
        assert_eq!(object.properties[1].name.as_ref(), "b");
        assert!(object.properties[0].optional);
    }

    fn value_symbol(model: &super::SemanticModel, name: &str) -> SymbolId {
        model
            .scopes()
            .iter()
            .find_map(|scope| scope.value(name))
            .unwrap_or_else(|| panic!("value `{name}` not bound"))
    }

    fn type_symbol(model: &super::SemanticModel, name: &str) -> SymbolId {
        model
            .scopes()
            .iter()
            .find_map(|scope| scope.type_binding(name))
            .unwrap_or_else(|| panic!("type `{name}` not bound"))
    }

    fn owning_scope(model: &super::SemanticModel, owner: SymbolId) -> Option<&super::Scope> {
        model
            .scopes()
            .iter()
            .find(|scope| scope.owner() == Some(owner))
    }

    #[test]
    fn enum_members_are_parented_to_the_enum_symbol() {
        let (model, diagnostics) = bound("enum E {\n    A,\n    B = A + 1,\n}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let enum_id = value_symbol(&model, "E");
        let member_scope = owning_scope(&model, enum_id).expect("enum member scope is owned");
        let a = member_scope.value("A").expect("member A bound");
        assert_eq!(model.symbol(a).parent(), Some(enum_id));
        assert_eq!(model.qualified_name(a), "E.A");
        // The enum itself renders bare.
        assert_eq!(model.symbol(enum_id).parent(), None);
        assert_eq!(model.qualified_name(enum_id), "E");
    }

    #[test]
    fn merged_enum_members_share_one_owner() {
        let (model, diagnostics) = bound("enum E {\n    A = 1,\n}\nenum E {\n    B = 2,\n}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let enum_id = value_symbol(&model, "E");
        let member_scope = owning_scope(&model, enum_id).expect("merged enum member scope owned");
        let a = member_scope.value("A").expect("member A bound");
        let b = member_scope.value("B").expect("member B bound");
        assert_eq!(model.symbol(a).parent(), Some(enum_id));
        assert_eq!(model.symbol(b).parent(), Some(enum_id));
        assert_eq!(model.qualified_name(a), "E.A");
        assert_eq!(model.qualified_name(b), "E.B");
    }

    #[test]
    fn namespace_exports_render_bare() {
        let (model, diagnostics) = bound("namespace N {\n    export var x = 1;\n}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let x = value_symbol(&model, "x");
        assert_eq!(model.symbol(x).parent(), None);
        assert_eq!(model.qualified_name(x), "x");
        // The scope holding the export has no owner.
        let export_scope = model
            .scopes()
            .iter()
            .find(|scope| scope.value("x").is_some())
            .expect("export scope exists");
        assert_eq!(export_scope.owner(), None);
    }

    #[test]
    fn nested_namespace_exports_render_bare() {
        let (model, diagnostics) =
            bound("namespace N {\n    export namespace M {\n        export var x = 1;\n    }\n}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let m = value_symbol(&model, "M");
        let x = value_symbol(&model, "x");
        assert_eq!(model.qualified_name(m), "M");
        assert_eq!(model.qualified_name(x), "x");
    }

    #[test]
    fn class_scope_is_owned_by_the_class_symbol() {
        let (model, diagnostics) = bound("class Ship {\n    isSunk: boolean;\n}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let ship = value_symbol(&model, "Ship");
        assert!(
            owning_scope(&model, ship).is_some(),
            "class scope owned by the class symbol"
        );
        assert_eq!(model.qualified_name(ship), "Ship");
    }

    #[test]
    fn named_class_expression_internal_name_renders_bare() {
        let (model, diagnostics) = bound("var x = class C {};\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let internal = value_symbol(&model, "C");
        assert_eq!(model.symbol(internal).parent(), None);
        assert_eq!(model.qualified_name(internal), "C");
        // The class scope is owned by the internal-name symbol.
        assert_eq!(
            owning_scope(&model, internal).map(|_| ()),
            Some(()),
            "class scope owned by internal name"
        );
    }

    #[test]
    fn class_type_parameters_render_bare() {
        let (model, diagnostics) = bound("class C<T> {}\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let class_id = value_symbol(&model, "C");
        let t = type_symbol(&model, "T");
        assert_eq!(model.symbol(t).parent(), None);
        assert_eq!(model.qualified_name(t), "T");
        assert!(
            owning_scope(&model, class_id).is_some(),
            "class scope still owned even with type params"
        );
    }

    #[test]
    fn interface_type_parameters_render_bare_and_members_qualified() {
        let (model, diagnostics) = bound("interface I<T> { item: T; }\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let interface_id = type_symbol(&model, "I");
        let t = type_symbol(&model, "T");
        assert_eq!(model.symbol(t).parent(), None);
        assert_eq!(model.qualified_name(t), "T");
        // The type-parameter scope itself has no owner; members bind into a
        // separate member scope owned by the interface (upstream `Symbol(I.item)`).
        let item = symbol_named(&model, "item");
        assert_eq!(model.symbol(item).parent(), Some(interface_id));
        assert_eq!(model.qualified_name(item), "I.item");
    }

    #[test]
    fn type_alias_type_parameters_render_bare() {
        let (model, diagnostics) = bound("type F<T> = T;\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let t = type_symbol(&model, "T");
        assert_eq!(model.symbol(t).parent(), None);
        assert_eq!(model.qualified_name(t), "T");
    }

    #[test]
    fn explicit_type_arguments_instantiate_interface_properties() {
        let (_, diagnostics) = bound(
            "interface I<T, U> { one: T; two?: U; }\n\
             var obj: I<number, string> = { one: 1 };\n",
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == TYPE_NOT_ASSIGNABLE),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn explicit_type_arguments_instantiate_type_alias() {
        let (_, diagnostics) = bound(
            "type F<T> = { x: T };\n\
             var obj: F<number> = { x: 1 };\n",
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == TYPE_NOT_ASSIGNABLE),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn call_argument_mismatch_and_type_errors_are_diagnosed() {
        let (_, diagnostics) = bound(
            "function foo(a: string) {}\n\
             foo(2);\n\
             foo('foo', 'bar');\n\
             foo();\n",
        );
        let relevant = diagnostics
            .iter()
            .filter(|diagnostic| {
                diagnostic.code() == ARGUMENT_NOT_ASSIGNABLE
                    || diagnostic.code() == ARGUMENT_COUNT_MISMATCH
            })
            .count();
        assert_eq!(relevant, 3, "{diagnostics:?}");
    }

    #[test]
    fn required_parameter_after_default_counts_toward_minimum_arity() {
        let (_, diagnostics) = bound(
            "function f(a=1, b:string) {}\n\
             f();\n\
             f(1);\n\
             f(1, 'x');\n",
        );
        let count = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code() == ARGUMENT_COUNT_MISMATCH)
            .count();
        assert_eq!(count, 2, "{diagnostics:?}");
    }

    fn bound_strict(text: &str) -> (super::SemanticModel, Vec<Diagnostic>) {
        bound_with_options(
            text,
            super::ProgramCheckOptions::standard()
                .with_strict_null_checks(true)
                .with_strict_property_initialization(true),
        )
    }

    fn bound_with_options(
        text: &str,
        options: super::ProgramCheckOptions,
    ) -> (super::SemanticModel, Vec<Diagnostic>) {
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        super::bind_source_with_environment(
            parsed.product(),
            super::super::intrinsic_environment::GlobalEnvironment::standard(
                crate::checker::intrinsic_environment::LibSet::ALL,
            ),
            super::source_is_module(parsed.product()),
            options,
        )
    }

    #[test]
    fn non_callable_expression_emits_not_callable() {
        let (_, diagnostics) = bound("const x = 1; x();");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == EXPRESSION_NOT_CALLABLE)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn non_null_assertion_removes_nullish_union_members() {
        let (_, diagnostics) =
            bound_strict("declare const value: string | null; const text: string = value!;");
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == TYPE_NOT_ASSIGNABLE),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn strict_null_direct_member_access_is_diagnosed() {
        let (_, diagnostics) = bound_strict("declare const value: { x: number } | null; value.x;");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == super::STRICT_NULL_MEMBER_ACCESS),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn strict_null_non_null_and_optional_member_access_preserve_types() {
        let (_, diagnostics) = bound_strict(
            "declare const value: { x: number } | null;\n\
             const asserted: number = value!.x;\n\
             const optional: number | undefined = value?.x;",
        );
        assert!(
            !diagnostics.iter().any(|diagnostic| {
                matches!(
                    diagnostic.code(),
                    super::STRICT_NULL_MEMBER_ACCESS | TYPE_NOT_ASSIGNABLE
                )
            }),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn used_before_assigned_only_within_same_execution_boundary() {
        let (_, diagnostics) = bound_strict(
            "var a: string;\n\
             function f() { a; }\n\
             class C { static x = a; }\n\
             namespace N { var b: string; b; }\n\
             function g() { var c: string; c; }\n\
             var d: string; d;\n",
        );
        let c038 = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code() == super::USED_BEFORE_ASSIGNED)
            .count();
        assert_eq!(
            c038, 3,
            "expected C038 for namespace b, inner g c, and top-level d"
        );
    }
    #[test]
    fn class_property_initialized_in_constructor() {
        let (_, diagnostics) = bound_strict(
            "class C { x: number; constructor() { this.x = 1; } }\n\
             class D { y: number; constructor() { return; } }\n\
             class F { w: number; }\n",
        );
        let c028 = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code() == PROPERTY_NOT_INITIALIZED)
            .count();
        assert_eq!(c028, 2, "expected C028 for D.y and F.w, not for C.x");
    }

    #[test]
    fn property_initialization_requires_the_strict_option() {
        // Upstream abstractClassUnionInstantiation.errors.txt (sha256
        // 20f79cd35dd8e7298a3cdfe4ba051d9cc4227c910b9a5fd5ca351a5dc6be9f02)
        // reports TS2564 for `a: string` on an abstract class under the
        // suite's strict-default-on run. As upstream documents,
        // strictPropertyInitialization only takes effect together with
        // strictNullChecks: the undefined-membership probe is a strict-null
        // relation. Off either flag, the source is clean.
        let on = bound_with_options(
            "abstract class A { a: string; }\n",
            super::ProgramCheckOptions::standard()
                .with_strict_null_checks(true)
                .with_strict_property_initialization(true),
        );
        assert!(
            on.1.iter()
                .any(|diagnostic| diagnostic.code() == PROPERTY_NOT_INITIALIZED),
            "{:?}",
            on.1
        );

        let spi_only = bound_with_options(
            "abstract class A { a: string; }\n",
            super::ProgramCheckOptions::standard().with_strict_property_initialization(true),
        );
        assert!(
            !spi_only
                .1
                .iter()
                .any(|diagnostic| diagnostic.code() == PROPERTY_NOT_INITIALIZED),
            "TS2564 is inert without strictNullChecks: {:?}",
            spi_only.1
        );

        let off = bound_with_options(
            "abstract class A { a: string; }\n",
            super::ProgramCheckOptions::standard(),
        );
        assert!(
            !off.1
                .iter()
                .any(|diagnostic| diagnostic.code() == PROPERTY_NOT_INITIALIZED),
            "{:?}",
            off.1
        );
    }

    fn overload_diagnostics(
        diagnostics: &[Diagnostic],
    ) -> Vec<(crate::diagnostic::DiagnosticCode, usize, usize)> {
        diagnostics
            .iter()
            .filter(|diagnostic| {
                [
                    MISSING_METHOD_RETURN_TYPE,
                    FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION,
                    FUNCTION_IMPLEMENTATION_WRONG_NAME,
                ]
                .contains(&diagnostic.code())
            })
            .map(|diagnostic| {
                let range = diagnostic.range();
                (diagnostic.code(), range.start().get(), range.end().get())
            })
            .collect()
    }

    #[test]
    fn implicit_any_return_pair_requires_no_implicit_any() {
        let source = "function f1();\n1+1;\n";
        let (_, strict_diagnostics) = bound_with_options(
            source,
            super::ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert_eq!(
            overload_diagnostics(&strict_diagnostics),
            vec![
                (FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, 9, 11),
                (MISSING_METHOD_RETURN_TYPE, 9, 11),
            ],
            "{strict_diagnostics:?}"
        );

        let (_, loose_diagnostics) =
            bound_with_options(source, super::ProgramCheckOptions::standard());
        assert_eq!(
            overload_diagnostics(&loose_diagnostics),
            vec![(FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, 9, 11)],
            "{loose_diagnostics:?}"
        );
    }

    #[test]
    fn wrong_name_implementation_reports_wrong_name_not_missing() {
        let (_, diagnostics) = bound_with_options(
            "function foo();\nfunction bar() {}\n",
            super::ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert_eq!(
            overload_diagnostics(&diagnostics),
            vec![
                (MISSING_METHOD_RETURN_TYPE, 9, 12),
                (FUNCTION_IMPLEMENTATION_WRONG_NAME, 25, 28),
            ],
            "{diagnostics:?}"
        );
    }

    #[test]
    fn block_statement_lists_scan_overload_groups() {
        let (_, diagnostics) = bound_with_options(
            "{\n    function foo();\n    function bar() {}\n}\n",
            super::ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert_eq!(
            overload_diagnostics(&diagnostics),
            vec![
                (MISSING_METHOD_RETURN_TYPE, 15, 18),
                (FUNCTION_IMPLEMENTATION_WRONG_NAME, 35, 38),
            ],
            "{diagnostics:?}"
        );
    }

    #[test]
    fn namespace_statement_lists_scan_overload_groups() {
        let (_, diagnostics) = bound_with_options(
            "namespace M {\n   function foo();\n}\n",
            super::ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert_eq!(
            overload_diagnostics(&diagnostics),
            vec![
                (FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, 26, 29),
                (MISSING_METHOD_RETURN_TYPE, 26, 29),
            ],
            "{diagnostics:?}"
        );
    }

    #[test]
    fn annotated_block_signature_skips_return_pair() {
        let (_, diagnostics) = bound_with_options(
            "{\n    function foo(): void;\n}\n",
            super::ProgramCheckOptions::standard(),
        );
        assert_eq!(
            overload_diagnostics(&diagnostics),
            vec![(FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION, 15, 18)],
            "{diagnostics:?}"
        );
    }

    #[test]
    fn default_export_function_overloads_share_the_statement_group() {
        let (_, wrong_name) = bound_with_options(
            "export default function foo();\nexport default function bar() {}\n",
            super::ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert_eq!(
            overload_diagnostics(&wrong_name),
            vec![
                (MISSING_METHOD_RETURN_TYPE, 24, 27),
                (FUNCTION_IMPLEMENTATION_WRONG_NAME, 55, 58),
            ],
            "{wrong_name:?}"
        );

        let (_, matched) =
            bound("export default function f();\nexport default function f(value: string) {}\n");
        assert!(overload_diagnostics(&matched).is_empty(), "{matched:?}");
    }

    #[test]
    fn literal_named_properties_exempt_from_initialization_check() {
        let (_, diagnostics) = bound_strict("class C { 1: number; 'a': number; b: number; }\n");
        let c028 = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code() == PROPERTY_NOT_INITIALIZED)
            .count();
        assert_eq!(
            c028, 1,
            "expected C028 only for identifier-named property b"
        );
    }

    #[test]
    fn export_default_interface_binds_name_for_type_references() {
        let (_, diagnostics) = bound("export default interface A { x: number; }\ntype T = A;\n");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn new_target_outside_function_is_diagnosed() {
        let (_, diagnostics) = bound("const a = new.target;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code().as_str() == "BAMTS-C044")
        );
    }

    #[test]
    fn new_target_inside_function_and_constructor_is_allowed() {
        let (_, diagnostics) = bound(
            "function f() { new.target; } \
             const g = function () { new.target; }; \
             class C { constructor() { new.target; } }",
        );
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code().as_str() == "BAMTS-C044")
        );
    }

    #[test]
    fn new_target_inside_method_and_static_block_is_diagnosed() {
        let (_, diagnostics) = bound(
            "class C { \
                 m() { new.target; } \
                 static { new.target; } \
             }",
        );
        let new_target_errors = diagnostics
            .iter()
            .filter(|d| d.code().as_str() == "BAMTS-C044")
            .count();
        assert_eq!(new_target_errors, 2, "{diagnostics:?}");
    }

    #[test]
    fn new_target_inside_arrow_inherits_enclosing_function() {
        let (_, diagnostics) = bound("function f() { const a = () => new.target; }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code().as_str() == "BAMTS-C044")
        );
    }

    #[test]
    fn set_accessor_parameter_initializer_is_diagnosed() {
        let (_, diagnostics) = bound("class C { set foo(x = 1) { } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == SET_ACCESSOR_PARAMETER_INITIALIZER)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn object_literal_set_accessor_parameter_initializer_is_diagnosed() {
        let (_, diagnostics) = bound("const o = { set bar(y = 2) { } };");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == SET_ACCESSOR_PARAMETER_INITIALIZER)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn plain_set_accessor_without_initializer_is_not_diagnosed() {
        let (_, diagnostics) = bound("class C { set foo(x) { } }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == SET_ACCESSOR_PARAMETER_INITIALIZER),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ambient_class_getter_implementation_is_diagnosed() {
        let (_, diagnostics) = bound("declare class C { get foo() { return 0; } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == AMBIENT_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ambient_class_setter_implementation_is_diagnosed() {
        let (_, diagnostics) = bound("declare class C { set foo(v) { } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == AMBIENT_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ambient_class_method_implementation_is_diagnosed() {
        let (_, diagnostics) = bound("declare class C { m() { } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == AMBIENT_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ambient_function_implementation_is_diagnosed() {
        let (_, diagnostics) = bound("declare function f() { }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == AMBIENT_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn free_function_overloads_are_retained_before_the_active_implementation() {
        let (model, diagnostics) = bound(
            "function f(value: string): string;\
             function f(value: number): number;\
             function f(value: any): any { return value; }",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");

        let symbol = value_symbol(&model, "f");
        let overloads = model.overload_signatures(symbol);
        assert_eq!(overloads.len(), 2);
        assert_eq!(
            overloads[0].parameters()[0].type_id(),
            model.types().string()
        );
        assert_eq!(overloads[0].return_type(), model.types().string());
        assert_eq!(
            overloads[1].parameters()[0].type_id(),
            model.types().number()
        );
        assert_eq!(overloads[1].return_type(), model.types().number());

        let Type::Function(active) = model.types().get(model.symbol_type(symbol)) else {
            panic!("function symbol has an active function type");
        };
        assert_eq!(active.parameters()[0].type_id(), model.types().any());
        assert_eq!(active.return_type(), model.types().any());
    }

    #[test]
    fn declaration_file_functions_do_not_require_implementations() {
        let (_, ambient) = bound_declaration("export function f(): void;");
        assert!(
            !ambient
                .iter()
                .any(|diagnostic| diagnostic.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION),
            "{ambient:?}"
        );

        let (_, active) = bound("function f(): void;");
        assert_eq!(
            active
                .iter()
                .filter(|diagnostic| {
                    diagnostic.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION
                })
                .count(),
            1,
            "{active:?}"
        );
    }

    #[test]
    fn declaration_file_class_methods_do_not_require_implementations() {
        let (_, diagnostics) =
            bound_declaration("export class Queue<T> { drain(): IterableIterator<T>; }");
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn non_ambient_class_method_implementation_is_allowed() {
        let (_, diagnostics) = bound("class C { m() { return 0; } }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == AMBIENT_IMPLEMENTATION),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ambient_class_overload_signature_is_allowed() {
        let (_, diagnostics) = bound("declare class C { m(); }");
        assert!(
            !diagnostics.iter().any(|d| {
                d.code() == AMBIENT_IMPLEMENTATION
                    || d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION
                    || d.code() == FUNCTION_IMPLEMENTATION_WRONG_NAME
            }),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn class_method_overload_inside_declare_namespace_is_allowed() {
        let (_, diagnostics) = bound("declare namespace N { export class C { m(); } }");
        assert!(
            !diagnostics.iter().any(|d| {
                d.code() == AMBIENT_IMPLEMENTATION
                    || d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION
                    || d.code() == FUNCTION_IMPLEMENTATION_WRONG_NAME
            }),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn get_accessor_parameters_are_diagnosed() {
        let (_, diagnostics) = bound("const o = { get foo(v: number) { return 0; } };");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == GET_ACCESSOR_PARAMETERS)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn get_accessor_without_return_value_is_diagnosed() {
        let (_, diagnostics) = bound("const o = { get foo() { } };");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == GET_ACCESSOR_NO_RETURN)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn get_accessor_with_return_value_is_allowed() {
        let (_, diagnostics) = bound("const o = { get foo() { return 0; } };");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == GET_ACCESSOR_NO_RETURN),
            "{diagnostics:?}"
        );
    }

    /// Upstream accessorWithoutBody1 expects zero diagnostics: a getter whose
    /// body the parser silently recovers as absent must not trip the
    /// missing-return check (object-literal and class sides share the gate).
    #[test]
    fn bodyless_getter_stays_silent_on_missing_return() {
        let (_, diagnostics) = bound("const o = { get foo() };");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == GET_ACCESSOR_NO_RETURN),
            "{diagnostics:?}"
        );
        let (_, diagnostics) = bound("class C { get bar() }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == GET_ACCESSOR_NO_RETURN),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn class_method_overload_missing_implementation_is_diagnosed() {
        let (_, diagnostics) = bound("class C { foo(); }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn class_method_overload_wrong_implementation_name_is_diagnosed() {
        let (_, diagnostics) = bound("class C { foo(); bar() { } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == FUNCTION_IMPLEMENTATION_WRONG_NAME)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn class_method_overload_with_implementation_is_allowed() {
        let (_, diagnostics) = bound("class C { foo(a: string); foo(a: number); foo(a: any) { } }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION
                    || d.code() == FUNCTION_IMPLEMENTATION_WRONG_NAME),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn abstract_method_is_not_an_overload_signature() {
        // An abstract method is a complete declaration: it has no body by
        // definition and must not be treated as an overload signature that
        // requires a following implementation, nor paired against the next
        // method as a name-mismatched implementation.
        let (_, diagnostics) = bound("abstract class C { abstract foo(): void; bar() { } }");
        assert!(
            !diagnostics.iter().any(|d| {
                d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION
                    || d.code() == FUNCTION_IMPLEMENTATION_WRONG_NAME
            }),
            "{diagnostics:?}"
        );

        // The abstract exemption must not blanket-disable the diagnostic: a
        // genuine bodyless non-abstract overload signature with no following
        // implementation still reports C039, even inside an abstract class.
        let (_, diagnostics) = bound("abstract class C { real(): void; }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn constructor_type_parameters_are_diagnosed() {
        let (_, diagnostics) = bound("class C { constructor<T>() { } }");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == CONSTRUCTOR_TYPE_PARAMETERS)
                .count(),
            1,
            "{diagnostics:?}"
        );
    }

    #[test]
    fn constructor_without_type_parameters_is_allowed() {
        let (_, diagnostics) = bound("class C { constructor() { } }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == CONSTRUCTOR_TYPE_PARAMETERS),
            "{diagnostics:?}"
        );
    }
    #[test]
    fn class_member_symbol_parent_is_class() {
        let (model, diagnostics) =
            bound("class Board { ships: number[] = []; allShipsSunk() { return true; } }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let ships = model
            .symbols()
            .iter()
            .find(|s| s.name() == "ships")
            .expect("ships symbol");
        let method = model
            .symbols()
            .iter()
            .find(|s| s.name() == "allShipsSunk")
            .expect("method symbol");
        assert_eq!(
            model
                .symbols()
                .iter()
                .filter(|s| s.name() == "allShipsSunk")
                .count(),
            1,
            "duplicate allShipsSunk"
        );
        assert_eq!(
            ships.parent().map(|s| model.symbol(s).name()),
            Some("Board"),
            "ships parent"
        );
        assert!(
            method.parent().is_some(),
            "method parent is None; kind={:?}",
            method.kind()
        );
    }

    #[test]
    fn function_this_parameter_typed_body_uses_it() {
        let (model, diagnostics) =
            bound("interface Foo { n: number; }\nfunction f(this: Foo) { return this.n; }");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let index = model
            .symbols()
            .iter()
            .position(|s| s.name() == "f")
            .expect("function symbol");
        let function_type = model.symbol_type(SymbolId::new(index as u32));
        assert!(
            matches!(model.types().get(function_type), Type::Function(signature) if signature.parameters().is_empty()),
            "'this' parameter is not part of the function signature"
        );
    }

    #[test]
    fn accessor_this_parameter_is_diagnosed() {
        let (_, diagnostics) = bound("const o = { get x(this: any) { return 0; } };");
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == ACCESSOR_THIS_PARAMETER)
                .count(),
            1,
            "{diagnostics:?}"
        );
        assert_eq!(
            diagnostics
                .iter()
                .filter(|d| d.code() == GET_ACCESSOR_PARAMETERS)
                .count(),
            0,
            "this-only getter should not emit generic get-accessor-parameters error"
        );
    }

    #[test]
    fn object_literal_get_and_set_combine_into_non_readonly_property() {
        let (model, diagnostics) =
            bound("const o = { get x() { return 1; }, set x(v: number) { } };");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let index = model
            .symbols()
            .iter()
            .position(|s| s.name() == "o")
            .expect("object symbol");
        let object_type = model.symbol_type(SymbolId::new(index as u32));
        let Type::ObjectType(object) = model.types().get(object_type) else {
            panic!(
                "object literal type expected, got {:?}",
                model.types().get(object_type)
            );
        };
        let x = object
            .properties
            .iter()
            .find(|p| p.name() == "x")
            .expect("x property");
        assert!(!x.readonly(), "get/set pair should not be readonly");
        assert_eq!(model.types().get(x.type_id()), &Type::Number);
    }

    #[test]
    fn js_unannotated_let_accepts_reassignment_of_different_type() {
        // In plain JavaScript the checker must not invent an annotation for an
        // un-annotated mutable binding, so reassigning it to a wholly different
        // type is not a TYPE_NOT_ASSIGNABLE error.
        let (_, diagnostics) = bound_js("let g = { a: 1 };\ng = 0;\n");
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == TYPE_NOT_ASSIGNABLE),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn ts_annotated_const_mismatch_still_reports_not_assignable() {
        // A genuine annotation mismatch in a TypeScript source must still fire.
        let (_, diagnostics) = bound("const s: string = 1;\n");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == TYPE_NOT_ASSIGNABLE),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn function_body_narrowing_does_not_leak_to_sibling_statements() {
        // A guard inside a function body narrows a captured outer variable only
        // for the function's own control flow; the outer program point must keep
        // the declared union. Without flow isolation, the assignment below would
        // incorrectly see `x` as `string`.
        let (_, diagnostics) = bound(
            "declare let x: string | number;\n\
             function f() { if (typeof x !== \"string\") return; }\n\
             const y: string = x;\n",
        );
        assert!(
            diagnostics.iter().any(|d| d.code() == TYPE_NOT_ASSIGNABLE),
            "expected x to remain string | number after the function: {diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_readonly_class_property_in_constructor_is_allowed() {
        let (_, diagnostics) =
            bound("class C { readonly x: number; constructor() { this.x = 1; } }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_readonly_class_property_outside_constructor_is_diagnosed() {
        let (_, diagnostics) = bound("class C { readonly x: number; m() { this.x = 1; } }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_getter_only_class_property_in_constructor_is_diagnosed() {
        let (_, diagnostics) =
            bound("class C { get x() { return 1; } constructor() { this.x = 1; } }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_getter_only_object_property_is_diagnosed() {
        let (_, diagnostics) = bound("const o = { get x() { return 1; } }; o.x = 1;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_get_set_object_property_is_allowed() {
        let (_, diagnostics) =
            bound("const o = { get x() { return 1; }, set x(v: number) { } }; o.x = 1;");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_readonly_interface_property_is_diagnosed() {
        let (_, diagnostics) =
            bound("interface I { readonly x: number; } declare const o: I; o.x = 1;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn assignment_to_readonly_type_literal_property_is_diagnosed() {
        let (_, diagnostics) = bound("declare const o: { readonly x: number }; o.x = 1;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == ASSIGNMENT_TO_READONLY),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn const_narrowed_value_remains_narrowed_inside_nested_arrow() {
        // A `const` binding narrowed by a guard before the arrow should stay
        // narrowed inside the arrow body: `x` is `string` there, so assigning
        // it to `number` must error.
        let (_, diagnostics) = bound(
            "declare const x: string | number;\n\
             if (typeof x !== \"string\") return;\n\
             const f = () => { const y: number = x; };\n",
        );
        assert!(
            diagnostics.iter().any(|d| d.code() == TYPE_NOT_ASSIGNABLE),
            "expected x to be narrowed to string inside the arrow: {diagnostics:?}"
        );
    }

    #[test]
    fn reassigned_let_narrowing_does_not_cross_function_boundary() {
        // A `let` binding that is narrowed before a function declaration is
        // reassigned later in the same scope. The narrowing must NOT cross the
        // function boundary because the variable could be changed between the
        // guard and the deferred call.
        let (_, diagnostics) = bound(
            "declare let x: string | number;\n\
             if (typeof x !== \"string\") return;\n\
             function f() { const y: number = x; }\n\
             x = 1;\n",
        );
        assert!(
            diagnostics.iter().any(|d| d.code() == TYPE_NOT_ASSIGNABLE),
            "expected x to remain string | number inside f because it is reassigned: {diagnostics:?}"
        );
    }

    #[test]
    fn sibling_branch_narrowing_does_not_leak_into_nested_function() {
        // A guard in one branch of an `if` narrows `x` to `string` only within
        // that branch. A function declared in the sibling (else) branch must
        // NOT see the narrowing.
        let (_, diagnostics) = bound(
            "declare let x: string | number;\n\
             if (typeof x === \"string\") {\n\
               const a: string = x;\n\
             } else {\n\
               const f = () => { const y: string = x; };\n\
             }\n",
        );
        assert!(
            diagnostics.iter().any(|d| d.code() == TYPE_NOT_ASSIGNABLE),
            "expected x to remain string | number in the else-branch arrow: {diagnostics:?}"
        );
    }

    #[test]
    fn const_narrowing_passes_through_function_declaration() {
        // A `const` binding narrowed before a function declaration: the
        // function body should see the narrowed type because `const` cannot be
        // reassigned. Assigning `x` (narrowed to `string`) to `number` inside
        // the function must error.
        let (_, diagnostics) = bound(
            "declare const x: string | number;\n\
             if (typeof x !== \"string\") return;\n\
             function f() { const y: number = x; }\n",
        );
        assert!(
            diagnostics.iter().any(|d| d.code() == TYPE_NOT_ASSIGNABLE),
            "expected x to be narrowed to string inside f: {diagnostics:?}"
        );
    }

    #[test]
    fn future_write_prevents_captured_narrowing() {
        let (_, diagnostics) = bound(
            "let f: (() => void) | undefined = () => {};\n             if (f) {\n                 const g = () => f();\n                 f = undefined;\n                 g();\n             }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == EXPRESSION_NOT_CALLABLE),
            "expected a later write to invalidate the earlier closure capture: {diagnostics:?}"
        );
    }

    #[test]
    fn loop_destructuring_write_prevents_captured_narrowing() {
        let (_, diagnostics) = bound(
            "let f: (() => void) | undefined = () => {};\n             if (f) {\n                 const read = () => f();\n                 for ([f] of [[undefined]]) {}\n                 read();\n             }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == EXPRESSION_NOT_CALLABLE),
            "expected a destructuring for-of write to invalidate capture: {diagnostics:?}"
        );
    }

    #[test]
    fn never_written_let_narrowing_passes_into_nested_arrow() {
        let (_, diagnostics) = bound(
            "declare let f: (() => void) | undefined;\n             if (f) {\n                 const read = () => f();\n                 read();\n             }",
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == EXPRESSION_NOT_CALLABLE),
            "expected a never-written root to remain narrowed: {diagnostics:?}"
        );
    }

    #[test]
    fn property_type_identity_includes_access_and_declaring_class() {
        use crate::syntax::Accessibility;

        let mut table = TypeTable::new();
        let number = table.number();
        let owner = SymbolId::new(900);
        let other_owner = SymbolId::new(901);

        let public = PropertyType::new("x", false, number);
        let private = PropertyType::new("x", false, number)
            .with_accessibility(Accessibility::Private, Some(owner));
        let protected = PropertyType::new("x", false, number)
            .with_accessibility(Accessibility::Protected, Some(owner));
        let private_other = PropertyType::new("x", false, number)
            .with_accessibility(Accessibility::Private, Some(other_owner));

        assert_eq!(public, public);
        assert_eq!(private, private);
        assert_eq!(protected, protected);
        assert_ne!(public, private);
        assert_ne!(public, protected);
        assert_ne!(private, protected);
        assert_ne!(private, private_other);

        let public_first = table.object_type(vec![public.clone()]);
        let private_first = table.object_type(vec![private.clone()]);
        let public_second = table.object_type(vec![public.clone()]);
        let private_second = table.object_type(vec![private.clone()]);
        let public_fresh = table.object_type(vec![PropertyType::new("x", false, number)]);

        assert_eq!(public_first, public_second);
        assert_eq!(public_first, public_fresh);
        assert_eq!(private_first, private_second);
        assert_ne!(public_first, private_first);
    }

    #[test]
    fn object_type_interning_is_declaration_order_independent() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();

        let forward = table.object_type(vec![
            PropertyType::new("a", false, number),
            PropertyType::new("b", false, string),
        ]);
        let backward = table.object_type(vec![
            PropertyType::new("b", false, string),
            PropertyType::new("a", false, number),
        ]);

        assert_eq!(forward, backward);
    }

    #[test]
    fn tuple_possible_elements_include_optional_prefix_rest_and_suffix() {
        let table = TypeTable::new();
        let first = table.number();
        let optional = table.string();
        let rest = table.boolean();
        let suffix = table.unknown();
        let shape = TupleShape {
            prefix: vec![first, optional],
            required: 0,
            rest: Some(rest),
            suffix: vec![suffix],
        };

        assert_eq!(shape.element_types_at(0), [first, rest, suffix]);
        assert_eq!(shape.element_types_at(1), [optional, rest, suffix]);
        assert_eq!(shape.element_types_at_length(0, 2), [rest, first]);
        assert_eq!(shape.element_types_from_end(2), [rest, first, optional]);
    }

    #[test]
    fn imported_symbol_identity_is_source_local_and_preserves_private_origin() {
        use crate::syntax::Accessibility;

        let source_symbol = SymbolId::new(700);
        let mut left = TypeTable::new();
        let left_number = left.number();
        left.declare_class(source_symbol, Vec::new());
        let left_raw = left.object_type(vec![
            PropertyType::new("value", false, left_number)
                .with_accessibility(Accessibility::Private, Some(source_symbol)),
        ]);
        left.publish_final_class_template(source_symbol, left_raw);
        let left_class = left.applied_class(source_symbol, Vec::new());

        let mut right = TypeTable::new();
        let right_string = right.string();
        right.declare_class(source_symbol, Vec::new());
        let right_raw = right.object_type(vec![
            PropertyType::new("value", false, right_string)
                .with_accessibility(Accessibility::Private, Some(source_symbol)),
        ]);
        right.publish_final_class_template(source_symbol, right_raw);
        let right_class = right.applied_class(source_symbol, Vec::new());

        let mut target = TypeTable::new();
        let mut next_symbol = 1_000;
        let (imported_left, _) = target.import_type(
            &left,
            left_class,
            &[],
            &mut super::ImportedTypeMap::default(),
            &mut next_symbol,
        );
        let (imported_right, _) = target.import_type(
            &right,
            right_class,
            &[],
            &mut super::ImportedTypeMap::default(),
            &mut next_symbol,
        );
        let Type::AppliedClass {
            symbol: left_symbol,
            ..
        } = target.get(imported_left)
        else {
            panic!("left import must remain an applied class");
        };
        let left_symbol = *left_symbol;
        let Type::AppliedClass {
            symbol: right_symbol,
            ..
        } = target.get(imported_right)
        else {
            panic!("right import must remain an applied class");
        };
        let right_symbol = *right_symbol;
        assert_ne!(left_symbol, right_symbol);

        let left_view = target
            .prepare_applied_class_view(imported_left)
            .expect("left class view");
        let right_view = target
            .prepare_applied_class_view(imported_right)
            .expect("right class view");
        let Type::ObjectType(left_object) = target.get(left_view) else {
            panic!("left class view must be structural");
        };
        let Type::ObjectType(right_object) = target.get(right_view) else {
            panic!("right class view must be structural");
        };
        assert_eq!(
            left_object.properties[0].declaring_class(),
            Some(left_symbol)
        );
        assert_eq!(
            right_object.properties[0].declaring_class(),
            Some(right_symbol)
        );
    }

    #[test]
    fn imported_named_structure_is_independent_of_source_symbol_numbering() {
        let mut left = TypeTable::new();
        let left_number = left.number();
        let left_structure = left.object_type(vec![PropertyType::new("value", false, left_number)]);
        let left_symbol = SymbolId::new(3);
        left.set_interface_structure(left_symbol, left_structure);
        let left_named = left.named(left_symbol);

        let mut right = TypeTable::new();
        let right_number = right.number();
        let right_structure =
            right.object_type(vec![PropertyType::new("value", false, right_number)]);
        let right_symbol = SymbolId::new(999);
        right.set_interface_structure(right_symbol, right_structure);
        let right_named = right.named(right_symbol);

        let mut target = TypeTable::new();
        let mut next_symbol = 2_000;
        let (imported_left, _) = target.import_type(
            &left,
            left_named,
            &[],
            &mut super::ImportedTypeMap::default(),
            &mut next_symbol,
        );
        let (imported_right, _) = target.import_type(
            &right,
            right_named,
            &[],
            &mut super::ImportedTypeMap::default(),
            &mut next_symbol,
        );

        assert_eq!(
            target.named_structural_view(imported_left),
            target.named_structural_view(imported_right)
        );
    }

    #[test]
    fn tuple_rest_call_arity_counts_required_optional_and_variadic_elements() {
        let (_, diagnostics) = bound(
            "function allOptional(...args: [number?]) {}\n\
             allOptional();\n\
             allOptional(1);\n\
             allOptional(1, 2);\n\
             function requiredFirst(...args: [number, string?]) {}\n\
             requiredFirst();\n\
             requiredFirst(1);\n\
             requiredFirst(1, 'x');\n\
             requiredFirst(1, 'x', true);\n\
             function variadic(...args: [number, string?, ...boolean[]]) {}\n\
             variadic();\n\
             variadic(1);\n\
             variadic(1, 'x');\n\
             variadic(1, 'x', true, false);\n\
             function optionalFixed(a: number, b?: string, ...args: [boolean?]) {}\n\
             optionalFixed(1);\n\
             optionalFixed(1, 'x');\n\
             optionalFixed(1, 'x', true);\n\
             optionalFixed(1, 'x', true, false);\n\
             function mixed(a: number, ...args: [string, boolean?]) {}\n\
             mixed(1);\n\
             mixed(1, 'x');\n\
             mixed(1, 'x', true);\n\
             mixed(1, 'x', true, false);\n",
        );
        let count = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code() == ARGUMENT_COUNT_MISMATCH)
            .count();
        assert_eq!(count, 7, "{diagnostics:?}");
    }

    fn symbol_named(model: &super::SemanticModel, name: &str) -> SymbolId {
        let index = model
            .symbols()
            .iter()
            .position(|symbol| symbol.name() == name)
            .unwrap_or_else(|| panic!("symbol `{name}` not bound"));
        SymbolId::new(index as u32)
    }

    /// F3 exemplar ClassDeclaration11: a class member binds as a qualified
    /// `C.foo` symbol whose declaration anchor is the member name token.
    #[test]
    fn class_member_symbol_carries_qualified_identity_and_member_anchor() {
        let (model, diagnostics) = bound("class C {\n   constructor();\n   foo() { }\n}");
        // The bare `constructor();` signature before `foo` trips the
        // pre-existing overload-order check (C049); the F3 contract under test
        // here is the member symbol itself, so only duplicates are forbidden.
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == DUPLICATE_DECLARATION),
            "{diagnostics:?}"
        );
        let class_id = value_symbol(&model, "C");
        let foo = symbol_named(&model, "foo");
        assert_eq!(model.symbol(foo).parent(), Some(class_id));
        assert_eq!(model.qualified_name(foo), "C.foo");
        // Anchor: the `foo` identifier starts at line 2, column 3; its UTF-16
        // offset lands at 31 in the 3-line source.
        assert_eq!(
            model.symbol(foo).range().start().get(),
            31,
            "anchor at `foo` identifier"
        );
    }

    #[test]
    fn interface_member_symbols_qualify_against_the_interface() {
        let (model, diagnostics) = bound("interface I {\n    item: number;\n    go(): void;\n}");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let interface_id = type_symbol(&model, "I");
        let item = symbol_named(&model, "item");
        let go = symbol_named(&model, "go");
        assert_eq!(model.symbol(item).parent(), Some(interface_id));
        assert_eq!(model.qualified_name(item), "I.item");
        assert_eq!(model.qualified_name(go), "I.go");
    }

    #[test]
    fn duplicate_interface_members_share_one_symbol() {
        let (model, diagnostics) = bound("interface I {\n    item: number;\n    item: number;\n}");
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == DUPLICATE_DECLARATION),
            "{diagnostics:?}"
        );
        assert_eq!(
            model
                .symbols()
                .iter()
                .filter(|symbol| symbol.name() == "item")
                .count(),
            1
        );
    }

    #[test]
    fn constructor_parameter_property_binds_as_qualified_class_member() {
        let (model, diagnostics) =
            bound("class C {\n    constructor(public x: number) { }\n}\nvar c = new C(1);\nc.x;");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let class_id = value_symbol(&model, "C");
        let x = symbol_named(&model, "x");
        assert_eq!(model.symbol(x).parent(), Some(class_id));
        assert_eq!(model.qualified_name(x), "C.x");
        // The reference row for `c.x` resolves to the parameter property.
        let member_refs: Vec<_> = model
            .symbol_references()
            .iter()
            .filter(|(_, symbol)| *symbol == x)
            .collect();
        assert!(!member_refs.is_empty(), "`c.x` records a reference row");
    }

    #[test]
    fn this_expression_records_class_owner_reference() {
        let (model, diagnostics) =
            bound("class C { m() { return this; } }\nvar c = new C();\nc.m();");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let class_id = value_symbol(&model, "C");
        assert!(
            model
                .symbol_references()
                .iter()
                .any(|(_, symbol)| *symbol == class_id),
            "`this` records a reference to the class symbol"
        );
    }

    #[test]
    fn member_access_records_qualified_reference_rows() {
        let (model, diagnostics) =
            bound("class C { m() { return this.n; } n: number = 0; }\nvar c = new C();\nc.m().n;");
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let n = symbol_named(&model, "n");
        let rows: Vec<_> = model
            .symbol_references()
            .iter()
            .filter(|(_, symbol)| *symbol == n)
            .map(|(range, _)| range)
            .collect();
        assert!(
            rows.len() >= 2,
            "identifier and path rows recorded: {rows:?}"
        );
    }
    /// F3 exemplars aliasUsedAsNameValue / aliasUsageInArray: `import x =
    /// require(...)` aliases bind as Import symbols anchored at their alias
    /// name, and their use sites record reference rows against the alias.
    #[test]
    fn import_alias_binds_with_anchor_and_reference_rows() {
        let (model, diagnostics) =
            bound("import mod = require(\"./mod\");\nimport b = require(\"./b\");\nb(mod);");
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == DUPLICATE_DECLARATION),
            "{diagnostics:?}"
        );
        let mod_alias = value_symbol(&model, "mod");
        let b_alias = value_symbol(&model, "b");
        assert_eq!(model.symbol(mod_alias).kind(), SymbolKind::Import);
        // ImportEquals aliases anchor at their statement full start (the
        // `import` keyword); upstream's Decl marker derives from that start.
        assert_eq!(model.symbol(mod_alias).range().start().get(), 0);
        assert_eq!(model.symbol(b_alias).range().start().get(), 31);
        assert!(
            model
                .symbol_references()
                .iter()
                .any(|(_, symbol)| *symbol == b_alias),
            "`b(mod)` records a reference row for `b`"
        );
        assert!(
            model
                .symbol_references()
                .iter()
                .any(|(_, symbol)| *symbol == mod_alias),
            "`b(mod)` records a reference row for `mod`"
        );
    }

    // -- TS2397: declaration name conflicts with built-in global identifier --

    #[test]
    fn var_global_this_in_script_reports_ts2397() {
        let (_model, diagnostics) = bound("var globalThis;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "var globalThis in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn var_undefined_in_script_reports_ts2397() {
        let (_model, diagnostics) = bound("var undefined = null;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "var undefined in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_undefined_in_script_reports_ts2397() {
        let (_model, diagnostics) = bound("namespace undefined { export var x = 42; }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "namespace undefined in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_global_this_in_script_reports_ts2397() {
        let (_model, diagnostics) = bound("namespace globalThis { export function foo() {} }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "namespace globalThis in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn var_global_this_in_module_does_not_report_ts2397() {
        let (_model, diagnostics) = bound("export var globalThis;");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "var globalThis in a module should NOT report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn class_undefined_in_script_does_not_report_ts2397() {
        let (_model, diagnostics) = bound("class undefined { foo: string; }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "class undefined should NOT report TS2397 (it gets TS2414): {diagnostics:?}"
        );
    }

    #[test]
    fn interface_undefined_in_script_does_not_report_ts2397() {
        let (_model, diagnostics) = bound("interface undefined { member: number; }");
        assert!(
            !diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "interface undefined should NOT report TS2397 (it gets TS2427): {diagnostics:?}"
        );
    }

    #[test]
    fn var_global_this_in_js_script_reports_ts2397() {
        let (_model, diagnostics) = bound_js("var globalThis;");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "var globalThis in a JS script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn function_undefined_in_script_reports_ts2397() {
        let (_model, diagnostics) = bound("function undefined() {}");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "function undefined in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn undefined_type_assignment4_namespace_emits_ts2397_after_class_and_interface() {
        // Mirrors the authority baseline undefinedTypeAssignment4.ts: class and
        // interface named `undefined` get TS2414/TS2427 (not TS2397), but the
        // namespace merge must still emit TS2397. The namespace merges with the
        // preceding class declaration, so the check must fire before the merge
        // early-return in `declare()`.
        let (_model, diagnostics) = bound(
            "class undefined { foo: string; }
interface undefined { member: number; }
namespace undefined { export var x = 42; }",
        );
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "namespace undefined should report TS2397 even when merging with preceding class/interface: {diagnostics:?}"
        );
    }

    #[test]
    fn class_global_this_in_script_reports_ts2397() {
        // No upstream baseline has `class globalThis`, but TS2397 has no
        // special class-specific diagnostic for `globalThis` (unlike `undefined`
        // which gets TS2414). So class globalThis should be flagged.
        let (_model, diagnostics) = bound("class globalThis { foo: string; }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "class globalThis in a script should report TS2397: {diagnostics:?}"
        );
    }

    #[test]
    fn interface_global_this_in_script_reports_ts2397() {
        // No upstream baseline has `interface globalThis`, but TS2397 has no
        // special interface-specific diagnostic for `globalThis` (unlike
        // `undefined` which gets TS2427). So interface globalThis should be
        // flagged.
        let (_model, diagnostics) = bound("interface globalThis { member: number; }");
        assert!(
            diagnostics
                .iter()
                .any(|d| d.code() == DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL),
            "interface globalThis in a script should report TS2397: {diagnostics:?}"
        );
    }
    // ── Namespace scope resolution tests (TS2304 over-fire fixes) ──

    fn has_cannot_find_name(diagnostics: &[Diagnostic]) -> bool {
        diagnostics.iter().any(|d| d.code() == CANNOT_FIND_NAME)
    }

    fn has_cannot_find_type(diagnostics: &[Diagnostic]) -> bool {
        diagnostics.iter().any(|d| d.code() == CANNOT_FIND_TYPE)
    }

    fn has_namespace_no_exported_member(diagnostics: &[Diagnostic]) -> bool {
        diagnostics
            .iter()
            .any(|d| d.code() == NAMESPACE_NO_EXPORTED_MEMBER)
    }

    #[test]
    fn namespace_private_class_visible_from_exported_class_type_position() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                class C2_private {}
                export class C3_public {
                    private v: C2_private;
                }
            }",
        );
        assert!(
            !has_cannot_find_type(&diagnostics),
            "C2_private should resolve from C3_public's type annotation: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_private_class_visible_from_exported_class_value_position() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                class C2_private {}
                export class C3_public {
                    public f() { return new C2_private(); }
                }
            }",
        );
        assert!(
            !has_cannot_find_name(&diagnostics),
            "C2_private should resolve from C3_public's method body: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_private_interface_visible_from_exported_class() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                interface I2_private {}
                export class C3_public {
                    private v: I2_private;
                }
            }",
        );
        assert!(
            !has_cannot_find_type(&diagnostics),
            "I2_private should resolve from C3_public: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_private_var_visible_from_exported_class_method() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                var v_private = 42;
                export class C3_public {
                    public f() { return v_private; }
                }
            }",
        );
        assert!(
            !has_cannot_find_name(&diagnostics),
            "v_private should resolve from C3_public's method: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_private_function_visible_from_exported_class_method() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                function f_private() {}
                export class C3_public {
                    public f() { return f_private(); }
                }
            }",
        );
        assert!(
            !has_cannot_find_name(&diagnostics),
            "f_private should resolve from C3_public's method: {diagnostics:?}"
        );
    }

    #[test]
    fn nested_namespace_sees_parent_private_class_type_position() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                export namespace m2 {
                    export function f1(c1: C1) {}
                }
                class C1 {}
            }",
        );
        assert!(
            !has_cannot_find_type(&diagnostics),
            "C1 should resolve from nested namespace m2: {diagnostics:?}"
        );
    }

    #[test]
    fn nested_namespace_sees_parent_private_class_value_position() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                export namespace m2 {
                    export function f1() { return new C1(); }
                }
                class C1 {}
            }",
        );
        assert!(
            !has_cannot_find_name(&diagnostics),
            "C1 should resolve from nested namespace m2 value position: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_forward_reference_to_private_class_resolves() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                export class C3_public {
                    private v: C2_private;
                }
                class C2_private {}
            }",
        );
        assert!(
            !has_cannot_find_type(&diagnostics),
            "C2_private forward reference should resolve: {diagnostics:?}"
        );
    }

    #[test]
    fn genuinely_undeclared_name_in_namespace_still_reports_ts2304() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                export class C3_public {
                    private v: NonExistent;
                }
            }",
        );
        assert!(
            has_cannot_find_type(&diagnostics),
            "NonExistent should produce TS2304: {diagnostics:?}"
        );
    }

    #[test]
    fn namespace_private_member_not_visible_from_outside_qualified() {
        let (_model, diagnostics) = bound(
            "namespace m1 {
                class C2_private {}
            }
            let x: m1.C2_private;",
        );
        assert!(
            has_namespace_no_exported_member(&diagnostics),
            "m1.C2_private should report TS2694 (no exported member): {diagnostics:?}"
        );
        assert!(
            !has_cannot_find_type(&diagnostics),
            "m1.C2_private should NOT report TS2304: {diagnostics:?}"
        );
    }

    // -- symbols facet gap regressions -------------------------------------
    //
    // Each test pins the `.symbols` rows a cited authority baseline renders.
    // The `Decl(unit, line, character)` coordinates follow the observer's
    // full-start rule (the position just past the last non-whitespace source
    // character before the declaration name); the test sources below carry no
    // comments or decorators, so a whitespace scan reproduces it exactly.

    /// Full-start `(line, character)` for a UTF-16 offset into an ASCII test
    /// source: skip trailing whitespace backward, then count to the position.
    fn full_start(text: &str, start: usize) -> (usize, usize) {
        let bytes = text.as_bytes();
        let mut cursor = start;
        while cursor > 0 && bytes[cursor - 1].is_ascii_whitespace() {
            cursor -= 1;
        }
        let mut line = 0usize;
        let mut character = 0usize;
        for &byte in &bytes[..cursor] {
            if byte == b'\n' {
                line += 1;
                character = 0;
            } else {
                character += 1;
            }
        }
        (line, character)
    }

    fn symbol_by_qualified_name(
        model: &super::SemanticModel,
        qualified: &str,
    ) -> (SymbolId, usize) {
        model
            .symbols()
            .iter()
            .enumerate()
            .find(|(index, symbol)| {
                model.qualified_name(SymbolId::new(*index as u32)) == qualified
                    && symbol.name() == qualified.rsplit('.').next().unwrap_or(qualified)
            })
            .map(|(index, _)| (SymbolId::new(index as u32), index))
            .unwrap_or_else(|| panic!("symbol `{qualified}` is not bound"))
    }

    fn reference_ranges(model: &super::SemanticModel, symbol: SymbolId) -> Vec<(usize, usize)> {
        model
            .symbol_references()
            .iter()
            .filter(|(_, id)| *id == symbol)
            .map(|(range, _)| (range.start().get(), range.end().get()))
            .collect()
    }

    /// `declarationImportTypeAliasInferredAndEmittable.symbols` renders, for
    /// `this.connItem = c.item;`:
    /// `>this.connItem : Symbol(Wrap.connItem, ...)`,
    /// `>this : Symbol(Wrap, ...)`,
    /// `>connItem : Symbol(Wrap.connItem, ...)`.
    #[test]
    fn assignment_target_records_member_reference_rows() {
        let text = "class Wrap {\n    connItem: number;\n    constructor() {\n        this.connItem = 3;\n    }\n}\n";
        let (model, _) = bound(text);
        let (conn_item, conn_item_index) = symbol_by_qualified_name(&model, "Wrap.connItem");
        let (wrap, _) = symbol_by_qualified_name(&model, "Wrap");

        // Declaration row: `>connItem : Symbol(Wrap.connItem, Decl(..., 0, 12))`
        // — full-start at the end of `class Wrap {`.
        let declaration = &model.symbols()[conn_item_index];
        assert_eq!(
            full_start(text, declaration.range().start().get()),
            (0, 12),
            "connItem Decl anchors at the full start of its declaration"
        );

        let line3 = text.split('\n').take(3).map(str::len).sum::<usize>() + 3;
        let path = (line3 + 8, line3 + 21);
        let identifier = (line3 + 13, line3 + 21);
        let this_range = (line3 + 8, line3 + 12);
        let ranges = reference_ranges(&model, conn_item);
        assert!(
            ranges.contains(&path),
            "assignment path `this.connItem` must record a reference row: {ranges:?}"
        );
        assert!(
            ranges.contains(&identifier),
            "property identifier `connItem` must record a reference row: {ranges:?}"
        );
        assert!(
            reference_ranges(&model, wrap).contains(&this_range),
            "`this` must reference Wrap on the assignment target"
        );
    }

    /// `classExtendingClass.symbols` renders, for `var r = d.foo;` with `foo`
    /// declared on base `C`:
    /// `>d.foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))`,
    /// `>foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))`.
    #[test]
    fn inherited_member_reference_resolves_to_base_symbol() {
        let text = "class C {\n    foo: string;\n    thing() { }\n    static other() { }\n}\n\nclass D extends C {\n    bar: string;\n}\n\nvar d: D;\nvar r = d.foo;\n";
        let (model, _) = bound(text);
        let (c_foo, c_foo_index) = symbol_by_qualified_name(&model, "C.foo");

        // `>foo : Symbol(C.foo, Decl(classExtendingClass.ts, 0, 9))`.
        let declaration = &model.symbols()[c_foo_index];
        assert_eq!(
            full_start(text, declaration.range().start().get()),
            (0, 9),
            "C.foo Decl anchors at the end of the class C header"
        );

        let line11 = text.split('\n').take(11).map(str::len).sum::<usize>() + 11;
        let path = (line11 + 8, line11 + 13);
        let identifier = (line11 + 10, line11 + 13);
        let ranges = reference_ranges(&model, c_foo);
        assert!(
            ranges.contains(&path),
            "`d.foo` must reference the base symbol C.foo: {ranges:?}"
        );
        assert!(
            ranges.contains(&identifier),
            "`foo` must reference the base symbol C.foo: {ranges:?}"
        );
    }

    /// `privateNameComputedPropertyName3(target=esnext).symbols` renders:
    /// `>#name : Symbol(Foo.#name, Decl(..., 0, 11))` at the declaration and,
    /// for `this.#name = name;`, the path-only rows
    /// `>this.#name : Symbol(Foo.#name, ...)` plus `>this : Symbol(Foo, ...)`
    /// — no bare `>#name` identifier row.
    #[test]
    fn private_names_bind_as_symbols_and_record_path_rows() {
        let text = "class Foo {\n    #name;\n    constructor(name) {\n        this.#name = name;\n    }\n}\n";
        let (model, _) = bound(text);
        let (hash_name, hash_name_index) = symbol_by_qualified_name(&model, "Foo.#name");
        let (foo, _) = symbol_by_qualified_name(&model, "Foo");

        // `>#name : Symbol(Foo.#name, Decl(..., 0, 11))`.
        let declaration = &model.symbols()[hash_name_index];
        assert_eq!(declaration.name(), "#name");
        assert_eq!(
            full_start(text, declaration.range().start().get()),
            (0, 11),
            "#name Decl anchors at the end of the class Foo header"
        );

        let line3 = text.split('\n').take(3).map(str::len).sum::<usize>() + 3;
        let path = (line3 + 8, line3 + 18);
        let bare_identifier = (line3 + 13, line3 + 18);
        let this_range = (line3 + 8, line3 + 12);
        let ranges = reference_ranges(&model, hash_name);
        assert!(
            ranges.contains(&path),
            "`this.#name` must record the whole-path reference row: {ranges:?}"
        );
        assert!(
            !ranges.contains(&bare_identifier),
            "private names render no bare `>#name` identifier row: {ranges:?}"
        );
        assert!(
            reference_ranges(&model, foo).contains(&this_range),
            "`this` must reference Foo on the private assignment target"
        );
    }

    /// `contextualTypingFunctionReturningFunction.symbols` renders bare
    /// parameter rows for signature parameters:
    /// `>s : Symbol(s, Decl(..., 1, 3))` on `a(s: string): void;` and
    /// `>n : Symbol(n, Decl(..., 2, 7))` for the `n` inside the return type
    /// `(n: number) => void` of `b(): (n: number) => void;`.
    #[test]
    fn interface_signature_parameters_bind_as_symbols() {
        let text = "interface I {\n\ta(s: string): void;\n\tb(): (n: number) => void;\n}\n";
        let (model, _) = bound(text);
        let (_, s_index) = symbol_by_qualified_name(&model, "s");
        let (_, n_index) = symbol_by_qualified_name(&model, "n");
        assert!(matches!(
            model.symbols()[s_index].kind(),
            SymbolKind::Parameter
        ));
        assert!(matches!(
            model.symbols()[n_index].kind(),
            SymbolKind::Parameter
        ));

        // `>s : Symbol(s, Decl(..., 1, 3))` — full-start at the end of `(`.
        assert_eq!(
            full_start(text, model.symbols()[s_index].range().start().get()),
            (1, 3),
            "parameter `s` Decl anchors at the end of `(`"
        );
        // `>n : Symbol(n, Decl(..., 2, 7))` — inside the return function type.
        assert_eq!(
            model.symbols()[n_index].range().start().get(),
            text.split('\n').take(2).map(str::len).sum::<usize>() + 2 + 7
        );
        assert_eq!(
            full_start(text, model.symbols()[n_index].range().start().get()),
            (2, 7),
            "parameter `n` Decl anchors at the end of `(` in the return type"
        );
    }
}
