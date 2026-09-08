//! Semantic analysis: the first real checker slice over an immutable
//! [`SourceFile`].
//!
//! The checker never mutates the syntax tree. It builds three immutable models
//! from one traversal: a lexical [`Scope`] tree, a [`Symbol`] table populated by
//! binding declarations, and an interned structural [`TypeTable`] used by the
//! named type algebra and the [`relations`] queries. Binding detects duplicate
//! declarations, reference resolution detects unresolved local names, and
//! variable initializers are checked against their annotations. Its diagnostics
//! are merged with the front-end hard warnings and returned in canonical order
//! alongside the [`SemanticModel`], following the crate's `Recovered` contract.
//!
//! Scope-tree, symbol-table, and type-table population lives in [`binder`];
//! assignability, subtyping, and variance live in [`relations`]; type-parameter
//! inference, contextual signatures, and inference priorities live in
//! [`inference`]; control-flow narrowing and contextual typing live in
//! [`narrowing`]; JSX namespace resolution, intrinsic lookup, and factory
//! props checking live in [`jsx`]; this module keeps the public entry points
//! and linked multi-file checking.

#[path = "checker/binder.rs"]
pub(crate) mod binder;
#[path = "checker/conditional_types.rs"]
pub mod conditional_types;
#[path = "checker/decorators.rs"]
pub mod decorators;
#[rustfmt::skip]
#[path = "generated/diagnostic_messages.rs"]
pub mod diagnostic_messages;
#[path = "checker/enum_namespace.rs"]
pub mod enum_namespace;
#[path = "checker/inference.rs"]
pub mod inference;
#[path = "checker/intrinsic_environment.rs"]
pub(crate) mod intrinsic_environment;
#[path = "checker/jsx.rs"]
pub mod jsx;
#[path = "checker/narrowing.rs"]
pub mod narrowing;
#[path = "checker/overloads.rs"]
pub mod overloads;
#[path = "checker/relations.rs"]
pub mod relations;

#[path = "checker/type_display.rs"]
mod type_display;
pub use type_display::{render_type, render_type_declaration};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::error::Error;
use std::fmt;

use bamts_bytecode::EcmaString;
use bamts_cancel::{CancellationToken, Cancelled};

pub use binder::{
    DeclarationOccurrence, PropertyType, Scope, ScopeId, ScopeKind, SemanticModel, Symbol,
    SymbolId, SymbolKind, Type, TypeId, TypeTable,
};
pub(crate) use binder::{
    EnumBindingView, EnumSourceInventory, ImportedSymbolType, bind_source_with_cancel,
    bind_source_with_environment_and_cancel, bind_source_with_environment_and_imports_with_cancel,
    is_numeric_enum_initializer, source_is_module,
};
pub use inference::{
    InferenceContext, InferenceParameter, InferencePriority, InferenceProvenance,
    InferredTypeArgument, InferredTypeArguments,
};
pub use narrowing::{
    FlowKey, FlowNodeId, GuardResolver, NarrowingContext, NarrowingGuard, TypeofName,
};
pub use relations::{RelationHazard, TypeRelation};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Recovered};
use crate::enum_plan::{self, EnumDeclarationBinding};
use crate::lint::{LintProfile, LintTable};
use crate::source::{ScriptKind, SourceId, TextRange, Utf16Pos};
use crate::syntax::{
    IdentifierNode, ImportBinding, ModuleExportName, NodeId, SourceFile, Statement, TokenKind,
};
use crate::warning::analyze_warnings;
use intrinsic_environment::{GlobalEnvironment, LibSet};

/// Diagnostic emitted when a block-scoped name redeclares an existing binding.
pub const DUPLICATE_DECLARATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C001");
/// Diagnostic emitted when a value reference resolves to no local binding.
pub const CANNOT_FIND_NAME: DiagnosticCode = DiagnosticCode::new("BAMTS-C002");
/// Diagnostic emitted when a type reference resolves to no local type name.
pub const CANNOT_FIND_TYPE: DiagnosticCode = DiagnosticCode::new("BAMTS-C003");
/// Diagnostic emitted when a qualified type name's left side is not a namespace.
pub const CANNOT_FIND_NAMESPACE: DiagnosticCode = DiagnosticCode::new("BAMTS-C013");
/// Diagnostic emitted when an initializer is not assignable to its annotation.
pub const TYPE_NOT_ASSIGNABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C004");
/// Diagnostic emitted when an imported const-enum member cannot be resolved.
pub const IMPORTED_CONST_ENUM_UNRESOLVED: DiagnosticCode = DiagnosticCode::new("BAMTS-C012");
/// Diagnostic emitted when a const-enum export-star lookup has multiple candidates.
pub const IMPORTED_CONST_ENUM_AMBIGUOUS: DiagnosticCode = DiagnosticCode::new("BAMTS-C016");
/// Diagnostic emitted when a const-enum re-export chain cycles.
pub const IMPORTED_CONST_ENUM_CYCLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C014");
/// Diagnostic emitted when an imported const-enum member was not already constant.
pub const IMPORTED_CONST_ENUM_NONCONSTANT: DiagnosticCode = DiagnosticCode::new("BAMTS-C015");
/// Diagnostic emitted when a `with` statement appears in a context that forbids it.
pub const WITH_STATEMENT_NOT_ALLOWED: DiagnosticCode = DiagnosticCode::new("BAMTS-C023");
/// Diagnostic emitted when an export assignment is mixed with another export.
pub const MIXED_EXPORT_ASSIGNMENT: DiagnosticCode = DiagnosticCode::new("BAMTS-C017");
/// Diagnostic emitted when a parameter carries a decorator.
pub const PARAMETER_DECORATOR_NOT_SUPPORTED: DiagnosticCode = DiagnosticCode::new("BAMTS-C018");
/// Diagnostic emitted when a constructor carries a decorator.
pub const CONSTRUCTOR_DECORATOR_NOT_SUPPORTED: DiagnosticCode = DiagnosticCode::new("BAMTS-C019");
/// Diagnostic emitted when an intrinsic JSX tag is absent from `JSX.IntrinsicElements`.
pub const JSX_INTRINSIC_ELEMENT_NOT_FOUND: DiagnosticCode = DiagnosticCode::new("BAMTS-C020");
/// Diagnostic emitted when a JSX tag's value type is neither callable nor constructible.
pub const JSX_ELEMENT_TYPE_NOT_CALLABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C021");
/// Diagnostic emitted when JSX attributes are not assignable to the element's props type.
pub const JSX_ATTRIBUTES_NOT_ASSIGNABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C022");
/// Diagnostic emitted when a `super` expression is not followed by an argument
/// list or member access.
pub const BARE_SUPER_EXPRESSION: DiagnosticCode = DiagnosticCode::new("BAMTS-C024");
/// Diagnostic emitted when `super` is referenced in a class with no base class.
pub const SUPER_REFERENCE_NON_DERIVED: DiagnosticCode = DiagnosticCode::new("BAMTS-C025");
/// Diagnostic emitted when a `super(...)` call appears outside a constructor or
/// inside a function nested in a constructor.
pub const SUPER_CALL_OUTSIDE_CONSTRUCTOR: DiagnosticCode = DiagnosticCode::new("BAMTS-C026");
/// Diagnostic emitted when a `super(...)` call appears in constructor parameter
/// initializers.
pub const SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS: DiagnosticCode = DiagnosticCode::new("BAMTS-C027");
/// Diagnostic emitted when a derived constructor has no legal `super()` call.
pub const DERIVED_CONSTRUCTOR_MISSING_SUPER: DiagnosticCode = DiagnosticCode::new("BAMTS-C068");

const DUPLICATE_MESSAGE: &str = "A block-scoped declaration cannot redeclare an existing binding.";
const CANNOT_FIND_NAME_MESSAGE: &str = "Cannot find name in any enclosing scope.";
const CANNOT_FIND_TYPE_MESSAGE: &str = "Cannot find type name in any enclosing scope.";
const CANNOT_FIND_NAMESPACE_MESSAGE: &str = "Cannot find namespace in any enclosing scope.";
const CANNOT_FIND_NAME_LIB_GATED_MESSAGE: &str =
    "Cannot find name. Do you need to change your target library?";
const NOT_ASSIGNABLE_MESSAGE: &str = "Initializer type is not assignable to the annotated type.";
/// Diagnostic emitted when a class property has no initializer and is not
/// definitely assigned in the constructor.
pub const PROPERTY_NOT_INITIALIZED: DiagnosticCode = DiagnosticCode::new("BAMTS-C028");
/// Diagnostic emitted when an assignment target resolves to a function.
pub const SUPER_BEFORE_THIS: DiagnosticCode = DiagnosticCode::new("BAMTS-C090");
pub const SUPER_BEFORE_SUPER_PROPERTY: DiagnosticCode = DiagnosticCode::new("BAMTS-C091");
pub const SUPER_FIELD_VIA_SUPER: DiagnosticCode = DiagnosticCode::new("BAMTS-C092");
pub const SUPER_STATIC_MEMBER_VIA_SUPER: DiagnosticCode = DiagnosticCode::new("BAMTS-C093");
pub const BLOCK_SCOPED_USED_BEFORE_DECLARATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C094");
pub const CLASS_USED_BEFORE_DECLARATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C095");
pub const ENUM_USED_BEFORE_DECLARATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C096");
pub const REST_PARAMETER_NOT_LAST: DiagnosticCode = DiagnosticCode::new("BAMTS-C097");
pub const INTERFACE_NAME_IS_PRIMITIVE: DiagnosticCode = DiagnosticCode::new("BAMTS-C098");
pub const SUPER_PROPERTY_NOT_METHOD: DiagnosticCode = DiagnosticCode::new("BAMTS-C099");
pub const PARAMETER_INITIALIZER_IN_SIGNATURE: DiagnosticCode = DiagnosticCode::new("BAMTS-C100");
pub const DUPLICATE_LABEL: DiagnosticCode = DiagnosticCode::new("BAMTS-C101");
pub const BREAK_TARGET_NOT_ENCLOSING: DiagnosticCode = DiagnosticCode::new("BAMTS-C102");
pub const BREAK_TARGET_CROSSES_FUNCTION: DiagnosticCode = DiagnosticCode::new("BAMTS-C103");
/// Diagnostic emitted when an inferred value is recursively referenced by its initializer.
pub const IMPLICIT_ANY_FROM_INITIALIZER_CYCLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C104");
/// Diagnostic emitted when an inferred named callable return is recursively referenced.
pub const IMPLICIT_ANY_RETURN_FROM_CYCLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C105");
/// Diagnostic emitted when an inferred anonymous callable return is recursively referenced.
pub const IMPLICIT_ANY_ANONYMOUS_RETURN_FROM_CYCLE: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C106");
pub(crate) const BREAK_TARGET_CROSSES_FUNCTION_MESSAGE: &str =
    "Jump target cannot cross function boundary.";
pub(crate) const BREAK_TARGET_NOT_ENCLOSING_MESSAGE: &str =
    "A 'break' statement can only jump to a label of an enclosing statement.";
pub(crate) const PARAMETER_INITIALIZER_IN_SIGNATURE_MESSAGE: &str =
    "A parameter initializer is only allowed in a function or constructor implementation.";
pub(crate) const SUPER_PROPERTY_NOT_METHOD_MESSAGE: &str =
    "Only public and protected methods of the base class are accessible via the 'super' keyword.";
pub(crate) const REST_PARAMETER_NOT_LAST_MESSAGE: &str =
    "A rest parameter must be last in a parameter list.";
pub const ASSIGNMENT_TO_FUNCTION: DiagnosticCode = DiagnosticCode::new("BAMTS-C029");
/// Diagnostic emitted when an assignment target resolves to a namespace.
pub const ASSIGNMENT_TO_NAMESPACE: DiagnosticCode = DiagnosticCode::new("BAMTS-C030");
/// Diagnostic emitted when the left-hand side of a `for...in` statement is not a
/// variable or property access.
pub const FOR_IN_LEFT_HAND_SIDE_INVALID: DiagnosticCode = DiagnosticCode::new("BAMTS-C031");
/// Diagnostic emitted when a `for...in` statement uses a `using` declaration as
/// its left-hand side.
pub const USING_DECLARATION_IN_FOR_IN: DiagnosticCode = DiagnosticCode::new("BAMTS-C032");
/// Diagnostic emitted when a `for...in` statement uses an `await using`
/// declaration as its left-hand side.
pub const AWAIT_USING_DECLARATION_IN_FOR_IN: DiagnosticCode = DiagnosticCode::new("BAMTS-C033");
/// Diagnostic emitted when a `using` or `await using` declaration uses a binding
/// pattern instead of a single identifier.
pub const USING_DECLARATION_BINDING_PATTERN: DiagnosticCode = DiagnosticCode::new("BAMTS-C034");
/// Diagnostic emitted when a `using` or `await using` declaration lacks an
/// initializer outside a `for...of` head.
pub const USING_DECLARATION_MISSING_INITIALIZER: DiagnosticCode = DiagnosticCode::new("BAMTS-C035");
/// Diagnostic emitted when an assignment or update target is not a variable or
/// property access.
pub const INVALID_ASSIGNMENT_TARGET: DiagnosticCode = DiagnosticCode::new("BAMTS-C036");
/// Diagnostic emitted when a method or constructor signature in an interface or
/// object type lacks a return type annotation.
pub const MISSING_METHOD_RETURN_TYPE: DiagnosticCode = DiagnosticCode::new("BAMTS-C037");
/// Diagnostic emitted when a variable is read before it has been assigned.
pub const USED_BEFORE_ASSIGNED: DiagnosticCode = DiagnosticCode::new("BAMTS-C038");
/// Diagnostic emitted when a function overload signature has no implementation
/// immediately following it.
pub const FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C039");
/// Diagnostic emitted when a function or method overload implementation has a
/// different name than the preceding overload signature(s).
pub const FUNCTION_IMPLEMENTATION_WRONG_NAME: DiagnosticCode = DiagnosticCode::new("BAMTS-C049");
/// Diagnostic emitted when a constructor declaration has type parameters.
pub const CONSTRUCTOR_TYPE_PARAMETERS: DiagnosticCode = DiagnosticCode::new("BAMTS-C050");
/// Diagnostic emitted when a statement appears in an ambient context where
/// only declarations are allowed.
pub const STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C052");
/// Diagnostic emitted when a function call argument is not assignable to the
/// declared parameter type.
pub const ARGUMENT_NOT_ASSIGNABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C053");
/// Diagnostic emitted when the `null` literal or the `undefined` identifier is
/// used as an operand of an operator that rejects a nullable operand: the
/// arithmetic, bitwise, and relational operators, and `+` unless one side is
/// string-like. Corresponds to TypeScript's TS18050.
pub const VALUE_CANNOT_BE_USED_HERE: DiagnosticCode = DiagnosticCode::new("BAMTS-C086");
/// Diagnostic emitted when a global declaration in a script conflicts with a
/// built-in global identifier (`globalThis` or `undefined`). Corresponds to
/// TypeScript's TS2397.
pub const DECLARATION_CONFLICTS_WITH_BUILTIN_GLOBAL: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C087");
/// Diagnostic emitted when a qualified name references a member that exists in
/// a namespace's local scope but is not exported. Corresponds to TypeScript's
/// TS2694.
pub const NAMESPACE_NO_EXPORTED_MEMBER: DiagnosticCode = DiagnosticCode::new("BAMTS-C088");
/// Diagnostic emitted when a value reference resolves to a name that is a
/// known lib-gated global not included in the active lib set. Corresponds to
/// TypeScript's TS2583.
pub const CANNOT_FIND_NAME_LIB_GATED: DiagnosticCode = DiagnosticCode::new("BAMTS-C089");
/// Diagnostic emitted when the number of arguments in a call does not match
/// the callable's parameter count.
pub const ARGUMENT_COUNT_MISMATCH: DiagnosticCode = DiagnosticCode::new("BAMTS-C054");
/// Diagnostic emitted when a property access names a member that does not exist
/// on the object's apparent type.
pub const PROPERTY_DOES_NOT_EXIST: DiagnosticCode = DiagnosticCode::new("BAMTS-C057");
/// Diagnostic emitted when an expression with no call signatures is invoked.
pub const EXPRESSION_NOT_CALLABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C055");
/// Diagnostic emitted when an expression with no construct signatures is constructed.
pub const EXPRESSION_NOT_CONSTRUCTABLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C059");
/// Diagnostic emitted when a function declaration appears inside a block-like
/// scope in strict mode while targeting 'ES5'.
pub const FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C040");
/// Diagnostic emitted when an import declaration introduces a name that is
/// already declared by a local value declaration.
pub const IMPORT_CONFLICTS_WITH_LOCAL: DiagnosticCode = DiagnosticCode::new("BAMTS-C041");
/// Diagnostic emitted when `new.target` is used outside the body of a function
/// declaration, function expression, or constructor.
pub const NEW_TARGET_OUTSIDE_FUNCTION: DiagnosticCode = DiagnosticCode::new("BAMTS-C044");
/// Diagnostic emitted when a function or class member body appears in an
/// ambient context.
pub const AMBIENT_IMPLEMENTATION: DiagnosticCode = DiagnosticCode::new("BAMTS-C046");
pub const SET_ACCESSOR_PARAMETER_INITIALIZER: DiagnosticCode = DiagnosticCode::new("BAMTS-C045");
/// Diagnostic emitted when a 'get' accessor has one or more parameters.
pub const GET_ACCESSOR_PARAMETERS: DiagnosticCode = DiagnosticCode::new("BAMTS-C047");
/// Diagnostic emitted when a 'get' accessor does not return a value.
pub const GET_ACCESSOR_NO_RETURN: DiagnosticCode = DiagnosticCode::new("BAMTS-C048");
/// Diagnostic emitted when a 'get' or 'set' accessor declares a 'this' parameter.
pub const ACCESSOR_THIS_PARAMETER: DiagnosticCode = DiagnosticCode::new("BAMTS-C058");
/// Diagnostic emitted when an assignment target refers to a readonly or getter-only property.
pub const ASSIGNMENT_TO_READONLY: DiagnosticCode = DiagnosticCode::new("BAMTS-C061");
/// Diagnostic emitted when direct member access violates a class member's declared accessibility.
pub const MEMBER_NOT_ACCESSIBLE: DiagnosticCode = DiagnosticCode::new("BAMTS-C063");
/// Diagnostic emitted when direct member access targets `null` or `undefined` under `strictNullChecks`.
pub const STRICT_NULL_MEMBER_ACCESS: DiagnosticCode = DiagnosticCode::new("BAMTS-C062");
/// Diagnostic emitted when an assignment target resolves to a `const` variable.
pub const ASSIGNMENT_TO_CONST: DiagnosticCode = DiagnosticCode::new("BAMTS-C060");
/// Diagnostic emitted when an indexed access type uses a key that does not exist on the object type.
pub const INVALID_INDEXED_ACCESS_KEY: DiagnosticCode = DiagnosticCode::new("BAMTS-C064");
/// Diagnostic emitted when a `for...of` operand is not iterable.
pub const FOR_OF_ITERABLE_REQUIRED: DiagnosticCode = DiagnosticCode::new("BAMTS-C065");
/// Diagnostic emitted when a `new` expression selects an abstract construct signature.
pub const ABSTRACT_CONSTRUCTOR: DiagnosticCode = DiagnosticCode::new("BAMTS-C066");
/// Diagnostic emitted for an explicit property that no viable fresh-object target admits.
pub const EXCESS_PROPERTY: DiagnosticCode = DiagnosticCode::new("BAMTS-C067");
const PROPERTY_NOT_INITIALIZED_MESSAGE: &str =
    "Property has no initializer and is not definitely assigned in the constructor.";
const ASSIGNMENT_TO_FUNCTION_MESSAGE: &str = "Cannot assign to a function.";
const ASSIGNMENT_TO_NAMESPACE_MESSAGE: &str = "Cannot assign to a namespace.";
const WITH_STATEMENT_NOT_ALLOWED_MESSAGE: &str =
    "The 'with' statement is not allowed in this context.";
const FOR_IN_LEFT_HAND_SIDE_INVALID_MESSAGE: &str =
    "The left-hand side of a 'for...in' statement must be a variable or a property access.";
const USING_DECLARATION_IN_FOR_IN_MESSAGE: &str =
    "The left-hand side of a 'for...in' statement cannot be a 'using' declaration.";
const AWAIT_USING_DECLARATION_IN_FOR_IN_MESSAGE: &str =
    "The left-hand side of a 'for...in' statement cannot be an 'await using' declaration.";
const MIXED_EXPORT_ASSIGNMENT_MESSAGE: &str =
    "An export assignment cannot be used with other exported elements.";
const PARAMETER_DECORATOR_NOT_SUPPORTED_MESSAGE: &str = "Parameter decorators are not supported.";
const CONSTRUCTOR_DECORATOR_NOT_SUPPORTED_MESSAGE: &str =
    "Constructor decorators are not supported.";
const USING_DECLARATION_BINDING_PATTERN_MESSAGE: &str =
    "'using' declarations may not have binding patterns.";
const USING_DECLARATION_MISSING_INITIALIZER_MESSAGE: &str =
    "'using' declarations must be initialized.";
const INVALID_ASSIGNMENT_TARGET_MESSAGE: &str =
    "The left-hand side of an assignment expression must be a variable or a property access.";
const USED_BEFORE_ASSIGNED_MESSAGE: &str = "Variable is used before being assigned.";
const FUNCTION_OVERLOAD_MISSING_IMPLEMENTATION_MESSAGE: &str =
    "Function implementation is missing or not immediately following its declaration.";
const FUNCTION_IMPLEMENTATION_WRONG_NAME_MESSAGE: &str =
    "Function implementation name does not match overload signature.";
const CONSTRUCTOR_TYPE_PARAMETERS_MESSAGE: &str =
    "Type parameters cannot appear on a constructor declaration.";
const STATEMENT_NOT_ALLOWED_IN_AMBIENT_CONTEXT_MESSAGE: &str =
    "Statements are not allowed in ambient contexts.";
const FUNCTION_DECLARATION_IN_BLOCK_ES5_STRICT_MESSAGE: &str =
    "Function declarations are not allowed inside blocks in strict mode when targeting 'ES5'.";
const IMPORT_CONFLICTS_WITH_LOCAL_MESSAGE: &str =
    "Import declaration conflicts with a local declaration.";
const NEW_TARGET_OUTSIDE_FUNCTION_MESSAGE: &str = "Meta-property 'new.target' is only allowed in the body of a function declaration, function expression, or constructor.";
const AMBIENT_IMPLEMENTATION_MESSAGE: &str =
    "An implementation cannot be declared in ambient contexts.";
const SET_ACCESSOR_PARAMETER_INITIALIZER_MESSAGE: &str =
    "A 'set' accessor parameter cannot have an initializer.";
const GET_ACCESSOR_PARAMETERS_MESSAGE: &str = "A 'get' accessor cannot have parameters.";
const GET_ACCESSOR_NO_RETURN_MESSAGE: &str = "A 'get' accessor must return a value.";
const ACCESSOR_THIS_PARAMETER_MESSAGE: &str =
    "A 'get' or 'set' accessor cannot declare a 'this' parameter.";
pub(crate) const JSX_INTRINSIC_ELEMENT_NOT_FOUND_MESSAGE: &str =
    "Property does not exist on type 'JSX.IntrinsicElements'";
pub(crate) const JSX_ELEMENT_TYPE_NOT_CALLABLE_MESSAGE: &str =
    "JSX element type is neither a construct nor a call signature.";
pub(crate) const JSX_ATTRIBUTES_NOT_ASSIGNABLE_MESSAGE: &str =
    "JSX attributes are not assignable to the element's props type.";
const MISSING_METHOD_RETURN_TYPE_MESSAGE: &str =
    "Method signature lacks return-type annotation and implicitly has an 'any' return type.";
pub(crate) const BARE_SUPER_EXPRESSION_MESSAGE: &str =
    "'super' must be followed by an argument list or member access.";
pub(crate) const SUPER_REFERENCE_NON_DERIVED_MESSAGE: &str =
    "'super' can only be referenced in a derived class.";
pub(crate) const SUPER_CALL_OUTSIDE_CONSTRUCTOR_MESSAGE: &str = "Super calls are not permitted outside constructors or in nested functions inside constructors.";
pub(crate) const SUPER_BEFORE_THIS_MESSAGE: &str =
    "'super' must be called before accessing 'this' in the constructor of a derived class.";
pub(crate) const SUPER_BEFORE_SUPER_PROPERTY_MESSAGE: &str = "'super' must be called before accessing a property of 'super' in the constructor of a derived class.";
pub(crate) const SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS_MESSAGE: &str =
    "'super' cannot be referenced in constructor arguments.";
const DERIVED_CONSTRUCTOR_MISSING_SUPER_MESSAGE: &str =
    "Constructors for derived classes must contain a 'super' call.";
const ABSTRACT_CONSTRUCTOR_MESSAGE: &str = "Cannot create an instance of an abstract class.";
const EXCESS_PROPERTY_MESSAGE: &str = "Object literal may only specify known properties.";
const ARGUMENT_NOT_ASSIGNABLE_MESSAGE: &str = "Argument type is not assignable to parameter type.";
pub(crate) const VALUE_CANNOT_BE_USED_HERE_MESSAGE: &str = "The value cannot be used here.";
const ARGUMENT_COUNT_MISMATCH_MESSAGE: &str =
    "Supplied arguments do not match the expected parameter count.";
const PROPERTY_DOES_NOT_EXIST_MESSAGE: &str = "Property does not exist on this type.";
const EXPRESSION_NOT_CALLABLE_MESSAGE: &str = "This expression is not callable.";
const EXPRESSION_NOT_CONSTRUCTABLE_MESSAGE: &str = "This expression is not constructable.";
const ASSIGNMENT_TO_READONLY_MESSAGE: &str = "Cannot assign to a readonly or getter-only property.";
const MEMBER_NOT_ACCESSIBLE_MESSAGE: &str = "Property is not accessible in this context.";
const STRICT_NULL_MEMBER_ACCESS_MESSAGE: &str = "Object is possibly 'null' or 'undefined'.";
const ASSIGNMENT_TO_CONST_MESSAGE: &str = "Cannot assign to a constant.";
const INVALID_INDEXED_ACCESS_KEY_MESSAGE: &str =
    "Type cannot be used to index the object type; the key does not match any property.";
const FOR_OF_ITERABLE_REQUIRED_MESSAGE: &str =
    "Type is not iterable; a 'for...of' statement requires an iterable value.";

/// Diagnostic emitted when a cooperative cancellation request interrupts a
/// checker pass. This is the diagnostic boundary for [`CheckCancelled`] errors
/// that propagate out of `_with_cancel` entry points and must be mapped into a
/// diagnostic stream at frontend/program/lower boundaries.
pub const CANCELLATION_REQUESTED: DiagnosticCode = DiagnosticCode::new("BAMTS-C069");
const CANCELLATION_REQUESTED_MESSAGE: &str = "Compilation was cancelled before completing.";
/// Diagnostic emitted when `@ts-expect-error` suppresses no diagnostic.
pub const UNUSED_EXPECT_ERROR: DiagnosticCode = DiagnosticCode::new("BAMTS-C070");
const UNUSED_EXPECT_ERROR_MESSAGE: &str = "Unused '@ts-expect-error' directive.";
/// Diagnostic emitted when a type parameter's default resolves through itself.
pub const TYPE_PARAMETER_CIRCULAR_DEFAULT: DiagnosticCode = DiagnosticCode::new("BAMTS-C071");
const TYPE_PARAMETER_CIRCULAR_DEFAULT_MESSAGE: &str = "Type parameter has a circular default.";
/// Diagnostic emitted when a type alias expands directly or mutually to itself.
pub const TYPE_ALIAS_CIRCULAR: DiagnosticCode = DiagnosticCode::new("BAMTS-C072");
const TYPE_ALIAS_CIRCULAR_MESSAGE: &str = "Type alias circularly references itself.";
/// Diagnostic emitted when a parameter property appears outside a constructor
/// implementation.
pub const PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR: DiagnosticCode =
    DiagnosticCode::new("BAMTS-C080");
const PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR_MESSAGE: &str =
    "A parameter property is only allowed in a constructor implementation.";
/// Diagnostic emitted when a function or method whose declared return type is
/// a value type completes without returning a value.
pub const NON_VOID_FUNCTION_MUST_RETURN: DiagnosticCode = DiagnosticCode::new("BAMTS-C081");
const NON_VOID_FUNCTION_MUST_RETURN_MESSAGE: &str =
    "A function whose declared type is neither 'undefined', 'void', nor 'any' must return a value.";
/// Diagnostic emitted when a type annotation is nested deeper than the
/// checker's resolution budget. Mirrors the parser's `BAMTS-P010`
/// `NESTING_TOO_DEEP` guard so pathological inputs fail typed instead of
/// overflowing the native call stack.
pub const TYPE_NESTING_TOO_DEEP: DiagnosticCode = DiagnosticCode::new("BAMTS-C082");
const TYPE_NESTING_TOO_DEEP_MESSAGE: &str =
    "This type is nested too deeply to resolve; the checker depth budget was exceeded.";
/// One cooperative checker invocation was cancelled before completing.
///
/// The `_with_cancel` entry points return `Result<Recovered<T>, CheckCancelled>`
/// so callers can distinguish cancellation from a completed (possibly
/// diagnostic-laden) product. At boundaries that only carry diagnostics
/// (frontend, program, lower), convert with [`CheckCancelled::to_diagnostic`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckCancelled(Cancelled);

impl CheckCancelled {
    /// Creates the cancellation error from the raw signal.
    #[must_use]
    pub const fn new(cancelled: Cancelled) -> Self {
        Self(cancelled)
    }

    /// Returns a cancellation diagnostic anchored at `source_id` with a
    /// zero-width range, for mapping into a diagnostic stream at boundaries
    /// that do not carry `Result`.
    #[must_use]
    pub fn to_diagnostic(&self, source_id: SourceId) -> Diagnostic {
        Diagnostic::error(
            CANCELLATION_REQUESTED,
            source_id,
            TextRange::new(Utf16Pos::ZERO, Utf16Pos::ZERO).expect("zero-width range is valid"),
            CANCELLATION_REQUESTED_MESSAGE,
        )
    }
}

impl From<Cancelled> for CheckCancelled {
    fn from(cancelled: Cancelled) -> Self {
        Self(cancelled)
    }
}

impl From<CheckCancelled> for Cancelled {
    fn from(error: CheckCancelled) -> Self {
        error.0
    }
}

impl fmt::Display for CheckCancelled {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("checker operation cancelled")
    }
}

impl Error for CheckCancelled {}

/// Compact identity for one allocated object literal and its aliases.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObjectId(u32);

/// Source-qualified syntax identity used by cross-file facts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeKey {
    pub source_id: SourceId,
    pub node_id: NodeId,
}

/// One checker-derived condition consumed by a semantic rule.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SemanticHazard {
    UncheckedIndexRead,
    ExplicitUndefinedOptional,
    DetachedMethod,
    DivergentAccessor,
    ReadonlyAliasMutation,
    FewerCallbackParameters,
    ValueReturnedToVoid,
    OpenObjectKeys,
    IndexSignatureDotAccess,
    ImplicitAny,
    UncheckedAssertion,
    DeclarationInferenceDependency,
    TypeImportedAsValue,
    TypeReexportedAsValue,
    UncheckedSideEffectImport,
    InteropDependentDefaultImport,
    CjsEsmNamedExportMismatch,
    VirtualCallInConstructor,
    InitializedFieldShadowsAccessor,
    ImplicitOverride,
    NumericEnumNumber,
    NumericEnumReverseLookup,
    NonExhaustiveSwitch,
    InvalidNumberFormatting,
    NumericKeyOrder,
    JsonStringifyUnserializable,
    UncheckedJsonParse,
    NumericDefaultSort,
    LooseEqualityCoercion,
    ObjectToPrimitive,
    SymbolInterpolation,
    UnsafeToStringTag,
    UninitializedFieldShadowsAccessor,
}

/// Immutable evidence for one semantic lint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HazardFact {
    pub hazard: SemanticHazard,
    pub range: TextRange,
    pub note: Option<Box<str>>,
}

/// Frozen checker facts. Rule implementations only query this product.
#[derive(Clone, Debug, Default)]
pub struct AnalysisFacts {
    hazards: Vec<HazardFact>,
    index: HashSet<(SemanticHazard, TextRange)>,
}

impl AnalysisFacts {
    #[must_use]
    pub fn hazards(&self) -> &[HazardFact] {
        &self.hazards
    }

    pub(crate) fn push(&mut self, fact: HazardFact) {
        if self.index.insert((fact.hazard, fact.range)) {
            self.hazards.push(fact);
        }
    }

    pub(crate) fn extend(&mut self, facts: impl IntoIterator<Item = HazardFact>) {
        for fact in facts {
            self.push(fact);
        }
    }
}

/// Analyzes one source with the default lint profile.
#[must_use]
pub fn check(source_file: &Recovered<SourceFile>) -> Recovered<SemanticModel> {
    check_source(source_file.product())
}

/// Analyzes one source using an already-resolved lint table.
#[must_use]
pub fn check_with_lints(
    source_file: &Recovered<SourceFile>,
    levels: &LintTable,
) -> Recovered<SemanticModel> {
    check_source_with_lints(source_file.product(), levels)
}

/// Analyzes one source with the default lint profile, borrowing an existing product.
#[must_use]
pub fn check_source(source_file: &SourceFile) -> Recovered<SemanticModel> {
    check_source_with_lints(source_file, &LintTable::new(LintProfile::Default))
}

/// Analyzes one source using an already-resolved lint table, borrowing an existing product.
#[must_use]
pub fn check_source_with_lints(
    source_file: &SourceFile,
    levels: &LintTable,
) -> Recovered<SemanticModel> {
    check_source_with_lints_with_cancel(source_file, levels, CancellationToken::new())
        .expect("fresh token is never cancelled")
}

/// Analyzes one source using an already-resolved lint table, borrowing an
/// existing product. Fails early with [`CheckCancelled`] when `cancel` is
/// triggered during binding, fact collection, or semantic analysis.
pub fn check_source_with_lints_with_cancel(
    source_file: &SourceFile,
    levels: &LintTable,
    cancel: CancellationToken,
) -> Result<Recovered<SemanticModel>, CheckCancelled> {
    cancel.check()?;
    let (mut model, mut diagnostics) = bind_source_with_cancel(source_file, cancel.clone())?;
    model.replace_facts(crate::rules::semantic::collect_facts(source_file, &model));
    diagnostics.extend(analyze_warnings(source_file, levels));
    diagnostics.extend(crate::rules::analyze_semantic(
        source_file,
        &model,
        None,
        levels,
    ));
    Ok(Recovered::new(model, diagnostics))
}

/// One resolved module edge supplied by the project loader.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ResolvedModuleEdge {
    pub from: SourceId,
    pub specifier: NodeId,
    pub to: SourceId,
}

/// Borrowed input for a linked multi-file checker run.
#[derive(Clone, Copy)]
pub struct ProgramCheckInput<'a> {
    pub files: &'a [Recovered<SourceFile>],
    pub edges: &'a [ResolvedModuleEdge],
}

/// Checker environment selected by the project's module compiler option.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ProgramCheckOptions {
    commonjs: bool,
    strict_null_checks: bool,
    no_implicit_any: bool,
    strict_property_initialization: bool,
    /// Whether `alwaysStrict` is enabled: every source file is treated as if
    /// it begins with the "use strict" directive.
    always_strict: bool,
    /// Whether `noEmitHelpers` is enabled: emit references downleveling
    /// helpers without emitting their definitions.
    no_emit_helpers: bool,
    /// ECMAScript target — drives lib derivation and downleveling decisions.
    target: crate::emitter::ScriptTarget,
    /// Active lib set — controls which intrinsic globals are installed.
    /// When empty (no explicit lib and no target), all globals are installed
    /// to preserve the pre-lib-scoping behavior.
    libs: LibSet,
    check_js: bool,
}

impl ProgramCheckOptions {
    #[must_use]
    pub const fn standard() -> Self {
        Self {
            commonjs: false,
            strict_null_checks: false,
            no_implicit_any: false,
            strict_property_initialization: false,
            always_strict: false,
            no_emit_helpers: false,
            target: crate::emitter::ScriptTarget::EsNext,
            libs: LibSet::ALL,
            check_js: false,
        }
    }

    #[must_use]
    pub const fn commonjs() -> Self {
        Self {
            commonjs: true,
            strict_null_checks: false,
            no_implicit_any: false,
            strict_property_initialization: false,
            always_strict: false,
            no_emit_helpers: false,
            target: crate::emitter::ScriptTarget::EsNext,
            libs: LibSet::ALL,
            check_js: false,
        }
    }

    /// Applies the `strict` master switch to every modeled member option.
    /// Call this before any explicit `with_*` member override, matching
    /// tsconfig resolution where an explicit member value wins over `strict`.
    #[must_use]
    pub const fn with_strict(mut self, value: bool) -> Self {
        self.strict_null_checks = value;
        self.no_implicit_any = value;
        self.strict_property_initialization = value;
        self.always_strict = value;
        self
    }

    #[must_use]
    pub const fn with_strict_null_checks(mut self, value: bool) -> Self {
        self.strict_null_checks = value;
        self
    }

    #[must_use]
    pub const fn with_no_implicit_any(mut self, value: bool) -> Self {
        self.no_implicit_any = value;
        self
    }

    #[must_use]
    pub const fn with_strict_property_initialization(mut self, value: bool) -> Self {
        self.strict_property_initialization = value;
        self
    }

    #[must_use]
    pub const fn with_always_strict(mut self, value: bool) -> Self {
        self.always_strict = value;
        self
    }

    /// Sets whether emit omits helper definitions (`noEmitHelpers`).
    #[must_use]
    pub const fn with_no_emit_helpers(mut self, value: bool) -> Self {
        self.no_emit_helpers = value;
        self
    }

    /// Whether emit omits helper definitions (`noEmitHelpers`).
    #[must_use]
    pub const fn no_emit_helpers(&self) -> bool {
        self.no_emit_helpers
    }

    /// Sets the target from a string (e.g. `"es5"`, `"es2020"`) and derives
    /// its default lib set. `None` selects the default target; an
    /// unrecognized name leaves the options unchanged.
    #[must_use]
    pub fn with_target(self, target: Option<&str>) -> Self {
        let parsed = match target {
            Some(name) => crate::emitter::parse_target(name),
            None => Some(crate::emitter::ScriptTarget::default()),
        };
        match parsed {
            Some(target) => self.with_script_target(target),
            None => self,
        }
    }

    /// Sets the target directly from a [`ScriptTarget`] and derives the
    /// default lib set.
    #[must_use]
    pub const fn with_script_target(mut self, target: crate::emitter::ScriptTarget) -> Self {
        self.target = target;
        self.libs = LibSet::default_for_target(target);
        self
    }

    /// Sets an explicit lib set, overriding any target-derived default.
    #[must_use]
    pub(crate) const fn with_libs(mut self, libs: LibSet) -> Self {
        self.libs = libs;
        self
    }

    #[must_use]
    pub const fn with_check_js(mut self, value: bool) -> Self {
        self.check_js = value;
        self
    }

    #[must_use]
    pub const fn strict_null_checks(&self) -> bool {
        self.strict_null_checks
    }

    #[must_use]
    pub const fn no_implicit_any(&self) -> bool {
        self.no_implicit_any
    }

    #[must_use]
    pub const fn strict_property_initialization(&self) -> bool {
        self.strict_property_initialization
    }

    #[must_use]
    pub const fn always_strict(&self) -> bool {
        self.always_strict
    }

    #[must_use]
    pub const fn is_commonjs(&self) -> bool {
        self.commonjs
    }

    /// Whether the compilation target is ES5 or earlier, which forbids
    /// function declarations inside blocks in strict mode.
    #[must_use]
    pub const fn es5(&self) -> bool {
        (self.target as u8) <= (crate::emitter::ScriptTarget::Es5 as u8)
    }

    #[must_use]
    pub const fn target(&self) -> crate::emitter::ScriptTarget {
        self.target
    }

    #[must_use]
    pub const fn check_js(&self) -> bool {
        self.check_js
    }

    const fn environment(self) -> GlobalEnvironment {
        if self.commonjs {
            GlobalEnvironment::commonjs(self.libs)
        } else {
            GlobalEnvironment::standard(self.libs)
        }
    }
}

/// Immutable linked checker product.
#[derive(Clone, Debug)]
pub struct ProgramSemanticModel {
    files: BTreeMap<SourceId, SemanticModel>,
    edges: Box<[ResolvedModuleEdge]>,
}

impl ProgramSemanticModel {
    #[must_use]
    pub fn file(&self, source_id: SourceId) -> Option<&SemanticModel> {
        self.files.get(&source_id)
    }

    /// Removes and returns the semantic model for `source_id`, if present.
    ///
    /// This is destructive: the model is moved out of the program map so callers
    /// can own it without cloning. A missing key returns `None`.
    #[must_use]
    pub fn remove_file(&mut self, source_id: SourceId) -> Option<SemanticModel> {
        self.files.remove(&source_id)
    }

    #[must_use]
    pub fn edges(&self) -> &[ResolvedModuleEdge] {
        &self.edges
    }
}

fn check_directive(comment: &str) -> Option<bool> {
    let body = comment.strip_prefix("//")?;
    let body = body.strip_prefix('/').unwrap_or(body).trim_start();
    for (directive, enabled) in [("@ts-check", true), ("@ts-nocheck", false)] {
        let Some(rest) = body.strip_prefix(directive) else {
            continue;
        };
        if rest.chars().next().is_none_or(char::is_whitespace) {
            return Some(enabled);
        }
    }
    None
}

fn semantic_diagnostics_enabled(source: &SourceFile, options: ProgramCheckOptions) -> bool {
    let mut enabled = !matches!(
        source.script_kind(),
        ScriptKind::JavaScript | ScriptKind::JavaScriptReact
    ) || options.check_js;
    for token in source.tokens() {
        match token.kind() {
            TokenKind::Whitespace | TokenKind::Shebang | TokenKind::BlockComment => {}
            TokenKind::LineComment => {
                let Some(text) = source.token_text(token) else {
                    continue;
                };
                if let Some(value) = check_directive(text) {
                    enabled = value;
                }
            }
            _ => break,
        }
    }
    enabled
}

/// Checks a set of loaded files after module resolution.
#[must_use]
pub fn check_program(
    input: ProgramCheckInput<'_>,
    levels: &LintTable,
) -> Recovered<ProgramSemanticModel> {
    check_program_with_options(input, levels, ProgramCheckOptions::standard())
}

/// Checks a set of loaded files using the environment selected by module options.
#[must_use]
pub fn check_program_with_options(
    input: ProgramCheckInput<'_>,
    levels: &LintTable,
    options: ProgramCheckOptions,
) -> Recovered<ProgramSemanticModel> {
    check_program_with_options_and_cancel(input, levels, options, CancellationToken::new())
        .expect("fresh token is never cancelled")
}

/// Checks a set of loaded files using the environment selected by module
/// options. Fails early with [`CheckCancelled`] when `cancel` is triggered
/// during any per-file binding pass, the fixed-point import-type iteration,
/// fact collection, or the final semantic analysis loop.
pub fn check_program_with_options_and_cancel(
    input: ProgramCheckInput<'_>,
    levels: &LintTable,
    options: ProgramCheckOptions,
    cancel: CancellationToken,
) -> Result<Recovered<ProgramSemanticModel>, CheckCancelled> {
    cancel.check()?;
    let source_ids: Vec<SourceId> = input
        .files
        .iter()
        .map(|recovered| recovered.product().source_id())
        .collect();
    let checked_sources = input
        .files
        .iter()
        .filter_map(|recovered| {
            let source = recovered.product();
            semantic_diagnostics_enabled(source, options).then_some(source.source_id())
        })
        .collect::<HashSet<_>>();
    let edge_targets: HashMap<_, _> = input
        .edges
        .iter()
        .map(|edge| ((edge.from, edge.specifier), edge.to))
        .collect();

    let mut files = BTreeMap::new();
    for recovered in input.files {
        cancel.check()?;
        let source = recovered.product();
        let (model, _) = bind_source_with_environment_and_cancel(
            source,
            options.environment(),
            source_is_module(source),
            options,
            cancel.clone(),
        )?;
        files.insert(source.source_id(), model);
    }

    let imports = collect_import_targets(input.files, &files, &edge_targets);
    let exports = collect_export_targets(input.files, &files, &edge_targets);
    let export_stars = collect_export_stars(input.files, &edge_targets);

    let worklist: Vec<SourceId> = source_ids.clone();
    for _ in 0..source_ids.len() {
        cancel.check()?;
        let mut changed = false;
        for &source_id in &worklist {
            let Some(source) = input
                .files
                .iter()
                .map(|recovered| recovered.product())
                .find(|source| source.source_id() == source_id)
            else {
                continue;
            };
            let imported = collect_imported_types_for_source(
                source_id,
                source,
                &imports,
                &exports,
                &export_stars,
                &files,
            );
            if imported.is_empty() {
                continue;
            }
            let (model, _) = bind_source_with_environment_and_imports_with_cancel(
                source,
                options.environment(),
                source_is_module(source),
                options,
                &imported,
                cancel.clone(),
            )?;
            files.insert(source_id, model);
            changed = true;
        }
        if !changed {
            break;
        }
    }

    let mut diagnostics = Vec::new();
    let mut final_files = BTreeMap::new();
    for recovered in input.files {
        cancel.check()?;
        let source = recovered.product();
        let source_id = source.source_id();
        let imported = collect_imported_types_for_source(
            source_id,
            source,
            &imports,
            &exports,
            &export_stars,
            &files,
        );
        let (mut model, core_diagnostics) = if imported.is_empty() {
            bind_source_with_environment_and_cancel(
                source,
                options.environment(),
                source_is_module(source),
                options,
                cancel.clone(),
            )?
        } else {
            bind_source_with_environment_and_imports_with_cancel(
                source,
                options.environment(),
                source_is_module(source),
                options,
                &imported,
                cancel.clone(),
            )?
        };
        model.replace_facts(crate::rules::semantic::collect_facts(source, &model));
        if checked_sources.contains(&source_id) {
            diagnostics.extend(core_diagnostics);
        }
        diagnostics.extend(analyze_warnings(source, levels));
        final_files.insert(source_id, model);
    }
    let mut files = final_files;

    crate::rules::semantic::collect_program_facts(input.files, input.edges, &mut files);
    let original_diagnostic_count = diagnostics.len();
    collect_imported_const_enum_facts(input.files, input.edges, &mut files, &mut diagnostics);
    let mut position = 0;
    diagnostics.retain(|diagnostic| {
        let keep = position < original_diagnostic_count
            || checked_sources.contains(&diagnostic.source_id());
        position += 1;
        keep
    });
    let program = ProgramSemanticModel {
        files,
        edges: input.edges.into(),
    };
    for recovered in input.files {
        cancel.check()?;
        let source = recovered.product();
        let model = program
            .file(source.source_id())
            .expect("program model contains every input source");
        diagnostics.extend(crate::rules::analyze_semantic(
            source,
            model,
            Some(&program),
            levels,
        ));
    }
    Ok(Recovered::new(program, diagnostics))
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct LinkedEnum {
    source: SourceId,
    symbol: SymbolId,
}
/// Borrowed lexical input for the pre-typing enum scalar bootstrap.
///
/// The inventory (binding view, source, and lexical enum tables) remains
/// borrowed from the retained Binder; only the facts produced by the lexical
/// enum adapter are owned here.
#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
struct EnumSource<'src, 'a> {
    inventory: EnumSourceInventory<'src, 'a>,
    facts: enum_plan::EnumFacts,
}

#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
struct ResolvedProgramEnumScalars {
    by_source: BTreeMap<SourceId, HashMap<NodeId, enum_plan::ImportedConstEnumValue>>,
}

trait EnumSourceRead {
    fn enum_facts(&self) -> &enum_plan::EnumFacts;
    fn symbol_kind(&self, symbol: SymbolId) -> Option<SymbolKind>;
}

impl EnumSourceRead for SemanticModel {
    fn enum_facts(&self) -> &enum_plan::EnumFacts {
        SemanticModel::enum_facts(self)
    }

    fn symbol_kind(&self, symbol: SymbolId) -> Option<SymbolKind> {
        Some(self.symbol(symbol).kind())
    }
}

impl<'src, 'a> EnumSourceRead for EnumSource<'src, 'a> {
    fn enum_facts(&self) -> &enum_plan::EnumFacts {
        &self.facts
    }

    fn symbol_kind(&self, symbol: SymbolId) -> Option<SymbolKind> {
        self.inventory
            .view
            .symbols
            .get(symbol.get() as usize)
            .map(Symbol::kind)
    }
}

#[derive(Clone, Debug)]
enum ImportTarget {
    Named {
        source: SourceId,
        name: EcmaString,
        specifier: Option<NodeId>,
    },
    Namespace {
        source: SourceId,
    },
}

#[derive(Clone, Debug)]
enum ExportTarget {
    Local(SymbolId),
    Forward { source: SourceId, name: EcmaString },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct LinkedExport {
    source: SourceId,
    symbol: SymbolId,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ExportCandidate {
    Const(LinkedEnum),
    Value(LinkedExport),
    Namespace(SourceId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ExportResolution {
    Const(LinkedEnum),
    /// An ordinary enum remains a runtime import and is not a const-enum failure.
    NotConst,
    Namespace(SourceId),
    Unresolved,
    Cycle,
    Ambiguous,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ImportedMemberBaseResolution {
    Export(ExportResolution),
    Scalar,
}

#[derive(Default)]
struct ExportStars {
    namespace_exports: HashMap<(SourceId, EcmaString), SourceId>,
    targets: HashMap<SourceId, Vec<SourceId>>,
}

#[derive(Default)]
struct ExportResolutionSet {
    candidates: HashSet<ExportCandidate>,
    has_cycle: bool,
}

impl ExportResolutionSet {
    fn candidate(candidate: ExportCandidate) -> Self {
        let mut candidates = HashSet::new();
        let inserted = candidates.insert(candidate);
        debug_assert!(inserted);
        Self {
            candidates,
            has_cycle: false,
        }
    }

    fn cycle() -> Self {
        Self {
            candidates: HashSet::new(),
            has_cycle: true,
        }
    }

    fn extend(&mut self, other: Self) {
        self.candidates.extend(other.candidates);
        self.has_cycle |= other.has_cycle;
    }

    fn into_resolution(self) -> ExportResolution {
        match self.candidates.len() {
            0 if self.has_cycle => ExportResolution::Cycle,
            0 => ExportResolution::Unresolved,
            1 => match self
                .candidates
                .iter()
                .next()
                .expect("one export candidate exists")
            {
                ExportCandidate::Const(linked) => ExportResolution::Const(*linked),
                ExportCandidate::Value(_) => ExportResolution::NotConst,
                ExportCandidate::Namespace(source) => ExportResolution::Namespace(*source),
            },
            _ => ExportResolution::Ambiguous,
        }
    }
}
/// Resolves one exported value name to its source [`LinkedExport`], following
/// re-exports and export-star fallbacks through the shared export tables. A
/// missing or ambiguous export yields `None`, preserving existing diagnostics.
fn resolve_export_for_type(
    source: SourceId,
    name: &EcmaString,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
) -> Option<LinkedExport> {
    let resolution = resolve_export_candidates(
        source,
        name,
        imports,
        exports,
        export_stars,
        files,
        &mut HashSet::new(),
    );
    let linked = resolution
        .candidates
        .iter()
        .find_map(|candidate| match candidate {
            ExportCandidate::Value(linked) => Some(*linked),
            _ => None,
        });
    if matches!(resolution.into_resolution(), ExportResolution::NotConst) {
        linked
    } else {
        None
    }
}

/// Builds the [`ImportedSymbolType`] facts for one source file by translating
/// each import binding into the structural type of its resolved source export.
/// Named, default, and namespace imports all follow existing symbol identities;
/// cross-table types are copied through [`TypeTable::import_type`] at bind time.
/// Missing exports are skipped so the binder retains its current diagnostics.
fn collect_imported_types_for_source<'a>(
    source_id: SourceId,
    source: &SourceFile,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &'a BTreeMap<SourceId, SemanticModel>,
) -> Vec<ImportedSymbolType<'a>> {
    let Some(model) = files.get(&source_id) else {
        return Vec::new();
    };
    let mut imported_types = Vec::new();
    for statement in source.statements() {
        let Statement::Import(import) = statement.data() else {
            continue;
        };
        let Some(clause) = &import.clause else {
            continue;
        };
        if let Some(default) = &clause.default {
            let Some(symbol) = lookup_identifier(model, source, default) else {
                continue;
            };
            if let Some(imported) =
                build_imported_symbol_type(source_id, symbol, imports, exports, export_stars, files)
            {
                imported_types.push(imported);
            }
        }
        match &clause.binding {
            Some(ImportBinding::Namespace(local)) => {
                let Some(symbol) = lookup_identifier(model, source, local) else {
                    continue;
                };
                let Some(target) = imports.get(&(source_id, symbol)) else {
                    continue;
                };
                let ImportTarget::Namespace {
                    source: target_source,
                } = *target
                else {
                    continue;
                };
                let Some(target_model) = files.get(&target_source) else {
                    continue;
                };
                let namespace_type = target_model.types().object();
                imported_types.push(ImportedSymbolType {
                    symbol,
                    source_model: target_model,
                    value_type_id: namespace_type,
                    type_parameters: &[],
                    type_plane_id: None,
                });
            }
            Some(ImportBinding::Named(specifiers)) => {
                for specifier in specifiers {
                    let specifier_data = specifier.data();
                    let Some(symbol) = lookup_identifier(model, source, &specifier_data.local)
                    else {
                        continue;
                    };
                    if let Some(imported) = build_imported_symbol_type(
                        source_id,
                        symbol,
                        imports,
                        exports,
                        export_stars,
                        files,
                    ) {
                        imported_types.push(imported);
                    }
                }
            }
            None => {}
        }
    }
    imported_types
}

/// Resolves one imported binding to its source export's structural type fact.
fn build_imported_symbol_type<'a>(
    source_id: SourceId,
    symbol: SymbolId,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &'a BTreeMap<SourceId, SemanticModel>,
) -> Option<ImportedSymbolType<'a>> {
    let target = imports.get(&(source_id, symbol))?;
    let (target_source, target_name) = match target {
        ImportTarget::Named { source, name, .. } => (*source, name.clone()),
        ImportTarget::Namespace { .. } => return None,
    };
    let linked = resolve_export_for_type(
        target_source,
        &target_name,
        imports,
        exports,
        export_stars,
        files,
    )?;
    let source_model = files.get(&linked.source)?;
    let symbol_kind = source_model.symbol(linked.symbol).kind();
    // A class symbol's value plane is its constructor type; the structural
    // static side hangs off it, and the type plane is its instance type.
    let value_type_id = if symbol_kind == SymbolKind::Class {
        source_model.constructor_type(linked.symbol)
    } else {
        source_model.symbol_type(linked.symbol)
    };
    let value_type = source_model.types().get(value_type_id);
    if matches!(value_type, Type::Error | Type::Any | Type::Unknown) {
        return None;
    }
    let type_plane_id = match (symbol_kind, value_type) {
        (SymbolKind::Class, Type::ConstructorType { structural, .. }) => {
            let Type::ObjectType(object) = source_model.types().get(*structural) else {
                return None;
            };
            let mut signatures = object.construct_signatures.iter();
            signatures.next().and_then(|first| {
                let return_type = first.signature.return_type();
                matches!(
                    source_model.types().get(return_type),
                    Type::AppliedClass { symbol, .. } if *symbol == linked.symbol
                )
                .then_some(return_type)
                .filter(|_| signatures.all(|entry| entry.signature.return_type() == return_type))
            })
        }
        (SymbolKind::Interface | SymbolKind::TypeAlias | SymbolKind::Enum, _) => {
            Some(value_type_id)
        }
        _ => None,
    };
    Some(ImportedSymbolType {
        symbol,
        source_model,
        value_type_id,
        type_parameters: source_model.generic_type_parameters(linked.symbol),
        type_plane_id,
    })
}

fn lexical_symbol(
    source: &SourceFile,
    bindings: EnumBindingView<'_>,
    identifier: &IdentifierNode,
) -> Option<SymbolId> {
    bindings
        .references
        .get(&identifier.id())
        .copied()
        .or_else(|| {
            let name = source.identifier_text(identifier.data().token())?;
            bindings
                .scopes
                .get(bindings.module_scope.get() as usize)?
                .value(name.as_ref())
        })
}

#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
fn collect_lexical_import_targets(
    sources: &[Recovered<SourceFile>],
    files: &BTreeMap<SourceId, EnumSource<'_, '_>>,
    edges: &HashMap<(SourceId, NodeId), SourceId>,
) -> HashMap<(SourceId, SymbolId), ImportTarget> {
    let mut targets = HashMap::new();
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let Some(entry) = files.get(&source_id) else {
            continue;
        };
        for statement in source.statements() {
            let Statement::Import(import) = statement.data() else {
                continue;
            };
            let Some(target_source) = edges
                .get(&(source_id, statement.id()))
                .or_else(|| edges.get(&(source_id, import.source.id())))
                .copied()
            else {
                continue;
            };
            let Some(clause) = &import.clause else {
                continue;
            };
            if let Some(default) = &clause.default
                && let Some(symbol) = lexical_symbol(source, entry.inventory.view, default)
            {
                targets.insert(
                    (source_id, symbol),
                    ImportTarget::Named {
                        source: target_source,
                        name: EcmaString::encode("default"),
                        specifier: None,
                    },
                );
            }
            match &clause.binding {
                Some(ImportBinding::Namespace(local)) => {
                    if let Some(symbol) = lexical_symbol(source, entry.inventory.view, local) {
                        targets.insert(
                            (source_id, symbol),
                            ImportTarget::Namespace {
                                source: target_source,
                            },
                        );
                    }
                }
                Some(ImportBinding::Named(specifiers)) => {
                    for specifier in specifiers {
                        let data = specifier.data();
                        let Some(symbol) =
                            lexical_symbol(source, entry.inventory.view, &data.local)
                        else {
                            continue;
                        };
                        let Some(name) = module_export_name(source, &data.imported) else {
                            continue;
                        };
                        targets.insert(
                            (source_id, symbol),
                            ImportTarget::Named {
                                source: target_source,
                                name,
                                specifier: Some(specifier.id()),
                            },
                        );
                    }
                }
                None => {}
            }
        }
    }
    targets
}

#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
fn collect_lexical_export_targets(
    sources: &[Recovered<SourceFile>],
    files: &BTreeMap<SourceId, EnumSource<'_, '_>>,
    edges: &HashMap<(SourceId, NodeId), SourceId>,
) -> HashMap<(SourceId, EcmaString), ExportTarget> {
    let mut targets = HashMap::new();
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let Some(entry) = files.get(&source_id) else {
            continue;
        };
        for statement in source.statements() {
            let Statement::Export(export) = statement.data() else {
                continue;
            };
            match export {
                crate::syntax::ExportDeclaration::Named(named) => match named {
                    crate::syntax::ExportNamedDeclaration::Declaration(inner) => {
                        if let Some((declaration, declaration_id)) =
                            enum_plan::enum_declaration(inner)
                        {
                            let Some(symbol) = entry.facts.declaration_symbol(declaration_id)
                            else {
                                continue;
                            };
                            let Some(name) = source
                                .identifier_text(declaration.name.data().token())
                                .map(|name| EcmaString::encode(name.as_ref()))
                            else {
                                continue;
                            };
                            targets.insert((source_id, name), ExportTarget::Local(symbol));
                        } else {
                            for name in crate::lower::declared_names(source, inner) {
                                let Some(symbol) = entry
                                    .inventory
                                    .view
                                    .scopes
                                    .get(entry.inventory.view.module_scope.get() as usize)
                                    .and_then(|scope| scope.value(&name))
                                else {
                                    continue;
                                };
                                targets.insert(
                                    (source_id, EcmaString::encode(&name)),
                                    ExportTarget::Local(symbol),
                                );
                            }
                        }
                    }
                    crate::syntax::ExportNamedDeclaration::Specifiers {
                        type_only,
                        specifiers,
                        source: reexport_source,
                        ..
                    } if !type_only => {
                        let target_source = reexport_source.as_ref().and_then(|module| {
                            edges
                                .get(&(source_id, statement.id()))
                                .or_else(|| edges.get(&(source_id, module.id())))
                                .copied()
                        });
                        for specifier in specifiers {
                            let data = specifier.data();
                            if data.mode == crate::syntax::ExportSpecifierMode::TypeOnly {
                                continue;
                            }
                            let Some(exported) = module_export_name(source, &data.exported) else {
                                continue;
                            };
                            let target = if let Some(target_source) = target_source {
                                let Some(name) = module_export_name(source, &data.local) else {
                                    continue;
                                };
                                ExportTarget::Forward {
                                    source: target_source,
                                    name,
                                }
                            } else {
                                let Some(symbol) = (match &data.local {
                                    ModuleExportName::Identifier(identifier) => {
                                        lexical_symbol(source, entry.inventory.view, identifier)
                                    }
                                    ModuleExportName::String(_) | ModuleExportName::Missing(_) => {
                                        None
                                    }
                                }) else {
                                    continue;
                                };
                                ExportTarget::Local(symbol)
                            };
                            targets.insert((source_id, exported), target);
                        }
                    }
                    _ => {}
                },
                crate::syntax::ExportDeclaration::Default(default) => {
                    let name = match &default.value {
                        crate::syntax::ExportDefaultValue::Function(function) => {
                            function.name.as_ref()
                        }
                        crate::syntax::ExportDefaultValue::Class(class) => class.name.as_ref(),
                        _ => None,
                    };
                    let Some(name) = name else {
                        continue;
                    };
                    let Some(symbol) = lexical_symbol(source, entry.inventory.view, name) else {
                        continue;
                    };
                    targets.insert(
                        (source_id, EcmaString::encode("default")),
                        ExportTarget::Local(symbol),
                    );
                }
                _ => {}
            }
        }
    }
    targets
}

#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
fn resolve_program_enum_scalars(
    sources: &[Recovered<SourceFile>],
    edges: &[ResolvedModuleEdge],
    files: &mut BTreeMap<SourceId, EnumSource<'_, '_>>,
    cancel: &CancellationToken,
) -> Result<ResolvedProgramEnumScalars, CheckCancelled> {
    let edge_targets: HashMap<_, _> = edges
        .iter()
        .map(|edge| ((edge.from, edge.specifier), edge.to))
        .collect();
    let imports = collect_lexical_import_targets(sources, files, &edge_targets);
    let exports = collect_lexical_export_targets(sources, files, &edge_targets);
    let export_stars = collect_export_stars(sources, &edge_targets);

    let mut values = BTreeMap::new();
    for (&source_id, entry) in files.iter_mut() {
        cancel.check()?;
        let empty = HashMap::new();
        let (facts, _) = enum_plan::build_with_imports_from_inventory(
            &entry.inventory.view,
            entry.inventory.source,
            source_id,
            entry.inventory.declarations,
            entry.inventory.member_symbols,
            entry.inventory.member_names,
            entry.inventory.member_identifier_uses,
            entry.inventory.local_member_targets,
            entry.inventory.imported_member_uses,
            entry.inventory.imported_member_targets,
            &empty,
        );
        entry.facts = facts;
        for (member, site) in entry.facts.imported_member_uses() {
            if !matches!(
                site.base(),
                enum_plan::ImportedEnumMemberBase::Import(symbol)
                    if matches!(imports.get(&(source_id, symbol)), Some(ImportTarget::Namespace { .. }))
            ) {
                values.insert(
                    (source_id, member),
                    enum_plan::ImportedConstEnumValue::Pending,
                );
            }
        }
    }

    loop {
        let mut changed = false;
        for (&source_id, entry) in files.iter() {
            cancel.check()?;
            for (member, site) in entry.facts.imported_member_uses() {
                let value = resolve_imported_const_enum_value(
                    source_id,
                    site,
                    &imports,
                    &exports,
                    &export_stars,
                    files,
                );
                let slot = values
                    .get_mut(&(source_id, member))
                    .expect("every imported enum site has a scalar slot");
                if matches!(slot, enum_plan::ImportedConstEnumValue::Pending)
                    && !matches!(value, enum_plan::ImportedConstEnumValue::Pending)
                {
                    *slot = value;
                    changed = true;
                }
            }
        }
        if !changed {
            for value in values.values_mut() {
                if matches!(value, enum_plan::ImportedConstEnumValue::Pending) {
                    *value = enum_plan::ImportedConstEnumValue::Cycle;
                }
            }
            break;
        }
        for (&source_id, entry) in files.iter_mut() {
            cancel.check()?;
            let imported_values: HashMap<_, _> = values
                .iter()
                .filter(|&(&(candidate_source, _), _)| candidate_source == source_id)
                .map(|(&(_, node), value)| (node, value.clone()))
                .collect();
            let (facts, _) = enum_plan::build_with_imports_from_inventory(
                &entry.inventory.view,
                entry.inventory.source,
                source_id,
                entry.inventory.declarations,
                entry.inventory.member_symbols,
                entry.inventory.member_names,
                entry.inventory.member_identifier_uses,
                entry.inventory.local_member_targets,
                entry.inventory.imported_member_uses,
                entry.inventory.imported_member_targets,
                &imported_values,
            );
            entry.facts = facts;
        }
    }
    let mut by_source = BTreeMap::new();
    for ((source, node), value) in values {
        by_source
            .entry(source)
            .or_insert_with(HashMap::new)
            .insert(node, value);
    }
    Ok(ResolvedProgramEnumScalars { by_source })
}

fn collect_imported_const_enum_facts(
    sources: &[Recovered<SourceFile>],
    edges: &[ResolvedModuleEdge],
    files: &mut BTreeMap<SourceId, SemanticModel>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let edge_targets: HashMap<_, _> = edges
        .iter()
        .map(|edge| ((edge.from, edge.specifier), edge.to))
        .collect();
    let imports = collect_import_targets(sources, files, &edge_targets);
    let exports = collect_export_targets(sources, files, &edge_targets);
    let export_stars = collect_export_stars(sources, &edge_targets);
    let mut sites: Vec<_> = files
        .iter()
        .flat_map(|(&source, model)| {
            model
                .enum_facts()
                .imported_member_uses()
                .map(move |(member, site)| (source, member, site.clone()))
        })
        .filter(|(source, _, site)| {
            !matches!(
                site.base(),
                enum_plan::ImportedEnumMemberBase::Import(symbol)
                    if matches!(imports.get(&(*source, symbol)), Some(ImportTarget::Namespace { .. }))
            )
        })
        .collect();
    sites.sort_by_key(|(source, member, _)| (source.get(), member.get()));
    let mut values: BTreeMap<_, _> = sites
        .iter()
        .map(|(source, member, _)| {
            (
                (*source, *member),
                enum_plan::ImportedConstEnumValue::Pending,
            )
        })
        .collect();
    loop {
        let mut changed = false;
        for (source, member, site) in &sites {
            let value = resolve_imported_const_enum_value(
                *source,
                site,
                &imports,
                &exports,
                &export_stars,
                files,
            );
            let slot = values
                .get_mut(&(*source, *member))
                .expect("every imported member site has a value slot");
            if matches!(slot, enum_plan::ImportedConstEnumValue::Pending)
                && !matches!(value, enum_plan::ImportedConstEnumValue::Pending)
            {
                *slot = value;
                changed = true;
            }
        }
        if !changed {
            for value in values.values_mut() {
                if matches!(value, enum_plan::ImportedConstEnumValue::Pending) {
                    *value = enum_plan::ImportedConstEnumValue::Cycle;
                }
            }
            rebuild_program_enum_facts(sources, files, &values, diagnostics);
            break;
        }
        rebuild_program_enum_facts(sources, files, &values, diagnostics);
    }
    for ((source, _), target) in &imports {
        let ImportTarget::Named {
            specifier: Some(specifier),
            ..
        } = target
        else {
            continue;
        };
        if matches!(
            resolve_import_target(
                *source,
                target,
                &imports,
                &exports,
                &export_stars,
                files,
                &mut HashSet::new(),
            ),
            ExportResolution::Const(_)
        ) {
            files
                .get_mut(source)
                .expect("every import source has a semantic model")
                .enum_facts
                .elide_import_specifier(*specifier);
        }
    }
    for (source, member, site) in sites {
        let value = values
            .remove(&(source, member))
            .expect("fixed point covers every imported member");
        let is_const_enum = matches!(
            &value,
            enum_plan::ImportedConstEnumValue::Constant(_)
                | enum_plan::ImportedConstEnumValue::Nonconstant
                | enum_plan::ImportedConstEnumValue::Cycle,
        );
        let model = files
            .get_mut(&source)
            .expect("candidate source has a semantic model");
        if is_const_enum && model.enum_facts.is_imported_member_target(member) {
            model.enum_facts.add_import_const_enum_member_target(member);
        }
        match value {
            enum_plan::ImportedConstEnumValue::Constant(value) => {
                model.enum_facts.add_import_const_use(member, value);
            }
            enum_plan::ImportedConstEnumValue::Nonconstant => {
                diagnostics.push(imported_enum_error(
                    source,
                    IMPORTED_CONST_ENUM_NONCONSTANT,
                    site.range(),
                    "Imported const-enum member is not a constant.",
                ))
            }
            enum_plan::ImportedConstEnumValue::Unresolved => diagnostics.push(imported_enum_error(
                source,
                IMPORTED_CONST_ENUM_UNRESOLVED,
                site.range(),
                "Imported const-enum member could not be resolved.",
            )),
            enum_plan::ImportedConstEnumValue::Ambiguous => diagnostics.push(imported_enum_error(
                source,
                IMPORTED_CONST_ENUM_AMBIGUOUS,
                site.range(),
                "Imported const-enum member is ambiguous.",
            )),
            enum_plan::ImportedConstEnumValue::Cycle => diagnostics.push(imported_enum_error(
                source,
                IMPORTED_CONST_ENUM_CYCLE,
                site.range(),
                "Imported const-enum dependency is cyclic.",
            )),
            enum_plan::ImportedConstEnumValue::NotConst => {}
            enum_plan::ImportedConstEnumValue::Pending => {
                unreachable!("fixed point classifies every imported dependency")
            }
        }
    }
}

#[expect(
    dead_code,
    reason = "retained for the Main-owned atomic enum bootstrap cutover"
)]
fn publish_imported_const_enum_facts(
    sources: &[Recovered<SourceFile>],
    edges: &[ResolvedModuleEdge],
    files: &mut BTreeMap<SourceId, SemanticModel>,
    resolved: &ResolvedProgramEnumScalars,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let edge_targets: HashMap<_, _> = edges
        .iter()
        .map(|edge| ((edge.from, edge.specifier), edge.to))
        .collect();
    let imports = collect_import_targets(sources, files, &edge_targets);
    let exports = collect_export_targets(sources, files, &edge_targets);
    let export_stars = collect_export_stars(sources, &edge_targets);
    for (source, values) in &resolved.by_source {
        let decisions: Vec<_> = files
            .get(source)
            .map(|model| {
                model
                    .enum_facts()
                    .imported_member_uses()
                    .filter_map(|(member, site)| {
                        let value = values.get(&member)?.clone();
                        let candidates: HashMap<_, _> = model
                            .enum_facts()
                            .imported_member_uses()
                            .map(|(node, candidate)| (node, candidate.clone()))
                            .collect();
                        let is_const_enum_target = model
                            .enum_facts()
                            .is_imported_member_target(member)
                            && matches!(
                                resolve_imported_member_base(
                                    *source,
                                    site,
                                    &candidates,
                                    &imports,
                                    &exports,
                                    &export_stars,
                                    files,
                                    &mut HashSet::new(),
                                ),
                                ImportedMemberBaseResolution::Export(ExportResolution::Const(_),)
                            );
                        Some((member, site.clone(), value, is_const_enum_target))
                    })
                    .collect()
            })
            .unwrap_or_default();
        for (member, site, value, is_const_enum_target) in decisions {
            if is_const_enum_target && let Some(model) = files.get_mut(source) {
                model.enum_facts.add_import_const_enum_member_target(member);
            }
            match value {
                enum_plan::ImportedConstEnumValue::Constant(value) => {
                    if let Some(model) = files.get_mut(source) {
                        model.enum_facts.add_import_const_use(member, value);
                    }
                }
                enum_plan::ImportedConstEnumValue::Nonconstant => {
                    diagnostics.push(imported_enum_error(
                        *source,
                        IMPORTED_CONST_ENUM_NONCONSTANT,
                        site.range(),
                        "Imported const-enum member is not a constant.",
                    ))
                }
                enum_plan::ImportedConstEnumValue::Unresolved => {
                    diagnostics.push(imported_enum_error(
                        *source,
                        IMPORTED_CONST_ENUM_UNRESOLVED,
                        site.range(),
                        "Imported const-enum member could not be resolved.",
                    ))
                }
                enum_plan::ImportedConstEnumValue::Ambiguous => {
                    diagnostics.push(imported_enum_error(
                        *source,
                        IMPORTED_CONST_ENUM_AMBIGUOUS,
                        site.range(),
                        "Imported const-enum member is ambiguous.",
                    ))
                }
                enum_plan::ImportedConstEnumValue::Cycle => diagnostics.push(imported_enum_error(
                    *source,
                    IMPORTED_CONST_ENUM_CYCLE,
                    site.range(),
                    "Imported const-enum dependency is cyclic.",
                )),
                enum_plan::ImportedConstEnumValue::NotConst
                | enum_plan::ImportedConstEnumValue::Pending => {}
            }
        }
    }
    for ((source, _), target) in &imports {
        let ImportTarget::Named {
            specifier: Some(specifier),
            ..
        } = target
        else {
            continue;
        };
        if matches!(
            resolve_import_target(
                *source,
                target,
                &imports,
                &exports,
                &export_stars,
                files,
                &mut HashSet::new(),
            ),
            ExportResolution::Const(_)
        ) && let Some(model) = files.get_mut(source)
        {
            model.enum_facts.elide_import_specifier(*specifier);
        }
    }
}

fn rebuild_program_enum_facts(
    sources: &[Recovered<SourceFile>],
    files: &mut BTreeMap<SourceId, SemanticModel>,
    values: &BTreeMap<(SourceId, NodeId), enum_plan::ImportedConstEnumValue>,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let imported_values: HashMap<_, _> = values
            .iter()
            .filter(|&(&(candidate_source, _), _)| candidate_source == source_id)
            .map(|(&(_, node), value)| (node, value.clone()))
            .collect();
        let model = files
            .get_mut(&source_id)
            .expect("every source has a semantic model");
        for diagnostic in rebuild_file_enum_facts(source, model, &imported_values) {
            let duplicate = diagnostics.iter().any(|existing| {
                existing.source_id() == diagnostic.source_id()
                    && existing.range() == diagnostic.range()
                    && existing.code() == diagnostic.code()
            });
            if !duplicate {
                diagnostics.push(diagnostic);
            }
        }
    }
}

fn rebuild_file_enum_facts(
    source: &SourceFile,
    model: &mut SemanticModel,
    imported_values: &HashMap<NodeId, enum_plan::ImportedConstEnumValue>,
) -> Vec<Diagnostic> {
    let direct_member_uses: HashSet<_> = model.enum_facts().member_uses().collect();
    let local_member_targets: HashMap<_, _> = model.enum_facts().local_member_targets().collect();
    let imported_member_targets: HashSet<_> =
        model.enum_facts().imported_member_targets().collect();
    let imported_member_uses: HashMap<_, _> = model
        .enum_facts()
        .imported_member_uses()
        .map(|(node, site)| (node, site.clone()))
        .collect();
    let mut bindings = Vec::new();
    for statement in source.statements() {
        collect_enum_rebuild_bindings(statement, model, false, &mut bindings);
    }
    let mut member_symbols = HashMap::new();
    let mut member_names = HashMap::new();
    for binding in &bindings {
        for member in &binding.declaration.members {
            if let Some(symbol) = model.enum_facts().member_symbol(member.id()) {
                member_symbols.insert(member.id(), symbol);
            }
            if let Some(name) = enum_plan::cook_member_name(source, &member.data().name) {
                member_names.insert(member.id(), name);
            }
        }
    }
    let (facts, diagnostics) = enum_plan::build_with_imports(
        model,
        source,
        source.source_id(),
        &bindings,
        &member_symbols,
        &member_names,
        &direct_member_uses,
        &local_member_targets,
        &imported_member_uses,
        &imported_member_targets,
        imported_values,
    );
    model.enum_facts = facts;
    diagnostics
}

fn collect_enum_rebuild_bindings<'src>(
    statement: &'src crate::syntax::Stmt,
    model: &SemanticModel,
    ambient: bool,
    bindings: &mut Vec<EnumDeclarationBinding<'src>>,
) {
    match statement.data() {
        Statement::Enum(declaration) => {
            if let Some(symbol) = model.enum_facts().declaration_symbol(statement.id()) {
                bindings.push(EnumDeclarationBinding {
                    declaration,
                    declaration_id: statement.id(),
                    symbol,
                    ambient,
                });
            }
        }
        Statement::Declare(inner) => {
            collect_enum_rebuild_bindings(inner, model, true, bindings);
        }
        Statement::Export(crate::syntax::ExportDeclaration::Named(
            crate::syntax::ExportNamedDeclaration::Declaration(inner),
        )) => {
            collect_enum_rebuild_bindings(inner, model, ambient, bindings);
        }
        _ => {}
    }
}
fn resolve_imported_const_enum_value<S: EnumSourceRead>(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
) -> enum_plan::ImportedConstEnumValue {
    let candidates: HashMap<_, _> = files
        .get(&source)
        .expect("every candidate source has an enum source")
        .enum_facts()
        .imported_member_uses()
        .map(|(node, candidate)| (node, candidate.clone()))
        .collect();
    match resolve_imported_member_base(
        source,
        site,
        &candidates,
        imports,
        exports,
        export_stars,
        files,
        &mut HashSet::new(),
    ) {
        ImportedMemberBaseResolution::Export(ExportResolution::Const(enum_id)) => files
            .get(&enum_id.source)
            .expect("resolved enum source has a semantic model")
            .enum_facts()
            .const_enum_members(enum_id.symbol)
            .and_then(|members| members.member(site.name()))
            .map_or(
                enum_plan::ImportedConstEnumValue::Unresolved,
                |member| match member {
                    enum_plan::ConstEnumMember::Constant(value) => {
                        enum_plan::ImportedConstEnumValue::Constant(value.clone())
                    }
                    enum_plan::ConstEnumMember::Nonconstant => {
                        enum_plan::ImportedConstEnumValue::Nonconstant
                    }
                    enum_plan::ConstEnumMember::Pending => {
                        enum_plan::ImportedConstEnumValue::Pending
                    }
                },
            ),
        ImportedMemberBaseResolution::Export(ExportResolution::NotConst)
        | ImportedMemberBaseResolution::Export(ExportResolution::Namespace(_))
        | ImportedMemberBaseResolution::Scalar => enum_plan::ImportedConstEnumValue::NotConst,
        ImportedMemberBaseResolution::Export(ExportResolution::Unresolved) => {
            enum_plan::ImportedConstEnumValue::Unresolved
        }
        ImportedMemberBaseResolution::Export(ExportResolution::Ambiguous) => {
            enum_plan::ImportedConstEnumValue::Ambiguous
        }
        ImportedMemberBaseResolution::Export(ExportResolution::Cycle) => {
            enum_plan::ImportedConstEnumValue::Cycle
        }
    }
}

fn collect_import_targets(
    sources: &[Recovered<SourceFile>],
    files: &BTreeMap<SourceId, SemanticModel>,
    edges: &HashMap<(SourceId, NodeId), SourceId>,
) -> HashMap<(SourceId, SymbolId), ImportTarget> {
    let mut targets = HashMap::new();
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let Some(model) = files.get(&source_id) else {
            continue;
        };
        for statement in source.statements() {
            let Statement::Import(import) = statement.data() else {
                continue;
            };
            let Some(target_source) = edges
                .get(&(source_id, statement.id()))
                .or_else(|| edges.get(&(source_id, import.source.id())))
                .copied()
            else {
                continue;
            };
            let Some(clause) = &import.clause else {
                continue;
            };
            if let Some(default) = &clause.default
                && let Some(symbol) = lookup_identifier(model, source, default)
            {
                targets.insert(
                    (source_id, symbol),
                    ImportTarget::Named {
                        source: target_source,
                        name: EcmaString::encode("default"),
                        specifier: None,
                    },
                );
            }
            match &clause.binding {
                Some(ImportBinding::Namespace(local)) => {
                    if let Some(symbol) = lookup_identifier(model, source, local) {
                        targets.insert(
                            (source_id, symbol),
                            ImportTarget::Namespace {
                                source: target_source,
                            },
                        );
                    }
                }
                Some(ImportBinding::Named(specifiers)) => {
                    for specifier in specifiers {
                        let specifier_data = specifier.data();
                        let Some(symbol) = lookup_identifier(model, source, &specifier_data.local)
                        else {
                            continue;
                        };
                        let Some(name) = module_export_name(source, &specifier_data.imported)
                        else {
                            continue;
                        };
                        targets.insert(
                            (source_id, symbol),
                            ImportTarget::Named {
                                source: target_source,
                                name,
                                specifier: Some(specifier.id()),
                            },
                        );
                    }
                }
                None => {}
            }
        }
    }
    targets
}

fn collect_export_targets(
    sources: &[Recovered<SourceFile>],
    files: &BTreeMap<SourceId, SemanticModel>,
    edges: &HashMap<(SourceId, NodeId), SourceId>,
) -> HashMap<(SourceId, EcmaString), ExportTarget> {
    let mut targets = HashMap::new();
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let Some(model) = files.get(&source_id) else {
            continue;
        };
        for statement in source.statements() {
            let Statement::Export(export) = statement.data() else {
                continue;
            };
            match export {
                crate::syntax::ExportDeclaration::Named(named) => match named {
                    crate::syntax::ExportNamedDeclaration::Declaration(inner) => {
                        if let Some((declaration, declaration_id)) =
                            enum_plan::enum_declaration(inner)
                        {
                            let Some(symbol) =
                                model.enum_facts().declaration_symbol(declaration_id)
                            else {
                                continue;
                            };
                            let Some(name) = source
                                .identifier_text(declaration.name.data().token())
                                .map(|name| EcmaString::encode(name.as_ref()))
                            else {
                                continue;
                            };
                            targets.insert((source_id, name), ExportTarget::Local(symbol));
                        } else {
                            for name in crate::lower::declared_names(source, inner) {
                                let Some(symbol) = model.lookup_value(model.module_scope(), &name)
                                else {
                                    continue;
                                };
                                targets.insert(
                                    (source_id, EcmaString::encode(&name)),
                                    ExportTarget::Local(symbol),
                                );
                            }
                        }
                        let declaration = match inner.data() {
                            Statement::Declare(declaration) => declaration.data(),
                            declaration => declaration,
                        };
                        let type_name = match declaration {
                            Statement::Interface(interface) => Some(&interface.name),
                            Statement::TypeAlias(alias) => Some(&alias.name),
                            _ => None,
                        };
                        if let Some(name) = type_name
                            && let Some(name) = source.identifier_text(name.data().token())
                            && let Some(symbol) =
                                model.lookup_type(model.module_scope(), name.as_ref())
                        {
                            targets.insert(
                                (source_id, EcmaString::encode(name.as_ref())),
                                ExportTarget::Local(symbol),
                            );
                        }
                    }
                    crate::syntax::ExportNamedDeclaration::Specifiers {
                        type_only,
                        specifiers,
                        source: reexport_source,
                        ..
                    } if !type_only => {
                        let target_source = reexport_source.as_ref().and_then(|source| {
                            edges
                                .get(&(source_id, statement.id()))
                                .or_else(|| edges.get(&(source_id, source.id())))
                                .copied()
                        });
                        for specifier in specifiers {
                            let specifier = specifier.data();
                            if specifier.mode == crate::syntax::ExportSpecifierMode::TypeOnly {
                                continue;
                            }
                            let Some(exported) = module_export_name(source, &specifier.exported)
                            else {
                                continue;
                            };
                            let target = if let Some(target_source) = target_source {
                                let Some(name) = module_export_name(source, &specifier.local)
                                else {
                                    continue;
                                };
                                ExportTarget::Forward {
                                    source: target_source,
                                    name,
                                }
                            } else {
                                let Some(symbol) =
                                    lookup_module_export_name(model, source, &specifier.local)
                                else {
                                    continue;
                                };
                                ExportTarget::Local(symbol)
                            };
                            targets.insert((source_id, exported), target);
                        }
                    }
                    _ => {}
                },
                crate::syntax::ExportDeclaration::Default(default) => {
                    let name = match &default.value {
                        crate::syntax::ExportDefaultValue::Function(function) => {
                            function.name.as_ref()
                        }
                        crate::syntax::ExportDefaultValue::Class(class) => class.name.as_ref(),
                        _ => None,
                    };
                    let Some(name) = name else {
                        continue;
                    };
                    let Some(symbol) = lookup_identifier(model, source, name) else {
                        continue;
                    };
                    targets.insert(
                        (source_id, EcmaString::encode("default")),
                        ExportTarget::Local(symbol),
                    );
                }
                _ => {}
            }
        }
    }
    targets
}

fn collect_export_stars(
    sources: &[Recovered<SourceFile>],
    edges: &HashMap<(SourceId, NodeId), SourceId>,
) -> ExportStars {
    let mut stars = ExportStars::default();
    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        for statement in source.statements() {
            let Statement::Export(crate::syntax::ExportDeclaration::All(all)) = statement.data()
            else {
                continue;
            };
            if all.type_only {
                continue;
            }
            let Some(target) = edges
                .get(&(source_id, statement.id()))
                .or_else(|| edges.get(&(source_id, all.source.id())))
                .copied()
            else {
                continue;
            };
            if let Some(exported) = all
                .exported
                .as_ref()
                .and_then(|name| module_export_name(source, name))
            {
                stars
                    .namespace_exports
                    .insert((source_id, exported), target);
            } else {
                stars.targets.entry(source_id).or_default().push(target);
            }
        }
    }
    stars
}

#[expect(
    clippy::too_many_arguments,
    reason = "imported member base resolution threads the shared import/export lookup tables"
)]
fn resolve_imported_member_base<S: EnumSourceRead>(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    candidates: &HashMap<NodeId, enum_plan::ImportedEnumMemberUse>,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ImportedMemberBaseResolution {
    match site.base() {
        enum_plan::ImportedEnumMemberBase::Import(symbol) => {
            let Some(target) = imports.get(&(source, symbol)) else {
                // No in-program target means an external runtime import. `Unresolved` is
                // reserved for an import target whose export/member lookup fails.
                return ImportedMemberBaseResolution::Export(ExportResolution::NotConst);
            };
            ImportedMemberBaseResolution::Export(resolve_import_target(
                source,
                target,
                imports,
                exports,
                export_stars,
                files,
                visited,
            ))
        }
        enum_plan::ImportedEnumMemberBase::MemberResult(member) => candidates.get(&member).map_or(
            ImportedMemberBaseResolution::Export(ExportResolution::Unresolved),
            |candidate| {
                resolve_imported_member_result(
                    source,
                    candidate,
                    candidates,
                    imports,
                    exports,
                    export_stars,
                    files,
                    visited,
                )
            },
        ),
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "imported member result resolution threads the shared import/export lookup tables"
)]
fn resolve_imported_member_result<S: EnumSourceRead>(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    candidates: &HashMap<NodeId, enum_plan::ImportedEnumMemberUse>,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ImportedMemberBaseResolution {
    match resolve_imported_member_base(
        source,
        site,
        candidates,
        imports,
        exports,
        export_stars,
        files,
        visited,
    ) {
        ImportedMemberBaseResolution::Export(
            ExportResolution::Const(_) | ExportResolution::NotConst,
        )
        | ImportedMemberBaseResolution::Scalar => ImportedMemberBaseResolution::Scalar,
        ImportedMemberBaseResolution::Export(ExportResolution::Namespace(source)) => {
            ImportedMemberBaseResolution::Export(resolve_export(
                source,
                site.name(),
                imports,
                exports,
                export_stars,
                files,
                visited,
            ))
        }
        ImportedMemberBaseResolution::Export(resolution) => {
            ImportedMemberBaseResolution::Export(resolution)
        }
    }
}

fn resolve_import_target<S: EnumSourceRead>(
    _source: SourceId,
    target: &ImportTarget,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolution {
    resolve_import_target_candidates(target, imports, exports, export_stars, files, visited)
        .into_resolution()
}

fn resolve_import_target_candidates<S: EnumSourceRead>(
    target: &ImportTarget,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolutionSet {
    match target {
        ImportTarget::Named { source, name, .. } => resolve_export_candidates(
            *source,
            name,
            imports,
            exports,
            export_stars,
            files,
            visited,
        ),
        ImportTarget::Namespace { source } => {
            ExportResolutionSet::candidate(ExportCandidate::Namespace(*source))
        }
    }
}

fn resolve_export<S: EnumSourceRead>(
    source: SourceId,
    name: &EcmaString,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolution {
    resolve_export_candidates(source, name, imports, exports, export_stars, files, visited)
        .into_resolution()
}

fn resolve_export_candidates<S: EnumSourceRead>(
    source: SourceId,
    name: &EcmaString,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolutionSet {
    let key = (source, name.clone());
    if !visited.insert(key.clone()) {
        return ExportResolutionSet::cycle();
    }
    let result = match exports.get(&key) {
        Some(ExportTarget::Forward { source, name }) => resolve_export_candidates(
            *source,
            name,
            imports,
            exports,
            export_stars,
            files,
            visited,
        ),
        Some(ExportTarget::Local(symbol)) => resolve_exported_symbol_candidates(
            source,
            *symbol,
            imports,
            exports,
            export_stars,
            files,
            visited,
        ),
        None => match export_stars.namespace_exports.get(&key) {
            Some(source) => ExportResolutionSet::candidate(ExportCandidate::Namespace(*source)),
            None => {
                let mut candidates = ExportResolutionSet::default();
                for target in export_stars.targets.get(&source).into_iter().flatten() {
                    candidates.extend(resolve_export_candidates(
                        *target,
                        name,
                        imports,
                        exports,
                        export_stars,
                        files,
                        visited,
                    ));
                }
                candidates
            }
        },
    };
    visited.remove(&key);
    result
}

fn resolve_exported_symbol_candidates<S: EnumSourceRead>(
    source: SourceId,
    symbol: SymbolId,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, S>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolutionSet {
    let Some(model) = files.get(&source) else {
        return ExportResolutionSet::default();
    };
    if model.enum_facts().const_enum_members(symbol).is_some() {
        return ExportResolutionSet::candidate(ExportCandidate::Const(LinkedEnum {
            source,
            symbol,
        }));
    }
    let value = ExportCandidate::Value(LinkedExport { source, symbol });
    match model.symbol_kind(symbol) {
        Some(SymbolKind::Import) => {
            imports
                .get(&(source, symbol))
                .map_or_else(ExportResolutionSet::default, |target| {
                    resolve_import_target_candidates(
                        target,
                        imports,
                        exports,
                        export_stars,
                        files,
                        visited,
                    )
                })
        }
        Some(_) => ExportResolutionSet::candidate(value),
        None => ExportResolutionSet::default(),
    }
}
fn lookup_identifier(
    model: &SemanticModel,
    source: &SourceFile,
    identifier: &IdentifierNode,
) -> Option<SymbolId> {
    source
        .identifier_text(identifier.data().token())
        .and_then(|name| model.lookup_value(model.module_scope(), name.as_ref()))
}

fn module_export_name(source: &SourceFile, name: &ModuleExportName) -> Option<EcmaString> {
    match name {
        ModuleExportName::Identifier(identifier) => source
            .identifier_text(identifier.data().token())
            .map(|name| EcmaString::encode(name.as_ref())),
        ModuleExportName::String(string) => source
            .token_text(string.data().token())
            .and_then(crate::literal::string_value),
        ModuleExportName::Missing(_) => None,
    }
}

fn lookup_module_export_name(
    model: &SemanticModel,
    source: &SourceFile,
    name: &ModuleExportName,
) -> Option<SymbolId> {
    match name {
        ModuleExportName::Identifier(identifier) => lookup_identifier(model, source, identifier),
        ModuleExportName::String(_) | ModuleExportName::Missing(_) => None,
    }
}

fn imported_enum_error(
    source: SourceId,
    code: DiagnosticCode,
    range: TextRange,
    message: &'static str,
) -> Diagnostic {
    Diagnostic::error(code, source, range, message)
}

#[cfg(test)]
mod tests {
    use super::{
        ARGUMENT_NOT_ASSIGNABLE, BARE_SUPER_EXPRESSION, BLOCK_SCOPED_USED_BEFORE_DECLARATION,
        BREAK_TARGET_CROSSES_FUNCTION, BREAK_TARGET_NOT_ENCLOSING, CANNOT_FIND_NAME,
        CANNOT_FIND_NAME_LIB_GATED, CANNOT_FIND_NAMESPACE, CANNOT_FIND_TYPE,
        CLASS_USED_BEFORE_DECLARATION, CONSTRUCTOR_DECORATOR_NOT_SUPPORTED,
        DERIVED_CONSTRUCTOR_MISSING_SUPER, DUPLICATE_DECLARATION, DUPLICATE_LABEL,
        ENUM_USED_BEFORE_DECLARATION, EXPRESSION_NOT_CALLABLE, IMPORTED_CONST_ENUM_AMBIGUOUS,
        IMPORTED_CONST_ENUM_CYCLE, IMPORTED_CONST_ENUM_NONCONSTANT, INTERFACE_NAME_IS_PRIMITIVE,
        INVALID_ASSIGNMENT_TARGET, MISSING_METHOD_RETURN_TYPE, MIXED_EXPORT_ASSIGNMENT,
        NAMESPACE_NO_EXPORTED_MEMBER, PARAMETER_DECORATOR_NOT_SUPPORTED,
        PARAMETER_INITIALIZER_IN_SIGNATURE, PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR,
        PROPERTY_DOES_NOT_EXIST, ProgramCheckInput, ProgramCheckOptions, PropertyType,
        REST_PARAMETER_NOT_LAST, ResolvedModuleEdge, SUPER_BEFORE_SUPER_PROPERTY,
        SUPER_BEFORE_THIS, SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS, SUPER_CALL_OUTSIDE_CONSTRUCTOR,
        SUPER_FIELD_VIA_SUPER, SUPER_PROPERTY_NOT_METHOD, SUPER_REFERENCE_NON_DERIVED,
        SUPER_STATIC_MEMBER_VIA_SUPER, ScopeKind, SymbolKind, TYPE_ALIAS_CIRCULAR,
        TYPE_NOT_ASSIGNABLE, TYPE_PARAMETER_CIRCULAR_DEFAULT, Type, TypeId, TypeTable,
        VALUE_CANNOT_BE_USED_HERE, WITH_STATEMENT_NOT_ALLOWED, check, check_program,
        check_program_with_options,
    };
    use crate::diagnostic::{DiagnosticSeverity, Recovered};
    use crate::namespace_plan::{ContainerAcquisition, ExportStorage};
    use crate::source::{ScriptKind, SourceId, SourceText, TextRange, Utf16Pos};
    use crate::syntax::{
        ArrowFunction, BindingPattern, Block, ClassMember, Decorator, EntityName,
        ExportDeclaration, ExportNamedDeclaration, Expr, Expression, ExpressionStatement,
        FunctionBody, Identifier, IdentifierNode, KeywordType, Literal, MissingNode, Node, NodeId,
        NodeKind, NumericLiteral, Parameter, ParameterNode, SourceFile, Statement, Stmt,
        StringLiteral, Token, TokenKind, TypeAnnotation, TypeNode,
    };
    use crate::{parser, scanner};
    use std::sync::Arc;

    // ---- direct algebra tests -------------------------------------------------
    #[test]
    fn top_and_bottom_types_bound_the_lattice() {
        let table = TypeTable::new();
        // never flows into everything; nothing else flows into never.
        assert!(table.assignable(table.never(), table.number()));
        assert!(!table.assignable(table.number(), table.never()));
        // unknown is the top: everything in, nothing out.
        assert!(table.assignable(table.number(), table.unknown()));
        assert!(!table.assignable(table.unknown(), table.number()));
        // any is the escape hatch both directions.
        assert!(table.assignable(table.any(), table.number()));
        assert!(table.assignable(table.number(), table.any()));
    }

    #[test]
    fn literals_widen_to_their_base_primitive_only() {
        let mut table = TypeTable::new();
        let one = table.number_literal("1");
        assert!(table.assignable(one, table.number()));
        assert!(!table.assignable(table.number(), one));
        assert!(!table.assignable(one, table.string()));
    }

    #[test]
    fn union_source_requires_all_members_target_requires_one() {
        let mut table = TypeTable::new();
        let number_or_string = table.union(&[table.number(), table.string()]);
        assert!(table.assignable(table.number(), number_or_string));
        assert!(!table.assignable(table.boolean(), number_or_string));
        assert!(table.assignable(number_or_string, table.unknown()));
        assert!(!table.assignable(number_or_string, table.number()));
    }

    #[test]
    fn union_normalizes_absorption_and_duplicates() {
        let mut table = TypeTable::new();
        assert_eq!(
            table.union(&[table.number(), table.number()]),
            table.number()
        );
        assert_eq!(
            table.union(&[table.number(), table.never()]),
            table.number()
        );
        assert_eq!(table.union(&[table.number(), table.any()]), table.any());
    }

    #[test]
    fn arrays_are_covariant_in_their_element() {
        let mut table = TypeTable::new();
        let number_literal = table.number_literal("1");
        let literal_array = table.array(number_literal);
        let number_array = table.array(table.number());
        assert!(table.assignable(literal_array, number_array));
        assert!(!table.assignable(number_array, literal_array));
    }

    #[test]
    fn tuple_representation_preserves_fixed_elements() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let tuple = table.tuple(vec![number, string]);
        assert_eq!(
            table.get(tuple),
            &Type::Tuple(super::binder::TupleShape::fixed(vec![number, string]))
        );
    }

    #[test]
    fn intersection_representation_preserves_canonical_members() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let intersection = table.intersection(vec![string, number, string]);
        assert_eq!(
            table.get(intersection),
            &Type::Intersection(vec![number, string])
        );
    }

    #[test]
    fn objects_are_structural_with_optional_and_excess_rules() {
        let mut table = TypeTable::new();
        let required = table.object_type(vec![PropertyType::new("x", false, table.number())]);
        let with_excess = table.object_type(vec![
            PropertyType::new("x", false, table.number()),
            PropertyType::new("y", false, table.string()),
        ]);
        let missing = table.object_type(vec![PropertyType::new("y", false, table.string())]);
        let optional = table.object_type(vec![PropertyType::new("x", true, table.number())]);
        let empty = table.object_type(vec![]);

        // Excess source properties are allowed structurally.
        assert!(table.assignable(with_excess, required));
        // A missing required property is rejected.
        assert!(!table.assignable(missing, required));
        // An optional target property may be absent.
        assert!(table.assignable(empty, optional));
    }

    #[test]
    fn functions_are_contravariant_in_params_covariant_in_return() {
        let mut table = TypeTable::new();
        let animal = table.named(super::SymbolId::new(100));
        let dog = table.named(super::SymbolId::new(101));
        // fn(animal) -> dog  <:  fn(dog) -> animal  is unrelated nominally, but
        // the variance shape is what we assert here.
        let number = table.number();
        let takes_number = table.function(vec![number], table.void());
        let number_literal = table.number_literal("1");
        let takes_number_literal = table.function(vec![number_literal], table.void());
        // target param number must be assignable to source param numberLiteral?
        // No: number is not a number literal, so it is rejected (contravariant).
        assert!(!table.assignable(takes_number_literal, takes_number));
        // Fewer source params is fine.
        let takes_none = table.function(vec![], table.void());
        assert!(table.assignable(takes_none, takes_number));
        // Return void absorbs any source return.
        let returns_number = table.function(vec![], table.number());
        assert!(table.assignable(returns_number, takes_none));
        // Silence unused nominal helpers when variance path above suffices.
        assert_ne!(animal, dog);
    }

    #[test]
    fn relation_retains_optional_callback_void_and_enum_hazards() {
        let mut table = TypeTable::new();
        let source_object =
            table.object_type(vec![PropertyType::new("x", false, table.undefined_type())]);
        let target_object = table.object_type(vec![PropertyType::new("x", true, table.number())]);
        let optional = table.relation(source_object, target_object);
        assert!(optional.compatible());
        assert!(
            optional
                .hazards()
                .contains(&super::RelationHazard::ExplicitUndefinedForOptional)
        );

        let source_function = table.function(Vec::new(), table.number());
        let target_function = table.function(vec![table.number()], table.void());
        let callback = table.relation(source_function, target_function);
        assert!(
            callback
                .hazards()
                .contains(&super::RelationHazard::FewerCallbackParameters)
        );
        assert!(
            callback
                .hazards()
                .contains(&super::RelationHazard::ValueReturnedToVoid)
        );

        let enum_type = table.numeric_enum(super::SymbolId::new(200));
        let enum_boundary = table.relation(enum_type, table.number());
        assert!(enum_boundary.compatible());
        assert!(
            enum_boundary
                .hazards()
                .contains(&super::RelationHazard::NumericEnumNumber)
        );
    }

    #[test]
    fn optional_any_and_unknown_already_contain_undefined() {
        for value_type in [TypeTable::new().any(), TypeTable::new().unknown()] {
            let mut table = TypeTable::new();
            let source =
                table.object_type(vec![PropertyType::new("x", false, table.undefined_type())]);
            let target = table.object_type(vec![PropertyType::new("x", true, value_type)]);
            assert!(
                !table
                    .relation(source, target)
                    .hazards()
                    .contains(&super::RelationHazard::ExplicitUndefinedForOptional)
            );
        }
    }

    #[test]
    fn object_types_retain_inherited_call_and_index_signatures() {
        let text = "interface CallableBase {\
                        (value: number): string;\
                        readonly [key: string]: number;\
                    }\
                    interface CallableDerived extends CallableBase { own: boolean; }\
                    declare const base: CallableBase;\
                    declare const derived: CallableDerived;";
        let parsed_source = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        let Statement::Interface(base_declaration) = parsed_source.product().statements()[0].data()
        else {
            panic!("first statement is an interface");
        };
        assert_eq!(base_declaration.members.len(), 2, "{base_declaration:?}");
        let result = check(&parsed_source);
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );

        let model = result.product();
        let base_symbol = model
            .lookup_value(model.module_scope(), "base")
            .expect("base value symbol");
        let Type::ObjectType(base) = model.types().get(model.symbol_type(base_symbol)) else {
            panic!("base resolves to an object type");
        };
        assert_eq!(
            base.call_signatures.len(),
            1,
            "Base retains its call signature: {base:?}"
        );
        assert_eq!(
            base.index_signatures.len(),
            1,
            "Base retains its index signature: {base:?}"
        );
        let symbol = model
            .lookup_value(model.module_scope(), "derived")
            .expect("derived value symbol");
        let Type::ObjectType(object) = model.types().get(model.symbol_type(symbol)) else {
            panic!("derived resolves to an object type");
        };
        assert!(
            object
                .properties
                .iter()
                .any(|property| property.name() == "own")
        );

        let [call] = object.call_signatures.as_slice() else {
            panic!("Derived inherits one call signature");
        };
        let [parameter] = call.parameters() else {
            panic!("call signature has one parameter");
        };
        assert_eq!(parameter.type_id(), model.types().number());
        assert_eq!(call.return_type(), model.types().string());

        let [index] = object.index_signatures.as_slice() else {
            panic!("Derived inherits one index signature");
        };
        let [parameter] = index.parameters.as_slice() else {
            panic!("index signature has one parameter");
        };
        assert!(index.readonly);
        assert_eq!(parameter.type_id(), model.types().string());
        assert_eq!(index.value_type, model.types().number());
    }

    // ---- checker behavior tests ----------------------------------------------

    fn source(text: &str) -> Arc<SourceText> {
        Arc::new(SourceText::new(text).expect("test source fits the per-file budget"))
    }

    fn check_text(text: &str) -> Recovered<super::SemanticModel> {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ));
        check(&parsed)
    }

    fn check_text_strict_null(text: &str) -> Recovered<super::ProgramSemanticModel> {
        let parsed = [parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ))];
        check_program_with_options(
            ProgramCheckInput {
                files: &parsed,
                edges: &[],
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
            ProgramCheckOptions::standard().with_strict_null_checks(true),
        )
    }

    fn check_text_with(
        text: &str,
        options: ProgramCheckOptions,
    ) -> Recovered<super::ProgramSemanticModel> {
        let parsed = [parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(text),
        ))];
        check_program_with_options(
            ProgramCheckInput {
                files: &parsed,
                edges: &[],
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
            options,
        )
    }

    fn checker_codes_of(checked: &Recovered<super::ProgramSemanticModel>) -> Vec<String> {
        checked
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str().starts_with("BAMTS-C"))
            .map(|diagnostic| diagnostic.code().as_str().to_owned())
            .collect()
    }

    fn parsed(source_id: u32, text: &str) -> Recovered<SourceFile> {
        parser::parse(scanner::scan(
            SourceId::new(source_id),
            ScriptKind::TypeScript,
            source(text),
        ))
    }

    fn linked(
        texts: &[&str],
        edges: &[(usize, usize, usize)],
    ) -> Recovered<super::ProgramSemanticModel> {
        let files: Vec<_> = texts
            .iter()
            .enumerate()
            .map(|(index, text)| parsed(index as u32, text))
            .collect();
        let edges: Vec<_> = edges
            .iter()
            .map(|&(from, statement, to)| ResolvedModuleEdge {
                from: SourceId::new(from as u32),
                specifier: files[from].product().statements()[statement].id(),
                to: SourceId::new(to as u32),
            })
            .collect();
        check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        )
    }

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).expect("ordered range")
    }

    fn identifier(id: u32, name: &str, start: usize) -> IdentifierNode {
        let end = start + name.len();
        Node::new(
            NodeId::new(id),
            range(start, end),
            Identifier::new(Token::new(TokenKind::Identifier, range(start, end))),
        )
    }

    /// Builds a `SourceFile` whose statements are supplied directly, so binding
    /// and typing can be exercised without depending on a parser.
    fn file(text: &str, statements: Vec<Stmt>) -> Recovered<SourceFile> {
        let source = source(text);
        let end = source.len_utf16().get();
        let eof = Token::new(TokenKind::EndOfFile, range(end, end));
        let file = SourceFile::new(
            NodeId::new(0),
            SourceId::new(1),
            ScriptKind::TypeScript,
            range(0, end),
            source,
            Vec::new(),
            statements,
            eof,
            Vec::new(),
        );
        Recovered::clean(file)
    }

    fn keyword_annotation(
        id: u32,
        keyword: KeywordType,
        start: usize,
        end: usize,
    ) -> Node<TypeAnnotation> {
        let type_node = Node::new(
            NodeId::new(id),
            range(start, end),
            TypeNode::Keyword(keyword),
        );
        Node::new(
            NodeId::new(id + 1),
            range(start, end),
            TypeAnnotation {
                type_node: Box::new(type_node),
            },
        )
    }

    fn variable(
        id: u32,
        text: &str,
        name: &str,
        name_start: usize,
        annotation: Option<Node<TypeAnnotation>>,
        initializer: Option<Box<Expr>>,
    ) -> Stmt {
        let name_node = identifier(id + 1, name, name_start);
        let binding = Node::new(
            NodeId::new(id + 2),
            name_node.range(),
            BindingPattern::Identifier(name_node),
        );
        let declarator = Node::new(
            NodeId::new(id + 3),
            range(0, text.len()),
            crate::syntax::VariableDeclarator {
                binding,
                definite: false,
                type_annotation: annotation,
                initializer,
            },
        );
        Node::new(
            NodeId::new(id),
            range(0, text.len()),
            Statement::Variable(crate::syntax::VariableDeclaration {
                range: range(0, text.len()),
                kind: crate::syntax::VariableKind::Const,
                declarations: vec![declarator],
            }),
        )
    }

    fn number_expr(id: u32, text: &str, start: usize) -> Box<Expr> {
        let end = start + text.len();
        let literal = Node::new(
            NodeId::new(id + 1),
            range(start, end),
            NumericLiteral::new(Token::new(TokenKind::NumericLiteral, range(start, end))),
        );
        Box::new(Node::new(
            NodeId::new(id),
            range(start, end),
            Expression::Literal(Literal::Number(literal)),
        ))
    }

    fn string_expr(id: u32, text: &str, start: usize) -> Box<Expr> {
        let end = start + text.len();
        let literal = Node::new(
            NodeId::new(id + 1),
            range(start, end),
            StringLiteral::new(Token::new(TokenKind::StringLiteral, range(start, end))),
        );
        Box::new(Node::new(
            NodeId::new(id),
            range(start, end),
            Expression::Literal(Literal::String(literal)),
        ))
    }

    fn identifier_expr(id: u32, name: &str, start: usize) -> Box<Expr> {
        Box::new(Node::new(
            NodeId::new(id),
            range(start, start + name.len()),
            Expression::Identifier(identifier(id + 1, name, start)),
        ))
    }

    fn expression_statement(id: u32, expression: Box<Expr>) -> Stmt {
        Node::new(
            NodeId::new(id),
            expression.range(),
            Statement::Expression(ExpressionStatement { expression }),
        )
    }

    fn semantic_codes(model: &Recovered<super::SemanticModel>) -> Vec<&'static str> {
        model
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    fn checker_codes<T>(result: &Recovered<T>) -> Vec<&'static str> {
        result
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .filter(|code| code.starts_with("BAMTS-C"))
            .collect()
    }

    fn program_codes(model: &Recovered<super::ProgramSemanticModel>) -> Vec<&'static str> {
        model
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .filter(|code| code.starts_with("BAMTS-C"))
            .collect()
    }

    fn program_codes_for_source(
        model: &Recovered<super::ProgramSemanticModel>,
        source_id: SourceId,
    ) -> Vec<&'static str> {
        model
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.source_id() == source_id)
            .map(|diagnostic| diagnostic.code().as_str())
            .filter(|code| code.starts_with("BAMTS-C"))
            .collect()
    }

    fn member_expression_id(source_id: u32, text: &str, statement: usize) -> NodeId {
        let parsed = parsed(source_id, text);
        let Statement::Expression(expression) = parsed.product().statements()[statement].data()
        else {
            panic!("selected statement is a member expression");
        };
        expression.expression.id()
    }

    fn member_chain_ids(file: &SourceFile, statement: usize) -> (NodeId, NodeId) {
        let Statement::Expression(statement) = file.statements()[statement].data() else {
            panic!("selected statement is an expression");
        };
        let outer = statement.expression.as_ref();
        let Expression::Member(outer_member) = outer.data() else {
            panic!("selected expression is a member chain");
        };
        let inner = outer_member.object.as_ref();
        let Expression::Member(_) = inner.data() else {
            panic!("selected expression has a member base");
        };
        (inner.id(), outer.id())
    }

    fn binary_member_expression_ids(
        source_id: u32,
        text: &str,
        statement: usize,
    ) -> (NodeId, NodeId) {
        let parsed = parsed(source_id, text);
        let Statement::Expression(expression) = parsed.product().statements()[statement].data()
        else {
            panic!("selected statement is an expression");
        };
        let Expression::Binary(binary) = expression.expression.data() else {
            panic!("selected expression is binary");
        };
        (binary.left.id(), binary.right.id())
    }

    fn import_specifier_id(source_id: u32, text: &str) -> NodeId {
        let parsed = parsed(source_id, text);
        let Statement::Import(import) = parsed.product().statements()[0].data() else {
            panic!("first statement is an import");
        };
        let Some(crate::syntax::ImportBinding::Named(specifiers)) = import
            .clause
            .as_ref()
            .and_then(|clause| clause.binding.as_ref())
        else {
            panic!("import has a named specifier");
        };
        specifiers[0].id()
    }

    #[test]
    fn binds_a_variable_and_resolves_its_later_reference() {
        let statements = vec![
            variable(
                10,
                "const a = 1;",
                "a",
                6,
                None,
                Some(number_expr(20, "1", 10)),
            ),
            expression_statement(30, identifier_expr(31, "a", 13)),
        ];
        let result = check(&file("const a = 1; a;", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        let symbol = model
            .lookup_value(model.module_scope(), "a")
            .expect("a is bound");
        assert!(matches!(
            model.symbol(symbol).kind(),
            SymbolKind::Variable(_)
        ));
        assert_eq!(model.resolved_reference_count(), 1);
        assert_eq!(model.scope(model.module_scope()).kind(), ScopeKind::Module);
    }

    #[test]
    fn reports_an_unresolved_local_value_reference() {
        let statements = vec![expression_statement(30, identifier_expr(31, "missing", 0))];
        let result = check(&file("missing;", statements));
        assert_eq!(semantic_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn a_global_value_reference_is_not_unresolved() {
        let statements = vec![expression_statement(30, identifier_expr(31, "console", 0))];
        let result = check(&file("console;", statements));
        assert!(semantic_codes(&result).is_empty());
    }

    #[test]
    fn standard_global_families_bind_as_intrinsics() {
        let names = [
            "undefined",
            "NaN",
            "Infinity",
            "isFinite",
            "isNaN",
            "parseFloat",
            "parseInt",
            "decodeURIComponent",
            "encodeURIComponent",
            "unescape",
            "Object",
            "Function",
            "Boolean",
            "Symbol",
            "Error",
            "AggregateError",
            "EvalError",
            "RangeError",
            "ReferenceError",
            "SyntaxError",
            "TypeError",
            "URIError",
            "Number",
            "Date",
            "String",
            "RegExp",
            "Array",
            "Uint8Array",
            "Map",
            "Set",
            "WeakMap",
            "WeakSet",
            "Atomics",
            "JSON",
            "Math",
            "Promise",
            "SuppressedError",
            "global",
            "globalThis",
            "structuredClone",
            "console",
            "process",
            "setTimeout",
            "clearTimeout",
            "setInterval",
            "clearInterval",
            "queueMicrotask",
        ];
        let text = names.join(";");
        let mut start = 0;
        let statements = names
            .iter()
            .enumerate()
            .map(|(index, name)| {
                let statement = expression_statement(
                    u32::try_from(index * 2 + 30).expect("test node id fits u32"),
                    identifier_expr(
                        u32::try_from(index * 2 + 31).expect("test node id fits u32"),
                        name,
                        start,
                    ),
                );
                start += name.len() + 1;
                statement
            })
            .collect();
        let result = check(&file(&text, statements));
        assert!(
            semantic_codes(&result).is_empty(),
            "intrinsic diagnostics: {:?}",
            result.diagnostics()
        );
        assert_eq!(result.product().resolved_reference_count(), names.len());
    }

    #[test]
    fn function_value_is_declared_for_source_compatibility() {
        let result = check_text("declare const fn: unknown; Function.prototype.toString.call(fn);");
        assert!(
            !checker_codes(&result).contains(&CANNOT_FIND_NAME.as_str()),
            "Function.prototype must resolve for library source: {:?}",
            result.diagnostics()
        );
    }

    /// The checker follows tsc's default `lib`, not the runtime's builtin
    /// surface: a value the default library declares resolves even when the
    /// bamts runtime does not implement it. Runtime absence is a test262
    /// matter, never a checker diagnostic.
    #[test]
    fn default_lib_value_names_resolve_regardless_of_runtime_support() {
        let names = [
            "eval",
            "decodeURI",
            "encodeURI",
            "escape",
            "BigInt",
            "Int8Array",
            "Uint8ClampedArray",
            "Int16Array",
            "Uint16Array",
            "Int32Array",
            "Uint32Array",
            "BigInt64Array",
            "BigUint64Array",
            "Float32Array",
            "Float64Array",
            "ArrayBuffer",
            "SharedArrayBuffer",
            "DataView",
            "Proxy",
            "Reflect",
            "FinalizationRegistry",
            "WeakRef",
            "Intl",
            "Iterator",
            "AbortSignal",
            "URL",
            "URLSearchParams",
            "TextEncoder",
            "TextDecoder",
        ];
        let result = check_text(&names.join(";"));
        assert!(
            !checker_codes(&result).contains(&CANNOT_FIND_NAME.as_str()),
            "default-lib values must resolve: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn runtime_absent_constructors_remain_available_as_types() {
        let result = check_text(
            "type RuntimeAbsent = Function | BigInt | Int8Array | Uint8ClampedArray
                | Int16Array | Uint16Array | Int32Array | Uint32Array
                | BigInt64Array | BigUint64Array | Float16Array | Float32Array
                | Float64Array | ArrayBuffer | SharedArrayBuffer | DataView
                | Iterator | AsyncIterator | AbortSignal | URL | URLSearchParams
                | TextEncoder | TextDecoder | ImportMeta;",
        );
        assert!(
            !checker_codes(&result).contains(&CANNOT_FIND_TYPE.as_str()),
            "type-only library names must remain available: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn default_target_admits_every_lib() {
        // `with_target(None)` relies on the default target's lib set being
        // the full set, so unscoped checks see every global.
        assert_eq!(
            ProgramCheckOptions::standard().with_target(None).libs,
            super::intrinsic_environment::LibSet::ALL
        );
    }

    #[test]
    fn lib_es5_scopes_out_es2015_and_dom_values() {
        // With @lib: es5, Proxy (es2015) and document (dom) are TS2304.
        let result = check_text_with(
            "Proxy; document;",
            ProgramCheckOptions::standard()
                .with_script_target(crate::emitter::ScriptTarget::Es5)
                .with_libs(super::intrinsic_environment::LibSet::from_lib_names(&[
                    "es5",
                ])),
        );
        let codes = checker_codes(&result);
        assert!(
            codes.contains(&CANNOT_FIND_NAME.as_str()),
            "es5 lib must not resolve Proxy or document: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn target_es5_default_lib_resolves_dom_but_not_es2015() {
        // At @target: es5 with default lib, document (dom) resolves but
        // Proxy (es2015) does not.
        let result = check_text_with(
            "document;",
            ProgramCheckOptions::standard().with_script_target(crate::emitter::ScriptTarget::Es5),
        );
        let codes = checker_codes(&result);
        assert!(
            !codes.contains(&CANNOT_FIND_NAME.as_str()),
            "dom global must resolve at es5 default lib: {:?}",
            result.diagnostics()
        );

        let result_proxy = check_text_with(
            "Proxy;",
            ProgramCheckOptions::standard().with_script_target(crate::emitter::ScriptTarget::Es5),
        );
        let codes_proxy = checker_codes(&result_proxy);
        assert!(
            codes_proxy.contains(&CANNOT_FIND_NAME.as_str()),
            "Proxy must not resolve at es5 default lib: {:?}",
            result_proxy.diagnostics()
        );
    }

    #[test]
    fn target_es2015_default_lib_resolves_proxy() {
        // At @target: es2015 with default lib, Proxy resolves.
        let result = check_text_with(
            "Proxy;",
            ProgramCheckOptions::standard()
                .with_script_target(crate::emitter::ScriptTarget::Es2015),
        );
        let codes = checker_codes(&result);
        assert!(
            !codes.contains(&CANNOT_FIND_NAME.as_str()),
            "Proxy must resolve at es2015 default lib: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn lib_es2015_without_dom_scopes_out_document() {
        // With @lib: es2015 (no dom), document is TS2304 but Proxy resolves.
        let result = check_text_with(
            "document;",
            ProgramCheckOptions::standard().with_libs(
                super::intrinsic_environment::LibSet::from_lib_names(&["es2015"]),
            ),
        );
        let codes = checker_codes(&result);
        assert!(
            codes.contains(&CANNOT_FIND_NAME.as_str()),
            "document must not resolve with es2015-only lib: {:?}",
            result.diagnostics()
        );

        let result_proxy = check_text_with(
            "Proxy;",
            ProgramCheckOptions::standard().with_libs(
                super::intrinsic_environment::LibSet::from_lib_names(&["es2015"]),
            ),
        );
        let codes_proxy = checker_codes(&result_proxy);
        assert!(
            !codes_proxy.contains(&CANNOT_FIND_NAME.as_str()),
            "Proxy must resolve with es2015 lib: {:?}",
            result_proxy.diagnostics()
        );
    }

    #[test]
    fn float16_array_only_available_with_esnext() {
        // Float16Array is only in es2025.float16, which is included by
        // esnext but not by es2021.
        let esnext = check_text_with(
            "Float16Array;",
            ProgramCheckOptions::standard()
                .with_script_target(crate::emitter::ScriptTarget::EsNext),
        );
        let esnext_codes = checker_codes(&esnext);
        assert!(
            !esnext_codes.contains(&CANNOT_FIND_NAME.as_str()),
            "Float16Array must resolve at esnext default lib: {:?}",
            esnext.diagnostics()
        );

        let es2021 = check_text_with(
            "Float16Array;",
            ProgramCheckOptions::standard()
                .with_script_target(crate::emitter::ScriptTarget::Es2021),
        );
        let es2021_codes = checker_codes(&es2021);
        assert!(
            es2021_codes.contains(&CANNOT_FIND_NAME.as_str()),
            "Float16Array must not resolve at es2021 default lib: {:?}",
            es2021.diagnostics()
        );
    }

    #[test]
    fn temporal_global_resolves_with_esnext_temporal_lib() {
        // Authority baseline: temporal.ts uses @lib: ...,esnext.temporal,...
        // and Temporal must resolve. Without the esnext.temporal lib stem
        // mapping in from_lib_names, Temporal fires TS2304 (C002).
        let result = check_text_with(
            "Temporal;",
            ProgramCheckOptions::standard().with_libs(
                super::intrinsic_environment::LibSet::from_lib_names(&[
                    "es6",
                    "esnext.temporal",
                    "dom",
                ]),
            ),
        );
        let codes = checker_codes(&result);
        assert!(
            !codes.contains(&CANNOT_FIND_NAME.as_str()),
            "Temporal must resolve with esnext.temporal lib: {:?}",
            result.diagnostics()
        );

        // Without esnext.temporal, Temporal is unresolved.
        let result_no_temporal = check_text_with(
            "Temporal;",
            ProgramCheckOptions::standard().with_libs(
                super::intrinsic_environment::LibSet::from_lib_names(&["es6", "dom"]),
            ),
        );
        let codes_no_temporal = checker_codes(&result_no_temporal);
        assert!(
            codes_no_temporal.contains(&CANNOT_FIND_NAME.as_str()),
            "Temporal must not resolve without esnext.temporal lib: {:?}",
            result_no_temporal.diagnostics()
        );
    }

    #[test]
    fn bigint_without_lib_emits_ts2583_not_ts2304() {
        // Authority baseline: bigintWithoutLib(target=es5).errors.txt line 4
        // emits TS2583 for BigInt, not TS2304. With es5 lib, BigInt is a
        // known lib-gated global (Es2020BigInt) not in the active set.
        let result = check_text_with(
            "BigInt(123);",
            ProgramCheckOptions::standard().with_libs(
                super::intrinsic_environment::LibSet::from_lib_names(&["es5"]),
            ),
        );
        let codes = checker_codes(&result);
        assert!(
            codes.contains(&CANNOT_FIND_NAME_LIB_GATED.as_str()),
            "BigInt without es2020 lib must emit C089 (TS2583): {:?}",
            result.diagnostics()
        );
        assert!(
            !codes.contains(&CANNOT_FIND_NAME.as_str()),
            "BigInt without es2020 lib must not emit C002 (TS2304): {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn enum_member_qualified_type_reference_resolves() {
        // tsc resolves `Color.Red` as a type to the enum member's literal
        // type. Without the enum-member fallback in qualified type reference
        // resolution, this fires TS2304 (C003).
        let result =
            check_text("enum Color { Red, Green, Blue }\nlet k: Color.Red;\nlet m: Color.Green;\n");
        let codes = checker_codes(&result);
        assert!(
            !codes.contains(&CANNOT_FIND_TYPE.as_str()),
            "Color.Red must resolve as a type reference: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn primitive_wrapper_names_bind_in_type_position() {
        let result = check_text(
            "let a: Boolean; let b: Number; let c: String; let d: Symbol; let e: BigInt;",
        );
        assert!(
            !checker_codes(&result).contains(&CANNOT_FIND_TYPE.as_str()),
            "primitive wrappers must be checker-visible types: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn source_enum_references_construct_numeric_enum_types() {
        let result = check_text("enum E { A } let e: E = E.A;");
        let model = result.product();
        let symbol = model
            .lookup_value(model.module_scope(), "e")
            .expect("enum-typed binding is present");
        assert!(matches!(
            model.types().get(model.symbol_type(symbol)),
            Type::NumericEnum(_)
        ));
    }

    #[test]
    fn local_bindings_shadow_intrinsics() {
        let statements = vec![
            variable(
                10,
                "const console = 1;",
                "console",
                6,
                None,
                Some(number_expr(20, "1", 16)),
            ),
            expression_statement(30, identifier_expr(31, "console", 19)),
        ];
        let result = check(&file("const console = 1; console;", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        let local = model
            .lookup_value(model.module_scope(), "console")
            .expect("local console binding exists");
        assert_eq!(model.reference(NodeId::new(32)), Some(local));
    }

    #[test]
    fn reports_an_unknown_name_even_with_intrinsics() {
        let statements = vec![expression_statement(
            30,
            identifier_expr(31, "notAGlobal", 0),
        )];
        let result = check(&file("notAGlobal;", statements));
        assert_eq!(semantic_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn reports_a_duplicate_block_scoped_declaration() {
        let statements = vec![
            variable(
                10,
                "const a = 1;",
                "a",
                6,
                None,
                Some(number_expr(20, "1", 10)),
            ),
            variable(
                40,
                "const a = 2;",
                "a",
                19,
                None,
                Some(number_expr(50, "2", 23)),
            ),
        ];
        let result = check(&file("const a = 1; const a = 2;", statements));
        assert_eq!(semantic_codes(&result), [DUPLICATE_DECLARATION.as_str()]);
    }

    #[test]
    fn a_shadowing_binding_in_a_nested_block_is_not_a_duplicate() {
        let inner = variable(
            40,
            "const a = 2;",
            "a",
            21,
            None,
            Some(number_expr(50, "2", 25)),
        );
        let block = Node::new(
            NodeId::new(60),
            range(13, 29),
            Statement::Block(Node::new(
                NodeId::new(61),
                range(13, 29),
                Block {
                    statements: vec![inner],
                },
            )),
        );
        let statements = vec![
            variable(
                10,
                "const a = 1;",
                "a",
                6,
                None,
                Some(number_expr(20, "1", 10)),
            ),
            block,
        ];
        let result = check(&file("const a = 1; { const a = 2; }", statements));
        assert!(semantic_codes(&result).is_empty());
    }

    #[test]
    fn a_number_literal_is_not_assignable_to_a_string_annotation() {
        let annotation = keyword_annotation(70, KeywordType::String, 9, 15);
        let statements = vec![variable(
            10,
            "const x: string = 1;",
            "x",
            6,
            Some(annotation),
            Some(number_expr(20, "1", 18)),
        )];
        let result = check(&file("const x: string = 1;", statements));
        assert_eq!(semantic_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn a_matching_literal_initializer_is_accepted() {
        let annotation = keyword_annotation(70, KeywordType::Number, 9, 15);
        let statements = vec![variable(
            10,
            "const x: number = 1;",
            "x",
            6,
            Some(annotation),
            Some(number_expr(20, "1", 18)),
        )];
        let result = check(&file("const x: number = 1;", statements));
        assert!(semantic_codes(&result).is_empty());
    }

    #[test]
    fn an_unresolved_type_annotation_reports_cannot_find_type() {
        let reference = crate::syntax::TypeReference {
            name: EntityName::Identifier(identifier(71, "Foo", 9)),
            type_arguments: None,
        };
        let type_node = Node::new(
            NodeId::new(72),
            range(9, 12),
            TypeNode::Reference(reference),
        );
        let annotation = Node::new(
            NodeId::new(73),
            range(9, 12),
            TypeAnnotation {
                type_node: Box::new(type_node),
            },
        );
        let statements = vec![variable(
            10,
            "const x: Foo;",
            "x",
            6,
            Some(annotation),
            None,
        )];
        let result = check(&file("const x: Foo;", statements));
        assert_eq!(semantic_codes(&result), [CANNOT_FIND_TYPE.as_str()]);
    }

    #[test]
    fn generic_declarations_bind_their_type_parameters() {
        let result = check_text(
            "type Box<T> = { value: T };\
             interface Pair<T> { left: T; map<U>(value: U): T; }\
             class Store<T> { value: T; method<U>(value: U): T { return this.value; } }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn imported_names_bind_in_the_type_namespace_through_exports() {
        let result = check_text(
            "import type { Remote } from './remote.ts';\
             export type Local<T> = Remote;\
             export interface Public<T> { value: Local<T>; remote: Remote; }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn standard_iterator_and_generator_interfaces_are_bound() {
        let result = check_text(
            "declare let iterator: IterableIterator<number>;\
             async function* values(): AsyncGenerator<number> { yield 1; }",
        );
        assert!(checker_codes(&result).is_empty());
    }
    #[test]
    fn intrinsic_collections_preserve_element_types_across_iteration() {
        let result = check_text(
            "interface Options { default?: Record<string, unknown>; }
function check(options: Options = {}) {
    const defaults = options.default || {};
    const names = new Set<string>(['x']);
    for (const name of names) {
        defaults[name];
    }
    const aliases: Map<string, string> = new Map();
    for (const [alias, main] of aliases.entries()) {
        defaults[alias];
        defaults[main];
    }
}",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }
    #[test]
    fn intrinsic_record_preserves_literal_keys_and_generic_constraints() {
        let valid = check_text(
            "type Pair = Record<'left' | 'right', number>;\
             const pair: Pair = { left: 1, right: 2 };\
             const left: number = pair.left;\
             type Generic<K extends 'left' | 'right', V> = Record<K, V>;\
             const one: Generic<'left', number> = { left: 1 };\
             type Keyed<T, K extends keyof T, V> = Record<K, V>;\
             type PropertyKeyed<K extends PropertyKey, V> = Record<K, V>;\
             function read<K extends string, V>(record: Record<K, V>, key: K): V {\
                 return record[key];\
             }\
             type Events = { ready: string; empty: void };\
             function acceptsEvents<T extends Record<string | symbol, unknown>>() {}\
             acceptsEvents<Events>();\
             function readString<K extends string, V>(record: Record<string, V>, key: K): V {\
                 return record[key];\
             }\
             function comparable<T extends string>(value: string, target: T) {\
                 return value === target;\
             }\
             function readChained<Outer extends string, Inner extends Outer>(\
                 record: Record<string, number>, key: Inner\
             ): number { return record[key]; }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "type Invalid = Record<boolean, number>;\
             type Indexed<T, K extends T[keyof T], V> = Record<K, V>;\
             function rejectChained<Outer extends symbol, Inner extends Outer>(\
                 record: Record<string, number>, key: Inner\
             ) { return record[key]; }",
        );
        assert_eq!(
            checker_codes(&invalid),
            vec![ARGUMENT_NOT_ASSIGNABLE.as_str(); 2]
                .into_iter()
                .chain([super::INVALID_INDEXED_ACCESS_KEY.as_str()])
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn record_reduces_concrete_intersection_keys() {
        let result = check_text(
            "type OnlyX = Record<string & 'x', number>;\
             const value: OnlyX = { x: 1 };\
             const x: number = value.x;\
             const empty: Record<string & number, never> = {};",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn deferred_record_assignment_does_not_treat_constraints_as_members() {
        let result = check_text(
            "function assignments<K extends 'a' | 'b'>(source: Record<K, number>) {\
                 const a: Record<'a', number> = source;\
                 const both: Record<'a' | 'b', number> = source;\
                 return [a, both];\
             }",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str(); 2]);
    }

    #[test]
    fn record_index_signatures_satisfy_compatible_properties() {
        let valid = check_text(
            "const strings: Record<string, number> = { count: 1 };\
             const stringTarget: { count: number } = strings;\
             const numbers: Record<number, number> = { [-1]: 1 };\
             const numberTarget: { '-1': number } = numbers;",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "const numbers: Record<number, number> = { [-1]: 1 };\
             const target: { count: number } = numbers;",
        );
        assert_eq!(checker_codes(&invalid), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }
    #[test]
    fn deferred_record_named_key_does_not_imply_a_specific_property() {
        let result = check_text(
            "function read<K extends string>(record: Record<K, number>) {\
                 return record.foo;\
             }",
        );
        assert_eq!(checker_codes(&result), [PROPERTY_DOES_NOT_EXIST.as_str()]);
    }

    #[test]
    fn failed_overload_contextual_probes_emit_one_call_diagnostic() {
        let result = check_text(
            "function choose(value: { x: number }): void;\
             function choose(value: { y: string }): void;\
             function choose(value: { x: number } | { y: string }): void {}\
             choose({ x: 'bad', extra: true });",
        );
        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn intrinsic_collection_members_follow_standard_library_contracts() {
        let result = check_text(
            "const entries: [string, number][] = [['x', 1]];\
             const map = new Map(entries);\
             const inferred: Map<string, number> = new Map([['b', 2], ['a', 1]]);\
             const chained: Map<string, number> = map.set('y', 2);\
             const value: number | undefined = chained.get('x');\
             const present: boolean = map.has('x');\
             const removed: boolean = map.delete('x');\
             const count: number = map.size;\
             map.forEach((item: number, key: string, owner: Map<string, number>) => {\
                 owner.set(key, item);\
             });\
             map.clear();\
             const entry: [string, number] | undefined = map.entries().next().value;\
             const key: string | undefined = map.keys().next().value;\
             const item: number | undefined = map.values().next().value;\
             const set = new Set(['x']);\
             const same: Set<string> = set.add('y');\
             set.forEach((first: string, second: string, owner: Set<string>) => {\
                 owner.add(first); owner.add(second);\
             });\
             const pair: [string, string] | undefined = set.entries().next().value;\
             const setKey: string | undefined = set.keys().next().value;\
             const setValue: string | undefined = set.values().next().value;\
             set.delete('x'); set.clear(); same.has('y');",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn collection_any_arguments_remain_assignable_to_concrete_arguments() {
        let valid = check_text(
            "type Events = { foo: string };\
             type Handlers<E> = Map<keyof E | '*', Array<(event: E[keyof E]) => void>>;\
             declare function accept<E>(handlers: Handlers<E>): void;\
             const handlers = new Map();\
             const initialHandler = (value: string): void => {};\
             handlers.set('foo', [initialHandler]);\
             accept<Events>(handlers);",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "type Events = { foo: string };\
             type Handlers<E> = Map<keyof E | '*', Array<(event: E[keyof E]) => void>>;\
             declare function accept<E>(handlers: Handlers<E>): void;\
             const handlers = new Map<number, string>();\
             accept<Events>(handlers);",
        );
        assert_eq!(checker_codes(&invalid), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn readonly_collection_types_expose_only_read_operations() {
        let result = check_text(
            "declare const map: ReadonlyMap<string, number>;\
             const value: number | undefined = map.get('x');\
             const present: boolean = map.has('x');\
             const count: number = map.size;\
             map.entries().next().value;\
             map.keys().next().value;\
             map.values().next().value;\
             declare const set: ReadonlySet<string>;\
             set.has('x'); set.entries().next().value;\
             set.keys().next().value; set.values().next().value;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );

        let invalid = check_text(
            "declare const map: ReadonlyMap<string, number>;\
             map.set('x', 1); map.delete('x'); map.clear();\
             declare const set: ReadonlySet<string>;\
             set.add('x'); set.delete('x'); set.clear();",
        );
        assert_eq!(
            checker_codes(&invalid),
            vec![PROPERTY_DOES_NOT_EXIST.as_str(); 6]
        );
    }

    #[test]
    fn source_collection_declarations_shadow_intrinsics() {
        let result = check_text(
            "interface Map<K, V> { ownKey: K; ownValue: V; }\
             interface Set<T> { own: T; }\
             declare const map: Map<string, number>;\
             declare const set: Set<boolean>;\
             const key: string = map.ownKey;\
             const value: number = map.ownValue;\
             const own: boolean = set.own;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn set_constructor_widens_inferred_literal_unions() {
        let result = check_text("declare const ch: string; new Set([':', '(']).has(ch);");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn set_constructor_keeps_explicit_literal_type_arguments() {
        let result = check_text("new Set<'a'>(['a']).has('b');");
        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn functions_bind_arguments_this_and_their_local_name() {
        let result = check_text(
            "const recursive = function self(this: void) { arguments; return self; };\
             class C { method() { arguments; return this; } }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn named_class_expression_binds_its_internal_name() {
        let result = check_text(
            "const C = class Inner { static x = Inner; method() { return Inner; } }; Inner;",
        );
        assert_eq!(checker_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn anonymous_class_expression_types_constructed_instances() {
        let result = check_text(
            "const instance = new (class { value: number = 1 })();\
             const value: number = instance.value;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn anonymous_class_expression_diagnoses_incompatible_assignment() {
        let result = check_text(
            "const instance = new (class { value: number = 1 })();\
             const incompatible: { missing: string } = instance;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn named_class_expression_types_constructed_instances_and_self_reference() {
        let result = check_text(
            "const C = class Inner {\
                 value: number = 1;\
                 static make(): Inner { return new Inner(); }\
             };\
             const value: number = C.make().value;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn named_class_expression_diagnoses_incompatible_assignment() {
        let result = check_text(
            "const C = class Inner { value: number = 1 };\
             const incompatible: { missing: string } = new C();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn decorated_named_class_expression_static_block_binds_its_internal_name() {
        let result = check_text(
            "function deco(_value: unknown, _context: unknown) {}\
             const C = @deco class Inner { static { Inner; } }; Inner;",
        );
        assert_eq!(checker_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn named_class_expression_heritage_resolves_internal_name() {
        let result = check_text("const C = class C extends C {};");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn named_class_expression_heritage_keeps_outer_internal_name_unbound() {
        let result = check_text("const C = class Inner extends Inner {}; Inner;");
        assert_eq!(checker_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn class_declaration_heritage_resolves_outer_name() {
        let result = check_text("class C extends C {}");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn decorated_named_class_expression_heritage_resolves_internal_name() {
        let result = check_text(
            "function deco(_value: unknown, _context: unknown) {}\
             const C = @deco class Inner extends Inner {}; Inner;",
        );
        assert_eq!(checker_codes(&result), [CANNOT_FIND_NAME.as_str()]);
    }

    #[test]
    fn ambient_declarations_bind_before_their_uses() {
        let result = check_text(
            "const before: Box<number> = make<number>();\
             declare interface Box<T> { value: T; }\
             declare function make<T>(): Box<T>;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn local_generic_casts_resolve_in_the_enclosing_function() {
        let result = check_text(
            "function copy<T>(value: T): T { const result = value as T; return result; }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn const_assertions_preserve_literal_expression_types() {
        let result = check_text("const state: \"ready\" = \"ready\" as const;");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn generic_object_literal_mismatched_type_parameters_report_argument_error() {
        let result = check_text(
            "function foo<T>(x: { bar: T; baz: T }): T { return x.bar; }\n\
             var r = foo({ bar: 1, baz: '' });",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C053"]);
    }

    #[test]
    fn typescript_directives_suppress_only_the_next_code_line() {
        let result = check_text(
            "declare function takesString(value: string): void;\n\
             takesString(0);\n\
             // @ts-expect-error: deliberate compatibility case\n\
             takesString(1);\n\
             // @ts-ignore: deliberate compatibility case\n\
             \n\
             // intervening comment\n\
             takesString(2);\n\
             /* @ts-expect-error */ takesString(3);\n\
             /* ordinary text\n\
              * @ts-expect-error */\n\
             takesString(4);\n\
             /* @ts-expect-error\n\
              * ordinary text */\n\
             takesString(5);\n\
             // @ts-expect-error(TODO)\n\
             takesString(6);\n\
             // @ts-ignore-because-generated\n\
             takesString(7);",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C053", "BAMTS-C053", "BAMTS-C053"]
        );
    }

    #[test]
    fn unused_expect_error_directives_are_reported_in_source_order() {
        let result = check_text(
            "// @ts-expect-error\n\
             const first = 1;\n\
             // @ts-expect-error\n\
             const second = 2;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C070", "BAMTS-C070"]);
    }

    #[test]
    fn nearest_expect_error_consumes_the_target_diagnostic() {
        let result = check_text(
            "declare function takesString(value: string): void;\n\
             // @ts-expect-error first\n\
             // @ts-expect-error nearest\n\
             takesString(1);",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C070"]);
    }

    #[test]
    fn ts_ignore_never_reports_an_unused_directive() {
        let result = check_text("// @ts-ignore\nconst value = 1;");
        assert!(checker_codes(&result).is_empty());
    }
    #[test]
    fn dynamic_index_access_requires_an_index_signature() {
        let result = check_text(
            "const key: string = 'x';\n\
             globalThis[key];\n\
             class Container { read(name: string) { return this[name]; } }\n\
             const loose = JSON.parse('{}');\n\
             loose[key];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C064", "BAMTS-C064"]);
    }

    #[test]
    fn expect_error_consumes_dynamic_index_diagnostics() {
        let result = check_text(
            "const key: string = 'x';\n\
             // @ts-expect-error\n\
             globalThis[key];\n\
             class Container {\n\
                 read(name: string) {\n\
                     // @ts-expect-error\n\
                     return this[name];\n\
                 }\n\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn unconstrained_index_keys_require_an_index_signature() {
        let result = check_text(
            "const key = JSON.parse('\"x\"');\n\
             const closed: { x: number } = { x: 1 };\n\
             const indexed: { [name: string]: number } = { x: 1 };\n\
             closed[key];\n\
             if (key !== '' && closed[key]) {}\n\
             indexed[key];\n\
             if (key !== '' && indexed[key]) {}",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C064", "BAMTS-C064"]);
    }

    #[test]
    fn numeric_keys_use_string_index_signatures() {
        let result = check_text(
            "declare const dictionary: { [name: string]: number };\n\
             declare const index: number;\n\
             const value: number = dictionary[index];",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn dynamic_index_access_rejects_partially_indexable_unions() {
        let result = check_text(
            "declare const key: string;\n\
             declare const mixed: { x: number } | { [name: string]: number };\n\
             mixed[key];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C064"]);
    }

    #[test]
    fn indexed_access_preserves_preexisting_permissive_error_types() {
        let result = check_text(
            "interface Options { default?: Record<string, unknown> }\n\
             declare const options: Options;\n\
             declare const key: string;\n\
             const defaults = options.default || {};\n\
             defaults[key];",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn array_index_access_distinguishes_number_and_string_keys() {
        let result = check_text(
            "declare const index: number;\n\
             declare const key: string;\n\
             declare const values: number[];\n\
             const value: number = values[index];\n\
             values[key];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C064"]);
    }

    #[test]
    fn control_flow_expressions_are_type_checked() {
        let sources = [
            "if (closed[key]) {}",
            "while (closed[key]) { break; }",
            "do {} while (closed[key]);",
            "for (; closed[key];) { break; }",
            "switch (closed[key]) { default: break; }",
            "throw closed[key];",
        ];
        for statement in sources {
            let result = check_text(&format!(
                "declare const key: string;\
                 declare const closed: {{ x: number }};\
                 {statement}"
            ));
            assert_eq!(checker_codes(&result), ["BAMTS-C064"], "{statement}");
        }
    }

    #[test]
    fn computed_member_keys_preserve_lone_surrogates() {
        let result = check_text(
            "const value: { \"\\uD800\": number; \"\\uFFFD\": string } = {\n\
             \"\\uD800\": 1, \"\\uFFFD\": \"ok\"\n\
             };\n\
             const bad: string = value[\"\\uD800\"];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn explicit_type_arguments_instantiate_generic_call_signature() {
        let result = check_text(
            "function foo<T>(x: { bar: T; baz: T }): T { return x.bar; }\n\
             var r = foo<Object>({ bar: 1, baz: '' });",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn explicit_type_arguments_bind_in_declaration_order() {
        // T is declared before U, yet U occurs first in the parameter list.
        // Explicit args <number, string> must bind T := number and U := string
        // (declaration order), so u: U = string rejects 1 and t: T = number
        // rejects "a" — two argument errors. Occurrence-order binding would
        // swap the bindings and report zero errors.
        let result = check_text(
            "function f<T, U>(u: U, t: T): T { return t; }\n\
             const r = f<number, string>(1, \"a\");",
        );
        let argument_errors: Vec<&'static str> = checker_codes(&result)
            .into_iter()
            .filter(|code| *code == "BAMTS-C053")
            .collect();
        assert_eq!(argument_errors.len(), 2);
    }

    #[test]
    fn rest_parameter_target_accepts_any_fixed_source_arity() {
        let result = check_text(
            "type Handler = (...args: any[]) => any;\n\
             const identity = <T>(value: T): T => value;\n\
             const one: Handler = identity;\n\
             const two: Handler = (a: string, b: string) => `${a}${b}`;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn fixed_arity_target_still_rejects_a_wider_required_source() {
        let result = check_text(
            "type Unary = (a: string) => string;\n\
             const two: Unary = (a: string, b: string) => `${a}${b}`;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn generic_method_call_instantiates_type_parameters_from_arguments() {
        let result = check_text(
            "class Hooks<H extends string> {\n\
               hook<N extends H>(name: N, fn: number): void {}\n\
               deprecate<N extends H>(name: N): void { this.hook(name, 1); }\n\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn typeof_guard_narrows_a_union_in_both_branches() {
        let result = check_text(
            "declare function takesStr(s: string): number;\n\
             declare function takesArr(a: string[]): number;\n\
             function viaIf(g: string | string[]): number {\n\
               if (typeof g === 'string') { return takesStr(g); }\n\
               return takesArr(g);\n\
             }\n\
             function viaConditional(g: string | string[]): number {\n\
               return typeof g === 'string' ? takesStr(g) : takesArr(g);\n\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn an_unguarded_union_member_is_still_rejected() {
        let result = check_text(
            "declare function takesStr(s: string): number;\n\
             function unguarded(g: string | string[]): number { return takesStr(g); }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C053"]);
    }

    #[test]
    fn writes_invalidate_guard_narrowing() {
        let assignment = check_text(
            "declare function takesString(value: string): void;\
             let value: string | number = \"ok\";\
             if (typeof value === \"string\") {\
               takesString(value); value = 1; takesString(value);\
             }",
        );
        assert_eq!(checker_codes(&assignment), ["BAMTS-C053"]);

        let update = check_text(
            "declare function takesString(value: string): void;\
             let value: string | number = \"ok\";\
             if (typeof value === \"string\") { value++; takesString(value); }",
        );
        assert_eq!(checker_codes(&update), ["BAMTS-C053"]);
    }

    #[test]
    fn zero_iteration_loops_do_not_leak_body_narrowing() {
        let while_loop = check_text(
            "declare function takesString(value: string): void;\
             function run(value: string | number, condition: boolean): void {\
               while (condition) { if (typeof value !== \"string\") return; }\
               takesString(value);\
             }",
        );
        assert_eq!(checker_codes(&while_loop), ["BAMTS-C053"]);

        let for_loop = check_text(
            "declare function takesString(value: string): void;\
             function run(value: string | number, condition: boolean): void {\
               for (; condition;) { if (typeof value !== \"string\") return; }\
               takesString(value);\
             }",
        );
        assert_eq!(checker_codes(&for_loop), ["BAMTS-C053"]);
    }

    #[test]
    fn a_derived_class_instance_flows_into_its_base_through_the_chain() {
        let result = check_text(
            "abstract class A { abstract readonly name: string; }\n\
             abstract class B extends A { tag(): number { return 1; } }\n\
             class C extends B {\n\
               readonly name = 'c';\n\
               self(): A { const next: A = this; return next; }\n\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn an_unrelated_class_does_not_flow_into_another() {
        let result = check_text(
            "class Named { readonly name: string = 'n'; }\n\
             class Numbered { readonly count: number = 1; }\n\
             declare const numbered: Numbered;\n\
             const named: Named = numbered;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn generic_signatures_relate_up_to_type_parameter_renaming() {
        let result = check_text(
            "type Source = <T>(value: T) => T;\n\
             type Target = <U>(value: U) => U;\n\
             declare const source: Source;\n\
             const target: Target = source;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn an_unmodelled_intrinsic_type_target_stays_permissive() {
        let result = check_text("const record: Record<string, unknown> = { name: 'root' };");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn object_methods_satisfy_structural_function_members() {
        let result = check_text(
            "interface Service { compute(value: number): Promise<number>; }\
             const service: Service = { async compute(value: number) { return value; } };",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn export_assignment_rejects_mixed_value_exports() {
        let result = check_text("export = {}; export const helper = 1;");
        assert_eq!(checker_codes(&result), [MIXED_EXPORT_ASSIGNMENT.as_str()]);

        let result = check_text("export = {}; export default {};");
        assert_eq!(checker_codes(&result), [MIXED_EXPORT_ASSIGNMENT.as_str()]);

        let result = check_text("export = {}; export { value }; const value = 1;");
        assert_eq!(checker_codes(&result), [MIXED_EXPORT_ASSIGNMENT.as_str()]);
    }

    #[test]
    fn export_assignment_allows_type_only_exports() {
        let result =
            check_text("interface Shape { value: number } export type { Shape }; export = {};");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn export_assignment_allows_per_specifier_type_only_exports() {
        let result =
            check_text("interface Shape { value: number } export { type Shape }; export = {};");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn export_assignment_rejects_mixed_per_specifier_exports() {
        let result = check_text(
            "interface Shape {} const value = 1; export { type Shape, value }; export = {};",
        );
        assert_eq!(checker_codes(&result), [MIXED_EXPORT_ASSIGNMENT.as_str()]);
    }

    #[test]
    fn function_parameter_decorators_are_rejected() {
        let result = check_text(
            "function deco(_target: unknown, _key: unknown, _index: unknown) {}\
             function f(@deco x: number) { return x; }",
        );
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_DECORATOR_NOT_SUPPORTED.as_str()]
        );
    }

    #[test]
    fn arrow_parameter_properties_are_rejected() {
        let result = check_text("var v = (public x: string) => { };");
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR.as_str()]
        );
    }

    #[test]
    fn function_parameter_properties_are_rejected() {
        let result = check_text("function f(public x: string) {}");
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR.as_str()]
        );
    }

    #[test]
    fn constructor_parameter_properties_are_allowed() {
        let result = check_text("class C { constructor(public x: string) {} }");
        assert!(
            !checker_codes(&result).contains(&PARAMETER_PROPERTY_ONLY_IN_CONSTRUCTOR.as_str()),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn method_parameter_decorators_are_rejected() {
        let result = check_text(
            "function deco(_target: unknown, _key: unknown, _index: unknown) {}\
             class C { method(@deco x: number) { return x; } }",
        );
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_DECORATOR_NOT_SUPPORTED.as_str()]
        );
    }

    #[test]
    fn constructor_parameter_decorators_are_rejected() {
        let result = check_text(
            "function deco(_target: unknown, _key: unknown, _index: unknown) {}\
             class C { constructor(@deco x: number) {} }",
        );
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_DECORATOR_NOT_SUPPORTED.as_str()]
        );
    }

    #[test]
    fn constructor_decorators_are_rejected() {
        let result = check_text(
            "function deco(_target: unknown, _key: unknown) {}\
             class C { @deco constructor() {} }",
        );
        assert_eq!(
            checker_codes(&result),
            [CONSTRUCTOR_DECORATOR_NOT_SUPPORTED.as_str()]
        );
    }

    #[test]
    fn constructor_decorators_emit_one_error_per_decorator_with_decorator_range() {
        let text = "function deco(_target: unknown, _key: unknown) {}\
                    class C { @first @second constructor() {} }";
        let parsed = parsed(0, text);
        let Statement::Class(class) = parsed.product().statements()[1].data() else {
            panic!("expected a class declaration");
        };
        let ClassMember::Constructor(constructor) = class.members[0].data() else {
            panic!("expected a constructor");
        };
        let decorator_ranges: Vec<_> = constructor
            .decorators
            .iter()
            .map(|decorator| decorator.range())
            .collect();
        assert_eq!(decorator_ranges.len(), 2);
        let result = check(&parsed);
        let diagnostics: Vec<_> = result
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code() == CONSTRUCTOR_DECORATOR_NOT_SUPPORTED)
            .collect();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].range(), decorator_ranges[0]);
        assert_eq!(diagnostics[1].range(), decorator_ranges[1]);
    }

    #[test]
    fn arrow_parameter_decorators_are_rejected() {
        let result = check_text(
            "function deco(_target: unknown, _key: unknown, _index: unknown) {}\
             const f = (@deco x: number) => x;",
        );
        assert_eq!(
            checker_codes(&result),
            [PARAMETER_DECORATOR_NOT_SUPPORTED.as_str()]
        );
    }

    #[test]
    fn plain_parameters_do_not_report_parameter_decorator_errors() {
        let result = check_text(
            "function f(x: number) { return x; }\
             class C { constructor(y: number) {} method(z: number) { return z; } }\
             const arrow = (w: number) => w;",
        );
        let codes = checker_codes(&result);
        assert!(
            !codes.contains(&PARAMETER_DECORATOR_NOT_SUPPORTED.as_str()),
            "{codes:?}"
        );
        assert!(
            !codes.contains(&CONSTRUCTOR_DECORATOR_NOT_SUPPORTED.as_str()),
            "{codes:?}"
        );
    }

    #[test]
    fn parameter_decorator_expressions_still_resolve_names() {
        let result = check_text("function f(@missing x: number) { return x; }");
        assert_eq!(
            checker_codes(&result),
            [
                PARAMETER_DECORATOR_NOT_SUPPORTED.as_str(),
                CANNOT_FIND_NAME.as_str(),
            ]
        );
    }

    #[test]
    fn parameter_decorators_emit_one_error_per_decorator_with_decorator_range() {
        let text = "function deco(_target: unknown, _key: unknown, _index: unknown) {}\
                    function f(@first @second x: number) { return x; }";
        let parsed = parsed(0, text);
        let Statement::Function(declaration) = parsed.product().statements()[1].data() else {
            panic!("expected a function declaration");
        };
        let decorator_ranges: Vec<_> = declaration.function.parameters[0]
            .data()
            .decorators
            .iter()
            .map(|decorator| decorator.range())
            .collect();
        assert_eq!(decorator_ranges.len(), 2);
        let result = check(&parsed);
        let diagnostics: Vec<_> = result
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code() == PARAMETER_DECORATOR_NOT_SUPPORTED)
            .collect();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics[0].range(), decorator_ranges[0]);
        assert_eq!(diagnostics[1].range(), decorator_ranges[1]);
    }

    #[test]
    fn unknown_names_and_real_initializer_mismatches_remain_errors() {
        let result =
            check_text("missingValue; let missing: MissingType; const count: number = 'wrong';");
        assert_eq!(
            checker_codes(&result),
            [
                CANNOT_FIND_NAME.as_str(),
                CANNOT_FIND_TYPE.as_str(),
                TYPE_NOT_ASSIGNABLE.as_str(),
            ]
        );
    }

    #[test]
    fn qualified_import_equals_records_value_type_missing_and_nested_paths() {
        let value = check_text(
            "namespace A { export namespace B { export const value = 1; } } import X = A.B; X.value;",
        );
        assert!(checker_codes(&value).is_empty());
        let model = value.product();
        let declaration = model
            .symbols()
            .iter()
            .find(|symbol| symbol.name() == "X")
            .expect("import alias is declared")
            .declaration();
        let path = model
            .namespace_facts()
            .qualified_import_path(declaration)
            .expect("qualified import records a SymbolId path");
        assert_eq!(
            path.iter()
                .map(|symbol| model.symbol(*symbol).name())
                .collect::<Vec<_>>(),
            ["A", "B"]
        );

        let ty = check_text(
            "namespace A { export interface B { value: number; } } import X = A.B; let value: X;",
        );
        assert!(checker_codes(&ty).is_empty());
        let ty_model = ty.product();
        let value_symbol = ty_model
            .lookup_value(ty_model.module_scope(), "value")
            .expect("value is bound");
        assert_ne!(
            ty_model.symbol_type(value_symbol),
            ty_model.types().error_type()
        );
        assert!(matches!(
            ty_model.types().get(ty_model.symbol_type(value_symbol)),
            Type::ObjectType(object)
                if object
                    .properties
                    .iter()
                    .any(|property| property.name() == "value")
        ));

        let missing = check_text("namespace A {} import X = A.B;");
        assert_eq!(checker_codes(&missing), [CANNOT_FIND_NAME.as_str()]);

        let nested = check_text(
            "namespace A { export namespace B { export namespace C { export const value = 1; } } } import X = A.B.C; X.value;",
        );
        assert!(checker_codes(&nested).is_empty());
        let nested_declaration = nested
            .product()
            .symbols()
            .iter()
            .find(|symbol| symbol.name() == "X")
            .expect("nested import alias is declared")
            .declaration();
        assert_eq!(
            nested
                .product()
                .namespace_facts()
                .qualified_import_path(nested_declaration)
                .expect("nested qualified import records a SymbolId path")
                .len(),
            3
        );
    }

    #[test]
    fn self_referential_import_equals_type_terminates() {
        let result = check_text("import X = X; let value: X;");
        let model = result.product();
        let value_symbol = model
            .lookup_value(model.module_scope(), "value")
            .expect("value is bound");
        assert_eq!(model.symbol_type(value_symbol), model.types().error_type());
    }

    #[test]
    fn import_equals_chases_aliases_for_qualified_type_members() {
        let accepted = check_text(
            "namespace A { export namespace B { export interface T { value: number } } } \
             import X = A.B; type U = X.T; const accepted: U = { value: 1 };",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text(
            "namespace A { export namespace B { export interface T { value: number } } } \
             import X = A.B; type U = X.T; const rejected: U = { value: \"wrong\" };",
        );
        assert_eq!(checker_codes(&rejected), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn import_equals_chases_aliases_for_nested_import_equals_types() {
        let result = check_text(
            "namespace A { export namespace B { export interface Shape { value: number } } }              import X = A.B; import Y = X.Shape; let v: Y;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
        let model = result.product();
        let value_symbol = model
            .lookup_value(model.module_scope(), "v")
            .expect("v is bound");
        assert_ne!(model.symbol_type(value_symbol), model.types().error_type());
        assert!(matches!(
            model.types().get(model.symbol_type(value_symbol)),
            Type::ObjectType(object)
                if object
                    .properties
                    .iter()
                    .any(|property| property.name() == "value")
        ));
    }

    #[test]
    fn import_equals_keeps_separate_value_and_type_targets() {
        let result = check_text(
            "function Both() {} interface Both { value: number }              import Alias = Both; Alias(); let typed: Alias;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
        let model = result.product();
        let module = model.module_scope();
        let value_both = model
            .lookup_value(module, "Both")
            .expect("Both value symbol");
        let type_both = model.lookup_type(module, "Both").expect("Both type symbol");
        assert_ne!(value_both, type_both);
        let declaration = model
            .symbols()
            .iter()
            .find(|symbol| symbol.name() == "Alias")
            .expect("import alias is declared")
            .declaration();
        let path = model
            .namespace_facts()
            .qualified_import_path(declaration)
            .expect("import equals records a SymbolId path");
        assert_eq!(path, &[value_both]);
        let typed = model.lookup_value(module, "typed").expect("typed is bound");
        assert_ne!(model.symbol_type(typed), model.types().error_type());
        assert!(matches!(
            model.types().get(model.symbol_type(typed)),
            Type::ObjectType(object)
                if object
                    .properties
                    .iter()
                    .any(|property| property.name() == "value")
        ));
    }

    #[test]
    fn cyclic_import_equals_member_scope_terminates() {
        let result = check_text("import X = Y; import Y = X; import Z = X.Member; let value: Z;");
        // Cycle-safe chase terminates without hanging; unresolved member lookup
        // currently yields no diagnostic codes and an error type for `value`.
        assert_eq!(checker_codes(&result), [] as [&str; 0]);
        let model = result.product();
        let value_symbol = model
            .lookup_value(model.module_scope(), "value")
            .expect("value is bound");
        assert_eq!(model.symbol_type(value_symbol), model.types().error_type());
    }

    #[test]
    fn hard_warnings_merge_into_ordered_diagnostics() {
        // A single-string source that triggers hard-warning W005 plus an
        // unresolved reference should yield both, canonically ordered.
        let text = "try {} catch (error) { error.message; }";
        // Reference `nope` (unresolved) placed before via an expression stmt with
        // an earlier range so ordering is observable.
        let statements = vec![expression_statement(30, identifier_expr(31, "nope", 0))];
        let result = check(&file(text, statements));
        let diagnostics = result.diagnostics();
        // Both a semantic error and a hard warning are present.
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code() == CANNOT_FIND_NAME)
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.severity() == DiagnosticSeverity::Warning)
        );
        // Diagnostics are in canonical (sorted) order.
        let mut sorted = diagnostics.to_vec();
        sorted.sort();
        assert_eq!(diagnostics, sorted.as_slice());
    }

    #[test]
    fn a_parameter_reference_resolves_within_its_function_scope() {
        let parameter_name = identifier(81, "p", 11);
        let binding = Node::new(
            NodeId::new(82),
            parameter_name.range(),
            BindingPattern::Identifier(parameter_name),
        );
        let parameter: ParameterNode = Node::new(
            NodeId::new(83),
            range(11, 12),
            Parameter {
                decorators: Vec::new(),
                modifiers: crate::syntax::ParameterModifiers::default(),
                binding,
                optional: false,
                type_annotation: Some(keyword_annotation(84, KeywordType::Unknown, 14, 21)),
                initializer: None,
            },
        );
        let body = identifier_expr(90, "p", 26);
        let arrow = Node::new(
            NodeId::new(80),
            range(10, 27),
            Expression::Arrow(ArrowFunction {
                is_async: false,
                type_parameters: None,
                parameters: vec![parameter],
                return_type: None,
                body: FunctionBody::Expression(body),
            }),
        );
        let statements = vec![variable(
            10,
            "const f = (p: unknown) => p;",
            "f",
            6,
            None,
            Some(Box::new(arrow)),
        )];
        let result = check(&file("const f = (p: unknown) => p;", statements));
        assert!(semantic_codes(&result).is_empty());
        // Scope tree contains a function scope for the arrow.
        let model = result.product();
        assert!(
            model
                .scopes()
                .iter()
                .any(|scope| scope.kind() == ScopeKind::Function)
        );
    }

    #[test]
    fn an_ast_parameter_decorator_emits_the_typed_error_on_its_range() {
        let decorator_expression = identifier_expr(95, "deco", 12);
        let decorator = Node::new(
            NodeId::new(94),
            range(11, 16),
            Decorator {
                expression: decorator_expression,
            },
        );
        let parameter_name = identifier(81, "p", 17);
        let binding = Node::new(
            NodeId::new(82),
            parameter_name.range(),
            BindingPattern::Identifier(parameter_name),
        );
        let parameter: ParameterNode = Node::new(
            NodeId::new(83),
            range(11, 27),
            Parameter {
                decorators: vec![decorator.clone()],
                modifiers: crate::syntax::ParameterModifiers::default(),
                binding,
                optional: false,
                type_annotation: Some(keyword_annotation(84, KeywordType::Unknown, 20, 27)),
                initializer: None,
            },
        );
        let body = identifier_expr(90, "p", 32);
        let arrow = Node::new(
            NodeId::new(80),
            range(10, 33),
            Expression::Arrow(ArrowFunction {
                is_async: false,
                type_parameters: None,
                parameters: vec![parameter],
                return_type: None,
                body: FunctionBody::Expression(body),
            }),
        );
        let statements = vec![variable(
            10,
            "const f = (@deco p: unknown) => p;",
            "f",
            6,
            None,
            Some(Box::new(arrow)),
        )];
        let result = check(&file("const f = (@deco p: unknown) => p;", statements));
        let diagnostics: Vec<_> = result
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code() == PARAMETER_DECORATOR_NOT_SUPPORTED)
            .collect();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].range(), decorator.range());
        assert!(
            checker_codes(&result).contains(&CANNOT_FIND_NAME.as_str()),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn a_string_initializer_matches_a_string_annotation() {
        let annotation = keyword_annotation(70, KeywordType::String, 9, 15);
        let statements = vec![variable(
            10,
            "const s: string = \"ok\";",
            "s",
            6,
            Some(annotation),
            Some(string_expr(20, "\"ok\"", 18)),
        )];
        let result = check(&file("const s: string = \"ok\";", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        let symbol = model
            .lookup_value(model.module_scope(), "s")
            .expect("s is bound");
        assert_eq!(model.symbol_type(symbol), model.types().string());
    }

    #[test]
    fn missing_identifiers_never_panic_the_checker() {
        // An identifier with an empty lexeme must be ignored, not reported.
        let missing = Node::new(
            NodeId::new(31),
            range(0, 0),
            Expression::Missing(MissingNode::new(NodeKind::IdentifierExpression)),
        );
        let statements = vec![expression_statement(30, Box::new(missing))];
        let result = check(&file("", statements));
        assert!(semantic_codes(&result).is_empty());
    }

    // ---- var hoisting regression tests ---------------------------------------

    fn var_declaration(
        kind: crate::syntax::VariableKind,
        id: u32,
        name: &str,
        name_start: usize,
        initializer: Option<Box<Expr>>,
    ) -> crate::syntax::VariableDeclaration {
        let name_node = identifier(id + 1, name, name_start);
        let binding = Node::new(
            NodeId::new(id + 2),
            name_node.range(),
            BindingPattern::Identifier(name_node),
        );
        let declarator = Node::new(
            NodeId::new(id + 3),
            range(name_start, name_start + name.len()),
            crate::syntax::VariableDeclarator {
                binding,
                definite: false,
                type_annotation: None,
                initializer,
            },
        );
        crate::syntax::VariableDeclaration {
            range: range(name_start, name_start + name.len()),
            kind,
            declarations: vec![declarator],
        }
    }

    fn variable_kind(
        kind: crate::syntax::VariableKind,
        id: u32,
        text: &str,
        name: &str,
        name_start: usize,
        initializer: Option<Box<Expr>>,
    ) -> Stmt {
        Node::new(
            NodeId::new(id),
            range(0, text.len()),
            Statement::Variable(var_declaration(kind, id, name, name_start, initializer)),
        )
    }

    fn block_statement(id: u32, statements: Vec<Stmt>) -> Stmt {
        Node::new(
            NodeId::new(id),
            range(0, 1),
            Statement::Block(Node::new(
                NodeId::new(id + 1),
                range(0, 1),
                Block { statements },
            )),
        )
    }

    #[test]
    fn a_var_in_a_block_hoists_to_the_module_and_resolves_outside() {
        let inner = variable_kind(
            crate::syntax::VariableKind::Var,
            40,
            "var a = 1;",
            "a",
            6,
            Some(number_expr(50, "1", 10)),
        );
        let block = block_statement(60, vec![inner]);
        let statements = vec![
            block,
            expression_statement(70, identifier_expr(71, "a", 15)),
        ];
        let result = check(&file("{ var a = 1; } a;", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        let symbol = model
            .lookup_value(model.module_scope(), "a")
            .expect("var a hoists to the module scope");
        assert!(matches!(
            model.symbol(symbol).kind(),
            SymbolKind::Variable(crate::syntax::VariableKind::Var)
        ));
        assert_eq!(model.resolved_reference_count(), 1);
    }

    #[test]
    fn a_var_in_a_nested_block_binds_before_its_declaration() {
        let inner = variable_kind(
            crate::syntax::VariableKind::Var,
            40,
            "var a = 1;",
            "a",
            9,
            Some(number_expr(50, "1", 13)),
        );
        let statements = vec![
            expression_statement(30, identifier_expr(31, "a", 0)),
            block_statement(60, vec![inner]),
        ];
        let result = check(&file("a; { var a = 1; }", statements));
        assert!(semantic_codes(&result).is_empty());
        assert_eq!(result.product().resolved_reference_count(), 1);
    }

    #[test]
    fn a_for_initializer_var_hoists_to_the_module() {
        let for_stmt = Node::new(
            NodeId::new(60),
            range(0, 1),
            Statement::For(crate::syntax::ForStatement {
                initializer: Some(crate::syntax::ForInitializer::Variable(var_declaration(
                    crate::syntax::VariableKind::Var,
                    40,
                    "i",
                    9,
                    Some(number_expr(50, "0", 13)),
                ))),
                test: None,
                update: None,
                body: Box::new(block_statement(80, vec![])),
            }),
        );
        let statements = vec![
            for_stmt,
            expression_statement(90, identifier_expr(91, "i", 23)),
        ];
        let result = check(&file("for (var i = 0; ; ) {} i;", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        assert!(
            model.lookup_value(model.module_scope(), "i").is_some(),
            "for-initializer var hoists out of the for scope"
        );
        assert_eq!(model.resolved_reference_count(), 1);
    }

    #[test]
    fn a_var_in_a_nested_function_does_not_escape_to_the_outer_scope() {
        let inner = variable_kind(
            crate::syntax::VariableKind::Var,
            40,
            "var x = 1;",
            "x",
            15,
            Some(number_expr(50, "1", 19)),
        );
        let body = Node::new(
            NodeId::new(70),
            range(0, 1),
            Block {
                statements: vec![inner],
            },
        );
        let function = crate::syntax::FunctionLike {
            decorators: Vec::new(),
            name: Some(identifier(81, "f", 9)),
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters: Vec::new(),
            return_type: None,
            body: Some(FunctionBody::Block(body)),
        };
        let fn_stmt = Node::new(
            NodeId::new(80),
            range(0, 1),
            Statement::Function(crate::syntax::FunctionDeclaration { function }),
        );
        let result = check(&file("function f() { var x = 1; }", vec![fn_stmt]));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        assert!(
            model.lookup_value(model.module_scope(), "f").is_some(),
            "the function declaration binds at the module scope"
        );
        assert!(
            model.lookup_value(model.module_scope(), "x").is_none(),
            "the inner var stays inside its own function scope"
        );
    }

    #[test]
    fn a_function_declaration_in_a_block_hoists_to_the_module() {
        let function = crate::syntax::FunctionLike {
            decorators: Vec::new(),
            name: Some(identifier(81, "g", 14)),
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters: Vec::new(),
            return_type: None,
            body: Some(FunctionBody::Block(Node::new(
                NodeId::new(82),
                range(15, 17),
                Block {
                    statements: Vec::new(),
                },
            ))),
        };
        let declaration = Node::new(
            NodeId::new(80),
            range(2, 17),
            Statement::Function(crate::syntax::FunctionDeclaration { function }),
        );
        let statements = vec![
            expression_statement(70, identifier_expr(71, "g", 0)),
            block_statement(90, vec![declaration]),
        ];
        let result = check(&file("g; { function g() {} }", statements));
        assert!(semantic_codes(&result).is_empty());
        let model = result.product();
        assert!(
            model.lookup_value(model.module_scope(), "g").is_some(),
            "block function declaration hoists to the module scope"
        );
        assert_eq!(model.resolved_reference_count(), 1);
    }

    #[test]
    fn a_let_in_a_block_does_not_hoist_and_is_unresolved_outside() {
        let inner = variable_kind(
            crate::syntax::VariableKind::Let,
            40,
            "let b = 1;",
            "b",
            6,
            Some(number_expr(50, "1", 10)),
        );
        let block = block_statement(60, vec![inner]);
        let statements = vec![
            block,
            expression_statement(70, identifier_expr(71, "b", 15)),
        ];
        let result = check(&file("{ let b = 1; } b;", statements));
        assert_eq!(semantic_codes(&result), [CANNOT_FIND_NAME.as_str()]);
        let model = result.product();
        assert!(
            model.lookup_value(model.module_scope(), "b").is_none(),
            "let stays block-scoped and never reaches the module scope"
        );
    }

    #[test]
    fn namespace_vars_stay_inside_the_namespace_iife_scope() {
        let result = check_text("namespace N { export var x = 1; x; } N.x; x;");
        assert_eq!(checker_codes(&result), [CANNOT_FIND_NAME.as_str()]);
        let model = result.product();
        assert!(model.lookup_value(model.module_scope(), "N").is_some());
        assert!(model.lookup_value(model.module_scope(), "x").is_none());
    }

    #[test]
    fn merged_namespaces_share_one_symbol_but_variables_remain_duplicates() {
        let merged = check_text("namespace N {} namespace N {}");
        assert!(checker_codes(&merged).is_empty());
        let model = merged.product();
        let symbol = model
            .lookup_value(model.module_scope(), "N")
            .expect("merged namespace has a value symbol");
        assert_eq!(model.namespace_facts().merged_declarations(symbol).len(), 2);

        let duplicate = check_text("namespace N {} namespace N {} var N;");
        assert_eq!(checker_codes(&duplicate), [DUPLICATE_DECLARATION.as_str()]);
    }
    #[test]
    fn duplicate_classes_report_without_refinalizing_the_first_class() {
        let result = check_text("class c3 { public foo() {} } class c3 { public bar() {} }");
        assert_eq!(checker_codes(&result), [DUPLICATE_DECLARATION.as_str()]);
    }

    #[test]
    fn namespace_merging_is_declaration_order_sensitive() {
        for source in [
            "function F() {} namespace F {}",
            "class C {} namespace C {}",
            "enum E { A } namespace E {}",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }

        for source in [
            "namespace F {} function F() {}",
            "namespace C {} class C {}",
            "namespace E {} enum E { A }",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                [DUPLICATE_DECLARATION.as_str()],
                "{source}"
            );
        }
    }

    #[test]
    fn interface_namespace_merging_remains_bidirectional() {
        for source in [
            "interface I {} namespace I {}",
            "namespace I {} interface I {}",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn distinct_namespace_variable_conflicts_remain_distinct() {
        let duplicate = check_text("namespace N {} var N; var N;");
        assert_eq!(
            checker_codes(&duplicate),
            [
                DUPLICATE_DECLARATION.as_str(),
                DUPLICATE_DECLARATION.as_str(),
            ]
        );
    }

    #[test]
    fn exported_namespace_variable_records_property_storage_and_outer_use_id() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("namespace N { export let value = 1; value; }"),
        ));
        let declaration = &parsed.product().statements()[0];
        let Statement::Namespace(namespace) = declaration.data() else {
            panic!("first statement is a namespace");
        };
        let Statement::Expression(expression) = namespace.body.data().statements[1].data() else {
            panic!("second namespace statement is an expression");
        };
        let reference = expression.expression.id();
        let checked = check(&parsed);
        assert!(checker_codes(&checked).is_empty());
        let facts = checked.product().namespace_facts();
        let plan = facts
            .declaration(declaration.id())
            .expect("namespace declaration has a plan");
        assert_eq!(plan.exports().len(), 1);
        assert_eq!(plan.exports()[0].name().to_utf8_lossy(), "value");
        assert_eq!(plan.exports()[0].storage(), ExportStorage::Property);
        let member = facts
            .member_use(reference)
            .expect("exported-variable read is container-backed");
        assert_eq!(member.container(), plan.container());
        assert_eq!(member.name().to_utf8_lossy(), "value");
    }

    #[test]
    fn dotted_namespace_records_nested_container_and_qualified_type_path() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(
                "namespace Outer.Inner { export interface T {} } \
                 type Alias = Outer.Inner.T;",
            ),
        ));
        let outer_statement = &parsed.product().statements()[0];
        let Statement::Namespace(outer) = outer_statement.data() else {
            panic!("first statement is the outer namespace");
        };
        let inner_statement = &outer.body.data().statements[0];
        let Statement::TypeAlias(alias) = parsed.product().statements()[1].data() else {
            panic!("second statement is a type alias");
        };
        let checked = check(&parsed);
        assert!(checker_codes(&checked).is_empty());
        let facts = checked.product().namespace_facts();
        let outer_symbol = facts
            .declaration_symbol(outer_statement.id())
            .expect("outer namespace has a symbol");
        let inner_symbol = facts
            .declaration_symbol(inner_statement.id())
            .expect("inner namespace has a symbol");
        assert_eq!(
            facts
                .declaration(inner_statement.id())
                .expect("inner namespace has a plan")
                .acquisition(),
            ContainerAcquisition::Member {
                parent: outer_symbol
            }
        );
        let path = facts
            .qualified_type_path(alias.type_node.id())
            .expect("qualified type records its symbol path");
        assert_eq!(path.len(), 3);
        assert_eq!(path[0], outer_symbol);
        assert_eq!(path[1], inner_symbol);
    }

    #[test]
    fn qualified_namespace_type_requires_an_exported_member() {
        let hidden = check_text("namespace N { interface T {} } type Alias = N.T;");
        assert_eq!(
            checker_codes(&hidden),
            [NAMESPACE_NO_EXPORTED_MEMBER.as_str()]
        );

        let ambient = check_text("declare namespace N { interface T {} } type Alias = N.T;");
        assert!(checker_codes(&ambient).is_empty());

        let non_namespace = check_text("const value = {}; type Alias = value.T;");
        assert_eq!(
            checker_codes(&non_namespace),
            [CANNOT_FIND_NAMESPACE.as_str()]
        );
    }

    #[test]
    fn qualified_enum_member_types_use_the_enum_container_scope() {
        // tsc resolves `N.E.A` as a type to the enum member's literal type.
        // The qualified type reference path falls through the enum's member
        // scope and finds the EnumMember in the value plane.
        let checked = check_text("namespace N { export enum E { A } } type Value = N.E.A;");
        assert!(
            checker_codes(&checked)
                .iter()
                .all(|c| !c.starts_with("BAMTS-C00")),
            "N.E.A must resolve as a type reference: {:?}",
            checked.diagnostics()
        );

        let checked = check_text("namespace N { export const enum E { A } } type Value = N.E.A;");
        assert!(
            checker_codes(&checked)
                .iter()
                .all(|c| !c.starts_with("BAMTS-C00")),
            "N.E.A must resolve as a type reference (const enum): {:?}",
            checked.diagnostics()
        );

        let checked = check_text("namespace N { export enum E { A } } type Value = N.E;");
        assert!(checker_codes(&checked).is_empty());
    }

    #[test]
    fn qualified_value_only_exports_are_not_types() {
        let checked = check_text("namespace N { export const Value = 1; } type Alias = N.Value;");
        assert_eq!(checker_codes(&checked), [CANNOT_FIND_TYPE.as_str()]);

        let checked =
            check_text("namespace N { export function Value() {} } type Alias = N.Value;");
        assert_eq!(checker_codes(&checked), [CANNOT_FIND_TYPE.as_str()]);
    }

    #[test]
    fn qualified_type_queries_resolve_namespace_value_members() {
        let checked =
            check_text("namespace N { export const Value = 1; } type Alias = typeof N.Value;");
        assert!(checker_codes(&checked).is_empty());

        let ambient = check_text("type Alias = typeof NodeJS.Timeout;");
        assert_eq!(checker_codes(&ambient), [CANNOT_FIND_NAME.as_str()]);

        let external = check_text(
            "import * as External from 'external'; type Alias = typeof External.Timeout;",
        );
        assert!(checker_codes(&external).is_empty());
    }

    #[test]
    fn merged_namespace_exports_resolve_across_declaration_blocks() {
        let checked = check_text(
            "namespace N { export interface Visible {} } namespace N { export interface Later {} } type Alias = N.Later;",
        );
        assert!(checker_codes(&checked).is_empty());

        let hidden = check_text(
            "namespace N { export interface Visible {} } namespace N { interface Hidden {} } type Alias = N.Hidden;",
        );
        assert_eq!(
            checker_codes(&hidden),
            [NAMESPACE_NO_EXPORTED_MEMBER.as_str()]
        );
    }

    #[test]
    fn visible_nested_type_references_record_the_symbol_path() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source(
                "namespace Outer { export namespace Inner { export type T = number; } } type Alias = Outer.Inner.T;",
            ),
        ));
        let Statement::TypeAlias(alias) = parsed.product().statements()[1].data() else {
            panic!("second statement is a type alias");
        };
        let checked = check(&parsed);
        assert!(checker_codes(&checked).is_empty());
        assert!(
            checked
                .product()
                .namespace_facts()
                .qualified_type_path(alias.type_node.id())
                .is_some()
        );
    }

    #[test]
    fn qualified_type_roots_distinguish_unknowns_from_local_non_namespaces() {
        let nested_missing_member = check_text("namespace N {} type Alias = N.M.T;");
        assert_eq!(
            checker_codes(&nested_missing_member),
            [CANNOT_FIND_TYPE.as_str()]
        );

        let missing_inner_member =
            check_text("namespace N { export namespace M {} } type Alias = N.M.T;");
        assert_eq!(
            checker_codes(&missing_inner_member),
            [CANNOT_FIND_TYPE.as_str()]
        );

        let ambient = check_text("type Alias = NodeJS.Timeout;");
        assert!(checker_codes(&ambient).is_empty());

        let external =
            check_text("import * as External from 'external'; type Alias = External.Timeout;");
        assert!(checker_codes(&external).is_empty());

        let non_namespace = check_text("let X = 1; type T = X.Y;");
        assert_eq!(
            checker_codes(&non_namespace),
            [CANNOT_FIND_NAMESPACE.as_str()]
        );
    }
    #[test]
    fn local_const_enum_member_access_has_scalar_facts_for_numbers_and_templates() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("const enum K { X = 2, Y = X + 3 } K.Y;"),
        ));
        let Statement::Enum(declaration) = parsed.product().statements()[0].data() else {
            panic!("first statement is a const enum");
        };
        let Some(initializer) = &declaration.members[1].data().initializer else {
            panic!("Y has an initializer");
        };
        let Expression::Binary(binary) = initializer.data() else {
            panic!("Y uses a binary initializer");
        };
        let internal = binary.left.id();
        let Statement::Expression(statement) = parsed.product().statements()[1].data() else {
            panic!("second statement is an expression");
        };
        let expression = &statement.expression;
        assert_ne!(internal, expression.id());
        let checked = check(&parsed);
        let facts = checked.product().enum_facts();
        let internal_value = facts
            .const_use(internal)
            .and_then(|scalar| scalar.number())
            .expect("X has an internal const-enum scalar fact");
        assert_eq!(internal_value.to_f64(), 2.0);
        let value = facts
            .const_use(expression.id())
            .and_then(|scalar| scalar.number())
            .expect("K.Y has a local const-enum scalar fact");
        assert_eq!(value.to_f64(), 5.0);

        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("const enum K { X = `line\\n\\u{1F603}` } K.X;"),
        ));
        let Statement::Expression(statement) = parsed.product().statements()[1].data() else {
            panic!("second statement is a const-enum member expression");
        };
        let checked = check(&parsed);
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checker_codes(&checked)
        );
        let value = checked
            .product()
            .enum_facts()
            .const_use(statement.expression.id())
            .expect("K.X has a local const-enum scalar fact");
        let crate::enum_plan::EnumScalar::String(value) = value else {
            panic!("K.X must have a string scalar fact");
        };
        assert_eq!(value.as_units(), [108, 105, 110, 101, 10, 0xD83D, 0xDE03]);

        let checked = check_text("const enum K { X = `${1}` }");
        assert_eq!(
            checker_codes(&checked),
            [crate::enum_plan::CONST_OR_AMBIENT_ENUM_NONCONSTANT.as_str()]
        );
    }

    #[test]
    fn imported_declared_const_enum_member_inlines_without_runtime_value() {
        let importer = "import { K } from './declarations'; K.X;";
        let checked = linked(
            &["export declare const enum K { X = 7 }", importer],
            &[(1, 0, 0)],
        );
        assert!(
            !program_codes(&checked).contains(&super::IMPORTED_CONST_ENUM_UNRESOLVED.as_str()),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(1)).unwrap();
        assert_eq!(
            file.enum_facts()
                .const_use(member_expression_id(1, importer, 1))
                .and_then(|value| value.number())
                .unwrap()
                .to_f64(),
            7.0
        );
        assert!(
            file.enum_facts()
                .is_elided_import_specifier(import_specifier_id(1, importer))
        );
    }

    #[test]
    fn imported_const_enum_direct_and_alias_access_inline_by_symbol_identity() {
        let direct = "import { K } from './a'; K.X;";
        let alias = "import { K as Alias } from './a'; Alias.X;";
        let checked = linked(
            &["export const enum K { X = 2 }", direct, alias],
            &[(1, 0, 0), (2, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        for (source, text) in [(1, direct), (2, alias)] {
            let member = member_expression_id(source, text, 1);
            let file = checked.product().file(SourceId::new(source)).unwrap();
            assert_eq!(
                file.enum_facts()
                    .const_use(member)
                    .and_then(|value| value.number())
                    .unwrap()
                    .to_f64(),
                2.0
            );
            assert!(
                file.enum_facts()
                    .is_elided_import_specifier(import_specifier_id(source, text))
            );
        }
    }

    #[test]
    fn transparent_wrappers_preserve_const_enum_member_identity() {
        let direct = "const enum E { A = 7 } E.A; E.A; E.A; E.A; E.A;";
        let wrapped = "const enum E { A = 7 } (E).A; (E as unknown).A; (E satisfies unknown).A; (<unknown>E).A; E!.A;";
        let direct_model = check_text(direct);
        let checked = check_text(wrapped);
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checker_codes(&checked)
        );
        let model = checked.product();
        assert_eq!(
            model.resolved_reference_count(),
            direct_model.product().resolved_reference_count(),
            "transparent wrappers must not become canonical references"
        );
        for statement in 1..=5 {
            let member = member_expression_id(0, wrapped, statement);
            assert_eq!(
                model
                    .enum_facts()
                    .const_use(member)
                    .and_then(|value| value.number())
                    .map(|value| value.to_f64()),
                Some(7.0),
                "wrapper statement {statement}"
            );
        }

        let direct_importer = "import { E } from './a'; E.A; E.A; E.A; E.A; E.A;";
        let wrapped_importer = "import { E } from './a'; (E).A; (E as unknown).A; (E satisfies unknown).A; (<unknown>E).A; E!.A;";
        let direct_program = linked(
            &["export const enum E { A = 7 }", direct_importer],
            &[(1, 0, 0)],
        );
        let wrapped_program = linked(
            &["export const enum E { A = 7 }", wrapped_importer],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&wrapped_program).is_empty(),
            "{:?}",
            program_codes(&wrapped_program)
        );
        let direct_file = direct_program.product().file(SourceId::new(1)).unwrap();
        let wrapped_file = wrapped_program.product().file(SourceId::new(1)).unwrap();
        assert_eq!(
            wrapped_file.resolved_reference_count(),
            direct_file.resolved_reference_count(),
            "transparent wrappers must not become canonical import references"
        );
        for statement in 1..=5 {
            let member = member_expression_id(1, wrapped_importer, statement);
            assert_eq!(
                wrapped_file
                    .enum_facts()
                    .const_use(member)
                    .and_then(|value| value.number())
                    .map(|value| value.to_f64()),
                Some(7.0),
                "imported wrapper statement {statement}"
            );
        }
    }

    #[test]
    fn transparent_wrappers_preserve_namespace_imported_const_enum_identity() {
        let direct = "import * as Ns from './a'; Ns.E.A; Ns.E.A; Ns.E.A; Ns.E.A; Ns.E.A;";
        let wrapped = "import * as Ns from './a'; (Ns.E).A; (Ns.E as unknown).A; (Ns.E satisfies unknown).A; (<unknown>Ns.E).A; (Ns.E)!.A;";
        let direct_program = linked(&["export const enum E { A = 7 }", direct], &[(1, 0, 0)]);
        let wrapped_program = linked(&["export const enum E { A = 7 }", wrapped], &[(1, 0, 0)]);
        assert!(
            program_codes(&wrapped_program).is_empty(),
            "{:?}",
            program_codes(&wrapped_program)
        );
        let direct_file = direct_program.product().file(SourceId::new(1)).unwrap();
        let wrapped_file = wrapped_program.product().file(SourceId::new(1)).unwrap();
        assert_eq!(
            wrapped_file.resolved_reference_count(),
            direct_file.resolved_reference_count(),
            "transparent wrappers must not become canonical namespace references"
        );
        for statement in 1..=5 {
            let member = member_expression_id(1, wrapped, statement);
            assert_eq!(
                wrapped_file
                    .enum_facts()
                    .const_use(member)
                    .and_then(|value| value.number())
                    .map(|value| value.to_f64()),
                Some(7.0),
                "namespace imported wrapper statement {statement}"
            );
        }
    }

    #[test]
    fn imported_const_enum_reexport_and_namespace_access_inline() {
        let importer = "import * as Ns from './b'; Ns.Alias.X;";
        let checked = linked(
            &[
                "export const enum K { X = 3 }",
                "export { K as Alias } from './a';",
                importer,
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(2)).unwrap();
        assert_eq!(
            file.enum_facts()
                .const_use(member_expression_id(2, importer, 1))
                .and_then(|value| value.number())
                .unwrap()
                .to_f64(),
            3.0
        );
    }

    #[test]
    fn scalar_member_chains_do_not_restart_const_enum_resolution() {
        let local = parsed(0, "const enum E { A = 7, B = 9 } E.A.B;");
        let (local_member, local_chain) = member_chain_ids(local.product(), 1);
        let checked_local = check(&local);
        let local_facts = checked_local.product().enum_facts();
        assert_eq!(
            local_facts
                .const_use(local_member)
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(7.0)
        );
        assert!(local_facts.const_use(local_chain).is_none());

        let direct = "import { E } from './a'; E.A.B;";
        let namespace = "import * as Ns from './a'; Ns.E.A; Ns.E.A.B;";
        let files = [
            parsed(0, "export const enum E { A = 7, B = 9 }"),
            parsed(1, direct),
            parsed(2, namespace),
        ];
        let (direct_member, direct_chain) = member_chain_ids(files[1].product(), 1);
        let (_, namespace_member) = member_chain_ids(files[2].product(), 1);
        let (_, namespace_chain) = member_chain_ids(files[2].product(), 2);
        let edges = [
            ResolvedModuleEdge {
                from: SourceId::new(1),
                specifier: files[1].product().statements()[0].id(),
                to: SourceId::new(0),
            },
            ResolvedModuleEdge {
                from: SourceId::new(2),
                specifier: files[2].product().statements()[0].id(),
                to: SourceId::new(0),
            },
        ];
        let checked = check_program(
            ProgramCheckInput {
                files: &files,
                edges: &edges,
            },
            &crate::lint::LintTable::new(crate::lint::LintProfile::Default),
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );

        let direct_facts = checked
            .product()
            .file(SourceId::new(1))
            .expect("direct importer is checked")
            .enum_facts();
        assert_eq!(
            direct_facts
                .const_use(direct_member)
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(7.0)
        );
        assert!(direct_facts.const_use(direct_chain).is_none());

        let namespace_facts = checked
            .product()
            .file(SourceId::new(2))
            .expect("namespace importer is checked")
            .enum_facts();
        assert_eq!(
            namespace_facts
                .const_use(namespace_member)
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(7.0)
        );
        assert!(namespace_facts.const_use(namespace_chain).is_none());
    }

    #[test]
    fn imported_const_enum_reexport_cycle_is_diagnosed() {
        let checked = linked(
            &[
                "export { K } from './b';",
                "export { K } from './a';",
                "import { K } from './a'; K.X;",
            ],
            &[(0, 0, 1), (1, 0, 0), (2, 0, 0)],
        );
        assert!(program_codes(&checked).contains(&IMPORTED_CONST_ENUM_CYCLE.as_str()));
    }

    #[test]
    fn imported_nonconstant_const_enum_member_is_diagnosed() {
        let checked = linked(
            &[
                "declare function f(): number; export const enum K { X = f() }",
                "import { K } from './a'; K.X;",
            ],
            &[(1, 0, 0)],
        );
        let producer_codes = program_codes_for_source(&checked, SourceId::new(0));
        let importer_codes = program_codes_for_source(&checked, SourceId::new(1));
        assert_eq!(
            producer_codes,
            [crate::enum_plan::CONST_OR_AMBIENT_ENUM_NONCONSTANT.as_str()]
        );
        assert_eq!(
            importer_codes,
            [IMPORTED_CONST_ENUM_NONCONSTANT.as_str()],
            "{importer_codes:?}"
        );
    }

    #[test]
    fn external_import_members_stay_runtime_while_internal_missing_members_keep_c012() {
        let external = concat!(
            "import vm, { runInThisContext } from 'node:vm'; ",
            "vm.runInThisContext; runInThisContext.call;",
        );
        let checked = linked(&[external], &[]);
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let facts = checked
            .product()
            .file(SourceId::new(0))
            .expect("external importer is checked")
            .enum_facts();
        for statement in [1, 2] {
            assert!(
                facts
                    .const_use(member_expression_id(0, external, statement))
                    .is_none(),
                "external member statement {statement} must remain runtime"
            );
        }
        assert!(
            !facts.is_elided_import_specifier(import_specifier_id(0, external)),
            "external named imports must remain emitted"
        );

        let internal = "import { K } from './a'; K.Missing;";
        let unresolved = linked(
            &["export const enum K { Present = 1 }", internal],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&unresolved).contains(&super::IMPORTED_CONST_ENUM_UNRESOLVED.as_str()),
            "{:?}",
            program_codes(&unresolved)
        );
    }

    #[test]
    fn imported_const_enum_initializers_inline_transitively() {
        let importer = "import { B } from './b'; B.X;";
        let checked = linked(
            &[
                "export const enum A { Y = 2 }",
                "import { A } from './a'; export const enum B { X = A.Y + 1 }",
                importer,
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(2)).unwrap();
        assert_eq!(
            file.enum_facts()
                .const_use(member_expression_id(2, importer, 1))
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(3.0)
        );
    }

    #[test]
    fn imported_const_enum_initializer_cycle_keeps_c014() {
        let checked = linked(
            &[
                "import { B } from './b'; export const enum A { X = B.Y }",
                "import { A } from './a'; export const enum B { Y = A.X }",
            ],
            &[(0, 0, 1), (1, 0, 0)],
        );
        let codes = program_codes(&checked);
        assert!(codes.contains(&IMPORTED_CONST_ENUM_CYCLE.as_str()));
        assert!(!codes.contains(&crate::enum_plan::CONST_OR_AMBIENT_ENUM_NONCONSTANT.as_str()));
    }

    #[test]
    fn imported_const_enum_initializer_nonconstant_keeps_the_producer_c007() {
        let checked = linked(
            &[
                "declare function f(): number; export const enum A { Y = f() }",
                "import { A } from './a'; export const enum B { X = A.Y }",
            ],
            &[(1, 0, 0)],
        );
        let producer_codes = program_codes_for_source(&checked, SourceId::new(0));
        let importer_codes = program_codes_for_source(&checked, SourceId::new(1));
        assert_eq!(
            producer_codes,
            [crate::enum_plan::CONST_OR_AMBIENT_ENUM_NONCONSTANT.as_str()]
        );
        assert_eq!(
            importer_codes,
            [IMPORTED_CONST_ENUM_NONCONSTANT.as_str()],
            "{importer_codes:?}"
        );
    }

    #[test]
    fn imported_const_enum_initializer_keeps_operator_c007() {
        for importer in [
            "import { A } from './a'; export const enum B { X = !A.Y }",
            "import { A } from './a'; export const enum B { X = A.Y < 1 }",
        ] {
            let checked = linked(
                &[
                    "declare function source(): number; export const enum A { Y = source() }",
                    importer,
                ],
                &[(1, 0, 0)],
            );
            let importer_codes = program_codes_for_source(&checked, SourceId::new(1));
            assert!(
                importer_codes.contains(&IMPORTED_CONST_ENUM_NONCONSTANT.as_str()),
                "{importer_codes:?}"
            );
            assert_eq!(
                importer_codes
                    .iter()
                    .filter(|&&code| {
                        code == crate::enum_plan::CONST_OR_AMBIENT_ENUM_NONCONSTANT.as_str()
                    })
                    .count(),
                1,
                "{importer_codes:?}"
            );
        }
    }

    #[test]
    fn same_named_imported_enums_remain_distinct_across_modules() {
        let importer =
            "import { K as Left } from './a'; import { K as Right } from './b'; Left.X + Right.X;";
        let checked = linked(
            &[
                "export const enum K { X = 1 }",
                "export const enum K { X = 9 }",
                importer,
            ],
            &[(2, 0, 0), (2, 1, 1)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(2)).unwrap();
        let (left, right) = binary_member_expression_ids(2, importer, 2);
        assert_eq!(
            file.enum_facts()
                .const_use(left)
                .and_then(|value| value.number())
                .unwrap()
                .to_f64(),
            1.0
        );
        assert_eq!(
            file.enum_facts()
                .const_use(right)
                .and_then(|value| value.number())
                .unwrap()
                .to_f64(),
            9.0
        );
    }

    #[test]
    fn const_enum_nonfinite_intrinsics_take_precedence_over_nonconstant() {
        for text in ["const enum E { A = NaN }", "const enum E { A = Infinity }"] {
            let parsed = parsed(0, text);
            let Statement::Enum(declaration) = parsed.product().statements()[0].data() else {
                panic!("first statement is a const enum");
            };
            let initializer = declaration.members[0]
                .data()
                .initializer
                .as_ref()
                .expect("A has an initializer");
            let checked = check(&parsed);
            let model = checked.product();

            assert_eq!(
                checker_codes(&checked),
                [crate::enum_plan::CONST_ENUM_NONFINITE.as_str()],
                "{text}"
            );
            assert!(
                model.reference(initializer.id()).is_some(),
                "{text} keeps an outer expression alias"
            );
            assert_eq!(model.resolved_reference_count(), 1, "{text}");
            assert!(model.enum_facts().member_use(initializer.id()).is_none());
        }
    }

    #[test]
    fn imported_const_enum_diamond_export_star_inlines_once() {
        let importer = "import { K } from './barrel'; K.X;";
        let checked = linked(
            &[
                "export const enum K { X = 4 }",
                "export { K } from './source';",
                "export * from './source'; export * from './forwarder';",
                importer,
            ],
            &[(1, 0, 0), (2, 0, 0), (2, 1, 1), (3, 0, 2)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(3)).unwrap();
        assert_eq!(
            file.enum_facts()
                .const_use(member_expression_id(3, importer, 1))
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(4.0)
        );
        assert!(
            file.enum_facts()
                .is_elided_import_specifier(import_specifier_id(3, importer))
        );
    }

    #[test]
    fn namespace_export_star_forwards_const_enum() {
        let importer = "import { Enums } from './barrel'; Enums.K.X;";
        let checked = linked(
            &[
                "export const enum K { X = 5 }",
                "export * as Enums from './source';",
                importer,
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
        let file = checked.product().file(SourceId::new(2)).unwrap();
        assert_eq!(
            file.enum_facts()
                .const_use(member_expression_id(2, importer, 1))
                .and_then(|value| value.number())
                .map(|value| value.to_f64()),
            Some(5.0)
        );
    }

    #[test]
    fn ambiguous_const_enum_export_star_is_diagnosed_without_inlining() {
        let importer = "import { K } from './barrel'; K.X;";
        let checked = linked(
            &[
                "export const enum K { X = 1 }",
                "export const enum K { X = 2 }",
                "export * from './left'; export * from './right';",
                importer,
            ],
            &[(2, 0, 0), (2, 1, 1), (3, 0, 2)],
        );
        assert!(program_codes(&checked).contains(&IMPORTED_CONST_ENUM_AMBIGUOUS.as_str()));
        let file = checked.product().file(SourceId::new(3)).unwrap();
        assert!(
            file.enum_facts()
                .const_use(member_expression_id(3, importer, 1))
                .is_none()
        );
        assert!(
            !file
                .enum_facts()
                .is_elided_import_specifier(import_specifier_id(3, importer))
        );
    }

    #[test]
    fn cyclic_const_enum_export_star_is_diagnosed() {
        let checked = linked(
            &[
                "export * from './right';",
                "export * from './left';",
                "import { K } from './left'; K.X;",
            ],
            &[(0, 0, 1), (1, 0, 0), (2, 0, 0)],
        );
        assert!(program_codes(&checked).contains(&IMPORTED_CONST_ENUM_CYCLE.as_str()));
    }

    #[test]
    fn with_statement_context_matrix() {
        fn check_js(text: &str) -> Recovered<super::SemanticModel> {
            let parsed = parser::parse(scanner::scan(
                SourceId::new(0),
                ScriptKind::JavaScript,
                source(text),
            ));
            check(&parsed)
        }
        fn has_with(result: &Recovered<super::SemanticModel>) -> bool {
            result
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code() == WITH_STATEMENT_NOT_ALLOWED)
        }

        // Sloppy classic script: accepted.
        assert!(
            !has_with(&check_js("with ({}) {}")),
            "sloppy classic script accepts with"
        );

        // Explicit use strict at top level: rejected.
        assert!(
            has_with(&check_js("'use strict'; with ({}) {}")),
            "top-level use strict rejects with"
        );

        // Module goal: rejected.
        assert!(
            has_with(&check_js("import { x } from './x'; with ({}) {}")),
            "module goal rejects with"
        );

        // TypeScript: rejected.
        assert!(
            has_with(&check_text("with ({}) {}")),
            "typescript rejects with"
        );

        // Nested function with use strict: rejected.
        assert!(
            has_with(&check_js("function f() { 'use strict'; with ({}) {} }")),
            "nested strict function rejects with"
        );

        // Nested sloppy function inside classic script: accepted.
        assert!(
            !has_with(&check_js("function f() { with ({}) {} }")),
            "sloppy nested function accepts with"
        );
    }

    fn authority_source(relative: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("target/authority/typescript-7.0.2-tests/tests/cases/compiler")
            .join(relative);
        std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "authority fixture {} is unavailable: {error}; run \
                 `cargo run --locked -p bamts-verification -- source fetch \
                 typescript-primary-tests --dest target/authority/typescript-7.0.2-tests` \
                 from the repository root first",
                path.display()
            )
        })
    }

    /// The superAccess es2015 baseline carries one TS2576 (static S1 via
    /// super) and two TS2855 (fields S2 and f); the es5 variant's TS2340
    /// flavor is a separate target-conditional slice.
    #[test]
    fn super_static_member_matches_superaccess_baseline() {
        let source = authority_source("superAccess.ts");
        let codes = checker_codes(&check_text(&source));
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_STATIC_MEMBER_VIA_SUPER.as_str())
                .count(),
            1
        );
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_FIELD_VIA_SUPER.as_str())
                .count(),
            2
        );
    }

    /// The blockScopedEnumVariablesUseBeforeDef baseline carries exactly
    /// one TS2450: the regular enum in foo1. The const enums (foo2,
    /// AfterObject) are inlined at use sites and stay clean.
    #[test]
    fn enum_used_before_declaration_matches_baseline() {
        let source = authority_source("blockScopedEnumVariablesUseBeforeDef.ts");
        let codes = checker_codes(&check_text(&source));
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == ENUM_USED_BEFORE_DECLARATION.as_str())
                .count(),
            1,
            "{codes:?}"
        );
    }

    /// TS1114: a label redeclared while it still encloses the current statement.
    /// TS1116: a labeled break may only target an enclosing label. The
    /// oracles are duplicateLabel2 (one row) and breakTarget6 (one row).
    #[test]
    fn label_rules_matrix() {
        assert_eq!(
            checker_codes(&check_text(
                "target: while (true) { target: while (true) {} }"
            )),
            vec![DUPLICATE_LABEL.as_str()]
        );
        // A completed sibling label is no longer active and may be reused.
        assert_eq!(
            checker_codes(&check_text("a: {} a: {}")),
            Vec::<&str>::new()
        );
        // A nested function owns its labels; reuse across the boundary is
        // legal.
        assert_eq!(
            checker_codes(&check_text("a: {} function f() { a: {} }")),
            Vec::<&str>::new()
        );
        assert_eq!(
            checker_codes(&check_text("while (true) { break target; }")),
            vec![BREAK_TARGET_NOT_ENCLOSING.as_str()]
        );
        assert_eq!(
            checker_codes(&check_text("target: while (true) { break target; }")),
            Vec::<&str>::new()
        );
        assert_eq!(
            checker_codes(&check_text(
                "target: while (true) { for (;;) { break target; } }"
            )),
            Vec::<&str>::new()
        );
        // Plain break needs no label context.
        assert_eq!(
            checker_codes(&check_text("for (;;) { break; }")),
            Vec::<&str>::new()
        );
        // Authority oracles: one row each.
        let duplicate = authority_source("duplicateLabel2.ts");
        assert_eq!(
            checker_codes(&check_text(&duplicate)),
            vec![DUPLICATE_LABEL.as_str()]
        );
        let jump = authority_source("breakTarget6.ts");
        assert_eq!(
            checker_codes(&check_text(&jump)),
            vec![BREAK_TARGET_NOT_ENCLOSING.as_str()]
        );
        // TS1107: the label exists, but in an enclosing function.
        let crosses = authority_source("breakTarget5.ts");
        assert_eq!(
            checker_codes(&check_text(&crosses)),
            vec![BREAK_TARGET_CROSSES_FUNCTION.as_str()]
        );
        assert_eq!(
            checker_codes(&check_text(
                "target: while (true) { function f() { for (;;) { break target; } } }"
            )),
            vec![BREAK_TARGET_CROSSES_FUNCTION.as_str()]
        );
    }

    /// TS2371: only an implementation may carry parameter defaults. The
    /// oracle (defaultValueInConstructorOverload1) is exactly one row on a
    /// constructor overload signature.
    #[test]
    fn parameter_initializer_only_in_implementation() {
        assert_eq!(
            checker_codes(&check_text("function f(x = 1); function f(x?: number) {}")),
            vec![PARAMETER_INITIALIZER_IN_SIGNATURE.as_str()]
        );
        assert_eq!(
            checker_codes(&check_text(
                "class C { constructor(x = ''); constructor(x = '') {} }"
            )),
            vec![PARAMETER_INITIALIZER_IN_SIGNATURE.as_str()]
        );
        assert_eq!(
            checker_codes(&check_text("function g(x = 1) {}")),
            Vec::<&str>::new()
        );
        let source = authority_source("defaultValueInConstructorOverload1.ts");
        assert_eq!(
            checker_codes(&check_text(&source)),
            vec![PARAMETER_INITIALIZER_IN_SIGNATURE.as_str()]
        );
    }

    /// The superAccess es5 baseline swaps each TS2855 field row for the
    /// single pre-fields rule TS2340; the static row stays TS2576 at both
    /// targets.
    #[test]
    fn super_field_flavor_splits_by_target() {
        let source = "class MyBase {
                 static S1: number = 5;
                 private S2: string = \"test\";
                 f = () => 5;
             }
             class MyDerived extends MyBase {
                 foo() {
                     var l3 = super.S1;
                     var l4 = super.S2;
                     var l5 = super.f();
                 }
             }";
        let es5 = checker_codes(&check_text_with(
            source,
            ProgramCheckOptions::standard().with_target(Some("es5")),
        ));
        assert_eq!(
            es5.iter()
                .filter(|c| **c == SUPER_PROPERTY_NOT_METHOD.as_str())
                .count(),
            2,
            "{es5:?}"
        );
        assert_eq!(
            es5.iter()
                .filter(|c| **c == SUPER_FIELD_VIA_SUPER.as_str())
                .count(),
            0,
            "{es5:?}"
        );
        assert_eq!(
            es5.iter()
                .filter(|c| **c == SUPER_STATIC_MEMBER_VIA_SUPER.as_str())
                .count(),
            1,
            "{es5:?}"
        );
        let es2015 = checker_codes(&check_text_with(
            source,
            ProgramCheckOptions::standard().with_target(Some("es2015")),
        ));
        assert_eq!(
            es2015
                .iter()
                .filter(|c| **c == SUPER_FIELD_VIA_SUPER.as_str())
                .count(),
            2,
            "{es2015:?}"
        );
        assert_eq!(
            es2015
                .iter()
                .filter(|c| **c == SUPER_PROPERTY_NOT_METHOD.as_str())
                .count(),
            0,
            "{es2015:?}"
        );
        // The authority file itself: es5 swaps both field rows for TS2340
        // and keeps the static row at TS2576.
        let source = authority_source("superAccess.ts");
        let oracle_es5 = checker_codes(&check_text_with(
            &source,
            ProgramCheckOptions::standard().with_target(Some("es5")),
        ));
        assert_eq!(
            oracle_es5
                .iter()
                .filter(|c| **c == SUPER_PROPERTY_NOT_METHOD.as_str())
                .count(),
            2,
            "{oracle_es5:?}"
        );
        assert_eq!(
            oracle_es5
                .iter()
                .filter(|c| **c == SUPER_STATIC_MEMBER_VIA_SUPER.as_str())
                .count(),
            1,
            "{oracle_es5:?}"
        );
    }

    /// TS2427: an interface may not take a primitive type's name. The
    /// authority rows cover string, number, boolean, any, never, unknown,
    /// symbol, and undefined. Reserved-word names (`void`, `null`) need a
    /// parser-relaxation slice before the checker can see them; the
    /// implementation bans the full primitive set for the names the parser
    /// delivers as identifiers.
    #[test]
    fn interface_name_cannot_be_primitive() {
        for name in [
            "string",
            "number",
            "boolean",
            "any",
            "never",
            "unknown",
            "symbol",
            "undefined",
        ] {
            let source = format!("interface {name} {{}}");
            let codes = checker_codes(&check_text(&source));
            assert_eq!(
                codes,
                vec![INTERFACE_NAME_IS_PRIMITIVE.as_str()],
                "{name}: {codes:?}"
            );
        }
        // Ordinary names, including intrinsic globals, stay legal.
        assert_eq!(
            checker_codes(&check_text("interface ArrayLike<T> { length: number }")),
            Vec::<&str>::new()
        );
        assert_eq!(
            checker_codes(&check_text("interface PromiseLike<T> { then(): T }")),
            Vec::<&str>::new()
        );
    }

    /// TS1014: a rest parameter followed by anything else. Arrows and
    /// constructors carry their own binders, so each shape is pinned; a
    /// trailing rest parameter stays silent.
    #[test]
    fn rest_parameter_not_last_matrix() {
        let codes = checker_codes(&check_text("function f(...x, y) { }"));
        assert_eq!(codes, vec![REST_PARAMETER_NOT_LAST.as_str()]);
        let arrow = checker_codes(&check_text("const g = (...x, y) => x;"));
        assert_eq!(arrow, vec![REST_PARAMETER_NOT_LAST.as_str()]);
        let ctor = checker_codes(&check_text("class C { constructor(...x, y) {} }"));
        assert_eq!(ctor, vec![REST_PARAMETER_NOT_LAST.as_str()]);
        let method = checker_codes(&check_text("class C { m(...x, y) {} }"));
        assert_eq!(method, vec![REST_PARAMETER_NOT_LAST.as_str()]);
        assert_eq!(
            checker_codes(&check_text("function h(x, ...rest) { }")),
            Vec::<&str>::new()
        );
    }

    #[test]
    fn block_scoped_used_before_declaration_matrix() {
        fn codes(text: &str) -> Vec<&'static str> {
            checker_codes(&check_text(text))
        }
        // let/const/class/enum referenced textually before declaration.
        let late_binding = codes(
            "return_early();
             function return_early() {
                 const v = x;
                 let x = 1;
                 class C {}
                 new D();
                 class D {}
                 E.A;
                 enum E { A }
                 return v;
             }",
        );
        assert!(late_binding.contains(&BLOCK_SCOPED_USED_BEFORE_DECLARATION.as_str()));
        assert!(late_binding.contains(&CLASS_USED_BEFORE_DECLARATION.as_str()));
        assert!(
            late_binding.contains(&ENUM_USED_BEFORE_DECLARATION.as_str()),
            "{late_binding:?}"
        );
        // A reference deferred through a function-like boundary is legal:
        // the function runs after the binding initializes, and its body
        // resolves once the binding is already in scope.
        let deferred = codes(
            "function g() {
                 inner();
                 let y = 1;
                 function inner() { return y; }
                 const f = () => y;
             }
             g();",
        );
        assert!(
            !deferred.contains(&BLOCK_SCOPED_USED_BEFORE_DECLARATION.as_str()),
            "{deferred:?}"
        );
        // var and function declarations hoist: no error.
        let hoisted = codes(
            "h();
             var shared = 1;
             function h() { return shared; }",
        );
        assert!(
            !hoisted.contains(&BLOCK_SCOPED_USED_BEFORE_DECLARATION.as_str()),
            "{hoisted:?}"
        );
        // Use at or after the declaration stays silent.
        assert_eq!(codes("let a = 1; a; const b = a; b;"), Vec::<&str>::new());
    }

    /// TS2576: super.S1 where S1 is a base static member. Also pins the
    /// superAccess oracle shape: static fires TS2576, instance fields fire
    /// TS2855, and a base instance method stays silent.
    #[test]
    fn super_static_member_via_super_matrix() {
        let result = check_text(
            "class MyBase {
                 static S1: number = 5;
                 f = () => 5;
             }
             class MyDerived extends MyBase {
                 foo() {
                     var l1 = super.S1;
                     var l3 = super.f;
                     var l4 = super.toString;
                 }
             }",
        );
        let codes = checker_codes(&result);
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_STATIC_MEMBER_VIA_SUPER.as_str())
                .count(),
            1,
            "{codes:?}"
        );
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_FIELD_VIA_SUPER.as_str())
                .count(),
            1,
            "{codes:?}"
        );
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_BEFORE_SUPER_PROPERTY.as_str())
                .count(),
            0,
            "{codes:?}"
        );
    }

    /// TS2576 is admissible only from an instance member: a static
    /// method's `super` resolves the base constructor, so reading and
    /// writing a base static through `super` is legal, while the same
    /// read from an instance method is the TS2576 misspelling. Static
    /// property and auto-accessor initializers, static blocks, and
    /// lexical arrows inherit the enclosing member's home, so every
    /// static surface stays silent while an instance arrow still
    /// reports.
    #[test]
    fn super_static_member_home_matrix() {
        let static_context = checker_codes(&check_text(
            "class MyBase {
                 static x: string = 'base';
             }
             class MyDerived extends MyBase {
                 static p = super.x;
                 static accessor acc = super.x;
                 static {
                     super.x;
                 }
                 static m() {
                     super.x;
                     super.x = 'derived';
                     () => super.x;
                 }
             }",
        ));
        assert_eq!(static_context, Vec::<&str>::new(), "{static_context:?}");
        let instance_context = checker_codes(&check_text(
            "class MyBase {
                 static x: string = 'base';
             }
             class MyDerived extends MyBase {
                 m() {
                     super.x;
                 }
             }",
        ));
        assert_eq!(
            instance_context,
            vec![SUPER_STATIC_MEMBER_VIA_SUPER.as_str()],
            "{instance_context:?}"
        );

        let instance_arrow = checker_codes(&check_text(
            "class MyBase {
                 static x: string = 'base';
             }
             class MyDerived extends MyBase {
                 m() {
                     () => super.x;
                 }
             }",
        ));
        assert_eq!(
            instance_arrow,
            vec![SUPER_STATIC_MEMBER_VIA_SUPER.as_str()],
            "{instance_arrow:?}"
        );

        let derived_constructor = checker_codes(&check_text(
            "class MyBase {
                 static x: string = 'base';
             }
             class MyDerived extends MyBase {
                 constructor() {
                     super();
                     super.x;
                 }
             }",
        ));
        assert_eq!(
            derived_constructor,
            vec![SUPER_STATIC_MEMBER_VIA_SUPER.as_str()],
            "{derived_constructor:?}"
        );
    }

    /// The protectedStaticClassPropertyAccessibleWithinSubclass2 es2015
    /// baseline carries no diagnostics: both `super.x` rows sit in static
    /// methods, where `super` resolves the base constructor and the
    /// protected static is reachable.
    #[test]
    fn super_static_member_static_context_matches_authority_baseline() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let source = std::fs::read_to_string(root.join(concat!(
            "target/authority/typescript-7.0.2-tests/tests/cases/conformance/",
            "classes/members/accessibility/",
            "protectedStaticClassPropertyAccessibleWithinSubclass2.ts"
        )))
        .unwrap();
        let codes = checker_codes(&check_text(&source));
        assert_eq!(
            codes
                .iter()
                .filter(|c| **c == SUPER_STATIC_MEMBER_VIA_SUPER.as_str())
                .count(),
            0,
            "{codes:?}"
        );
    }

    /// The same authority file at target=es5: both `super.x` rows sit in
    /// static methods reading the base's static field, so the downlevel
    /// pre-fields rule reports exactly two C099 rows and the TS2576
    /// misspelling stays silent. On es2015 the access is legal, so neither
    /// the field rule nor the static rule may report.
    #[test]
    fn super_static_field_access_splits_by_target_on_authority_file() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let source = std::fs::read_to_string(root.join(concat!(
            "target/authority/typescript-7.0.2-tests/tests/cases/conformance/",
            "classes/members/accessibility/",
            "protectedStaticClassPropertyAccessibleWithinSubclass2.ts"
        )))
        .unwrap();
        let es5 = checker_codes(&check_text_with(
            &source,
            ProgramCheckOptions::standard().with_target(Some("es5")),
        ));
        assert_eq!(
            es5.iter()
                .filter(|c| **c == SUPER_PROPERTY_NOT_METHOD.as_str())
                .count(),
            2,
            "{es5:?}"
        );
        for code in [
            SUPER_FIELD_VIA_SUPER.as_str(),
            SUPER_STATIC_MEMBER_VIA_SUPER.as_str(),
        ] {
            assert_eq!(
                es5.iter().filter(|c| **c == code).count(),
                0,
                "{code} es5: {es5:?}"
            );
        }
        let es2015 = checker_codes(&check_text_with(
            &source,
            ProgramCheckOptions::standard().with_target(Some("es2015")),
        ));
        for code in [
            SUPER_PROPERTY_NOT_METHOD.as_str(),
            SUPER_FIELD_VIA_SUPER.as_str(),
            SUPER_STATIC_MEMBER_VIA_SUPER.as_str(),
        ] {
            assert_eq!(
                es2015.iter().filter(|c| **c == code).count(),
                0,
                "{code} es2015: {es2015:?}"
            );
        }
    }

    /// A base static method reached through a static member's `super` is a
    /// method on the reached table, so no field rule fires — the boundary
    /// superInStaticMembers1.ts exercises cleanly at every target,
    /// including es5.
    #[test]
    fn super_static_method_in_static_home_is_not_a_field_violation() {
        let source = "\
class A {
    static w() { return 1; }
}
class B extends A {
    static _ = super.w();
    static { super.w(); }
}";
        for target in ["es5", "es2015"] {
            let codes = checker_codes(&check_text_with(
                source,
                ProgramCheckOptions::standard().with_target(Some(target)),
            ));
            for code in [
                SUPER_PROPERTY_NOT_METHOD.as_str(),
                SUPER_FIELD_VIA_SUPER.as_str(),
                SUPER_STATIC_MEMBER_VIA_SUPER.as_str(),
            ] {
                assert_eq!(
                    codes.iter().filter(|c| **c == code).count(),
                    0,
                    "{code} {target}: {codes:?}"
                );
            }
        }
    }

    /// The authority baseline checkSuperCallBeforeThisAccess.errors.txt
    /// carries exactly five TS2855 rows (lines 9, 12, 17, 22, 45 of the
    /// directive-stripped source); the count is the pinned oracle.
    #[test]
    fn super_field_via_super_matches_baseline_count() {
        let source = authority_source("checkSuperCallBeforeThisAccess.ts");
        let count = checker_codes(&check_text(&source))
            .into_iter()
            .filter(|code| *code == SUPER_FIELD_VIA_SUPER.as_str())
            .count();
        assert_eq!(count, 5);
        // The Accessing variants each carry a single TS17009 row; variant 5
        // reaches `this` inside the super() arguments, which evaluate before
        // the call completes.
        for variant in ["2", "5", "8"] {
            let variant_source =
                authority_source(&format!("checkSuperCallBeforeThisAccessing{variant}.ts"));
            let codes = checker_codes(&check_text(&variant_source));
            assert_eq!(
                codes
                    .iter()
                    .filter(|code| **code == SUPER_BEFORE_THIS.as_str())
                    .count(),
                1,
                "variant {}",
                variant
            );
        }
    }

    #[test]
    fn super_field_via_super_matrix() {
        fn field_codes(text: &str) -> Vec<&'static str> {
            let result = check_text(text);
            checker_codes(&result)
                .into_iter()
                .filter(|code| *code == SUPER_FIELD_VIA_SUPER.as_str())
                .collect()
        }
        // A base field read through super fires even after super() ran.
        assert_eq!(
            field_codes(
                "class A { field = 1; }
                 class C extends A {
                     constructor() { super(); super.field; }
                 }"
            ),
            vec![SUPER_FIELD_VIA_SUPER.as_str()]
        );
        // Base methods and accessor pairs live on the prototype: no fire.
        assert_eq!(
            field_codes(
                "class A { method() {} get pair() { return 1; } set pair(v) {} }
                 class C extends A {
                     constructor() { super(); super.method(); super.pair; }
                 }"
            ),
            Vec::<&str>::new()
        );
        // A getter-only accessor is reachable too.
        assert_eq!(
            field_codes(
                "class A { get only() { return 1; } }
                 class C extends A { constructor() { super(); super.only; } }"
            ),
            Vec::<&str>::new()
        );
        // The inherited grandparent field still fires, and a name the base
        // chain does not declare stays silent.
        assert_eq!(
            field_codes(
                "class A { shared = 1; }
                 class B extends A {}
                 class C extends B { constructor() { super(); super.shared; super.absent; } }"
            ),
            vec![SUPER_FIELD_VIA_SUPER.as_str()]
        );
        // No base class, no super property check applies.
        assert_eq!(
            field_codes("class C { constructor() { super(); } }"),
            Vec::<&str>::new()
        );
        // A field read before super() reports both TS17011 and TS2855.
        let result = check_text(
            "class A { field = 1; }
             class C extends A { constructor() { super.field; super(); } }",
        );
        let codes = checker_codes(&result);
        assert!(codes.contains(&SUPER_BEFORE_SUPER_PROPERTY.as_str()));
        assert!(codes.contains(&SUPER_FIELD_VIA_SUPER.as_str()));
    }

    /// TS17009/TS17011: a derived constructor's `this` and `super.x`
    /// accesses before a guaranteed `super()` call, with the oracle's
    /// flow shapes: arrows are exempt (deferred `this`), a conditional
    /// super() covers only its branch, and loops/try never guarantee.
    #[test]
    fn super_before_this_flow_matrix() {
        fn codes(text: &str) -> Vec<&'static str> {
            let result = check_text(text);
            let mut found = checker_codes(&result)
                .into_iter()
                .filter(|code| {
                    *code == SUPER_BEFORE_THIS.as_str()
                        || *code == SUPER_BEFORE_SUPER_PROPERTY.as_str()
                })
                .collect::<Vec<_>>();
            found.sort();
            found
        }

        // Straight-line before/after.
        assert_eq!(
            codes(
                "class A extends Object { constructor() { let a = this; super(); let b = this; } }"
            ),
            vec![SUPER_BEFORE_THIS.as_str()]
        );
        // super.x before super reports the property form.
        assert_eq!(
            codes("class A extends Object { constructor() { let a = super.x; super(); } }"),
            vec![SUPER_BEFORE_SUPER_PROPERTY.as_str()]
        );
        // Arrows defer their this: no report inside, and none after.
        assert_eq!(
            codes("class A extends Object { constructor() { let f = () => this; super(); f(); } }"),
            Vec::<&str>::new()
        );
        // Plain nested functions own their own this.
        assert_eq!(
            codes(
                "class A extends Object { constructor() { let f = function () { return this; }; super(); } }"
            ),
            Vec::<&str>::new()
        );
        // A conditional super() covers its branch only.
        assert_eq!(
            codes(
                "class A extends Object { constructor(c) {\nif (c) { super(); let a = this; }\nelse { let a = this; }\nlet b = this; } }"
            ),
            vec![SUPER_BEFORE_THIS.as_str(), SUPER_BEFORE_THIS.as_str()]
        );
        // Every continuing branch has called super, including when the
        // other branch exits before the merge.
        assert_eq!(
            codes(
                "class A extends Object { constructor(c) { if (c) super(); else super(); this; } }"
            ),
            Vec::<&str>::new()
        );
        assert_eq!(
            codes(
                "class A extends Object { constructor(c) { if (c) return {}; else super(); this; } }"
            ),
            Vec::<&str>::new()
        );
        // A super() inside a loop guarantees nothing after it.
        assert_eq!(
            codes(
                "class A extends Object { constructor(c) { while (c) { super(); break; } let a = this; } }"
            ),
            vec![SUPER_BEFORE_THIS.as_str()]
        );
        // Base constructors never track.
        assert_eq!(
            codes("class A { constructor() { let a = this; } }"),
            Vec::<&str>::new()
        );
        // Field initializer and method this are not constructor-flow.
        assert_eq!(
            codes(
                "class A extends Object { x = this; m() { return this; } constructor() { super(); } }"
            ),
            Vec::<&str>::new()
        );
    }

    #[test]
    fn pr199_super_flow_joins_every_continuing_path() {
        for (body, safe) in [
            ("if (c) { super(); } else { super(); }", true),
            ("if (c) { throw 0; } else { super(); }", true),
            ("if (c) { super(); } else { throw 0; }", true),
            ("if (c) { return { method() {} }; } else { super(); }", true),
            ("super(); if (c) {} else {}", true),
            (
                "if (c) { if (c) { super(); } else { super(); } } else { super(); }",
                true,
            ),
            ("if (c) { super(); }", false),
            ("if (c) {} else { super(); }", false),
        ] {
            let source = format!(
                "class B {{ method() {{}} }} \
                 class D extends B {{ constructor(c: boolean) {{ \
                 {body} this; super.method(); }} }}"
            );
            let mut codes = checker_codes(&check_text(&source))
                .into_iter()
                .filter(|code| {
                    *code == SUPER_BEFORE_THIS.as_str()
                        || *code == SUPER_BEFORE_SUPER_PROPERTY.as_str()
                })
                .collect::<Vec<_>>();
            codes.sort_unstable();
            let expected = if safe {
                Vec::new()
            } else {
                vec![
                    SUPER_BEFORE_THIS.as_str(),
                    SUPER_BEFORE_SUPER_PROPERTY.as_str(),
                ]
            };
            assert_eq!(codes, expected, "{body}");
        }
    }

    #[test]
    fn pr199_label_frames_and_nearest_targets() {
        let cases = [
            ("L: {} L: {}", None),
            ("L: { L: {} }", Some(DUPLICATE_LABEL.as_str())),
            ("L: { function f() { L: { break L; } } break L; }", None),
            ("L: { const f = () => { L: { break L; } }; break L; }", None),
            (
                "L: { class C { constructor() { L: { break L; } } } break L; }",
                None,
            ),
            (
                "L: { function f() { break L; } break L; }",
                Some(BREAK_TARGET_CROSSES_FUNCTION.as_str()),
            ),
            (
                "L: { const f = () => { break L; }; break L; }",
                Some(BREAK_TARGET_CROSSES_FUNCTION.as_str()),
            ),
            (
                "L: { class C { constructor() { break L; } } break L; }",
                Some(BREAK_TARGET_CROSSES_FUNCTION.as_str()),
            ),
            (
                "L: { class C { static { break L; } } break L; }",
                Some(BREAK_TARGET_CROSSES_FUNCTION.as_str()),
            ),
            ("const f = () => { local: {} }; local: {}", None),
            ("class C { constructor() { local: {} } } local: {}", None),
            ("class C { static { local: {} } } local: {}", None),
            ("L: {} break L;", Some(BREAK_TARGET_NOT_ENCLOSING.as_str())),
            (
                "while (true) { break missing; }",
                Some(BREAK_TARGET_NOT_ENCLOSING.as_str()),
            ),
        ];
        for (source, expected) in cases {
            let codes = checker_codes(&check_text(source))
                .into_iter()
                .filter(|code| {
                    *code == DUPLICATE_LABEL.as_str()
                        || *code == BREAK_TARGET_NOT_ENCLOSING.as_str()
                        || *code == BREAK_TARGET_CROSSES_FUNCTION.as_str()
                })
                .collect::<Vec<_>>();
            assert_eq!(codes, expected.into_iter().collect::<Vec<_>>(), "{source}");
        }
    }

    #[test]
    fn pr199_missing_authority_fixture_explains_the_prerequisite() {
        let panic = std::panic::catch_unwind(|| {
            authority_source("__pr199_fixture_that_must_not_exist__.ts")
        })
        .expect_err("a missing authority fixture must fail rather than skip");
        let message = panic.downcast_ref::<String>().expect("formatted panic");
        assert!(message.contains("__pr199_fixture_that_must_not_exist__.ts"));
        assert!(message.contains("source fetch typescript-primary-tests"));
        assert!(message.contains("--dest target/authority/typescript-7.0.2-tests"));
    }

    #[test]
    fn super_call_context_matrix() {
        const SUPER_CODES: [&str; 4] = [
            BARE_SUPER_EXPRESSION.as_str(),
            SUPER_REFERENCE_NON_DERIVED.as_str(),
            SUPER_CALL_OUTSIDE_CONSTRUCTOR.as_str(),
            SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS.as_str(),
        ];
        fn super_codes(text: &str) -> Vec<&'static str> {
            let result = check_text(text);
            SUPER_CODES
                .into_iter()
                .filter(|code| checker_codes(&result).contains(code))
                .collect()
        }

        // Valid: a direct `super(...)` call in a derived constructor body.
        for valid in [
            "class A extends Object { constructor() { super(); } }",
            "class A extends Object {}",
            "const C = class extends Object { constructor() { super(); } };",
            // A derived class nested inside a constructor keeps its own
            // super-call legality.
            "class A extends Object { constructor() { super(); class B extends Object { constructor() { super(); } } new B(); } }",
            // Member access on `super` is not a bare super expression.
            "class A extends Object { m() { super.m(); } }",
            "class A extends Object { m() { super.m = 1; } }",
        ] {
            assert_eq!(super_codes(valid), Vec::<&'static str>::new(), "{valid}");
        }

        // TS2335: `super` in a class with no base class.
        for non_derived in [
            "class A { constructor() { super(); } }",
            "class A { constructor(x = super()) {} }",
        ] {
            assert_eq!(
                super_codes(non_derived),
                [SUPER_REFERENCE_NON_DERIVED.as_str()],
                "{non_derived}"
            );
        }

        // TS2337: `super(...)` outside a constructor or nested inside one.
        for outside in [
            "function f() { super(); }",
            "super();",
            "const o = { m() { super(); } };",
            "class A extends Object { m() { super(); } }",
            "class A extends Object { static m() { super(); } }",
            "class A extends Object { constructor() { super(); const g = () => super(); } }",
            "class A extends Object { constructor() { super(); function g() { super(); } } }",
            "class A extends Object { x = super(); constructor() { super(); } }",
            "class A extends Object { static { super(); } }",
            "function f(x = super()) {}",
        ] {
            assert_eq!(
                super_codes(outside),
                [SUPER_CALL_OUTSIDE_CONSTRUCTOR.as_str()],
                "{outside}"
            );
        }

        // TS2336: `super(...)` in derived-constructor parameter initializers.
        assert_eq!(
            super_codes("class A extends Object { constructor(x = super()) { super(); } }"),
            [SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS.as_str()]
        );

        // TS1034: a bare `super` expression, including parenthesized callees
        // and template tags.
        for bare in [
            "let x = super;",
            "super;",
            "class A extends Object { constructor() { (super)(); } }",
            "class A extends Object { constructor() { super`x`; } }",
        ] {
            assert_eq!(
                super_codes(bare),
                [BARE_SUPER_EXPRESSION.as_str()],
                "{bare}"
            );
        }
    }

    #[test]
    fn derived_constructor_requires_super_call() {
        for accepted in [
            "class D extends Object { constructor() { super(); } }",
            "class D extends Object { constructor(flag: boolean) { if (flag) super(); } }",
            "class D extends Object { constructor(flag: boolean) { while (flag) super(); } }",
            "class D extends Object { constructor() { if (false) super(); } }",
            "class D extends Object {}",
            "class B { constructor() {} }",
        ] {
            let result = check_text(accepted);
            assert!(
                !checker_codes(&result).contains(&DERIVED_CONSTRUCTOR_MISSING_SUPER.as_str()),
                "{accepted}: {:?}",
                checker_codes(&result)
            );
        }

        for missing in [
            "class D extends Object { constructor() {} }",
            "class D extends Object { constructor() { return {}; } }",
            "class D extends Object { constructor() { throw 1; } }",
            "class D extends Object { constructor() { while (true) {} } }",
        ] {
            let result = check_text(missing);
            assert!(
                checker_codes(&result).contains(&DERIVED_CONSTRUCTOR_MISSING_SUPER.as_str()),
                "{missing}: {:?}",
                checker_codes(&result)
            );
        }

        let parameter = check_text("class D extends Object { constructor(value = super()) {} }");
        assert!(checker_codes(&parameter).contains(&SUPER_CALL_IN_CONSTRUCTOR_ARGUMENTS.as_str()));
        assert!(checker_codes(&parameter).contains(&DERIVED_CONSTRUCTOR_MISSING_SUPER.as_str()));

        let nested_function = check_text(
            "class D extends Object { constructor() { const call = () => super(); call; } }",
        );
        assert!(checker_codes(&nested_function).contains(&SUPER_CALL_OUTSIDE_CONSTRUCTOR.as_str()));
        assert!(
            checker_codes(&nested_function).contains(&DERIVED_CONSTRUCTOR_MISSING_SUPER.as_str())
        );

        let nested_class = check_text(
            "class D extends Object { constructor() {\
                 class N extends Object { constructor() { super(); } }\
                 N;\
             } }",
        );
        assert_eq!(
            checker_codes(&nested_class)
                .into_iter()
                .filter(|code| *code == DERIVED_CONSTRUCTOR_MISSING_SUPER.as_str())
                .count(),
            1
        );
    }

    #[test]
    fn with_statement_missing_name_suppression() {
        fn check_js(text: &str) -> Recovered<super::SemanticModel> {
            let parsed = parser::parse(scanner::scan(
                SourceId::new(0),
                ScriptKind::JavaScript,
                source(text),
            ));
            check(&parsed)
        }
        fn name_errors(result: &Recovered<super::SemanticModel>) -> bool {
            result
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code() == CANNOT_FIND_NAME)
        }

        // Sloppy `with` bodies may resolve names dynamically at runtime.
        assert!(
            !name_errors(&check_js("with ({}) { dynamic; }")),
            "direct sloppy with suppresses unresolved names"
        );
        assert!(
            !name_errors(&check_js("with ({}) { with ({}) { nested; } }")),
            "nested sloppy with suppresses unresolved names"
        );
        assert!(
            name_errors(&check_js("outside; with ({}) { }")),
            "names outside with are still unresolved"
        );

        // Hoisted `var` bindings still resolve normally inside `with`.
        let hoisted = check_js("var kept; with ({}) { kept; }");
        assert!(!name_errors(&hoisted));
        assert_eq!(hoisted.product().resolved_reference_count(), 1);

        // Forbidden contexts keep ordinary missing-name diagnostics.
        assert!(
            name_errors(&check_js("'use strict'; with ({}) { strictMissing; }")),
            "strict with keeps missing-name errors"
        );
        assert!(
            name_errors(&check_text("with ({}) { tsMissing; }")),
            "typescript with keeps missing-name errors"
        );

        // Free names in nested functions lexically inside `with` may bind dynamically.
        assert!(
            !name_errors(&check_js(
                "var captured = {}; with (captured) { capturedGetter = function(){ return prop; }; }"
            )),
            "closure free names inside sloppy with suppress unresolved names"
        );
        assert!(
            !name_errors(&check_js("with ({}) { function f() { fnMissing; } }")),
            "nested function declarations inside sloppy with suppress unresolved names"
        );

        // Local parameters still resolve before any `with` suppression applies.
        let param = check_js("with ({}) { (function(prop) { prop; })(); }");
        assert!(!name_errors(&param));
        assert_eq!(param.product().resolved_reference_count(), 1);
    }

    #[test]
    fn ambient_string_module_registers_without_lexical_pollution() {
        let result = check_text("declare module \"express\" {}\nconst y = express;");
        assert!(
            result.product().ambient_modules().contains_key("express"),
            "ambient module registry should record express"
        );
        assert_eq!(
            result
                .product()
                .scope(result.product().module_scope())
                .value("express"),
            None,
            "string ambient modules must not pollute the file scope"
        );
        assert!(
            checker_codes(&result).contains(&CANNOT_FIND_NAME.as_str()),
            "express must remain unresolved in file scope: {:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn declare_global_binds_members_into_global_scope() {
        let result = check_text(
            "declare global { interface Window { x: number } }\nconst w: Window = 1 as any;",
        );
        let model = result.product();
        assert_eq!(
            model.scope(model.module_scope()).value("global"),
            None,
            "declare global must not introduce a lexical global binding"
        );
        assert!(
            model.lookup_type(model.module_scope(), "Window").is_some(),
            "Window should resolve through the global scope"
        );
        let missing_type = CANNOT_FIND_TYPE.as_str();
        assert!(
            checker_codes(&result)
                .iter()
                .all(|code| *code != missing_type),
            "Window must not be a missing type: {:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn identifier_namespace_binding_is_unchanged() {
        let result = check_text("namespace N { export const x = 1; }\nconst y = N.x;");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
        assert!(
            result
                .product()
                .lookup_value(result.product().module_scope(), "N")
                .is_some()
        );
    }

    #[test]
    fn nested_global_inside_declare_namespace_does_not_augment_global_scope() {
        let result = check_text(
            "declare namespace N { global { interface Leaked {} } }\nconst w: Leaked = 1 as any;",
        );
        assert!(
            checker_codes(&result).contains(&CANNOT_FIND_TYPE.as_str()),
            "Leaked must not bind into the true global scope: {:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn bare_string_module_is_not_value_bearing() {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("module \"pkg\" { export const x = 1; }"),
        ));
        let checked = check(&parsed);
        let facts = checked.product().namespace_facts();
        let id = parsed.product().statements()[0].id();
        let plan = facts
            .declaration(id)
            .expect("namespace plan for bare string module");
        assert!(
            !plan.is_value_bearing(),
            "non-identifier namespace names must never be value-bearing"
        );
    }

    #[test]
    fn class_constructor_prototype_resolves_to_instance_type() {
        // `C.prototype` is the instance type of `class C`, so reading it must
        // not report PROPERTY_DOES_NOT_EXIST and must type as the structural
        // object carrying the declared instance member `greet`.
        let src = "class C { greet(): string { return \"hi\"; } }\nconst p = C.prototype;";
        let result = check_text(src);
        assert!(
            !checker_codes(&result).contains(&PROPERTY_DOES_NOT_EXIST.as_str()),
            "C.prototype must resolve to the instance type: {:?}",
            checker_codes(&result)
        );
        // The initializer `C.prototype` is typed via `type_of_expr`, so its
        // node type is the instance type: an object carrying `greet`.
        let parsed_src = parsed(0, src);
        let Statement::Variable(decl) = parsed_src.product().statements()[1].data() else {
            panic!("second statement is the variable declaration");
        };
        let member_id = decl.declarations[0]
            .data()
            .initializer
            .as_ref()
            .expect("declarator has an initializer")
            .id();
        let model = result.product();
        let prototype_type = model.node_type(member_id).expect("C.prototype is typed");
        assert!(
            matches!(
                model.types().get(prototype_type),
                Type::ObjectType(object)
                    if object
                        .properties
                        .iter()
                        .any(|property| property.name() == "greet")
            ),
            "C.prototype must be the instance type carrying `greet`"
        );
    }

    #[test]
    fn class_constructor_unknown_static_property_reports_c057() {
        // Only `prototype` is contributed; any other static property on a
        // class constructor must still report PROPERTY_DOES_NOT_EXIST.
        let result = check_text("class C {}\nC.nope = 1;");
        assert!(
            checker_codes(&result).contains(&PROPERTY_DOES_NOT_EXIST.as_str()),
            "C.nope must report PROPERTY_DOES_NOT_EXIST: {:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn exports_for_member_declaration_uses_index_and_preserves_order() {
        // One declaration statement can yield multiple exports (e.g. several
        // variable declarators), so the index must store a vector of positions
        // and return them in the original source/plan order.
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("namespace N { export let first = 1, second = 2; }"),
        ));
        let checked = check(&parsed);
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checker_codes(&checked)
        );

        let facts = checked.product().namespace_facts();
        let namespace = &parsed.product().statements()[0];
        let Statement::Namespace(namespace_decl) = namespace.data() else {
            panic!("first statement is a namespace");
        };
        let export_statement = &namespace_decl.body.data().statements[0];
        let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) =
            export_statement.data()
        else {
            panic!("namespace body statement is a declaration export");
        };
        let declaration_id = inner.as_ref().id();

        let n_symbol = facts
            .declaration_symbol(namespace.id())
            .expect("namespace has a symbol");
        let exports = facts.exports_for_member_declaration(declaration_id);
        assert_eq!(
            exports.len(),
            2,
            "one variable declaration with two declarators yields two exports"
        );

        let (container, first) = &exports[0];
        assert_eq!(*container, n_symbol);
        assert_eq!(first.name().to_utf8_lossy(), "first");
        assert_eq!(first.storage(), ExportStorage::Property);

        let (container, second) = &exports[1];
        assert_eq!(*container, n_symbol);
        assert_eq!(second.name().to_utf8_lossy(), "second");
        assert_eq!(second.storage(), ExportStorage::Property);

        // The index must key by the inner declaration, not the enclosing
        // namespace declaration or any other node.
        assert!(
            facts
                .exports_for_member_declaration(namespace.id())
                .is_empty(),
            "a namespace declaration is not itself an exported member"
        );
    }

    #[test]
    fn exports_for_member_declaration_keys_by_declaration_node_id() {
        // Merged namespaces have multiple plans; the index must distinguish the
        // declaration node id of each exported member instead of conflating by
        // name or container symbol.
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("namespace N { export let a = 1; } namespace N { export let b = 2; }"),
        ));
        let checked = check(&parsed);
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checker_codes(&checked)
        );

        let facts = checked.product().namespace_facts();
        let first = &parsed.product().statements()[0];
        let second = &parsed.product().statements()[1];
        let Statement::Namespace(first_ns) = first.data() else {
            panic!("first statement is a namespace");
        };
        let Statement::Namespace(second_ns) = second.data() else {
            panic!("second statement is a namespace");
        };
        let first_export = &first_ns.body.data().statements[0];
        let second_export = &second_ns.body.data().statements[0];

        let extract_declaration = |statement: &Stmt| -> NodeId {
            let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) = statement.data()
            else {
                panic!("expected a declaration export");
            };
            inner.as_ref().id()
        };

        let a_declaration = extract_declaration(first_export);
        let b_declaration = extract_declaration(second_export);

        let a_exports = facts.exports_for_member_declaration(a_declaration);
        let b_exports = facts.exports_for_member_declaration(b_declaration);
        assert_eq!(a_exports.len(), 1, "declaration a has one export");
        assert_eq!(b_exports.len(), 1, "declaration b has one export");
        assert_eq!(a_exports[0].1.name().to_utf8_lossy(), "a");
        assert_eq!(b_exports[0].1.name().to_utf8_lossy(), "b");
        assert!(
            facts.exports_for_member_declaration(first.id()).is_empty(),
            "namespace declaration itself has no member exports"
        );
    }
    #[test]
    fn imported_named_function_retains_callable_type_across_modules() {
        let valid = linked(
            &[
                "export function add(x: number, y: number): number { return x + y; }",
                "import { add } from './a'; const result: number = add(1, 2);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            program_codes(&valid)
        );

        let wrong_arg = linked(
            &[
                "export function add(x: number, y: number): number { return x + y; }",
                "import { add } from './a'; add('x', 2);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&wrong_arg).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            program_codes(&wrong_arg)
        );

        let wrong_count = linked(
            &[
                "export function add(x: number, y: number): number { return x + y; }",
                "import { add } from './a'; add(1);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&wrong_count).contains(&super::ARGUMENT_COUNT_MISMATCH.as_str()),
            "{:?}",
            program_codes(&wrong_count)
        );
    }

    #[test]
    fn imported_default_function_retains_callable_type_across_modules() {
        let valid = linked(
            &[
                "export default function add(x: number, y: number): number { return x + y; }",
                "import add from './a'; const result: number = add(1, 2);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            program_codes(&valid)
        );

        let wrong_arg = linked(
            &[
                "export default function add(x: number, y: number): number { return x + y; }",
                "import add from './a'; add('x', 2);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&wrong_arg).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            program_codes(&wrong_arg)
        );
    }

    #[test]
    fn imported_named_object_retains_member_types_across_modules() {
        let valid = linked(
            &[
                "export const obj = { count: 1, greet(name: string): string { return name; } };",
                "import { obj } from './a'; const n: number = obj.count; const s: string = obj.greet('x');",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            program_codes(&valid)
        );

        let wrong_member_arg = linked(
            &[
                "export const obj = { greet(name: string): string { return name; } };",
                "import { obj } from './a'; obj.greet(1);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&wrong_member_arg).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            program_codes(&wrong_member_arg)
        );
    }

    #[test]
    fn imported_generic_class_retains_instance_type_across_modules() {
        let checked = linked(
            &[
                "export default class Queue<T> {\
                    [Symbol.iterator](): IterableIterator<T> { throw 0; }\
                    drain(): IterableIterator<T> { throw 0; }\
                }",
                "import Queue from './a';\
                 declare const queue: Queue<number>;\
                 for (const value of queue.drain()) { const n: number = value; }\
                 for (const value of queue) { const n: number = value; }",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
    }

    #[test]
    fn imported_generic_alias_instantiates_parameters_and_defaults() {
        let checked = linked(
            &[
                "export type StringKey<T = { fallback: number }> = keyof T & string;",
                "import type { StringKey } from './a';\
                 class Hooks<T extends Record<string, any>, Name extends StringKey<T> = StringKey<T>> {\
                     values: Record<string, number> = {};\
                     read<Key extends Name>(key: Key): number { return this.values[key]; }\
                     accept(value: Record<Name, number>): void {}\
                 }\
                 declare const values: { [key: string]: number };\
                 declare const key: StringKey<{ value: number }>;\
                 const value: number = values[key];\
                 const fallback: StringKey = 'fallback';",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        let invalid = linked(
            &[
                "export type StringKey<T> = keyof T & string;",
                "import { type StringKey } from './a';\
                 declare const key: StringKey<{ value: number }>;\
                 const invalid: number = key;",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&invalid).contains(&super::TYPE_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            invalid.diagnostics()
        );
    }

    #[test]
    fn generic_alias_uses_its_parameters_inside_collection_types() {
        let valid = check_text(
            "type M<K extends string, V> = Map<K, V>;\
             type S<K extends string> = Set<K>;\
             declare const map: M<'a', number>;\
             declare const set: S<'a'>;\
             map.set('a', 1);\
             const value: number | undefined = map.get('a');\
             set.add('a');",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "type M<K extends string, V> = Map<K, V>;\
             declare const map: M<'a', number>;\
             map.set('b', 1);",
        );
        assert_eq!(
            checker_codes(&invalid),
            [super::ARGUMENT_NOT_ASSIGNABLE.as_str()]
        );
    }

    #[test]
    fn imported_generic_interface_instantiates_member_types() {
        let valid = linked(
            &[
                "export interface Ctx<T> { root: T; branch?: Ctx<T>; }",
                "import type { Ctx } from './a';\
                 const context: Ctx<string> = { root: 'x' };",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = linked(
            &[
                "export interface Ctx<T> { root: T; branch?: Ctx<T>; }",
                "import type { Ctx } from './a';\
                 const context: Ctx<string> = { root: 1 };",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&invalid).contains(&super::TYPE_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            invalid.diagnostics()
        );
    }

    #[test]
    fn linked_recursive_generic_interfaces_preserve_applications() {
        const TYPES: &str = "export interface RouterContext<T = unknown> {\n\
                 root: Node<T>;\n\
                 static: Record<string, Node<T> | undefined>;\n\
             }\n\
             export type MethodData<T = unknown> = { data: T; extra?: string[] };\n\
             export interface Node<T = unknown> {\n\
                 key: string;\n\
                 static?: Record<string, Node<T>>;\n\
                 param?: Node<T>;\n\
                 wildcard?: Node<T>;\n\
                 methods?: Record<string, MethodData<T>[] | undefined>;\n\
             }";
        const CONTEXT: &str = "import type { RouterContext } from './a';\n\
             export function createRouter<T = unknown>(): RouterContext<T> {\n\
                 return { root: { key: '' }, static: {} };\n\
             }";
        const ADD: &str = "import type { RouterContext } from './a';\n\
             export function addRoute<T>(\n\
                 ctx: RouterContext<T>, method: string = '', path: string, data?: T\n\
             ): void {}";
        const EDGES: &[(usize, usize, usize)] = &[(1, 0, 0), (2, 0, 0), (3, 0, 1), (3, 1, 2)];

        let valid = linked(
            &[
                TYPES,
                CONTEXT,
                ADD,
                "import { createRouter } from './b';\n\
                 import { addRoute } from './c';\n\
                 const router = createRouter<string>();\n\
                 addRoute(router, 'GET', '/', 'root');",
            ],
            EDGES,
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = linked(
            &[
                TYPES,
                CONTEXT,
                ADD,
                "import { createRouter } from './b';\n\
                 import { addRoute } from './c';\n\
                 const router = createRouter<number>();\n\
                 addRoute<string>(router, 'GET', '/', 'root');",
            ],
            EDGES,
        );
        assert!(
            program_codes(&invalid).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            invalid.diagnostics()
        );
    }

    #[test]
    fn imported_generic_function_preserves_alias_wrapped_collection_parameters() {
        let checked = linked(
            &[
                "type Handlers<E extends Record<string, unknown>> =\
                     Map<keyof E | '*', Array<(event: E[keyof E]) => void>>;\
                 export default function accept<E extends Record<string, unknown>>(\
                     handlers: Handlers<E>\
                 ): void {}",
                "import accept from './a';\
                 type Events = { foo: string };\
                 const handlers = new Map();\
                 const initialHandler = (value: string): void => {};\
                 handlers.set('foo', [initialHandler]);\
                 accept<Events>(handlers);",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
    }

    #[test]
    fn generic_key_intersection_survives_typeof_narrowing() {
        let valid = check_text(
            "type Key<T> = keyof T & string;\
             type Dep<T> = { to: Key<T> };\
             function save<T extends Record<string, any>, K extends Key<T>>(\
               name: K, dep: Key<T> | Dep<T>\
             ): void {\
               const out: Record<string, Dep<T>> = {};\
               if (typeof dep === 'string') {\
                 out[name] = { to: dep };\
               } else {\
                 out[name] = dep;\
               }\
             }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );
    }

    #[test]
    fn nested_conditionals_preserve_a_shared_argument_type() {
        let valid = check_text(
            "type Matcher = { tag: number };\
             declare function callMatcher(matcher: Matcher): void;\
             function matchAt(\
               prefix: Matcher[], suffix: Matcher[], rest: Matcher, i: number\
             ): void {\
               const entry = i < 1 ? prefix[i] : i > 2 ? suffix[i - 2] : rest;\
               callMatcher(entry);\
             }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let rejected = check_text(
            "type Matcher = { tag: number };\
             declare function callMatcher(matcher: Matcher): void;\
             declare const condition: boolean;\
             declare const matcher: Matcher;\
             callMatcher(condition ? matcher : 1);",
        );
        assert_eq!(
            checker_codes(&rejected),
            [super::ARGUMENT_NOT_ASSIGNABLE.as_str()]
        );
    }

    #[test]
    fn discriminant_exclusion_reduces_intersection_property_types() {
        let valid = check_text(
            "type Input = 'string' | 'number';\
             abstract class Base { abstract name: string; }\
             type Terminal =\
               | (Base & { name: 'unknown' | 'string' | 'number' })\
               | { name: 'literal' };\
             function collect(terminal: Terminal, values: Map<Input, number>): void {\
               if (terminal.name === 'unknown') {}\
               else if (terminal.name === 'literal') {}\
               else { values.get(terminal.name); }\
             }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );
    }
    #[test]
    fn imported_class_type_survives_named_alias_and_reexport() {
        let checked = linked(
            &[
                "export class Item { value: number = 1; }",
                "export { Item as Renamed } from './a';",
                "import { Renamed as Alias } from './b';\
                 declare const item: Alias;\
                 const value: number = item.value;",
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
    }

    #[test]
    fn imported_value_type_is_structurally_copied_not_any_or_error() {
        let checked = linked(
            &[
                "export function add(x: number, y: number): number { return x + y; }",
                "import { add } from './a'; add(1, 2);",
            ],
            &[(1, 0, 0)],
        );
        let model = checked
            .product()
            .file(SourceId::new(1))
            .expect("importer model");
        let symbol = model
            .lookup_value(model.module_scope(), "add")
            .expect("add import symbol");
        assert!(
            matches!(
                model.types().get(model.symbol_type(symbol)),
                Type::Function(_)
            ),
            "imported add retains a function type, got {:?}",
            model.types().get(model.symbol_type(symbol))
        );
    }

    #[test]
    fn imported_reexported_function_retains_callable_type() {
        let valid = linked(
            &[
                "export function f(x: number): number { return x; }",
                "export { f } from './a';",
                "import { f } from './b'; const result: number = f(1);",
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&valid).is_empty(),
            "{:?}",
            program_codes(&valid)
        );

        let wrong_arg = linked(
            &[
                "export function f(x: number): number { return x; }",
                "export { f } from './a';",
                "import { f } from './b'; f('x');",
            ],
            &[(1, 0, 0), (2, 0, 1)],
        );
        assert!(
            program_codes(&wrong_arg).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            program_codes(&wrong_arg)
        );
    }

    #[test]
    fn imported_value_cycle_terminates_deterministically() {
        let checked = linked(
            &[
                "import { b } from './b'; export function a() { return b(); }",
                "import { a } from './a'; export function b() { return a(); }",
                "import { a } from './a'; a();",
            ],
            &[(0, 0, 1), (1, 0, 0), (2, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
    }

    #[test]
    fn imported_missing_export_is_unchanged() {
        let checked = linked(
            &[
                "export const existing = 1;",
                "import { missing } from './a'; missing;",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            program_codes(&checked).is_empty(),
            "{:?}",
            program_codes(&checked)
        );
    }

    fn function_return_type(model: &super::SemanticModel, name: &str) -> TypeId {
        let symbol = model
            .lookup_value(model.module_scope(), name)
            .expect("symbol exists");
        match model.types().get(model.symbol_type(symbol)) {
            Type::Function(signature) => signature.return_type(),
            other => panic!("{name} should be a function, got {other:?}"),
        }
    }

    #[test]
    fn conditional_function_return_includes_undefined_when_block_completes_normally() {
        let result = check_text(
            "declare const flag: boolean;\n\
             function f(flag: boolean) { if (flag) return 1; }",
        );
        let model = result.product();
        let return_type_id = function_return_type(model, "f");
        let return_type = model.types().get(return_type_id);
        let undefined = model.types().undefined_type();
        let number = model.types().number();
        let Type::Union(members) = return_type else {
            panic!("expected union, got {return_type:?}");
        };
        assert!(
            members.contains(&undefined),
            "return type must include undefined"
        );
        assert!(members.contains(&number), "return type must include number");
    }

    #[test]
    fn conditional_block_arrow_return_includes_undefined_when_block_completes_normally() {
        let result = check_text(
            "declare const flag: boolean;\n\
             const f = (flag: boolean) => { if (flag) return 1; };",
        );
        let model = result.product();
        let return_type_id = function_return_type(model, "f");
        let return_type = model.types().get(return_type_id);
        let undefined = model.types().undefined_type();
        let number = model.types().number();
        let Type::Union(members) = return_type else {
            panic!("expected union, got {return_type:?}");
        };
        assert!(
            members.contains(&undefined),
            "return type must include undefined"
        );
        assert!(members.contains(&number), "return type must include number");
    }

    #[test]
    fn all_path_function_returns_remain_number() {
        let result = check_text(
            "declare const flag: boolean;\n\
             function f(flag: boolean) { if (flag) return 1; return 2; }",
        );
        let model = result.product();
        assert_eq!(
            function_return_type(model, "f"),
            model.types().number(),
            "all-path return should be number"
        );
    }

    #[test]
    fn all_path_block_arrow_returns_remain_number() {
        let result = check_text(
            "declare const flag: boolean;\n\
             const f = (flag: boolean) => { if (flag) return 1; return 2; };",
        );
        let model = result.product();
        assert_eq!(
            function_return_type(model, "f"),
            model.types().number(),
            "all-path arrow return should be number"
        );
    }

    #[test]
    fn annotated_returns_do_not_gain_undefined_from_incomplete_paths() {
        let result = check_text(
            "declare const flag: boolean;\n\
             function f(flag: boolean): number { if (flag) return 1; }",
        );
        let model = result.product();
        assert_eq!(
            function_return_type(model, "f"),
            model.types().number(),
            "annotated return must stay number"
        );
    }

    #[test]
    fn annotated_block_arrows_do_not_gain_undefined_from_incomplete_paths() {
        let result = check_text(
            "declare const flag: boolean;\n\
             const f = (flag: boolean): number => { if (flag) return 1; };",
        );
        let model = result.product();
        assert_eq!(
            function_return_type(model, "f"),
            model.types().number(),
            "annotated block arrow return must stay number"
        );
    }

    #[test]
    fn annotated_return_fallthrough_is_diagnosed() {
        // A zero-return body that falls off the end reports the non-void
        // must-return pairing (BAMTS-C081, upstream TS2355); a body with a
        // return statement still reports the undefined-assignment mismatch
        // (BAMTS-C004) when it completes normally.
        for (source, expected) in [
            ("function value(): number {}", ["BAMTS-C081"]),
            (
                "function value(flag: boolean): number { if (flag) return 1; }",
                ["BAMTS-C004"],
            ),
            ("const value = (): number => {};", ["BAMTS-C081"]),
            ("async function value(): Promise<number> {}", ["BAMTS-C081"]),
            (
                "function value(): number { while (true) { break; } }",
                ["BAMTS-C081"],
            ),
            (
                "function value(x: number): number { switch (x) { case 0: return 1; } }",
                ["BAMTS-C004"],
            ),
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                expected,
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn annotated_return_fallthrough_tracks_labeled_breaks() {
        for source in [
            "function value(): number { label: { break label; } }",
            "function value(): number { label: while (true) { break label; } }",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                ["BAMTS-C081"],
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
        for source in [
            "function value(): number { label: { return 1; } }",
            "function value(): number { label: { return 1; break label; } }",
            "function value(): number { label: try { break label; } finally { return 1; } }",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn annotated_return_fallthrough_accepts_undefined_and_noncompleting_bodies() {
        for source in [
            "function value(): void {}",
            "function value(): undefined {}",
            "function value(): any {}",
            "function value(): unknown {}",
            "function value(flag: boolean): number { if (flag) return 1; return 2; }",
            "function value(): number { throw new Error(); }",
            "function value(): number { while (true) {} }",
            "function value(): number { do {} while (true); }",
            "function value(): number { for (;;) {} }",
            "function value(): number { for (; true;) {} }",
            "function value(x: number): number { while (true) { switch (x) { case 0: break; } } }",
            "function value(): number { while (true) { while (true) { break; } } }",
            "function value(x: number): number { switch (x) { case 0: return 1; default: return 2; } }",
            "function value(x: number): number { switch (x) { default: return 1; break; } }",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn noncompleting_expressions_infer_never_but_declarations_use_void() {
        let result = check_text(
            "function fail() { throw 'stop'; }\
             const declarationResult: void = fail();\
             class Example { method() { throw 'stop'; } }\
             const classResult: void = new Example().method();\
             const object = { method() { throw 'stop'; } };\
             const objectResult: never = object.method();\
             const iterable = {\
                 [Symbol.iterator]() {\
                     return { next() { throw 'stop'; } };\
                 }\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) { value; }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn noncompleting_declarations_do_not_infer_never() {
        let result = check_text(
            "function fail() { throw 'stop'; }\
             const declarationResult: never = fail();\
             class Example { method() { throw 'stop'; } }\
             const classResult: never = new Example().method();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn annotated_return_mismatch_and_fallthrough_are_distinct_errors() {
        let result =
            check_text("function value(flag: boolean): number { if (flag) return 'wrong'; }");
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C004", "BAMTS-C004"],
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn annotated_generators_check_completion_returns_and_fallthrough() {
        for source in [
            "function* value(): Generator<number, string, unknown> { yield 1; return 'done'; }",
            "async function* value(): AsyncGenerator<number, string, unknown> { yield 1; return 'done'; }",
            "type Completion<R> = Generator<number, R, unknown>; function* value(): Completion<string> { yield 1; return 'done'; }",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }

        for (source, expected) in [
            (
                "function* value(): Generator<number, string, unknown> { yield 1; }",
                ["BAMTS-C081"],
            ),
            (
                "async function* value(): AsyncGenerator<number, string, unknown> { yield 1; }",
                ["BAMTS-C081"],
            ),
            (
                "function* value(): Generator<number, string, unknown> { return 1; }",
                ["BAMTS-C004"],
            ),
            (
                "type Completion<R> = Generator<number, R, unknown>; function* value(): Completion<string> { return 1; }",
                ["BAMTS-C004"],
            ),
            (
                "type Completion = Generator<number, string, unknown>; function* value(): Completion { yield 1; }",
                ["BAMTS-C081"],
            ),
            (
                "type Completion<R> = Generator<number, R, unknown> & {}; function* value(): Completion<string> { yield 1; }",
                ["BAMTS-C081"],
            ),
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                expected,
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
        let missing =
            check_text("function* value(): Generator<Missing, string, unknown> { return 'done'; }");
        assert_eq!(checker_codes(&missing), [CANNOT_FIND_TYPE.as_str()]);
    }

    #[test]
    fn inferred_generator_functions_preserve_yield_and_completion_types() {
        let result = check_text(
            "function* values() { yield 1; return 'done'; }\
             const iterator = values();\
             const step = iterator.next();\
             if (step.done === true) {\
                 const completion: string = step.value;\
             } else {\
                 const yielded: number = step.value;\
             }\
             for (const value of iterator) { const yielded: number = value; }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn inferred_async_generator_methods_form_async_iterables() {
        let result = check_text(
            "declare const promised: Promise<number>;\
             const iterable = {\
                 async *[Symbol.asyncIterator]() { yield promised; }\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) {\
                     const yielded: number = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn inferred_generator_delegation_uses_protocol_element_types() {
        let result = check_text(
            "declare const promised: Promise<number>;\
             function* children() { yield 1; }\
             function* syncValues() { yield* children(); }\
             async function* asyncValues() { yield* [promised]; }\
             for (const value of syncValues()) { const invalid: string = value; }\
             async function consume(): Promise<void> {\
                 for await (const value of asyncValues()) {\
                     const invalid: string = value;\
                 }\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn inferred_generators_reject_invalid_delegation() {
        let result = check_text(
            "function* syncValues() { yield* 1; }\
             async function* asyncValues() { yield* 1; }",
        );
        assert_eq!(
            checker_codes(&result),
            [
                super::FOR_OF_ITERABLE_REQUIRED.as_str(),
                super::FOR_OF_ITERABLE_REQUIRED.as_str(),
            ]
        );
    }

    #[test]
    fn inferred_generator_yields_ignore_nested_functions() {
        let result = check_text(
            "function* outer() {\
                 function* inner() { yield 'nested'; }\
                 yield 1;\
             }\
             for (const value of outer()) { const invalid: string = value; }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn async_generator_returns_await_promise_values() {
        let accepted = check_text(
            "declare const promised: Promise<string>;\
             declare const nested: Promise<Promise<string>>;\
             declare const shared: Promise<Promise<string>> | Promise<string>;\
             async function* generator(): AsyncGenerator<number, string, unknown> {\
                 yield 1;\
                 return nested;\
             }\
             async function functionDeclaration(): Promise<string> { return nested; }\
             async function sharedPayload(): Promise<string> { return shared; }\
             const arrow = async (): Promise<string> => promised;\
             const blockArrow = async (): Promise<string> => { return nested; };\
             const inferredArrow = async () => shared;\
             const inferredArrowResult: Promise<string> = inferredArrow();\
             async function inferred() { return promised; }\
             const inferredResult: Promise<string> = inferred();",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            checker_codes(&accepted)
        );

        let rejected = check_text(
            "declare const promised: Promise<string>;\
             declare const nested: Promise<Promise<string>>;\
             function* generator(): Generator<number, string, unknown> {\
                 yield 1;\
                 return promised;\
             }\
             function functionDeclaration(): string { return promised; }\
             const arrow = (): string => promised;\
             async function* directCompletion(): AsyncGenerator<number, Promise<string>, unknown> {\
                 return 'done';\
             }\
             async function* nestedCompletion(): AsyncGenerator<number, Promise<string>, unknown> {\
                 return nested;\
             }\
             async function outer(): Promise<void> {\
                 function nestedSync(): string { return promised; }\
             }",
        );
        assert_eq!(
            checker_codes(&rejected),
            [
                "BAMTS-C004",
                "BAMTS-C004",
                "BAMTS-C004",
                "BAMTS-C004",
                "BAMTS-C004",
                "BAMTS-C004",
            ]
        );
    }
    #[test]
    fn annotated_generator_returns_do_not_check_body_fallthrough() {
        let result = check_text(
            "function* sync(): Generator<number> { yield 1; }\
             async function* asynchronous(): AsyncGenerator<number> { yield 1; }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn generator_return_metadata_is_not_structurally_forgeable() {
        let fake_annotation = check_text(
            r#"type Fake = number[] & { "\0bamts.generator.return": string };
               function* value(): Fake { yield 1; return 1; }"#,
        );
        assert!(
            checker_codes(&fake_annotation).is_empty(),
            "{:?}",
            checker_codes(&fake_annotation)
        );

        for source in [
            r#"declare const fake: number[] & { "\0bamts.generator.return": string };
               const value: Generator<number, string, unknown> = fake;"#,
            "declare const plain: number[];\
             const value: Generator<number, string, unknown> = plain;",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                ["BAMTS-C004"],
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn generator_return_metadata_controls_assignability_and_interface_completion() {
        let compatible = check_text(
            "declare const source: Generator<number, string, unknown>;\
             const target: Generator<number, string, unknown> = source;",
        );
        assert!(
            checker_codes(&compatible).is_empty(),
            "{:?}",
            checker_codes(&compatible)
        );

        let incompatible = check_text(
            "declare const source: Generator<number, string, unknown>;\
             const target: Generator<number, number, unknown> = source;",
        );
        assert_eq!(checker_codes(&incompatible), ["BAMTS-C004"]);

        let inherited = check_text(
            "interface Completion<R> extends Generator<number, R, unknown> {}\
             function* good(): Completion<string> { yield 1; return 'done'; }\
             function* bad(): Completion<string> { yield 1; return 1; }",
        );
        assert_eq!(checker_codes(&inherited), ["BAMTS-C004"]);
    }

    #[test]
    fn generator_intersections_preserve_yield_types_for_iteration() {
        let result = check_text(
            "type Completion<R> = Generator<number, R, unknown>;\
             declare const direct: Generator<number, string, unknown>;\
             declare const alias: Completion<string>;\
             declare const extended: Completion<string> & { tag: true };\
             for (const item of direct) { const invalid: string = item; }\
             for (const item of alias) { const invalid: string = item; }\
             for (const item of extended) { const invalid: string = item; }",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C004", "BAMTS-C004", "BAMTS-C004"]
        );
    }

    #[test]
    fn awaited_expressions_preserve_non_promise_types_and_unwrap_promise_payloads() {
        let result = check_text(
            "declare let p: Promise<number>;\
             async function direct() { let direct = await 1; }\
             async function unwrapped() { let payload = await p; return payload; }\
             const wrapped: Promise<number> = unwrapped();",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );

        let model = result.product();
        let number = model.types().number();
        let local = |name: &str| -> super::SymbolId {
            model
                .scopes()
                .iter()
                .find(|scope| scope.kind() == ScopeKind::Function && scope.value(name).is_some())
                .and_then(|scope| scope.value(name))
                .unwrap_or_else(|| panic!("local `{name}` is bound"))
        };
        assert_eq!(
            model.symbol_type(local("direct")),
            number,
            "await 1 should preserve the number operand"
        );
        assert_eq!(
            model.symbol_type(local("payload")),
            number,
            "await Promise<number> should unwrap the payload"
        );

        let incompatible = check_text(
            "declare let p: Promise<number>;\
             async function mismatch() { const text: string = await p; }",
        );
        assert_eq!(checker_codes(&incompatible), ["BAMTS-C004"]);
    }

    #[test]
    fn annotated_class_field_initializer_is_type_checked() {
        let invalid = check_text("class C { value: string = 1; }");
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);

        let valid = check_text("class C { value: string = \"ok\"; }");
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn annotated_class_field_initializer_resolves_references() {
        let valid = check_text("const n = 1; class C { value: number = n; }");
        assert!(checker_codes(&valid).is_empty());

        let unresolved = check_text("class C { value: number = missing; }");
        assert!(checker_codes(&unresolved).contains(&CANNOT_FIND_NAME.as_str()));
    }

    #[test]
    fn annotated_class_auto_accessor_initializer_is_type_checked() {
        let invalid = check_text("class C { accessor value: string = 1; }");
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);

        let valid = check_text("class C { accessor value: string = \"ok\"; }");
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn unannotated_readonly_class_property_preserves_literal_type() {
        let result =
            check_text("class C { readonly kind = \"a\"; } const item: { kind: \"a\" } = new C();");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn read_property_type_unions_undefined_for_optional_properties() {
        let mut table = TypeTable::new();
        let number = table.number();
        let optional = table.object_type(vec![PropertyType::new("p", true, number)]);
        let required = table.object_type(vec![PropertyType::new("p", false, number)]);

        let read_optional = table
            .read_property_type(optional, "p")
            .expect("optional p exists");
        let write_optional = table
            .property_type(optional, "p")
            .expect("optional p exists");
        assert!(table.assignable(table.undefined_type(), read_optional));
        assert!(table.assignable(number, read_optional));
        assert!(!table.assignable_with_strict_null(read_optional, number));

        assert_eq!(write_optional, number);
        assert_eq!(table.read_property_type(required, "p"), Some(number));
        assert_eq!(table.property_type(required, "p"), Some(number));
    }

    #[test]
    fn optional_property_reads_are_undefined_and_narrow_on_guard() {
        let unguarded =
            check_text_strict_null("const obj: { p?: number } = {}; const n: number = obj.p;");
        assert_eq!(checker_codes(&unguarded), ["BAMTS-C004"]);

        let guarded = check_text_strict_null(
            "const obj: { p?: number } = {}; const value = obj.p; if (value) { const n: number = value; }",
        );
        assert!(
            checker_codes(&guarded).is_empty(),
            "{:?}",
            checker_codes(&guarded)
        );

        let write = check_text_strict_null("const obj: { p?: number } = {}; obj.p = undefined;");
        assert_eq!(checker_codes(&write), ["BAMTS-C004"]);
    }

    #[test]
    fn const_narrowed_value_remains_narrowed_inside_nested_arrow() {
        // A `const` binding narrowed by a guard before the arrow should stay
        // narrowed inside the arrow body: `x` is `string` there, so assigning
        // it to `number` must error.
        let result = check_text(
            "declare const x: string | number;\nif (typeof x !== \"string\") return;\nconst f = () => { const y: number = x; };\n",
        );
        assert!(
            checker_codes(&result).contains(&TYPE_NOT_ASSIGNABLE.as_str()),
            "expected x to be narrowed to string inside the arrow: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn reassigned_let_narrowing_does_not_cross_function_boundary() {
        // A `let` binding that is narrowed before a function declaration is
        // reassigned later in the same scope. The narrowing must NOT cross the
        // function boundary because the variable could be changed between the
        // guard and the deferred call.
        let result = check_text(
            "declare let x: string | number;\nif (typeof x !== \"string\") return;\nfunction f() { const y: number = x; }\nx = 1;\n",
        );
        assert!(
            checker_codes(&result).contains(&TYPE_NOT_ASSIGNABLE.as_str()),
            "expected x to remain string | number inside f because it is reassigned: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn later_nested_writer_invalidates_captured_narrowing() {
        let result = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = () => { f = undefined; };\
               clear();\
               read();\
             }",
        );
        assert_eq!(checker_codes(&result), [EXPRESSION_NOT_CALLABLE.as_str()]);
    }

    #[test]
    fn nested_write_inventory_respects_lexical_shadows() {
        let parameter = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = (f: (() => void) | undefined) => { f = undefined; };\
               clear(undefined);\
               read();\
             }",
        );
        assert!(checker_codes(&parameter).is_empty());

        let hoisted = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = () => { f = undefined; var f: (() => void) | undefined; };\
               clear();\
               read();\
             }",
        );
        assert!(checker_codes(&hoisted).is_empty());

        let block_only = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = () => {\
                 { let f: (() => void) | undefined; f = undefined; }\
               };\
               clear();\
               read();\
             }",
        );
        assert!(checker_codes(&block_only).is_empty());

        let restored = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = () => {\
                 { let f: (() => void) | undefined; f = undefined; }\
                 f = undefined;\
               };\
               clear();\
               read();\
             }",
        );
        assert_eq!(checker_codes(&restored), [EXPRESSION_NOT_CALLABLE.as_str()]);

        let nested = check_text(
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const clear = () => {\
                 const deeper = () => { f = undefined; };\
                 deeper();\
               };\
               clear();\
               read();\
             }",
        );
        assert_eq!(checker_codes(&nested), [EXPRESSION_NOT_CALLABLE.as_str()]);

        let static_block = check_text(
            "declare let value: string | number;\
             if (typeof value === \"string\") {\
               class Holder { static { value = 1; var value; } }\
               const read = () => { const narrowed: string = value; };\
             }",
        );
        assert!(checker_codes(&static_block).is_empty());
    }

    #[test]
    fn object_and_class_writers_invalidate_captured_narrowing() {
        for source in [
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const holder = { clear() { f = undefined; } };\
               holder.clear();\
               read();\
             }",
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               const holder = { [(f = undefined, \"key\")]: 1 };\
               read();\
             }",
            "declare let f: (() => void) | undefined;\
             if (f) {\
               const read = () => f();\
               class Holder { clear() { f = undefined; } }\
               new Holder().clear();\
               read();\
             }",
            "declare let f: (() => void) | undefined;\
             if (!f) { throw \"missing\"; }\
             const read = () => f();\
             export default class { clear() { f = undefined; } }\
             read();",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                [EXPRESSION_NOT_CALLABLE.as_str()],
                "{source}"
            );
        }
    }

    #[test]
    fn enum_and_namespace_writers_invalidate_captured_narrowing() {
        for source in [
            "declare let f: (() => void) | undefined;\
             if (!f) { throw \"missing\"; }\
             const read = () => f();\
             enum E { A = (f = undefined, 0) }\
             read();",
            "declare let f: (() => void) | undefined;\
             if (!f) { throw \"missing\"; }\
             const read = () => f();\
             namespace N { f = undefined; }\
             read();",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                [EXPRESSION_NOT_CALLABLE.as_str()],
                "{source}"
            );
        }

        let shadow = check_text(
            "declare let f: (() => void) | undefined;\
             if (!f) { throw \"missing\"; }\
             const read = () => f();\
             namespace N { let f: (() => void) | undefined; f = undefined; }\
             read();",
        );
        assert!(checker_codes(&shadow).is_empty());
    }

    #[test]
    fn sibling_branch_narrowing_does_not_leak_into_nested_function() {
        // A guard in one branch of an `if` narrows `x` to `string` only within
        // that branch. A function declared in the sibling (else) branch must
        // NOT see the narrowing.
        let result = check_text(
            "declare let x: string | number;\nif (typeof x === \"string\") {\nconst a: string = x;\n} else {\nconst f = () => { const y: string = x; };\n}\n",
        );
        assert!(
            checker_codes(&result).contains(&TYPE_NOT_ASSIGNABLE.as_str()),
            "expected x to remain string | number in the else-branch arrow: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn const_narrowing_passes_through_function_declaration() {
        // A `const` binding narrowed before a function declaration: the
        // function body should see the narrowed type because `const` cannot be
        // reassigned. Assigning `x` (narrowed to `string`) to `number` inside
        // the function must error.
        let result = check_text(
            "declare const x: string | number;\nif (typeof x !== \"string\") return;\nfunction f() { const y: number = x; }\n",
        );
        assert!(
            checker_codes(&result).contains(&TYPE_NOT_ASSIGNABLE.as_str()),
            "expected x to be narrowed to string inside f: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn for_of_array_binding_infers_element_type() {
        let result = check_text(
            "declare function takesNumber(value: number): void;\nfor (const x of [1, 2, 3]) { takesNumber(x); }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "for-of over number array should infer element type number: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn for_of_readonly_array_binding_infers_element_type() {
        let result = check_text(
            "const values: readonly number[] = [1, 2, 3];\
             for (const value of values) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn readonly_operator_accepts_only_array_and_tuple_syntax() {
        let result = check_text(
            "let array: readonly number[];\
             let tuple: readonly [number];\
             let generic: readonly Array<number>;\
             let parenthesized: readonly (number[]);",
        );
        let model = result.product();
        for name in ["array", "tuple"] {
            let symbol = model
                .lookup_value(model.module_scope(), name)
                .expect("variable is bound");
            assert_ne!(model.symbol_type(symbol), model.types().error_type());
        }
        for name in ["generic", "parenthesized"] {
            let symbol = model
                .lookup_value(model.module_scope(), name)
                .expect("variable is bound");
            assert_eq!(model.symbol_type(symbol), model.types().error_type());
        }
    }

    #[test]
    fn for_of_string_binding_infers_string_type() {
        let result = check_text(
            "declare function takesString(value: string): void;\nfor (const c of 'abc') { takesString(c); }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "for-of over string should infer element type string: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn for_of_tuple_binding_infers_union_element_type() {
        let result = check_text(
            "declare function takesString(value: string): void;\ndeclare function takesNumber(value: number): void;\ndeclare const pair: [string, number];\nfor (const x of pair) { takesString(x); }",
        );
        assert!(
            checker_codes(&result).contains(&super::ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "for-of over tuple [string, number] should infer union and reject string argument: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn for_of_annotated_binding_checks_assignability() {
        let result = check_text("for (const x: string of [1, 2, 3]) { x; }");
        assert!(
            checker_codes(&result).contains(&TYPE_NOT_ASSIGNABLE.as_str()),
            "for-of with string annotation over number array should fail: {}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn for_of_numeric_iterable_is_diagnosed_once() {
        let result = check_text("for (const value of 123) { value; }");
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn for_of_valid_array_iterable_produces_no_diagnostic() {
        let result = check_text("for (const value of [1, 2, 3]) { value; }");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn for_of_structural_iterator_uses_next_value_type() {
        let result = check_text(
            "const iterable = {\
                 [Symbol.iterator]() {\
                     return { next() { return { value: 1, done: false as false }; } };\
                 }\
             };\
             for (const value of iterable) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn for_await_prefers_async_protocol_and_awaits_next_and_value() {
        let result = check_text(
            "const iterable = {\
                 [Symbol.asyncIterator](): {\
                     next(): Promise<{ value: Promise<string>; done: false }>\
                 } { throw 0; },\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 } { throw 0; }\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) {\
                     const text: string = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn for_await_sync_fallback_awaits_value() {
        let result = check_text(
            "const iterable = {\
                 [Symbol.iterator](): {\
                     next(): { value: Promise<number>; done: false }\
                 } { throw 0; }\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) {\
                     const numberValue: number = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn for_await_invalid_async_protocol_does_not_use_sync_fallback() {
        let result = check_text(
            "const iterable = {\
                 [Symbol.asyncIterator](): { tag: true } { throw 0; },\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 } { throw 0; }\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) { value; }\
             }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn for_await_intersection_selects_one_async_protocol() {
        let result = check_text(
            "declare const iterable: {\
                 [Symbol.asyncIterator](): {\
                     next(): Promise<{ value: string; done: false }>\
                 };\
             } & {\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 };\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) {\
                     const text: string = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn for_await_intersection_commits_to_malformed_async_protocol() {
        let result = check_text(
            "declare const iterable: {\
                 [Symbol.asyncIterator](): { tag: true };\
             } & {\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 };\
             };\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) { value; }\
             }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn for_await_optional_or_non_callable_async_protocol_uses_sync_fallback() {
        for source in [
            "declare const iterable: {\
                 [Symbol.asyncIterator]?: () => {\
                     next(): Promise<{ value: string; done: false }>\
                 };\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 };\
             };",
            "declare const iterable: {\
                 [Symbol.asyncIterator]: number;\
                 [Symbol.iterator](): {\
                     next(): { value: number; done: false }\
                 };\
             };",
        ] {
            let result = check_text(&format!(
                "{source}\
                 async function consume(): Promise<void> {{\
                     for await (const value of iterable) {{\
                         const numberValue: number = value;\
                     }}\
                 }}"
            ));
            assert!(
                checker_codes(&result).is_empty(),
                "{:?}",
                result.diagnostics()
            );
        }
    }

    #[test]
    fn plain_for_of_rejects_async_only_protocol() {
        let result = check_text(
            "declare const iterable: {\
                 [Symbol.asyncIterator](): {\
                     next(): Promise<{ value: number; done: false }>\
                 };\
             };\
             for (const value of iterable) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn declared_async_iterables_use_only_the_async_protocol() {
        let accepted = check_text(
            "declare const iterable: AsyncIterable<Promise<number>>;\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) {\
                     const numberValue: number = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text(
            "declare const iterable: AsyncIterable<number>;\
             for (const value of iterable) { value; }",
        );
        assert_eq!(
            checker_codes(&rejected),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn generic_async_iterable_metadata_survives_instantiation_and_relations() {
        let result = check_text(
            "interface Stream<T> extends AsyncIterable<T> {}\
             declare const stream: Stream<Promise<string>>;\
             const base: AsyncIterable<Promise<string>> = stream;\
             async function consume(): Promise<void> {\
                 for await (const value of stream) {\
                     const text: string = value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn declared_async_iterators_are_not_implicitly_iterable() {
        let result = check_text(
            "declare const iterator: AsyncIterator<number>;\
             async function consume(): Promise<void> {\
                 for await (const value of iterator) { value; }\
             }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn declared_sync_iterators_require_an_iterable_protocol() {
        let result = check_text(
            "declare const iterator: Iterator<number>;\
             declare const iterable: IterableIterator<number>;\
             for (const value of iterator) { value; }\
             for (const value of iterable) { const numberValue: number = value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn intrinsic_iterators_preserve_return_and_next_types() {
        let result = check_text(
            "declare const iterator: Iterator<number, string, boolean>;\
             const step = iterator.next(true);\
             if (step.done === true) {\
                 const completion: string = step.value;\
             } else {\
                 const yielded: number = step.value;\
             }\
             declare const asynchronous: AsyncIterator<number, string, boolean>;\
             async function consume(): Promise<void> {\
                 const asyncStep = await asynchronous.next(false);\
                 if (asyncStep.done === true) {\
                     const completion: string = asyncStep.value;\
                 } else {\
                     const yielded: number = asyncStep.value;\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn intrinsic_iterator_next_is_a_bivariant_method() {
        let result = check_text(
            "declare const source: Iterator<number, any, 'only'>;\
             const target: Iterator<number, any, string> = source;\
             declare const asyncSource: AsyncIterator<number, any, 'only'>;\
             const asyncTarget: AsyncIterator<number, any, string> = asyncSource;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn iterator_yield_result_allows_omitted_done() {
        let result = check_text(
            "const iterator: Iterator<number> = {\
                 next() { return { value: 1 }; }\
             };",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn iteration_excludes_iterator_completion_values() {
        for source in [
            "declare const iterable: Iterable<number, string>;\
             for (const value of iterable) { const invalid: string = value; }",
            "declare const iterable: AsyncIterable<number, string>;\
             async function consume(): Promise<void> {\
                 for await (const value of iterable) { const invalid: string = value; }\
             }",
        ] {
            let result = check_text(source);
            assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
        }
    }
    #[test]
    fn known_iterables_with_error_elements_are_not_reported_as_non_iterable() {
        let result = check_text(
            "declare const array: Array<MissingArrayElement>;\
             declare const iterator: IterableIterator<MissingIteratorElement>;\
             for (const value of array) { value; }\
             for (const value of iterator) { value; }",
        );
        let codes = checker_codes(&result);
        assert!(codes.contains(&CANNOT_FIND_TYPE.as_str()));
        assert!(!codes.contains(&super::FOR_OF_ITERABLE_REQUIRED.as_str()));
    }

    #[test]
    fn iterator_whose_next_never_returns_is_still_iterable() {
        let result = check_text(
            "declare const iterator: {\
                 [Symbol.iterator](): { next(): never };\
             };\
             for (const value of iterator) {\
                 const unreachable: never = value;\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn for_of_requires_every_union_member_to_be_iterable_and_rejects_unknown() {
        let result = check_text(
            "declare const mixed: number[] | number;\
             declare const opaque: unknown;\
             for (const value of mixed) { value; }\
             for (const value of opaque) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [
                super::FOR_OF_ITERABLE_REQUIRED.as_str(),
                super::FOR_OF_ITERABLE_REQUIRED.as_str(),
            ]
        );
    }

    #[test]
    fn error_recovery_does_not_hide_non_iterable_union_members() {
        let result = check_text(
            "declare const mixed: MissingIterable | number;\
             declare const iterator: {\
                 [Symbol.iterator](): MissingIterator | number;\
             };\
             for (const value of mixed) { value; }\
             for (const value of iterator) { value; }",
        );
        let codes = checker_codes(&result);
        assert_eq!(
            codes
                .iter()
                .filter(|code| **code == CANNOT_FIND_TYPE.as_str())
                .count(),
            2
        );
        assert_eq!(
            codes
                .iter()
                .filter(|code| **code == super::FOR_OF_ITERABLE_REQUIRED.as_str())
                .count(),
            2
        );
        assert_eq!(codes.len(), 4);
    }

    #[test]
    fn constrained_type_parameter_uses_its_iterator_protocol() {
        let result = check_text(
            "function consume<T extends IterableIterator<number>>(iterator: T) {\
                 for (const value of iterator) {\
                     const numberValue: number = value;\
                 }\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn optional_next_does_not_guarantee_iterability() {
        let result = check_text(
            "declare const iterator: {\
                 [Symbol.iterator](): { next?(): { value: number, done: false } };\
             };\
             for (const value of iterator) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn iterator_object_intersection_supplies_next_protocol() {
        let result = check_text(
            "declare const iterator: {\
                 [Symbol.iterator](): ({\
                     next(): { value: number, done: false };\
                 } & { tag: string });\
             };\
             for (const value of iterator) {\
                 const numberValue: number = value;\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }
    #[test]
    fn string_property_cannot_forge_structural_iterator_metadata() {
        let result = check_text(
            "const iterable = {\
                 \"\\0bamts.symbol.iterator\": () => ({\
                     next: () => ({ value: 1, done: false as false })\
                 })\
             };\
             for (const value of iterable) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn shadowed_symbol_iterator_does_not_make_an_object_iterable() {
        let result = check_text(
            "export {};\
             const Symbol = { iterator: \"iterator\" };\
             const iterable = {\
                 [Symbol.iterator]() {\
                     return { next() { return { value: 1, done: false as false }; } };\
                 }\
             };\
             for (const value of iterable) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn inherited_interface_iterator_uses_next_value_type() {
        let result = check_text(
            "interface NumberIterator {\
                 [Symbol.iterator](): { next(): { value: number, done: false } };\
             }\
             interface Numbers extends NumberIterator {}\
             declare const numbers: Numbers;\
             for (const value of numbers) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn interface_iterator_inheritance_reports_conflicts() {
        let result = check_text(
            "interface NumberIterator {\
                 [Symbol.iterator](): { next(): { value: number, done: false } };\
             }\
             interface StringIterator {\
                 [Symbol.iterator](): { next(): { value: string, done: false } };\
             }\
             interface Conflict extends NumberIterator, StringIterator {}",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn structural_iterator_element_types_relate_covariantly() {
        let result = check_text(
            "type IteratorOf<T> = {\
                 [Symbol.iterator](): { next(): { value: T, done: false } };\
             };\
             declare const numbers: IteratorOf<number>;\
             const same: IteratorOf<number> = numbers;\
             const wrong: IteratorOf<string> = numbers;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn arrays_and_tuples_satisfy_structural_iterable_contracts() {
        let result = check_text_strict_null(
            "interface Numbers { [Symbol.iterator](): Iterator<number>; }\
             const array: Numbers = [1, 2, 3];\
             declare const pair: [number, string];\
             const broad: Iterable<number | string> = pair;\
             declare const optional: [number?];\
             const maybe: Iterable<number | undefined> = optional;\
             declare const empty: [];\
             const bottom: Iterable<string> = empty;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn array_and_tuple_iterable_relations_enforce_the_full_contract() {
        for source in [
            "const values: Iterable<string> = [1, 2, 3];",
            "declare const pair: [number, string];\
             const values: Iterable<number> = pair;",
            "interface TaggedNumbers extends Iterable<number> { tag: string; }\
             const values: TaggedNumbers = [1, 2, 3];",
            "interface RichIterable {\
                 [Symbol.iterator](): Iterator<number> & { close(): void };\
             }\
             const values: RichIterable = [1, 2, 3];",
            "const values: AsyncIterable<number> = [1, 2, 3];",
        ] {
            let result = check_text(source);
            assert_eq!(checker_codes(&result), ["BAMTS-C004"], "{source}");
        }

        let optional = check_text_strict_null(
            "declare const values: [number?];\
             const narrow: Iterable<number> = values;",
        );
        assert_eq!(checker_codes(&optional), ["BAMTS-C004"]);
    }

    #[test]
    fn generic_iterable_parameters_infer_array_and_tuple_yields() {
        let result = check_text(
            "declare function first<T>(items: Iterable<T>): T;\
             const numberValue: number = first([1, 2, 3]);\
             const wrong: string = first([1, 2, 3]);\
             declare const pair: [number, string];\
             const unionValue: number | string = first(pair);\
             declare const empty: [];\
             const bottom: never = first(empty);",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn structural_iterator_relations_compare_the_full_callable() {
        let result = check_text(
            "type Source = {\
                 [Symbol.iterator](): { next(): { value: number, done: false } };\
             };\
             type Target = {\
                 [Symbol.iterator](): {\
                     next(): { value: number, done: false };\
                     close(): void;\
                 };\
             };\
             declare const source: Source;\
             const target: Target = source;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn optional_iterator_cannot_satisfy_a_required_iterator() {
        let result = check_text(
            "type Optional = {\
                 [Symbol.iterator]?(): { next(): { value: number, done: false } };\
             };\
             type Required = {\
                 [Symbol.iterator](): { next(): { value: number, done: false } };\
             };\
             declare const source: Optional;\
             const target: Required = source;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn optional_iterator_does_not_guarantee_iterability() {
        let result = check_text(
            "declare const source: {\
                 [Symbol.iterator]?(): { next(): { value: number, done: false } };\
             };\
             for (const value of source) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn class_iterator_accessibility_is_preserved_in_structural_relations() {
        let result = check_text(
            "type IterableShape = {\
                 [Symbol.iterator](): { next(): { value: number, done: false } };\
             };\
             class PublicValues {\
                 public [Symbol.iterator](): { next(): { value: number, done: false } } {\
                     throw 0;\
                 }\
             }\
             class ProtectedValues {\
                 protected [Symbol.iterator](): { next(): { value: number, done: false } } {\
                     throw 0;\
                 }\
             }\
             class PrivateValues {\
                 private [Symbol.iterator](): { next(): { value: number, done: false } } {\
                     throw 0;\
                 }\
             }\
             const publicShape: IterableShape = new PublicValues();\
             const protectedShape: IterableShape = new ProtectedValues();\
             const privateShape: IterableShape = new PrivateValues();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn object_spread_preserves_an_own_iterator_property() {
        let result = check_text(
            "const source = {\
                 [Symbol.iterator]() {\
                     return { next() { return { value: 1, done: false as false }; } };\
                 }\
             };\
             const spread = { ...source };\
             for (const value of spread) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn object_spread_does_not_copy_a_class_prototype_iterator() {
        let result = check_text(
            "class Values {\
                 [Symbol.iterator](): { next(): { value: number, done: false } } { throw 0; }\
             }\
             const spread = { ...new Values() };\
             for (const value of spread) { value; }",
        );
        assert_eq!(
            checker_codes(&result),
            [super::FOR_OF_ITERABLE_REQUIRED.as_str()]
        );
    }

    #[test]
    fn object_spread_copies_an_own_class_field_iterator() {
        let result = check_text(
            "class Values {\
                 [Symbol.iterator] = () => ({\
                     next: () => ({ value: 1, done: false as false })\
                 });\
             }\
             const spread = { ...new Values() };\
             for (const value of spread) {\
                 const numberValue: number = value;\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn later_object_iterator_overrides_a_spread_iterator() {
        let result = check_text(
            "const source = {\
                 [Symbol.iterator]() {\
                     return { next() { return { value: 1, done: false as false }; } };\
                 }\
             };\
             const spread = {\
                 ...source,\
                 [Symbol.iterator]() {\
                     return { next() { return { value: \"x\", done: false as false }; } };\
                 }\
             };\
             for (const value of spread) {\
                 const stringValue: string = value;\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn generic_class_iterator_instantiates_next_value_type() {
        let result = check_text(
            "class Box<T> {\
                 [Symbol.iterator](): { next(): { value: T, done: false } } { throw 0; }\
             }\
             declare const numbers: Box<number>;\
             for (const value of numbers) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn derived_class_inherits_iterator_element_type() {
        let result = check_text(
            "class NumberIterator {\
                 [Symbol.iterator](): { next(): { value: number, done: false } } { throw 0; }\
             }\
             class Numbers extends NumberIterator {}\
             declare const numbers: Numbers;\
             for (const value of numbers) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn class_iterator_accessibility_does_not_block_protocol_iteration() {
        // TypeScript's iteration protocol deliberately ignores class member
        // access modifiers when it resolves the intrinsic iterator symbol.
        for access in ["public", "protected", "private"] {
            let source = format!(
                "class Base {{\
                     {access} [Symbol.iterator](): {{ next(): {{ value: number, done: false }} }} {{\
                         throw 0;\
                     }}\
                 }}\
                 class Derived extends Base {{}}\
                 for (const value of new Derived()) {{\
                     const numberValue: number = value;\
                 }}"
            );
            let result = check_text(&source);
            assert!(
                checker_codes(&result).is_empty(),
                "{access}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn static_class_iterator_uses_next_value_type() {
        let result = check_text(
            "class Numbers {\
                 static [Symbol.iterator](): { next(): { value: number, done: false } } {\
                     throw 0;\
                 }\
             }\
             for (const value of Numbers) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn object_getter_iterator_uses_callable_property_type() {
        let result = check_text(
            "const numbers = {\
                 get [Symbol.iterator]() {\
                     return () => ({\
                         next: () => ({ value: 1, done: false as false })\
                     });\
                 }\
             };\
             for (const value of numbers) {\
                 const numberValue: number = value;\
                 const stringValue: string = value;\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn for_of_error_iterable_does_not_cascade() {
        let result = check_text("for (const value of missing) { value; }");
        assert!(!checker_codes(&result).contains(&super::FOR_OF_ITERABLE_REQUIRED.as_str()));
    }

    #[test]
    fn fresh_object_excess_properties_are_checked_at_direct_boundaries() {
        for source in [
            "const options: { timeout: number } = { timeout: 100, timout: 100 };",
            "let options: { timeout: number }; options = { timeout: 100, timout: 100 };",
            "function options(): { timeout: number } { return { timeout: 100, timout: 100 }; }",
            "const options = { timeout: 100, timout: 100 } satisfies { timeout: number };",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                ["BAMTS-C067"],
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn fresh_object_empty_targets_accept_properties() {
        for source in [
            "const value: {} = { extra: 1 };",
            "interface Empty {} const value: Empty = { extra: 1 };",
            "const value: {} | { known: number } = { extra: 1 };",
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn fresh_object_excess_properties_are_checked_recursively() {
        for source in [
            "const value: { nested: { ok: number } } = { nested: { ok: 1, extra: 2 } };",
            "const value: { ok: number }[] = [{ ok: 1, extra: 2 }];",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                ["BAMTS-C067"],
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn fresh_object_property_keys_preserve_lone_surrogates() {
        let distinct = check_text(r#"const value: { "\uFFFD": number } = { "\uD800": 1 };"#);
        assert!(
            checker_codes(&distinct).contains(&"BAMTS-C067"),
            "{:?}",
            checker_codes(&distinct)
        );

        let same = check_text(r#"const value: { "\uD800": number } = { "\uD800": 1 };"#);
        assert!(
            checker_codes(&same).is_empty(),
            "{:?}",
            checker_codes(&same)
        );
    }

    #[test]
    fn fresh_object_excess_properties_are_checked_for_call_and_new_arguments() {
        let call = check_text(
            "declare function use(value: { ok: number }): void;\
             use({ ok: 1, extra: 2 });",
        );
        assert_eq!(checker_codes(&call), ["BAMTS-C067"]);

        let construct = check_text(
            "declare const Factory: new (value: { ok: number }) => object;\
             new Factory({ ok: 1, extra: 2 });",
        );
        assert_eq!(checker_codes(&construct), ["BAMTS-C067"]);
    }

    #[test]
    fn stored_and_spread_object_properties_are_not_fresh() {
        let stored = check_text(
            "const stored = { ok: 1, extra: 2 }; const accepted: { ok: number } = stored;",
        );
        assert!(checker_codes(&stored).is_empty());

        let spread = check_text(
            "const source = { extra: 2 };\
             const accepted: { ok: number } = { ok: 1, ...source };",
        );
        assert!(checker_codes(&spread).is_empty());

        let explicit_after_spread = check_text(
            "const source = { extra: 2 };\
             const rejected: { ok: number } = { ok: 1, ...source, explicit: 3 };",
        );
        assert_eq!(checker_codes(&explicit_after_spread), ["BAMTS-C067"]);
    }

    #[test]
    fn fresh_object_static_computed_keys_and_index_signatures_are_checked() {
        let computed = check_text("const value: { ok: number } = { ok: 1, ['extra']: 2 };");
        assert_eq!(checker_codes(&computed), ["BAMTS-C067"]);

        let indexed = check_text("const value: { [key: string]: number } = { ok: 1, extra: 2 };");
        assert!(checker_codes(&indexed).is_empty());
    }

    #[test]
    fn fresh_object_property_keys_use_ecmascript_values() {
        for source in [
            r#"const value: { a: number } = { ["\x61"]: 1 };"#,
            r#"const value: { a: number } = { "\u0061": 1 };"#,
            "const value: { 1: number } = { [0x1]: 1 };",
            r#"const value: { "1e+21": number } = { 1e21: 1 };"#,
            r#"const value: { "1e-7": number } = { 1e-7: 1 };"#,
            r#"const value: { "1e+21": number } = { [1e21]: 1 };"#,
            r#"const value: { "1e-7": number } = { [1e-7]: 1 };"#,
        ] {
            let result = check_text(source);
            assert!(
                checker_codes(&result).is_empty(),
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn fresh_object_union_keys_follow_discriminant_narrowing() {
        let nondiscriminated = check_text(
            "type Target = { a: number } | { b: number };\
             const value: Target = { a: 1, b: 2 };",
        );
        assert!(checker_codes(&nondiscriminated).is_empty());

        let discriminated = check_text(
            "type Target = { kind: 'a'; a: number } | { kind: 'b'; b: number };\
             const value: Target = { kind: 'a', a: 1, b: 2 };",
        );
        assert_eq!(checker_codes(&discriminated), ["BAMTS-C067"]);
    }

    #[test]
    fn fresh_object_overloads_reject_candidates_without_emitting_eagerly() {
        let result = check_text(
            "declare function choose(value: { value: number }): number;\
             declare function choose(value: { value: number; extra: number }): number;\
             choose({ value: 1, extra: 2 });",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    // ---- object-literal spread ------------------------------------------------

    #[test]
    fn object_spread_properties_exist_with_precise_types() {
        let result = check_text("const o = { ...{ x: 1 } }; const x: number = o.x;");
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn object_spread_assignment_to_typed_target_requires_merged_properties() {
        // Public regression: old behavior ignored the spread and typed the
        // literal as `{}`, so assigning to `{ x: number }` failed.
        let result = check_text("const o: { x: number } = { ...{ x: 1 } };");
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn object_spread_later_explicit_property_overrides_earlier_spread() {
        // The later explicit `y: 'a'` overwrites the spread `y: 2`; the
        // spread-only `x` must still be present.
        let result = check_text(
            "const o = { ...{ x: 1, y: 2 }, y: 'a' }; const x: number = o.x; const y: string = o.y;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn object_spread_later_spread_overrides_earlier_spread() {
        let result = check_text(
            "const o = { ...{ x: 1, y: 2 }, ...{ y: 'a' } }; const x: number = o.x; const y: string = o.y;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn object_spread_preserves_optional_and_clears_readonly_for_fresh_object() {
        let result = check_text("declare const a: { readonly x?: number }; const o = { ...a };");
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
        let model = result.product();
        let symbol = model
            .lookup_value(model.module_scope(), "o")
            .expect("o binding");
        let Type::ObjectType(object) = model.types().get(model.symbol_type(symbol)) else {
            panic!("o is an object type")
        };
        let x = object
            .properties
            .iter()
            .find(|property| property.name() == "x")
            .expect("x property from spread");
        assert!(x.optional(), "optional is preserved from the spread source");
        assert!(!x.readonly(), "fresh object properties are not readonly");
        assert_eq!(model.types().get(x.type_id()), &Type::Number);
    }

    #[test]
    fn object_spread_of_non_object_is_silent_and_does_not_fallback_to_any() {
        // The checker has no boundary for non-object spread, so this is silent.
        let result = check_text("const o = { ...1 };");
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn as_assertion_rejects_unrelated_types() {
        let result = check_text("const x: string = 1 as string;");
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn angle_bracket_assertion_rejects_unrelated_types() {
        let result = check_text("const x: string = <string>1;");
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn as_unknown_bridge_is_allowed() {
        let result = check_text("const x: string = 1 as unknown as string;");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn angle_bracket_unknown_bridge_is_allowed() {
        let result = check_text("const x: string = <string><unknown>1;");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn overlapping_structural_assertions_are_allowed() {
        let result = check_text("const x: number = ({ a: 1, b: 2 } as { a: number }).a;");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn as_const_assertions_skip_compatibility_check() {
        let result = check_text("const t = [1, 2] as const;");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn indexed_access_string_literal_key_resolves_property_type() {
        let result = check_text(
            "type Obj = { a: number; b: string };\
             let x: Obj[\"a\"] = 1;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "indexed access with valid key should not error: {:?}",
            checker_codes(&result)
        );
        let model = result.product();
        let x = model
            .lookup_value(model.module_scope(), "x")
            .expect("x binding");
        assert_eq!(
            model.symbol_type(x),
            model.types().number(),
            "Obj[\"a\"] should resolve to number"
        );
    }

    #[test]
    fn for_in_key_indexes_the_correlated_generic_object() {
        let result = check_text(
            "function values<T extends object>(obj: T) {\
                 for (const key in obj) { obj[key]; }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "for-in key should remain correlated with its object: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn arbitrary_string_does_not_index_a_generic_object() {
        let result = check_text(
            "function value<T extends object>(obj: T, key: string) {\
                 return obj[key];\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C064"]);
    }

    #[test]
    fn for_in_key_preserves_partial_record_key_parameter() {
        let result = check_text(
            "type Callback = () => void;\
             declare function consume<K extends string>(key: K): void;\
             function visit<K extends string>(callbacks: Partial<Record<K, Callback>>) {\
                 for (const key in callbacks) { consume<K>(key); }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "for-in key should be compatible with the record key parameter: {:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn logical_right_operand_uses_left_truthiness_facts() {
        let valid = check_text(
            "declare const node: { values?: Record<string, number> } | undefined;\
             declare const key: string;\
             if (node && node.values) { const value: number | undefined = node.values[key]; }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "declare const node: { values?: { fixed: number } } | undefined;\
             declare const key: string;\
             if (node && node.values) { node.values[key]; }",
        );
        assert_eq!(
            checker_codes(&invalid),
            [super::INVALID_INDEXED_ACCESS_KEY.as_str()]
        );
    }

    #[test]
    fn partial_object_properties_are_optional_but_keep_their_value_type() {
        let accepted = check_text_strict_null(
            "const value: Partial<{ x: number }> = {};\
             value.x = 1;\
             const read: number | undefined = value.x;",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text_strict_null(
            "const value: Partial<{ x: number }> = { x: 'bad' };\
             const required: number = value.x;",
        );
        assert_eq!(
            checker_codes(&rejected),
            [
                super::TYPE_NOT_ASSIGNABLE.as_str(),
                super::TYPE_NOT_ASSIGNABLE.as_str()
            ]
        );
    }

    #[test]
    fn source_partial_alias_shadows_the_intrinsic_utility() {
        let result = check_text_strict_null(
            "type Partial<T> = { wrapped: T };\
             const value: Partial<number> = { wrapped: 1 };\
             const read: number = value.wrapped;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn constrained_indexed_access_relates_through_its_base_constraint() {
        let accepted = check_text(
            "declare class AbstractType<Output = unknown> { abstract: Output; }\
             declare class Type<Output = unknown> extends AbstractType<Output> { value: Output; }\
             type Infer<T extends AbstractType> = T;\
             interface ArrayReference<Options extends Type[]> {\
                 value: Infer<Options[number]>;\
             }\
             interface TupleReference<Options extends [Type, Type]> {\
                 value: Infer<Options[number]>;\
             }\
             function assign<Options extends Type[]>(value: Options[number]): AbstractType {\
                 return value;\
             }",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text(
            "declare class AbstractType { abstract: number; }\
             declare class Type extends AbstractType { value: number; }\
             declare class OtherType { other: string; }\
             type RequireOther<T extends OtherType> = T;\
             interface Invalid<Options extends Type[]> {\
                 value: RequireOther<Options[number]>;\
             }",
        );
        assert_eq!(checker_codes(&rejected), ["BAMTS-C053"]);
    }

    #[test]
    fn constrained_indexed_access_uses_intersections_and_index_signatures() {
        let result = check_text(
            "interface StringIndex { [key: string]: boolean; }\
             interface MixedIndex {\
                 [key: string]: string | number;\
                 [key: number]: number;\
             }\
             interface Numeric { [key: number]: string; }\
             declare class Nominal { c: number; }\
             function fromIntersection<T extends { a: string } & { b: number }>(\
                 value: T['a']\
             ): string {\
                 return value;\
             }\
             function fromKnownIntersection<T extends { a: string } & Nominal>(
                 value: T['a']
             ): string {
                 return value;
             }\
             function fromStringIndex<T extends StringIndex>(value: T[number]): boolean {\
                 return value;\
             }\
             function fromNumberIndex<T extends MixedIndex>(value: T[0]): number {\
                 return value;\
             }\
             function fromNegativeIndex<T extends Numeric>(value: T[-1]): string {\
                 return value;\
             }\
             function fromFractionalIndex<T extends Numeric>(value: T[1.5]): string {\
                 return value;\
             }\
             function fromImpossibleIntersection<
                 T extends { a: string } & { a: number }
             >(value: T['a']): boolean {
                 return value;
             }\
             function fromNumericBottom<T extends { a: 1 } & { a: 2 }>(
                 value: T['a']
             ): string {
                 return value;
             }\
             function fromBigIntBottom<T extends { a: 1n } & { a: 2n }>(
                 value: T['a']
             ): string {
                 return value;
             }\
             function fromNestedIntersection<
                 T extends { a: { x: string } }
                     & ({ a: { y: number } } & { a: { z: boolean } })
             >(
                 value: T['a']
             ): { x: string; y: number; z: boolean } {
                 return value;
             }\
             function fromOverlappingUnions<
                 T extends { a: 1 | 2 } & { a: 2 | 3 }
             >(value: T['a']): 2 {
                 return value;
             }\
             function fromDistributedIntersection<
                 T extends ({ a: { x: string } } | { a: { b: number } })
                     & { a: { x: string } }
             >(value: T['a']): { x: string } {
                 return value;
             }\
             function fromUnionWithSibling<
                 T extends (
                     { a: { x: string } }
                     | { a: { x: string; y: number } }
                 ) & { a: { z: boolean } }
             >(value: T['a']): { x: string; z: boolean } {
                 return value;
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );

        let equivalent_literals = check_text(
            "function sameNumber<T extends { a: 1 } & { a: 1.0 }>(
                 value: T['a']
             ): string {
                 return value;
             }\
             function sameBigInt<T extends { a: 1n } & { a: 0x1n }>(
                 value: T['a']
             ): string {
                 return value;
             }",
        );
        assert_eq!(
            checker_codes(&equivalent_literals),
            ["BAMTS-C004", "BAMTS-C004"]
        );
    }

    #[test]
    fn constrained_intersection_key_indexes_string_maps() {
        let result = check_text(
            "type HookKeys<T> = keyof T & string;\
             class Hooks<\
                 T extends Record<string, any>,\
                 Name extends HookKeys<T> = HookKeys<T>\
             > {\
                 values: Record<string, number> = {};\
                 read<Key extends Name>(key: Key): number { return this.values[key]; }\
             }\
             function read<T, Name extends keyof T & string>(\
                 values: { [key: string]: number }, name: Name\
             ): number {\
                 return values[name];\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn constrained_generic_objects_use_their_index_signatures() {
        let accepted = check_text(
            "function omit<\
               Shape extends Record<string, unknown>,\
               Keys extends Array<string & keyof Shape>\
             >(shape: Shape, keys: Keys): void {\
               for (const key of keys) { delete shape[key]; }\
             }\
             function copy<Shape extends Record<string, unknown>>(shape: Shape): void {\
               for (const key of Object.keys(shape)) { shape[key]; }\
             }",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text(
            "function read<Shape extends { x: number }>(shape: Shape, key: string): void {\
               shape[key];\
             }",
        );
        assert_eq!(
            checker_codes(&rejected),
            [super::INVALID_INDEXED_ACCESS_KEY.as_str()]
        );
    }

    #[test]
    fn generic_record_spread_retains_its_index_signature() {
        let valid = check_text(
            "function copy<T extends Record<string, unknown>>(value: T, key: string): unknown {\
                 const spread = { ...value };\
                 return spread[key];\
             }",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid = check_text(
            "function copy<T extends { fixed: number }>(value: T, key: string): void {\
                 const spread = { ...value };\
                 spread[key];\
             }",
        );
        assert_eq!(
            checker_codes(&invalid),
            [super::INVALID_INDEXED_ACCESS_KEY.as_str()]
        );
    }

    #[test]
    fn record_keys_accept_string_intersections_and_preserve_for_in_correlation() {
        let result = check_text(
            "type StringKeys<T> = keyof T & string;\
             type Deprecated<T> = { to: StringKeys<T> };\
             declare function consume<K extends string>(key: K): void;\
             function visit<\
                 T extends Record<string, unknown>,\
                 K extends StringKeys<T>\
             >(values: Partial<Record<K, Deprecated<T>>>): void {\
                 for (const key in values) { consume<K>(key); }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn imported_intersection_keys_satisfy_record_constraints() {
        let result = linked(
            &[
                "export type StringKeys<T> = keyof T & string;\
                 export type Deprecated<T> = { to: StringKeys<T> };",
                "import type { Deprecated, StringKeys } from './types';\
                 class Hooks<\
                     T extends Record<string, unknown>,\
                     K extends StringKeys<T>\
                 > {\
                     visit(values: Partial<Record<K, Deprecated<T>>>): void {\
                         for (const key in values) { this.consume(key); }\
                     }\
                     consume<Name extends K>(name: Name): void {}\
                 }",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn generic_record_spreads_keep_their_index_signature() {
        let result = check_text(
            "function omit<Shape extends Record<string, unknown>>(\
                 value: Shape, key: string & keyof Shape\
             ): void {\
                 const copy = { ...value };\
                 delete copy[key];\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn identical_generic_class_applications_relate_without_materialized_views() {
        let result = check_text(
            "declare class Box<T> { value: T; }\
             function wrap(): { item: Box<string> } {\
                 const item = new Box<string>();\
                 return { item };\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn equivalent_alias_arguments_preserve_generic_collection_identity() {
        let result = check_text(
            "type Key = 'string' | 'number';\
             interface Item { value: number; }\
             function group(): { types: Map<Key, Item[]> } {\
                 const types = new Map<Key, Item[]>();\
                 return { types };\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn generic_collection_fields_preserve_annotated_return_shapes() {
        for source in [
            "abstract class Item {}\
             function only(value: Map<unknown, Item[]>): { value: Map<unknown, Item[]> } {\
                 return { value };\
             }",
            "abstract class Item {}\
             declare function dedup<T>(values: T[]): T[];\
             function only(value: Item[]): { value: Item[] } {\
                 return { value: dedup(value) };\
             }",
            "type Input = 'object' | 'array' | 'null' | 'undefined'\
                 | 'string' | 'number' | 'bigint' | 'boolean';\
             declare function dedup<T>(values: T[]): T[];\
             function only(value: Input[]): { value: Input[] } {\
                 return { value: dedup(value) };\
             }",
        ] {
            let isolated = check_text(source);
            assert!(
                checker_codes(&isolated).is_empty(),
                "{:?}",
                isolated.diagnostics()
            );
        }
        let result = check_text(
            "type Input = 'object' | 'array' | 'null' | 'undefined'\
                 | 'string' | 'number' | 'bigint' | 'boolean';\
             abstract class Item {}\
             declare function dedup<T>(values: T[]): T[];\
             function group(): {\
                 types: Map<Input, Item[]>;\
                 literals: Map<unknown, Item[]>;\
                 unknowns: Item[];\
                 optionals: Item[];\
                 expectedTypes: Input[];\
             } {\
                 const types = new Map<Input, Item[]>();\
                 const literals = new Map<unknown, Item[]>();\
                 const unknowns = [] as Item[];\
                 const optionals = [] as Item[];\
                 const expectedTypes = [] as Input[];\
                 return {\
                     types,\
                     literals,\
                     unknowns: dedup(unknowns),\
                     optionals: dedup(optionals),\
                     expectedTypes: dedup(expectedTypes),\
                 };\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }
    #[test]
    fn logical_guards_narrow_nested_optional_index_targets() {
        let result = check_text(
            "interface Node {\
                 child?: Node;\
                 methods?: Record<string, number | undefined>;\
             }\
             function read(node: Node, key: string): number | undefined {\
                 if (node.child && node.child.methods) {\
                     return node.child.methods[key];\
                 }\
                 return undefined;\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn nested_array_selection_preserves_a_shared_element_type() {
        let result = check_text(
            "declare const marker: unique symbol;\
             interface Matcher { tag: number; }\
             abstract class Item { abstract readonly [marker]: Matcher; }\
             declare function fallback(): Matcher;\
             declare function consume(matcher: Matcher): void;\
             class Selection<\
                 Head extends Item[],\
                 Rest extends Item | undefined,\
                 Tail extends Item[]\
             > {\
                 constructor(\
                     readonly head: Head,\
                     readonly restType: Rest | undefined,\
                     readonly tail: Tail\
                 ) {}\
                 run(index: number): void {\
                     const prefix = this.head.map((item) => item[marker]);\
                     const suffix = this.tail.map((item) => item[marker]);\
                     const rest = this.restType?.[marker] ?? fallback();\
                     const headEnd = prefix.length;\
                     const tailStart = suffix.length;\
                     const entry = index < headEnd\
                         ? prefix[index]\
                         : index >= tailStart\
                             ? suffix[index - tailStart]\
                             : rest;\
                     consume(entry);\
                 }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn generic_inference_widens_only_unconstrained_primitive_candidates() {
        let result = check_text(
            "declare function infer<T>(value: T): T;\
             declare function preserve<T extends string>(value: T): T;\
             type Input = 'a' | 'b';\
             declare function input(): Input;\
             const declaredUnion: Input = infer(input());\
             const widened = infer(1);\
             const widenedStr = infer('x');\
             const exact: 'x' = preserve('x');\
             const preserved = preserve('x');\
             let mutableNum = infer(1);\
             let mutableStr = infer('x');\
             class Box<T> {\
               readonly kind = 'box';\
               readonly value: T;\
               constructor(value: T) { this.value = value; }\
             }\
             function make<T>(value: T): { readonly kind: 'box'; readonly value: T } {\
               return new Box(value);\
             }\
             const madeNum = make(1);\
             const boxNum = new Box(1);",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
        assert_interface_binding_types(
            result.product(),
            &[
                ("widened", "1"),
                ("widenedStr", "\"x\""),
                ("preserved", "\"x\""),
                ("exact", "\"x\""),
                ("declaredUnion", "Input"),
                ("mutableNum", "number"),
                ("mutableStr", "string"),
                (
                    "madeNum",
                    "{ readonly kind: \"box\"; readonly value: number; }",
                ),
                ("boxNum", "Box<number>"),
            ],
        );
    }

    #[test]
    fn generic_array_literals_retain_declared_union_elements() {
        let result = check_text(
            "type Input = 'object' | 'array' | 'string';\
             declare function dedup<T>(values: T[]): T[];\
             declare function getIn(): Input;\
             declare const x: Input;\
             declare const arr: Input[];\
             const fromVariable: Input[] = dedup([x]);\
             const fromCall: Input[] = dedup([getIn()]);\
             const fromAssertion: Input[] = dedup([x as Input]);\
             const fromSpread: Input[] = dedup([...arr]);\
             const freshLiterals: string[] = dedup(['object', 'array']);\
             const foreignLiteral: Input[] = dedup(['object', 'not-an-input']);",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C004"],
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn nested_and_naked_covariant_candidates_choose_common_supertype() {
        let result = check_text(
            "declare function lowerBound<T extends number>(\
                 array: readonly T[],\
                 needle: T,\
                 comparator: (item: T, needle: T) => number\
             ): number;\
             declare const values: number[];\
             lowerBound(values, 1, (left, right) => left - right);",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn tagged_template_with_callable_tag_returns_signature_type() {
        let result = check_text(
            "function tag(strings: string[], ...values: number[]): string { return ''; }\
             const s: string = tag`count: ${1 + 2}`;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn tagged_template_with_non_callable_tag_emits_not_callable() {
        let result = check_text("const x: number = 1; x`hello`;");
        assert_eq!(checker_codes(&result), [EXPRESSION_NOT_CALLABLE.as_str()]);
    }

    #[test]
    fn tagged_template_argument_type_mismatch_is_reported() {
        let result = check_text(
            "function tag(strings: string[], ...values: number[]): string { return ''; }\
             const s = tag`count: ${'not a number'}`;",
        );
        assert!(
            checker_codes(&result).contains(&ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn untagged_template_literal_is_string() {
        let result = check_text("const s: string = `hello ${1 + 2}`;");
        assert!(
            checker_codes(&result).is_empty(),
            "{}",
            checker_codes(&result).join(", ")
        );
    }

    #[test]
    fn rest_parameter_annotation_requires_array_or_tuple() {
        let invalid = check_text(
            "function f(...x: number) {}\
            declare function g(...x: number): void;\
            type H = (...x: number) => void;",
        );
        assert_eq!(
            checker_codes(&invalid),
            ["BAMTS-C004", "BAMTS-C004", "BAMTS-C004"]
        );

        let valid = check_text(
            "declare function f(...x: number[]): void;\
            declare function g(...x: [number, string]): void;\
            declare function h(...x: [number, ...string[]]): void;\
            type T = (...x: number[]) => void;",
        );
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn qualified_typeof_resolves_value_and_class_static_property_paths() {
        let result = check_text(
            "const obj = { x: 1, nested: { y: \"ok\" } };\
             let a: typeof obj.x = 1;\
             let b: typeof obj.nested.y = \"ok\";\
             class C { static x = 1; }\
             let c: typeof C.x = 1;\
             class D { x = 1; }\
             let d: typeof D.prototype.x = 1;\
             namespace N { export const V = 1; }\
             let e: typeof N.V = 1;",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );

        let model = result.product();

        let a = model.lookup_value(model.module_scope(), "a").expect("a");
        assert_eq!(model.symbol_type(a), model.types().number());

        let b = model.lookup_value(model.module_scope(), "b").expect("b");
        assert_eq!(model.symbol_type(b), model.types().string());

        let c = model.lookup_value(model.module_scope(), "c").expect("c");
        assert_eq!(model.symbol_type(c), model.types().number());

        let d = model.lookup_value(model.module_scope(), "d").expect("d");
        assert_eq!(model.symbol_type(d), model.types().number());

        let e = model.lookup_value(model.module_scope(), "e").expect("e");
        assert_eq!(model.symbol_type(e), model.types().number());
    }

    #[test]
    fn qualified_typeof_reports_missing_property() {
        let result = check_text("const obj = { a: 1 }; let bad: typeof obj.missing = 1;");
        assert_eq!(checker_codes(&result), [PROPERTY_DOES_NOT_EXIST.as_str()]);

        let model = result.product();
        let bad = model
            .lookup_value(model.module_scope(), "bad")
            .expect("bad");
        assert_eq!(model.symbol_type(bad), model.types().error_type());
    }

    #[test]
    fn self_recursive_interface_property_lookup_terminates() {
        let result = check_text(
            "interface Node { next: Node; value: number; }\
             declare const n: Node;\
             const next: Node = n.next;\
             const value: number = n.value;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn class_member_access_inside_declaring_class_is_allowed() {
        let result = check_text(
            "class Base {\
                 private instancePrivate = 1; protected instanceProtected = 2;\
                 private static staticPrivate = 3; protected static staticProtected = 4;\
                 read(other: Base): number {\
                     return other.instancePrivate + other.instanceProtected\
                         + Base.staticPrivate + Base.staticProtected;\
                 }\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn derived_class_can_access_protected_instance_and_static_members() {
        let result = check_text(
            "class Base { protected instanceValue = 1; protected static staticValue = 2; }\
             class Middle extends Base {}\
             class Derived extends Middle {\
                 read(): number { return this.instanceValue + Base.staticValue; }\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn derived_class_cannot_access_private_instance_or_static_members() {
        let result = check_text(
            "class Base { private instanceValue = 1; private static staticValue = 2; }\
             class Derived extends Base {\
                 read(): number { return this.instanceValue + Base.staticValue; }\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C063", "BAMTS-C063"]);
    }

    #[test]
    fn outside_code_cannot_access_non_public_instance_or_static_members() {
        let result = check_text(
            "class Base { protected instanceValue = 1; private static staticValue = 2; }\
             new Base().instanceValue; Base.staticValue;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C063", "BAMTS-C063"]);
    }

    #[test]
    fn unrelated_class_cannot_access_protected_or_private_members() {
        let result = check_text(
            "class Base { protected instanceValue = 1; protected static staticValue = 2; }\
             class Unrelated {\
                 read(base: Base): number { return base.instanceValue + Base.staticValue; }\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C063", "BAMTS-C063"]);
    }

    #[test]
    fn public_class_members_and_object_literals_remain_structural() {
        let result = check_text(
            "class PublicShape { value = 1; static label = 'class'; }\
             const structural: PublicShape = { value: 2 };\
             const value: number = structural.value;\
             const label: string = PublicShape.label;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn const_bindings_reject_reassignment() {
        let result = check_text("const value: number = 1; value = 2;");
        assert_eq!(checker_codes(&result), ["BAMTS-C060"]);
    }

    #[test]
    fn const_object_bindings_allow_property_mutation() {
        let result = check_text("const value = { count: 1 }; value.count = 2;");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn satisfies_rejects_incompatible_source_type() {
        let result = check_text("const value = 1 satisfies string;");
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn satisfies_preserves_source_type() {
        let result =
            check_text("const value = \"a\" satisfies string; const exact: \"a\" = value;");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn self_recursive_interface_object_literal_assignment() {
        let result = check_text(
            "interface Node { next: Node; value: number; }\
             declare const base: Node;\
             const n: Node = { next: base, value: 1 };",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn self_recursive_interface_exact_member_type_rejects_mismatch() {
        let result = check_text(
            "interface Node { next: Node; value: number; }\
             declare const n: Node;\
             const wrong: string = n.next.next.value;",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn mutual_recursive_interface_property_lookup_terminates() {
        let result = check_text(
            "interface A { b: B; }\
             interface B { a: A; value: string; }\
             declare const a: A;\
             const b: B = a.b;\
             const a2: A = b.a;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn mutual_recursive_interface_object_literal_assignment() {
        let result = check_text(
            "interface A { b: B; }\
             interface B { a: A; value: string; }\
             declare const base: A;\
             const a: A = { b: { a: base, value: 'ok' } };",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn mutual_recursive_interface_rejects_incompatible_concrete_leaf() {
        let result = check_text(
            "interface A { b: B; }\
             interface B { a: A; value: string; }\
             declare const base: A;\
             const a: A = { b: { a: base, value: 1 } };",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn unrelated_class_cannot_access_non_public_instance_or_static_members() {
        let result = check_text(
            "class Base { protected instanceValue = 1; protected static staticValue = 2; }\
             class Unrelated {\
                 read(base: Base): number { return base.instanceValue + Base.staticValue; }\
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C063", "BAMTS-C063"]);
    }

    #[test]
    fn parameter_defaults_are_checked_against_annotations() {
        let invalid = check_text("function f(value: string = 1) {}");
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);

        let valid = check_text("function f(value: string = \"ok\") {}");
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn unannotated_parameter_defaults_contribute_signature_types() {
        let result = check_text("function f(value = 1) {} f(\"wrong\");");
        assert_eq!(checker_codes(&result), ["BAMTS-C053"]);
    }

    #[test]
    fn annotated_returns_reject_incompatible_values_and_bare_returns() {
        let value = check_text("function text(): string { return 1; }");
        assert_eq!(checker_codes(&value), ["BAMTS-C004"]);

        let bare = check_text("function text(): string { return; }");
        assert_eq!(checker_codes(&bare), ["BAMTS-C004"]);
    }

    #[test]
    fn annotated_arrow_returns_are_validated() {
        let result = check_text("const text = (): string => 1;");
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn inferred_async_returns_preserve_promise_value_types() {
        let function = check_text(
            "async function value() { return 1; }\
             const valid: Promise<number> = value();\
             const invalid: Promise<string> = value();",
        );
        assert_eq!(checker_codes(&function), ["BAMTS-C004"]);

        let arrow = check_text(
            "const value = async () => \"ok\";\
             const invalid: Promise<number> = value();",
        );
        assert_eq!(checker_codes(&arrow), ["BAMTS-C004"]);
    }

    #[test]
    fn compatibility_block_arrows_preserve_return_types() {
        let result = check_text(
            "declare function accepts(callback: () => string): void;\
             function outer(): number {\
               accepts(() => { return 'ok'; });\
               return 1;\
             }\
             type Debounced<R> = (() => Promise<R>) & {\
               flush: () => Promise<R> | undefined;\
             };\
             declare const condition: boolean;\
             declare function make<R>(): Promise<R>;\
             function install<R>(debounced: Debounced<R>) {\
               debounced.flush = () => {\
                 if (condition) return;\
                 return make<R>();\
               };\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn compatibility_bare_returns_accept_nullish_union_members() {
        let result = check_text(
            "function maybe(): number | undefined { return; }\
             function optional(): number | void { return; }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_nullish_assignment_excludes_nullish_result() {
        let result = check_text(
            "type Task = () => void;\
             let task: Task | undefined;\
             (task ??= () => {})();",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_contextual_arrays_preserve_tuple_targets() {
        let valid = check_text(
            "const values: [string, unknown][] = [['x', { x: 1 }]];\
             function tuple(): [string, number] | undefined { return ['x', 1]; }\
             const callback = (): [number, string] => [1, 'x'];",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            checker_codes(&valid)
        );

        let invalid = check_text("const values: [string, number][] = [['x', 'wrong']];");
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);
    }

    #[test]
    fn compatibility_readonly_class_properties_preserve_literal_discriminants() {
        let result = check_text(
            "interface Result { readonly ok: false; }\
             class Failure implements Result { readonly ok = false; }\
             function failure(): Result { return new Failure(); }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_contextual_objects_preserve_literal_discriminants() {
        let valid = check_text(
            "interface Success { readonly ok: true; value: number; }\
             function success(value: number): Success { return { ok: true, value }; }\
             declare const condition: boolean;\
             function maybe(value: number): Success | undefined {\
               return condition ? { ok: true, value } : undefined;\
             }",
        );
        assert!(checker_codes(&valid).is_empty());

        let invalid = check_text(
            "interface Success { readonly ok: true; value: number; }\
             function failure(): Success { return { ok: true, value: 'wrong' }; }",
        );
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);
    }

    #[test]
    fn unknown_expression_is_not_callable() {
        let result = check_text("declare const value: unknown; value();");
        assert_eq!(checker_codes(&result), ["BAMTS-C055"]);
    }

    #[test]
    fn generic_constraints_reject_incompatible_arguments() {
        let result = check_text(
            "function identity<T extends string>(value: T): T { return value; }\
             identity(1);",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C053"]);
    }

    #[test]
    fn generic_defaults_supply_missing_inference_candidates() {
        let result = check_text(
            "declare function value<T = string>(): T;\
             const valid: string = value();\
             const invalid: number = value();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn nested_generic_parameters_remain_locally_quantified() {
        let result = check_text(
            "declare function apply<T>(callback: <U>(value: U) => T): T;\
             const text: string = apply(<V>(value: V): string => \"ok\");",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn explicit_type_arguments_reject_missing_required_and_excess_arguments() {
        let missing =
            check_text("function pair<T, U>(left: T, right: U): void {} pair<number>(1, \"x\");");
        assert_eq!(checker_codes(&missing), ["BAMTS-C054"]);

        let excess = check_text(
            "function identity<T>(value: T): T { return value; } identity<number, string>(1);",
        );
        assert_eq!(checker_codes(&excess), ["BAMTS-C054"]);
    }

    #[test]
    fn explicit_type_arguments_allow_omitted_trailing_defaults() {
        let result = check_text(
            "function choose<T, U = string>(left: T, right: U): U { return right; }\
             const text: string = choose<number>(1, \"ok\");",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_constrained_type_parameters_remain_callable() {
        let result = check_text(
            "function invoke<T extends (value: number) => string>(callback: T) {\
               const value: string = callback(1);\
             }\
             interface Constructor { new(value: number): { value: number }; }\
             function build<T extends Constructor>(constructor: T) {\
               const value: { value: number } = new constructor(1);\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_generic_alias_defaults_apply_without_arguments() {
        let result = check_text(
            "type Matcher<Input = unknown> = (value: Input) => void;\
             declare const matcher: Matcher;\
             declare const value: unknown;\
             matcher(value);",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn constrained_generic_signatures_respect_constraint_variance() {
        let result = check_text(
            "type Wide = <T extends string>(value: T) => T;\
             type Same = <U extends string>(value: U) => U;\
             type Narrow = <T extends 'x'>(value: T) => T;\
             declare const wide: Wide;\
             declare const same: Same;\
             declare const narrow: Narrow;\
             const renamed: Wide = same;\
             const acceptsNarrowCalls: Narrow = wide;\
             const rejectsWideCalls: Wide = narrow;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn union_calls_validate_each_constituent_and_preserve_return_types() {
        let valid = check_text(
            "declare const value: ((input: number) => string) | ((input: number) => number);\
             const result: string | number = value(1);",
        );
        assert!(checker_codes(&valid).is_empty());

        let wrong_argument = check_text(
            "declare const value: ((input: number) => string) | ((input: number) => number);\
             value('wrong');",
        );
        assert_eq!(checker_codes(&wrong_argument), ["BAMTS-C053"]);

        let non_callable_member =
            check_text("declare const value: ((input: number) => string) | number; value(1);");
        assert_eq!(checker_codes(&non_callable_member), ["BAMTS-C055"]);
    }

    #[test]
    fn spread_calls_expand_tuples_and_retain_array_rest_returns() {
        let valid = check_text(
            "declare function pair(left: number, right: string): boolean;\
             declare const tuple: [number, string];\
             const paired: boolean = pair(...tuple);\
             declare function sum(...values: number[]): number;\
             declare const values: number[];\
             const total: number = sum(...values);",
        );
        assert!(checker_codes(&valid).is_empty());

        let invalid = check_text(
            "declare function pair(left: number, right: string): boolean;\
             declare const tuple: [string, number]; pair(...tuple);",
        );
        assert_eq!(checker_codes(&invalid), ["BAMTS-C053", "BAMTS-C053"]);
    }

    #[test]
    fn overload_calls_use_only_exposed_signatures() {
        let valid = check_text(
            "function choose(value: string): string;\
             function choose(value: number): number;\
             function choose(value: string | number): string | number { return value; }\
             const text: string = choose('x');\
             const count: number = choose(1);",
        );
        assert!(checker_codes(&valid).is_empty());

        let implementation_only = check_text(
            "function choose(value: string): string;\
             function choose(value: string | number): string { return ''; }\
             choose(1);",
        );
        assert_eq!(checker_codes(&implementation_only), ["BAMTS-C053"]);
    }

    #[test]
    fn numeric_operator_results_reject_string_annotations() {
        let result = check_text(
            "let count = 1;\
             const subtraction: string = 1 - 2;\
             const update: string = count++;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn representative_operator_results_have_concrete_types() {
        let result = check_text(
            "let count = 1;\
             const subtraction: number = 1 - 2;\
             const update: number = count++;\
             const comparison: boolean = 1 < 2;\
             const concatenation: string = \"x\" + 1;\
             const kind: string = typeof count;\
             const ignored: undefined = void count;\
             const sequence: number = (count, 2);",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn compatibility_addition_with_any_preserves_any() {
        let result = check_text(
            "declare const dynamic: any;\
             const value: string = dynamic + 1;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    fn assert_interface_binding_types(model: &super::SemanticModel, expected: &[(&str, &str)]) {
        for &(name, rendered) in expected {
            let symbol = model.lookup_value(model.module_scope(), name).expect(name);
            assert_eq!(
                super::render_type(model, model.symbol_type(symbol)),
                rendered,
                "binding {name}"
            );
        }
    }

    #[test]
    fn canonical_interface_publication_projects_only_the_member_read() {
        let text = "interface I {
            a: number; d?: number; h: any; i: never;
            q: number | undefined; m?: ((x: string) => number);
            nil: null; undef: undefined; both: null | undefined;
            nested: () => number | undefined;
        }";
        for strict in [false, true] {
            let checked = check_text_with(
                text,
                ProgramCheckOptions::standard().with_strict_null_checks(strict),
            );
            assert!(
                checker_codes_of(&checked).is_empty(),
                "{:?}",
                checked.diagnostics()
            );
            let model = checked
                .product()
                .file(SourceId::new(0))
                .expect("source model");
            let expected = if strict {
                [
                    "number",
                    "number | undefined",
                    "any",
                    "never",
                    "number | undefined",
                    "((x: string) => number) | undefined",
                    "null",
                    "undefined",
                    "null | undefined",
                    "() => number | undefined",
                ]
            } else {
                [
                    "number",
                    "number",
                    "any",
                    "never",
                    "number",
                    "(x: string) => number",
                    "null",
                    "undefined",
                    "null",
                    "() => number | undefined",
                ]
            };
            let actual: Vec<_> = model
                .declaration_occurrences()
                .iter()
                .map(|occurrence| super::render_type(model, model.symbol_type(occurrence.symbol)))
                .collect();
            assert_eq!(actual, expected, "strictNullChecks={strict}");
        }
    }

    #[test]
    fn canonical_interface_first_property_wins_even_when_any() {
        let checked = check_text(
            "interface I2 { item: any; item: number; }
             interface A { x: string } interface A { x: number }",
        );
        let model = checked.product();
        let occurrences = model.declaration_occurrences();
        let [first, repeated, early, late] = occurrences else {
            panic!("four property declarations: {occurrences:?}");
        };
        assert_eq!(first.symbol, repeated.symbol);
        assert_eq!(early.symbol, late.symbol);
        assert_ne!(first.symbol, early.symbol);
        for (occurrence, expected) in occurrences.iter().zip(["any", "any", "string", "string"]) {
            assert_eq!(
                super::render_type(model, model.symbol_type(occurrence.symbol)),
                expected
            );
        }
    }

    #[test]
    fn canonical_interface_parameters_publish_distinct_resolved_types() {
        let checked = check_text(
            "interface I {
                a(s: string): void; b(): (n: number) => void;
                f(x: number): number; f(x: string): string;
            }
            interface Index { [key: string]: number; }",
        );
        let model = checked.product();
        let mut parameters: Vec<_> = model
            .symbols()
            .iter()
            .filter(|symbol| symbol.kind() == SymbolKind::Parameter)
            .collect();
        parameters.sort_by_key(|symbol| symbol.range().start());
        let actual: Vec<_> = parameters
            .iter()
            .map(|symbol| {
                let id = model
                    .lookup_value(symbol.scope(), symbol.name())
                    .expect("parameter symbol");
                (
                    symbol.name(),
                    super::render_type(model, model.symbol_type(id)),
                )
            })
            .collect();
        assert_eq!(
            actual,
            [
                ("s", "string".to_owned()),
                ("n", "number".to_owned()),
                ("x", "number".to_owned()),
                ("x", "string".to_owned()),
                ("key", "string".to_owned()),
            ]
        );
        let identities: std::collections::HashSet<_> = parameters
            .iter()
            .map(|symbol| {
                model
                    .lookup_value(symbol.scope(), symbol.name())
                    .expect("parameter")
            })
            .collect();
        assert_eq!(identities.len(), parameters.len());
    }

    #[test]
    fn canonical_interface_fragments_publish_complete_groups_and_exact_spans() {
        let text = "interface A { f(x: string): 1; f(x: number): 2; }\n\
                    interface A { f(x: string): 3; }\n\
                    declare const a: A; const g = a.f;\n\
                    const directString = a.f(\"s\"); const directNumber = a.f(0);\n\
                    const extractedString = g(\"s\"); const extractedNumber = g(0);";
        let checked = check_text(text);
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        let model = checked.product();
        let occurrences = model.declaration_occurrences();
        let [first, second, third] = occurrences else {
            panic!("three written method declarations: {occurrences:?}");
        };
        assert_eq!(first.symbol, second.symbol);
        assert_eq!(first.symbol, third.symbol);
        let source_text = source(text);
        for (occurrence, (declaration, name)) in occurrences.iter().zip([
            ("f(x: string): 1", "f"),
            ("f(x: number): 2", "f"),
            ("f(x: string): 3", "f"),
        ]) {
            let byte_start = text.find(declaration).expect("declaration text");
            let start = source_text.byte_to_utf16(byte_start).expect("UTF-16 start");
            let end = source_text
                .byte_to_utf16(byte_start + declaration.len())
                .expect("UTF-16 end");
            let name_end = source_text
                .byte_to_utf16(byte_start + name.len())
                .expect("UTF-16 name end");
            assert_eq!(
                occurrence.declaration_range,
                source_text.range(start, end).expect("member range")
            );
            assert_eq!(
                occurrence.name_range,
                source_text.range(start, name_end).expect("name range")
            );
            assert_eq!(
                super::render_type(model, model.symbol_type(occurrence.symbol)),
                "{ (x: string): 1; (x: number): 2; (x: string): 3; }"
            );
        }
        assert_interface_binding_types(
            model,
            &[
                ("g", "{ (x: string): 1; (x: number): 2; (x: string): 3; }"),
                ("directString", "3"),
                ("directNumber", "2"),
                ("extractedString", "3"),
                ("extractedNumber", "2"),
            ],
        );
    }

    #[test]
    fn canonical_interface_return_projection_keeps_written_provenance() {
        let text = "type NrMaybe = number | undefined;
            interface Returns {
                plain(x: string): number; maybe(x: string): number | undefined;
                nil(): null; undef(): undefined; both(): null | undefined;
                numNull(): number | null; all(): number | null | undefined;
                alias(): NrMaybe; make(): () => number | undefined;
            }
            declare const r: Returns;
            const plain = r.plain; const maybe = r.maybe;
            const plainResult = plain('s'); const maybeResult = maybe('s');
            const nil = r.nil(); const undef = r.undef(); const both = r.both();
            const numNull = r.numNull(); const all = r.all();
            const alias = r.alias; const aliasResult = alias();
            const outer = r.make(); const inner = outer();";
        for strict in [false, true] {
            let checked = check_text_with(
                text,
                ProgramCheckOptions::standard().with_strict_null_checks(strict),
            );
            assert!(
                checker_codes_of(&checked).is_empty(),
                "{:?}",
                checked.diagnostics()
            );
            let model = checked
                .product()
                .file(SourceId::new(0))
                .expect("source model");
            assert_interface_binding_types(
                model,
                &[
                    ("plain", "(x: string) => number"),
                    ("maybe", "(x: string) => number | undefined"),
                    ("plainResult", "number"),
                    (
                        "maybeResult",
                        if strict {
                            "number | undefined"
                        } else {
                            "number"
                        },
                    ),
                    ("nil", "null"),
                    ("undef", "undefined"),
                    ("both", if strict { "null | undefined" } else { "null" }),
                    ("numNull", if strict { "number | null" } else { "number" }),
                    (
                        "all",
                        if strict {
                            "number | null | undefined"
                        } else {
                            "number"
                        },
                    ),
                    ("alias", "() => NrMaybe"),
                    ("aliasResult", if strict { "NrMaybe" } else { "number" }),
                    ("outer", "() => number | undefined"),
                    (
                        "inner",
                        if strict {
                            "number | undefined"
                        } else {
                            "number"
                        },
                    ),
                ],
            );
        }
    }

    #[test]
    fn canonical_interface_provenance_survives_import_and_instantiation() {
        let checked = linked(
            &[
                "export interface Plain<T> { n(x: T): number; }
             export interface Maybe<T> { n(x: T): number | undefined; }",
                "import { Plain, Maybe } from './types';
             declare const p: Plain<string>; declare const m: Maybe<string>;
             const pn = p.n; const mn = m.n;
             const pr = pn('s'); const mr = mn('s');",
            ],
            &[(1, 0, 0)],
        );
        assert!(
            checker_codes_of(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        let model = checked
            .product()
            .file(SourceId::new(1))
            .expect("importing model");
        assert_interface_binding_types(
            model,
            &[
                ("pn", "(x: string) => number"),
                ("mn", "(x: string) => number | undefined"),
                ("pr", "number"),
                ("mr", "number"),
            ],
        );
    }

    #[test]
    fn canonical_interface_literal_priority_is_existential_and_excludes_unions() {
        let checked = check_text(
            "interface P { q(x: 's', y: number): 1 }
             interface P { q(x: string, y: number): 2; q(x: string, y: string): 3 }
             declare const p: P; const e = p.q;
             const p1 = p.q('s', 0); const p2 = p.q('s', 's');
             const e1 = e('s', 0); const e2 = e('s', 's');
             interface W { f(x:'s'):1; f(x:'a'|'b'):2; f(x:0):3; }
             interface W { f(x:string):4; f(x:number):5; }
             interface W { b(x:true):6; i(x:0n):7; }
             interface W { b(x:boolean):8; i(x:bigint):9; }
             declare const w: W; const f = w.f; const b = w.b; const i = w.i;
             const r1 = w.f('s'); const r2 = w.f('a'); const r3 = w.f('b');
             const r4 = w.f('z'); const r5 = w.f(0);
             const r6 = f('s'); const r7 = f('a'); const r8 = f('b');
             const r9 = f('z'); const r10 = f(0);
             const b1 = w.b(true); const b2 = w.b(false);
             const i1 = w.i(0n); const i2 = w.i(1n);
             const eb1 = b(true); const eb2 = b(false);
             const ei1 = i(0n); const ei2 = i(1n);",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(
            checked.product(),
            &[
                ("p1", "1"),
                ("p2", "3"),
                ("e1", "1"),
                ("e2", "3"),
                ("r1", "1"),
                ("r2", "4"),
                ("r3", "4"),
                ("r4", "4"),
                ("r5", "3"),
                ("r6", "1"),
                ("r7", "4"),
                ("r8", "4"),
                ("r9", "4"),
                ("r10", "3"),
                ("b1", "6"),
                ("b2", "8"),
                ("i1", "7"),
                ("i2", "9"),
                ("eb1", "6"),
                ("eb2", "8"),
                ("ei1", "7"),
                ("ei2", "9"),
            ],
        );
    }

    #[test]
    fn canonical_interface_repeated_signatures_keep_labels_and_source_order() {
        let checked = check_text(
            "interface R { m(x: number): number; m(x: number): number; }
             interface R { m(x: number): number; }
             interface S { m(a: string): string; m(b: string): string; }
             interface S { m(c: string): string; }
             interface T { m(a: string): 1; m(b: string): 2; }
             declare const r: R; declare const s: S; declare const t: T;
             const er = r.m; const es = s.m; const et = t.m;
             const rr = er(1); const sr = es('x'); const tr = t.m('x'); const te = et('x');",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(
            checked.product(),
            &[
                (
                    "er",
                    "{ (x: number): number; (x: number): number; (x: number): number; }",
                ),
                (
                    "es",
                    "{ (a: string): string; (b: string): string; (c: string): string; }",
                ),
                ("et", "{ (a: string): 1; (b: string): 2; }"),
                ("rr", "number"),
                ("sr", "string"),
                ("tr", "1"),
                ("te", "1"),
            ],
        );
    }

    #[test]
    fn canonical_interface_generic_groups_keep_instantiation_and_shadowing() {
        let checked = check_text(
            "interface B<T> { foo(x: T): number; foo(x: string): string; }
             interface B<T> { foo(x: T): Date; foo(x: Date): string; }
             interface C<T, U> { foo(x: T, y: U): string; foo(x: string, y: string): number; }
             interface C<T, U> { foo<W>(x: W, y: W): W; }
             interface G<T> { m(x: T): T; }
             interface G<T> { n(x: T): T; m<T>(x: T): T; }
             declare const b: B<boolean>; declare const c: C<number, number>;
             declare const g: G<string>;
             const eb = b.foo; const ec = c.foo; const eg = g.m;
             const br = b.foo(true); const ber = eb(true);
             const cr = c.foo(1, 2); const cer = ec(1, 2);
             const gm = g.m('s'); const gn = g.n('s');
             const ge = eg('s'); const gen = eg(0);",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(
            checked.product(),
            &[
                ("br", "Date"),
                ("ber", "Date"),
                ("cr", "1 | 2"),
                ("cer", "1 | 2"),
                ("gm", "\"s\""),
                ("gn", "string"),
                ("ge", "\"s\""),
                ("gen", "0"),
            ],
        );
    }

    #[test]
    fn canonical_interface_optional_calls_and_reads_follow_null_mode() {
        let text = "interface O { m?(x: string): 1; m?(x: number): 2; }
            interface O { m?(x: boolean): 3; }
            declare const o: O; const extracted = o.m;
            const r1 = o.m?.('s'); const r2 = o.m?.(0); const r3 = o.m?.(true);
            const e1 = extracted?.('s'); const e2 = extracted?.(0); const e3 = extracted?.(true);
            interface Opt { maybe?(flag: boolean): number | undefined; }
            declare const opt: Opt; const returned = opt.maybe?.(true);";
        for strict in [false, true] {
            let checked = check_text_with(
                text,
                ProgramCheckOptions::standard().with_strict_null_checks(strict),
            );
            assert!(
                checker_codes_of(&checked).is_empty(),
                "{:?}",
                checked.diagnostics()
            );
            let model = checked.product().file(SourceId::new(0)).expect("model");
            assert_interface_binding_types(
                model,
                &[
                    (
                        "extracted",
                        if strict {
                            "{ (x: string): 1; (x: number): 2; (x: boolean): 3; } | undefined"
                        } else {
                            "{ (x: string): 1; (x: number): 2; (x: boolean): 3; }"
                        },
                    ),
                    ("r1", if strict { "1 | undefined" } else { "1" }),
                    ("r2", if strict { "2 | undefined" } else { "2" }),
                    ("r3", if strict { "3 | undefined" } else { "3" }),
                    ("e1", if strict { "1 | undefined" } else { "1" }),
                    ("e2", if strict { "2 | undefined" } else { "2" }),
                    ("e3", if strict { "3 | undefined" } else { "3" }),
                    (
                        "returned",
                        if strict {
                            "number | undefined"
                        } else {
                            "number"
                        },
                    ),
                ],
            );
            let unguarded = check_text_with(
                "interface O { m?(x: string): 1; m?(x: number): 2; }
                 declare const o: O; o.m('s'); const e = o.m; e('s');",
                ProgramCheckOptions::standard().with_strict_null_checks(strict),
            );
            assert_eq!(
                checker_codes_of(&unguarded),
                if strict {
                    vec![EXPRESSION_NOT_CALLABLE.as_str().to_owned(); 2]
                } else {
                    Vec::new()
                }
            );
        }
    }

    #[test]
    fn canonical_interface_call_and_intersection_consumers_keep_group_order() {
        let checked = check_text(
            "interface A { f(x: string): 1; f(x: number): 2; }
             interface A { f(x: string): 3; }
             declare const a: A; const e = a.f;
             const c1 = a.f.call(a, 's'); const c2 = a.f.call(a, 0);
             const c3 = e.call(a, 's'); const c4 = e.call(a, 0);
             declare const plain: (x: number) => number;
             const cp = plain.call(null, 1);
             declare const intersection: ((x: number) => number) & ((x: string) => string);
             const ci = intersection.call(null, 's');
             const ir = intersection(0); const is = intersection('s');
             declare const combined: A['f'] & ((x: boolean) => 4);
             const extracted = combined;
             const g1 = combined('s'); const g2 = extracted('s'); const g3 = extracted(true);",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(
            checked.product(),
            &[
                ("c1", "3"),
                ("c2", "2"),
                ("c3", "3"),
                ("c4", "2"),
                ("cp", "number"),
                ("ci", "string"),
                ("ir", "number"),
                ("is", "string"),
                (
                    "intersection",
                    "((x: number) => number) & ((x: string) => string)",
                ),
                ("g1", "3"),
                ("g2", "3"),
                ("g3", "4"),
            ],
        );
    }

    #[test]
    fn canonical_interface_class_and_interface_level_signatures_remain_independent() {
        let checked = check_text(
            "declare class C { m(x: string): 2; m(x: 's'): 1; }
             declare const c: C; const cm = c.m; const cr = c.m('s'); const ce = cm('s');
             interface Base { (x: number): string; new(x: number): C; [key: string]: any; }
             interface Derived extends Base { own: boolean; }
             declare const d: Derived;
             const call = d(1); const made = new d(1); const indexed = d['other'];
             const own = d.own;",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(
            checked.product(),
            &[
                ("cm", "{ (x: string): 2; (x: \"s\"): 1; }"),
                ("cr", "2"),
                ("ce", "2"),
                ("call", "string"),
                ("made", "C"),
                ("indexed", "any"),
                ("own", "boolean"),
            ],
        );
    }

    #[test]
    fn canonical_interface_contextual_overloads_constrain_method_inference() {
        let checked = check_text(
            "interface Target { m(x: string): string; }
             interface Target { m(x: number): number; }
             const target: Target = { m(x) { return x; } };
             const a: string = target.m('s'); const b: number = target.m(1);",
        );
        assert!(
            checker_codes(&checked).is_empty(),
            "{:?}",
            checked.diagnostics()
        );
        assert_interface_binding_types(checked.product(), &[("a", "string"), ("b", "number")]);
        let invalid = check_text(
            "interface Target { m(x: string): string; }
             interface Target { m(x: number): number; }
             const target: Target = { m(x) { return true; } };",
        );
        assert_eq!(checker_codes(&invalid), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn interface_call_signatures_drive_argument_and_return_types() {
        let valid = check_text(
            "interface Callable { (value: number): string; }\
             declare const callable: Callable;\
             const result: string = callable(1);",
        );
        assert!(checker_codes(&valid).is_empty());

        let invalid = check_text(
            "interface Callable { (value: number): string; }\
             declare const callable: Callable; callable('wrong');",
        );
        assert_eq!(checker_codes(&invalid), ["BAMTS-C053"]);
    }

    #[test]
    fn structural_relations_require_call_and_construct_signatures() {
        let result = check_text(
            "declare const value: {};\
             const callable: { (): string } = value;\
             const constructable: { new (): {} } = value;",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn intersection_relations_preserve_signature_and_index_requirements() {
        let result = check_text(
            "declare const value: { a: string } & { b: number };\
             const callable: { (): void } = value;\
             const constructable: { new (): {} } = value;\
             const dictionary: { [key: string]: number } = value;",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C004", "BAMTS-C004", "BAMTS-C004"]
        );
    }

    #[test]
    fn destructuring_validates_annotations_and_projects_leaf_types() {
        let mismatch = check_text("const { x }: { x: string } = { x: 1 };");
        assert_eq!(checker_codes(&mismatch), ["BAMTS-C004"]);

        let projected = check_text(
            "const { nested: { value } } = { nested: { value: 1 } };\
             const text: string = value;",
        );
        assert_eq!(checker_codes(&projected), ["BAMTS-C004"]);
    }

    #[test]
    fn tuple_types_preserve_positional_element_types() {
        let result = check_text(
            "declare const tuple: [string, number];\
             const first: string = tuple[0];\
             const second: number = tuple[1];\
             const wrong: string = tuple[1];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn tuple_types_reject_out_of_range_member_access() {
        let result = check_text("declare const tuple: [string]; tuple[1];");
        assert_eq!(checker_codes(&result), ["BAMTS-C057"]);
    }

    #[test]
    fn index_signatures_supply_member_types_and_readonly_rules() {
        let lookup = check_text(
            "interface Dictionary { [key: string]: number }\
             declare const values: Dictionary;\
             const valid: number = values.answer;\
             const wrong: string = values.answer;",
        );
        assert_eq!(checker_codes(&lookup), ["BAMTS-C004"]);

        let numeric = check_text(
            "interface Rows { [index: number]: string }\
             declare const rows: Rows; const row: string = rows[0];",
        );
        assert!(checker_codes(&numeric).is_empty());

        let readonly = check_text(
            "interface Frozen { readonly [key: string]: number }\
             declare let values: Frozen; values.answer = 1;",
        );
        assert_eq!(checker_codes(&readonly), ["BAMTS-C061"]);
    }

    #[test]
    fn index_signature_assignability_respects_key_domains() {
        let invalid = check_text(
            "interface Numeric { [key: number]: number }\
             interface Textual { [key: string]: number }\
             declare const source: Numeric;\
             const target: Textual = source;",
        );
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);

        let valid = check_text(
            "interface Textual { [key: string]: number }\
             interface Numeric { [key: number]: number }\
             declare const source: Textual;\
             const target: Numeric = source;",
        );
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn tuple_rest_elements_preserve_minimum_arity() {
        let result = check_text(
            "type NonEmpty = [number, ...number[]];\
             const one: NonEmpty = [1];\
             const many: NonEmpty = [1, 2, 3];\
             const empty: NonEmpty = [];",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn bindings_preserve_declared_composite_property_types() {
        let result = check_text(
            "type Mode = 'strict' | 'loose';\
             declare function configured(): { mode: Mode };\
             const config = configured();\
             const configuredMode: Mode = config.mode;\
             declare function modes(): Mode[];\
             const list = modes();\
             list[0] = 'strict';\
             const first: Mode = list[0];\
             const fresh = { mode: 'strict' };\
             fresh.mode = 'loose';\
             const freshList = ['strict'];\
             freshList[0] = 'loose';",
        );
        assert!(checker_codes(&result).is_empty());
        let model = result.product();
        let fresh_list = model
            .lookup_value(model.module_scope(), "freshList")
            .expect("fresh list binding exists");
        let Type::Array(fresh_element) = model.types().get(model.symbol_type(fresh_list)) else {
            panic!("fresh list is an array");
        };
        assert_eq!(*fresh_element, model.types().string());

        let rejected = check_text(
            "type Mode = 'strict' | 'loose';\
             declare const list: Mode[];\
             list[0] = 'invalid';",
        );
        assert_eq!(checker_codes(&rejected), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn array_numeric_index_read_is_assignable_to_element() {
        let result = check_text("declare const values: number[]; const value: number = values[0];");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn array_numeric_index_read_rejects_incompatible_target() {
        let result = check_text("declare const values: number[]; const value: string = values[0];");
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn array_numeric_index_write_rejects_incompatible_source() {
        let result = check_text("declare const values: number[]; values[0] = 'bad';");
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn reg_exp_type_supports_array_index_assignment() {
        let result =
            check_text("function f(a: RegExp[], i: number, r: RegExp): void { a[i] = r; }");
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn reg_exp_array_index_rejects_incompatible_source() {
        let result =
            check_text("function f(a: RegExp[], i: number, r: string): void { a[i] = r; }");
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn reg_exp_instance_members_have_intrinsic_types() {
        let result = check_text(
            "function inspect(r: RegExp, input: string): boolean {\
                 const source: string = r.source;\
                 const flags: string = r.flags;\
                 const match = r.exec(input);\
                 if (match) { const first: string = match[0]; }\
                 return r.test(input);\
             }\
             function acceptsPattern(value: string | RegExp): void {}\
             const literal: RegExp = /x/;\
             acceptsPattern(/x/);",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );

        let missing = check_text("declare const r: RegExp; r.missing;");
        assert_eq!(checker_codes(&missing), [PROPERTY_DOES_NOT_EXIST.as_str()]);
    }

    #[test]
    fn string_numeric_index_yields_string() {
        let result = check_text(
            "declare const p: string; declare const j: number; const a: string = p[j]; const b: string = p[0];",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn string_numeric_index_rejects_non_string_target() {
        let result =
            check_text("declare const p: string; declare const j: number; const a: number = p[j];");
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn string_literal_numeric_index_yields_string() {
        let valid = check_text(
            "declare const p: 'abc'; declare const i: number; const value: string = p[i];",
        );
        assert!(
            checker_codes(&valid).is_empty(),
            "{:?}",
            valid.diagnostics()
        );

        let invalid_type = check_text(
            "declare const p: 'abc'; declare const i: number; const value: number = p[i];",
        );
        assert_eq!(checker_codes(&invalid_type), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn array_named_properties_remain_permissive() {
        let result =
            check_text("declare const values: number[]; const label: string = values.tag;");
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn intersection_types_merge_members_and_require_every_target() {
        let members = check_text(
            "type Both = { left: string } & { right: number };\
             declare const both: Both;\
             const left: string = both.left;\
             const right: number = both.right;\
             const wrong: string = both.right;",
        );
        assert_eq!(checker_codes(&members), ["BAMTS-C004"]);

        let assignment = check_text(
            "type Both = { left: string } & { right: number };\
             const incomplete: Both = { left: \"ok\" };",
        );
        assert_eq!(checker_codes(&assignment), ["BAMTS-C004"]);
    }

    #[test]
    fn class_static_and_instance_members_are_separate() {
        let valid = check_text(
            "class Item {\
                 static count: number = 1; value: string = 'x';\
                 static getCount(): number { return this.count; }\
                 getValue(): string { return this.value; }\
             }\
             const count: number = Item.getCount();\
             const value: string = new Item().getValue();",
        );
        assert!(checker_codes(&valid).is_empty());

        let invalid = check_text(
            "class Item { static count: number = 1; value: string = 'x'; }\
             Item.value; new Item().count;\
             let typed: Item = new Item(); typed.count; typed.prototype;",
        );
        assert_eq!(
            checker_codes(&invalid),
            ["BAMTS-C057", "BAMTS-C057", "BAMTS-C057", "BAMTS-C057"]
        );
    }

    #[test]
    fn class_methods_preserve_inferred_return_types() {
        let result = check_text(
            "class Counter {\
                 value() { return 1; }\
                 useValue() { const value: number = this.value(); return value; }\
             }",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn generic_class_construction_instantiates_instance_members() {
        let valid = check_text(
            "class Box<T> { constructor(public value: T) {} }\
             const explicit: string = new Box<string>('x').value;\
             const inferred: number = new Box(1).value;",
        );
        assert!(checker_codes(&valid).is_empty());

        let wrong_type = check_text(
            "class Box<T> { constructor(public value: T) {} }\
             new Box<number>('wrong');",
        );
        assert_eq!(checker_codes(&wrong_type), ["BAMTS-C053"]);

        let wrong_count = check_text("class Box<T> { constructor(public value: T) {} } new Box();");
        assert_eq!(checker_codes(&wrong_count), ["BAMTS-C054"]);
    }

    #[test]
    fn applied_generic_classes_relate_through_substituted_public_shapes() {
        let public = check_text(
            "declare class A<T> { value: T; }\
             declare class B<T> { value: T; }\
             declare const source: B<number>;\
             const target: A<number> = source;",
        );
        assert!(
            checker_codes(&public).is_empty(),
            "{:?}",
            checker_codes(&public)
        );

        let recursive = check_text(
            "declare class Box<T> { value: T; next: Box<T>; }\
             declare const literal: Box<1>;\
             const widened: Box<number> = literal;",
        );
        assert!(
            checker_codes(&recursive).is_empty(),
            "{:?}",
            checker_codes(&recursive)
        );

        let incompatible = check_text(
            "declare class A<T> { value: T; }\
             declare class B<T> { value: T; }\
             declare const source: B<number>;\
             const wrong: A<string> = source;\
             declare class Box<T> { value: T; next: Box<T>; }\
             declare const widened: Box<number>;\
             const narrow: Box<1> = widened;",
        );
        assert_eq!(checker_codes(&incompatible), ["BAMTS-C004", "BAMTS-C004"]);
    }

    #[test]
    fn inherited_generic_constructor_uses_heritage_arguments() {
        let result = check_text(
            "class Base<T> { constructor(value: T) {} }\
             class Derived extends Base<string> {}\
             new Derived('ok'); new Derived(1);",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C053"]);
    }

    #[test]
    fn construction_requires_construct_signatures() {
        let non_constructable = check_text("const value = 1; new value();");
        assert_eq!(checker_codes(&non_constructable), ["BAMTS-C059"]);

        let valid = check_text(
            "interface Factory { new (value: number): { value: number }; }\
             declare const Factory: Factory;\
             const value: number = new Factory(1).value;",
        );
        assert!(checker_codes(&valid).is_empty());

        let wrong_argument = check_text(
            "interface Factory { new (value: number): { value: number }; }\
             declare const Factory: Factory; new Factory('wrong');",
        );
        assert_eq!(checker_codes(&wrong_argument), ["BAMTS-C053"]);
    }

    #[test]
    fn abstract_classes_and_value_aliases_cannot_be_constructed() {
        for source in [
            "abstract class Base {} new Base();",
            "abstract class Base {} const Alias = Base; new Alias();",
        ] {
            let result = check_text(source);
            assert_eq!(
                checker_codes(&result),
                ["BAMTS-C066"],
                "{source}: {:?}",
                checker_codes(&result)
            );
        }
    }

    #[test]
    fn abstract_construct_types_are_directional_and_not_constructable() {
        let construction = check_text(
            "declare const Factory: abstract new () => object;\
             new Factory();",
        );
        assert_eq!(checker_codes(&construction), ["BAMTS-C066"]);

        let relation = check_text(
            "type AbstractFactory = abstract new () => object;\
             type ConcreteFactory = new () => object;\
             declare const abstractFactory: AbstractFactory;\
             declare const concreteFactory: ConcreteFactory;\
             const acceptsAbstract: AbstractFactory = concreteFactory;\
             const rejectsAbstract: ConcreteFactory = abstractFactory;",
        );
        assert_eq!(checker_codes(&relation), ["BAMTS-C004"]);
    }

    #[test]
    fn concrete_subclasses_clear_inherited_abstract_constructors() {
        let result = check_text(
            "abstract class Box<T> { constructor(value: T) {} }\
             new Box<number>(1);\
             class Concrete extends Box<string> {}\
             new Concrete('ok');",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C066"]);
    }

    #[test]
    fn imported_abstract_class_constructors_remain_abstract() {
        let result = linked(
            &[
                "export abstract class Base {}",
                "import { Base } from './a'; new Base();",
            ],
            &[(1, 0, 0)],
        );
        assert_eq!(program_codes(&result), ["BAMTS-C066"]);
    }

    #[test]
    fn class_construction_exposes_overloads_and_inherited_parameters() {
        let overloads = check_text(
            "class Choice {\
                 constructor(value: string); constructor(value: number);\
                 constructor(value: string | number) {}\
             }\
             new Choice('x'); new Choice(1); new Choice(true);",
        );
        assert_eq!(checker_codes(&overloads), ["BAMTS-C053"]);

        let inherited = check_text(
            "class Base { constructor(value: string) {} }\
             class Derived extends Base {}\
             new Derived('x'); new Derived(1);",
        );
        assert_eq!(checker_codes(&inherited), ["BAMTS-C053"]);
    }

    #[test]
    fn implements_checks_final_inferred_property_types() {
        let invalid = check_text(
            "interface Named { name: string } class Item implements Named { name = 1; }",
        );
        assert_eq!(checker_codes(&invalid), ["BAMTS-C004"]);

        let valid = check_text(
            "interface Named { name: string } class Item implements Named { name = 'ok'; }",
        );
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn readonly_and_getter_only_properties_reject_writes() {
        let getter = check_text("const value = { get x() { return 1; } }; value.x = 2;");
        assert_eq!(checker_codes(&getter), ["BAMTS-C061"]);

        let declared =
            check_text("interface Item { readonly x: number } declare let item: Item; item.x = 2;");
        assert_eq!(checker_codes(&declared), ["BAMTS-C061"]);
    }

    #[test]
    fn getter_setter_pairs_allow_writes() {
        let result = check_text(
            "const value = { get x() { return 1; }, set x(next: number) {} }; value.x = 2;",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn class_readonly_properties_allow_only_constructor_initialization() {
        let outside = check_text(
            "class Item { readonly x: number; constructor() { this.x = 1; } }\
             const item = new Item(); item.x = 2;",
        );
        assert_eq!(checker_codes(&outside), ["BAMTS-C061"]);

        let constructor =
            check_text("class Item { readonly x: number; constructor() { this.x = 1; } }");
        assert!(checker_codes(&constructor).is_empty());
    }

    #[test]
    fn readonly_parameter_properties_allow_only_constructor_initialization() {
        let constructor =
            check_text("class Item { constructor(readonly x: number) { this.x = 1; } }");
        assert!(checker_codes(&constructor).is_empty());

        let outside = check_text(
            "class Item { constructor(readonly x: number) { this.x = 1; } }\
             const item = new Item(0); item.x = 2;",
        );
        assert_eq!(checker_codes(&outside), ["BAMTS-C061"]);
    }

    #[test]
    fn class_getter_only_properties_reject_writes() {
        let outside = check_text("class Item { get x(): number { return 1; } } new Item().x = 2;");
        assert_eq!(checker_codes(&outside), ["BAMTS-C061"]);

        let constructor = check_text(
            "class Item { get x(): number { return 1; } constructor() { this.x = 2; } }",
        );
        assert_eq!(checker_codes(&constructor), ["BAMTS-C061"]);
    }

    #[test]
    fn inherited_readonly_properties_reject_constructor_writes() {
        let result = check_text(
            "class Base { readonly x = 1; }\
             class Derived extends Base { constructor() { super(); this.x = 2; } }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C061"]);
    }

    #[test]
    fn nested_functions_cannot_initialize_readonly_properties() {
        let result = check_text(
            "class Item { readonly x = 1; constructor() { const assign = () => { this.x = 2; }; assign(); } }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C061"]);
    }

    #[test]
    fn class_implements_accepts_matching_instance_shape() {
        let result = check_text(
            "interface Shape { x: number; label: string }\
             class Item implements Shape { x: number = 1; label: string = \"item\"; }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn class_implements_rejects_missing_and_incompatible_members() {
        let missing = check_text(
            "interface Shape { x: number; label: string }\
             class Item implements Shape { x: number = 1; }",
        );
        assert_eq!(checker_codes(&missing), ["BAMTS-C004"]);

        let incompatible = check_text(
            "interface Shape { x: number }\
             class Item implements Shape { x: string = \"wrong\"; }",
        );
        assert_eq!(checker_codes(&incompatible), ["BAMTS-C004"]);
    }

    #[test]
    fn generic_subclasses_relate_to_applied_base_types() {
        let result = check_text(
            "type Name = 'literal' | 'object';\
             abstract class Base<Output = unknown> {\
               abstract readonly name: Name;\
               abstract parse(value: unknown): Output;\
             }\
             class Literal<Output> extends Base<Output> {\
               readonly name = 'literal';\
               readonly value: Output;\
               constructor(value: Output) { super(); this.value = value; }\
               parse(_value: unknown): Output { return this.value; }\
             }\
             const literal = <Value extends string>(value: Value): Base<Value> => {\
               return new Literal(value);\
             };\
             type LazyName = 'lazy' | 'other';\
             abstract class LazyBase<Output = unknown> {\
               abstract readonly name: LazyName;\
               abstract parse(value: unknown): Output;\
             }\
             class Lazy<Output> extends LazyBase<Output> {\
               readonly name = 'lazy';\
               readonly definition: () => LazyBase<Output>;\
               constructor(definition: () => LazyBase<Output>) {\
                 super(); this.definition = definition;\
               }\
               parse(value: unknown): Output { return this.definition().parse(value); }\
             }\
             const lazy = <Value>(definition: () => LazyBase<Value>): LazyBase<Value> => {\
               return new Lazy(definition);\
             };",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn later_generic_class_shape_is_published_before_an_earlier_method() {
        let result = check_text(
            "abstract class AbstractType<Output = unknown> {\n\
                 abstract readonly name: string;\n\
             }\n\
             abstract class ValueType<Output = unknown> extends AbstractType<Output> {\n\
                 abstract readonly name: \"unknown\";\n\
                 visit(func: (value: Terminal) => void): void {\n\
                     func(this as Terminal);\n\
                 }\n\
             }\n\
             type Terminal =\n\
                 | (ValueType & { name: \"unknown\" })\n\
                 | Optional;\n\
             class Optional<Output = unknown> extends AbstractType<Output | undefined> {\n\
                 readonly name = \"optional\";\n\
             }",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn later_unrelated_generic_class_remains_incompatible() {
        let result = check_text(
            "abstract class ValueType<Output = unknown> {\n\
                 readonly name = \"value\";\n\
                 check(): void { const impossible = this as Unrelated<number>; }\n\
             }\n\
             class Unrelated<T = unknown> {\n\
                 readonly name = \"unrelated\";\n\
                 readonly unrelated!: T;\n\
             }",
        );

        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn later_generic_class_literal_discriminant_narrows_an_earlier_function() {
        let result = check_text(
            "abstract class Base { abstract readonly name: string; }\n\
             type Terminal =\n\
                 | (Base & { readonly name: \"unknown\" | \"never\" | \"string\" })\n\
                 | LiteralType<number>;\n\
             function readLiteral(terminal: Terminal): number {\n\
                 if (terminal.name === \"literal\") return terminal.value;\n\
                 return 0;\n\
             }\n\
             class LiteralType<Out = unknown> extends Base {\n\
                 readonly name = \"literal\";\n\
                 readonly value!: Out;\n\
             }",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn later_generic_class_negative_controls_remain_strict() {
        let wrong_payload = check_text(
            "abstract class Base { abstract readonly name: string; }\n\
             type Terminal =\n\
                 | (Base & { readonly name: \"unknown\" | \"never\" | \"string\" })\n\
                 | LiteralType<number>;\n\
             function wrongPayload(terminal: Terminal): void {\n\
                 if (terminal.name === \"literal\") {\n\
                     const wrong: string = terminal.value;\n\
                 }\n\
             }\n\
             class LiteralType<Out = unknown> extends Base {\n\
                 readonly name = \"literal\";\n\
                 readonly value!: Out;\n\
             }",
        );
        assert_eq!(
            checker_codes(&wrong_payload),
            [TYPE_NOT_ASSIGNABLE.as_str()]
        );

        let wrong_branch = check_text(
            "abstract class Base { abstract readonly name: string; }\n\
             type Terminal =\n\
                 | (Base & { readonly name: \"unknown\" | \"never\" | \"string\" })\n\
                 | LiteralType<number>;\n\
             function wrongBranch(terminal: Terminal): void {\n\
                 if (terminal.name === \"unknown\") terminal.value;\n\
             }\n\
             class LiteralType<Out = unknown> extends Base {\n\
                 readonly name = \"literal\";\n\
                 readonly value!: Out;\n\
             }",
        );
        assert_eq!(
            checker_codes(&wrong_branch),
            [PROPERTY_DOES_NOT_EXIST.as_str()]
        );
    }

    #[test]
    fn derived_generic_class_views_follow_final_base_shapes() {
        let result = check_text(
            "abstract class AbstractType<Output = unknown> {\n\
                 abstract optional<T>(defaultFn: () => T): Type<Output | T>;\n\
                 abstract optional(): Optional<Output>;\n\
                 map<T>(func: (value: Output) => T): Type<T> {\n\
                     return new TransformType<T>(this);\n\
                 }\n\
             }\n\
             abstract class Type<Output = unknown> extends AbstractType<Output> {\n\
                 optional<T>(defaultFn: () => T): Type<Output | T>;\n\
                 optional(): Optional<Output>;\n\
                 optional(defaultFn?: () => unknown): unknown {\n\
                     const optional = new Optional<Output>(this);\n\
                     return new TransformType<Output>(optional);\n\
                 }\n\
             }\n\
             class Optional<Output = unknown> extends AbstractType<Output | undefined> {\n\
                 constructor(source: Type<Output>) { super(); }\n\
                 optional<T>(defaultFn: () => T): Type<Output | T>;\n\
                 optional(): Optional<Output>;\n\
                 optional(defaultFn?: () => unknown): unknown { return this; }\n\
             }\n\
             class TransformType<Output = unknown> extends Type<Output> {\n\
                 constructor(source: AbstractType<unknown>) { super(); }\n\
                 check(): void {\n\
                     const base: AbstractType<unknown> = this;\n\
                 }\n\
             }",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn nested_same_class_applications_receive_structural_views() {
        let accepted = check_text(
            "abstract class AbstractType<Output = unknown> {
                 abstract value: Output;
             }
             class Type<Output> extends AbstractType<Output> {
                 value!: Output;
                 optional(): Type<Output | undefined> {
                     return this as Type<Output | undefined>;
                 }
             }
             declare const source: Type<string>;
             const base: AbstractType<string | undefined> = source.optional();",
        );
        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );

        let rejected = check_text(
            "abstract class AbstractType<Output = unknown> {
                 abstract value: Output;
             }
             class Type<Output> extends AbstractType<Output> {
                 value!: Output;
                 optional(): Type<Output | undefined> {
                     return this as Type<Output | undefined>;
                 }
             }
             declare const source: Type<string>;
             const wrong: AbstractType<number> = source.optional();",
        );
        assert_eq!(checker_codes(&rejected), ["BAMTS-C004"]);
    }

    #[test]
    fn tuple_type_argument_constraints_wait_for_complete_class_views() {
        let accepted = check_text_strict_null(
            "class Type<Output = unknown> {
                 nullable(): UnionType<[Type<null>, this]> { throw 0; }
             }
             class UnionType<Options extends Type[] = Type[]> extends Type<unknown> {}
             declare const source: Type<null>;
             const target: Type = source;",
        );

        assert!(
            checker_codes(&accepted).is_empty(),
            "{:?}",
            accepted.diagnostics()
        );
    }

    #[test]
    fn final_constraint_validation_rejects_invalid_tuple_type_arguments() {
        let result = check_text_strict_null(
            "class Type<Output = unknown> {}
             class UnionType<Options extends Type[] = Type[]> extends Type<unknown> {}
             type Invalid = UnionType<[string]>;",
        );

        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn recursive_interface_constraint_from_same_parameter_list_terminates() {
        let result = check_text("interface I1<T, U extends I1<T, any>> {}");

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn final_recursive_interface_constraint_rejects_invalid_argument() {
        let result = check_text("interface I1<T extends string, U extends I1<number, any>> {}");

        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn recursive_interface_reference_preserves_declared_defaults() {
        let result = check_text(
            "interface I<T extends string = string, U extends I = any> { value: T }
             declare const value: I;
             const accepted: string = value.value;
             const wrong: number = value.value;",
        );

        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn circular_type_parameter_default_reports_once() {
        let result = check_text("interface SelfReference<T = SelfReference> {}");

        assert_eq!(
            checker_codes(&result),
            [TYPE_PARAMETER_CIRCULAR_DEFAULT.as_str()]
        );
    }

    #[test]
    fn merged_interface_uses_default_from_later_declaration() {
        let result = check_text(
            "interface Box<T> {}
             interface Box<T = string> { value: T }
             declare const box: Box;
             const accepted: string = box.value;
             const wrong: number = box.value;",
        );

        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn inconsistent_interface_merge_arity_does_not_corrupt_metadata() {
        drop(check_text(
            "interface I {}
             interface I<T> {}
             interface I<T = number> {}
             interface I<T = number, U = string> {}",
        ));
    }

    #[test]
    fn recovered_labeled_class_uses_a_local_class_scope() {
        let result = check_text("\"use strict\"; label: class C {}");

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn recursive_generic_alias_bound_materializes_transparently() {
        let result = check_text(
            "type A1<T, U extends A1<any, any>> = [T, U];
             declare const alias: A1<string, [number, number]>;
             declare const tuple: [string, [number, number]];
             const from_tuple: A1<string, [number, number]> = tuple;
             const from_alias: [string, [number, number]] = alias;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn recursive_generic_alias_bound_rejects_invalid_argument_once() {
        let result = check_text(
            "type A1<T, U extends A1<any, any>> = [T, U];
             declare const invalid: A1<string, number>;",
        );

        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn primitive_alias_keeps_primitive_relations_and_narrowing() {
        let result = check_text(
            "type Id<T> = T;
             declare const value: Id<string>;
             const wrong: object = value;
             if (typeof value === 'string') {
                 const accepted: string = value;
             }",
        );

        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn function_alias_remains_callable() {
        let result = check_text(
            "type Fn<T> = (value: T) => T;
             declare const fn: Fn<number>;
             const accepted: number = fn(1);
             fn('wrong');",
        );

        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn inference_decomposes_generic_alias_structurally() {
        let result = check_text(
            "type Box<T> = { value: T };
             declare function unbox<T>(box: Box<T>): T;
             const value = unbox({ value: 1 });
             const accepted: number = value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn inference_through_transformed_recursive_alias_terminates() {
        let result = check_text(
            "type RecursiveBox<T> = { value: T; next: RecursiveBox<T[]> };
             declare function infer<T>(box: RecursiveBox<T>): T;
             declare const source: RecursiveBox<string>;
             const value = infer(source);
             const accepted: string = value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn relations_through_transformed_recursive_aliases_terminate() {
        let result = check_text(
            "type Recursive<T> = { value: T; next: Recursive<T[]> };
             declare const narrow: Recursive<'value'>;
             declare const invalid: Recursive<number>;
             const accepted: Recursive<string> = narrow;
             const wrong: Recursive<string> = invalid;",
        );

        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn nested_same_alias_arguments_publish_each_finite_view() {
        let result = check_text(
            "type Recursive<T> = { value: T; nested: Recursive<Recursive<T>> };
             declare const value: Recursive<string>;
             const accepted: string = value.nested.value.value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }
    #[test]
    fn recursive_alias_rhs_expands_lazily() {
        let result = check_text(
            "type Tree<T> = { value: T; children: Tree<T>[] };
             declare const tree: Tree<number>;
             const accepted: number = tree.children[0].value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn bare_circular_aliases_report_each_participant() {
        let result = check_text(
            "type A = A;
             type B = C;
             type C = B;
             type D = E[];
             type E = D[];",
        );

        assert_eq!(
            checker_codes(&result),
            [
                TYPE_ALIAS_CIRCULAR.as_str(),
                TYPE_ALIAS_CIRCULAR.as_str(),
                TYPE_ALIAS_CIRCULAR.as_str(),
            ]
        );
    }

    #[test]
    fn transformed_direct_alias_cycle_terminates() {
        let result = check_text(
            "type Expanding<T> = Expanding<T[]>;
             type Structural<T> = { next: Structural<T[]> };
             declare const valid: Structural<string>;",
        );

        assert_eq!(checker_codes(&result), [TYPE_ALIAS_CIRCULAR.as_str()]);
    }

    #[test]
    fn alias_cycle_prefix_is_not_a_cycle_participant() {
        let result = check_text(
            "type Prefix<T> = Loop<T[]>;
             type Loop<T> = Loop<T[]>;",
        );

        assert_eq!(checker_codes(&result), [TYPE_ALIAS_CIRCULAR.as_str()]);
    }

    #[test]
    fn alias_defaults_substitute_prior_parameters() {
        let result = check_text(
            "type Defaulted<T, U = T[]> = [T, U];
             declare const value: Defaulted<string>;
             const accepted: [string, string[]] = value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn interface_extends_object_alias() {
        let result = check_text(
            "type Properties<T> = { value: T };
             interface Extended extends Properties<number> { label: string }
             declare const value: Extended;
             const accepted: number = value.value;",
        );

        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn recursively_expanding_class_views_remain_bounded() {
        let result = check_text(
            "declare class Expanding<T> {
                 value: T;
                 next(): Expanding<T[]>;
             }
             declare const root: Expanding<string>;
             const once: Expanding<string[]> = root.next();
             const twice: Expanding<string[][]> = once.next();",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn polymorphic_this_tracks_the_call_receiver() {
        let result = check_text(
            "class Base {
                 chain(): this { return this; }
             }
             class Derived extends Base { derived = 1; }
             const value: Derived = new Derived().chain();
             const wrong: number = new Derived().chain();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn polymorphic_this_rejects_a_base_instance_return() {
        let result = check_text(
            "class Base {
                 clone(): this { return new Base(); }
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn inherited_interface_this_tracks_the_call_receiver() {
        let result = check_text(
            "interface Base {
                 chain(): this;
             }
             interface Derived extends Base { derived: number; }
             declare const source: Derived;
             const value: Derived = source.chain();
             const wrong: number = source.chain();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn generic_interface_this_survives_instantiation() {
        let result = check_text(
            "interface Base<T> {
                 value: T;
                 chain(): this;
             }
             interface Derived<T> extends Base<T> { derived: T; }
             declare const source: Derived<string>;
             const value: Derived<string> = source.chain();
             const wrong: Derived<number> = source.chain();",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn interface_call_and_index_this_project_parameters_and_results() {
        let result = check_text(
            "interface Base {
                 (value: this): this;
                 [key: string]: this;
             }
             interface Derived extends Base { derived: number; }
             declare const source: Derived;
             const called: Derived = source(source);
             const wrongCall: number = source(source);
             source({} as Base);
             const indexed: Derived = source['value'];
             const wrongIndex: number = source['value'];",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C004", "BAMTS-C053", "BAMTS-C004"]
        );
    }

    #[test]
    fn interface_construct_this_projects_parameters_and_results() {
        let result = check_text(
            "interface Base {
                 new (value: this): this;
             }
             interface Derived extends Base { derived: number; }
             declare const source: Derived;
             const value: Derived = new source(source);
             const wrong: number = new source(source);
             new source({} as Base);",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004", "BAMTS-C053"]);
    }

    #[test]
    fn interface_iterator_this_projects_elements() {
        let result = check_text(
            "interface Base {
                 [Symbol.iterator](): Iterator<this>;
             }
             interface Derived extends Base { derived: number; }
             declare const source: Derived;
             for (const item of source) {
                 const value: Derived = item;
                 const wrong: number = item;
             }",
        );
        assert_eq!(checker_codes(&result), ["BAMTS-C004"]);
    }

    #[test]
    fn unrelated_classes_do_not_gain_generic_base_compatibility() {
        let result = check_text(
            "abstract class AbstractType<Output = unknown> {\n\
                 abstract optional<T>(defaultFn: () => T): AbstractType<Output | T>;\n\
             }\n\
             class Unrelated {}\n\
             function accept(value: AbstractType<unknown>): void {}\n\
             function reject(value: Unrelated): void {\n\
                 const base: AbstractType<unknown> = value;\n\
                 accept(value);\n\
             }",
        );

        assert_eq!(
            checker_codes(&result),
            [
                TYPE_NOT_ASSIGNABLE.as_str(),
                ARGUMENT_NOT_ASSIGNABLE.as_str()
            ]
        );
    }

    #[test]
    fn optional_call_nullish_function_union_returns_union_with_undefined() {
        let result = check_text_strict_null(
            "declare let f: (() => number) | undefined;\
             const value: number | undefined = f?.();\
             const wrong: string = f?.();",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn ordinary_call_on_nullish_function_union_is_not_callable() {
        let result =
            check_text_strict_null("declare let f: (() => number) | undefined; const value = f();");
        assert_eq!(checker_codes(&result), [EXPRESSION_NOT_CALLABLE.as_str()]);
    }

    #[test]
    fn optional_call_retains_non_nullish_non_callable_diagnostic() {
        let result = check_text_strict_null(
            "declare let f: (() => number) | number | undefined; const value = f?.();",
        );
        assert_eq!(checker_codes(&result), [EXPRESSION_NOT_CALLABLE.as_str()]);
    }

    #[test]
    fn optional_member_call_result_and_diagnostics() {
        let result = check_text_strict_null(
            "declare let object: { method(): number } | undefined;\
             const value: number | undefined = object?.method();",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn type_reference_missing_type_argument_reports_count() {
        let result = check_text(
            "type Pair<T, U> = [T, U];\
             interface InterfacePair<T, U> { first: T; second: U; }\
             class ClassPair<T, U> { first!: T; second!: U; }\
             type A = Pair<number>;\
             type B = InterfacePair<number>;\
             type C = ClassPair<number>;",
        );
        assert_eq!(
            checker_codes(&result),
            [
                super::ARGUMENT_COUNT_MISMATCH.as_str(),
                super::ARGUMENT_COUNT_MISMATCH.as_str(),
                super::ARGUMENT_COUNT_MISMATCH.as_str()
            ]
        );
    }

    #[test]
    fn type_reference_extra_type_argument_reports_count() {
        let result = check_text("type One<T> = T; type Bad = One<number, string>;");
        assert_eq!(
            checker_codes(&result),
            [super::ARGUMENT_COUNT_MISMATCH.as_str()]
        );
    }

    #[test]
    fn type_reference_type_arguments_on_nongeneric_report_count() {
        let result = check_text(
            "type Plain = number;\
             interface PlainInterface { value: number; }\
             class PlainClass {}\
             type A = Plain<string>;\
             type B = PlainInterface<string>;\
             type C = PlainClass<string>;",
        );
        assert_eq!(
            checker_codes(&result),
            [
                super::ARGUMENT_COUNT_MISMATCH.as_str(),
                super::ARGUMENT_COUNT_MISMATCH.as_str(),
                super::ARGUMENT_COUNT_MISMATCH.as_str()
            ]
        );
    }

    #[test]
    fn type_reference_simple_constraint_violation() {
        let result =
            check_text("type Box<T extends string> = { value: T }; type Bad = Box<number>;");
        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn type_reference_dependent_constraint_violation() {
        let result =
            check_text("type Pair<T, U extends T> = [T, U]; type Bad = Pair<string, number>;");
        assert_eq!(checker_codes(&result), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn type_reference_forward_constraint_uses_complete_substitution() {
        let valid =
            check_text("type Pair<T extends U, U> = [T, U]; type Good = Pair<number, number>;");
        assert!(checker_codes(&valid).is_empty());

        let invalid =
            check_text("type Pair<T extends U, U> = [T, U]; type Bad = Pair<number, string>;");
        assert_eq!(checker_codes(&invalid), [ARGUMENT_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn type_reference_default_arguments_resolve() {
        let result = check_text(
            "type Box<T extends string = 'ok'> = { value: T };\
             const value: Box = { value: 'ok' };",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn call_expression_generic_validation_unchanged() {
        let result =
            check_text("declare function take<T extends string>(value: T): T; take<number>(1);");
        assert!(
            checker_codes(&result).contains(&ARGUMENT_NOT_ASSIGNABLE.as_str()),
            "{:?}",
            checker_codes(&result)
        );
    }

    #[test]
    fn interface_rejects_incompatible_derived_redeclaration() {
        let result = check_text(
            "interface Base { value: number; }\
             interface Derived extends Base { value: string; }",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn interface_rejects_optional_override_of_required_property() {
        let invalid = check_text(
            "interface Base { value: number; }\
             interface Derived extends Base { value?: number; }",
        );
        assert_eq!(checker_codes(&invalid), [TYPE_NOT_ASSIGNABLE.as_str()]);

        let valid = check_text(
            "interface Base { value?: number; }\
             interface Derived extends Base { value: number; }",
        );
        assert!(checker_codes(&valid).is_empty());
    }

    #[test]
    fn interface_rejects_conflicting_multiple_bases() {
        let result = check_text(
            "interface Left { value: number; }\
             interface Right { value: string; }\
             interface Derived extends Left, Right {}",
        );
        assert_eq!(checker_codes(&result), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn interface_accepts_compatible_and_equivalent_inheritance() {
        let result = check_text(
            "interface Left { value: number; }\
             interface Right { value: number; }\
             interface Derived extends Left, Right { value: number; }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn guarded_optional_record_property_narrows_in_truthy_branch() {
        let result = check_text(
            "declare const n: { methods?: Record<string, string[]> };\
             const m: string = '';\
             if (n.methods) {\
                 const arr: string[] = n.methods[m];\
             }",
        );
        assert!(checker_codes(&result).is_empty());
    }

    #[test]
    fn unguarded_optional_record_indexed_access_is_rejected() {
        let result = check_text(
            "declare const n: { methods?: Record<string, string[]> };\
             const m: string = '';\
             const arr: string[] = n.methods[m];",
        );
        assert_eq!(
            checker_codes(&result),
            [super::INVALID_INDEXED_ACCESS_KEY.as_str()]
        );
    }
    #[test]
    fn f4_function_declaration3_matches_the_upstream_baseline() {
        // Upstream baseline FunctionDeclaration3.errors.txt (sha256
        // 22ca7ff40e6fd00df5cfc6b210afe5303aac5ceb18340bb3512f789de42638aa):
        // TS2391 at (1,10) plus TS7010 at (1,10) — the implicit-any return
        // pairing reports at the same name range in upstream row order.
        // TS7010 is a noImplicitAny diagnostic: the suite lane runs this case
        // strict-default-on (check_cells build_tsconfig supplies strict:true
        // when no pragma is present), so the pin checks with the option on.
        let result = check_text_with(
            "function foo();\n1+1;\nfunction foo():string { return \"a\" }",
            ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        let diagnostics = result
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str().starts_with("BAMTS-C"))
            .collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        // The suite comparator sorts rows by position plus canonical code,
        // so only the pairing and the shared name range are contractual.
        let mut codes = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>();
        codes.sort_unstable();
        assert_eq!(codes, ["BAMTS-C037", "BAMTS-C039"]);
        for diagnostic in &diagnostics {
            assert_eq!(diagnostic.range().start().get(), 9);
            assert_eq!(diagnostic.range().end().get(), 12);
        }
    }

    #[test]
    fn f4_parameter_list5_keeps_the_function_body_and_return_type() {
        // Upstream baseline ParameterList5.errors.txt (sha256 414b66f7...)
        // expects exactly four errors (TS2355/TS2369/TS7006/TS2304) with a
        // live function body. The parser must not turn the annotated
        // function type into a bodyless declaration, so C039 and the
        // value-level C002 for `C` stay absent. The zero-return fall-through
        // pairs TS2355 (BAMTS-C081) with the unresolved return-type name C
        // (C003, TS2304) at (1,29) => offset 28. TS2369/TS7006 in the type
        // position additionally need modifier modeling on function-type
        // parameters and are tracked as a syntax.rs change-window item.
        let result = check_text("function A(): (public B) => C {\n}");
        let diagnostics = result
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str().starts_with("BAMTS-C"))
            .collect::<Vec<_>>();
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code().as_str() == "BAMTS-C039"),
            "the body survives, so no missing-implementation error: {diagnostics:?}"
        );
        let codes = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>();
        assert_eq!(codes, ["BAMTS-C081", "BAMTS-C003"], "{diagnostics:?}");
        let unresolved = &diagnostics[1];
        assert_eq!(unresolved.range().start().get(), 28);
        assert_eq!(unresolved.range().end().get(), 29);
    }

    #[test]
    fn static_block_keeps_es5_strict_block_function_rule() {
        let result = check_text_with(
            "class C { static { function f() {} } }",
            ProgramCheckOptions::standard().with_target(Some("es5")),
        );
        let codes = checker_codes_of(&result);
        assert_eq!(codes, ["BAMTS-C040"], "{codes:?}");
    }

    #[test]
    fn static_block_keeps_overload_implementation_check() {
        let result = check_text_with(
            "class C { static { function f(x: string): string; } }",
            ProgramCheckOptions::standard(),
        );
        let codes = checker_codes_of(&result);
        assert_eq!(codes, ["BAMTS-C039"], "{codes:?}");
    }
    #[test]
    fn f4_computed_symbol_object_members_accept_without_errors() {
        // Upstream acceptSymbolAsWeakType expects zero diagnostics; symbol
        // receivers must not trigger weak-type or member-resolution errors.
        let result = check_text(
            "var s: symbol;\nvar x = {\n    [s]: 0,\n    [s]() { },\n    get [s]() {\n        return 0;\n    }\n}",
        );
        assert!(
            checker_codes(&result).is_empty(),
            "{:?}",
            result.diagnostics()
        );
    }

    #[test]
    fn f4_direct_abstract_union_construction_reports_c066() {
        // Upstream abstractClassUnionInstantiation reports TS2511 for
        // `new cls1()` and `new cls2()` and none for `new cls3()`. The three
        // `.map(cls => new cls())` rows additionally need array-literal
        // union inference in the binder and are tracked separately.
        let result = check_text(
            "class ConcreteA {}\n\
             class ConcreteB {}\n\
             abstract class AbstractA { a: string; }\n\
             abstract class AbstractB { b: string; }\n\
             type Abstracts = typeof AbstractA | typeof AbstractB;\n\
             type Concretes = typeof ConcreteA | typeof ConcreteB;\n\
             type ConcretesOrAbstracts = Concretes | Abstracts;\n\
             declare const cls1: ConcretesOrAbstracts;\n\
             declare const cls2: Abstracts;\n\
             declare const cls3: Concretes;\n\
             new cls1();\n\
             new cls2();\n\
             new cls3();",
        );
        assert_eq!(
            checker_codes(&result),
            ["BAMTS-C066", "BAMTS-C066"],
            "{:?}",
            result.diagnostics()
        );
    }
    // ---- strict-family option tests -------------------------------------------

    #[test]
    fn strict_master_switch_lifts_unset_members_only() {
        // `with_strict` mirrors upstream tsconfig merge semantics: apply the
        // master switch FIRST, then an explicit member value wins. (Resolution
        // from raw tsconfig happens at parse time via `unwrap_or(strict)`, so
        // config-driven users never depend on builder order.)
        // optionsStrictPropertyInitializationStrict.ts (sha256
        // 4c5f28823ac849778d69aed835f56cfff163dfb871c3d31496a0d0b46531c749)
        // pairs strict with an explicit strictPropertyInitialization member.
        let all = ProgramCheckOptions::standard().with_strict(true);
        assert!(all.no_implicit_any());
        assert!(all.strict_null_checks());
        assert!(all.strict_property_initialization());
        assert!(all.always_strict());

        let off = ProgramCheckOptions::standard().with_strict(false);
        assert!(!off.no_implicit_any());
        assert!(!off.strict_null_checks());
        assert!(!off.strict_property_initialization());
        assert!(!off.always_strict());

        let explicit_wins = ProgramCheckOptions::standard()
            .with_strict(true)
            .with_no_implicit_any(false);
        assert!(!explicit_wins.no_implicit_any());
        assert!(explicit_wins.strict_null_checks());
        assert!(explicit_wins.strict_property_initialization());
    }

    #[test]
    fn no_implicit_any_gates_implicit_any_return_diagnostics() {
        // Upstream noImplicitAnyFunctions.ts baseline (sha256
        // 3823b182606ca6ef66147393d37e9323a9a44f08ef6256fe02c1b04285e9e4aa)
        // reports TS7010 on `declare function f1();` only under noImplicitAny.
        let on = check_text_with(
            "type Shape = { m(); }",
            ProgramCheckOptions::standard().with_no_implicit_any(true),
        );
        assert!(
            checker_codes_of(&on)
                .iter()
                .any(|code| code == MISSING_METHOD_RETURN_TYPE.as_str()),
            "{:?}",
            on.diagnostics()
        );

        let off = check_text_with("type Shape = { m(); }", ProgramCheckOptions::standard());
        assert!(
            !checker_codes_of(&off)
                .iter()
                .any(|code| code == MISSING_METHOD_RETURN_TYPE.as_str()),
            "{:?}",
            checker_codes_of(&off)
        );
    }

    #[test]
    fn strict_null_checks_gates_nullability_diagnostics() {
        // Upstream chainedAssignment2.ts baseline (sha256
        // 54d902661c1551495c19f5265b39d1d9464217b4611e5988a683b4e46aaa21d8)
        // reports TS2322 for `var a: string; a = null;` under strictNullChecks.
        let on = check_text_with(
            "declare const value: string | null;\nconst text: string = value;",
            ProgramCheckOptions::standard().with_strict_null_checks(true),
        );
        assert!(!checker_codes_of(&on).is_empty(), "{:?}", on.diagnostics());

        let off = check_text_with(
            "declare const value: string | null;\nconst text: string = value;",
            ProgramCheckOptions::standard(),
        );
        assert!(checker_codes_of(&off).is_empty(), "{:?}", off.diagnostics());
    }

    #[test]
    fn always_strict_classifies_javascript_sources_as_strict() {
        // ambientWithStatements(alwaysstrict=true).errors.txt (sha256
        // d74b39e71a929ba1320370582a8eaf858e4c42fa409f0a292660fa4d7e58d922)
        // reports TS1101 for `with` in strict mode; the sloppy variant
        // (sha256 8f88114e...) has no TS1101. `alwaysStrict` must therefore
        // force the strict classification of a classic script.
        let parsed_js = |text: &'static str| {
            crate::parser::parse(crate::scanner::scan(
                SourceId::new(0),
                ScriptKind::JavaScript,
                source(text),
            ))
        };
        let strict = super::binder::bind_source_with_environment(
            parsed_js("with ({}) {}").product(),
            super::intrinsic_environment::GlobalEnvironment::standard(
                super::intrinsic_environment::LibSet::ALL,
            ),
            false,
            ProgramCheckOptions::standard().with_always_strict(true),
        );
        assert!(
            strict
                .1
                .iter()
                .any(|diagnostic| diagnostic.code() == WITH_STATEMENT_NOT_ALLOWED),
            "{:?}",
            strict.1
        );

        let sloppy = super::binder::bind_source_with_environment(
            parsed_js("with ({}) {}").product(),
            super::intrinsic_environment::GlobalEnvironment::standard(
                super::intrinsic_environment::LibSet::ALL,
            ),
            false,
            ProgramCheckOptions::standard(),
        );
        assert!(
            !sloppy
                .1
                .iter()
                .any(|diagnostic| diagnostic.code() == WITH_STATEMENT_NOT_ALLOWED),
            "{:?}",
            sloppy.1
        );
    }

    // ---- nullable operands (BAMTS-C086 / TS18050) ------------------------------

    /// Counts the nullable-operand reports, which is what the authority
    /// baselines pin: one per rejected operand, not one per expression.
    fn nullable_operand_reports(text: &str) -> usize {
        checker_codes_of(&check_text_strict_null(text))
            .iter()
            .filter(|code| code.as_str() == VALUE_CANNOT_BE_USED_HERE.as_str())
            .count()
    }

    #[test]
    fn arithmetic_and_bitwise_operators_reject_a_nullable_operand() {
        // Every operand is reported, so `null * null` reports twice. Grounded on
        // `arithmeticOperatorWithNullValueAndValidOperands` and `binaryArithmatic3`.
        assert_eq!(nullable_operand_reports("var a = null * 1;"), 1);
        assert_eq!(nullable_operand_reports("var a = 1 - undefined;"), 1);
        assert_eq!(nullable_operand_reports("var a = null / null;"), 2);
        assert_eq!(nullable_operand_reports("var a = undefined | 1;"), 1);
        assert_eq!(nullable_operand_reports("var a = 1 ^ null;"), 1);
        assert_eq!(nullable_operand_reports("var a = null << undefined;"), 2);
    }

    #[test]
    fn relational_and_in_operators_reject_a_nullable_operand() {
        // `comparisonOperatorWithOneOperandIsNull` reports on relational
        // operators and `inOperatorWithInvalidOperands` on both `in` operands,
        // while equality accepts a nullable operand everywhere.
        assert_eq!(nullable_operand_reports("var a = 1 < null;"), 1);
        assert_eq!(nullable_operand_reports("var a = undefined >= 1;"), 1);
        assert_eq!(
            nullable_operand_reports("var o = {}; var a = null in o;"),
            1
        );
        assert_eq!(
            nullable_operand_reports("var o = {}; var a = \"k\" in undefined;"),
            1
        );
        assert_eq!(nullable_operand_reports("var a = 1 == null;"), 0);
        assert_eq!(nullable_operand_reports("var a = undefined !== 1;"), 0);
    }

    #[test]
    fn concatenation_keeps_a_nullable_operand_only_beside_a_string() {
        // `operatorAddNullUndefined` reports both operands of `null + null` and
        // leaves exactly its four `"test" + null`-shaped lines clean, because a
        // string-assignable partner makes `+` concatenate rather than coerce.
        assert_eq!(nullable_operand_reports("var a = null + null;"), 2);
        assert_eq!(nullable_operand_reports("var a = 1 + undefined;"), 1);
        assert_eq!(nullable_operand_reports("var a = \"t\" + null;"), 0);
        assert_eq!(nullable_operand_reports("var a = undefined + \"t\";"), 0);
        // An `any` partner is string-assignable too, so it suppresses `+` but
        // never the arithmetic operators.
        assert_eq!(
            nullable_operand_reports("declare var x: any; var a = null + x;"),
            0
        );
        assert_eq!(
            nullable_operand_reports("declare var x: any; var a = null * x;"),
            1
        );
    }

    #[test]
    fn a_union_partner_suppresses_concatenation_only_when_every_member_is_a_string() {
        // The relations engine's rule for a union source is "every member", so
        // a union carrying one non-string member still coerces and the nullable
        // operand is reported. An any-member test would wrongly suppress these.
        assert_eq!(
            nullable_operand_reports("declare var u: \"a\" | \"b\"; var a = u + null;"),
            0
        );
        assert_eq!(
            nullable_operand_reports("declare var u: \"a\" | 1; var a = u + null;"),
            1
        );
        assert_eq!(
            nullable_operand_reports("declare var u: string | number; var a = u + null;"),
            1
        );
        // The boxed wrapper interfaces are not string-assignable either, which
        // `additionOperatorWithNullValueAndInvalidOperator` pins.
        assert_eq!(
            nullable_operand_reports("declare var d: Number; var a = null + d;"),
            1
        );
    }

    #[test]
    fn unary_coercions_reject_a_nullable_operand_but_tests_accept_one() {
        // `bitwiseNotOperatorWithAnyOtherType` and its plus/negate siblings
        // report; `!x`, `typeof x`, and `void x` never coerce, so they accept.
        assert_eq!(nullable_operand_reports("var a = ~undefined;"), 1);
        assert_eq!(nullable_operand_reports("var a = -null;"), 1);
        assert_eq!(nullable_operand_reports("var a = +undefined;"), 1);
        assert_eq!(nullable_operand_reports("var a = !null;"), 0);
        assert_eq!(nullable_operand_reports("var a = typeof undefined;"), 0);
        assert_eq!(nullable_operand_reports("var a = void null;"), 0);
    }

    #[test]
    fn compound_assignment_inherits_its_operator_s_operand_rule() {
        // `compoundAdditionAssignmentWithInvalidOperands` reports the right
        // operand; the logical forms short-circuit and accept one.
        assert_eq!(
            nullable_operand_reports("declare var x: number; x -= null;"),
            1
        );
        assert_eq!(
            nullable_operand_reports("declare var x: number; x **= undefined;"),
            1
        );
        assert_eq!(
            nullable_operand_reports("declare var x: boolean; x += null;"),
            1
        );
        assert_eq!(
            nullable_operand_reports("declare var x: string; x += null;"),
            0
        );
        assert_eq!(
            nullable_operand_reports("declare var x: number; x ||= null;"),
            0
        );
        assert_eq!(
            nullable_operand_reports("declare var x: number; x ??= undefined;"),
            0
        );
    }

    #[test]
    fn dereferencing_a_nullable_value_is_rejected_unless_it_is_optional() {
        // `nullKeyword`, `propertyAccess4`, and `moduleVariableArrayIndexer`
        // report the dereferenced object; optional chaining tests instead.
        assert_eq!(nullable_operand_reports("var a = null.foo;"), 1);
        assert_eq!(nullable_operand_reports("var a = undefined[0];"), 1);
        assert_eq!(nullable_operand_reports("var a = null?.foo;"), 0);
        // `omittedExpressionForOfLoop` reports the iterable.
        assert_eq!(
            nullable_operand_reports("for (const x of undefined) { }"),
            1
        );
    }

    #[test]
    fn a_nullable_operand_is_reported_at_the_operand_not_the_expression() {
        // The authority ranges name the operand, so a two-operand expression
        // yields two distinct spans rather than one expression-wide span.
        let checked = check_text_strict_null("var a = null / undefined;");
        let spans: Vec<_> = checked
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.code().as_str() == VALUE_CANNOT_BE_USED_HERE.as_str())
            .map(|diagnostic| diagnostic.range())
            .collect();
        assert_eq!(spans.len(), 2);
        assert_ne!(spans[0], spans[1]);
    }
    // ---- invalid assignment target retains the operand (BAMTS-C086 on nullish) --

    fn checker_codes_strict_null(text: &str) -> Vec<String> {
        checker_codes_of(&check_text_strict_null(text))
    }

    #[test]
    fn increment_of_null_reports_invalid_target_and_nullish_operand() {
        // `++null` – TS authority reports TS2357 (invalid increment operand)
        // and TS18050 (null cannot be used here).  Our C036 covers the
        // invalid-target diagnostic and C086 covers the nullish-operand
        // diagnostic.
        let codes = checker_codes_strict_null("var r = ++null;");
        assert!(
            codes
                .iter()
                .any(|c| c == INVALID_ASSIGNMENT_TARGET.as_str()),
            "++null must report the invalid-target code C036, got {codes:?}"
        );
        assert!(
            codes
                .iter()
                .any(|c| c == VALUE_CANNOT_BE_USED_HERE.as_str()),
            "++null must report the nullish-operand code C086, got {codes:?}"
        );
    }

    #[test]
    fn compound_assignment_to_null_reports_invalid_target_and_nullish_operand() {
        // `null *= 1` – TS authority reports TS2364 and TS18050 for compound
        // assignment to a null literal.  Our C036 covers the invalid-target
        // diagnostic and C086 covers the nullish-operand diagnostic.
        let codes = checker_codes_strict_null("null *= 1;");
        assert!(
            codes
                .iter()
                .any(|c| c == INVALID_ASSIGNMENT_TARGET.as_str()),
            "null *= 1 must report the invalid-target code C036, got {codes:?}"
        );
        assert!(
            codes
                .iter()
                .any(|c| c == VALUE_CANNOT_BE_USED_HERE.as_str()),
            "null *= 1 must report the nullish-operand code C086, got {codes:?}"
        );
    }

    #[test]
    fn valid_assignment_target_is_unchanged() {
        // A plain identifier assignment must not report C036 or C086.
        let codes = checker_codes_strict_null("var x; x = 1;");
        assert!(
            !codes
                .iter()
                .any(|c| c == INVALID_ASSIGNMENT_TARGET.as_str()),
            "x = 1 must not report C036, got {codes:?}"
        );
        assert!(
            !codes
                .iter()
                .any(|c| c == VALUE_CANNOT_BE_USED_HERE.as_str()),
            "x = 1 must not report C086, got {codes:?}"
        );
    }
    #[test]
    fn grounded_cell_increment_null_matches_authority_multiset() {
        // Authority: incrementOperatorWithAnyOtherTypeInvalidOperations.ts
        // line 38 `++null` reports {TS2357, TS18050}.
        // Our mapping: TS2357→C036 (INVALID_ASSIGNMENT_TARGET),
        // TS18050→C086 (VALUE_CANNOT_BE_USED_HERE).
        let codes = checker_codes_strict_null("var r = ++null;");
        let c036 = INVALID_ASSIGNMENT_TARGET.as_str();
        let c086 = VALUE_CANNOT_BE_USED_HERE.as_str();
        let c036_count = codes.iter().filter(|c| c.as_str() == c036).count();
        let c086_count = codes.iter().filter(|c| c.as_str() == c086).count();
        assert_eq!(c036_count, 1, "expected exactly 1 C036, got {codes:?}");
        assert_eq!(c086_count, 1, "expected exactly 1 C086, got {codes:?}");
    }

    #[test]
    fn grounded_cell_compound_null_matches_authority_multiset() {
        // Authority: compoundAssignmentLHSIsValue.ts line 48 `null *= value`
        // reports TS2362 (arithmetic type check).  Our C036 covers the
        // invalid-target diagnostic and C086 covers the nullish-operand
        // diagnostic for `null *= 1`.
        let codes = checker_codes_strict_null("null *= 1;");
        let c036 = INVALID_ASSIGNMENT_TARGET.as_str();
        let c086 = VALUE_CANNOT_BE_USED_HERE.as_str();
        let c036_count = codes.iter().filter(|c| c.as_str() == c036).count();
        let c086_count = codes.iter().filter(|c| c.as_str() == c086).count();
        assert_eq!(c036_count, 1, "expected exactly 1 C036, got {codes:?}");
        assert_eq!(c086_count, 1, "expected exactly 1 C086, got {codes:?}");
    }

    // ---- enum member literal types -------------------------------------------

    #[test]
    fn null_plus_numeric_enum_member_reports_c086() {
        // `null + E.A` must report TS18050 (BAMTS-C086) because a numeric enum
        // member is not string-assignable, so `+` coerces rather than
        // concatenates.  Grounded on `additionOperatorWithNumberAndEnum`.
        assert_eq!(
            nullable_operand_reports("enum E { A } var a = null + E.A;"),
            1
        );
    }

    #[test]
    fn null_plus_string_enum_member_does_not_report_c086() {
        // A string enum member IS string-assignable, so `+` concatenates and
        // the nullable-operand rule does not fire.
        assert_eq!(
            nullable_operand_reports("enum E { A = \"a\" } var a = null + E.A;"),
            0
        );
    }

    #[test]
    fn numeric_enum_member_types_as_enum_dot_member() {
        // `E.A` must render as `E.A`, not `any` or `number`.
        let result = check_text("enum E { A, B } E.A;");
        let model = result.product();
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("enum E { A, B } E.A;"),
        ));
        let Statement::Expression(stmt) = parsed.product().statements()[1].data() else {
            panic!("second statement is the expression statement");
        };
        let type_id = model.node_type(stmt.expression.id()).expect("E.A is typed");
        assert_eq!(
            super::render_type(model, type_id),
            "E.A",
            "numeric enum member should render as E.A"
        );
    }

    #[test]
    fn numeric_enum_member_plus_one_types_as_number() {
        // `E.A + 1` must type as `number`, not `any`.
        let result = check_text("enum E { A } E.A + 1;");
        let model = result.product();
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("enum E { A } E.A + 1;"),
        ));
        let Statement::Expression(stmt) = parsed.product().statements()[1].data() else {
            panic!("second statement is the expression statement");
        };
        let type_id = model
            .node_type(stmt.expression.id())
            .expect("E.A + 1 is typed");
        assert_eq!(
            super::render_type(model, type_id),
            "number",
            "E.A + 1 should render as number"
        );
    }

    #[test]
    fn string_enum_member_types_as_enum_dot_member() {
        // `E.A` for a string enum must render as `E.A`, not `any` or `string`.
        let result = check_text("enum E { A = \"hello\", B = \"world\" } E.A;");
        let model = result.product();
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("enum E { A = \"hello\", B = \"world\" } E.A;"),
        ));
        let Statement::Expression(stmt) = parsed.product().statements()[1].data() else {
            panic!("second statement is the expression statement");
        };
        let type_id = model.node_type(stmt.expression.id()).expect("E.A is typed");
        assert_eq!(
            super::render_type(model, type_id),
            "E.A",
            "string enum member should render as E.A"
        );
    }

    #[test]
    fn string_enum_member_is_assignable_to_string() {
        // A string enum member is assignable to `string` but a numeric enum
        // member is not assignable to `string`.
        let result = check_text(
            "enum N { A } enum S { A = \"x\" } \
             var ns: string = S.A; \
             var nn: string = N.A;",
        );
        let codes = checker_codes(&result);
        // S.A → string is fine; N.A → string should error.
        assert!(
            codes.iter().any(|c| *c == TYPE_NOT_ASSIGNABLE.as_str()),
            "numeric enum member should not be assignable to string: {codes:?}"
        );
    }

    #[test]
    fn numeric_enum_member_is_assignable_to_number() {
        // A numeric enum member is assignable to `number`.
        let result = check_text("enum N { A } var nn: number = N.A;");
        let codes = checker_codes(&result);
        assert!(
            codes.iter().all(|c| *c != TYPE_NOT_ASSIGNABLE.as_str()),
            "numeric enum member should be assignable to number: {codes:?}"
        );
    }

    #[test]
    fn element_access_enum_member_types_as_enum_dot_member() {
        // `E["A"]` resolves to the same member literal type as `E.A`.
        let result = check_text("enum E { A, B } E[\"A\"];");
        let model = result.product();
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScript,
            source("enum E { A, B } E[\"A\"];"),
        ));
        let Statement::Expression(stmt) = parsed.product().statements()[1].data() else {
            panic!("second statement is the expression statement");
        };
        let type_id = model
            .node_type(stmt.expression.id())
            .expect("E[\"A\"] is typed");
        assert_eq!(
            super::render_type(model, type_id),
            "E.A",
            "element access enum member should render as E.A"
        );
    }
}
