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

pub(crate) mod binder;
pub mod conditional_types;
pub mod decorators;
#[rustfmt::skip]
#[path = "generated/diagnostic_messages.rs"]
pub mod diagnostic_messages;
pub mod enum_namespace;
pub mod inference;
pub(crate) mod intrinsic_environment;
pub mod jsx;
pub mod narrowing;
pub mod overloads;
pub mod relations;

mod type_display;
pub(crate) mod unused_imports;
pub(crate) mod unused_locals;
pub(crate) mod unused_reads;
pub use type_display::{render_type, render_type_annotated, render_type_declaration};

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
    EnumBindingView, ImportedSymbolType, bind_source_with_cancel,
    bind_source_with_environment_and_cancel, bind_source_with_environment_and_imports_with_cancel,
    is_numeric_enum_initializer, source_is_module,
};
pub use inference::{
    InferenceContext, InferenceParameter, InferencePriority, InferenceProvenance,
    InferredTypeArgument, InferredTypeArguments,
};
pub use intrinsic_environment::{global_lib_decl_file, lib_decl_files_for_global};
pub use narrowing::{
    FlowKey, FlowNodeId, GuardResolver, NarrowingContext, NarrowingGuard, TypeofName,
};
pub use relations::{RelationHazard, TypeRelation};

use crate::diagnostic::{Diagnostic, DiagnosticCode, Recovered};
use crate::enum_plan::{self, EnumDeclarationBinding};
use crate::lint::{LintProfile, LintTable};
use crate::source::{ScriptKind, SourceId, TextRange, Utf16Pos};
use crate::syntax::{
    ExternalModuleReference, IdentifierNode, ImportBinding, ModuleExportName, NodeId, SourceFile,
    Statement, TokenKind,
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
/// Diagnostic emitted when `eval` or `arguments` binds, assigns, or updates in
/// strict code outside a class or module. Corresponds to TypeScript's TS1100.
pub const EVAL_OR_ARGUMENTS_IN_STRICT_MODE: DiagnosticCode = DiagnosticCode::new("TS1100");
/// Diagnostic emitted when `eval` or `arguments` binds, assigns, or updates
/// inside a class body. Corresponds to TypeScript's TS1210.
pub const EVAL_OR_ARGUMENTS_IN_CLASS: DiagnosticCode = DiagnosticCode::new("TS1210");
/// Diagnostic emitted when `eval` or `arguments` binds, assigns, or updates in
/// a module outside a class body. Corresponds to TypeScript's TS1215.
pub const EVAL_OR_ARGUMENTS_IN_MODULE: DiagnosticCode = DiagnosticCode::new("TS1215");
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
/// Diagnostic emitted when an unannotated rest parameter's inferred type is not an array type.
pub const REST_PARAMETER_ARRAY_TYPE: DiagnosticCode = DiagnosticCode::new("BAMTS-C107");
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
pub(crate) const REST_PARAMETER_ARRAY_TYPE_MESSAGE: &str =
    "A rest parameter must be of an array type.";
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
    remove_comments: bool,
    /// ECMAScript target — drives lib derivation and downleveling decisions.
    target: crate::emitter::ScriptTarget,
    /// Active lib set — controls which intrinsic globals are installed.
    /// When empty (no explicit lib and no target), all globals are installed
    /// to preserve the pre-lib-scoping behavior.
    libs: LibSet,
    check_js: bool,
    /// Report an unused import binding with TS6133.
    no_unused_locals: bool,
    /// The JSX emit mode, for the classic factory read exemption.
    jsx: Option<crate::source::JsxEmit>,
    /// Report an unused parameter with TS6133.
    no_unused_parameters: bool,
    /// A custom classic JSX factory, fragment factory, or react namespace is configured.
    jsx_custom_factory: bool,
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
            remove_comments: false,
            target: crate::emitter::ScriptTarget::EsNext,
            libs: LibSet::ALL,
            check_js: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            jsx: None,
            jsx_custom_factory: false,
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
            remove_comments: false,
            target: crate::emitter::ScriptTarget::EsNext,
            libs: LibSet::ALL,
            check_js: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            jsx: None,
            jsx_custom_factory: false,
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

    #[must_use]
    pub const fn with_remove_comments(mut self, value: bool) -> Self {
        self.remove_comments = value;
        self
    }

    #[must_use]
    pub const fn remove_comments(&self) -> bool {
        self.remove_comments
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
    pub const fn with_no_unused_locals(mut self, value: bool) -> Self {
        self.no_unused_locals = value;
        self
    }

    #[must_use]
    pub const fn with_jsx(mut self, value: Option<crate::source::JsxEmit>) -> Self {
        self.jsx = value;
        self
    }

    #[must_use]
    pub const fn with_jsx_custom_factory(mut self, value: bool) -> Self {
        self.jsx_custom_factory = value;
        self
    }

    #[must_use]
    pub const fn with_no_unused_parameters(mut self, value: bool) -> Self {
        self.no_unused_parameters = value;
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

    #[must_use]
    pub const fn no_unused_locals(&self) -> bool {
        self.no_unused_locals
    }

    #[must_use]
    pub const fn jsx(&self) -> Option<crate::source::JsxEmit> {
        self.jsx
    }

    #[must_use]
    pub const fn jsx_custom_factory(&self) -> bool {
        self.jsx_custom_factory
    }

    #[must_use]
    pub const fn no_unused_parameters(&self) -> bool {
        self.no_unused_parameters
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

fn sibling_script_models<'m>(
    files: &'m BTreeMap<SourceId, SemanticModel>,
    script_ids: &HashSet<SourceId>,
    self_id: SourceId,
) -> Vec<&'m SemanticModel> {
    files
        .iter()
        .filter_map(|(id, model)| {
            if *id != self_id && script_ids.contains(id) {
                Some(model)
            } else {
                None
            }
        })
        .collect()
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

    let script_ids: HashSet<SourceId> = input
        .files
        .iter()
        .filter(|recovered| !source_is_module(recovered.product()))
        .map(|recovered| recovered.product().source_id())
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
    let direct_index = build_export_name_index(&exports);

    let worklist: Vec<SourceId> = source_ids.clone();
    for _ in 0..source_ids.len() {
        cancel.check()?;
        let mut member_cache: HashMap<SourceId, Vec<(EcmaString, TypeId)>> = HashMap::new();
        let mut rebound = Vec::new();
        for &source_id in &worklist {
            let Some(source) = input
                .files
                .iter()
                .map(|recovered| recovered.product())
                .find(|source| source.source_id() == source_id)
            else {
                continue;
            };
            let tables = CrossFileImportTables {
                imports: &imports,
                exports: &exports,
                export_stars: &export_stars,
                files: &files,
                direct_index: &direct_index,
            };
            let imported =
                collect_imported_types_for_source(source_id, source, &tables, &mut member_cache);
            if imported.is_empty() {
                continue;
            }
            let sibling_scripts = sibling_script_models(&files, &script_ids, source_id);
            let (model, _) = bind_source_with_environment_and_imports_with_cancel(
                source,
                options.environment(),
                source_is_module(source),
                options,
                &imported,
                &sibling_scripts,
                cancel.clone(),
            )?;
            rebound.push((source_id, model));
        }
        if rebound.is_empty() {
            break;
        }
        for (source_id, model) in rebound {
            files.insert(source_id, model);
        }
    }

    let mut diagnostics = Vec::new();
    let mut final_files = BTreeMap::new();
    let mut member_cache: HashMap<SourceId, Vec<(EcmaString, TypeId)>> = HashMap::new();
    for recovered in input.files {
        cancel.check()?;
        let source = recovered.product();
        let source_id = source.source_id();
        let tables = CrossFileImportTables {
            imports: &imports,
            exports: &exports,
            export_stars: &export_stars,
            files: &files,
            direct_index: &direct_index,
        };
        let imported =
            collect_imported_types_for_source(source_id, source, &tables, &mut member_cache);
        let sibling_scripts = sibling_script_models(&files, &script_ids, source_id);
        let (mut model, core_diagnostics) = bind_source_with_environment_and_imports_with_cancel(
            source,
            options.environment(),
            source_is_module(source),
            options,
            &imported,
            &sibling_scripts,
            cancel.clone(),
        )?;
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
        if options.no_unused_locals() && checked_sources.contains(&source.source_id()) {
            diagnostics.extend(unused_imports::unused_import_diagnostics(
                source,
                model,
                unused_imports::UnusedImportOptions {
                    jsx: options.jsx(),
                    jsx_custom_factory: options.jsx_custom_factory(),
                },
            ));
        }
        if (options.no_unused_locals() || options.no_unused_parameters())
            && checked_sources.contains(&source.source_id())
        {
            let unused = unused_locals::unused_diagnostics(source, model);
            if options.no_unused_locals() {
                diagnostics.extend(unused.locals);
            }
            if options.no_unused_parameters() {
                diagnostics.extend(unused.params);
            }
        }
    }
    Ok(Recovered::new(program, diagnostics))
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct LinkedEnum {
    source: SourceId,
    symbol: SymbolId,
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

#[cfg(test)]
std::thread_local! {
    static IMPORT_PROBE_ARMED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static IMPORT_INDEX_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static IMPORT_MEMBER_COMPUTES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
struct ImportProbe {
    _private: (),
}

#[cfg(test)]
impl ImportProbe {
    fn arm() -> Self {
        IMPORT_PROBE_ARMED.with(|armed| armed.set(true));
        IMPORT_INDEX_BUILDS.with(|count| count.set(0));
        IMPORT_MEMBER_COMPUTES.with(|count| count.set(0));
        ImportProbe { _private: () }
    }
    fn index_builds(&self) -> usize {
        IMPORT_INDEX_BUILDS.with(|count| count.get())
    }
    fn member_computes(&self) -> usize {
        IMPORT_MEMBER_COMPUTES.with(|count| count.get())
    }
}

#[cfg(test)]
impl Drop for ImportProbe {
    fn drop(&mut self) {
        IMPORT_PROBE_ARMED.with(|armed| armed.set(false));
    }
}

fn build_export_name_index(
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
) -> HashMap<SourceId, Vec<EcmaString>> {
    #[cfg(test)]
    if IMPORT_PROBE_ARMED.with(|armed| armed.get()) {
        IMPORT_INDEX_BUILDS.with(|count| count.set(count.get() + 1));
    }
    let mut direct_index: HashMap<SourceId, Vec<EcmaString>> = HashMap::new();
    for (source, name) in exports.keys() {
        direct_index.entry(*source).or_default().push(name.clone());
    }
    direct_index
}

fn namespace_export_names(
    target: SourceId,
    direct_index: &HashMap<SourceId, Vec<EcmaString>>,
    export_stars: &ExportStars,
) -> Vec<EcmaString> {
    let default_name = EcmaString::encode("default");
    let mut seen_sources = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut names = Vec::new();
    let mut stack = vec![target];
    while let Some(source) = stack.pop() {
        if !seen_sources.insert(source) {
            continue;
        }
        let is_target = source == target;
        if let Some(direct) = direct_index.get(&source) {
            for name in direct {
                if !is_target && *name == default_name {
                    continue;
                }
                if seen_names.insert(name.clone()) {
                    names.push(name.clone());
                }
            }
        }
        if let Some(targets) = export_stars.targets.get(&source) {
            for next in targets {
                if !seen_sources.contains(next) {
                    stack.push(*next);
                }
            }
        }
    }
    names.sort();
    names
}

fn namespace_member_types(
    target: SourceId,
    files: &BTreeMap<SourceId, SemanticModel>,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    direct_index: &HashMap<SourceId, Vec<EcmaString>>,
    cache: &mut HashMap<SourceId, Vec<(EcmaString, TypeId)>>,
) -> Vec<(EcmaString, TypeId)> {
    if let Some(cached) = cache.get(&target) {
        return cached.clone();
    }
    #[cfg(test)]
    if IMPORT_PROBE_ARMED.with(|armed| armed.get()) {
        IMPORT_MEMBER_COMPUTES.with(|count| count.set(count.get() + 1));
    }
    let names = namespace_export_names(target, direct_index, export_stars);
    let mut members = Vec::with_capacity(names.len());
    for name in names {
        let mut visited = HashSet::new();
        let resolution = resolve_export_candidates(
            target,
            &name,
            imports,
            exports,
            export_stars,
            files,
            &mut visited,
        );
        let mut values = HashSet::new();
        for candidate in &resolution.candidates {
            if let ExportCandidate::Value(linked) = candidate {
                values.insert(*linked);
            }
        }
        if values.len() != 1 {
            continue;
        }
        let linked = values.into_iter().next().expect("one value candidate");
        let Some(source_model) = files.get(&linked.source) else {
            continue;
        };
        let value = source_model.value_side_type(linked.symbol);
        if matches!(source_model.types().get(value), Type::Error) {
            continue;
        }
        members.push((name, value));
    }
    cache.insert(target, members.clone());
    members
}

struct CrossFileImportTables<'a> {
    imports: &'a HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &'a HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &'a ExportStars,
    files: &'a BTreeMap<SourceId, SemanticModel>,
    direct_index: &'a HashMap<SourceId, Vec<EcmaString>>,
}

/// Builds the [`ImportedSymbolType`] facts for one source file by translating
/// each import binding into the structural type of its resolved source export.
/// Named, default, and namespace imports all follow existing symbol identities;
/// cross-table types are copied through [`TypeTable::import_type`] at bind time.
/// Missing exports are skipped so the binder retains its current diagnostics.
fn collect_imported_types_for_source<'a>(
    source_id: SourceId,
    source: &SourceFile,
    tables: &CrossFileImportTables<'a>,
    member_cache: &mut HashMap<SourceId, Vec<(EcmaString, TypeId)>>,
) -> Vec<ImportedSymbolType<'a>> {
    let files = tables.files;
    let Some(model) = files.get(&source_id) else {
        return Vec::new();
    };
    let mut imported_types = Vec::new();
    for statement in source.statements() {
        if let Statement::ImportEquals(import) = statement.data() {
            if import.is_type_only
                || !matches!(&import.reference, ExternalModuleReference::Require(_))
            {
                continue;
            }
            let Some(symbol) = lookup_identifier(model, source, &import.local) else {
                continue;
            };
            let Some(ImportTarget::Namespace {
                source: target_source,
            }) = tables.imports.get(&(source_id, symbol))
            else {
                continue;
            };
            let target_source = *target_source;
            let members = namespace_member_types(
                target_source,
                tables.files,
                tables.imports,
                tables.exports,
                tables.export_stars,
                tables.direct_index,
                member_cache,
            );
            if members.is_empty() {
                continue;
            }
            let Some(target_model) = files.get(&target_source) else {
                continue;
            };
            imported_types.push(ImportedSymbolType {
                symbol,
                source_model: target_model,
                value_type_id: target_model.types().object(),
                type_parameters: &[],
                type_plane_id: None,
                const_key_type_id: None,
                namespace_members: members,
            });
            continue;
        }
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
                build_imported_symbol_type(source_id, symbol, tables, member_cache)
            {
                imported_types.push(imported);
            }
        }
        match &clause.binding {
            Some(ImportBinding::Namespace(local)) => {
                let Some(symbol) = lookup_identifier(model, source, local) else {
                    continue;
                };
                let Some(target) = tables.imports.get(&(source_id, symbol)) else {
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
                    const_key_type_id: None,
                    namespace_members: namespace_member_types(
                        target_source,
                        tables.files,
                        tables.imports,
                        tables.exports,
                        tables.export_stars,
                        tables.direct_index,
                        member_cache,
                    ),
                });
            }
            Some(ImportBinding::Named(specifiers)) => {
                for specifier in specifiers {
                    let specifier_data = specifier.data();
                    let Some(symbol) = lookup_identifier(model, source, &specifier_data.local)
                    else {
                        continue;
                    };
                    if let Some(imported) =
                        build_imported_symbol_type(source_id, symbol, tables, member_cache)
                    {
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
/// A named import of a namespace re-export (`export * as ns from './m'`)
/// answers the namespace's member list, so member access keeps each type.
fn build_imported_symbol_type<'a>(
    source_id: SourceId,
    symbol: SymbolId,
    tables: &CrossFileImportTables<'a>,
    member_cache: &mut HashMap<SourceId, Vec<(EcmaString, TypeId)>>,
) -> Option<ImportedSymbolType<'a>> {
    let target = tables.imports.get(&(source_id, symbol))?;
    let (target_source, target_name) = match target {
        ImportTarget::Named { source, name, .. } => (*source, name.clone()),
        ImportTarget::Namespace { .. } => return None,
    };
    let mut visited = HashSet::new();
    let resolution = resolve_export_candidates(
        target_source,
        &target_name,
        tables.imports,
        tables.exports,
        tables.export_stars,
        tables.files,
        &mut visited,
    );
    if resolution.candidates.len() != 1 {
        return None;
    }
    match resolution
        .candidates
        .iter()
        .next()
        .expect("checked single candidate")
    {
        ExportCandidate::Value(linked) => {
            let linked = *linked;
            let source_model = tables.files.get(&linked.source)?;
            let symbol_kind = source_model.symbol(linked.symbol).kind();
            // Classes and enums answer their constructor on the value plane;
            // the helper owns that rule for every reader.
            let value_type_id = source_model.value_side_type(linked.symbol);
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
                        .filter(|_| {
                            signatures.all(|entry| entry.signature.return_type() == return_type)
                        })
                    })
                }
                (SymbolKind::Interface | SymbolKind::TypeAlias, _) => Some(value_type_id),
                // Enums split planes like classes: the value plane is the
                // constructor, the type plane stays the scalar enum type.
                (SymbolKind::Enum, _) => Some(source_model.symbol_type(linked.symbol)),
                _ => None,
            };
            Some(ImportedSymbolType {
                symbol,
                source_model,
                value_type_id,
                type_parameters: source_model.generic_type_parameters(linked.symbol),
                type_plane_id,
                const_key_type_id: source_model.const_key_type(linked.symbol),
                namespace_members: Vec::new(),
            })
        }
        ExportCandidate::Namespace(namespace_source) => {
            let namespace_source = *namespace_source;
            let members = namespace_member_types(
                namespace_source,
                tables.files,
                tables.imports,
                tables.exports,
                tables.export_stars,
                tables.direct_index,
                member_cache,
            );
            if members.is_empty() {
                return None;
            }
            let namespace_model = tables.files.get(&namespace_source)?;
            Some(ImportedSymbolType {
                symbol,
                source_model: namespace_model,
                value_type_id: namespace_model.types().object(),
                type_parameters: &[],
                type_plane_id: None,
                const_key_type_id: None,
                namespace_members: members,
            })
        }
        ExportCandidate::Const(_) => None,
    }
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
fn resolve_imported_const_enum_value(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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
            if let Statement::ImportEquals(import) = statement.data()
                && let ExternalModuleReference::Require(_) = &import.reference
            {
                let Some(symbol) = lookup_identifier(model, source, &import.local) else {
                    continue;
                };
                let Some(target_source) = edges.get(&(source_id, statement.id())).copied() else {
                    continue;
                };
                targets.insert(
                    (source_id, symbol),
                    ImportTarget::Namespace {
                        source: target_source,
                    },
                );
                continue;
            }
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
fn resolve_imported_member_base(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    candidates: &HashMap<NodeId, enum_plan::ImportedEnumMemberUse>,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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
fn resolve_imported_member_result(
    source: SourceId,
    site: &enum_plan::ImportedEnumMemberUse,
    candidates: &HashMap<NodeId, enum_plan::ImportedEnumMemberUse>,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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

fn resolve_import_target(
    _source: SourceId,
    target: &ImportTarget,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolution {
    resolve_import_target_candidates(target, imports, exports, export_stars, files, visited)
        .into_resolution()
}

fn resolve_import_target_candidates(
    target: &ImportTarget,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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

fn resolve_export(
    source: SourceId,
    name: &EcmaString,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
    visited: &mut HashSet<(SourceId, EcmaString)>,
) -> ExportResolution {
    resolve_export_candidates(source, name, imports, exports, export_stars, files, visited)
        .into_resolution()
}

fn resolve_export_candidates(
    source: SourceId,
    name: &EcmaString,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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

fn resolve_exported_symbol_candidates(
    source: SourceId,
    symbol: SymbolId,
    imports: &HashMap<(SourceId, SymbolId), ImportTarget>,
    exports: &HashMap<(SourceId, EcmaString), ExportTarget>,
    export_stars: &ExportStars,
    files: &BTreeMap<SourceId, SemanticModel>,
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
    match model.symbol(symbol).kind() {
        SymbolKind::Import => {
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
        _ => ExportResolutionSet::candidate(value),
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
mod tests;
