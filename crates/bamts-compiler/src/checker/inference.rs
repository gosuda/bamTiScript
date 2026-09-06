//! Type-parameter inference over the interned [`TypeTable`]: generic call
//! inference, contextual signatures, and inference priorities.
//!
//! Generic functions are modeled as a [`Type::Function`] whose parameter and
//! return types mention [`Type::Named`] occurrences of type-parameter symbols.
//! [`InferenceContext`] opens one inference session over such a signature: each
//! [`InferenceContext::infer_from_argument`] call walks a declared parameter
//! type against a concrete argument type and records candidates for every
//! type-parameter occurrence it reaches. [`InferenceContext::resolve`] then
//! collapses the accumulated candidates into one [`InferredTypeArguments`]
//! mapping per type parameter, applying the parameter's `extends` constraint
//! and default as fallbacks.
//!
//! The resulting [`InferredTypeArguments`] also drives contextual typing:
//! [`InferredTypeArguments::instantiate`] and
//! [`InferredTypeArguments::instantiate_signature`] substitute the inferred
//! arguments through a type or signature, yielding the concrete signature a
//! contextually typed lambda is checked against.
//!
//! # Inference priorities
//!
//! Every candidate carries an [`InferencePriority`] tier, ordered
//! `Top > Middle > Low`:
//!
//! - **Top** — a *naked* type variable in a covariant position: the declared
//!   parameter type is exactly `T` (`identity<T>(value: T)`).
//! - **Middle** — a type variable nested inside a covariant composite: array
//!   elements, object properties, union members, and function return types
//!   (`first<T>(items: T[])`).
//! - **Low** — a type variable reached through a contravariant position:
//!   the parameter types of a function-typed argument
//!   (`map<T, U>(items: T[], f: (item: T) => U)` reaches `T` through `f`).
//!
//! Resolution is deterministic. Candidates are processed in argument
//! (encounter) order; the highest non-empty tier wins, and lower tiers are
//! discarded. Within one tier, distinct candidates combine by tier kind:
//!
//! - Upper-bound tiers (`Top`, `Middle`) pick the *best common supertype* —
//!   the first candidate in encounter order that every other tier candidate
//!   structurally subtypes. With no such candidate the tier resolves to the
//!   normalized union of its candidates.
//! - The lower-bound tier (`Low`) picks the *best common subtype* — the first
//!   candidate that subtypes every other. With no such candidate the first
//!   candidate in encounter order wins; intersection types are not modeled.
//!
//! A parameter with no candidates falls back to its declared default, then to
//! its `extends` constraint, then to `unknown`. An inferred candidate that is
//! not assignable to the parameter's `extends` constraint is replaced by the
//! constraint. Each outcome is recorded as [`InferenceProvenance`] so future
//! diagnostics can attribute a type argument to its source.

use std::collections::HashSet;

use super::binder::{
    ConstructEntry, FunctionParameter, FunctionSignature, IndexSignature, ObjectType, PropertyType,
    SymbolId, TupleShape, Type, TypeId, TypeParameterBounds, TypeTable,
};
use super::relations::TypeRelations;

/// The tier of one inference candidate, deciding which candidates a type
/// parameter resolves from. Ordered `Low < Middle < Top`; see the module
/// documentation for the exact position rules.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub enum InferencePriority {
    /// Reached through a contravariant position (function parameter types).
    Low,
    /// Nested inside a covariant composite (elements, properties, returns).
    Middle,
    /// A naked type variable in a covariant position.
    Top,
}

/// Where one resolved type argument came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InferenceProvenance {
    /// Inferred from an argument candidate.
    Inferred,
    /// No candidate survived; the `extends` constraint was substituted, or an
    /// inferred candidate failed the constraint check.
    Constraint,
    /// No candidates existed; the declared default type argument was used.
    Default,
    /// No candidates, default, or constraint; `unknown` was substituted.
    Unknown,
    /// Supplied explicitly in a type-argument list.
    Explicit,
}

/// One type parameter opened for inference, with its resolved bounds.
///
/// The constraint (`extends` clause) and default (`= ...` clause) are consumed
/// as already-resolved [`TypeId`]s; binding and resolving those syntax nodes is
/// the binder's job, not this module's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InferenceParameter {
    symbol: SymbolId,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
}

impl InferenceParameter {
    /// Opens the type parameter identified by `symbol` for inference.
    #[must_use]
    pub const fn new(symbol: SymbolId) -> Self {
        Self {
            symbol,
            constraint: None,
            default: None,
        }
    }

    /// Attaches the resolved `extends` constraint.
    #[must_use]
    pub const fn with_constraint(mut self, constraint: TypeId) -> Self {
        self.constraint = Some(constraint);
        self
    }

    /// Attaches the resolved default type argument.
    #[must_use]
    pub const fn with_default(mut self, default: TypeId) -> Self {
        self.default = Some(default);
        self
    }

    /// The symbol identifying the type parameter in [`Type::Named`].
    #[must_use]
    pub const fn symbol(&self) -> SymbolId {
        self.symbol
    }

    /// The resolved `extends` constraint, if any.
    #[must_use]
    pub const fn constraint(&self) -> Option<TypeId> {
        self.constraint
    }

    /// The resolved default type argument, if any.
    #[must_use]
    pub const fn default(&self) -> Option<TypeId> {
        self.default
    }
}

/// One candidate type recorded for a type parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct InferenceCandidate {
    type_id: TypeId,
    priority: InferencePriority,
    source: u32,
}
/// The variance of the position currently being walked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Variance {
    Covariant,
    Contravariant,
}

/// One resolved type argument for one type parameter, with provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InferredTypeArgument {
    symbol: SymbolId,
    type_id: TypeId,
    provenance: InferenceProvenance,
    widen_literal_union: bool,
}

impl InferredTypeArgument {
    /// The type parameter this argument was resolved for.
    #[must_use]
    pub const fn symbol(&self) -> SymbolId {
        self.symbol
    }

    /// The resolved type argument.
    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_id
    }

    /// Where the resolved type argument came from.
    #[must_use]
    pub const fn provenance(&self) -> InferenceProvenance {
        self.provenance
    }

    /// Creates a resolved argument for `symbol` from `type_id` with the given provenance.
    #[must_use]
    pub const fn new(symbol: SymbolId, type_id: TypeId, provenance: InferenceProvenance) -> Self {
        Self {
            symbol,
            type_id,
            provenance,
            widen_literal_union: false,
        }
    }
}

/// The resolved type arguments of one inference session, in type-parameter
/// declaration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InferredTypeArguments {
    arguments: Box<[InferredTypeArgument]>,
    this_receiver: Option<(SymbolId, TypeId)>,
}

impl InferredTypeArguments {
    /// The resolved type arguments in type-parameter declaration order.
    #[must_use]
    pub fn arguments(&self) -> &[InferredTypeArgument] {
        &self.arguments
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.arguments.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.arguments.is_empty()
    }

    /// Build a substitution from explicit type arguments.
    #[must_use]
    pub fn new(arguments: Vec<InferredTypeArgument>) -> Self {
        Self {
            arguments: arguments.into_boxed_slice(),
            this_receiver: None,
        }
    }

    #[must_use]
    pub fn for_this(owner: SymbolId, receiver: TypeId) -> Self {
        Self {
            arguments: Box::new([]),
            this_receiver: Some((owner, receiver)),
        }
    }

    /// Widens primitive-literal type arguments whose type parameter has no
    /// `extends` constraint, in place. Constrained parameters and non-literal
    /// arguments are untouched. The binder calls this after
    /// [`InferenceContext::resolve`] so the inferred function signature
    /// matches TypeScript's literal-widening for unconstrained generics
    /// (`infer(1)` yields `number`), while raw inference preserves literals.
    pub fn widen_unconstrained_literals(
        &mut self,
        table: &mut TypeTable,
        parameters: &[InferenceParameter],
    ) {
        for argument in self.arguments.iter_mut() {
            let unconstrained = parameters
                .iter()
                .find(|parameter| parameter.symbol() == argument.symbol())
                .is_some_and(|parameter| parameter.constraint().is_none());
            let literal_union = matches!(table.get(argument.type_id), Type::Union(_));
            let should_widen = !literal_union || argument.widen_literal_union;
            if unconstrained && should_widen && is_literal_union(table, argument.type_id) {
                argument.type_id = table.widen(argument.type_id, false);
            }
        }
    }

    /// The resolved type argument for `symbol`, if it was part of the session.
    #[must_use]
    pub fn get(&self, symbol: SymbolId) -> Option<TypeId> {
        self.arguments
            .iter()
            .find(|argument| argument.symbol() == symbol)
            .map(InferredTypeArgument::type_id)
    }

    /// The provenance of the resolved argument for `symbol`.
    #[must_use]
    pub fn provenance(&self, symbol: SymbolId) -> Option<InferenceProvenance> {
        self.arguments
            .iter()
            .find(|argument| argument.symbol() == symbol)
            .map(InferredTypeArgument::provenance)
    }

    /// Substitutes the inferred arguments through `ty`, returning the interned
    /// result. Types that mention no inferred type parameter intern back to
    /// their original [`TypeId`].
    pub fn instantiate(&self, table: &mut TypeTable, ty: TypeId) -> TypeId {
        let marker = table.substituted_alias_marker();
        let instantiated = self.instantiate_inner(table, ty);
        table.prepare_substituted_aliases(marker);
        instantiated
    }

    fn instantiate_inner(&self, table: &mut TypeTable, ty: TypeId) -> TypeId {
        match table.get(ty).clone() {
            Type::Named(symbol) => self.get(symbol).unwrap_or(ty),
            Type::This { owner, constraint } => {
                if let Some((expected, receiver)) = self.this_receiver
                    && expected == owner
                {
                    receiver
                } else {
                    let constraint = self.instantiate_inner(table, constraint);
                    table.this_type(owner, constraint)
                }
            }
            Type::Array(element) => {
                let element = self.instantiate_inner(table, element);
                table.array(element)
            }
            Type::Tuple(shape) => {
                let prefix = shape
                    .prefix
                    .iter()
                    .map(|&element| self.instantiate_inner(table, element))
                    .collect();
                let rest = shape
                    .rest
                    .map(|element| self.instantiate_inner(table, element));
                let suffix = shape
                    .suffix
                    .iter()
                    .map(|&element| self.instantiate_inner(table, element))
                    .collect();
                table.tuple_shape(TupleShape {
                    prefix,
                    rest,
                    suffix,
                    required: shape.required,
                })
            }
            Type::Union(members) => {
                let members: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.instantiate_inner(table, *member))
                    .collect();
                table.union(&members)
            }
            Type::Intersection(members) => {
                let members = members
                    .iter()
                    .map(|member| self.instantiate_inner(table, *member))
                    .collect();
                table.intersection_ordered(members)
            }
            Type::ObjectType(object) => {
                let properties: Vec<PropertyType> = object
                    .properties
                    .iter()
                    .map(|property| {
                        PropertyType::new(
                            property.name(),
                            property.optional(),
                            self.instantiate_inner(table, property.type_id()),
                        )
                        .with_readonly(property.readonly())
                        .with_getter_only(property.getter_only())
                        .with_accessibility(property.access(), property.declaring_class())
                        .with_declaring_types(property.declaring_types().to_vec())
                        .with_method(property.is_method())
                        .with_spreadable(property.spreadable())
                    })
                    .collect();
                let call_signatures = object
                    .call_signatures
                    .iter()
                    .map(|signature| {
                        let type_id = self.instantiate_function(
                            table,
                            signature.type_parameters(),
                            signature,
                        );
                        let Type::Function(signature) = table.get(type_id) else {
                            unreachable!("function instantiation returns a function type");
                        };
                        signature.clone()
                    })
                    .collect();
                let construct_signatures = object
                    .construct_signatures
                    .iter()
                    .map(|entry| {
                        let type_id = self.instantiate_function(
                            table,
                            entry.signature.type_parameters(),
                            &entry.signature,
                        );
                        let Type::Function(signature) = table.get(type_id) else {
                            unreachable!("function instantiation returns a function type");
                        };
                        ConstructEntry {
                            signature: signature.clone(),
                            is_abstract: entry.is_abstract,
                        }
                    })
                    .collect();
                let index_signatures = object
                    .index_signatures
                    .iter()
                    .map(|signature| IndexSignature {
                        readonly: signature.readonly,
                        parameters: signature
                            .parameters
                            .iter()
                            .map(|parameter| {
                                FunctionParameter::new(
                                    parameter.name().to_owned(),
                                    self.instantiate_inner(table, parameter.type_id()),
                                    parameter.optional(),
                                    parameter.rest(),
                                )
                            })
                            .collect(),
                        value_type: self.instantiate_inner(table, signature.value_type),
                        declaring_types: signature.declaring_types.clone(),
                    })
                    .collect();
                let generator_return = object
                    .generator_return
                    .map(|return_type| self.instantiate_inner(table, return_type));
                let iterator_property = object.iterator_property.as_ref().map(|property| {
                    property.with_type_id(self.instantiate_inner(table, property.type_id()))
                });
                let async_iterator_property =
                    object.async_iterator_property.as_ref().map(|property| {
                        property.with_type_id(self.instantiate_inner(table, property.type_id()))
                    });
                table.object_type_with_members(ObjectType {
                    properties,
                    call_signatures,
                    call_candidate_order: Vec::new(),
                    construct_signatures,
                    index_signatures,
                    generator_return,
                    iterator_property,
                    async_iterator_property,
                })
            }
            Type::Function(signature) => {
                self.instantiate_function(table, signature.type_parameters(), &signature)
            }
            Type::AppliedClass { symbol, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|&argument| self.instantiate_inner(table, argument))
                    .collect();
                table.applied_class(symbol, arguments)
            }
            Type::ConstructorType {
                symbol,
                arguments,
                structural,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|&argument| self.instantiate_inner(table, argument))
                    .collect();
                let structural = self.instantiate_inner(table, structural);
                table.constructor_type(symbol, arguments, structural)
            }
            Type::AppliedAlias { symbol, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|&argument| self.instantiate_inner(table, argument))
                    .collect();
                table.intern_substituted_alias(symbol, arguments)
            }
            Type::Keyof(operand) => {
                let operand = self.instantiate_inner(table, operand);
                table.keyof(operand)
            }
            Type::IndexedAccess { object, index } => {
                let object = self.instantiate_inner(table, object);
                let index = self.instantiate_inner(table, index);
                table.indexed_access(object, index)
            }
            Type::Record { key, value } => {
                let key = self.instantiate_inner(table, key);
                let value = self.instantiate_inner(table, value);
                table.record(key, value)
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
            | Type::NumericEnum(_)
            | Type::EnumMember { .. } => ty,
        }
    }

    /// Substitutes the inferred arguments through a generic signature and
    /// interns the result: the *contextual signature* a lambda argument is
    /// checked against once the call's type arguments are known.
    pub fn instantiate_signature(
        &self,
        table: &mut TypeTable,
        signature: &FunctionSignature,
    ) -> TypeId {
        let marker = table.substituted_alias_marker();
        let instantiated = self.instantiate_function(table, &[], signature);
        table.prepare_substituted_aliases(marker);
        instantiated
    }

    /// Shared core of [`Self::instantiate`] and [`Self::instantiate_signature`]:
    /// substitutes the inferred arguments through `signature`'s parameters and
    /// return type, preserving `type_parameters` on the interned result. The
    /// top-level contextual signature passes `&[]` (its own generics are
    /// resolved); nested function types pass their own `type_parameters` so
    /// inner generics survive instantiation.
    fn instantiate_function(
        &self,
        table: &mut TypeTable,
        type_parameters: &[SymbolId],
        signature: &FunctionSignature,
    ) -> TypeId {
        let parameters: Vec<FunctionParameter> = signature
            .parameters()
            .iter()
            .map(|parameter| {
                FunctionParameter::new(
                    parameter.name().to_owned(),
                    self.instantiate_inner(table, parameter.type_id()),
                    parameter.optional(),
                    parameter.rest(),
                )
            })
            .collect();
        let mut bounds = Vec::with_capacity(type_parameters.len());
        if !type_parameters.is_empty() {
            debug_assert_eq!(
                type_parameters.len(),
                signature.type_parameter_bounds().len()
            );
            for bound in signature.type_parameter_bounds() {
                let constraint = bound
                    .constraint()
                    .map(|constraint| self.instantiate_inner(table, constraint));
                let default = bound
                    .default()
                    .map(|default| self.instantiate_inner(table, default));
                bounds.push(TypeParameterBounds::new(constraint, default));
            }
        }
        let return_type = self.instantiate_inner(table, signature.return_type());
        let type_id = table.function_with_parameter_bounds(
            type_parameters.to_vec(),
            bounds,
            parameters,
            return_type,
            signature.javascript(),
        );
        if signature.declaring_types().is_empty() {
            return type_id;
        }
        let Type::Function(instantiated) = table.get(type_id) else {
            unreachable!("function construction returns a function type");
        };
        table.function_signature(
            instantiated
                .clone()
                .with_declaring_types(signature.declaring_types().to_vec()),
        )
    }
}
/// Returns true when `type_id` is a primitive literal or a union consisting
/// only of primitive literals, so unconstrained generic inference can widen it
/// to its base primitive type.
fn is_literal_union(table: &TypeTable, type_id: TypeId) -> bool {
    match table.get(type_id) {
        Type::StringLiteral(_)
        | Type::NumberLiteral(_)
        | Type::BooleanLiteral(_)
        | Type::BigIntLiteral(_) => true,
        Type::Union(members) => members
            .iter()
            .all(|&member| is_literal_union(table, member)),
        _ => false,
    }
}

/// One inference session over an interned [`TypeTable`].
///
/// Construct with the type parameters to solve, feed every argument of the
/// call through [`InferenceContext::infer_from_argument`] (or
/// [`InferenceContext::infer_from_arguments`] for a whole signature), then
/// consume the context with [`InferenceContext::resolve`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum AliasInferenceKey {
    Pair(SymbolId, SymbolId),
    Target(SymbolId, TypeId),
}

pub struct InferenceContext<'table> {
    table: &'table mut TypeTable,
    parameters: Vec<ParameterInference>,
    fresh_literal_sources: HashSet<u32>,
    active_pairs: HashSet<(TypeId, TypeId)>,
    active_aliases: HashSet<AliasInferenceKey>,
    /// Type parameters whose inferred candidates flowed through an
    /// instantiated generic *argument* signature. Their candidates may name
    /// an earlier type parameter of the same session (the argument's type
    /// parameter was paired with the declared one), so at resolve time the
    /// candidate routes through the earlier resolution instead of leaking a
    /// dangling type-parameter occurrence out of the call.
    substitute_candidate_symbols: HashSet<SymbolId>,
    /// Cooperative cancellation signal. `None` for the non-cancellable path.
    cancel: Option<bamts_cancel::CancellationToken>,
}

struct ParameterInference {
    parameter: InferenceParameter,
    candidates: Vec<InferenceCandidate>,
}

impl<'table> InferenceContext<'table> {
    pub fn new(table: &'table mut TypeTable, parameters: &[InferenceParameter]) -> Self {
        Self::new_with_cancel(table, parameters, None)
    }

    /// Opens an inference session that polls `cancel` during recursive type
    /// walking. Pass `None` for the non-cancellable path.
    #[must_use]
    pub fn new_with_cancel(
        table: &'table mut TypeTable,
        parameters: &[InferenceParameter],
        cancel: Option<bamts_cancel::CancellationToken>,
    ) -> Self {
        Self {
            table,
            parameters: parameters
                .iter()
                .map(|parameter| ParameterInference {
                    parameter: *parameter,
                    candidates: Vec::new(),
                })
                .collect(),
            fresh_literal_sources: HashSet::new(),
            active_pairs: HashSet::new(),
            active_aliases: HashSet::new(),
            substitute_candidate_symbols: HashSet::new(),
            cancel,
        }
    }

    /// Marks one call argument as a fresh literal whose nested literal
    /// candidates use TypeScript's widening inference.
    pub fn mark_fresh_literal_source(&mut self, source: u32) {
        self.fresh_literal_sources.insert(source);
    }

    /// Records inferences from one argument against its declared parameter
    /// type. `argument_type` is covariant: it flows into the parameter.
    pub fn infer_from_argument(
        &mut self,
        parameter_type: TypeId,
        argument_type: TypeId,
        source: u32,
    ) {
        self.infer_types(
            parameter_type,
            argument_type,
            true,
            Variance::Covariant,
            source,
        );
    }
    /// Records inferences for a whole call: each argument is zipped against
    /// the declared parameters of `signature` in order. Extra arguments and
    /// missing (optional/rest) parameters are ignored.
    pub fn infer_from_arguments(&mut self, signature: &FunctionSignature, arguments: &[TypeId]) {
        for (argument_index, parameter) in signature.parameters().iter().enumerate() {
            if parameter.rest() {
                // A rest parameter collects arguments[argument_index..], but
                // argument_index is the *parameter* index, not an argument
                // index. When fixed parameters before the rest are unsupplied
                // (e.g. f<T>(a: number, ...rest: T[]) called as f()), the
                // parameter index can exceed arguments.len() and the slice
                // would panic. Guard here, mirroring the non-rest bounds check
                // below.
                if argument_index >= arguments.len() {
                    break;
                }
                if let Type::Array(element) = self.table.get(parameter.type_id()).clone() {
                    for (offset, &argument_type) in arguments[argument_index..].iter().enumerate() {
                        self.infer_from_argument(
                            element,
                            argument_type,
                            (argument_index + offset) as u32,
                        );
                    }
                } else if let Type::Tuple(shape) = self.table.get(parameter.type_id()).clone() {
                    let rest_length = arguments.len() - argument_index;
                    for (offset, &argument_type) in arguments[argument_index..].iter().enumerate() {
                        for element in shape.element_types_at_length(offset, rest_length) {
                            self.infer_from_argument(
                                element,
                                argument_type,
                                (argument_index + offset) as u32,
                            );
                        }
                    }
                }
                break;
            }
            if argument_index >= arguments.len() {
                break;
            }
            self.infer_from_argument(
                parameter.type_id(),
                arguments[argument_index],
                argument_index as u32,
            );
        }
    }

    /// Collapses every recorded candidate into the final type arguments,
    /// applying defaults and `extends` constraints as documented in the
    /// module-level priority rules. Resolution runs in declaration order and
    /// each fallback is re-instantiated through the already resolved earlier
    /// arguments, so a default like `<T = string, U = T>` stores the concrete
    /// type for `U` rather than a bare `T` occurrence.
    #[must_use]
    pub fn resolve(mut self) -> InferredTypeArguments {
        let mut resolved = Vec::with_capacity(self.parameters.len());
        for index in 0..self.parameters.len() {
            let state = &self.parameters[index];
            let (parameter, candidates) = (state.parameter, state.candidates.clone());
            let (type_id, provenance, widen_literal_union) =
                self.resolve_parameter(&parameter, &candidates, &resolved);
            resolved.push(InferredTypeArgument {
                symbol: parameter.symbol(),
                type_id,
                provenance,
                widen_literal_union,
            });
        }
        InferredTypeArguments {
            arguments: resolved.into_boxed_slice(),
            this_receiver: None,
        }
    }

    fn is_inference_symbol(&self, symbol: SymbolId) -> bool {
        self.parameters
            .iter()
            .any(|state| state.parameter.symbol() == symbol)
    }

    fn add_candidate(
        &mut self,
        symbol: SymbolId,
        type_id: TypeId,
        priority: InferencePriority,
        source: u32,
    ) {
        if let Some(state) = self
            .parameters
            .iter_mut()
            .find(|state| state.parameter.symbol() == symbol)
        {
            state.candidates.push(InferenceCandidate {
                type_id,
                priority,
                source,
            });
        }
    }

    fn infer_types(
        &mut self,
        parameter_type: TypeId,
        argument_type: TypeId,
        naked: bool,
        variance: Variance,
        source: u32,
    ) {
        // Poll the cancellation token on every recursive entry. A cancelled
        // inference walk returns immediately; the binder's next `check_cancel`
        // propagates the typed error.
        if let Some(token) = &self.cancel
            && token.is_cancelled()
        {
            return;
        }
        let pair = (parameter_type, argument_type);
        if !self.active_pairs.insert(pair) {
            return;
        }
        let alias_key = match self.table.get(parameter_type) {
            Type::AppliedAlias {
                symbol: parameter_symbol,
                ..
            } => Some(match self.table.get(argument_type) {
                Type::AppliedAlias {
                    symbol: argument_symbol,
                    ..
                } => AliasInferenceKey::Pair(*parameter_symbol, *argument_symbol),
                _ => AliasInferenceKey::Target(*parameter_symbol, argument_type),
            }),
            _ => None,
        };
        if alias_key.is_some_and(|key| !self.active_aliases.insert(key)) {
            self.active_pairs.remove(&pair);
            return;
        }
        let parameter_type = self
            .table
            .prepare_applied_alias_view(parameter_type)
            .unwrap_or(parameter_type);
        let argument_type = self
            .table
            .prepare_applied_alias_view(argument_type)
            .unwrap_or(argument_type);
        let parameter = self.table.get(parameter_type).clone();
        match parameter {
            Type::Named(symbol) if self.is_inference_symbol(symbol) => {
                let priority = match variance {
                    Variance::Contravariant => InferencePriority::Low,
                    Variance::Covariant if naked => InferencePriority::Top,
                    Variance::Covariant => InferencePriority::Middle,
                };
                self.add_candidate(symbol, argument_type, priority, source);
            }
            Type::Array(parameter_element) => match self.table.get(argument_type).clone() {
                Type::Array(argument_element) => {
                    self.infer_types(parameter_element, argument_element, false, variance, source);
                }
                Type::Tuple(argument_shape) => {
                    let elements = argument_shape.all_element_types();
                    if !elements.is_empty() {
                        let unioned = if elements.len() == 1 {
                            elements[0]
                        } else {
                            self.table.union(&elements)
                        };
                        self.infer_types(parameter_element, unioned, false, variance, source);
                    }
                }
                _ => {}
            },
            Type::Tuple(parameter_shape) => {
                match self.table.get(argument_type).clone() {
                    Type::Tuple(argument_shape) => {
                        // Back suffixes first; they bound how much of the
                        // argument can be consumed from the front.
                        let mut back_count = 0;
                        if parameter_shape.rest.is_some() {
                            let argument_suffix = if argument_shape.rest.is_some() {
                                &argument_shape.suffix
                            } else {
                                &argument_shape.prefix
                            };
                            for (&parameter_element, &argument_element) in parameter_shape
                                .suffix
                                .iter()
                                .rev()
                                .zip(argument_suffix.iter().rev())
                            {
                                self.infer_types(
                                    parameter_element,
                                    argument_element,
                                    false,
                                    variance,
                                    source,
                                );
                                back_count += 1;
                            }
                        }

                        // Front prefix alignment.
                        let argument_front_available = if argument_shape.rest.is_some() {
                            argument_shape.prefix.len()
                        } else {
                            argument_shape
                                .max_arity()
                                .expect("fixed tuple has a maximum arity")
                                .saturating_sub(back_count)
                        };
                        let front_count =
                            parameter_shape.prefix.len().min(argument_front_available);
                        for index in 0..front_count {
                            self.infer_types(
                                parameter_shape.prefix[index],
                                argument_shape.prefix[index],
                                false,
                                variance,
                                source,
                            );
                        }

                        // Middle union of all argument element types that are
                        // not consumed by the front/back alignment.
                        let all_elements = argument_shape.all_element_types();
                        let start = front_count.min(all_elements.len());
                        let end = all_elements.len().saturating_sub(back_count);
                        if start < end {
                            let middle = if end - start == 1 {
                                all_elements[start]
                            } else {
                                self.table.union(&all_elements[start..end])
                            };

                            for index in front_count..parameter_shape.prefix.len() {
                                self.infer_types(
                                    parameter_shape.prefix[index],
                                    middle,
                                    false,
                                    variance,
                                    source,
                                );
                            }
                            if let Some(rest) = parameter_shape.rest {
                                self.infer_types(rest, middle, false, variance, source);
                            }
                            for offset in (back_count + 1)..=parameter_shape.suffix.len() {
                                let suffix_index = parameter_shape.suffix.len() - offset;
                                self.infer_types(
                                    parameter_shape.suffix[suffix_index],
                                    middle,
                                    false,
                                    variance,
                                    source,
                                );
                            }
                        }
                    }
                    Type::Array(argument_element) => {
                        for parameter_element in parameter_shape.all_element_types() {
                            self.infer_types(
                                parameter_element,
                                argument_element,
                                false,
                                variance,
                                source,
                            );
                        }
                    }
                    _ => {}
                }
            }
            Type::Union(members) => {
                for member in members {
                    self.infer_types(member, argument_type, false, variance, source);
                }
            }
            Type::ObjectType(object) => {
                let argument_type = match self.table.get(argument_type) {
                    Type::Array(_) | Type::Tuple(_) => self
                        .table
                        .iterable_view(argument_type)
                        .unwrap_or(argument_type),
                    _ => argument_type,
                };
                if let Type::ObjectType(argument_object) = self.table.get(argument_type).clone() {
                    for property in object.properties {
                        if let Some(argument_property) = argument_object
                            .properties
                            .iter()
                            .find(|candidate| candidate.name() == property.name())
                        {
                            self.infer_types(
                                property.type_id(),
                                argument_property.type_id(),
                                false,
                                variance,
                                source,
                            );
                        }
                    }
                    if let (Some(parameter_iterator), Some(argument_iterator)) = (
                        object.iterator_property.as_ref(),
                        argument_object.iterator_property.as_ref(),
                    ) && let (Some(parameter_yield), Some(argument_yield)) = (
                        self.sync_iterator_yield(parameter_iterator.type_id()),
                        self.sync_iterator_yield(argument_iterator.type_id()),
                    ) {
                        self.infer_types(parameter_yield, argument_yield, false, variance, source);
                    }
                }
            }
            Type::Function(signature) => {
                if let Type::Function(argument_signature) = self.table.get(argument_type).clone() {
                    let argument_signature = self
                        .instantiate_generic_argument_signature(&signature, &argument_signature);
                    for (actual_index, declared) in signature.parameters().iter().enumerate() {
                        if declared.rest() {
                            let actual = &argument_signature.parameters()[actual_index..];
                            match actual.first() {
                                Some(first) if first.rest() => {
                                    self.infer_types(
                                        declared.type_id(),
                                        first.type_id(),
                                        false,
                                        Variance::Contravariant,
                                        source,
                                    );
                                }
                                _ if !actual.is_empty() => {
                                    let rest_index =
                                        actual.iter().position(FunctionParameter::rest);
                                    let fixed = rest_index.unwrap_or(actual.len());
                                    let prefix = actual[..fixed]
                                        .iter()
                                        .map(FunctionParameter::type_id)
                                        .collect::<Vec<_>>();
                                    let required = actual[..fixed]
                                        .iter()
                                        .take_while(|parameter| !parameter.optional())
                                        .count()
                                        as u32;
                                    let rest = rest_index.and_then(|index| {
                                        match self.table.get(actual[index].type_id()) {
                                            Type::Array(element) => Some(*element),
                                            _ => None,
                                        }
                                    });
                                    let tuple = self.table.tuple_shape(TupleShape {
                                        prefix,
                                        required,
                                        rest,
                                        suffix: Vec::new(),
                                    });
                                    self.infer_types(
                                        declared.type_id(),
                                        tuple,
                                        false,
                                        Variance::Contravariant,
                                        source,
                                    );
                                }
                                _ => {}
                            }
                            break;
                        }
                        let Some(actual) = argument_signature.parameters().get(actual_index) else {
                            break;
                        };
                        self.infer_types(
                            declared.type_id(),
                            actual.type_id(),
                            false,
                            Variance::Contravariant,
                            source,
                        );
                    }
                    self.infer_types(
                        signature.return_type(),
                        argument_signature.return_type(),
                        false,
                        variance,
                        source,
                    );
                }
            }

            Type::AppliedClass { symbol, arguments } => {
                if let Type::AppliedClass {
                    symbol: argument_symbol,
                    arguments: argument_arguments,
                } = self.table.get(argument_type).clone()
                    && symbol == argument_symbol
                    && arguments.len() == argument_arguments.len()
                {
                    for (&parameter_argument, &argument_argument) in
                        arguments.iter().zip(argument_arguments.iter())
                    {
                        self.infer_types(
                            parameter_argument,
                            argument_argument,
                            false,
                            variance,
                            source,
                        );
                    }
                }
            }
            _ => {}
        }
        self.active_pairs.remove(&pair);
        if let Some(key) = alias_key {
            self.active_aliases.remove(&key);
        }
    }

    /// Instantiates a generic function-typed *argument* against the declared
    /// (contextual) signature before the positional pairing in
    /// [`InferenceContext::infer_types`]. TypeScript instantiates the source
    /// signature in the context of the target: for
    /// `map<T, U>(x: T, f: (y: T) => U)` called with `identity<V>(y: V)`,
    /// `V` is paired with the declared parameter type `T`, so the argument
    /// reads `(y: T) => T` and `U` infers from its return. Without this step
    /// the argument's own type parameter would flow into the candidates as a
    /// foreign symbol and the call result would mention a type parameter
    /// declared by nobody. Returns `argument` unchanged when it is not
    /// generic, when its type parameters already pair with the declared
    /// ones, or when some type parameter has no naked parameter-position
    /// candidate.
    fn instantiate_generic_argument_signature(
        &mut self,
        declared: &FunctionSignature,
        argument: &FunctionSignature,
    ) -> FunctionSignature {
        let argument_parameters = argument.type_parameters();
        if argument_parameters.is_empty() || argument_parameters == declared.type_parameters() {
            return argument.clone();
        }
        let declared_parameters = declared.parameters();
        let mut arguments = Vec::new();
        for (index, parameter) in argument.parameters().iter().enumerate() {
            if parameter.rest() {
                break;
            }
            let Some(declared_parameter) = declared_parameters.get(index) else {
                break;
            };
            let Type::Named(symbol) = self.table.get(parameter.type_id()) else {
                continue;
            };
            let symbol = *symbol;
            if !argument_parameters.contains(&symbol)
                || self.type_mentions_any(declared_parameter.type_id(), argument_parameters)
                || arguments
                    .iter()
                    .any(|resolved: &InferredTypeArgument| resolved.symbol() == symbol)
            {
                continue;
            }
            arguments.push(InferredTypeArgument::new(
                symbol,
                declared_parameter.type_id(),
                InferenceProvenance::Inferred,
            ));
        }
        if argument_parameters.iter().any(|symbol| {
            !arguments
                .iter()
                .any(|resolved| resolved.symbol() == *symbol)
        }) {
            return argument.clone();
        }
        // The declared signature's parameters now receive candidates that may
        // name a sibling type parameter of the same session (`U` names `T`
        // above); opt them into resolve-time substitution.
        for symbol in declared.type_parameters() {
            self.substitute_candidate_symbols.insert(*symbol);
        }
        let instantiated =
            InferredTypeArguments::new(arguments).instantiate_signature(self.table, argument);
        match self.table.get(instantiated).clone() {
            Type::Function(instantiated) => instantiated,
            _ => argument.clone(),
        }
    }

    /// Whether `type_id` mentions any of `symbols` as a [`Type::Named`]
    /// occurrence. Conservative: unenumerated composites report `false`.
    fn type_mentions_any(&self, type_id: TypeId, symbols: &[SymbolId]) -> bool {
        match self.table.get(type_id) {
            Type::Named(symbol) => symbols.contains(symbol),
            Type::Array(element) => self.type_mentions_any(*element, symbols),
            Type::Tuple(shape) => shape
                .all_element_types()
                .iter()
                .any(|&element| self.type_mentions_any(element, symbols)),
            Type::Union(members) => members
                .iter()
                .any(|&member| self.type_mentions_any(member, symbols)),
            Type::Function(signature) => {
                signature
                    .parameters()
                    .iter()
                    .any(|parameter| self.type_mentions_any(parameter.type_id(), symbols))
                    || self.type_mentions_any(signature.return_type(), symbols)
            }
            Type::AppliedClass { arguments, .. } => arguments
                .iter()
                .any(|&argument| self.type_mentions_any(argument, symbols)),
            _ => false,
        }
    }

    fn sync_iterator_yield(&mut self, method: TypeId) -> Option<TypeId> {
        let iterator = match self.table.get(method) {
            Type::Any | Type::Never | Type::Error => return Some(method),
            Type::Function(signature) => signature.return_type(),
            _ => return None,
        };
        let next = self.table.property_type(iterator, "next")?;
        let result = match self.table.get(next) {
            Type::Any | Type::Never | Type::Error => return Some(next),
            Type::Function(signature) => signature.return_type(),
            _ => return None,
        };
        self.iterator_result_yield(result)
    }

    fn iterator_result_yield(&mut self, result: TypeId) -> Option<TypeId> {
        match self.table.get(result).clone() {
            Type::Any | Type::Never | Type::Error => Some(result),
            Type::Union(members) => {
                let mut yields = Vec::with_capacity(members.len());
                for member in members {
                    yields.push(self.iterator_result_yield(member)?);
                }
                Some(self.table.union(&yields))
            }
            Type::ObjectType(object) => {
                let value = self.table.property_type(result, "value")?;
                let completes = object.properties.iter().any(|property| {
                    property.name() == "done"
                        && !property.optional()
                        && matches!(
                            self.table.get(property.type_id()),
                            Type::BooleanLiteral(true)
                        )
                });
                Some(if completes { self.table.never() } else { value })
            }
            _ => None,
        }
    }

    fn resolve_parameter(
        &mut self,
        parameter: &InferenceParameter,
        candidates: &[InferenceCandidate],
        earlier: &[InferredTypeArgument],
    ) -> (TypeId, InferenceProvenance, bool) {
        let Some((candidate, widen_literal_union)) = self.combine_candidates(candidates) else {
            return if let Some(default) = parameter.default() {
                (
                    self.substitute_earlier_arguments(default, earlier),
                    InferenceProvenance::Default,
                    false,
                )
            } else if let Some(constraint) = parameter.constraint() {
                (
                    self.substitute_earlier_arguments(constraint, earlier),
                    InferenceProvenance::Constraint,
                    false,
                )
            } else {
                (self.table.unknown(), InferenceProvenance::Unknown, false)
            };
        };
        if let Some(constraint) = parameter.constraint()
            && !TypeRelations::new(self.table).assignable(candidate, constraint)
        {
            return (
                self.substitute_earlier_arguments(constraint, earlier),
                InferenceProvenance::Constraint,
                false,
            );
        }
        let candidate = if self
            .substitute_candidate_symbols
            .contains(&parameter.symbol())
        {
            self.substitute_earlier_arguments(candidate, earlier)
        } else {
            candidate
        };
        (
            candidate,
            InferenceProvenance::Inferred,
            widen_literal_union,
        )
    }

    /// Substitutes the already resolved earlier type arguments through a
    /// fallback type. A default or constraint that names a parameter declared
    /// earlier (`<T = string, U = T>`) must store the resolved argument
    /// (`string`), not the bare occurrence — downstream instantiation only
    /// substitutes the parameter under check, so an unresolved occurrence
    /// would leak out of the call. Inferred and explicit results never route
    /// here: they carry their own evidence. Occurrences of parameters declared
    /// later pass through unchanged, preserving the existing forward-reference
    /// behavior.
    fn substitute_earlier_arguments(
        &mut self,
        fallback: TypeId,
        earlier: &[InferredTypeArgument],
    ) -> TypeId {
        if earlier.is_empty() {
            return fallback;
        }
        InferredTypeArguments::new(earlier.to_vec()).instantiate(self.table, fallback)
    }

    /// Combines the candidates of one parameter into a single type following
    /// the documented priority tiers. Returns `None` with no candidates.
    fn combine_candidates(&mut self, candidates: &[InferenceCandidate]) -> Option<(TypeId, bool)> {
        let best_priority = candidates
            .iter()
            .map(|candidate| candidate.priority)
            .max()?;
        // Naked and nested covariant evidence selects one common supertype.
        // Low-priority contravariant evidence stays in its own tier.
        let mut tier: Vec<&InferenceCandidate> = Vec::new();
        for candidate in candidates {
            let include = candidate.priority == best_priority
                || (best_priority == InferencePriority::Top
                    && candidate.priority == InferencePriority::Middle);
            if include
                && !tier
                    .iter()
                    .any(|existing| existing.type_id == candidate.type_id)
            {
                tier.push(candidate);
            }
        }
        let widen_literal_union = tier
            .iter()
            .any(|candidate| self.fresh_literal_sources.contains(&candidate.source));
        if tier.len() == 1 {
            return Some((tier[0].type_id, widen_literal_union));
        }
        let best = {
            let relations = TypeRelations::new(self.table);
            let type_ids: Vec<TypeId> = tier.iter().map(|candidate| candidate.type_id).collect();
            if best_priority == InferencePriority::Low {
                type_ids.iter().copied().find(|candidate| {
                    type_ids
                        .iter()
                        .all(|other| relations.subtype(*candidate, *other))
                })
            } else {
                type_ids.iter().copied().find(|candidate| {
                    type_ids
                        .iter()
                        .all(|other| relations.subtype(*other, *candidate))
                })
            }
        };
        match (best_priority, best) {
            (_, Some(best)) => Some((best, widen_literal_union)),
            // Contravariant candidates with no common subtype keep the first
            // candidate in encounter order; intersection types are not modeled.
            (InferencePriority::Low, None) => Some((tier[0].type_id, widen_literal_union)),
            // Covariant candidates from the same argument position must agree;
            // with no common supertype, keep the first candidate so the call
            // argument check reports the mismatch. Candidates from different
            // arguments are unioned.
            (_, None) => {
                if tier
                    .iter()
                    .all(|candidate| candidate.source == tier[0].source)
                {
                    Some((tier[0].type_id, widen_literal_union))
                } else {
                    Some((
                        self.table
                            .union(&tier.iter().map(|c| c.type_id).collect::<Vec<_>>()),
                        widen_literal_union,
                    ))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parameter(id: u32) -> SymbolId {
        SymbolId::new(id)
    }

    /// `identity<T>(value: T): T` with a concrete argument infers the argument
    /// type at top priority and instantiates the signature end to end.
    #[test]
    fn a_naked_parameter_infers_the_argument_type_at_top_priority() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let signature = table.function(vec![t], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[one]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(
            inferred.provenance(parameter(1)),
            Some(InferenceProvenance::Inferred)
        );
        // The contextual signature is (value: 1) => 1.
        let contextual = inferred.instantiate_signature(&mut table, &signature);
        assert_eq!(contextual, table.function(vec![one], one));
    }

    /// `first<T>(items: T[]): T` reaches the variable through an array element:
    /// a middle-priority candidate.
    #[test]
    fn a_nested_variable_infers_the_element_type() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let items = table.array(t);
        let signature = table.function(vec![items], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let strings = table.array(table.string());
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[strings]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(table.string()));
    }

    /// `map<T, U>(items: T[], f: (item: T) => U): U[]` exercises all three
    /// tiers at once: `T` wins on its top/middle candidates even though the
    /// callback parameter reaches it contravariantly, and `U` infers from the
    /// callback return.
    #[test]
    fn higher_order_inference_orders_priorities_and_types_the_callback_contextually() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let items = table.array(t);
        let callback = table.function(vec![t], u);
        let result = table.array(u);
        let signature = table.function(vec![items, callback], result);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let numbers = table.array(table.number());
        // The callback argument claims (item: string) => boolean: `T` sees a
        // contravariant `string` candidate and `U` sees `boolean`.
        let argument_callback = table.function(vec![table.string()], table.boolean());
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[numbers, argument_callback]);
        let inferred = context.resolve();

        // The array's middle-priority `number` beats the callback's
        // low-priority `string` for `T`; `U` infers `boolean` from the
        // covariant callback return.
        assert_eq!(inferred.get(parameter(1)), Some(table.number()));
        assert_eq!(inferred.get(parameter(2)), Some(table.boolean()));

        // Instantiating the signature yields the contextual signature used to
        // check the lambda: (items: number[], f: (item: number) => boolean).
        let contextual = inferred.instantiate_signature(&mut table, &signature);
        let expected_callback = table.function(vec![table.number()], table.boolean());
        let booleans = table.array(table.boolean());
        let expected = table.function(vec![numbers, expected_callback], booleans);
        assert_eq!(contextual, expected);
    }
    #[test]
    fn rest_parameter_with_unsupplied_fixed_params_does_not_panic() {
        // f<T>(a: number, ...rest: T[]) called as f() — the rest branch must not
        // slice arguments[1..] when arguments.len() == 0. With no candidates,
        // T remains unconstrained and resolves to `unknown`.
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let number = table.number();
        let rest_array = table.array(t);
        let a = FunctionParameter::new("a".to_owned(), number, false, false);
        let rest = FunctionParameter::new("rest".to_owned(), rest_array, false, true);
        let sig_type = table.function_with_parameters(vec![parameter(1)], vec![a, rest], t);
        let Type::Function(sig) = table.get(sig_type).clone() else {
            panic!("function type");
        };
        let mut ctx = InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        // No arguments supplied — fixed param and rest both unsupplied.
        ctx.infer_from_arguments(&sig, &[]);
        let inferred = ctx.resolve();
        // No panic, and T has no candidates so it falls back to `unknown`.
        assert_eq!(inferred.get(parameter(1)), Some(table.unknown()));
    }
    #[test]
    fn nested_generic_signature_is_preserved_through_instantiation() {
        // Outer: <T>(value: T): <U>(x: U) => T
        // Inner: <U>(x: U) => T  — inner <U> must survive instantiation of outer T.
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let inner = table.function_with_parameters(
            vec![parameter(2)],
            vec![FunctionParameter::new("x".to_owned(), u, false, false)],
            t,
        );
        let outer = table.function_with_parameters(
            vec![parameter(1)],
            vec![FunctionParameter::new("value".to_owned(), t, false, false)],
            inner,
        );
        let Type::Function(outer_sig) = table.get(outer).clone() else {
            panic!("function type");
        };
        let string = table.string();
        let mut ctx = InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        ctx.infer_from_arguments(&outer_sig, &[string]);
        let inferred = ctx.resolve();
        assert_eq!(inferred.get(parameter(1)), Some(string));
        // Instantiate the outer return type (the inner function) — T -> string, U preserved.
        let instantiated = inferred.instantiate(&mut table, inner);
        let expected = table.function_with_parameters(
            vec![parameter(2)],
            vec![FunctionParameter::new("x".to_owned(), u, false, false)],
            string,
        );
        assert_eq!(instantiated, expected);
    }

    /// Two distinct top-priority candidates with no common supertype resolve
    /// to their union.
    #[test]
    fn equal_top_candidates_combine_into_a_union() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let signature = table.function(vec![t, t], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let (one, two) = (table.number_literal("1"), table.number_literal("2"));
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[one, two]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(table.union(&[one, two])));
    }
    /// Two candidates for the same type parameter from the *same* argument
    /// position must agree; with no common supertype the first one wins.
    #[test]
    fn same_source_incomparable_candidates_pick_first() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let obj = table.object_type(vec![
            PropertyType::new("a", false, t),
            PropertyType::new("b", false, t),
        ]);
        let signature = table.function(vec![obj], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let two = table.number_literal("2");
        let arg = table.object_type(vec![
            PropertyType::new("a", false, one),
            PropertyType::new("b", false, two),
        ]);
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[arg]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(one));
    }

    /// A candidate that supertypes every sibling in its tier wins without a
    /// union, regardless of encounter order.
    #[test]
    fn the_best_common_supertype_wins_an_upper_tier() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let signature = table.function(vec![t, t], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let (number, one) = (table.number(), table.number_literal("1"));
        for arguments in [[one, number], [number, one]] {
            let mut context =
                InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
            context.infer_from_arguments(&signature, &arguments);
            assert_eq!(context.resolve().get(parameter(1)), Some(number));
        }
    }

    /// Contravariant candidates combine toward the best common subtype; with
    /// incomparable candidates the first in encounter order wins.
    #[test]
    fn the_best_common_subtype_wins_the_lower_tier_with_an_order_fallback() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        // `compose<T>(f: (value: T) => void, g: (value: T) => void): void`
        let callback = table.function(vec![t], table.void());
        let signature = table.function(vec![callback, callback], table.void());
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let (number, one, string) = (table.number(), table.number_literal("1"), table.string());
        let takes_number = table.function(vec![number], table.void());
        let takes_one = table.function(vec![one], table.void());
        let takes_string = table.function(vec![string], table.void());

        // 1 subtypes number, so the literal wins the lower tier.
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[takes_number, takes_one]);
        assert_eq!(context.resolve().get(parameter(1)), Some(one));

        // string and number are incomparable: encounter order decides.
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[takes_number, takes_string]);
        assert_eq!(context.resolve().get(parameter(1)), Some(number));
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_arguments(&signature, &[takes_string, takes_number]);
        assert_eq!(context.resolve().get(parameter(1)), Some(string));
    }

    /// With no candidates a parameter is fixed by its default, then its
    /// constraint, then `unknown`.
    #[test]
    fn an_unreached_parameter_falls_back_to_default_constraint_unknown() {
        let mut table = TypeTable::new();
        let (number, string, unknown) = (table.number(), table.string(), table.unknown());
        let t = table.named(parameter(1));
        assert_eq!(table.get(t), &Type::Named(parameter(1)));

        // No arguments are fed, so no parameter records a candidate.
        let context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)).with_default(string),
                InferenceParameter::new(parameter(2)).with_constraint(number),
                InferenceParameter::new(parameter(3)),
            ],
        );
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(string));
        assert_eq!(
            inferred.provenance(parameter(1)),
            Some(InferenceProvenance::Default)
        );
        assert_eq!(inferred.get(parameter(2)), Some(number));
        assert_eq!(
            inferred.provenance(parameter(2)),
            Some(InferenceProvenance::Constraint)
        );
        assert_eq!(inferred.get(parameter(3)), Some(unknown));
        assert_eq!(
            inferred.provenance(parameter(3)),
            Some(InferenceProvenance::Unknown)
        );
    }

    /// `pick<T = string, U = T, V = U>` with no arguments: every default
    /// references the parameter declared before it, so resolution walks the
    /// chain in declaration order and stores the concrete `string` for each
    /// parameter — not a bare occurrence of an earlier one.
    #[test]
    fn chained_defaults_resolve_through_earlier_parameters_in_declaration_order() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let string = table.string();
        let context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)).with_default(string),
                InferenceParameter::new(parameter(2)).with_default(t),
                InferenceParameter::new(parameter(3)).with_default(u),
            ],
        );
        let inferred = context.resolve();

        for id in [1, 2, 3] {
            assert_eq!(inferred.get(parameter(id)), Some(string));
            assert_eq!(
                inferred.provenance(parameter(id)),
                Some(InferenceProvenance::Default)
            );
        }
        // The contextual signature `(value: U) => U` instantiates end to end;
        // with a bare-occurrence fallback the parameter type would stay an
        // unresolved `T`.
        let signature = table.function(vec![u], u);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };
        let contextual = inferred.instantiate_signature(&mut table, &signature);
        assert_eq!(contextual, table.function(vec![string], string));
    }

    /// An argument violating a constraint that references an earlier
    /// parameter still falls back to the substituted constraint. The
    /// resolution is neither `unknown`, `any`, nor `error`, so the binder's
    /// assignability check — the one emitting the argument-not-assignable
    /// call diagnostic — still rejects the invalid key/value.
    #[test]
    fn an_invalid_argument_keeps_the_substituted_constraint_fallback() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let number = table.number();
        let constraint = table.object_type(vec![PropertyType::new("value", false, t)]);
        let signature = table.function(vec![u], u);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let string = table.string();
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)).with_default(number),
                InferenceParameter::new(parameter(2)).with_constraint(constraint),
            ],
        );
        context.infer_from_arguments(&signature, &[string]);
        let inferred = context.resolve();

        let expected = table.object_type(vec![PropertyType::new("value", false, number)]);
        let resolved = inferred.get(parameter(2)).expect("U resolves");
        assert_eq!(resolved, expected);
        assert_ne!(resolved, table.unknown());
        assert_ne!(resolved, table.any());
        assert_ne!(resolved, table.error_type());
        assert_eq!(
            inferred.provenance(parameter(2)),
            Some(InferenceProvenance::Constraint)
        );
        // The invalid key/value still fails the relation behind the call
        // diagnostic: `string` is not assignable to `{ value: number }`.
        assert!(!TypeRelations::new(&table).assignable(string, resolved));
    }

    /// An inferred candidate that violates the `extends` constraint is
    /// replaced by the constraint.
    #[test]
    fn a_candidate_failing_its_constraint_falls_back_to_the_constraint() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let number = table.number();
        let signature = table.function(vec![t], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let string = table.string();
        let mut context = InferenceContext::new(
            &mut table,
            &[InferenceParameter::new(parameter(1)).with_constraint(number)],
        );
        context.infer_from_arguments(&signature, &[string]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(number));
        assert_eq!(
            inferred.provenance(parameter(1)),
            Some(InferenceProvenance::Constraint)
        );
    }

    /// A candidate satisfying its constraint is kept.
    #[test]
    fn a_candidate_within_its_constraint_is_kept() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let number = table.number();
        let signature = table.function(vec![t], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let mut context = InferenceContext::new(
            &mut table,
            &[InferenceParameter::new(parameter(1)).with_constraint(number)],
        );
        context.infer_from_arguments(&signature, &[one]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(
            inferred.provenance(parameter(1)),
            Some(InferenceProvenance::Inferred)
        );
    }

    /// Object properties and union members of the declared parameter type all
    /// contribute candidates.
    #[test]
    fn object_properties_and_union_members_contribute_candidates() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let pair = table.object_type(vec![
            PropertyType::new("first", false, t),
            PropertyType::new("second", false, u),
        ]);
        let flexible = table.union(&[t, table.number()]);
        let signature = table.function(vec![pair, flexible], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let (string, boolean, number) = (table.string(), table.boolean(), table.number());
        let argument_pair = table.object_type(vec![
            PropertyType::new("first", false, string),
            PropertyType::new("second", false, boolean),
            PropertyType::new("extra", false, number),
        ]);
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[argument_pair, string]);
        let inferred = context.resolve();

        // `T` sees `string` from the property and from the union member;
        // deduplicated, one candidate remains. `U` sees only `boolean`.
        assert_eq!(inferred.get(parameter(1)), Some(table.string()));
        assert_eq!(inferred.get(parameter(2)), Some(table.boolean()));
    }

    /// Instantiation leaves types without inferred parameters untouched and
    /// substitutes through nested composites.
    #[test]
    fn instantiation_substitutes_only_inferred_parameters() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let other = table.named(parameter(9));
        let (items, name) = (table.array(t), table.string());
        let composite = table.object_type(vec![
            PropertyType::new("items", false, items),
            PropertyType::new("name", false, name),
            PropertyType::new("other", false, other),
        ]);

        let number = table.number();
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_argument(t, number, 0);
        let inferred = context.resolve();

        let instantiated = inferred.instantiate(&mut table, composite);
        let numbers = table.array(number);
        let expected = table.object_type(vec![
            PropertyType::new("items", false, numbers),
            PropertyType::new("name", false, name),
            PropertyType::new("other", false, other),
        ]);
        assert_eq!(instantiated, expected);
        // Primitives and unrelated named types intern back to themselves.
        let string = table.string();
        assert_eq!(inferred.instantiate(&mut table, string), string);
        assert_eq!(inferred.instantiate(&mut table, other), other);
    }

    /// Object-property metadata survives generic instantiation rather than
    /// silently degrading the structural contract.
    #[test]
    fn instantiation_preserves_object_property_flags() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let composite = table.object_type(vec![
            PropertyType::new("mutable", false, t),
            PropertyType::new("locked", false, t)
                .with_readonly(true)
                .with_spreadable(true),
        ]);

        let number = table.number();
        let mut context =
            InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
        context.infer_from_argument(t, number, 0);
        let inferred = context.resolve();
        let instantiated = inferred.instantiate(&mut table, composite);

        let Type::ObjectType(object) = table.get(instantiated).clone() else {
            panic!("object type");
        };
        let locked = object
            .properties
            .iter()
            .find(|property| property.name() == "locked")
            .expect("locked property");
        assert!(locked.readonly(), "readonly survives instantiation");
        assert!(locked.spreadable(), "spreadability survives instantiation");
        let mutable = object
            .properties
            .iter()
            .find(|property| property.name() == "mutable")
            .expect("mutable property");
        assert!(!mutable.readonly(), "non-readonly stays non-readonly");
        assert!(
            !mutable.spreadable(),
            "ordinary members stay non-spreadable"
        );
    }

    /// Resolution is deterministic: the same session built twice yields the
    /// same mapping.
    #[test]
    fn resolution_is_deterministic_across_identical_sessions() {
        let run = || {
            let mut table = TypeTable::new();
            let t = table.named(parameter(1));
            let items = table.array(t);
            let signature = table.function(vec![items, t], t);
            let Type::Function(signature) = table.get(signature).clone() else {
                panic!("function type");
            };
            let one = table.number_literal("1");
            let numbers = table.array(table.number());
            let mut context =
                InferenceContext::new(&mut table, &[InferenceParameter::new(parameter(1))]);
            context.infer_from_arguments(&signature, &[numbers, one]);
            let inferred = context.resolve();
            let resolved = inferred.get(parameter(1)).expect("resolved");
            table.get(resolved).clone()
        };
        let resolved = run();
        assert_eq!(resolved, Type::Number);
        assert_eq!(resolved, run());
    }
    /// A tuple-typed rest parameter infers each remaining argument against the
    /// corresponding tuple element, not as a single array rest.
    #[test]
    fn tuple_typed_rest_parameter_infers_each_position() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let rest_tuple = table.tuple(vec![t, u]);
        let rest = FunctionParameter::new("rest".to_owned(), rest_tuple, false, true);
        let signature =
            table.function_with_parameters(vec![parameter(1), parameter(2)], vec![rest], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let string = table.string();
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[one, string]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(inferred.get(parameter(2)), Some(string));
    }

    /// A tuple-typed rest parameter with an optional element skips the missing
    /// position and still infers the intended type when the element is supplied.
    #[test]
    fn tuple_typed_rest_parameter_with_optional_element() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let rest_tuple = table.tuple_shape(TupleShape {
            prefix: vec![t, u],
            required: 1,
            rest: None,
            suffix: Vec::new(),
        });
        let rest = FunctionParameter::new("rest".to_owned(), rest_tuple, false, true);
        let signature =
            table.function_with_parameters(vec![parameter(1), parameter(2)], vec![rest], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[one]);
        let inferred = context.resolve();
        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(inferred.get(parameter(2)), Some(table.unknown()));

        let string = table.string();
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[one, string]);
        let inferred = context.resolve();
        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(inferred.get(parameter(2)), Some(string));
    }

    /// A tuple-typed rest parameter with a tuple rest tail infers the leading
    /// positions distinctly and collects the remaining positions as the rest
    /// type argument.
    #[test]
    fn tuple_typed_rest_parameter_with_rest_tail() {
        let mut table = TypeTable::new();
        let t = table.named(parameter(1));
        let u = table.named(parameter(2));
        let rest_tuple = table.tuple_shape(TupleShape {
            prefix: vec![t],
            required: 1,
            rest: Some(u),
            suffix: Vec::new(),
        });
        let rest = FunctionParameter::new("rest".to_owned(), rest_tuple, false, true);
        let signature =
            table.function_with_parameters(vec![parameter(1), parameter(2)], vec![rest], t);
        let Type::Function(signature) = table.get(signature).clone() else {
            panic!("function type");
        };

        let one = table.number_literal("1");
        let string = table.string();
        let boolean = table.boolean();
        let mut context = InferenceContext::new(
            &mut table,
            &[
                InferenceParameter::new(parameter(1)),
                InferenceParameter::new(parameter(2)),
            ],
        );
        context.infer_from_arguments(&signature, &[one, string, boolean]);
        let inferred = context.resolve();

        assert_eq!(inferred.get(parameter(1)), Some(one));
        assert_eq!(
            inferred.get(parameter(2)),
            Some(table.union(&[string, boolean]))
        );
    }
}
