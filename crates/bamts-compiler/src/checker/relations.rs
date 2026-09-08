//! Type relations over the interned [`TypeTable`]: assignability, subtyping,
//! variance, and a bounded relation cache.
//!
//! The algebra is deliberately split into two modes:
//!
//! - [`TypeRelations::assignable`] is TypeScript compatibility: every
//!   intentional concession (the bidirectional `any` hatch, number-to-enum,
//!   explicit `undefined` for an optional property) is accepted and reported
//!   as a [`RelationHazard`] through [`TypeRelations::relation`].
//! - [`TypeRelations::subtype`] is structural subtyping: the concessions are
//!   rejected, while genuine subtyping rules (fewer parameters, `void` return
//!   absorption, literal widening) are retained. [`TypeRelations::supertype`]
//!   and [`TypeRelations::equivalent`] are derived from it.
//!
//! Recursive structural queries are memoized in a bounded cache and guarded by
//! the complete interned [`TypeId`] pair plus mode while in progress. Generic
//! applications with different arguments therefore remain distinct, while an
//! exact repeated pair is a sound coinductive recursion boundary.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use bamts_bytecode::MAX_BIGINT_BYTES;

use super::binder::{
    ConstraintTypeExpr, ConstructEntry, FunctionParameter, FunctionSignature,
    IndexedAccessConstraint, IteratorProperty, ObjectType, PropertyType, SymbolId, TupleShape,
    Type, TypeId, TypeTable,
};
use crate::literal::{MAX_BIGINT_CONVERSION_LIMB_OPS, canonical_bigint_text, number_value};
use crate::syntax::Accessibility;
/// Completed structural relations are memoized up to this bound; beyond it,
/// results stay deterministic because the algebra never depends on cache state.
const RELATION_CACHE_CAPACITY: usize = 4096;
const ERASURE_VARIANTS_PER_RELATION: usize = 8;

/// A compatibility decision plus the intentional TypeScript hazards that made
/// the conversion possible.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeRelation {
    compatible: bool,
    hazards: Box<[RelationHazard]>,
}

impl TypeRelation {
    #[must_use]
    pub const fn compatible(&self) -> bool {
        self.compatible
    }

    #[must_use]
    pub fn hazards(&self) -> &[RelationHazard] {
        &self.hazards
    }
}

/// A type-system concession retained for the semantic lint pass.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RelationHazard {
    ExplicitUndefinedForOptional,
    FewerCallbackParameters,
    ValueReturnedToVoid,
    NumericEnumNumber,
}

/// How a relation query treats TypeScript's intentional compatibility
/// concessions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Strictness {
    /// Full assignability: every documented concession is accepted.
    Assignable,
    /// Structural subtyping: the `any` escape hatch, number-to-enum, and
    /// explicit-`undefined`-for-optional concessions are rejected.
    Strict,
    /// Assignability with `strictNullChecks` enabled: `null` and `undefined`
    /// flow only to types that explicitly include them.
    StrictNull,
    /// Symmetric overlap used by TypeScript assertions. Union sources need one
    /// related constituent rather than every constituent.
    Comparable,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum PrimitiveDomain {
    Null,
    Undefined,
    Boolean,
    Number,
    BigInt,
    String,
    Symbol,
}

#[derive(Clone, Copy)]
enum ParameterVariance {
    Contravariant,
    Bivariant,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RelationKey {
    source: TypeId,
    target: TypeId,
    strictness: Strictness,
    context: usize,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RelationContext {
    parameter_aliases: Box<[(SymbolId, SymbolId)]>,
    alpha_aliases: usize,
    erasure_active: bool,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RelationEndpoint {
    Alias(SymbolId),
    Class(SymbolId),
    Type(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum TemplateHead {
    Class(SymbolId),
    Alias(SymbolId),
}

#[derive(Default)]
struct FreeSymbolSearch {
    types: HashSet<TypeId>,
    templates: HashSet<TemplateHead>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct AliasRelationKey {
    source: RelationEndpoint,
    target: RelationEndpoint,
    strictness: Strictness,
    context: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ErasureRequirement {
    symbol: SymbolId,
    erased: bool,
}

#[derive(Debug)]
struct DependencyFrame {
    assumptions: HashSet<RelationKey>,
    erasure_requirements: HashMap<SymbolId, bool>,
    erased_base: usize,
    approximate_alias: bool,
}

impl DependencyFrame {
    fn new(erased_base: usize) -> Self {
        Self {
            assumptions: HashSet::new(),
            erasure_requirements: HashMap::new(),
            erased_base,
            approximate_alias: false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CachedRelation {
    compatible: bool,
    assumptions: Box<[RelationKey]>,
    erasure_requirements: Box<[ErasureRequirement]>,
}

/// Relation queries over one interned [`TypeTable`].
///
/// Construct once per relation-heavy pass and reuse it so the memoized pairs
/// amortize across queries; the convenience delegates on [`TypeTable`] build a
/// short-lived instance per call.
pub struct TypeRelations<'table> {
    table: &'table TypeTable,
    cache: RefCell<HashMap<RelationKey, Vec<CachedRelation>>>,
    /// Pairs currently being compared, to break recursive structural types.
    visiting: RefCell<HashSet<RelationKey>>,
    /// Semantic alias pairs active on the current structural path.
    active_alias_relations: RefCell<HashSet<AliasRelationKey>>,
    /// Coinductive assumptions and erased-membership predicates consumed by
    /// each active relation frame.
    dependency_stack: RefCell<Vec<DependencyFrame>>,
    /// Interned identities for effective alias/erasure environments. Identity
    /// zero is the empty environment.
    contexts: RefCell<HashMap<RelationContext, usize>>,
    /// Proven capture reachability in immutable class and alias templates.
    template_capture_reachability: RefCell<HashMap<(TemplateHead, SymbolId), bool>>,
    /// Proven free-symbol reachability from concrete relation endpoints.
    free_symbol_reachability: RefCell<HashMap<(TypeId, SymbolId), bool>>,
    active_context: Cell<usize>,
    /// Type parameters paired positionally by the generic signatures currently
    /// being compared, so `<T>(x: T) => T` relates to `<U>(x: U) => U`.
    /// Non-empty only inside such a comparison.
    parameter_aliases: RefCell<Vec<(SymbolId, SymbolId)>>,
    /// Number of directed pairs introduced by each active signature frame.
    parameter_alias_frames: RefCell<Vec<usize>>,
    /// Signature type parameters erased to `any` for the comparable relation.
    erased_parameters: RefCell<Vec<SymbolId>>,
    /// Type parameters inferred from the non-generic signature during a
    /// generic-to-non-generic function comparison, mapped to their inferred
    /// concrete types. Non-empty only inside such a comparison.
    inferred_type_arguments: RefCell<HashMap<SymbolId, TypeId>>,
    /// All type-parameter symbols declared by the signatures currently being
    /// compared, so unconstrained parameters can be treated as `unknown`
    /// (their implicit constraint) without consulting the symbol table.
    known_type_parameters: RefCell<HashSet<SymbolId>>,
    /// Cooperative cancellation signal. `None` for the non-cancellable path.
    cancel: Option<bamts_cancel::CancellationToken>,
    #[cfg(test)]
    computed_relations: Cell<usize>,
}

impl<'table> TypeRelations<'table> {
    pub fn new(table: &'table TypeTable) -> Self {
        Self::new_with_cancel(table, None)
    }

    /// Constructs a relation engine that polls `cancel` on recursive
    /// backedges. Pass `None` for the non-cancellable path.
    #[must_use]
    pub fn new_with_cancel(
        table: &'table TypeTable,
        cancel: Option<bamts_cancel::CancellationToken>,
    ) -> Self {
        Self {
            table,
            cache: RefCell::new(HashMap::new()),
            visiting: RefCell::new(HashSet::new()),
            active_alias_relations: RefCell::new(HashSet::new()),
            dependency_stack: RefCell::new(Vec::new()),
            contexts: RefCell::new(HashMap::new()),
            template_capture_reachability: RefCell::new(HashMap::new()),
            free_symbol_reachability: RefCell::new(HashMap::new()),
            active_context: Cell::new(0),
            parameter_aliases: RefCell::new(Vec::new()),
            parameter_alias_frames: RefCell::new(Vec::new()),
            erased_parameters: RefCell::new(Vec::new()),
            inferred_type_arguments: RefCell::new(HashMap::new()),
            known_type_parameters: RefCell::new(HashSet::new()),
            cancel,
            #[cfg(test)]
            computed_relations: Cell::new(0),
        }
    }

    /// Number of memoized pairs, exposed for cache consumers and tests.
    #[must_use]
    pub fn cached_pairs(&self) -> usize {
        self.cache.borrow().len()
    }

    #[cfg(test)]
    fn computed_relations(&self) -> usize {
        self.computed_relations.get()
    }

    /// Returns whether a value of `source` may be assigned where `target` is
    /// expected, using structural rules over the modeled type space.
    #[must_use]
    pub fn assignable(&self, source: TypeId, target: TypeId) -> bool {
        self.relates(source, target, Strictness::Assignable)
    }

    /// Returns whether `source` may be assigned to `target` under
    /// `strictNullChecks`.
    #[must_use]
    pub fn assignable_with_strict_null(&self, source: TypeId, target: TypeId) -> bool {
        self.relates(source, target, Strictness::StrictNull)
    }

    /// Returns whether either direction has sufficient structural overlap for
    /// a TypeScript type assertion.
    #[must_use]
    pub fn comparable(&self, left: TypeId, right: TypeId) -> bool {
        self.relates(left, right, Strictness::Comparable)
            || self.relates(right, left, Strictness::Comparable)
    }

    /// Returns whether `source` is a structural subtype of `target`, without
    /// the assignability concessions.
    #[must_use]
    pub fn subtype(&self, source: TypeId, target: TypeId) -> bool {
        self.relates(source, target, Strictness::Strict)
    }

    /// Returns whether `source` is a structural supertype of `target`.
    #[must_use]
    pub fn supertype(&self, source: TypeId, target: TypeId) -> bool {
        self.subtype(target, source)
    }

    /// Returns whether the two types are mutually subtypes.
    #[must_use]
    pub fn equivalent(&self, left: TypeId, right: TypeId) -> bool {
        left == right || (self.subtype(left, right) && self.subtype(right, left))
    }

    /// Computes compatibility once while retaining every accepted unsound
    /// concession for rule consumers.
    #[must_use]
    pub fn relation(&self, source: TypeId, target: TypeId) -> TypeRelation {
        let compatible = self.assignable(source, target);
        if !compatible {
            return TypeRelation {
                compatible,
                hazards: Box::new([]),
            };
        }
        let (Some(source), Some(target)) = (
            self.relation_alias_view(source),
            self.relation_alias_view(target),
        ) else {
            return TypeRelation {
                compatible,
                hazards: Box::new([]),
            };
        };

        let mut hazards = Vec::new();
        if let (Type::Function(from), Type::Function(to)) =
            (self.table.get(source), self.table.get(target))
        {
            if from.parameters().len() < to.parameters().len() {
                hazards.push(RelationHazard::FewerCallbackParameters);
            }
            if matches!(self.table.get(to.return_type()), Type::Void)
                && !matches!(self.table.get(from.return_type()), Type::Void | Type::Never)
            {
                hazards.push(RelationHazard::ValueReturnedToVoid);
            }
        }
        if matches!(
            (self.table.get(source), self.table.get(target)),
            (Type::NumericEnum(_), Type::Number) | (Type::Number, Type::NumericEnum(_))
        ) {
            hazards.push(RelationHazard::NumericEnumNumber);
        }
        if let (Type::ObjectType(from), Type::ObjectType(to)) =
            (self.table.get(source), self.table.get(target))
        {
            for target_property in to.properties.iter().filter(|property| property.optional()) {
                let Some(source_property) = from
                    .properties
                    .iter()
                    .find(|property| property.name() == target_property.name())
                else {
                    continue;
                };
                if matches!(self.table.get(source_property.type_id()), Type::Undefined)
                    && !self.contains_undefined(target_property.type_id())
                {
                    hazards.push(RelationHazard::ExplicitUndefinedForOptional);
                    break;
                }
            }
        }
        TypeRelation {
            compatible,
            hazards: hazards.into_boxed_slice(),
        }
    }

    fn relates(&self, source: TypeId, target: TypeId, strictness: Strictness) -> bool {
        if source == target {
            return true;
        }
        // Poll the cancellation token on every recursive entry. A cancelled
        // relation short-circuits to `false`; the binder's next `check_cancel`
        // propagates the typed error and discards any spurious diagnostics.
        if let Some(token) = &self.cancel
            && token.is_cancelled()
        {
            return false;
        }
        let relation = RelationKey {
            source,
            target,
            strictness,
            context: self.active_context.get(),
        };
        let cacheable = self.is_structural(source) || self.is_structural(target);
        if cacheable {
            let cached = {
                let visiting = self.visiting.borrow();
                let erased = self.erased_parameters.borrow();
                self.cache.borrow().get(&relation).and_then(|entries| {
                    let mut matched: Option<&CachedRelation> = None;
                    let mut conflict = false;
                    for entry in entries.iter().filter(|entry| {
                        entry
                            .assumptions
                            .iter()
                            .all(|assumption| visiting.contains(assumption))
                            && entry.erasure_requirements.iter().all(|requirement| {
                                erased.contains(&requirement.symbol) == requirement.erased
                            })
                    }) {
                        if matched.is_some_and(|current| current.compatible != entry.compatible) {
                            conflict = true;
                            break;
                        }
                        matched.get_or_insert(entry);
                    }
                    debug_assert!(
                        !conflict,
                        "matching relation cache variants disagree on compatibility"
                    );
                    (!conflict).then(|| matched.cloned()).flatten()
                })
            };
            if let Some(cached) = cached {
                if let Some(parent) = self.dependency_stack.borrow_mut().last_mut() {
                    parent
                        .assumptions
                        .extend(cached.assumptions.iter().copied());
                    for requirement in cached.erasure_requirements.iter().copied() {
                        self.record_erasure_requirement(parent, requirement);
                    }
                }
                return cached.compatible;
            }
        }

        let is_root = self.visiting.borrow().is_empty();
        {
            let mut visiting = self.visiting.borrow_mut();
            if !visiting.insert(relation) {
                if let Some(parent) = self.dependency_stack.borrow_mut().last_mut() {
                    parent.assumptions.insert(relation);
                }
                return true;
            }
        }
        self.dependency_stack
            .borrow_mut()
            .push(DependencyFrame::new(self.erased_parameters.borrow().len()));

        // Applications relate through their substituted structural views.
        // The in-progress key above uses the applied TypeIds themselves, so a
        // recursive Box<1>/Box<number> comparison terminates without conflating
        // either application with a different argument pair.
        let source_class = matches!(self.table.get(source), Type::AppliedClass { .. });
        let target_class = matches!(self.table.get(target), Type::AppliedClass { .. });
        let source_alias = matches!(self.table.get(source), Type::AppliedAlias { .. });
        let target_alias = matches!(self.table.get(target), Type::AppliedAlias { .. });
        let source_applied = source_class || source_alias;
        let target_applied = target_class || target_alias;
        let identical_application = matches!(
            (self.table.get(source), self.table.get(target)),
            (
                Type::AppliedClass {
                    symbol: source_symbol,
                    arguments: source_arguments,
                },
                Type::AppliedClass {
                    symbol: target_symbol,
                    arguments: target_arguments,
                },
            ) if source_symbol == target_symbol && source_arguments == target_arguments
        );
        let alias_relation = (source_applied || target_applied).then(|| AliasRelationKey {
            source: match self.table.get(source) {
                Type::AppliedAlias { symbol, .. } => RelationEndpoint::Alias(*symbol),
                Type::AppliedClass { symbol, .. } => RelationEndpoint::Class(*symbol),
                _ => RelationEndpoint::Type(source),
            },
            target: match self.table.get(target) {
                Type::AppliedAlias { symbol, .. } => RelationEndpoint::Alias(*symbol),
                Type::AppliedClass { symbol, .. } => RelationEndpoint::Class(*symbol),
                _ => RelationEndpoint::Type(target),
            },
            strictness,
            context: self.alias_relation_context(source, target),
        });
        let alias_relation_inserted =
            alias_relation.is_none_or(|key| self.active_alias_relations.borrow_mut().insert(key));
        if !alias_relation_inserted {
            self.dependency_stack
                .borrow_mut()
                .last_mut()
                .expect("active relation owns a dependency frame")
                .approximate_alias = true;
        }
        let result = if !alias_relation_inserted || identical_application {
            true
        } else if source_applied || target_applied {
            let source_view = if source_class {
                self.table.applied_class_view(source)
            } else if source_alias {
                self.relation_alias_view(source)
            } else {
                None
            };
            let target_view = if target_class {
                self.table.applied_class_view(target)
            } else if target_alias {
                self.relation_alias_view(target)
            } else {
                None
            };
            if (source_alias && source_view.is_none()) || (target_alias && target_view.is_none()) {
                false
            } else if source_view.is_some() || target_view.is_some() {
                self.relates(
                    source_view.unwrap_or(source),
                    target_view.unwrap_or(target),
                    strictness,
                )
            } else {
                self.relates_uncached(source, target, strictness)
            }
        } else {
            self.relates_uncached(source, target, strictness)
        };
        if alias_relation_inserted && let Some(key) = alias_relation {
            self.active_alias_relations.borrow_mut().remove(&key);
        }

        let mut frame = self
            .dependency_stack
            .borrow_mut()
            .pop()
            .expect("active relation owns a dependency frame");
        self.visiting.borrow_mut().remove(&relation);
        if is_root {
            frame.assumptions.clear();
        } else if let Some(parent) = self.dependency_stack.borrow_mut().last_mut() {
            parent.assumptions.extend(frame.assumptions.iter().copied());
            parent.approximate_alias |= frame.approximate_alias;
            for (&symbol, &erased) in &frame.erasure_requirements {
                self.record_erasure_requirement(parent, ErasureRequirement { symbol, erased });
            }
        }
        if cacheable && !frame.approximate_alias && (result || frame.assumptions.is_empty()) {
            let mut assumptions: Vec<_> = frame.assumptions.into_iter().collect();
            assumptions.sort_unstable();
            let mut erasure_requirements: Vec<_> = frame
                .erasure_requirements
                .into_iter()
                .map(|(symbol, erased)| ErasureRequirement { symbol, erased })
                .collect();
            erasure_requirements.sort_unstable();
            let cached = CachedRelation {
                compatible: result,
                assumptions: assumptions.into_boxed_slice(),
                erasure_requirements: erasure_requirements.into_boxed_slice(),
            };
            let mut cache = self.cache.borrow_mut();
            if cache.len() < RELATION_CACHE_CAPACITY || cache.contains_key(&relation) {
                let entries = cache.entry(relation).or_default();
                let dominates = |left: &CachedRelation, right: &CachedRelation| {
                    left.compatible == right.compatible
                        && left
                            .assumptions
                            .iter()
                            .all(|assumption| right.assumptions.binary_search(assumption).is_ok())
                        && left.erasure_requirements.iter().all(|requirement| {
                            right
                                .erasure_requirements
                                .binary_search(requirement)
                                .is_ok()
                        })
                };
                if !entries.iter().any(|entry| dominates(entry, &cached)) {
                    entries.retain(|entry| !dominates(&cached, entry));
                    if entries.len() < ERASURE_VARIANTS_PER_RELATION {
                        entries.push(cached);
                    }
                }
            }
        }
        result
    }

    fn intern_context(
        &self,
        mut parameter_aliases: Vec<(SymbolId, SymbolId)>,
        alpha_aliases: usize,
        erasure_active: bool,
    ) -> usize {
        parameter_aliases.sort_unstable();
        parameter_aliases.dedup();
        if parameter_aliases.is_empty() && alpha_aliases == 0 && !erasure_active {
            return 0;
        }

        let context = RelationContext {
            parameter_aliases: parameter_aliases.into_boxed_slice(),
            alpha_aliases,
            erasure_active,
        };
        let mut contexts = self.contexts.borrow_mut();
        let next = contexts.len() + 1;
        *contexts.entry(context).or_insert(next)
    }

    fn refresh_context(&self) {
        let parameter_aliases = self.parameter_aliases.borrow().clone();
        let erasure_active = !self.erased_parameters.borrow().is_empty();
        self.active_context
            .set(self.intern_context(parameter_aliases, 0, erasure_active));
    }

    fn alias_relation_context(&self, source: TypeId, target: TypeId) -> usize {
        let current_frame = self
            .parameter_alias_frames
            .borrow()
            .last()
            .copied()
            .unwrap_or(0);
        debug_assert_eq!(current_frame % 2, 0);
        let alpha_aliases = current_frame / 2;
        let mut aliases = {
            let aliases = self.parameter_aliases.borrow();
            debug_assert!(current_frame <= aliases.len());
            aliases[..aliases.len() - current_frame].to_vec()
        };
        aliases.sort_unstable();
        aliases.dedup();
        let erasure_active = !self.erased_parameters.borrow().is_empty();
        if aliases.is_empty() {
            return self.intern_context(Vec::new(), alpha_aliases, erasure_active);
        }
        let mut projected = Vec::with_capacity(aliases.len());

        for alias in aliases {
            let forward = Self::both_reachable(
                self.reaches_free_symbol(source, alias.0),
                self.reaches_free_symbol(target, alias.1),
            );
            let reverse = Self::both_reachable(
                self.reaches_free_symbol(source, alias.1),
                self.reaches_free_symbol(target, alias.0),
            );
            if forward == Some(true) || reverse == Some(true) {
                projected.push(alias);
            } else if forward.is_none() || reverse.is_none() {
                return self.active_context.get();
            }
        }

        self.intern_context(projected, alpha_aliases, erasure_active)
    }

    fn both_reachable(left: Option<bool>, right: Option<bool>) -> Option<bool> {
        match (left, right) {
            (Some(true), Some(true)) => Some(true),
            (Some(false), _) | (_, Some(false)) => Some(false),
            _ => None,
        }
    }

    fn reaches_free_symbol(&self, type_id: TypeId, symbol: SymbolId) -> Option<bool> {
        if let Some(found) = self
            .free_symbol_reachability
            .borrow()
            .get(&(type_id, symbol))
            .copied()
        {
            return Some(found);
        }

        let mut search = FreeSymbolSearch::default();
        let found = self.type_reaches_free_symbol(type_id, symbol, &mut search);
        if let Some(found) = found {
            self.free_symbol_reachability
                .borrow_mut()
                .insert((type_id, symbol), found);
        }
        found
    }

    fn type_reaches_free_symbol(
        &self,
        type_id: TypeId,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        if !search.types.insert(type_id) {
            return Some(false);
        }

        match self.table.get(type_id) {
            Type::Array(element) | Type::Keyof(element) => {
                self.type_reaches_free_symbol(*element, symbol, search)
            }
            Type::Tuple(shape) => self.any_types_reach_free_symbol(
                shape
                    .prefix
                    .iter()
                    .copied()
                    .chain(shape.rest)
                    .chain(shape.suffix.iter().copied()),
                symbol,
                search,
            ),
            Type::Union(members) | Type::Intersection(members) => {
                self.any_types_reach_free_symbol(members.iter().copied(), symbol, search)
            }
            Type::ObjectType(object) => self.object_reaches_free_symbol(object, symbol, search),
            Type::Function(signature) => {
                self.signature_reaches_free_symbol(signature, symbol, search)
            }
            Type::Named(named) => {
                if *named == symbol {
                    return Some(true);
                }
                self.any_types_reach_free_symbol(
                    [
                        self.table.type_parameter_constraint(*named),
                        self.table.interface_structure(*named),
                    ]
                    .into_iter()
                    .flatten(),
                    symbol,
                    search,
                )
            }
            Type::AppliedClass {
                symbol: head,
                arguments,
            } => {
                let arguments_reach =
                    self.any_types_reach_free_symbol(arguments.iter().copied(), symbol, search);
                if arguments_reach == Some(true) {
                    return Some(true);
                }
                Self::combine_reachability(
                    arguments_reach,
                    self.template_reaches_free_symbol(TemplateHead::Class(*head), symbol, search),
                )
            }
            Type::AppliedAlias {
                symbol: head,
                arguments,
            } => {
                let arguments_reach =
                    self.any_types_reach_free_symbol(arguments.iter().copied(), symbol, search);
                if arguments_reach == Some(true) {
                    return Some(true);
                }
                Self::combine_reachability(
                    arguments_reach,
                    self.template_reaches_free_symbol(TemplateHead::Alias(*head), symbol, search),
                )
            }
            Type::IndexedAccess { object, index } => {
                self.any_types_reach_free_symbol([*object, *index], symbol, search)
            }
            Type::Record { key, value } => {
                self.any_types_reach_free_symbol([*key, *value], symbol, search)
            }
            Type::This { constraint, .. } => {
                self.type_reaches_free_symbol(*constraint, symbol, search)
            }
            Type::ConstructorType {
                arguments,
                structural,
                ..
            } => {
                let arguments_reach =
                    self.any_types_reach_free_symbol(arguments.iter().copied(), symbol, search);
                if arguments_reach == Some(true) {
                    return Some(true);
                }
                let structural_reach = self.type_reaches_free_symbol(*structural, symbol, search);
                Self::combine_reachability(arguments_reach, structural_reach)
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
            | Type::EnumMember { .. } => Some(false),
        }
    }

    fn template_reaches_free_symbol(
        &self,
        head: TemplateHead,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        if !search.templates.is_empty() {
            return self.template_reaches_free_symbol_inner(head, symbol, search);
        }
        if let Some(found) = self
            .template_capture_reachability
            .borrow()
            .get(&(head, symbol))
            .copied()
        {
            return Some(found);
        }

        let mut template_search = FreeSymbolSearch::default();
        let found = self.template_reaches_free_symbol_inner(head, symbol, &mut template_search);
        if let Some(found) = found {
            self.template_capture_reachability
                .borrow_mut()
                .insert((head, symbol), found);
        }
        found
    }

    fn template_reaches_free_symbol_inner(
        &self,
        head: TemplateHead,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        if !search.templates.insert(head) {
            return Some(false);
        }

        let (parameters, raw) = match head {
            TemplateHead::Class(head) => (
                self.table.class_type_parameters(head),
                self.table.class_template_raw(head),
            ),
            TemplateHead::Alias(head) => (
                self.table.alias_type_parameters(head),
                self.table.alias_template_raw(head),
            ),
        };
        let found = if parameters.contains(&symbol) {
            Some(false)
        } else {
            raw.and_then(|raw| self.type_reaches_free_symbol(raw, symbol, search))
        };
        search.templates.remove(&head);
        found
    }

    fn object_reaches_free_symbol(
        &self,
        object: &ObjectType,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        let mut complete = true;
        for property in &object.properties {
            if Self::found_or_mark_incomplete(
                self.type_reaches_free_symbol(property.type_id(), symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        for signature in &object.call_signatures {
            if Self::found_or_mark_incomplete(
                self.signature_reaches_free_symbol(signature, symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        for entry in &object.construct_signatures {
            if Self::found_or_mark_incomplete(
                self.signature_reaches_free_symbol(&entry.signature, symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        for signature in &object.index_signatures {
            for parameter in &signature.parameters {
                if Self::found_or_mark_incomplete(
                    self.type_reaches_free_symbol(parameter.type_id(), symbol, search),
                    &mut complete,
                ) {
                    return Some(true);
                }
            }
            if Self::found_or_mark_incomplete(
                self.type_reaches_free_symbol(signature.value_type, symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        for type_id in [
            object.generator_return,
            object
                .iterator_property
                .as_ref()
                .map(|property| property.type_id()),
            object
                .async_iterator_property
                .as_ref()
                .map(|property| property.type_id()),
        ]
        .into_iter()
        .flatten()
        {
            if Self::found_or_mark_incomplete(
                self.type_reaches_free_symbol(type_id, symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        complete.then_some(false)
    }

    fn signature_reaches_free_symbol(
        &self,
        signature: &FunctionSignature,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        if signature.type_parameters().contains(&symbol) {
            return Some(false);
        }

        let bounds = signature
            .type_parameter_bounds()
            .iter()
            .flat_map(|bound| [bound.constraint(), bound.default()].into_iter().flatten());
        let parameters = signature
            .parameters()
            .iter()
            .map(FunctionParameter::type_id);
        self.any_types_reach_free_symbol(
            bounds
                .chain(parameters)
                .chain(std::iter::once(signature.return_type())),
            symbol,
            search,
        )
    }

    fn any_types_reach_free_symbol(
        &self,
        types: impl IntoIterator<Item = TypeId>,
        symbol: SymbolId,
        search: &mut FreeSymbolSearch,
    ) -> Option<bool> {
        let mut complete = true;
        for type_id in types {
            if Self::found_or_mark_incomplete(
                self.type_reaches_free_symbol(type_id, symbol, search),
                &mut complete,
            ) {
                return Some(true);
            }
        }
        complete.then_some(false)
    }

    fn found_or_mark_incomplete(found: Option<bool>, complete: &mut bool) -> bool {
        match found {
            Some(found) => found,
            None => {
                *complete = false;
                false
            }
        }
    }

    fn combine_reachability(left: Option<bool>, right: Option<bool>) -> Option<bool> {
        match (left, right) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        }
    }

    fn relates_uncached(&self, source: TypeId, target: TypeId, strictness: Strictness) -> bool {
        #[cfg(test)]
        self.computed_relations
            .set(self.computed_relations.get() + 1);
        let (from, to) = (self.table.get(source), self.table.get(target));
        match (from, to) {
            (Type::Error, _) | (_, Type::Error) => true,
            // `any` is the deliberate escape hatch in both directions for
            // assignability and for strict-null assignability; it is not a
            // subtype of anything.
            (Type::Any, _) | (_, Type::Any) => {
                matches!(
                    strictness,
                    Strictness::Assignable | Strictness::StrictNull | Strictness::Comparable
                )
            }
            (
                Type::This {
                    owner: source_owner,
                    constraint: source_constraint,
                },
                Type::This {
                    owner: target_owner,
                    constraint: target_constraint,
                },
            ) => {
                source_owner == target_owner
                    && self.relates(*source_constraint, *target_constraint, strictness)
            }
            (Type::This { constraint, .. }, _) => self.relates(*constraint, target, strictness),
            (Type::Never, Type::This { .. }) => true,
            (_, Type::This { .. }) => false,
            // Inferred type argument: a generic signature's type parameter
            // that was positionally inferred from the non-generic counterpart.
            // Substitute the inferred concrete type and continue.
            (Type::Named(symbol), _)
                if let Some(&inferred) = self.inferred_type_arguments.borrow().get(symbol) =>
            {
                inferred != source && self.relates(inferred, target, strictness)
            }
            (_, Type::Named(symbol))
                if let Some(&inferred) = self.inferred_type_arguments.borrow().get(symbol) =>
            {
                inferred != target && self.relates(source, inferred, strictness)
            }
            // Generic signatures compare their type parameters by position.
            // Resolve that temporary identity before consulting constraints;
            // otherwise two renamed constrained parameters decay to their
            // bounds and can never match each other.
            (Type::Named(source_symbol), Type::Named(target_symbol))
                if self
                    .parameter_aliases
                    .borrow()
                    .contains(&(*source_symbol, *target_symbol)) =>
            {
                true
            }
            // A known type parameter without a declared constraint has an
            // implicit constraint of `unknown`: everything flows in, nothing
            // flows out — exactly the `unknown` arms below.
            (Type::Named(symbol), _)
                if self.known_type_parameters.borrow().contains(symbol)
                    && self.table.type_parameter_constraint(*symbol).is_none() =>
            {
                false
            }
            (_, Type::Named(symbol))
                if self.known_type_parameters.borrow().contains(symbol)
                    && self.table.type_parameter_constraint(*symbol).is_none() =>
            {
                true
            }
            (Type::Named(symbol), _)
                if strictness == Strictness::Comparable && self.is_erased_parameter(*symbol) =>
            {
                true
            }
            (_, Type::Named(symbol))
                if strictness == Strictness::Comparable && self.is_erased_parameter(*symbol) =>
            {
                true
            }
            // An unresolved constraint is already represented by `Error`.
            // Preserve that recovery boundary in both directions so one
            // unsupported generic does not emit unrelated compatibility errors.
            (_, Type::Named(symbol))
                if self
                    .table
                    .type_parameter_constraint(*symbol)
                    .is_some_and(|constraint| {
                        matches!(self.table.get(constraint), Type::Error)
                    }) =>
            {
                true
            }
            (_, Type::Named(symbol))
                if matches!(strictness, Strictness::Assignable | Strictness::StrictNull)
                    && self.table.type_parameter_constraint(*symbol).is_some() =>
            {
                let constraint = self
                    .table
                    .type_parameter_constraint(*symbol)
                    .expect("guard checked constraint");
                constraint != target && self.relates(source, constraint, strictness)
            }
            // `unknown` is the top type: everything flows in, nothing flows out.
            (_, Type::Unknown) => true,
            (Type::Unknown, _) => false,
            // A value whose type is a type parameter carries at least its
            // declared constraint. Class and interface names are absent from
            // this table and keep their nominal handling below.
            (Type::Named(symbol), _) if self.table.type_parameter_constraint(*symbol).is_some() => {
                let constraint = self
                    .table
                    .type_parameter_constraint(*symbol)
                    .expect("guard checked constraint");
                constraint != source && self.relates(constraint, target, strictness)
            }
            // A deferred indexed access carries relation evidence from its type-parameter
            // constraints. Keep the indexed-access identity intact: deriving this view
            // must not mutate the interned table or erase generic correlations.
            (Type::IndexedAccess { .. }, _) => {
                match self.table.indexed_access_constraint_view(source) {
                    IndexedAccessConstraint::Reduced(expression) => {
                        self.constraint_source_relates(&expression, target, strictness)
                    }
                    IndexedAccessConstraint::Invalid => false,
                }
            }
            (
                Type::Record {
                    key: source_key,
                    value: source_value,
                },
                Type::Record {
                    key: target_key,
                    value: target_value,
                },
            ) => {
                self.relates(*target_key, *source_key, strictness)
                    && self.relates(*source_value, *target_value, strictness)
            }
            (
                Type::ObjectType(source_object),
                Type::Record {
                    key: target_key,
                    value: target_value,
                },
            ) => {
                self.object_satisfies_record(source_object, *target_key, *target_value, strictness)
            }
            (Type::Record { .. }, Type::Object) => true,
            (Type::Never, Type::Record { .. }) => true,
            (Type::Record { .. }, _) | (_, Type::Record { .. }) => false,
            // An interface with a completed structural body expands through that body
            // once. The `visiting` set in `relates` terminates recursive self and mutual
            // interface pairs; returned member types that are the interface's own head stay inert.
            (Type::Named(source_symbol), _)
                if self.table.interface_structure(*source_symbol).is_some() =>
            {
                let view = self.table.named_structural_view(source);
                self.relates(view, target, strictness)
            }
            (_, Type::Named(target_symbol))
                if self.table.interface_structure(*target_symbol).is_some() =>
            {
                let view = self.table.named_structural_view(target);
                self.relates(source, view, strictness)
            }
            // `never` is the bottom type: it flows into everything, nothing else
            // flows into it (identity already handled above).
            (Type::Never, _) => true,
            (_, Type::Never) => false,
            (_, Type::Intersection(targets)) => targets
                .iter()
                .all(|member| self.relates(source, *member, strictness)),
            (Type::Intersection(sources), Type::ObjectType(target)) => {
                self.intersection_object_relates(sources, target, strictness)
            }
            (Type::Intersection(sources), _) => sources
                .iter()
                .any(|member| self.relates(*member, target, strictness)),
            (Type::StringLiteral(_), Type::String) => true,
            (Type::NumberLiteral(_), Type::Number) => true,
            (Type::BooleanLiteral(_), Type::Boolean) => true,
            (Type::BigIntLiteral(_), Type::BigInt) => true,
            // Enum member types are genuine subtypes of `number`; the reverse
            // direction is an assignability concession in both assignable modes.
            (Type::NumericEnum(_), Type::Number) => true,
            (Type::Number, Type::NumericEnum(_)) => {
                matches!(
                    strictness,
                    Strictness::Assignable | Strictness::StrictNull | Strictness::Comparable
                )
            }
            // A numeric enum member literal is a subtype of `number` and of
            // its enum type, exactly like `NumericEnum` itself.
            (
                Type::EnumMember {
                    string_value: None, ..
                },
                Type::Number,
            ) => true,
            (
                Type::Number,
                Type::EnumMember {
                    string_value: None, ..
                },
            ) => {
                matches!(
                    strictness,
                    Strictness::Assignable | Strictness::StrictNull | Strictness::Comparable
                )
            }
            // A string enum member literal is a subtype of `string`, like a
            // string literal.
            (
                Type::EnumMember {
                    string_value: Some(_),
                    ..
                },
                Type::String,
            ) => true,
            // An enum member literal is assignable to its own enum type.
            (Type::EnumMember { enum_symbol, .. }, Type::NumericEnum(target_symbol))
                if enum_symbol == target_symbol =>
            {
                true
            }
            (
                Type::EnumMember {
                    enum_symbol,
                    string_value: Some(_),
                    ..
                },
                Type::Named(target_symbol),
            ) if enum_symbol == target_symbol => true,
            // A string enum member with a specific value is assignable to the
            // matching string literal type.
            (
                Type::EnumMember {
                    string_value: Some(value),
                    ..
                },
                Type::StringLiteral(target_value),
            ) if value == target_value => true,
            // Null/undefined are assignable to any type in non-strict mode,
            // but not to `never`. Under strict null checks they only flow to
            // types that explicitly include them.
            (Type::Null | Type::Undefined, _) if strictness == Strictness::Assignable => {
                !matches!(to, Type::Never)
            }
            (Type::Union(sources), _) => {
                if strictness == Strictness::Comparable {
                    sources
                        .iter()
                        .any(|member| self.relates(*member, target, strictness))
                } else {
                    sources
                        .iter()
                        .all(|member| self.relates(*member, target, strictness))
                }
            }
            (_, Type::Union(targets)) => targets
                .iter()
                .any(|member| self.relates(source, *member, strictness)),
            (Type::Undefined, _) if strictness == Strictness::StrictNull => {
                matches!(to, Type::Any | Type::Unknown | Type::Void | Type::Undefined)
            }
            (Type::Null, _) if strictness == Strictness::StrictNull => {
                matches!(to, Type::Any | Type::Unknown | Type::Null)
            }
            // Array elements are covariant, matching TypeScript's accepted
            // unsoundness for mutable arrays.
            (Type::Array(source_element), Type::Array(target_element)) => {
                self.relates(*source_element, *target_element, strictness)
            }
            (Type::Tuple(source_shape), Type::Tuple(target_shape)) => {
                self.tuple_relates(source_shape, target_shape, strictness)
            }
            (Type::Tuple(source_shape), Type::Array(target_element)) => source_shape
                .all_element_types()
                .iter()
                .all(|&source| self.relates(source, *target_element, strictness)),
            (Type::Array(_), Type::Tuple(_)) => false,
            (Type::Array(_) | Type::Tuple(_), Type::ObjectType(target_object)) => {
                if target_object.iterator_property.is_some()
                    && target_object.index_signatures.is_empty()
                {
                    self.table
                        .iterable_view(source)
                        .is_some_and(|view| self.relates(view, target, strictness))
                } else {
                    self.array_relates_to_index_object(source, target_object, strictness)
                }
            }
            (Type::ObjectType(source), Type::ObjectType(target)) => {
                self.object_relates(source, target, strictness)
            }
            (Type::Function(source_sig), Type::Function(target_sig)) => {
                self.function_relates(source_sig, target_sig, strictness)
            }
            // A function is assignable to an object type with call signatures
            // when the object type has no required members beyond those
            // signatures and the function satisfies at least one call signature.
            (Type::Function(source_sig), Type::ObjectType(target_object)) => {
                target_object.properties.iter().all(|p| p.optional())
                    && target_object.construct_signatures.is_empty()
                    && target_object.index_signatures.is_empty()
                    && target_object.iterator_property.is_none()
                    && target_object.async_iterator_property.is_none()
                    && target_object.generator_return.is_none()
                    && self.signature_sets_relate(
                        std::slice::from_ref(source_sig),
                        &target_object.call_signatures,
                        strictness,
                    )
            }
            // An object type with call signatures is assignable to a function
            // when at least one call signature satisfies the target function.
            (Type::ObjectType(source_object), Type::Function(target_sig)) => self
                .signature_sets_relate(
                    &source_object.call_signatures,
                    std::slice::from_ref(target_sig),
                    strictness,
                ),
            // `object` is the non-primitive type: object literals, arrays,
            // functions, and class instances all flow into it.
            (
                Type::ObjectType(_)
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::Function(_)
                | Type::Named(_)
                | Type::AppliedClass { .. },
                Type::Object,
            ) => true,
            // `Object` (capital O, the boxed object type) is the top object
            // type that includes primitives: number, string, boolean, etc.
            // are assignable to `Object`, and `Object` is assignable to `object`
            // when the target is `Object` (any) or `object` with optional props.
            (
                Type::Number
                | Type::String
                | Type::Boolean
                | Type::BigInt
                | Type::Symbol
                | Type::NumberLiteral(_)
                | Type::StringLiteral(_)
                | Type::BooleanLiteral(_)
                | Type::BigIntLiteral(_)
                | Type::NumericEnum(_)
                | Type::EnumMember { .. }
                | Type::AppliedClass { .. },
                Type::Named(symbol),
            ) if self.is_object_symbol(*symbol) => true,
            // `object` can be assigned to an empty or all-optional object type,
            // but not to a type that requires specific properties.
            (Type::Object, Type::ObjectType(target)) => {
                target.properties.iter().all(|property| property.optional())
            }
            (Type::ConstructorType { structural, .. }, _) => {
                self.relates(*structural, target, strictness)
            }
            (_, Type::ConstructorType { structural, .. }) => {
                self.relates(source, *structural, strictness)
            }
            (
                Type::Void
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
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::ObjectType(_)
                | Type::Function(_)
                | Type::Named(_)
                | Type::AppliedClass { .. }
                | Type::AppliedAlias { .. }
                | Type::NumericEnum(_)
                | Type::EnumMember { .. }
                | Type::Keyof(_),
                _,
            ) => false,
        }
    }
    fn is_object_symbol(&self, symbol: SymbolId) -> bool {
        self.table.is_object_symbol(symbol)
    }

    /// Pairs the type parameters of two generic signatures for the duration of
    /// `compare`. Pairing is positional, and only applies when both signatures
    /// declare the same number of parameters; otherwise they are compared as-is.
    fn with_parameter_aliases(
        &self,
        source: &FunctionSignature,
        target: &FunctionSignature,
        strictness: Strictness,
        variance: ParameterVariance,
        compare: impl FnOnce() -> bool,
    ) -> bool {
        if strictness == Strictness::Comparable {
            return self.with_erased_parameters(source, target, compare);
        }
        let (source_parameters, target_parameters) =
            (source.type_parameters(), target.type_parameters());
        if source_parameters.is_empty() && target_parameters.is_empty() {
            return compare();
        }
        // When one side is generic and the other is not, TypeScript
        // instantiates the generic side. For assignability we approximate
        // this with positional inference from the non-generic side's
        // parameter types, falling back to the constraint (or `unknown` for
        // unconstrained parameters) for type parameters that cannot be
        // inferred. Strict subtype keeps the nominal comparison.
        if source_parameters.len() != target_parameters.len() {
            if matches!(strictness, Strictness::Assignable | Strictness::StrictNull) {
                return self.with_inferred_parameters(
                    source,
                    target,
                    source_parameters,
                    target_parameters,
                    compare,
                );
            }
            return compare();
        }
        let same_declaration = source_parameters == target_parameters;
        // Renaming is symmetric. A method instantiated from one declaration
        // may compare the outer substitutions in either direction. Distinct
        // generic declarations still require target-domain coverage.
        let added = source_parameters.len() * 2;
        let previous_context = self.active_context.get();
        let mut aliases = self.parameter_aliases.borrow_mut();
        for (&source_parameter, &target_parameter) in
            source_parameters.iter().zip(target_parameters.iter())
        {
            aliases.push((source_parameter, target_parameter));
            aliases.push((target_parameter, source_parameter));
        }
        drop(aliases);
        self.parameter_alias_frames.borrow_mut().push(added);
        self.refresh_context();
        let constraints_relate = source
            .type_parameter_bounds()
            .iter()
            .zip(target.type_parameter_bounds())
            .all(|(source_bound, target_bound)| {
                let source_constraint = source_bound
                    .constraint()
                    .unwrap_or_else(|| self.table.unknown());
                let target_constraint = target_bound
                    .constraint()
                    .unwrap_or_else(|| self.table.unknown());
                self.relates(target_constraint, source_constraint, strictness)
                    || (same_declaration
                        && matches!(variance, ParameterVariance::Bivariant)
                        && self.relates(source_constraint, target_constraint, strictness))
            });
        let result = constraints_relate && compare();
        let removed = self
            .parameter_alias_frames
            .borrow_mut()
            .pop()
            .expect("active generic signature owns one alias frame");
        debug_assert_eq!(removed, added);
        let mut aliases = self.parameter_aliases.borrow_mut();
        let kept = aliases.len() - added;
        aliases.truncate(kept);
        drop(aliases);
        self.active_context.set(previous_context);
        result
    }

    /// Relates a generic signature to a non-generic one (or two generics
    /// with different arities) by inferring the generic side's type
    /// parameters from the non-generic counterpart's parameter types.
    ///
    /// Positional inference matches each source parameter type against the
    /// corresponding target parameter type. When the source parameter is a
    /// bare type parameter `T`, it is inferred as the target parameter type.
    /// When the source parameter is a structural type containing `T` (e.g.
    /// `T[]`, `(arg: T) => U`), inference recurses into the structure. Type
    /// parameters that cannot be inferred from any parameter position keep
    /// their declared constraint (or the implicit `unknown` when
    /// unconstrained), which is handled by the `known_type_parameters` arms
    /// in `relates_uncached`.
    fn with_inferred_parameters(
        &self,
        source: &FunctionSignature,
        target: &FunctionSignature,
        source_parameters: &[SymbolId],
        target_parameters: &[SymbolId],
        compare: impl FnOnce() -> bool,
    ) -> bool {
        let previous_context = self.active_context.get();

        // Register source type parameters as known so unconstrained ones
        // are treated as `unknown` (their implicit constraint). Target TPs
        // are only registered when the source is also generic — otherwise
        // the target's unconstrained TPs should go through the normal
        // constraint arms, not be collapsed to `unknown` (which would make
        // everything assignable to them).
        let mut known = self.known_type_parameters.borrow_mut();
        known.extend(source_parameters.iter().copied());
        if !source_parameters.is_empty() {
            known.extend(target_parameters.iter().copied());
        }
        drop(known);

        // Infer source type parameters from target parameter types.
        let mut inferred = self.inferred_type_arguments.borrow_mut();
        let inferred_added: Vec<SymbolId>;
        if !source_parameters.is_empty() && target_parameters.is_empty() {
            // Source is generic, target is not: infer source TPs from target params.
            inferred_added = source_parameters.to_vec();
            for &tp in source_parameters {
                inferred
                    .entry(tp)
                    .or_insert_with(|| self.infer_type_argument(tp, source, target));
            }
        } else if source_parameters.is_empty() && !target_parameters.is_empty() {
            // Target is generic, source is not: infer target TPs from
            // source parameter types so the comparison uses the concrete
            // instantiations. Only infer when a real match is found —
            // falling back to `unknown` would make everything assignable
            // to the target, which is wrong.
            let mut added: Vec<SymbolId> = Vec::new();
            let target_params = target.parameters();
            let source_params = source.parameters();
            for &tp in target_parameters {
                for (tp_param, src_param) in target_params.iter().zip(source_params.iter()) {
                    if let Some(inferred_type) =
                        self.infer_from_type(tp, tp_param.type_id(), src_param.type_id())
                    {
                        inferred.entry(tp).or_insert(inferred_type);
                        added.push(tp);
                        break;
                    }
                }
            }
            inferred_added = added;
        } else {
            // Both generic with different arities: infer source TPs from
            // target params (with `unknown` fallback for unconstrained),
            // and target TPs from source params (only on real match —
            // `unknown` fallback would make everything assignable).
            let mut added: Vec<SymbolId> = source_parameters.to_vec();
            for &tp in source_parameters {
                inferred
                    .entry(tp)
                    .or_insert_with(|| self.infer_type_argument(tp, source, target));
            }
            let target_params = target.parameters();
            let source_params = source.parameters();
            for &tp in target_parameters {
                for (tp_param, src_param) in target_params.iter().zip(source_params.iter()) {
                    if let Some(inferred_type) =
                        self.infer_from_type(tp, tp_param.type_id(), src_param.type_id())
                    {
                        inferred.entry(tp).or_insert(inferred_type);
                        added.push(tp);
                        break;
                    }
                }
            }
            inferred_added = added;
        }
        drop(inferred);

        self.refresh_context();
        let result = compare();

        // Clean up.
        let mut inferred = self.inferred_type_arguments.borrow_mut();
        for tp in &inferred_added {
            inferred.remove(tp);
        }
        drop(inferred);

        let mut known = self.known_type_parameters.borrow_mut();
        // Remove only the ones we added (they were not present before).
        for tp in source_parameters.iter().chain(target_parameters.iter()) {
            known.remove(tp);
        }
        drop(known);

        self.active_context.set(previous_context);
        result
    }

    /// Attempts to infer a single type parameter `tp` by matching the
    /// parameter types of `generic` against those of `concrete`.
    fn infer_type_argument(
        &self,
        tp: SymbolId,
        generic: &FunctionSignature,
        concrete: &FunctionSignature,
    ) -> TypeId {
        let generic_params = generic.parameters();
        let concrete_params = concrete.parameters();
        for (generic_param, concrete_param) in generic_params.iter().zip(concrete_params.iter()) {
            if let Some(inferred) =
                self.infer_from_type(tp, generic_param.type_id(), concrete_param.type_id())
            {
                return inferred;
            }
        }
        // Could not infer from parameters: use the constraint, or `unknown`.
        self.table
            .type_parameter_constraint(tp)
            .unwrap_or_else(|| self.table.unknown())
    }

    /// Recursively matches `pattern` (which may contain the type parameter
    /// `tp`) against `concrete` to infer `tp`'s type.
    fn infer_from_type(&self, tp: SymbolId, pattern: TypeId, concrete: TypeId) -> Option<TypeId> {
        match self.table.get(pattern) {
            Type::Named(symbol) if *symbol == tp => Some(concrete),
            Type::Array(element) => {
                if let Type::Array(concrete_element) = self.table.get(concrete) {
                    self.infer_from_type(tp, *element, *concrete_element)
                } else if let Type::Tuple(concrete_shape) = self.table.get(concrete) {
                    // T[] matches a tuple if all elements are the same type.
                    let mut inferred = None;
                    for &elem in concrete_shape.all_element_types().iter() {
                        if let Some(elem_inferred) = self.infer_from_type(tp, *element, elem) {
                            if let Some(existing) = inferred {
                                if existing != elem_inferred {
                                    return None;
                                }
                            } else {
                                inferred = Some(elem_inferred);
                            }
                        }
                    }
                    inferred
                } else {
                    None
                }
            }
            Type::Tuple(shape) => {
                if let Type::Tuple(concrete_shape) = self.table.get(concrete) {
                    for (pattern_elem, concrete_elem) in shape
                        .all_element_types()
                        .iter()
                        .zip(concrete_shape.all_element_types().iter())
                    {
                        if let Some(inferred) =
                            self.infer_from_type(tp, *pattern_elem, *concrete_elem)
                        {
                            return Some(inferred);
                        }
                    }
                }
                None
            }
            Type::Function(sig) => {
                if let Type::Function(concrete_sig) = self.table.get(concrete) {
                    for (pattern_param, concrete_param) in sig
                        .parameters()
                        .iter()
                        .zip(concrete_sig.parameters().iter())
                    {
                        // Parameters are contravariant: match pattern param
                        // against concrete param in reverse.
                        if let Some(inferred) = self.infer_from_type(
                            tp,
                            concrete_param.type_id(),
                            pattern_param.type_id(),
                        ) {
                            return Some(inferred);
                        }
                    }
                    if let Some(inferred) =
                        self.infer_from_type(tp, sig.return_type(), concrete_sig.return_type())
                    {
                        return Some(inferred);
                    }
                }
                None
            }
            Type::ObjectType(obj) => {
                if let Type::ObjectType(concrete_obj) = self.table.get(concrete) {
                    for pattern_prop in &obj.properties {
                        if let Some(concrete_prop) = concrete_obj
                            .properties
                            .iter()
                            .find(|p| p.name() == pattern_prop.name())
                            && let Some(inferred) = self.infer_from_type(
                                tp,
                                pattern_prop.type_id(),
                                concrete_prop.type_id(),
                            )
                        {
                            return Some(inferred);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }
    fn with_erased_parameters(
        &self,
        source: &FunctionSignature,
        target: &FunctionSignature,
        compare: impl FnOnce() -> bool,
    ) -> bool {
        let added = source.type_parameters().len() + target.type_parameters().len();
        let previous_context = self.active_context.get();
        let mut erased = self.erased_parameters.borrow_mut();
        let already_active = !erased.is_empty();
        erased.extend(source.type_parameters());
        erased.extend(target.type_parameters());
        drop(erased);
        if !already_active {
            self.refresh_context();
        }
        let result = compare();
        let mut erased = self.erased_parameters.borrow_mut();
        let kept = erased.len() - added;
        erased.truncate(kept);
        drop(erased);
        self.active_context.set(previous_context);
        result
    }

    fn is_erased_parameter(&self, symbol: SymbolId) -> bool {
        let erased = self.erased_parameters.borrow().contains(&symbol);
        if let Some(frame) = self.dependency_stack.borrow_mut().last_mut() {
            self.record_erasure_requirement(frame, ErasureRequirement { symbol, erased });
        }
        erased
    }

    fn record_erasure_requirement(
        &self,
        frame: &mut DependencyFrame,
        requirement: ErasureRequirement,
    ) {
        if requirement.erased {
            let erased = self.erased_parameters.borrow();
            if !erased[..frame.erased_base.min(erased.len())].contains(&requirement.symbol) {
                return;
            }
        }
        if let Some(previous) = frame
            .erasure_requirements
            .insert(requirement.symbol, requirement.erased)
        {
            debug_assert_eq!(
                previous, requirement.erased,
                "one relation frame observed conflicting erasure membership"
            );
        }
    }

    fn is_structural(&self, type_id: TypeId) -> bool {
        matches!(
            self.table.get(type_id),
            Type::Union(_)
                | Type::Array(_)
                | Type::Tuple(_)
                | Type::ObjectType(_)
                | Type::Function(_)
                | Type::Named(_)
                | Type::AppliedClass { .. }
                | Type::AppliedAlias { .. }
                | Type::This { .. }
                | Type::Record { .. }
        )
    }

    /// Follows transparent alias heads without classifying a missing or cyclic
    /// view as the alias's nominal identity.
    fn relation_alias_view(&self, mut type_id: TypeId) -> Option<TypeId> {
        let mut visiting = HashSet::new();
        while matches!(self.table.get(type_id), Type::AppliedAlias { .. }) {
            if !visiting.insert(type_id) {
                return None;
            }
            type_id = self.table.applied_alias_view(type_id)?;
        }
        Some(type_id)
    }

    fn contains_undefined(&self, type_id: TypeId) -> bool {
        self.contains_undefined_inner(type_id, &mut HashSet::new())
    }

    fn contains_undefined_inner(
        &self,
        type_id: TypeId,
        visiting_aliases: &mut HashSet<TypeId>,
    ) -> bool {
        match self.table.get(type_id) {
            Type::Any | Type::Unknown | Type::Undefined => true,
            Type::Union(members) => members
                .iter()
                .any(|member| self.contains_undefined_inner(*member, visiting_aliases)),
            Type::AppliedClass { .. } => self
                .table
                .applied_class_view(type_id)
                .map(|view| self.contains_undefined_inner(view, visiting_aliases))
                .unwrap_or(false),
            Type::AppliedAlias { .. } => {
                if !visiting_aliases.insert(type_id) {
                    return false;
                }
                self.table
                    .applied_alias_view(type_id)
                    .map(|view| self.contains_undefined_inner(view, visiting_aliases))
                    .unwrap_or(false)
            }
            Type::ConstructorType { structural, .. } => {
                self.contains_undefined_inner(*structural, visiting_aliases)
            }
            Type::Error
            | Type::Intersection(_)
            | Type::Never
            | Type::Void
            | Type::Null
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
            | Type::Array(_)
            | Type::Tuple(_)
            | Type::ObjectType(_)
            | Type::Function(_)
            | Type::Named(_)
            | Type::NumericEnum(_)
            | Type::EnumMember { .. }
            | Type::Keyof(_)
            | Type::IndexedAccess { .. }
            | Type::Record { .. }
            | Type::This { .. } => false,
        }
    }

    /// Structural relation between two tuple shapes.
    ///
    /// A tuple relation must hold for every runtime length admitted by the
    /// source. The target must admit that full length interval, and every
    /// source element possible at a position must fit at least one target
    /// element possible at the same position.
    fn tuple_relates(
        &self,
        source: &TupleShape,
        target: &TupleShape,
        strictness: Strictness,
    ) -> bool {
        if source.min_arity() < target.min_arity() {
            return false;
        }
        match (source.max_arity(), target.max_arity()) {
            (Some(source_max), Some(target_max)) if source_max > target_max => return false,
            (None, Some(_)) => return false,
            _ => {}
        }

        let last_length = source.max_arity().unwrap_or_else(|| {
            (source.prefix.len() + source.suffix.len())
                .max(target.prefix.len() + target.suffix.len())
                .max(source.min_arity())
                .saturating_add(1)
        });
        (source.min_arity()..=last_length)
            .all(|length| self.tuple_length_relates(source, target, length, strictness))
    }

    fn tuple_length_relates(
        &self,
        source: &TupleShape,
        target: &TupleShape,
        length: usize,
        strictness: Strictness,
    ) -> bool {
        let source_layouts = source.prefix_lengths_at_length(length);
        let target_layouts = target.prefix_lengths_at_length(length);
        source_layouts.iter().all(|&source_prefix_len| {
            target_layouts.iter().any(|&target_prefix_len| {
                (0..length).all(|index| {
                    self.relates(
                        source.element_at_layout(index, length, source_prefix_len),
                        target.element_at_layout(index, length, target_prefix_len),
                        strictness,
                    )
                })
            })
        })
    }
    fn property_origin_compatible(have: &PropertyType, want: &PropertyType) -> bool {
        if want.access() == Accessibility::Public {
            return have.access() == Accessibility::Public;
        }
        have.access() != Accessibility::Public && have.declaring_class() == want.declaring_class()
    }

    fn iterator_property_origin_compatible(
        have: &IteratorProperty,
        want: &IteratorProperty,
    ) -> bool {
        if want.access() == Accessibility::Public {
            return have.access() == Accessibility::Public;
        }
        have.access() != Accessibility::Public && have.declaring_class() == want.declaring_class()
    }

    fn optional_semantic_type_relates(
        &self,
        source: Option<TypeId>,
        target: Option<TypeId>,
        strictness: Strictness,
    ) -> bool {
        let Some(target) = target else {
            return true;
        };
        source.is_some_and(|source| {
            self.relates(source, target, strictness)
                || (strictness == Strictness::Comparable
                    && self.relates(target, source, strictness))
        })
    }

    fn iterator_property_relates(
        &self,
        source: Option<&IteratorProperty>,
        target: Option<&IteratorProperty>,
        strictness: Strictness,
    ) -> bool {
        let Some(target) = target else {
            return true;
        };
        let Some(source) = source else {
            return target.optional();
        };
        if source.optional() && !target.optional() {
            return false;
        }
        Self::iterator_property_origin_compatible(source, target)
            && (self.relates(source.type_id(), target.type_id(), strictness)
                || (strictness == Strictness::Comparable
                    && self.relates(target.type_id(), source.type_id(), strictness))
                || (target.is_method()
                    && self.method_overloads_relate(
                        source.type_id(),
                        target.type_id(),
                        strictness,
                    )))
    }

    fn object_relates(
        &self,
        source: &ObjectType,
        target: &ObjectType,
        strictness: Strictness,
    ) -> bool {
        let properties_relate = target.properties.iter().all(|want| {
            if let Some(have) = source
                .properties
                .iter()
                .find(|have| have.name() == want.name())
            {
                return Self::property_origin_compatible(have, want)
                    && (self.property_type_relates(have, want, strictness)
                        || (matches!(
                            strictness,
                            Strictness::Assignable
                                | Strictness::StrictNull
                                | Strictness::Comparable
                        ) && want.optional()
                            && matches!(self.table.get(have.type_id()), Type::Undefined)));
            }
            if let Some(signature) = source.index_signatures.iter().find(|signature| {
                signature.parameters.first().is_some_and(|parameter| {
                    self.table
                        .property_name_assignable_to_key(want.name(), parameter.type_id())
                })
            }) {
                return self.relates(signature.value_type, want.type_id(), strictness);
            }
            want.optional()
        });
        properties_relate
            && self.optional_semantic_type_relates(
                source.generator_return,
                target.generator_return,
                strictness,
            )
            && self.iterator_property_relates(
                source.iterator_property.as_ref(),
                target.iterator_property.as_ref(),
                strictness,
            )
            && self.iterator_property_relates(
                source.async_iterator_property.as_ref(),
                target.async_iterator_property.as_ref(),
                strictness,
            )
            && self.signature_sets_relate(
                &source.call_signatures,
                &target.call_signatures,
                strictness,
            )
            && self.construct_sets_relate(
                &source.construct_signatures,
                &target.construct_signatures,
                strictness,
            )
            && target.index_signatures.iter().all(|want| {
                let Some(want_parameter) = want.parameters.first() else {
                    return false;
                };
                let properties_relate = source.properties.iter().all(|property| {
                    if !self
                        .table
                        .property_name_assignable_to_key(property.name(), want_parameter.type_id())
                    {
                        return true;
                    }
                    self.relates(property.type_id(), want.value_type, strictness)
                });
                let source_signature = match self.table.get(want_parameter.type_id()) {
                    Type::Number => source
                        .index_signatures
                        .iter()
                        .find(|have| {
                            have.parameters.first().is_some_and(|parameter| {
                                matches!(self.table.get(parameter.type_id()), Type::Number)
                            })
                        })
                        .or_else(|| {
                            source.index_signatures.iter().find(|have| {
                                have.parameters.first().is_some_and(|parameter| {
                                    matches!(self.table.get(parameter.type_id()), Type::String)
                                })
                            })
                        }),
                    Type::String => source.index_signatures.iter().find(|have| {
                        have.parameters.first().is_some_and(|parameter| {
                            matches!(self.table.get(parameter.type_id()), Type::String)
                        })
                    }),
                    Type::Symbol => source.index_signatures.iter().find(|have| {
                        have.parameters.first().is_some_and(|parameter| {
                            matches!(self.table.get(parameter.type_id()), Type::Symbol)
                        })
                    }),
                    _ => return false,
                };
                let signatures_relate = source_signature
                    .map(|have| self.relates(have.value_type, want.value_type, strictness))
                    .unwrap_or_else(|| source.index_signatures.is_empty());
                properties_relate && signatures_relate
            })
    }

    /// An array or tuple flows into an object type carrying numeric index
    /// signatures when the object has no members an array could not provide
    /// and every element type is assignable to each numeric index value type.
    /// TypeScript accepts `var x9: { [n: number]: Base; } = [d1, d2]` with
    /// zero TS2322 (generatedContextualTyping.errors.txt, which holds no
    /// TS2322 across 452 lines despite nine array-to-index-object writes),
    /// while assignmentCompatWithNumericIndexer3.errors.txt(14) still rejects
    /// `{ [x: number]: Base; }` for `A` because `Base` is not assignable to
    /// `Derived` — the same value-type covariance this check enforces. A
    /// second counterexample check: indexSignatures1.errors.txt(21) expects
    /// `IY` not assignable to `IX`, keeping indexer comparisons strict.
    fn array_relates_to_index_object(
        &self,
        source: TypeId,
        target_object: &ObjectType,
        strictness: Strictness,
    ) -> bool {
        if !target_object.call_signatures.is_empty()
            || !target_object.construct_signatures.is_empty()
            || target_object.generator_return.is_some()
            || target_object.async_iterator_property.is_some()
            || target_object
                .properties
                .iter()
                .any(|property| !property.optional())
        {
            return false;
        }
        let mut numeric_values = Vec::new();
        for signature in &target_object.index_signatures {
            let Some(parameter) = signature.parameters.first() else {
                return false;
            };
            if matches!(self.table.get(parameter.type_id()), Type::Number) {
                numeric_values.push(signature.value_type);
            } else {
                // Arrays carry no string or symbol index information, so a
                // target requiring one stays unrelated.
                return false;
            }
        }
        if numeric_values.is_empty() {
            return false;
        }
        let elements: Vec<TypeId> = match self.table.get(source) {
            Type::Array(element) => vec![*element],
            Type::Tuple(shape) => shape.all_element_types().to_vec(),
            _ => return false,
        };
        numeric_values.iter().all(|&value| {
            elements
                .iter()
                .all(|&element| self.relates(element, value, strictness))
        })
    }

    fn object_satisfies_record(
        &self,
        source: &ObjectType,
        key: TypeId,
        value: TypeId,
        strictness: Strictness,
    ) -> bool {
        if let Some(names) = self.record_literal_keys(key) {
            return names.iter().all(|name| {
                source
                    .properties
                    .iter()
                    .find(|property| property.name() == name)
                    .map(|property| self.relates(property.type_id(), value, strictness))
                    .or_else(|| {
                        source.index_signatures.iter().find_map(|signature| {
                            let parameter = signature.parameters.first()?;
                            self.table
                                .property_name_assignable_to_key(name, parameter.type_id())
                                .then(|| self.relates(signature.value_type, value, strictness))
                        })
                    })
                    .unwrap_or(false)
            });
        }
        if !self.record_key_is_concrete_domain(key) {
            return false;
        }
        source
            .properties
            .iter()
            .filter(|property| {
                self.table
                    .property_name_assignable_to_key(property.name(), key)
            })
            .all(|property| self.relates(property.type_id(), value, strictness))
            && source.index_signatures.iter().all(|signature| {
                let Some(parameter) = signature.parameters.first() else {
                    return false;
                };
                let parameter = parameter.type_id();
                let overlaps = self.relates(parameter, key, Strictness::Comparable)
                    || self.relates(key, parameter, Strictness::Comparable);
                !overlaps || self.relates(signature.value_type, value, strictness)
            })
    }

    fn record_literal_keys(&self, key: TypeId) -> Option<Vec<String>> {
        match self.table.get(key) {
            Type::Never => Some(Vec::new()),
            Type::StringLiteral(name) => name.to_utf8_strict().ok().map(|name| vec![name]),
            Type::NumberLiteral(name) => Some(vec![name.to_string()]),
            Type::Union(members) => {
                let mut names = Vec::new();
                for member in members {
                    names.extend(self.record_literal_keys(*member)?);
                }
                names.sort_unstable();
                names.dedup();
                Some(names)
            }
            _ => None,
        }
    }

    fn record_key_is_concrete_domain(&self, key: TypeId) -> bool {
        match self.table.get(key) {
            Type::Any
            | Type::Error
            | Type::Never
            | Type::String
            | Type::Number
            | Type::Symbol
            | Type::StringLiteral(_)
            | Type::NumberLiteral(_) => true,
            Type::Union(members) => members
                .iter()
                .all(|member| self.record_key_is_concrete_domain(*member)),
            _ => false,
        }
    }

    fn property_type_relates(
        &self,
        source: &PropertyType,
        target: &PropertyType,
        strictness: Strictness,
    ) -> bool {
        if source.optional() && !target.optional() {
            return false;
        }
        self.relates(source.type_id(), target.type_id(), strictness)
            || (strictness == Strictness::Comparable
                && self.relates(target.type_id(), source.type_id(), strictness))
            || (target.is_method()
                && self.method_overloads_relate(source.type_id(), target.type_id(), strictness))
    }

    fn constraint_source_relates(
        &self,
        expression: &ConstraintTypeExpr,
        target: TypeId,
        strictness: Strictness,
    ) -> bool {
        self.constraint_clauses_relate(vec![expression], Vec::new(), target, strictness)
    }

    fn constraint_clauses_relate<'expression>(
        &self,
        mut pending: Vec<&'expression ConstraintTypeExpr>,
        mut known: Vec<TypeId>,
        target: TypeId,
        strictness: Strictness,
    ) -> bool {
        loop {
            let Some(expression) = pending.pop() else {
                return self.constraint_clause_relates(&known, target, strictness);
            };
            match expression {
                ConstraintTypeExpr::Id(type_id) => known.push(*type_id),
                ConstraintTypeExpr::Opaque => {}
                ConstraintTypeExpr::Intersection(members) => {
                    pending.extend(members.iter().rev());
                }
                ConstraintTypeExpr::Union(members) => {
                    let relates = |member: &'expression ConstraintTypeExpr| {
                        let mut branch = pending.clone();
                        branch.push(member);
                        self.constraint_clauses_relate(branch, known.clone(), target, strictness)
                    };
                    return if strictness == Strictness::Comparable {
                        members.iter().any(relates)
                    } else {
                        members.iter().all(relates)
                    };
                }
            }
        }
    }

    fn constraint_clause_relates(
        &self,
        known: &[TypeId],
        target: TypeId,
        strictness: Strictness,
    ) -> bool {
        if self.constraint_clause_is_never(known) {
            return true;
        }
        let Some(target) = self.relation_alias_view(target) else {
            return false;
        };
        match self.table.get(target) {
            Type::Union(targets) => {
                return targets
                    .iter()
                    .any(|target| self.constraint_clause_relates(known, *target, strictness));
            }
            Type::Intersection(targets) => {
                return targets
                    .iter()
                    .all(|target| self.constraint_clause_relates(known, *target, strictness));
            }
            _ => {}
        }
        if known
            .iter()
            .any(|source| self.relates(*source, target, strictness))
        {
            return true;
        }
        let Type::ObjectType(target) = self.table.get(target) else {
            return false;
        };
        self.intersection_object_relates(known, target, strictness)
    }

    fn constraint_clause_is_never(&self, known: &[TypeId]) -> bool {
        known
            .iter()
            .any(|type_id| matches!(self.table.get(*type_id), Type::Never))
            || known.iter().enumerate().any(|(index, left)| {
                known[index + 1..]
                    .iter()
                    .any(|right| self.constraint_ids_disjoint(*left, *right))
            })
    }

    fn constraint_ids_disjoint(&self, left: TypeId, right: TypeId) -> bool {
        let Some(left) = self.relation_alias_view(left) else {
            return false;
        };
        let Some(right) = self.relation_alias_view(right) else {
            return false;
        };
        let left = self.table.get(left);
        let right = self.table.get(right);
        if matches!(left, Type::Never) || matches!(right, Type::Never) {
            return true;
        }
        let Some(left_domain) = Self::primitive_domain(left) else {
            return false;
        };
        let Some(right_domain) = Self::primitive_domain(right) else {
            return false;
        };
        if left_domain != right_domain {
            return true;
        }
        match (left, right) {
            (Type::BooleanLiteral(left), Type::BooleanLiteral(right)) => left != right,
            (Type::NumberLiteral(left), Type::NumberLiteral(right)) => {
                match (number_value(left), number_value(right)) {
                    (Some(left), Some(right)) => left != right,
                    _ => false,
                }
            }
            (Type::StringLiteral(left), Type::StringLiteral(right)) => left != right,
            (Type::BigIntLiteral(left), Type::BigIntLiteral(right)) => {
                let left = canonical_bigint_text(
                    left,
                    MAX_BIGINT_BYTES as usize,
                    MAX_BIGINT_CONVERSION_LIMB_OPS,
                );
                let right = canonical_bigint_text(
                    right,
                    MAX_BIGINT_BYTES as usize,
                    MAX_BIGINT_CONVERSION_LIMB_OPS,
                );
                match (left, right) {
                    (Ok(left), Ok(right)) => left != right,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn primitive_domain(type_: &Type) -> Option<PrimitiveDomain> {
        match type_ {
            Type::Null => Some(PrimitiveDomain::Null),
            Type::Undefined => Some(PrimitiveDomain::Undefined),
            Type::Boolean | Type::BooleanLiteral(_) => Some(PrimitiveDomain::Boolean),
            Type::Number
            | Type::NumberLiteral(_)
            | Type::NumericEnum(_)
            | Type::EnumMember {
                string_value: None, ..
            } => Some(PrimitiveDomain::Number),
            Type::BigInt | Type::BigIntLiteral(_) => Some(PrimitiveDomain::BigInt),
            Type::String
            | Type::StringLiteral(_)
            | Type::EnumMember {
                string_value: Some(_),
                ..
            } => Some(PrimitiveDomain::String),
            Type::Symbol => Some(PrimitiveDomain::Symbol),
            _ => None,
        }
    }
    fn relation_object_view(&self, type_id: TypeId) -> Option<&ObjectType> {
        let type_id = self.relation_alias_view(type_id)?;
        let type_id = match self.table.get(type_id) {
            Type::AppliedClass { .. } => self.table.applied_class_view(type_id).unwrap_or(type_id),
            Type::Named(symbol) => self
                .table
                .type_parameter_constraint(*symbol)
                .unwrap_or(type_id),
            _ => type_id,
        };
        let type_id = self.relation_alias_view(type_id)?;
        let type_id = self.table.named_structural_view(type_id);
        let type_id = self.relation_alias_view(type_id)?;
        match self.table.get(type_id) {
            Type::ObjectType(object) => Some(object),
            _ => None,
        }
    }

    fn intersection_object_relates(
        &self,
        sources: &[TypeId],
        target: &ObjectType,
        strictness: Strictness,
    ) -> bool {
        let properties_relate = target.properties.iter().all(|want| {
            let satisfied = sources.iter().any(|source| {
                let Some(object) = self.relation_object_view(*source) else {
                    return false;
                };
                object
                    .properties
                    .iter()
                    .find(|have| have.name() == want.name())
                    .is_some_and(|have| {
                        Self::property_origin_compatible(have, want)
                            && self.property_type_relates(have, want, strictness)
                    })
            });
            satisfied || want.optional()
        });
        let generator_return_relates = target.generator_return.is_none_or(|target_return| {
            sources.iter().any(|source| {
                self.relation_object_view(*source).is_some_and(|object| {
                    self.optional_semantic_type_relates(
                        object.generator_return,
                        Some(target_return),
                        strictness,
                    )
                })
            })
        });
        let iterator_property_relates = target.iterator_property.as_ref().is_none_or(|target| {
            sources.iter().any(|source| {
                self.relation_object_view(*source).is_some_and(|object| {
                    self.iterator_property_relates(
                        object.iterator_property.as_ref(),
                        Some(target),
                        strictness,
                    )
                })
            })
        });
        let async_iterator_property_relates =
            target
                .async_iterator_property
                .as_ref()
                .is_none_or(|target| {
                    sources.iter().any(|source| {
                        self.relation_object_view(*source).is_some_and(|object| {
                            self.iterator_property_relates(
                                object.async_iterator_property.as_ref(),
                                Some(target),
                                strictness,
                            )
                        })
                    })
                });
        if !properties_relate
            || !generator_return_relates
            || !iterator_property_relates
            || !async_iterator_property_relates
        {
            return false;
        }

        let mut combined = ObjectType {
            properties: Vec::new(),
            call_signatures: Vec::new(),
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        };
        let mut has_object = false;
        for source in sources {
            let Some(object) = self.relation_object_view(*source) else {
                continue;
            };
            has_object = true;
            combined
                .properties
                .extend(object.properties.iter().cloned());
            combined
                .call_signatures
                .extend(object.call_signatures.iter().cloned());
            combined
                .construct_signatures
                .extend(object.construct_signatures.iter().cloned());
            combined
                .index_signatures
                .extend(object.index_signatures.iter().cloned());
        }
        if !has_object {
            return false;
        }
        let index_target = ObjectType {
            properties: Vec::new(),
            call_signatures: Vec::new(),
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: target.index_signatures.clone(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        };
        self.signature_sets_relate(
            &combined.call_signatures,
            &target.call_signatures,
            strictness,
        ) && self.construct_sets_relate(
            &combined.construct_signatures,
            &target.construct_signatures,
            strictness,
        ) && self.object_relates(&combined, &index_target, strictness)
    }

    fn signature_sets_relate(
        &self,
        source: &[FunctionSignature],
        target: &[FunctionSignature],
        strictness: Strictness,
    ) -> bool {
        target.iter().all(|want| {
            source
                .iter()
                .any(|have| self.function_relates(have, want, strictness))
        })
    }

    fn construct_sets_relate(
        &self,
        source: &[ConstructEntry],
        target: &[ConstructEntry],
        strictness: Strictness,
    ) -> bool {
        target.iter().all(|want| {
            source.iter().any(|have| {
                (want.is_abstract || !have.is_abstract)
                    && self.function_relates(&have.signature, &want.signature, strictness)
            })
        })
    }

    fn function_relates(
        &self,
        source: &FunctionSignature,
        target: &FunctionSignature,
        strictness: Strictness,
    ) -> bool {
        self.signature_relates(source, target, strictness, ParameterVariance::Contravariant)
    }

    /// Bivariant method-overload comparison over the order-insensitive
    /// overload view: every target overload must be covered by some source
    /// overload. Types outside the pure-callable view — mixed objects,
    /// constructor-bearing objects, intersections with non-callable
    /// members — yield `None` on either side, so this returns false and the
    /// structural relation path handles them with the ordinary
    /// contravariant callable rules. Candidate ordering is never inspected.
    fn method_overloads_relate(
        &self,
        source: TypeId,
        target: TypeId,
        strictness: Strictness,
    ) -> bool {
        let Some(target_signatures) = self.table.overload_signatures(target) else {
            return false;
        };
        let Some(source_signatures) = self.table.overload_signatures(source) else {
            return false;
        };
        target_signatures.iter().all(|target_signature| {
            source_signatures.iter().any(|source_signature| {
                self.signature_relates(
                    source_signature,
                    target_signature,
                    strictness,
                    ParameterVariance::Bivariant,
                )
            })
        })
    }

    fn signature_relates(
        &self,
        source: &FunctionSignature,
        target: &FunctionSignature,
        strictness: Strictness,
        variance: ParameterVariance,
    ) -> bool {
        self.with_parameter_aliases(source, target, strictness, variance, || {
            let (source_required, _, _) = source.arity();
            let (target_required, _, target_rest) = target.arity();
            if target_rest.is_none() && source_required > target_required {
                return false;
            }
            let positions = source.parameters().len().max(target.parameters().len());
            for index in 0..positions {
                let (Some(source_types), Some(target_types)) = (
                    self.parameter_types_at(source, index),
                    self.parameter_types_at(target, index),
                ) else {
                    continue;
                };
                if !target_types.iter().all(|target_type| {
                    source_types.iter().any(|source_type| {
                        self.relates(*target_type, *source_type, strictness)
                            || (matches!(variance, ParameterVariance::Bivariant)
                                && self.relates(*source_type, *target_type, strictness))
                    })
                }) {
                    return false;
                }
            }
            matches!(self.table.get(target.return_type()), Type::Void)
                || self.relates(source.return_type(), target.return_type(), strictness)
        })
    }

    /// Types a signature accepts at `index`, or `None` when it accepts nothing
    /// there. A trailing tuple rest preserves its positional shape instead of
    /// comparing the tuple object itself with one scalar argument.
    fn parameter_types_at(
        &self,
        signature: &FunctionSignature,
        index: usize,
    ) -> Option<Vec<TypeId>> {
        let parameters = signature.parameters();
        if let Some(parameter) = parameters.get(index) {
            return Some(if parameter.rest() {
                self.rest_types_at(parameter.type_id(), 0)
            } else {
                vec![parameter.type_id()]
            });
        }
        let rest_index = parameters.len().checked_sub(1)?;
        let rest = &parameters[rest_index];
        rest.rest()
            .then(|| self.rest_types_at(rest.type_id(), index - rest_index))
    }

    fn rest_types_at(&self, type_id: TypeId, index: usize) -> Vec<TypeId> {
        let mut current = type_id;
        let mut seen = HashSet::new();
        while seen.insert(current) {
            match self.table.get(current) {
                Type::Array(element) => return vec![*element],
                Type::Tuple(shape) => return shape.element_types_at(index),
                Type::Any | Type::Error => return vec![current],
                Type::Named(symbol) => {
                    if let Some(constraint) = self.table.type_parameter_constraint(*symbol) {
                        current = constraint;
                        continue;
                    }
                    return vec![type_id];
                }
                _ => return vec![type_id],
            }
        }
        vec![type_id]
    }
}

#[cfg(test)]
mod tests {
    use super::super::binder::{FunctionParameter, TypeParameterBounds};
    use super::super::{PropertyType, SymbolId};
    use super::*;

    #[test]
    fn primitives_follow_the_lattice_in_both_modes() {
        let table = TypeTable::new();
        let relations = TypeRelations::new(&table);
        for strict in [false, true] {
            let relates = |source, target| {
                if strict {
                    relations.subtype(source, target)
                } else {
                    relations.assignable(source, target)
                }
            };
            // never flows into everything; nothing else flows into never.
            assert!(relates(table.never(), table.number()));
            assert!(!relates(table.number(), table.never()));
            // unknown is the top: everything in, nothing out.
            assert!(relates(table.number(), table.unknown()));
            assert!(!relates(table.unknown(), table.number()));
        }
        // `any` is an assignability-only escape hatch.
        assert!(relations.assignable(table.any(), table.number()));
        assert!(relations.assignable(table.number(), table.any()));
        assert!(!relations.subtype(table.any(), table.number()));
        assert!(!relations.subtype(table.number(), table.any()));
        // Identity keeps `any` related to itself in both modes.
        assert!(relations.subtype(table.any(), table.any()));
    }

    #[test]
    fn subtype_is_assignability_minus_the_concessions() {
        let mut table = TypeTable::new();
        let enum_type = table.numeric_enum(SymbolId::new(200));
        let (number, undefined) = (table.number(), table.undefined_type());
        let undefined_source = table.object_type(vec![PropertyType::new("x", false, undefined)]);
        let optional_target = table.object_type(vec![PropertyType::new("x", true, number)]);
        let relations = TypeRelations::new(&table);

        // Enum-to-number is genuine subtyping; number-to-enum is a concession.
        assert!(relations.subtype(enum_type, number));
        assert!(relations.assignable(number, enum_type));
        assert!(!relations.subtype(number, enum_type));
        // Explicit `undefined` for an optional property is a concession.
        assert!(relations.assignable(undefined_source, optional_target));
        assert!(!relations.subtype(undefined_source, optional_target));
    }

    #[test]
    fn strict_null_assignability_keeps_numeric_enum_concession() {
        let mut table = TypeTable::new();
        let enum_type = table.numeric_enum(SymbolId::new(201));
        let number = table.number();
        let null = table.null_type();
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable_with_strict_null(number, enum_type));
        assert!(!relations.assignable_with_strict_null(null, enum_type));
    }

    #[test]
    fn strict_null_allows_explicit_undefined_for_optional_property() {
        // `{p?: number} = {p: undefined}` is accepted under strict null checks
        // but still rejected by structural subtyping, and rejected when the
        // target property is non-optional.
        let mut table = TypeTable::new();
        let number = table.number();
        let undefined = table.undefined_type();
        let source = table.object_type(vec![PropertyType::new("p", false, undefined)]);
        let optional_target = table.object_type(vec![PropertyType::new("p", true, number)]);
        let required_target = table.object_type(vec![PropertyType::new("p", false, number)]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable_with_strict_null(source, optional_target));
        assert!(relations.assignable(source, optional_target));
        assert!(!relations.subtype(source, optional_target));
        assert!(!relations.assignable_with_strict_null(source, required_target));
    }

    #[test]
    fn structural_objects_arrays_and_unions_relate_in_both_modes() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let required = table.object_type(vec![PropertyType::new("x", false, number)]);
        let with_excess = table.object_type(vec![
            PropertyType::new("x", false, number),
            PropertyType::new("y", false, string),
        ]);
        let missing = table.object_type(vec![PropertyType::new("y", false, string)]);
        let optional = table.object_type(vec![PropertyType::new("x", true, number)]);
        let empty = table.object_type(Vec::new());
        let one = table.number_literal("1");
        let literal_array = table.array(one);
        let number_array = table.array(number);
        let union = table.union(&[number, string]);
        let relations = TypeRelations::new(&table);

        assert!(relations.subtype(with_excess, required));
        assert!(!relations.subtype(missing, required));
        assert!(relations.subtype(empty, optional));
        assert!(relations.subtype(literal_array, number_array));
        assert!(!relations.subtype(number_array, literal_array));
        assert!(relations.subtype(number, union));
        assert!(!relations.subtype(union, number));
    }

    #[test]
    fn comparable_relation_accepts_one_union_overlap_only() {
        let mut table = TypeTable::new();
        let a = table.string_literal("a");
        let b = table.string_literal("b");
        let c = table.string_literal("c");
        let number = table.number();
        let string = table.string();
        let broad_tag = table.union(&[a, b]);
        let broad = table.object_type(vec![
            PropertyType::new("kind", false, broad_tag),
            PropertyType::new("value", false, number),
        ]);
        let narrow = table.object_type(vec![
            PropertyType::new("kind", false, a),
            PropertyType::new("value", false, number),
        ]);
        let other = table.object_type(vec![
            PropertyType::new("kind", false, c),
            PropertyType::new("other", false, string),
        ]);
        let target = table.union(&[narrow, other]);
        let conflicting = table.object_type(vec![PropertyType::new("value", false, string)]);
        let disjoint = table.object_type(vec![PropertyType::new("other", false, string)]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(broad, target));
        assert!(!relations.assignable(target, broad));
        assert!(relations.comparable(broad, target));
        assert!(!relations.comparable(broad, conflicting));
        assert!(!relations.comparable(broad, disjoint));
        assert!(!relations.comparable(table.null_type(), string));
    }
    #[test]
    fn comparable_signatures_erase_generic_parameters() {
        let mut table = TypeTable::new();
        let parameter = SymbolId::new(700);
        let parameter_type = table.named(parameter);
        let generic = table.function_with_parameters(
            vec![parameter],
            vec![FunctionParameter::new(
                "value".to_owned(),
                parameter_type,
                false,
                false,
            )],
            parameter_type,
        );
        let number = table.number();
        let string = table.string();
        let concrete = table.function(vec![number], string);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(generic, concrete));
        assert!(!relations.assignable(concrete, generic));
        assert!(relations.comparable(generic, concrete));
    }

    #[test]
    fn intersection_uses_type_parameter_constraint_for_object_view() {
        let mut table = TypeTable::new();
        let number = table.number();
        let constraint = table.object_type(vec![PropertyType::new("value", false, number)]);
        let constrained_symbol = SymbolId::new(701);
        table.set_type_parameter_constraint(constrained_symbol, constraint);
        let constrained = table.named(constrained_symbol);
        let unconstrained = table.named(SymbolId::new(702));
        let error = table.error_type();
        let constrained_intersection = table.intersection(vec![error, constrained]);
        let unconstrained_intersection = table.intersection(vec![error, unconstrained]);
        let propertyless = table.object_type(Vec::new());
        let error_constrained_symbol = SymbolId::new(703);
        table.set_type_parameter_constraint(error_constrained_symbol, error);
        let error_constrained = table.named(error_constrained_symbol);
        let recovery_intersection = table.intersection(vec![error, error_constrained]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(constrained_intersection, propertyless));
        assert!(relations.assignable(propertyless, recovery_intersection));
        assert!(!relations.assignable(unconstrained_intersection, propertyless));
    }

    #[test]
    fn functions_are_contravariant_in_params_covariant_in_return() {
        let mut table = TypeTable::new();
        let number = table.number();
        let void = table.void();
        let one = table.number_literal("1");
        let two = table.number_literal("2");
        let takes_number = table.function(vec![number], void);
        let takes_literal = table.function(vec![one], void);
        let takes_none = table.function(Vec::new(), void);
        let returns_number = table.function(Vec::new(), number);
        let returns_literal = table.function(Vec::new(), two);
        let relations = TypeRelations::new(&table);

        // Contravariant parameter: the general target parameter cannot feed the
        // narrower source parameter.
        assert!(!relations.subtype(takes_literal, takes_number));
        assert!(relations.subtype(takes_number, takes_literal));
        // Fewer source parameters is genuine subtyping, kept in strict mode.
        assert!(relations.subtype(takes_none, takes_number));
        assert!(!relations.subtype(takes_number, takes_none));
        // Covariant return, plus `void` absorption in both modes.
        assert!(relations.subtype(returns_literal, returns_number));
        assert!(!relations.subtype(returns_number, returns_literal));
        assert!(relations.subtype(returns_number, takes_none));
    }

    #[test]
    fn method_parameters_are_bivariant_but_function_properties_are_not() {
        let mut table = TypeTable::new();
        let number = table.number();
        let literal = table.number_literal("1");
        let void = table.void();
        let takes_number = table.function(vec![number], void);
        let takes_literal = table.function(vec![literal], void);
        let narrow_method = table.object_type(vec![
            PropertyType::new("accept", false, takes_literal).with_method(true),
        ]);
        let broad_method = table.object_type(vec![
            PropertyType::new("accept", false, takes_number).with_method(true),
        ]);
        let narrow_property =
            table.object_type(vec![PropertyType::new("accept", false, takes_literal)]);
        let broad_property =
            table.object_type(vec![PropertyType::new("accept", false, takes_number)]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(narrow_method, broad_method));
        assert!(relations.assignable(broad_method, narrow_method));
        assert!(!relations.assignable(narrow_property, broad_property));
        assert!(relations.assignable(broad_property, narrow_property));
    }

    #[test]
    fn instantiated_method_constraints_are_bivariant_within_one_declaration() {
        let mut table = TypeTable::new();
        let parameter = SymbolId::new(401);
        let distinct_parameter = SymbolId::new(402);
        let parameter_type = table.named(parameter);
        let distinct_type = table.named(distinct_parameter);
        let number = table.number();
        let literal = table.number_literal("1");
        let void = table.void();
        let source = table.function_with_parameter_bounds(
            vec![parameter],
            vec![TypeParameterBounds::new(Some(literal), None)],
            vec![FunctionParameter::new(
                "value".to_owned(),
                parameter_type,
                false,
                false,
            )],
            void,
            false,
        );
        let target = table.function_with_parameter_bounds(
            vec![parameter],
            vec![TypeParameterBounds::new(Some(number), None)],
            vec![FunctionParameter::new(
                "value".to_owned(),
                parameter_type,
                false,
                false,
            )],
            void,
            false,
        );
        let distinct_target = table.function_with_parameter_bounds(
            vec![distinct_parameter],
            vec![TypeParameterBounds::new(Some(number), None)],
            vec![FunctionParameter::new(
                "value".to_owned(),
                distinct_type,
                false,
                false,
            )],
            void,
            false,
        );
        let source_method = table.object_type(vec![
            PropertyType::new("accept", false, source).with_method(true),
        ]);
        let target_method = table.object_type(vec![
            PropertyType::new("accept", false, target).with_method(true),
        ]);
        let distinct_target_method = table.object_type(vec![
            PropertyType::new("accept", false, distinct_target).with_method(true),
        ]);
        let source_property = table.object_type(vec![PropertyType::new("accept", false, source)]);
        let target_property = table.object_type(vec![PropertyType::new("accept", false, target)]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(source_method, target_method));
        assert!(!relations.assignable(source_method, distinct_target_method));
        assert!(!relations.assignable(source_property, target_property));
    }

    #[test]
    fn method_overloads_require_target_coverage_and_covariant_returns() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let literal = table.number_literal("1");
        let void = table.void();
        let number_source = table.function(vec![number], void);
        let string_source = table.function(vec![string], void);
        let full_source = table.intersection_ordered(vec![number_source, string_source]);
        let literal_target = table.function(vec![literal], void);
        let string_target = table.function(vec![string], void);
        let target_overloads = table.intersection_ordered(vec![literal_target, string_target]);
        let missing = table.object_type(vec![
            PropertyType::new("accept", false, number_source).with_method(true),
        ]);
        let full = table.object_type(vec![
            PropertyType::new("accept", false, full_source).with_method(true),
        ]);
        let target = table.object_type(vec![
            PropertyType::new("accept", false, target_overloads).with_method(true),
        ]);
        let bad_return = table.function(vec![number], number);
        let literal_return = table.function(vec![literal], literal);
        let bad_return_source = table.object_type(vec![
            PropertyType::new("accept", false, bad_return).with_method(true),
        ]);
        let literal_return_target = table.object_type(vec![
            PropertyType::new("accept", false, literal_return).with_method(true),
        ]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(missing, target));
        assert!(relations.assignable(full, target));
        assert!(!relations.assignable(bad_return_source, literal_return_target));
    }

    /// Builds a pure callable object type from call signatures.
    fn callable_object(table: &mut TypeTable, call_signatures: Vec<FunctionSignature>) -> TypeId {
        table.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures,
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        })
    }

    /// Extracts the signature of an interned function type.
    fn signature_of(table: &TypeTable, id: TypeId) -> FunctionSignature {
        match table.get(id) {
            Type::Function(signature) => signature.clone(),
            _ => panic!("helper requires a function type"),
        }
    }

    /// Wraps a type as a method property of an object type.
    fn as_method(table: &mut TypeTable, type_id: TypeId) -> TypeId {
        table.object_type(vec![
            PropertyType::new("accept", false, type_id).with_method(true),
        ])
    }

    #[test]
    fn pure_callable_object_methods_are_bivariant() {
        let mut table = TypeTable::new();
        let number = table.number();
        let literal = table.number_literal("1");
        let void = table.void();
        let narrow_function = table.function(vec![literal], void);
        let broad_function = table.function(vec![number], void);
        let narrow_signature = signature_of(&table, narrow_function);
        let broad_signature = signature_of(&table, broad_function);
        let narrow = callable_object(&mut table, vec![narrow_signature]);
        let broad = callable_object(&mut table, vec![broad_signature]);
        let narrow_method = as_method(&mut table, narrow);
        let broad_method = as_method(&mut table, broad);
        let relations = TypeRelations::new(&table);

        // Method properties flatten through the view and relate bivariantly.
        assert!(relations.assignable(narrow_method, broad_method));
        assert!(relations.assignable(broad_method, narrow_method));
        // Ordinary callable objects keep plain contravariance.
        assert!(!relations.assignable(narrow, broad));
        assert!(relations.assignable(broad, narrow));
    }

    #[test]
    fn pure_callable_object_methods_require_target_coverage_and_covariant_returns() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let literal = table.number_literal("1");
        let void = table.void();
        let number_function = table.function(vec![number], void);
        let string_function = table.function(vec![string], void);
        let literal_function = table.function(vec![literal], void);
        let number_return_function = table.function(vec![number], number);
        let literal_return_function = table.function(vec![literal], literal);
        let number_signature = signature_of(&table, number_function);
        let string_signature = signature_of(&table, string_function);
        let literal_signature = signature_of(&table, literal_function);
        let number_return = signature_of(&table, number_return_function);
        let literal_return = signature_of(&table, literal_return_function);
        let full_source = callable_object(
            &mut table,
            vec![number_signature.clone(), string_signature.clone()],
        );
        let missing_source = callable_object(&mut table, vec![number_signature.clone()]);
        let target_overloads =
            callable_object(&mut table, vec![literal_signature, string_signature]);
        let bad_return_source = callable_object(&mut table, vec![number_return]);
        let literal_return_target = callable_object(&mut table, vec![literal_return]);
        let missing = as_method(&mut table, missing_source);
        let full = as_method(&mut table, full_source);
        let target = as_method(&mut table, target_overloads);
        let bad_return = as_method(&mut table, bad_return_source);
        let literal_returns = as_method(&mut table, literal_return_target);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(missing, target));
        assert!(relations.assignable(full, target));
        assert!(!relations.assignable(bad_return, literal_returns));
    }

    #[test]
    fn mixed_callable_method_properties_do_not_take_the_overload_path() {
        let mut table = TypeTable::new();
        let string = table.string();
        let word = table.string_literal("s");
        let void = table.void();
        let string_function = table.function(vec![string], void);
        let word_function = table.function(vec![word], void);
        let string_signature = signature_of(&table, string_function);
        // `{ (x: string) => void; extra: string }` is a mixed callable, so
        // the overload view is `None` for it.
        let mixed = table.object_type_with_members(ObjectType {
            properties: vec![PropertyType::new("extra", false, string)],
            call_signatures: vec![string_signature],
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        });
        let mixed_method = as_method(&mut table, mixed);
        let word_method = as_method(&mut table, word_function);
        let relations = TypeRelations::new(&table);

        // Mixed source still relates structurally: its call signature
        // accepts the target's argument contravariantly.
        assert!(relations.assignable(mixed_method, word_method));
        // The bivariant-only direction must not flow through the mixed
        // object: the structural path rejects the required `extra` member
        // and the overload view is `None`.
        assert!(!relations.assignable(word_method, mixed_method));
    }

    #[test]
    fn intersection_embedded_pure_group_flattens_through_the_view() {
        let mut table = TypeTable::new();
        let number = table.number();
        let boolean = table.boolean();
        let word = table.string_literal("s");
        let void = table.void();
        let number_function = table.function(vec![number], void);
        let word_function = table.function(vec![word], void);
        let boolean_function = table.function(vec![boolean], void);
        let number_signature = signature_of(&table, number_function);
        let word_signature = signature_of(&table, word_function);
        let boolean_signature = signature_of(&table, boolean_function);
        // A pure callable group with a non-identity candidate order embeds
        // next to a plain function member.
        let group = callable_object(
            &mut table,
            vec![number_signature.clone(), word_signature.clone()],
        );
        let ordered = table.with_call_candidate_order(group, vec![1, 0]);
        let with_function = table.intersection_ordered(vec![ordered, boolean_function]);
        let without_function = table.intersection_ordered(vec![ordered, word_function]);
        let target_all = callable_object(
            &mut table,
            vec![boolean_signature, word_signature, number_signature],
        );
        let with = as_method(&mut table, with_function);
        let without = as_method(&mut table, without_function);
        let target = as_method(&mut table, target_all);
        let relations = TypeRelations::new(&table);

        // The group and the function member both flatten into the view in
        // declaration order, so the boolean overload is covered through the
        // bivariant method path while the structural intersection path
        // drops the function member and fails.
        assert!(relations.assignable(with, target));
        // Without the function member the boolean overload is uncovered.
        assert!(!relations.assignable(without, target));
    }

    #[test]
    fn supertype_and_equivalent_are_derived_from_subtype() {
        let mut table = TypeTable::new();
        let number = table.number();
        let literal = table.number_literal("1");
        let left = table.named(SymbolId::new(300));
        let right = table.named(SymbolId::new(301));
        let relations = TypeRelations::new(&table);

        assert!(relations.supertype(number, literal));
        assert!(!relations.supertype(literal, number));
        assert!(relations.equivalent(number, number));
        assert!(!relations.equivalent(number, literal));
        // Distinct named types are nominal: neither direction relates.
        assert!(!relations.equivalent(left, right));
        assert!(relations.equivalent(left, left));
    }

    #[test]
    fn repeated_queries_hit_the_cache_without_growing_it() {
        let mut table = TypeTable::new();
        let number = table.number();
        let one = table.number_literal("1");
        let inner = table.array(number);
        let outer = table.array(inner);
        let literal_inner = table.array(one);
        let literal_outer = table.array(literal_inner);
        let relations = TypeRelations::new(&table);

        // Identity short-circuits before the cache is consulted.
        assert!(relations.assignable(outer, outer));
        assert_eq!(relations.cached_pairs(), 0);
        // The first distinct query memoizes both the root and completed nested
        // structural subproblems under their active assumption paths.
        assert!(relations.assignable(literal_outer, outer));
        let grown = relations.cached_pairs();
        assert!(grown > 1);
        // Repeating the same pair returns the identical result from the cache.
        assert!(relations.assignable(literal_outer, outer));
        assert_eq!(relations.cached_pairs(), grown);
        // The strict mode memoizes under separate relation keys.
        assert!(relations.subtype(literal_outer, outer));
        let after_strict = relations.cached_pairs();
        assert!(after_strict > grown);
        assert!(relations.subtype(literal_outer, outer));
        assert_eq!(relations.cached_pairs(), after_strict);
    }

    #[test]
    fn cache_is_bounded_and_results_stay_deterministic() {
        // 100 distinct array-of-literal types yield 9900 ordered pairs, far
        // beyond the cache capacity.
        let mut table = TypeTable::new();
        let arrays: Vec<TypeId> = (0..100)
            .map(|index| {
                let literal = table.number_literal(&index.to_string());
                table.array(literal)
            })
            .collect();
        let relations = TypeRelations::new(&table);
        for &source in &arrays {
            for &target in &arrays {
                let expected = source == target;
                assert_eq!(relations.assignable(source, target), expected);
            }
        }
        assert!(relations.cached_pairs() <= RELATION_CACHE_CAPACITY);

        // A fresh relation engine over the same table computes identical
        // results, proving the cache never influences outcomes.
        let fresh = TypeRelations::new(&table);
        for &source in &arrays {
            for &target in &arrays {
                let expected = source == target;
                assert_eq!(fresh.assignable(source, target), expected);
                assert_eq!(relations.assignable(source, target), expected);
            }
        }
    }

    #[test]
    fn union_distributes_before_strict_null_leaf() {
        // Under StrictNull, a union target must be checked before the scalar
        // strict-null leaf. Old order: (Undefined, _) matched before
        // (_, Type::Union) and rejected `undefined -> number|undefined`.
        let mut table = TypeTable::new();
        let number = table.number();
        let undefined = table.undefined_type();
        let null = table.null_type();
        let union_undefined = table.union(&[number, undefined]);
        let union_null = table.union(&[number, null]);
        let string = table.string();
        let union_number_only = table.union(&[number, string]);
        let relations = TypeRelations::new(&table);
        // Scalar undefined/null must flow into a union that contains it (strict mode)
        assert!(relations.assignable_with_strict_null(undefined, union_undefined));
        assert!(relations.assignable_with_strict_null(null, union_null));
        // But not into a union that does not contain it
        assert!(!relations.assignable_with_strict_null(undefined, union_number_only));
        assert!(!relations.assignable_with_strict_null(null, union_number_only));
    }

    #[test]
    fn function_arity_compares_required_to_required() {
        // A source requiring more than the target requires is too narrow,
        // even if the target could accept more via optional params.
        // Old: source_required > target_total (2 > 2 false, would pass)
        // New: source_required > target_required (2 > 1 true, correctly fails)
        let mut table = TypeTable::new();
        let number = table.number();
        let void = table.void();
        // target: (a: number, b?: number) => void  => required 1, total 2
        let target = table.function_with_parameters(
            vec![],
            vec![
                crate::checker::binder::FunctionParameter::new(
                    "a".to_string(),
                    number,
                    false,
                    false,
                ),
                crate::checker::binder::FunctionParameter::new(
                    "b".to_string(),
                    number,
                    true,
                    false,
                ),
            ],
            void,
        );
        // source: (a: number, b: number) => void  => required 2
        let source = table.function(vec![number, number], void);
        let relations = TypeRelations::new(&table);
        assert!(!relations.subtype(source, target));
        assert!(relations.subtype(target, source));
    }

    // --- AppliedClass variance tests (TypeScript 7.0.2 direction semantics) ---

    /// Helper: declare a generic class with one type parameter `T` and a raw
    /// object template, then publish it as final. Returns the parameter symbol.
    fn declare_generic_class(
        table: &mut TypeTable,
        class_symbol: SymbolId,
        param_symbol: SymbolId,
        raw: TypeId,
    ) {
        table.declare_class(class_symbol, vec![param_symbol]);
        table.finish_class_bounds(class_symbol, vec![TypeParameterBounds::NONE]);
        table.publish_final_class_template(class_symbol, raw);
    }

    /// `Producer<T> { value: T }` — covariant in T.
    /// `Producer<Dog> <: Producer<Animal>` but not the reverse.
    #[test]
    fn producer_is_covariant_in_its_type_parameter() {
        let mut table = TypeTable::new();
        let string = table.string();
        let animal = table.object_type(vec![PropertyType::new("name", false, string)]);
        let dog = table.object_type(vec![
            PropertyType::new("name", false, string),
            PropertyType::new("breed", false, string),
        ]);
        let producer = SymbolId::new(400);
        let t = SymbolId::new(401);
        let named_t = table.named(t);
        let raw = table.object_type(vec![PropertyType::new("value", false, named_t)]);
        declare_generic_class(&mut table, producer, t, raw);
        let producer_animal = table.applied_class(producer, vec![animal]);
        let producer_dog = table.applied_class(producer, vec![dog]);
        let relations = TypeRelations::new(&table);
        // Covariant: Dog <: Animal, so Producer<Dog> <: Producer<Animal>.
        assert!(relations.subtype(producer_dog, producer_animal));
        assert!(!relations.subtype(producer_animal, producer_dog));
        // Assignability follows the same direction.
        assert!(relations.assignable(producer_dog, producer_animal));
        assert!(!relations.assignable(producer_animal, producer_dog));
    }

    /// `Sink<T> { consume(value: T): void }` — contravariant in T.
    /// `Sink<Animal> <: Sink<Dog>` but not the reverse.
    #[test]
    fn sink_is_contravariant_in_its_type_parameter() {
        let mut table = TypeTable::new();
        let string = table.string();
        let void = table.void();
        let animal = table.object_type(vec![PropertyType::new("name", false, string)]);
        let dog = table.object_type(vec![
            PropertyType::new("name", false, string),
            PropertyType::new("breed", false, string),
        ]);
        let sink = SymbolId::new(410);
        let t = SymbolId::new(411);
        let named_t = table.named(t);
        let consume = table.function(vec![named_t], void);
        let raw = table.object_type(vec![PropertyType::new("consume", false, consume)]);
        declare_generic_class(&mut table, sink, t, raw);
        let sink_animal = table.applied_class(sink, vec![animal]);
        let sink_dog = table.applied_class(sink, vec![dog]);
        let relations = TypeRelations::new(&table);
        // Contravariant: Animal is a supertype of Dog, so Sink<Animal> <: Sink<Dog>.
        assert!(relations.subtype(sink_animal, sink_dog));
        assert!(!relations.subtype(sink_dog, sink_animal));
        assert!(relations.assignable(sink_animal, sink_dog));
        assert!(!relations.assignable(sink_dog, sink_animal));
    }

    /// `Cell<T> { value: T; set(value: T): void }` — invariant in T.
    /// Neither direction relates when the arguments differ.
    #[test]
    fn cell_is_invariant_in_its_type_parameter() {
        let mut table = TypeTable::new();
        let string = table.string();
        let void = table.void();
        let animal = table.object_type(vec![PropertyType::new("name", false, string)]);
        let dog = table.object_type(vec![
            PropertyType::new("name", false, string),
            PropertyType::new("breed", false, string),
        ]);
        let cell = SymbolId::new(420);
        let t = SymbolId::new(421);
        let named_t = table.named(t);
        let set = table.function(vec![named_t], void);
        let raw = table.object_type(vec![
            PropertyType::new("value", false, named_t),
            PropertyType::new("set", false, set),
        ]);
        declare_generic_class(&mut table, cell, t, raw);
        let cell_animal = table.applied_class(cell, vec![animal]);
        let cell_dog = table.applied_class(cell, vec![dog]);
        let relations = TypeRelations::new(&table);
        // Invariant: the covariant `value` and contravariant `set` cancel, so
        // neither direction relates when the arguments differ.
        assert!(!relations.subtype(cell_dog, cell_animal));
        assert!(!relations.subtype(cell_animal, cell_dog));
        assert!(!relations.assignable(cell_dog, cell_animal));
        assert!(!relations.assignable(cell_animal, cell_dog));
        // Identity still relates.
        assert!(relations.subtype(cell_dog, cell_dog));
    }

    /// `Phantom<T> { tag: number }` — T is unused, so the argument is
    /// irrelevant and all applications are mutually assignable.
    #[test]
    fn phantom_type_parameter_is_irrelevant() {
        let mut table = TypeTable::new();
        let string = table.string();
        let animal = table.object_type(vec![PropertyType::new("name", false, string)]);
        let dog = table.object_type(vec![
            PropertyType::new("name", false, string),
            PropertyType::new("breed", false, string),
        ]);
        let phantom = SymbolId::new(430);
        let t = SymbolId::new(431);
        let raw = table.object_type(vec![PropertyType::new("tag", false, table.number())]);
        declare_generic_class(&mut table, phantom, t, raw);
        let phantom_animal = table.applied_class(phantom, vec![animal]);
        let phantom_dog = table.applied_class(phantom, vec![dog]);
        let relations = TypeRelations::new(&table);
        // Phantom: T is unused, so both applications share the same view and
        // relate in both directions.
        assert!(relations.subtype(phantom_dog, phantom_animal));
        assert!(relations.subtype(phantom_animal, phantom_dog));
        assert!(relations.assignable(phantom_dog, phantom_animal));
        assert!(relations.assignable(phantom_animal, phantom_dog));
    }

    /// AppliedClass instances relate structurally across class symbols and flow
    /// into the non-primitive object top type.
    #[test]
    fn applied_classes_are_structural_and_flow_into_object_top() {
        let mut table = TypeTable::new();
        let foo = SymbolId::new(440);
        let t = SymbolId::new(441);
        let named_t = table.named(t);
        let foo_raw = table.object_type(vec![PropertyType::new("x", false, named_t)]);
        declare_generic_class(&mut table, foo, t, foo_raw);
        let bar = SymbolId::new(450);
        let u = SymbolId::new(451);
        let named_u = table.named(u);
        let bar_raw = table.object_type(vec![PropertyType::new("x", false, named_u)]);
        declare_generic_class(&mut table, bar, u, bar_raw);
        let string = table.string();
        let number = table.number();
        let foo_string = table.applied_class(foo, vec![string]);
        let bar_string = table.applied_class(bar, vec![string]);
        let bar_number = table.applied_class(bar, vec![number]);
        let object = table.object();
        let relations = TypeRelations::new(&table);

        assert!(relations.subtype(foo_string, object));
        assert!(relations.subtype(foo_string, bar_string));
        assert!(relations.subtype(bar_string, foo_string));
        assert!(!relations.subtype(bar_number, foo_string));
    }

    /// Nested applications relate through their own substituted views.
    #[test]
    fn nested_applied_class_heads_relate_without_precreated_concrete_views() {
        let mut table = TypeTable::new();
        let string = table.string();
        let animal = table.object_type(vec![PropertyType::new("name", false, string)]);
        let dog = table.object_type(vec![
            PropertyType::new("name", false, string),
            PropertyType::new("breed", false, string),
        ]);
        let inner = SymbolId::new(460);
        let t_inner = SymbolId::new(461);
        let named_inner = table.named(t_inner);
        let inner_raw = table.object_type(vec![PropertyType::new("value", false, named_inner)]);
        declare_generic_class(&mut table, inner, t_inner, inner_raw);
        let outer = SymbolId::new(470);
        let t_outer = SymbolId::new(471);
        let named_outer = table.named(t_outer);
        let applied_inner = table.applied_class(inner, vec![named_outer]);
        let outer_raw = table.object_type(vec![PropertyType::new("child", false, applied_inner)]);
        declare_generic_class(&mut table, outer, t_outer, outer_raw);
        let outer_animal = table.applied_class(outer, vec![animal]);
        let outer_dog = table.applied_class(outer, vec![dog]);
        let relations = TypeRelations::new(&table);

        assert!(relations.subtype(outer_dog, outer_animal));
        assert!(!relations.subtype(outer_animal, outer_dog));
    }

    #[test]
    fn recursive_applied_classes_use_argument_sensitive_pair_keys() {
        let mut table = TypeTable::new();
        let box_symbol = SymbolId::new(480);
        let t = SymbolId::new(481);
        table.declare_class(box_symbol, vec![t]);
        table.finish_class_bounds(box_symbol, vec![TypeParameterBounds::NONE]);
        let named_t = table.named(t);
        let recursive = table.applied_class(box_symbol, vec![named_t]);
        let raw = table.object_type(vec![
            PropertyType::new("value", false, named_t),
            PropertyType::new("next", false, recursive),
        ]);
        table.publish_final_class_template(box_symbol, raw);
        let one = table.number_literal("1");
        let number = table.number();
        let box_one = table.applied_class(box_symbol, vec![one]);
        let box_number = table.applied_class(box_symbol, vec![number]);
        let relations = TypeRelations::new(&table);

        assert!(relations.subtype(box_one, box_number));
        assert!(!relations.subtype(box_number, box_one));
    }

    #[test]
    fn applied_classes_with_private_members_require_same_origin() {
        use crate::syntax::Accessibility;

        let mut table = TypeTable::new();
        let left = SymbolId::new(490);
        let left_t = SymbolId::new(491);
        let named_left = table.named(left_t);
        let left_raw = table.object_type(vec![
            PropertyType::new("value", false, named_left)
                .with_accessibility(Accessibility::Private, Some(left)),
        ]);
        declare_generic_class(&mut table, left, left_t, left_raw);
        let right = SymbolId::new(492);
        let right_t = SymbolId::new(493);
        let named_right = table.named(right_t);
        let right_raw = table.object_type(vec![
            PropertyType::new("value", false, named_right)
                .with_accessibility(Accessibility::Private, Some(right)),
        ]);
        declare_generic_class(&mut table, right, right_t, right_raw);
        let number = table.number();
        let left_number = table.applied_class(left, vec![number]);
        let right_number = table.applied_class(right, vec![number]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(left_number, left_number));
        assert!(!relations.assignable(left_number, right_number));
        assert!(!relations.assignable(right_number, left_number));
    }

    #[test]
    fn object_literal_satisfies_class_with_public_member() {
        use crate::syntax::Accessibility;
        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(500);
        table.declare_class(class_symbol, Vec::new());
        let raw = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Public, Some(class_symbol)),
        ]);
        table.publish_final_class_template(class_symbol, raw);
        let class = table.applied_class(class_symbol, Vec::new());
        let literal = table.object_type(vec![PropertyType::new("x", false, number)]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(literal, class));
        assert!(relations.subtype(literal, class));
    }

    #[test]
    fn object_literal_cannot_satisfy_class_by_private_member() {
        use crate::syntax::Accessibility;
        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(501);
        table.declare_class(class_symbol, Vec::new());
        let raw = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(class_symbol)),
        ]);
        table.publish_final_class_template(class_symbol, raw);
        let class = table.applied_class(class_symbol, Vec::new());
        let literal = table.object_type(vec![PropertyType::new("x", false, number)]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(literal, class));
        assert!(!relations.subtype(literal, class));
    }

    #[test]
    fn object_literal_cannot_satisfy_class_by_protected_member() {
        use crate::syntax::Accessibility;
        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(502);
        table.declare_class(class_symbol, Vec::new());
        let raw = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Protected, Some(class_symbol)),
        ]);
        table.publish_final_class_template(class_symbol, raw);
        let class = table.applied_class(class_symbol, Vec::new());
        let literal = table.object_type(vec![PropertyType::new("x", false, number)]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(literal, class));
        assert!(!relations.subtype(literal, class));
    }

    #[test]
    fn class_private_member_requires_same_declaring_origin() {
        use crate::syntax::Accessibility;
        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(503);
        let other_symbol = SymbolId::new(504);
        table.declare_class(class_symbol, Vec::new());
        table.declare_class(other_symbol, Vec::new());
        let raw = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(class_symbol)),
        ]);
        table.publish_final_class_template(class_symbol, raw);
        let class = table.applied_class(class_symbol, Vec::new());
        let mimic = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(other_symbol)),
        ]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(mimic, class));
        assert!(!relations.subtype(mimic, class));
    }

    #[test]
    fn optional_source_property_rejects_required_target() {
        let mut table = TypeTable::new();
        let number = table.number();
        let optional_source = table.object_type(vec![
            PropertyType::new("x", true, number),
            PropertyType::new("y", false, number),
        ]);
        let required_target = table.object_type(vec![PropertyType::new("x", false, number)]);
        let optional_target = table.object_type(vec![PropertyType::new("x", true, number)]);
        let required_source = table.object_type(vec![PropertyType::new("x", false, number)]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(optional_source, required_target));
        assert!(!relations.subtype(optional_source, required_target));
        assert!(!relations.assignable_with_strict_null(optional_source, required_target));
        assert!(relations.assignable(optional_source, optional_target));
        assert!(relations.subtype(optional_source, optional_target));
        assert!(relations.assignable(required_source, optional_target));
        assert!(relations.subtype(required_source, optional_target));
    }

    #[test]
    fn public_target_requires_public_source() {
        use crate::syntax::Accessibility;

        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(510);
        table.declare_class(class_symbol, Vec::new());
        let public_target = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Public, Some(class_symbol)),
        ]);
        let private_source = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(class_symbol)),
            PropertyType::new("y", false, number),
        ]);
        let public_source = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Public, Some(class_symbol)),
            PropertyType::new("y", false, number),
        ]);
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(private_source, public_target));
        assert!(!relations.subtype(private_source, public_target));
        assert!(relations.assignable(public_source, public_target));
        assert!(relations.subtype(public_source, public_target));
    }

    #[test]
    fn same_private_origin_still_compatible() {
        use crate::syntax::Accessibility;

        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(511);
        table.declare_class(class_symbol, Vec::new());
        let source = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(class_symbol)),
            PropertyType::new("y", false, number),
        ]);
        let target = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Private, Some(class_symbol)),
        ]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(source, target));
        assert!(relations.subtype(source, target));
    }

    #[test]
    fn protected_source_requires_same_origin_and_rejects_public_target() {
        use crate::syntax::Accessibility;

        let mut table = TypeTable::new();
        let number = table.number();
        let class_symbol = SymbolId::new(512);
        let other_symbol = SymbolId::new(513);
        table.declare_class(class_symbol, Vec::new());
        table.declare_class(other_symbol, Vec::new());
        let protected_target = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Protected, Some(class_symbol)),
        ]);
        let protected_source = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Protected, Some(class_symbol)),
            PropertyType::new("y", false, number),
        ]);
        let wrong_origin = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Protected, Some(other_symbol)),
        ]);
        let public_target = table.object_type(vec![
            PropertyType::new("x", false, number)
                .with_accessibility(Accessibility::Public, Some(class_symbol)),
        ]);
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(protected_source, protected_target));
        assert!(relations.subtype(protected_source, protected_target));
        assert!(!relations.assignable(wrong_origin, protected_target));
        assert!(!relations.subtype(wrong_origin, protected_target));
        assert!(!relations.assignable(protected_source, public_target));
        assert!(!relations.subtype(protected_source, public_target));
    }

    #[test]
    fn optional_tuple_accepts_every_source_length_and_checks_present_values() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let empty = table.tuple(Vec::new());
        let optional_number = table.tuple_shape(TupleShape {
            prefix: vec![number],
            required: 0,
            rest: None,
            suffix: Vec::new(),
        });
        let optional_string = table.tuple_shape(TupleShape {
            prefix: vec![string],
            required: 0,
            rest: None,
            suffix: Vec::new(),
        });
        let relations = TypeRelations::new(&table);

        assert!(relations.assignable(empty, optional_number));
        assert!(!relations.assignable(optional_number, empty));
        assert!(!relations.assignable(optional_number, optional_string));
    }

    #[test]
    fn tuple_relation_checks_required_positions_and_movable_suffixes() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let boolean = table.boolean();
        let empty = table.tuple(Vec::new());
        let required_number = table.tuple(vec![number]);
        let string_suffix = table.tuple_shape(TupleShape {
            prefix: Vec::new(),
            required: 0,
            rest: Some(number),
            suffix: vec![string],
        });
        let boolean_suffix = table.tuple_shape(TupleShape {
            prefix: Vec::new(),
            required: 0,
            rest: Some(number),
            suffix: vec![boolean],
        });
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(empty, required_number));
        assert!(!relations.assignable(string_suffix, boolean_suffix));
    }

    #[test]
    fn tuple_relation_preserves_layout_correlation() {
        let mut table = TypeTable::new();
        let a = table.number();
        let b = table.string();
        let c = table.boolean();
        let source = table.tuple(vec![c, b]);
        let target = table.tuple_shape(TupleShape {
            prefix: vec![a, b],
            required: 0,
            rest: Some(c),
            suffix: Vec::new(),
        });
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(source, target));
    }

    #[test]
    fn alias_guard_context_normalizes_local_binders_and_retains_captures() {
        let mut table = TypeTable::new();
        let source_class = SymbolId::new(800);
        let source_parameter = SymbolId::new(801);
        let source_parameter_type = table.named(source_parameter);
        let source_raw = table.object_type(vec![PropertyType::new(
            "value",
            false,
            source_parameter_type,
        )]);
        declare_generic_class(&mut table, source_class, source_parameter, source_raw);
        let target_class = SymbolId::new(802);
        let target_parameter = SymbolId::new(803);
        let target_parameter_type = table.named(target_parameter);
        let target_raw = table.object_type(vec![PropertyType::new(
            "value",
            false,
            target_parameter_type,
        )]);
        declare_generic_class(&mut table, target_class, target_parameter, target_raw);

        let outer_source = SymbolId::new(804);
        let outer_target = SymbolId::new(805);
        let inner_source = SymbolId::new(806);
        let inner_target = SymbolId::new(807);
        let outer_source_type = table.named(outer_source);
        let outer_target_type = table.named(outer_target);
        let inner_source_type = table.named(inner_source);
        let inner_target_type = table.named(inner_target);
        let outer_source_head = table.applied_class(source_class, vec![outer_source_type]);
        let outer_target_head = table.applied_class(target_class, vec![outer_target_type]);
        let inner_source_head = table.applied_class(source_class, vec![inner_source_type]);
        let inner_target_head = table.applied_class(target_class, vec![inner_target_type]);

        let captured_source_class = SymbolId::new(808);
        table.declare_class(captured_source_class, Vec::new());
        let captured_source_raw = table.object_type(vec![PropertyType::new(
            "captured",
            false,
            outer_source_type,
        )]);
        table.publish_final_class_template(captured_source_class, captured_source_raw);
        let captured_source_head = table.applied_class(captured_source_class, Vec::new());
        let captured_target_class = SymbolId::new(809);
        table.declare_class(captured_target_class, Vec::new());
        let captured_target_raw = table.object_type(vec![PropertyType::new(
            "captured",
            false,
            outer_target_type,
        )]);
        table.publish_final_class_template(captured_target_class, captured_target_raw);
        let captured_target_head = table.applied_class(captured_target_class, Vec::new());

        let constrained_source = SymbolId::new(810);
        let constrained_target = SymbolId::new(811);
        table.set_type_parameter_constraint(constrained_source, outer_source_type);
        table.set_type_parameter_constraint(constrained_target, outer_target_type);
        let constrained_source_type = table.named(constrained_source);
        let constrained_target_type = table.named(constrained_target);
        let constrained_source_head =
            table.applied_class(source_class, vec![constrained_source_type]);
        let constrained_target_head =
            table.applied_class(target_class, vec![constrained_target_type]);

        let outer_source_signature =
            table.function_with_parameters(vec![outer_source], Vec::new(), table.void());
        let outer_target_signature =
            table.function_with_parameters(vec![outer_target], Vec::new(), table.void());
        let inner_source_signature =
            table.function_with_parameters(vec![inner_source], Vec::new(), table.void());
        let inner_target_signature =
            table.function_with_parameters(vec![inner_target], Vec::new(), table.void());
        let signature = |type_id| match table.get(type_id) {
            Type::Function(signature) => signature.clone(),
            _ => panic!("test fixture must be a function"),
        };
        let outer_source_signature = signature(outer_source_signature);
        let outer_target_signature = signature(outer_target_signature);
        let inner_source_signature = signature(inner_source_signature);
        let inner_target_signature = signature(inner_target_signature);
        let relations = TypeRelations::new(&table);

        let local = Cell::new(0);
        assert!(relations.with_parameter_aliases(
            &inner_source_signature,
            &inner_target_signature,
            Strictness::Assignable,
            ParameterVariance::Bivariant,
            || {
                local.set(relations.alias_relation_context(inner_source_head, inner_target_head));
                true
            },
        ));

        let nested_local = Cell::new(0);
        let captured_argument = Cell::new(0);
        let captured_template = Cell::new(0);
        let captured_constraint = Cell::new(0);
        assert!(relations.with_parameter_aliases(
            &outer_source_signature,
            &outer_target_signature,
            Strictness::Assignable,
            ParameterVariance::Bivariant,
            || relations.with_parameter_aliases(
                &inner_source_signature,
                &inner_target_signature,
                Strictness::Assignable,
                ParameterVariance::Bivariant,
                || {
                    nested_local.set(
                        relations.alias_relation_context(inner_source_head, inner_target_head),
                    );
                    captured_argument.set(
                        relations.alias_relation_context(outer_source_head, outer_target_head),
                    );
                    captured_template.set(
                        relations
                            .alias_relation_context(captured_source_head, captured_target_head),
                    );
                    captured_constraint.set(
                        relations.alias_relation_context(
                            constrained_source_head,
                            constrained_target_head,
                        ),
                    );
                    true
                },
            ),
        ));

        assert_eq!(nested_local.get(), local.get());
        for context_id in [
            captured_argument.get(),
            captured_template.get(),
            captured_constraint.get(),
        ] {
            assert_ne!(context_id, local.get());
            let contexts = relations.contexts.borrow();
            let context = contexts
                .iter()
                .find_map(|(context, &id)| (id == context_id).then_some(context))
                .expect("projected context is interned");
            assert_eq!(context.alpha_aliases, 1);
            assert_eq!(context.parameter_aliases.len(), 2);
        }
    }

    #[test]
    fn comparable_recursive_signatures_share_monotone_erasure_context() {
        const DEPTH: usize = 16;

        let mut table = TypeTable::new();
        let left_symbols: Vec<_> = (0..DEPTH)
            .map(|index| SymbolId::new(600 + index as u32))
            .collect();
        let right_symbols: Vec<_> = (0..DEPTH)
            .map(|index| SymbolId::new(620 + index as u32))
            .collect();
        let left_heads: Vec<_> = left_symbols
            .iter()
            .map(|&symbol| table.named(symbol))
            .collect();
        let right_heads: Vec<_> = right_symbols
            .iter()
            .map(|&symbol| table.named(symbol))
            .collect();
        let captured = SymbolId::new(682);
        let captured_type = table.named(captured);

        for index in 0..DEPTH {
            let next = (index + 1) % DEPTH;
            let left_parameter = if index == DEPTH / 2 {
                captured
            } else {
                SymbolId::new(640 + index as u32)
            };
            let right_parameter = SymbolId::new(660 + index as u32);
            let left_next =
                table.function_with_parameters(vec![left_parameter], Vec::new(), left_heads[next]);
            let right_next = table.function_with_parameters(
                vec![right_parameter],
                Vec::new(),
                right_heads[next],
            );
            let mut left_properties = vec![PropertyType::new("next", false, left_next)];
            let mut right_properties = vec![PropertyType::new("next", false, right_next)];
            if index == 0 {
                left_properties.push(PropertyType::new("value", false, captured_type));
                right_properties.push(PropertyType::new("value", false, table.number()));
            }
            let left_structure = table.object_type(left_properties);
            let right_structure = table.object_type(right_properties);
            table.set_interface_structure(left_symbols[index], left_structure);
            table.set_interface_structure(right_symbols[index], right_structure);
        }

        let root_left =
            table.function_with_parameters(vec![SymbolId::new(680)], Vec::new(), left_heads[0]);
        let root_right =
            table.function_with_parameters(vec![SymbolId::new(681)], Vec::new(), right_heads[0]);
        let captured_root_left =
            table.function_with_parameters(vec![captured], Vec::new(), left_heads[0]);
        let captured_root_right =
            table.function_with_parameters(vec![SymbolId::new(686)], Vec::new(), right_heads[0]);
        let captured_object =
            table.object_type(vec![PropertyType::new("value", false, captured_type)]);
        let number_object =
            table.object_type(vec![PropertyType::new("value", false, table.number())]);
        let unrelated_left =
            table.function_with_parameters(vec![SymbolId::new(683)], Vec::new(), table.void());
        let unrelated_right =
            table.function_with_parameters(vec![SymbolId::new(684)], Vec::new(), table.void());
        let captured_left =
            table.function_with_parameters(vec![captured], Vec::new(), table.void());
        let captured_right =
            table.function_with_parameters(vec![SymbolId::new(685)], Vec::new(), table.void());
        let signature = |type_id| match table.get(type_id) {
            Type::Function(signature) => signature.clone(),
            _ => panic!("test fixture must be a function"),
        };
        let unrelated_left = signature(unrelated_left);
        let unrelated_right = signature(unrelated_right);
        let captured_left = signature(captured_left);
        let captured_right = signature(captured_right);
        let captured_array = table.array(captured_object);
        let number_array = table.array(number_object);
        let relations = TypeRelations::new(&table);

        assert!(!relations.comparable(root_left, root_right));
        assert!(relations.comparable(captured_root_left, captured_root_right));
        assert_eq!(
            relations.contexts.borrow().len(),
            1,
            "nested erased signatures must share one recursive context"
        );
        let unrelated_before = relations.computed_relations();
        assert!(
            !relations.with_erased_parameters(&unrelated_left, &unrelated_right, || relations
                .relates(captured_object, number_object, Strictness::Comparable),)
        );
        let unrelated_after = relations.computed_relations();
        assert!(unrelated_after > unrelated_before);
        assert!(
            !relations.with_erased_parameters(&unrelated_left, &unrelated_right, || relations
                .relates(captured_object, number_object, Strictness::Comparable),)
        );
        assert_eq!(relations.computed_relations(), unrelated_after);
        assert!(
            relations.with_erased_parameters(&captured_left, &captured_right, || relations
                .relates(captured_object, number_object, Strictness::Comparable),)
        );
        let captured_after = relations.computed_relations();
        assert!(
            relations.with_erased_parameters(&captured_left, &captured_right, || relations
                .relates(captured_object, number_object, Strictness::Comparable),)
        );
        assert_eq!(relations.computed_relations(), captured_after);
        let reverse = TypeRelations::new(&table);
        assert!(
            reverse.with_erased_parameters(&captured_left, &captured_right, || reverse.relates(
                captured_object,
                number_object,
                Strictness::Comparable
            ),)
        );
        assert!(
            !reverse.with_erased_parameters(&unrelated_left, &unrelated_right, || reverse.relates(
                captured_object,
                number_object,
                Strictness::Comparable
            ),)
        );

        let dependency = TypeRelations::new(&table);
        assert!(
            !dependency.with_erased_parameters(&unrelated_left, &unrelated_right, || dependency
                .relates(captured_object, number_object, Strictness::Comparable),)
        );
        assert!(
            !dependency.with_erased_parameters(&unrelated_left, &unrelated_right, || dependency
                .relates(captured_array, number_array, Strictness::Comparable),)
        );
        assert!(
            dependency.with_erased_parameters(&captured_left, &captured_right, || dependency
                .relates(captured_array, number_array, Strictness::Comparable),)
        );
    }

    #[test]
    fn locally_introduced_erasure_reuses_cache_across_outer_scopes() {
        let mut table = TypeTable::new();
        let inner_source_symbol = SymbolId::new(700);
        let inner_target_symbol = SymbolId::new(701);
        let source_value = table.named(inner_source_symbol);
        let source_object =
            table.object_type(vec![PropertyType::new("value", false, source_value)]);
        let target_object =
            table.object_type(vec![PropertyType::new("value", false, table.number())]);
        let inner_source =
            table.function_with_parameters(vec![inner_source_symbol], Vec::new(), source_object);
        let inner_target =
            table.function_with_parameters(vec![inner_target_symbol], Vec::new(), target_object);
        let outer_a =
            table.function_with_parameters(vec![SymbolId::new(702)], Vec::new(), table.void());
        let outer_b =
            table.function_with_parameters(vec![SymbolId::new(703)], Vec::new(), table.void());
        let outer_c =
            table.function_with_parameters(vec![SymbolId::new(704)], Vec::new(), table.void());
        let outer_d =
            table.function_with_parameters(vec![SymbolId::new(705)], Vec::new(), table.void());
        let signature = |type_id| match table.get(type_id) {
            Type::Function(signature) => signature.clone(),
            _ => panic!("test fixture must be a function"),
        };
        let outer_a = signature(outer_a);
        let outer_b = signature(outer_b);
        let outer_c = signature(outer_c);
        let outer_d = signature(outer_d);
        let relations = TypeRelations::new(&table);

        assert!(relations.with_erased_parameters(&outer_a, &outer_b, || {
            relations.comparable(inner_source, inner_target)
        },));
        let computed = relations.computed_relations();
        assert!(relations.with_erased_parameters(&outer_c, &outer_d, || {
            relations.comparable(inner_source, inner_target)
        },));
        assert_eq!(
            relations.computed_relations(),
            computed,
            "locally introduced generic erasure must not bind a cache entry to its outer scope"
        );
    }

    #[test]
    fn relation_cache_bounds_erasure_variants_per_pair() {
        const SYMBOLS: usize = ERASURE_VARIANTS_PER_RELATION + 1;

        let mut table = TypeTable::new();
        let symbols: Vec<_> = (0..SYMBOLS)
            .map(|index| SymbolId::new(720 + index as u32))
            .collect();
        let source_properties = symbols
            .iter()
            .enumerate()
            .map(|(index, &symbol)| {
                PropertyType::new(format!("value{index}"), false, table.named(symbol))
            })
            .collect();
        let target_properties = (0..SYMBOLS)
            .map(|index| PropertyType::new(format!("value{index}"), false, table.number()))
            .collect();
        let source = table.object_type(source_properties);
        let target = table.object_type(target_properties);
        let mut scopes = Vec::new();
        for count in 0..=SYMBOLS {
            let source_parameters = if count == 0 {
                vec![SymbolId::new(800)]
            } else {
                symbols[..count].to_vec()
            };
            let target_parameters = (0..source_parameters.len())
                .map(|index| SymbolId::new(820 + count as u32 * 16 + index as u32))
                .collect();
            let left = table.function_with_parameters(source_parameters, Vec::new(), table.void());
            let right = table.function_with_parameters(target_parameters, Vec::new(), table.void());
            let Type::Function(left) = table.get(left).clone() else {
                panic!("test fixture must be a function");
            };
            let Type::Function(right) = table.get(right).clone() else {
                panic!("test fixture must be a function");
            };
            scopes.push((left, right));
        }
        let relations = TypeRelations::new(&table);

        for (left, right) in &scopes {
            let _ = relations.with_erased_parameters(left, right, || {
                relations.relates(source, target, Strictness::Comparable)
            });
        }
        let variants = relations
            .cache
            .borrow()
            .iter()
            .filter(|(key, _)| {
                key.source == source
                    && key.target == target
                    && key.strictness == Strictness::Comparable
            })
            .map(|(_, entries)| entries.len())
            .sum::<usize>();
        assert_eq!(variants, ERASURE_VARIANTS_PER_RELATION);
    }

    #[test]
    fn recursive_generic_constraint_memoizes_under_polymorphic_this_aliases() {
        let mut table = TypeTable::new();
        let class = SymbolId::new(510);
        let class_value = SymbolId::new(511);
        let class_leaf = SymbolId::new(512);
        table.declare_class(class, vec![class_value, class_leaf]);
        table.finish_class_bounds(
            class,
            vec![TypeParameterBounds::NONE, TypeParameterBounds::NONE],
        );
        let value = table.named(class_value);
        let leaf = table.named(class_leaf);
        let recursive = table.applied_class(class, vec![value, leaf]);
        let recursive_this = table.this_type(class, recursive);
        let mut properties: Vec<PropertyType> = (0..64)
            .map(|index| PropertyType::new(format!("edge{index}"), false, recursive_this))
            .collect();
        properties.push(PropertyType::new("leaf", false, leaf));
        let template = table.object_type(properties);
        table.publish_final_class_template(class, template);

        let source_parameter = SymbolId::new(513);
        let target_parameter = SymbolId::new(514);
        let source_value = table.named(source_parameter);
        let target_value = table.named(target_parameter);
        let source_bound = table.applied_class(class, vec![source_value, table.number()]);
        let target_bound = table.applied_class(class, vec![target_value, table.string()]);
        let parent_source = table.array(source_bound);
        let parent_target = table.array(target_bound);
        let source = table.function_with_parameter_bounds(
            vec![source_parameter],
            vec![TypeParameterBounds::new(Some(source_bound), None)],
            Vec::new(),
            table.void(),
            false,
        );
        let target = table.function_with_parameter_bounds(
            vec![target_parameter],
            vec![TypeParameterBounds::new(Some(target_bound), None)],
            Vec::new(),
            table.void(),
            false,
        );
        let relations = TypeRelations::new(&table);

        assert!(!relations.assignable(source, target));
        assert!(relations.cached_pairs() > 0);
        assert!(
            relations.computed_relations() < 24,
            "recursive constraint relation expanded {} uncached pairs",
            relations.computed_relations()
        );

        let parent_relation = RelationKey {
            source: parent_source,
            target: parent_target,
            strictness: Strictness::Assignable,
            context: 0,
        };
        let child_relation = RelationKey {
            source: source_bound,
            target: target_bound,
            strictness: Strictness::Assignable,
            context: 0,
        };
        let dummy_relation = RelationKey {
            source,
            target,
            strictness: Strictness::Strict,
            context: 0,
        };
        relations.visiting.borrow_mut().insert(dummy_relation);
        relations
            .dependency_stack
            .borrow_mut()
            .push(DependencyFrame::new(0));
        assert!(!relations.assignable(parent_source, parent_target));
        relations.dependency_stack.borrow_mut().pop();
        relations.visiting.borrow_mut().remove(&dummy_relation);
        assert!(
            !relations.cache.borrow().contains_key(&parent_relation),
            "a cycle-dependent false nested result must not become universal"
        );

        relations.visiting.borrow_mut().insert(child_relation);
        relations
            .dependency_stack
            .borrow_mut()
            .push(DependencyFrame::new(0));
        assert!(relations.assignable(parent_source, parent_target));
        relations.dependency_stack.borrow_mut().pop();
        relations.visiting.borrow_mut().remove(&child_relation);
    }

    // --- Generic function inference tests ---

    /// `<T>(x: T) => T[]` is assignable to `(x: number) => number[]` because
    /// TypeScript infers `T = number` from the parameter and the instantiated
    /// return type matches. Without inference the unconstrained `T` would
    /// fall to `unknown` and the return check would fail.
    #[test]
    fn generic_function_infers_type_arguments_from_non_generic_target() {
        let mut table = TypeTable::new();
        let number = table.number();
        let t = SymbolId::new(600);
        let named_t = table.named(t);
        let number_array = table.array(number);
        let t_array = table.array(named_t);
        let source = table.function_with_parameter_bounds(
            vec![t],
            vec![TypeParameterBounds::NONE],
            vec![FunctionParameter::new(
                "x".to_string(),
                named_t,
                false,
                false,
            )],
            t_array,
            false,
        );
        let target = table.function(vec![number], number_array);
        let relations = TypeRelations::new(&table);
        assert!(
            relations.assignable(source, target),
            "generic <T>(x: T) => T[] should be assignable to (x: number) => number[]"
        );
    }

    /// `<T>(x: T) => T` is NOT assignable to `(x: number) => string` because
    /// after inferring `T = number`, the return type `number` is not
    /// assignable to `string`. This guards against the erasure-as-any
    /// over-approximation.
    #[test]
    fn generic_function_inference_catches_return_type_mismatch() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let t = SymbolId::new(610);
        let named_t = table.named(t);
        let source = table.function_with_parameter_bounds(
            vec![t],
            vec![TypeParameterBounds::NONE],
            vec![FunctionParameter::new(
                "x".to_string(),
                named_t,
                false,
                false,
            )],
            named_t,
            false,
        );
        let target = table.function(vec![number], string);
        let relations = TypeRelations::new(&table);
        assert!(
            !relations.assignable(source, target),
            "generic <T>(x: T) => T should NOT be assignable to (x: number) => string"
        );
    }

    /// A non-generic function is assignable to a generic target when the
    /// source satisfies the type parameter's constraint. `(x: number) => number`
    /// is assignable to `<T>(x: T) => T` because `number` is assignable to
    /// the implicit `unknown` constraint.
    #[test]
    fn non_generic_function_assignable_to_generic_target() {
        let mut table = TypeTable::new();
        let number = table.number();
        let t = SymbolId::new(620);
        let named_t = table.named(t);
        let source = table.function(vec![number], number);
        let target = table.function_with_parameter_bounds(
            vec![t],
            vec![TypeParameterBounds::NONE],
            vec![FunctionParameter::new(
                "x".to_string(),
                named_t,
                false,
                false,
            )],
            named_t,
            false,
        );
        let relations = TypeRelations::new(&table);
        assert!(
            relations.assignable(source, target),
            "(x: number) => number should be assignable to <T>(x: T) => T"
        );
    }

    // --- Function vs ObjectType with call signatures ---

    /// A function `() => number` is assignable to an object type with a
    /// call signature `(x: number): void` because void return absorption
    /// and fewer parameters are genuine subtyping concessions.
    #[test]
    fn function_assignable_to_object_type_with_call_signature() {
        let mut table = TypeTable::new();
        let number = table.number();
        let void = table.void();
        let source = table.function(Vec::new(), number);
        let call_sig_fn = table.function(vec![number], void);
        let call_sig = match table.get(call_sig_fn) {
            Type::Function(sig) => sig.clone(),
            _ => unreachable!(),
        };
        let target = table.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures: vec![call_sig],
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        });
        let relations = TypeRelations::new(&table);
        assert!(
            relations.assignable(source, target),
            "() => number should be assignable to {{ (x: number): void }}"
        );
    }

    /// An object type with a call signature `(x: number): string` is
    /// assignable to a function `(x: number): void` because void return
    /// absorption.
    #[test]
    fn object_type_with_call_signature_assignable_to_function() {
        let mut table = TypeTable::new();
        let number = table.number();
        let string = table.string();
        let void = table.void();
        let call_sig_fn = table.function(vec![number], string);
        let call_sig = match table.get(call_sig_fn) {
            Type::Function(sig) => sig.clone(),
            _ => unreachable!(),
        };
        let source = table.object_type_with_members(ObjectType {
            properties: Vec::new(),
            call_signatures: vec![call_sig],
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        });
        let target = table.function(vec![number], void);
        let relations = TypeRelations::new(&table);
        assert!(
            relations.assignable(source, target),
            "{{ (x: number): string }} should be assignable to (x: number) => void"
        );
    }

    /// A function is NOT assignable to an object type with a required
    /// property beyond the call signature.
    #[test]
    fn function_not_assignable_to_object_type_with_required_property() {
        let mut table = TypeTable::new();
        let number = table.number();
        let void = table.void();
        let string = table.string();
        let source = table.function(Vec::new(), number);
        let call_sig_fn = table.function(vec![number], void);
        let call_sig = match table.get(call_sig_fn) {
            Type::Function(sig) => sig.clone(),
            _ => unreachable!(),
        };
        let target = table.object_type_with_members(ObjectType {
            properties: vec![PropertyType::new("extra", false, string)],
            call_signatures: vec![call_sig],
            call_candidate_order: Vec::new(),
            construct_signatures: Vec::new(),
            index_signatures: Vec::new(),
            generator_return: None,
            iterator_property: None,
            async_iterator_property: None,
        });
        let relations = TypeRelations::new(&table);
        assert!(
            !relations.assignable(source, target),
            "() => number should NOT be assignable to {{ extra: string; (x: number): void }}"
        );
    }
}
