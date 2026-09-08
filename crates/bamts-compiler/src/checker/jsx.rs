//! JSX/TSX checking as a demand-only extension of the [`Binder`] expression
//! engine, split into a pure inference phase and a check-only diagnostic
//! phase per the WP-JSX cutover contract.
//!
//! - **Namespace resolution.** The in-scope `JSX` namespace (value or type
//!   plane, resolved from the element's lexical scope outward) provides the
//!   `IntrinsicElements` map and the `Element` result type. Members are found
//!   through the namespace's export scope first and then through the local
//!   scopes of every merged declaration, so non-exported `JSX` members still
//!   participate. Without a `JSX` namespace, intrinsic checking is inert —
//!   JSX carries no ambient meaning by itself — while value-based tags are
//!   still resolved and checked.
//! - **Element classification.** A lowercase, single-identifier tag is an
//!   *intrinsic* element looked up by name in `JSX.IntrinsicElements`; any
//!   other tag is *value-based* and resolves against the value namespace like
//!   an ordinary expression reference, completing the same reference events
//!   an identifier expression would.
//! - **Attribute/children checking.** Attributes fold into one structural
//!   props type — a bare attribute contributes `true`, `name="…"` a string,
//!   `name={expr}` the expression's type, and `{...spread}` members merge in
//!   source order with later members winning, each operand expanded
//!   demand-typed through the same structural views an object-literal spread
//!   reads through; a union-typed spread contributes one props branch per
//!   constituent, and only a truly opaque operand leaves the object
//!   unchecked. Non-whitespace children contribute a `children` property
//!   typed by the union of all children, where a `{...spread}` child
//!   contributes the elements its operand iterates. The props object is
//!   checked against the `IntrinsicElements` member or the resolved factory
//!   signature with the existing assignability relation.
//!
//! Value-based factories are resolved through [`Binder::signature_group`],
//! the canonical demand-based candidate list every callable symbol shares —
//! there is no JSX-specific declaration cache. A generic factory's type
//! arguments are inferred from the synthesized props object with
//! [`InferenceContext`], trying candidates in declaration order and keeping
//! the first whose parameter accepts the props (or that takes none). Intrinsic
//! elements and fragments take `JSX.Element`, falling back to `any` when the
//! namespace does not declare one.
//!
//! [`Binder::infer_jsx_outcome`] computes a [`JsxElementOutcome`] once; the
//! demand dispatch commits it atomically with the expression's
//! [`ExpressionResult`] (`type_id: outcome.result()`, `jsx: Some(outcome)`),
//! and inference itself never emits diagnostics or publishes.
//! [`Binder::check_jsx_element`] and its self-closing/fragment siblings
//! retrieve that committed outcome — never re-invoking inference — to decide
//! at most one diagnostic, then drive every attribute and child expression
//! through the general selected-check traversal exactly once before
//! publishing the element's result type.

use super::binder::{
    Binder, DemandPoll, DemandResult, FunctionParameter, FunctionSignature, IndexSignature,
    ObjectType, PropertyType, PublicationOrder, ScopeId, SlotContext, SymbolId, SymbolKind, Type,
    TypeId, demand_ready,
};
use super::inference::{InferenceContext, InferenceParameter};
use super::{
    CANNOT_FIND_NAME, CANNOT_FIND_NAME_MESSAGE, JSX_ATTRIBUTES_NOT_ASSIGNABLE,
    JSX_ATTRIBUTES_NOT_ASSIGNABLE_MESSAGE, JSX_ELEMENT_TYPE_NOT_CALLABLE,
    JSX_ELEMENT_TYPE_NOT_CALLABLE_MESSAGE, JSX_INTRINSIC_ELEMENT_NOT_FOUND,
    JSX_INTRINSIC_ELEMENT_NOT_FOUND_MESSAGE,
};
use crate::diagnostic::Diagnostic;
use crate::source::TextRange;
use crate::syntax::{
    Expr, Expression, IdentifierNode, JsxAttributeInitializer, JsxAttributeItem, JsxAttributeName,
    JsxChild, JsxElement, JsxElementName, JsxFragment, JsxSelfClosingElement, NodeId,
};

/// The `selected` frame input every check-only JSX entry point receives: the
/// slot the element was demanded under, and the contextual target its parent
/// expects, if any. Defined by WP-DEMAND; re-declared here only as a type
/// alias boundary comment — the real type lives in `binder.rs`.
type SelectedInput = super::binder::SelectedInput;

/// The classified, fully-inferred result of one JSX element, self-closing
/// element, or fragment expression. Computed once by
/// [`Binder::infer_jsx_outcome`] and stored atomically in the owning
/// [`ExpressionResult`]; the check phase replays this value instead of
/// re-inferring or maintaining a second type cache.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum JsxElementOutcome {
    /// A lowercase intrinsic tag resolved through `JSX.IntrinsicElements`.
    /// `target` is the tag's member type there, or `None` when the tag has
    /// no such member (including when `IntrinsicElements` itself is
    /// unresolvable, in which case classification degrades to
    /// [`JsxDegradation::OpaqueCallee`] instead of this variant).
    Intrinsic {
        result: TypeId,
        props: TypeId,
        target: Option<TypeId>,
        tag_range: TextRange,
    },
    /// A value-based tag resolved as a callable factory. `props_target` is
    /// the winning candidate's first parameter type, or `None` for a
    /// zero-parameter candidate that accepts props unconditionally.
    Value {
        result: TypeId,
        props: TypeId,
        props_target: Option<TypeId>,
        callee: TypeId,
        tag_range: TextRange,
    },
    /// A `<>...</>` fragment; children are still individually checked but
    /// their union does not determine the fragment's result type.
    Fragment { result: TypeId },
    /// Recovery: at most one diagnostic is anchored at `tag_range`; `result`
    /// is always a real recovery type (`JSX.Element` or `any`), never a bare
    /// stand-in for a missing chosen signature.
    Degraded {
        result: TypeId,
        reason: JsxDegradation,
        tag_range: TextRange,
    },
}

impl JsxElementOutcome {
    /// The element's result type, common to every classification.
    #[must_use]
    pub(crate) const fn result(self) -> TypeId {
        match self {
            Self::Intrinsic { result, .. }
            | Self::Value { result, .. }
            | Self::Fragment { result }
            | Self::Degraded { result, .. } => result,
        }
    }
}

/// Why a value-based JSX tag degraded to a recovery result instead of a
/// checked classification. `Fragment` is a distinct [`JsxElementOutcome`]
/// variant, never this reason, so it cannot be mistaken for a missing
/// intrinsic target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum JsxDegradation {
    /// The tag name (or a dotted member step) did not resolve to a value.
    /// The check phase republishes this as the "cannot find name"
    /// diagnostic: anchored at `anchor` when a resolvable root's dotted
    /// member step failed (the failed member's own span), otherwise at the
    /// whole tag span for an unresolvable root or namespaced tag.
    TagUnresolved { anchor: Option<TextRange> },
    /// The tag resolved to a value type with no call signatures.
    NotCallable,
    /// The tag resolved to an opaque (`any`/`unknown`/`error`) type, or to
    /// no ambient `JSX.IntrinsicElements` at all: there is nothing to check
    /// against, so the type itself is the unchecked target.
    OpaqueCallee,
}

/// The outcome of resolving a value-based JSX tag name to its value-plane
/// callee: the tag symbol when one is directly reachable through lexical
/// resolution (used for [`Self::signature_group`]) and its value type, or
/// which name step failed to resolve and where that step sits.
enum JsxTagCalleeResolution {
    /// The tag resolved to a value.
    Resolved(Option<SymbolId>, TypeId),
    /// The tag's root identifier (or the whole namespaced form) never
    /// resolved as a value; the whole tag span anchors the diagnostic.
    RootUnresolved,
    /// The root resolved but a dotted member step did not; the failed
    /// member identifier's own range anchors the diagnostic.
    MemberUnresolved(TextRange),
}

impl<'src> Binder<'src> {
    // -- inference --------------------------------------------------------------

    /// Classifies and infers a JSX element, self-closing element, or
    /// fragment expression in one pass, returning the full combined
    /// [`JsxElementOutcome`]: its [`JsxElementOutcome::result`] is the
    /// expression's `TypeId`, so the demand dispatch commits
    /// `ExpressionResult { type_id, jsx: Some(outcome) }` atomically from
    /// this single call. Never emits a diagnostic or publishes a reference;
    /// the check phase alone does that, retrieving the committed outcome
    /// instead of invoking this a second time.
    pub(crate) fn infer_jsx_outcome(
        &mut self,
        expression: &'src Expr,
        context: SlotContext,
    ) -> DemandResult<JsxElementOutcome> {
        match expression.data() {
            Expression::JsxElement(element) => {
                let opening = element.opening.data();
                self.infer_jsx_tag_outcome(
                    &opening.name,
                    &opening.attributes,
                    &element.children,
                    jsx_element_name_range(&opening.name),
                    context,
                )
            }
            Expression::JsxSelfClosingElement(element) => self.infer_jsx_tag_outcome(
                &element.name,
                &element.attributes,
                &[],
                jsx_element_name_range(&element.name),
                context,
            ),
            Expression::JsxFragment(_) => {
                let result = self.jsx_element_type(context.scope);
                Ok(DemandPoll::Ready(JsxElementOutcome::Fragment { result }))
            }
            _ => unreachable!("infer_jsx_outcome is dispatched only for JSX expressions"),
        }
    }

    /// Dispatches an opening tag to intrinsic or value-based inference.
    fn infer_jsx_tag_outcome(
        &mut self,
        name: &'src JsxElementName,
        attributes: &'src [JsxAttributeItem],
        children: &'src [JsxChild],
        tag_range: TextRange,
        context: SlotContext,
    ) -> DemandResult<JsxElementOutcome> {
        match name {
            JsxElementName::Identifier(identifier)
                if is_intrinsic_tag(&self.identifier_text(identifier)) =>
            {
                self.infer_intrinsic_outcome(identifier, attributes, children, tag_range, context)
            }
            _ => self.infer_value_outcome(name, attributes, children, tag_range, context),
        }
    }

    /// Infers an intrinsic tag against `JSX.IntrinsicElements`. With no such
    /// member resolvable at all, checking is inert: JSX has no ambient
    /// meaning on its own, so this degrades silently rather than producing
    /// an `Intrinsic` outcome with nothing to check.
    fn infer_intrinsic_outcome(
        &mut self,
        tag: &'src IdentifierNode,
        attributes: &'src [JsxAttributeItem],
        children: &'src [JsxChild],
        tag_range: TextRange,
        context: SlotContext,
    ) -> DemandResult<JsxElementOutcome> {
        let Some(intrinsics_symbol) = self.jsx_namespace_member(context.scope, "IntrinsicElements")
        else {
            let result = self.jsx_element_type(context.scope);
            return Ok(DemandPoll::Ready(JsxElementOutcome::Degraded {
                result,
                reason: JsxDegradation::OpaqueCallee,
                tag_range,
            }));
        };
        let intrinsics = self.resolve_type_symbol(intrinsics_symbol);
        let tag_name = self.identifier_text(tag).into_owned();
        let target = self.types.property_type(intrinsics, &tag_name);
        let props = demand_ready!(self.infer_jsx_props(attributes, children, target, context));
        let result = self.jsx_element_type(context.scope);
        Ok(DemandPoll::Ready(JsxElementOutcome::Intrinsic {
            result,
            props,
            target,
            tag_range,
        }))
    }

    /// Infers a value-based tag: resolves the tag value, selects the first
    /// applicable candidate from its canonical signature group against the
    /// synthesized props object, and returns the candidate's return type as
    /// the element's result type.
    fn infer_value_outcome(
        &mut self,
        name: &'src JsxElementName,
        attributes: &'src [JsxAttributeItem],
        children: &'src [JsxChild],
        tag_range: TextRange,
        context: SlotContext,
    ) -> DemandResult<JsxElementOutcome> {
        let (symbol, callee) = match demand_ready!(self.resolve_jsx_value_callee(name, context)) {
            JsxTagCalleeResolution::Resolved(symbol, callee) => (symbol, callee),
            JsxTagCalleeResolution::RootUnresolved => {
                let result = self.jsx_element_type(context.scope);
                return Ok(DemandPoll::Ready(JsxElementOutcome::Degraded {
                    result,
                    reason: JsxDegradation::TagUnresolved { anchor: None },
                    tag_range,
                }));
            }
            JsxTagCalleeResolution::MemberUnresolved(anchor) => {
                let result = self.jsx_element_type(context.scope);
                return Ok(DemandPoll::Ready(JsxElementOutcome::Degraded {
                    result,
                    reason: JsxDegradation::TagUnresolved {
                        anchor: Some(anchor),
                    },
                    tag_range,
                }));
            }
        };
        let signatures = demand_ready!(self.jsx_callable_signatures(symbol, callee));
        let props = demand_ready!(self.infer_jsx_props(attributes, children, None, context));
        let Some((props_target, result)) = select_jsx_factory_signature(&signatures, props, self)
        else {
            let result = self.jsx_element_type(context.scope);
            // An opaque callee with no callable shape stays unchecked; a
            // resolved non-callable value reports the not-callable
            // diagnostic. The signature demand runs first because a symbol
            // whose declared value is opaque can still own a canonical
            // declaration signature (namespaced function members are typed
            // only on demand).
            let reason = if matches!(
                self.types.get(callee),
                Type::Any | Type::Unknown | Type::Error
            ) {
                JsxDegradation::OpaqueCallee
            } else {
                JsxDegradation::NotCallable
            };
            return Ok(DemandPoll::Ready(JsxElementOutcome::Degraded {
                result,
                reason,
                tag_range,
            }));
        };
        Ok(DemandPoll::Ready(JsxElementOutcome::Value {
            result,
            props,
            props_target,
            callee,
            tag_range,
        }))
    }

    /// Resolves a value-based JSX tag name to the symbol that names it, when
    /// it is one directly reachable through lexical resolution (used for
    /// [`Self::signature_group`]), and its value type — following dotted
    /// member chains through ordinary structural property demand rather than
    /// a JSX-specific container scope walk. Namespaced (`ns:name`) tags never
    /// resolve as values, matching their absence as a runtime JS binding.
    /// Never emits a diagnostic: inference is pure; the resolution reports
    /// which name step failed so the check phase can anchor the
    /// cannot-find-name diagnostic at that step, and separately completes
    /// the root identifier's reference event.
    fn resolve_jsx_value_callee(
        &mut self,
        name: &'src JsxElementName,
        context: SlotContext,
    ) -> DemandResult<JsxTagCalleeResolution> {
        match name {
            JsxElementName::Identifier(identifier) => {
                let text = self.identifier_text(identifier).into_owned();
                match self.lookup_value(context.scope, &text) {
                    Some(symbol) => {
                        let value_type = demand_ready!(self.declared_value(symbol));
                        Ok(DemandPoll::Ready(JsxTagCalleeResolution::Resolved(
                            Some(symbol),
                            value_type,
                        )))
                    }
                    None => Ok(DemandPoll::Ready(JsxTagCalleeResolution::RootUnresolved)),
                }
            }
            JsxElementName::Member(member) => {
                let (object_symbol, object_type) =
                    match demand_ready!(self.resolve_jsx_value_callee(&member.object, context)) {
                        JsxTagCalleeResolution::Resolved(symbol, callee) => (symbol, callee),
                        resolution => return Ok(DemandPoll::Ready(resolution)),
                    };
                let property = self.identifier_text(&member.property).into_owned();
                // Mirror `Binder::type_of_member`: a namespace (or enum)
                // container resolves the member step to its declaration
                // symbol and that symbol's declared type, so the factory
                // demand below sees the member's own canonical signature
                // group instead of an opaque container value type with no
                // function shape.
                if let Some(object_symbol) = object_symbol
                    && let Some(member_scope) = self.container_member_scope(object_symbol)
                    && let Some(member_symbol) = self.scopes[member_scope.get() as usize]
                        .value(&property)
                        .or_else(|| {
                            self.scopes[member_scope.get() as usize].type_binding(&property)
                        })
                {
                    let mut member_symbol = member_symbol;
                    let mut value_type = demand_ready!(self.declared_value(member_symbol));
                    // The declared-value demand already reads past an opaque
                    // raw entry. When it still cannot type the member, the
                    // namespace's local-scope twin — where `resolve_function`
                    // re-declares member functions — carries the canonical
                    // signature, so prefer it before giving up.
                    if matches!(
                        self.types.get(value_type),
                        Type::Any | Type::Unknown | Type::Error
                    ) && let Some(local_scope) =
                        self.namespace_local_of_symbol.get(&object_symbol)
                        && let Some(local_symbol) =
                            self.scopes[local_scope.get() as usize].value(&property)
                    {
                        let local_type = demand_ready!(self.declared_value(local_symbol));
                        if !matches!(
                            self.types.get(local_type),
                            Type::Any | Type::Unknown | Type::Error
                        ) {
                            member_symbol = local_symbol;
                            value_type = local_type;
                        }
                    }
                    return Ok(DemandPoll::Ready(JsxTagCalleeResolution::Resolved(
                        Some(member_symbol),
                        value_type,
                    )));
                }
                match self.types.property_type(object_type, &property) {
                    Some(property_type) => Ok(DemandPoll::Ready(JsxTagCalleeResolution::Resolved(
                        None,
                        property_type,
                    ))),
                    // The root resolved but this member step did not: the
                    // failed member's own span anchors the check phase's
                    // cannot-find-name diagnostic instead of the whole tag.
                    None => Ok(DemandPoll::Ready(JsxTagCalleeResolution::MemberUnresolved(
                        member.property.range(),
                    ))),
                }
            }
            JsxElementName::Namespace(_) => {
                Ok(DemandPoll::Ready(JsxTagCalleeResolution::RootUnresolved))
            }
        }
    }

    /// Returns the callable candidates for a resolved JSX tag value: the
    /// symbol's own canonical signature group when it names one directly,
    /// or — covering dotted-member, aliased-import, object-literal, and
    /// class factories that have no symbol of their own to demand a group
    /// for — the value type's shape read through per-shape grouping views
    /// matching an ordinary call or `new` expression: applied aliases,
    /// applied classes, function types, object types carrying call or
    /// construct signatures, constructor types (the class static side), and
    /// named interfaces via their structural view. Unions and intersections
    /// return no candidates yet (an ordinary call distributes over them);
    /// a construct signature contributes its constructor's parameters and
    /// the class instance type as the element's result, matching the
    /// "neither a construct nor a call signature" diagnostic contract.
    fn jsx_callable_signatures(
        &mut self,
        symbol: Option<SymbolId>,
        callee: TypeId,
    ) -> DemandResult<Vec<FunctionSignature>> {
        if let Some(symbol) = symbol {
            let signatures = demand_ready!(self.signature_group(symbol));
            if !signatures.is_empty() {
                return Ok(DemandPoll::Ready(signatures));
            }
            // A class value's declared type is its instance side; the
            // construct signatures live on the static side (a
            // constructor type), so a class tag reads its candidates from
            // there, matching what a `new C` expression uses.
            if self.symbols[symbol.get() as usize].kind() == SymbolKind::Class
                && let Some(constructor_type) = self.class_constructor_types.get(&symbol).copied()
            {
                return self.jsx_callable_signatures(None, constructor_type);
            }
        }
        let resolved = self
            .types
            .prepare_applied_alias_view(callee)
            .unwrap_or(callee);
        let resolved = self
            .types
            .prepare_applied_class_view(resolved)
            .unwrap_or(resolved);
        let signatures = match self.types.get(resolved).clone() {
            Type::Function(signature) => vec![signature],
            Type::ObjectType(object) if !object.call_signatures.is_empty() => {
                // Call selection reads the stored candidate permutation;
                // relations keep declaration order.
                let ordered: Vec<&FunctionSignature> = if object.call_candidate_order.is_empty() {
                    object.call_signatures.iter().collect()
                } else {
                    object
                        .call_candidate_order
                        .iter()
                        .map(|&index| &object.call_signatures[index as usize])
                        .collect()
                };
                ordered.into_iter().cloned().collect()
            }
            Type::ObjectType(object) if !object.construct_signatures.is_empty() => object
                .construct_signatures
                .iter()
                .map(|entry| entry.signature.clone())
                .collect(),
            Type::ConstructorType { structural, .. } => {
                // The class static side wraps its structural member table;
                // construct signatures live on the table. this-projection is
                // unnecessary here: construct signatures carry no `this`
                // members on their fixed parameters.
                match self.types.get(structural).clone() {
                    Type::ObjectType(object) => object
                        .construct_signatures
                        .iter()
                        .map(|entry| entry.signature.clone())
                        .collect(),
                    _ => Vec::new(),
                }
            }
            Type::Named(symbol) if self.types.interface_structure(symbol).is_some() => {
                let view = self.types.named_structural_view(resolved);
                match self.types.get(view).clone() {
                    Type::ObjectType(object) => object.call_signatures.clone(),
                    _ => Vec::new(),
                }
            }
            _ => Vec::new(),
        };
        Ok(DemandPoll::Ready(signatures))
    }

    // -- props/children synthesis -------------------------------------------------

    /// Folds the attribute list and children into one structural props type.
    /// Spread members merge in source order; later members win, a union-typed
    /// spread contributes one distributable branch per constituent, and only
    /// a truly opaque (`any`/`unknown`/`error`) operand leaves the props
    /// object unchecked. `target` is the already-known props schema (an
    /// intrinsic's resolved member type), used only to look up a contextual
    /// type for the synthesized `children` property; individual attribute
    /// values are never contextually typed, matching ordinary call-argument
    /// inference.
    pub(crate) fn infer_jsx_props(
        &mut self,
        attributes: &'src [JsxAttributeItem],
        children: &'src [JsxChild],
        target: Option<TypeId>,
        context: SlotContext,
    ) -> DemandResult<TypeId> {
        // One entry per distributable branch of the props object: the members
        // merged so far. A union-typed spread multiplies the branches so
        // later members merge into every constituent, and the folded props
        // type is the union of the per-branch objects — the same shape an
        // ordinary call sees when a union argument flows into one parameter.
        let mut variants: Vec<JsxSpreadBranch> = vec![JsxSpreadBranch {
            properties: Vec::new(),
            index_signatures: Vec::new(),
        }];
        let mut has_opaque_spread = false;
        for attribute in attributes {
            match attribute {
                JsxAttributeItem::Attribute(attribute) => {
                    let data = attribute.data();
                    let name = jsx_attribute_key(self, &data.name);
                    let value = match &data.initializer {
                        None => self.types.boolean_literal(true),
                        Some(JsxAttributeInitializer::String(_)) => self.types.string(),
                        Some(JsxAttributeInitializer::Expression(container)) => {
                            match &container.data().expression {
                                Some(expression) => {
                                    demand_ready!(self.type_of_expr(expression, context))
                                }
                                None => self.types.any(),
                            }
                        }
                    };
                    for branch in &mut variants {
                        upsert_property(
                            &mut branch.properties,
                            PropertyType::new(name.clone(), false, value),
                        );
                    }
                }
                JsxAttributeItem::Spread(spread) => {
                    let spread_type =
                        demand_ready!(self.type_of_expr(&spread.data().expression, context));
                    self.check_cancel()?;
                    let Some(branches) = self.jsx_spread_branches(spread_type) else {
                        has_opaque_spread = true;
                        continue;
                    };
                    // The fold is a branch product: each spread multiplies
                    // the variant count by this operand's branch count, so
                    // unguarded `m^n` products intern an exponential number
                    // of props objects. Past the cap the operand's
                    // constituents collapse into one merged branch (later
                    // members winning) that merges into every existing
                    // variant — the same bounded approximation an opaque
                    // spread grants, instead of multiplying further.
                    let branches = if variants.len().saturating_mul(branches.len())
                        > MAX_JSX_SPREAD_BRANCHES
                    {
                        vec![jsx_merge_spread_branches(&branches)]
                    } else {
                        branches
                    };
                    variants = variants
                        .iter()
                        .flat_map(|variant| {
                            branches.iter().map(|branch| variant.merged_with(branch))
                        })
                        .collect();
                }
            }
        }
        let children_target =
            target.and_then(|target| self.types.property_type(target, "children"));
        if let Some(children_type) =
            demand_ready!(self.infer_jsx_children(children, children_target, context))
        {
            for branch in &mut variants {
                upsert_property(
                    &mut branch.properties,
                    PropertyType::new("children", false, children_type),
                );
            }
        }
        if has_opaque_spread {
            // A truly opaque spread operand could carry every remaining
            // member, so no typed answer exists to keep: the merged props
            // object stays unchecked as a whole.
            return Ok(DemandPoll::Ready(self.types.any()));
        }
        let props = if variants.len() == 1 {
            jsx_props_object(self, variants.remove(0))
        } else {
            let branch_types: Vec<TypeId> = variants
                .into_iter()
                .map(|branch| jsx_props_object(self, branch))
                .collect();
            self.types.union(&branch_types)
        };
        Ok(DemandPoll::Ready(props))
    }

    /// Infers every child, returning the union of all non-whitespace child
    /// types; whitespace-only text contributes nothing. `target` contextually
    /// types only `{expr}` containers, matching what [`Self::infer_jsx_props`]
    /// passes; spreads and nested elements are typed context-free. Nested
    /// JSX dispatches through the ordinary `type_of_expr` path, so it commits
    /// its own outcome without a JSX-specific recursive matcher here.
    pub(crate) fn infer_jsx_children(
        &mut self,
        children: &'src [JsxChild],
        target: Option<TypeId>,
        context: SlotContext,
    ) -> DemandResult<Option<TypeId>> {
        let mut child_types: Vec<TypeId> = Vec::new();
        for child in children {
            match child {
                JsxChild::Text(text) => {
                    if self.text(text.data().token()).trim().is_empty() {
                        continue;
                    }
                    child_types.push(self.types.string());
                }
                JsxChild::ExpressionContainer(container) => {
                    if let Some(expression) = &container.data().expression {
                        let value = match target {
                            Some(target) => {
                                demand_ready!(
                                    self.type_of_expr_with_target(expression, target, context)
                                )
                            }
                            None => demand_ready!(self.type_of_expr(expression, context)),
                        };
                        child_types.push(value);
                    }
                }
                JsxChild::Spread(spread) => {
                    let spread_type =
                        demand_ready!(self.type_of_expr(&spread.data().expression, context));
                    child_types.push(self.jsx_spread_child_element(spread_type));
                }
                JsxChild::Element(expression) => {
                    child_types.push(demand_ready!(self.type_of_expr(expression, context)));
                }
            }
        }
        let union = if child_types.is_empty() {
            None
        } else {
            Some(self.types.union(&child_types))
        };
        Ok(DemandPoll::Ready(union))
    }

    // -- spread operand typing --------------------------------------------------

    /// Resolves a spread operand's type-parameter head to its constraint, so
    /// spreading `T` reads the shape `T` is known to carry. A cyclic
    /// constraint chain stops at the repeated head and falls through to the
    /// structural views.
    fn jsx_spread_constraint_view(&self, spread_type: TypeId) -> TypeId {
        let mut current = spread_type;
        let mut seen: Vec<TypeId> = Vec::new();
        loop {
            if seen.contains(&current) {
                return current;
            }
            let constraint = match self.types.get(current) {
                Type::Named(symbol) => self.types.type_parameter_constraint(*symbol),
                _ => None,
            };
            let Some(constraint) = constraint else {
                return current;
            };
            seen.push(current);
            current = constraint;
        }
    }

    /// Maps [`Self::jsx_spread_branches`] over `members` in source order,
    /// failing the whole spread on the first opaque constituent.
    fn jsx_spread_member_branches(&mut self, members: &[TypeId]) -> Option<Vec<JsxSpreadBranch>> {
        let mut branches = Vec::new();
        for member in members {
            branches.extend(self.jsx_spread_branches(*member)?);
        }
        Some(branches)
    }

    /// Reduces one `{...spread}` operand to the typed members it contributes
    /// to the props object: one branch per union constituent, each expanded
    /// through the same views an object-literal spread reads through —
    /// type-parameter constraints, then the structural views for interface
    /// heads, `this` constraints, applied aliases, and applied classes.
    /// Returns `None` only when a constituent is truly opaque
    /// (`any`/`unknown`/`error`): no member list exists, so the merged props
    /// object stays unchecked as a whole. A known non-object operand
    /// contributes one empty branch, exactly like an object-literal spread
    /// whose operand carries no members.
    fn jsx_spread_branches(&mut self, spread_type: TypeId) -> Option<Vec<JsxSpreadBranch>> {
        let spread_type = self.jsx_spread_constraint_view(spread_type);
        let spread_type = self.types.indexed_access_view(spread_type);
        match self.types.get(spread_type).clone() {
            // A truly opaque operand has no member list: nothing about the
            // merged object is knowable, and one opaque union or
            // intersection member absorbs its whole spread the same way.
            Type::Any | Type::Unknown | Type::Error => None,
            Type::ObjectType(object) => Some(vec![JsxSpreadBranch {
                properties: object.properties.clone(),
                index_signatures: object.index_signatures.clone(),
            }]),
            Type::Record { key, value } => Some(vec![JsxSpreadBranch {
                properties: Vec::new(),
                index_signatures: vec![IndexSignature {
                    readonly: false,
                    parameters: vec![FunctionParameter::new("key".to_owned(), key, false, false)],
                    value_type: value,
                    declaring_types: Vec::new(),
                }],
            }]),
            Type::Intersection(members) => {
                let mut merged = JsxSpreadBranch {
                    properties: Vec::new(),
                    index_signatures: Vec::new(),
                };
                for branch in self.jsx_spread_member_branches(&members)? {
                    for property in branch.properties {
                        upsert_property(&mut merged.properties, property);
                    }
                    merged.index_signatures.extend(branch.index_signatures);
                }
                Some(vec![merged])
            }
            Type::Union(members) => self.jsx_spread_member_branches(&members),
            _ => Some(vec![JsxSpreadBranch {
                properties: Vec::new(),
                index_signatures: Vec::new(),
            }]),
        }
    }

    /// Types one `{...spread}` child by what its operand iterates: the union
    /// of each constituent's iteration element, expanded through the same
    /// views a props spread reads through. A constituent with a typed
    /// iteration element (array, tuple) contributes it; a known non-iterable
    /// contributes itself, so the children union still says what the operand
    /// could add; only a truly opaque (`any`/`unknown`/`error`) constituent
    /// contributes `any`, because no element type exists to keep.
    fn jsx_spread_child_element(&mut self, spread_type: TypeId) -> TypeId {
        let spread_type = self.jsx_spread_constraint_view(spread_type);
        let spread_type = self.types.indexed_access_view(spread_type);
        match self.types.get(spread_type).clone() {
            Type::Union(members) => {
                let elements: Vec<TypeId> = members
                    .iter()
                    .map(|member| self.jsx_spread_child_element(*member))
                    .collect();
                self.types.union(&elements)
            }
            _ => self
                .types
                .array_or_tuple_iteration_element(spread_type)
                .unwrap_or_else(|| {
                    if matches!(
                        self.types.get(spread_type),
                        Type::Any | Type::Unknown | Type::Error
                    ) {
                        self.types.any()
                    } else {
                        spread_type
                    }
                }),
        }
    }

    // -- checking -----------------------------------------------------------------

    /// Checks a balanced JSX element `<name attrs>children</name>`.
    pub(crate) fn check_jsx_element(
        &mut self,
        expression: &'src Expr,
        element: &'src JsxElement,
        selection: SelectedInput,
    ) -> Result<(), super::CheckCancelled> {
        let opening = element.opening.data();
        self.check_jsx_common(
            expression,
            &opening.name,
            &opening.attributes,
            &element.children,
            selection,
        )
    }

    /// Checks a self-closing JSX element `<name attrs />`.
    pub(crate) fn check_jsx_self_closing_element(
        &mut self,
        expression: &'src Expr,
        element: &'src JsxSelfClosingElement,
        selection: SelectedInput,
    ) -> Result<(), super::CheckCancelled> {
        self.check_jsx_common(
            expression,
            &element.name,
            &element.attributes,
            &[],
            selection,
        )
    }

    /// Checks a JSX fragment `<>children</>`.
    pub(crate) fn check_jsx_fragment(
        &mut self,
        expression: &'src Expr,
        fragment: &'src JsxFragment,
        selection: SelectedInput,
    ) -> Result<(), super::CheckCancelled> {
        let context = selection.context;
        let outcome = ready_demand(self.committed_jsx_outcome(expression, selection))?;
        for child in &fragment.children {
            self.check_jsx_child(child, None, context)?;
        }
        self.publish_selected_expression(expression, outcome.result())
    }

    /// Shared element/self-closing-element check path: replays the committed
    /// [`JsxElementOutcome`], queues at most one diagnostic from it, then
    /// drives every attribute and child expression through the general
    /// selected-check traversal exactly once — even on an inference memo hit
    /// — before publishing the element's result type.
    fn check_jsx_common(
        &mut self,
        expression: &'src Expr,
        name: &'src JsxElementName,
        attributes: &'src [JsxAttributeItem],
        children: &'src [JsxChild],
        selection: SelectedInput,
    ) -> Result<(), super::CheckCancelled> {
        let context = selection.context;
        let outcome = ready_demand(self.committed_jsx_outcome(expression, selection))?;
        self.complete_jsx_tag_references(name, context)?;
        let order = self.diagnostic_order(expression.id());
        // The outcome's props declaration type drives attribute-name anchor
        // recording below; fragment and degraded outcomes have none.
        let props_target = match &outcome {
            JsxElementOutcome::Intrinsic { target, .. } => *target,
            JsxElementOutcome::Value { props_target, .. } => *props_target,
            JsxElementOutcome::Fragment { .. } | JsxElementOutcome::Degraded { .. } => None,
        };
        match outcome {
            JsxElementOutcome::Intrinsic {
                props,
                target: Some(target),
                tag_range,
                ..
            } => self.check_jsx_props_assignable(tag_range, props, target, order)?,
            JsxElementOutcome::Intrinsic {
                target: None,
                tag_range,
                ..
            } => {
                self.queue_diagnostic(
                    Diagnostic::error(
                        JSX_INTRINSIC_ELEMENT_NOT_FOUND,
                        self.source.source_id(),
                        tag_range,
                        JSX_INTRINSIC_ELEMENT_NOT_FOUND_MESSAGE,
                    ),
                    order,
                    true,
                )?;
            }
            JsxElementOutcome::Value {
                props,
                props_target: Some(target),
                tag_range,
                ..
            } => self.check_jsx_props_assignable(tag_range, props, target, order)?,
            JsxElementOutcome::Value {
                props_target: None, ..
            }
            | JsxElementOutcome::Fragment { .. } => {}
            JsxElementOutcome::Degraded {
                reason: JsxDegradation::NotCallable,
                tag_range,
                ..
            } => {
                self.queue_diagnostic(
                    Diagnostic::error(
                        JSX_ELEMENT_TYPE_NOT_CALLABLE,
                        self.source.source_id(),
                        tag_range,
                        JSX_ELEMENT_TYPE_NOT_CALLABLE_MESSAGE,
                    ),
                    order,
                    true,
                )?;
            }
            JsxElementOutcome::Degraded {
                reason: JsxDegradation::TagUnresolved { anchor },
                tag_range,
                ..
            } => {
                // Inference stays pure, so the unresolved-tag degradation is
                // republished here as the cannot-find-name diagnostic the
                // tag's reference completion would have raised — once, in
                // source order, from the committed outcome rather than a
                // re-resolution. A dotted member step that failed after a
                // resolvable root anchors at the failed member only; a
                // wholly unresolved root anchors the whole tag span.
                if !self.suppresses_unresolved_value(context.scope) {
                    let anchor = anchor.unwrap_or(tag_range);
                    self.queue_diagnostic(
                        Diagnostic::error(
                            CANNOT_FIND_NAME,
                            self.source.source_id(),
                            anchor,
                            CANNOT_FIND_NAME_MESSAGE,
                        ),
                        order,
                        true,
                    )?;
                }
            }
            JsxElementOutcome::Degraded {
                reason: JsxDegradation::OpaqueCallee,
                ..
            } => {}
        }
        for attribute in attributes {
            self.check_jsx_attribute(attribute, props_target, context)?;
        }
        let children_target = match outcome {
            JsxElementOutcome::Intrinsic { target, .. } => {
                target.and_then(|target| self.types.property_type(target, "children"))
            }
            _ => None,
        };
        for child in children {
            self.check_jsx_child(child, children_target, context)?;
        }
        self.publish_selected_expression(expression, outcome.result())
    }

    /// Completes the reference event reserved at Stage-A for the tag's root
    /// identifier: a plain `Comp` and the `UI` root of a qualified
    /// `UI.Button` get their Stage-A event filled in with the resolved root
    /// symbol as its typed target. That is the extent of it — the member or
    /// factory step of a qualified tag is a structural property demand, not
    /// a lexical reference, so it completes no reference event of its own,
    /// and intrinsic tags complete nothing here.
    fn complete_jsx_tag_references(
        &mut self,
        name: &'src JsxElementName,
        context: SlotContext,
    ) -> Result<(), super::CheckCancelled> {
        match name {
            JsxElementName::Identifier(identifier) => {
                if is_intrinsic_tag(&self.identifier_text(identifier)) {
                    return Ok(());
                }
                let text = self.identifier_text(identifier).into_owned();
                let target = self.lookup_value(context.scope, &text);
                self.complete_jsx_reference(identifier.id(), target)
            }
            JsxElementName::Member(member) => {
                self.complete_jsx_tag_references(&member.object, context)
            }
            JsxElementName::Namespace(_) => Ok(()),
        }
    }

    fn complete_jsx_reference(
        &mut self,
        node: NodeId,
        target: Option<SymbolId>,
    ) -> Result<(), super::CheckCancelled> {
        match self.reference_sequence(node) {
            Some(sequence) => self.complete_reference_event(sequence, target, None),
            None => Ok(()),
        }
    }

    /// Checks the synthesized props object against the element's expected
    /// props type. Opaque targets absorb everything.
    fn check_jsx_props_assignable(
        &mut self,
        range: TextRange,
        props: TypeId,
        target: TypeId,
        order: PublicationOrder,
    ) -> Result<(), super::CheckCancelled> {
        if matches!(
            self.types.get(target),
            Type::Any | Type::Unknown | Type::Error
        ) {
            return Ok(());
        }
        if !self.types.assignable(props, target) {
            self.queue_diagnostic(
                Diagnostic::error(
                    JSX_ATTRIBUTES_NOT_ASSIGNABLE,
                    self.source.source_id(),
                    range,
                    JSX_ATTRIBUTES_NOT_ASSIGNABLE_MESSAGE,
                ),
                order,
                true,
            )?;
        }
        Ok(())
    }

    /// Checks one attribute item's initializer expression and records the
    /// attribute name as a property anchor against the props declaration
    /// owner, so rename and quick info treat JSX attribute names like
    /// ordinary property references. Recording happens in this check phase
    /// only — inference stays pure — and the attribute loop above iterates
    /// in source order, so anchors land in source order. The anchor store
    /// drops names that fail its identifier invariant, which also covers
    /// namespaced `ns:local` names on both the attribute and declaration
    /// sides.
    fn check_jsx_attribute(
        &mut self,
        attribute: &'src JsxAttributeItem,
        props_target: Option<TypeId>,
        context: SlotContext,
    ) -> Result<(), super::CheckCancelled> {
        match attribute {
            JsxAttributeItem::Attribute(attribute) => {
                let data = attribute.data();
                if let Some(JsxAttributeInitializer::Expression(container)) = &data.initializer
                    && let Some(expression) = &container.data().expression
                {
                    self.check_selected_expr(
                        expression,
                        SelectedInput {
                            context,
                            target: None,
                        },
                    )?;
                }
                if let JsxAttributeName::Identifier(identifier) = &data.name {
                    let name = self.identifier_text(identifier).into_owned();
                    self.record_jsx_attribute_anchor(props_target, &name, identifier.range());
                }
            }
            JsxAttributeItem::Spread(spread) => {
                self.check_selected_expr(
                    &spread.data().expression,
                    SelectedInput {
                        context,
                        target: None,
                    },
                )?;
            }
        }
        Ok(())
    }

    fn check_jsx_child(
        &mut self,
        child: &'src JsxChild,
        target: Option<TypeId>,
        context: SlotContext,
    ) -> Result<(), super::CheckCancelled> {
        match child {
            JsxChild::Text(_) => {}
            JsxChild::ExpressionContainer(container) => {
                if let Some(expression) = &container.data().expression {
                    self.check_selected_expr(expression, SelectedInput { context, target })?;
                }
            }
            JsxChild::Spread(spread) => {
                self.check_selected_expr(
                    &spread.data().expression,
                    SelectedInput {
                        context,
                        target: None,
                    },
                )?;
            }
            JsxChild::Element(expression) => {
                self.check_selected_expr(
                    expression,
                    SelectedInput {
                        context,
                        target: None,
                    },
                )?;
            }
        }
        Ok(())
    }

    // -- namespace resolution ---------------------------------------------------

    /// Resolves the in-scope `JSX` namespace symbol from `scope`, trying the
    /// value plane then the type plane.
    fn jsx_namespace_symbol(&self, scope: ScopeId) -> Option<SymbolId> {
        self.lookup_value(scope, "JSX")
            .or_else(|| self.lookup_type(scope, "JSX"))
    }

    /// Resolves a named member (`Element`, `IntrinsicElements`) of the `JSX`
    /// namespace: the export scope first, then the local scopes of every
    /// merged declaration, so non-exported members still participate.
    fn jsx_namespace_member(&self, scope: ScopeId, member: &str) -> Option<SymbolId> {
        let namespace = self.jsx_namespace_symbol(scope)?;
        let member_in = |scope: ScopeId| {
            let scope = &self.scopes[scope.get() as usize];
            scope.type_binding(member).or_else(|| scope.value(member))
        };
        if let Some(export_scope) = self.container_member_scope(namespace)
            && let Some(found) = member_in(export_scope)
        {
            return Some(found);
        }
        self.namespace_declarations
            .iter()
            .filter(|binding| binding.symbol == namespace)
            .filter_map(|binding| self.namespace_local_scopes.get(&binding.declaration_id))
            .find_map(|local_scope| member_in(*local_scope))
    }

    /// Returns the declared `JSX.Element` result type, or `any` when the
    /// namespace does not declare one.
    fn jsx_element_type(&mut self, scope: ScopeId) -> TypeId {
        match self.jsx_namespace_member(scope, "Element") {
            Some(symbol) => {
                let element = self.resolve_type_symbol(symbol);
                let view = self.types.named_structural_view(element);
                if view != element {
                    view
                } else if let Some(class_view) = self.types.prepare_applied_class_view(element) {
                    class_view
                } else if let Some(alias_view) = self.types.prepare_applied_alias_view(element) {
                    alias_view
                } else {
                    element
                }
            }
            None => self.types.any(),
        }
    }
}

/// Selects the first candidate in `signatures` whose parameters accept
/// `props` (P1: declaration order, first applicable wins), instantiating
/// each candidate's own generics independently against `props` with a fresh
/// cancellable inference session before testing assignability. A
/// zero-parameter candidate always accepts. A candidate whose call arity
/// requires more than the one synthesized props object (tuple-rest
/// minimums counted exactly as an ordinary call counts them) is skipped:
/// JSX supplies exactly one argument.
/// Falls back to the first arity-valid candidate's instantiation when none
/// match assignability, and to the very first candidate only when every
/// candidate is arity-invalid, so a single-candidate factory degrades the
/// same way a checked call would and a real, non-`any` recovery type is
/// still produced; returns `None` only when `signatures` is empty.
fn select_jsx_factory_signature(
    signatures: &[FunctionSignature],
    props: TypeId,
    binder: &mut Binder<'_>,
) -> Option<(Option<TypeId>, TypeId)> {
    let mut fallback = None;
    let mut first: Option<&FunctionSignature> = None;
    for signature in signatures {
        // Arity precedes instantiation: call_arity counts tuple-rest minimums
        // the way an ordinary call does, while arity() stops at the rest
        // parameter and would admit tuple-rest factories JSX cannot satisfy
        // with its single props argument. An arity-invalid candidate is only
        // instantiated when it turns out to be the sole recovery candidate.
        if signature.call_arity(&binder.types).0 > 1 {
            first.get_or_insert(signature);
            continue;
        }
        let (target, result) = instantiate_jsx_factory_signature(binder, signature, props);
        let matches = match target {
            Some(target) => binder.types.assignable(props, target),
            None => true,
        };
        if matches {
            return Some((target, result));
        }
        fallback.get_or_insert((target, result));
    }
    fallback.or_else(|| {
        first.map(|signature| instantiate_jsx_factory_signature(binder, signature, props))
    })
}

/// Instantiates one candidate signature's first-parameter target and return
/// type against `props`. Non-generic candidates use their declared types
/// directly; generic candidates infer their type arguments from `props`
/// exactly as an ordinary call would.
fn instantiate_jsx_factory_signature(
    binder: &mut Binder<'_>,
    signature: &FunctionSignature,
    props: TypeId,
) -> (Option<TypeId>, TypeId) {
    if signature.type_parameters().is_empty() {
        let target = signature
            .parameters()
            .first()
            .map(FunctionParameter::type_id);
        return (target, signature.return_type());
    }
    let inference_parameters: Vec<InferenceParameter> = signature
        .type_parameters()
        .iter()
        .zip(signature.type_parameter_bounds())
        .map(|(&symbol, bounds)| {
            let mut parameter = InferenceParameter::new(symbol);
            if let Some(constraint) = bounds.constraint() {
                parameter = parameter.with_constraint(constraint);
            }
            if let Some(default) = bounds.default() {
                parameter = parameter.with_default(default);
            }
            parameter
        })
        .collect();
    let mut context = InferenceContext::new_with_cancel(
        &mut binder.types,
        &inference_parameters,
        binder.cancel.clone(),
    );
    let first = signature
        .parameters()
        .first()
        .map(FunctionParameter::type_id);
    if let Some(first) = first {
        context.infer_from_argument(first, props, 0);
    }
    let inferred = context.resolve();
    let target = first.map(|first| inferred.instantiate(&mut binder.types, first));
    let result = inferred.instantiate(&mut binder.types, signature.return_type());
    (target, result)
}

/// Unwraps a demand result that selected checking guarantees is `Ready`: the
/// driver only dispatches selected checking after every frame dependency has
/// settled, so `Pending`/`Limited` here would be an internal scheduler
/// invariant violation, not a recoverable state. The JSX check path applies
/// this to the binder's already-driven
/// [`Binder::committed_jsx_outcome`] retrieval as well — the scheduler has
/// settled the expression before replay — and the binder's own demand
/// commit guarantees the retrieved outcome cache is `Some` for any
/// completed JSX expression.
fn ready_demand<T>(result: DemandResult<T>) -> Result<T, super::CheckCancelled> {
    match result? {
        DemandPoll::Ready(value) => Ok(value),
        DemandPoll::Pending(_) | DemandPoll::Limited { .. } => {
            unreachable!("selected checking only runs after all frame dependencies settle")
        }
    }
}

/// Returns whether `tag` is a lowercase intrinsic-style JSX tag such as
/// `div`. Member (`A.B`) and namespaced (`a:b`) tags never classify here;
/// they resolve through the value namespace instead.
fn is_intrinsic_tag(tag: &str) -> bool {
    tag.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
}

/// Returns the props member key for an attribute name. Namespaced attribute
/// names (`xml:lang`) follow the desugar contract's spelling: the quoted
/// string key `"ns:local"` over the full name span, so a props target
/// declaring that member checks the attribute instead of silently skipping
/// a supported label.
fn jsx_attribute_key(binder: &Binder<'_>, name: &JsxAttributeName) -> String {
    match name {
        JsxAttributeName::Identifier(identifier) => binder.identifier_text(identifier).into_owned(),
        JsxAttributeName::Namespace(namespaced) => format!(
            "{}:{}",
            binder.identifier_text(&namespaced.namespace),
            binder.identifier_text(&namespaced.name)
        ),
    }
}
/// Inserts `property` into `properties`, replacing any earlier member with
/// the same name so later attributes and spreads win in source order.
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

/// The most props-object branches one element's spread fold may hold. Each
/// union-typed spread multiplies the variant count by its constituents; a
/// spread whose multiplication would exceed this bound merges its
/// constituents into a single branch (later members winning) instead of
/// distributing, mirroring the conditional-type evaluator's
/// `DEFAULT_EXPANSION_LIMIT` philosophy: a bounded approximation beats an
/// unbounded product.
const MAX_JSX_SPREAD_BRANCHES: usize = 1_000;

/// Collapses one capped spread's branches into a single branch: each
/// property name carries the last branch's type for it (source order),
/// and index signatures concatenate in branch order.
fn jsx_merge_spread_branches(branches: &[JsxSpreadBranch]) -> JsxSpreadBranch {
    let mut merged = JsxSpreadBranch {
        properties: Vec::new(),
        index_signatures: Vec::new(),
    };
    for branch in branches {
        for property in &branch.properties {
            upsert_property(&mut merged.properties, property.clone());
        }
        merged
            .index_signatures
            .extend(branch.index_signatures.iter().cloned());
    }
    merged
}

/// One demand-reduced `{...spread}` contribution: the property members and
/// index signatures a single branch of the spread operand supplies.
struct JsxSpreadBranch {
    properties: Vec<PropertyType>,
    index_signatures: Vec<IndexSignature>,
}

impl JsxSpreadBranch {
    /// Merges one branch's members behind `self`, later members winning in
    /// source order.
    fn merged_with(&self, branch: &Self) -> Self {
        let mut properties = self.properties.clone();
        for property in &branch.properties {
            upsert_property(&mut properties, property.clone());
        }
        let mut index_signatures = self.index_signatures.clone();
        index_signatures.extend(branch.index_signatures.iter().cloned());
        Self {
            properties,
            index_signatures,
        }
    }
}

/// Interns one props branch as its structural object type.
fn jsx_props_object(binder: &mut Binder<'_>, branch: JsxSpreadBranch) -> TypeId {
    binder.types.object_type_with_members(ObjectType {
        properties: branch.properties,
        call_signatures: Vec::new(),
        call_candidate_order: Vec::new(),
        construct_signatures: Vec::new(),
        index_signatures: branch.index_signatures,
        generator_return: None,
        iterator_property: None,
        async_iterator_property: None,
    })
}

/// The source span anchoring diagnostics for a JSX tag name: the identifier
/// itself, or the full dotted/namespaced span for member and namespaced
/// names.
fn jsx_element_name_range(name: &JsxElementName) -> TextRange {
    match name {
        JsxElementName::Identifier(identifier) => identifier.range(),
        JsxElementName::Namespace(namespaced) => TextRange::new(
            namespaced.namespace.range().start(),
            namespaced.name.range().end(),
        )
        .unwrap_or_else(|_| namespaced.name.range()),
        JsxElementName::Member(member) => {
            let start = jsx_element_name_range(&member.object).start();
            TextRange::new(start, member.property.range().end())
                .unwrap_or_else(|_| member.property.range())
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::super::binder::{SemanticModel, bind_source};
    use super::super::{
        CANNOT_FIND_NAME, EXPRESSION_NOT_CALLABLE, JSX_ATTRIBUTES_NOT_ASSIGNABLE,
        JSX_ELEMENT_TYPE_NOT_CALLABLE, JSX_INTRINSIC_ELEMENT_NOT_FOUND, TYPE_NOT_ASSIGNABLE,
    };
    use crate::diagnostic::Diagnostic;
    use crate::source::{ScriptKind, SourceId, SourceText};
    use crate::{parser, scanner};

    fn bound(text: &str) -> (SemanticModel, Vec<Diagnostic>) {
        let parsed = parser::parse(scanner::scan(
            SourceId::new(0),
            ScriptKind::TypeScriptReact,
            Arc::new(SourceText::new(text).expect("test source fits the per-file budget")),
        ));
        assert!(
            parsed.diagnostics().is_empty(),
            "unexpected parse diagnostics: {:?}",
            parsed.diagnostics()
        );
        bind_source(parsed.product())
    }

    fn codes(text: &str) -> Vec<&'static str> {
        let (_model, diagnostics) = bound(text);
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    #[track_caller]
    fn assert_clean(codes: Vec<&'static str>) {
        assert!(codes.is_empty(), "unexpected diagnostics: {codes:?}");
    }

    /// A `JSX` namespace with an empty `Element` type and one intrinsic `div`
    /// taking `{ id?: string, children?: string }`.
    const JSX_PREAMBLE: &str = "namespace JSX { \
        interface Element {} \
        interface IntrinsicElements { div: { id?: string; children?: string } } \
    } ";

    // -- intrinsic vs value-based elements ---------------------------------------

    #[test]
    fn known_intrinsic_element_with_valid_attributes_is_clean() {
        assert_clean(codes(&format!(
            "{JSX_PREAMBLE} const x = <div id=\"a\" />;"
        )));
    }

    #[test]
    fn jsx_expression_writes_invalidate_captured_narrowing() {
        let source = format!(
            "{JSX_PREAMBLE} \
             declare let f: (() => void) | undefined; \
             if (f) {{ \
               const read = () => f(); \
               const node = <div id={{(f = undefined, \"value\")}} />; \
               read(); \
             }}"
        );
        assert_eq!(codes(&source), [EXPRESSION_NOT_CALLABLE.as_str()]);
    }

    #[test]
    fn unknown_intrinsic_element_reports_intrinsic_element_not_found() {
        assert_eq!(
            codes(&format!("{JSX_PREAMBLE} const x = <span />;")),
            [JSX_INTRINSIC_ELEMENT_NOT_FOUND.as_str()]
        );
    }

    #[test]
    fn value_based_element_resolves_its_factory() {
        let source = format!(
            "{JSX_PREAMBLE} function Comp(props: {{ id?: string }}) {{ return null; }} \
             const x = <Comp id=\"a\" />;"
        );
        assert_clean(codes(&source));
    }

    #[test]
    fn unknown_value_based_tag_reports_cannot_find_name() {
        assert_eq!(
            codes(&format!("{JSX_PREAMBLE} const x = <Missing />;")),
            [CANNOT_FIND_NAME.as_str()]
        );
    }

    #[test]
    fn unresolved_tag_names_report_cannot_find_name_in_every_name_shape() {
        for source in [
            format!("{JSX_PREAMBLE} const x = <Missing />;"),
            format!("{JSX_PREAMBLE} const x = <Missing.name />;"),
            format!("{JSX_PREAMBLE} const x = <Missing:name />;"),
        ] {
            assert_eq!(codes(&source), [CANNOT_FIND_NAME.as_str()], "{source}");
        }
    }

    #[test]
    fn non_callable_value_tag_reports_not_callable() {
        assert_eq!(
            codes(&format!("{JSX_PREAMBLE} const C = 42; const x = <C />;")),
            [JSX_ELEMENT_TYPE_NOT_CALLABLE.as_str()]
        );
    }

    #[test]
    fn dotted_tag_resolves_through_namespace_member_scopes() {
        let source = format!(
            "{JSX_PREAMBLE} namespace UI {{ \
                export function Button(props: {{ label: string }}) {{ return null; }} \
            }} \
            const ok = <UI.Button label=\"x\" />; \
            const bad = <UI.Button label={{1}} />;"
        );
        assert_eq!(codes(&source), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    // -- attribute type errors -----------------------------------------------------

    #[test]
    fn mistyped_intrinsic_attribute_reports_attributes_not_assignable() {
        assert_eq!(
            codes(&format!("{JSX_PREAMBLE} const x = <div id={{1}} />;")),
            [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]
        );
    }

    #[test]
    fn missing_required_intrinsic_attribute_is_an_error() {
        let source = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { id: string } } \
        } \
        const x = <div />;";
        assert_eq!(codes(source), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn mistyped_factory_prop_reports_attributes_not_assignable() {
        let source = format!(
            "{JSX_PREAMBLE} function Comp(props: {{ id: string }}) {{ return null; }} \
             const x = <Comp id={{1}} />;"
        );
        assert_eq!(codes(&source), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn bare_attribute_contributes_true() {
        let source = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { hidden?: boolean } } \
        } \
        const x = <div hidden />; \
        const y = <div hidden=\"yes\" />;";
        assert_eq!(codes(source), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    // -- children type checking -----------------------------------------------------

    #[test]
    fn text_children_check_against_the_children_prop() {
        let good = format!("{JSX_PREAMBLE} const x = <div>hello</div>;");
        assert_clean(codes(&good));

        let bad = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { children: number } } \
        } \
        const x = <div>hello</div>;";
        assert_eq!(codes(bad), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn expression_children_union_into_the_children_prop() {
        let bad = format!("{JSX_PREAMBLE} const n = 1; const x = <div>{{n}}</div>;");
        assert_eq!(codes(&bad), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn whitespace_only_children_contribute_no_children_prop() {
        let source = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { id?: string } } \
        } \
        const x = <div>   </div>;";
        assert_clean(codes(source));
    }

    #[test]
    fn spread_children_contribute_array_elements_and_keep_other_values_opaque() {
        let strings = format!(
            "{JSX_PREAMBLE} const items: string[] = []; const x = <div>{{...items}}</div>;"
        );
        assert_clean(codes(&strings));

        let numbers = format!(
            "{JSX_PREAMBLE} const items: number[] = []; const x = <div>{{...items}}</div>;"
        );
        assert_eq!(codes(&numbers), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);

        let opaque = format!(
            "{JSX_PREAMBLE} const items: unknown = null; const x = <div>{{...items}}</div>;"
        );
        assert_clean(codes(&opaque));
    }

    // -- spread attributes -------------------------------------------------------------

    #[test]
    fn spread_attributes_merge_into_the_props_object() {
        let good = format!(
            "{JSX_PREAMBLE} const extra = {{ id: \"x\" }}; const x = <div {{...extra}} />;"
        );
        assert_clean(codes(&good));

        let bad =
            format!("{JSX_PREAMBLE} const wrong = {{ id: 1 }}; const x = <div {{...wrong}} />;");
        assert_eq!(codes(&bad), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn later_spread_members_override_earlier_attributes() {
        let source = format!(
            "{JSX_PREAMBLE} const fix = {{ id: \"s\" }}; const x = <div id={{1}} {{...fix}} />;"
        );
        assert_clean(codes(&source));
    }

    #[test]
    fn opaque_spread_skips_element_props_assignability() {
        let source = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { id: string } } \
        } \
        const opaque: any = {}; \
        const element = <div {...opaque} />;";
        assert_clean(codes(source));
    }

    // -- factory function inference ----------------------------------------------------

    #[test]
    fn element_result_type_flows_from_the_factory_return_type() {
        let good = format!(
            "{JSX_PREAMBLE} function Comp(props: {{ id?: string }}): string {{ return \"x\"; }} \
             const x: string = <Comp />;"
        );
        assert_clean(codes(&good));

        let bad = format!(
            "{JSX_PREAMBLE} function Comp(props: {{ id?: string }}): string {{ return \"x\"; }} \
             const x: number = <Comp />;"
        );
        assert_eq!(codes(&bad), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn intrinsic_element_result_takes_the_jsx_element_type() {
        let bad = format!("{JSX_PREAMBLE} const x: number = <div />;");
        assert_eq!(codes(&bad), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn generic_factory_infers_type_arguments_from_the_props() {
        let source = format!(
            "{JSX_PREAMBLE} \
             function Comp<T>(props: {{ value: T }}): T {{ return props.value; }} \
             const ok: number = <Comp value={{1}} />; \
             const bad: string = <Comp value={{1}} />;"
        );
        assert_eq!(codes(&source), [TYPE_NOT_ASSIGNABLE.as_str()]);
    }

    #[test]
    fn generic_factory_signature_resolution_is_cached_per_declaration() {
        let one_use = format!(
            "{JSX_PREAMBLE} \
             function Comp<T>(props: {{ value: T }}): T {{ return props.value; }} \
             const number_value: number = <Comp value={{1}} />;"
        );
        let two_uses = format!(
            "{one_use} \
             const string_value: string = <Comp value={{\"value\"}} />;"
        );

        let (one_model, one_diagnostics) = bound(&one_use);
        let (two_model, two_diagnostics) = bound(&two_uses);
        assert!(one_diagnostics.is_empty(), "{one_diagnostics:?}");
        assert!(two_diagnostics.is_empty(), "{two_diagnostics:?}");
        assert_eq!(
            one_model.scopes().len(),
            two_model.scopes().len(),
            "a second JSX use must reuse the resolved declaration signature"
        );
    }

    #[test]
    fn generic_factory_respects_its_constraint() {
        let source = format!(
            "{JSX_PREAMBLE} \
             function Comp<T extends string>(props: {{ value: T }}) {{ return null; }} \
             const bad = <Comp value={{1}} />;"
        );
        assert_eq!(codes(&source), [JSX_ATTRIBUTES_NOT_ASSIGNABLE.as_str()]);
    }

    // -- malformed type parameters --------------------------------------------------------

    /// A generic JSX factory with a duplicate type parameter name must not
    /// panic the compiler. The binder reports the duplicate; the factory
    /// check degrades to a diagnostic instead of crashing on the type
    /// parameter lookup.
    #[test]
    fn generic_factory_with_duplicate_type_parameter_does_not_panic() {
        use super::super::DUPLICATE_DECLARATION;
        let source = format!(
            "{JSX_PREAMBLE} \
             function Comp<T, T>(props: {{ value: T }}) {{ return props.value; }} \
             const x = <Comp value={{1}} />;"
        );
        let diagnostics = codes(&source);
        // The compiler must not panic; it reports the duplicate declaration.
        assert!(
            diagnostics.contains(&DUPLICATE_DECLARATION.as_str()),
            "expected DUPLICATE_DECLARATION in {diagnostics:?}"
        );
    }

    // -- factory arity ---------------------------------------------------------------------------

    /// A candidate requiring more than the single synthesized props argument
    /// must not win selection: JSX supplies exactly one argument, so an
    /// arity-invalid candidate is skipped in favor of the first arity-valid
    /// one. Here the first overload requires two parameters (its props target
    /// would pass assignability but the second `string` argument is never
    /// supplied), so the one-parameter overload's `string` return must be
    /// selected instead of the first overload's `number`.
    #[test]
    fn factory_arity_gate_skips_candidates_requiring_more_than_props() {
        let source = format!(
            "{JSX_PREAMBLE} \
             declare function Comp(props: {{ id?: string }}, extra: string): number; \
             declare function Comp(props: {{ id?: string }}): string; \
             const x: string = <Comp />;"
        );
        assert_clean(codes(&source));
    }

    /// A tuple-rest candidate counts its rest minimum toward the arity gate
    /// exactly as an ordinary call does: `...rest: [string, number]` needs
    /// two more arguments past props, so the candidate is skipped even
    /// though a rest-blind arity would stop counting at the rest parameter.
    #[test]
    fn factory_arity_gate_counts_tuple_rest_minimum() {
        let source = format!(
            "{JSX_PREAMBLE} \
             declare function Comp(props: {{ id?: string }}, ...rest: [string, number]): number; \
             declare function Comp(props: {{ id?: string }}): string; \
             const x: string = <Comp />;"
        );
        assert_clean(codes(&source));
    }

    // -- callable shapes of value tags ------------------------------------------------------------

    /// A dotted member resolving to an `ObjectType` with call signatures
    /// must contribute candidates through the same grouping machinery an
    /// ordinary call uses, not only `Type::Function` values.
    #[test]
    fn object_with_call_signatures_resolves_as_a_jsx_factory() {
        let source = format!(
            "{JSX_PREAMBLE} \
             interface Factory {{ (props: {{ id?: string }}): string; }} \
             declare const comp: Factory; \
             const holder = {{ Comp: comp }}; \
             const x: string = <holder.Comp />;"
        );
        assert_clean(codes(&source));
    }

    /// A class tag constructs its instance through the class's construct
    /// signature; the diagnostic contract ("neither a construct nor a call
    /// signature") requires construct support. Props check against the
    /// constructor's parameter type.
    #[test]
    fn class_component_construct_signature_resolves_as_a_jsx_factory() {
        let source = format!(
            "{JSX_PREAMBLE} \
             class Widget {{ constructor(props: {{ id?: string }}) {{}} }} \
             const x = <Widget id=\"a\" />;"
        );
        assert_clean(codes(&source));
    }

    // -- dotted-tag member resolution degradation ---------------------------------------------------

    /// A dotted tag whose object resolves but lacks the member must anchor
    /// CANNOT_FIND_NAME at the failing member only, not the whole dotted
    /// span: the root identifier resolved fine, so the member step is the
    /// one that "cannot find" its name.
    #[test]
    fn dotted_tag_missing_member_anchors_cannot_find_name_on_the_member() {
        let source = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { id?: string } } \
        } \
        declare const UI: { label: string }; \
        const x = <UI.Button />;";
        let (_model, diagnostics) = bound(source);
        let member_offset = source.find("Button").expect("fixture contains Button");
        let member_pos = crate::source::Utf16Pos::new(member_offset);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>(),
            vec![CANNOT_FIND_NAME.as_str()],
        );
        let diagnostic = diagnostics
            .first()
            .expect("CANNOT_FIND_NAME already asserted");
        assert!(
            diagnostic.range().start() == member_pos,
            "expected CANNOT_FIND_NAME anchored at the failed member (offset {member_offset}), got {:?}",
            diagnostic.range(),
        );
    }

    /// The whole-tag anchor for a resolvable root and missing member stays
    /// distinguishable from a root miss: an unresolvable root keeps
    /// anchoring the full dotted span.
    #[test]
    fn root_miss_keeps_whole_tag_anchor() {
        let source = format!("{JSX_PREAMBLE} const x = <Missing.name />;");
        let (_model, diagnostics) = bound(&source);
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code().as_str())
                .collect::<Vec<_>>(),
            vec![CANNOT_FIND_NAME.as_str()],
        );
        let diagnostic = diagnostics
            .first()
            .expect("CANNOT_FIND_NAME already asserted");
        let name_start = source.find("Missing.name").expect("fixture contains tag") as usize;
        assert!(
            diagnostic.range().start().get() == name_start,
            "root miss anchors the whole dotted span, got {:?}",
            diagnostic.range(),
        );
    }

    // -- spread branch fold cap -----------------------------------------------------------------------
    /// The spread fold must cap the branch product: past the cap the
    /// remaining spread constituents merge in order (later members winning)
    /// instead of distributing. The pads below push the variant count to
    /// 256 (2^8), and the tail union would double it past the cap; the cap
    /// collapses the tail into its last-wins merged branch carrying
    /// `x: string`, which is assignable to the `x?: string` target. Without
    /// the cap the tail distributes, so branches carrying `x: number` make
    /// the folded props union fail against the target.
    #[test]
    fn spread_branch_fold_caps_branch_count_and_merges_beyond_the_cap() {
        let preamble = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { probe: { x?: string } } \
        } ";
        let mut spreads = String::new();
        for index in 0..9 {
            spreads.push_str(&format!(
                "const u{index}: {{ x{index}: string }} | {{ y{index}: number }} = {{ x{index}: \"s\" }}; "
            ));
        }
        let source = format!(
            "{preamble} \
             {spreads} \
             const tail: {{ x: number }} | {{ x: string }} = {{ x: \"ok\" }}; \
             const x = <probe {{...u0}} {{...u1}} {{...u2}} {{...u3}} {{...u4}} {{...u5}} {{...u6}} {{...u7}} {{...u8}} {{...tail}} />;"
        );
        assert_clean(codes(&source));
    }

    // -- namespace resolution degradation ------------------------------------------------

    #[test]
    fn intrinsic_elements_are_inert_without_a_jsx_namespace() {
        assert_clean(codes("const x = <div id={1} />;"));
    }

    #[test]
    fn nested_elements_and_fragments_check_recursively() {
        // `unknown` children keep the outer element clean so the nested
        // element's own diagnostic is the only one observed.
        let bad = "namespace JSX { \
            interface Element {} \
            interface IntrinsicElements { div: { children?: unknown } } \
        } \
        const x = <div><section /></div>;";
        assert_eq!(codes(bad), [JSX_INTRINSIC_ELEMENT_NOT_FOUND.as_str()]);

        let fragment = format!("{JSX_PREAMBLE} const x = <><div>text</div></>;");
        assert_clean(codes(&fragment));
    }

    // -- intrinsic type inventory --------------------------------------------------

    #[test]
    fn standard_intrinsic_json_math_atomics_resolve_in_type_position() {
        assert_clean(codes(
            "type JSONType = JSON; type MathType = Math; type AtomicsType = Atomics;",
        ));
    }
}
