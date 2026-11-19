//! ECMAScript private names (`#x`) below ES2022: WeakMap and WeakSet state
//! slots, the `__classPrivateField{Get,Set,In}` helper calls, and the
//! per-class declaration tsc prints after the class body.
//!
//! Each class that declares private members pushes one `PrivateClassScope`
//! onto the rewriter for the duration of its member walk; a private access
//! resolves against the innermost enclosing class that declares the name.

use std::collections::VecDeque;

use crate::source::TextRange;
use crate::syntax::*;

use super::helpers::HelperKind;
use super::{LanguageFeature, Rewriter};

/// What one private declaration lowers to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrivateKind {
    Field,
    Method,
    Get,
    Set,
}

impl PrivateKind {
    fn label(self) -> &'static str {
        match self {
            Self::Field => "f",
            Self::Method => "m",
            Self::Get | Self::Set => "a",
        }
    }

    fn function_suffix(self) -> &'static str {
        match self {
            Self::Get => "_get",
            Self::Set => "_set",
            Self::Field | Self::Method => "",
        }
    }
}

/// One private declaration's storage. `state` is the WeakMap, the WeakSet,
/// or the class alias; `holder` is the function or `{ value }` object a
/// helper call passes as its last argument.
#[derive(Clone)]
pub(super) struct PrivateSlot {
    name: String,
    kind: PrivateKind,
    pub(super) state: IdentifierNode,
    pub(super) holder: Option<IdentifierNode>,
}

/// The slots of the class being lowered, in member order.
pub(super) struct PrivateClassScope {
    members: Vec<PrivateSlot>,
}

/// Which side of a private name an expression touches.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum PrivateAccess {
    Read,
    Write,
    In,
}

/// A resolved access: what a helper call passes for `state`, `kind`, and `f`.
pub(super) struct ResolvedPrivate {
    state: IdentifierNode,
    kind: &'static str,
    holder: Option<IdentifierNode>,
}

/// The lowering facts of one private class member.
struct PrivateMemberInfo {
    name: String,
    is_static: bool,
    kind: PrivateKind,
}

/// The minted storage of one class, kept between the pre-pass and the walk.
pub(super) struct PrivatePlan {
    pub(super) slots: VecDeque<PrivateSlot>,
    pub(super) alias: Option<IdentifierNode>,
    pub(super) instances: Option<IdentifierNode>,
    pub(super) weakmaps: Vec<Expr>,
    pub(super) weakset: Option<Expr>,
    /// `_A_m = function _A_m() { ... }`, in member order.
    pub(super) functions: Vec<Expr>,
    /// The record and initial value of each static field, in member order.
    pub(super) static_fields: Vec<(IdentifierNode, Expr)>,
}

impl Rewriter<'_> {
    /// Private names lower to WeakMap state whenever the target has classes
    /// but no native private fields (ES2015 through ES2021).
    pub(super) fn private_lowering_active(&self) -> bool {
        !Self::needs(LanguageFeature::Classes, self.options)
            && !self.options.target.supports(LanguageFeature::ClassFields)
    }

    /// The name text of a `#name` property, without the hash.
    pub(super) fn private_property_name(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Private(node) => Some(self.hashless_name(node.data().token())),
            _ => None,
        }
    }

    /// The name text of a `#name` member access, without the hash.
    pub(super) fn private_member_name(&self, property: &MemberProperty) -> Option<String> {
        match property {
            MemberProperty::Private(node) => Some(self.hashless_name(node.data().token())),
            _ => None,
        }
    }

    /// Whether an identifier expression is the `#name` operand of an `in` test.
    pub(super) fn private_identifier_name(&self, expression: &Expr) -> Option<String> {
        let Expression::Identifier(identifier) = expression.data() else {
            return None;
        };
        let text = self.token_text(identifier.data().token());
        text.starts_with('#')
            .then(|| text.trim_start_matches('#').to_owned())
    }

    fn private_member_info(&self, member: &ClassMemberNode) -> Option<PrivateMemberInfo> {
        match member.data() {
            ClassMember::Property(property) => {
                if property.modifiers.is_declare || property.modifiers.is_abstract {
                    return None;
                }
                let name = self.private_property_name(&property.name)?;
                Some(PrivateMemberInfo {
                    name,
                    is_static: property.modifiers.is_static,
                    kind: PrivateKind::Field,
                })
            }
            ClassMember::Method(method) => {
                let name = self.private_property_name(&method.name)?;
                let kind = match method.modifier {
                    PropertyModifier::Get => PrivateKind::Get,
                    PropertyModifier::Set => PrivateKind::Set,
                    PropertyModifier::None => PrivateKind::Method,
                };
                Some(PrivateMemberInfo {
                    name,
                    is_static: method.modifiers.is_static,
                    kind,
                })
            }
            _ => None,
        }
    }

    fn hashless_name(&self, token: &Token) -> String {
        self.token_text(token).trim_start_matches('#').to_owned()
    }

    /// Mints the storage identifiers of the class's private members, pushes
    /// the class scope, and renames references to the class's own name when
    /// static private members need the alias. The member walk pops the slot
    /// queue, one slot per private member, in member order.
    pub(super) fn plan_private_class(
        &mut self,
        class: &mut ClassDeclaration,
        static_target: Option<&IdentifierNode>,
        inferred_name: Option<&str>,
    ) -> PrivatePlan {
        let infos: Vec<PrivateMemberInfo> = class
            .members
            .iter()
            .filter_map(|member| self.private_member_info(member))
            .collect();
        let display = class
            .name
            .as_ref()
            .and_then(|name| self.identifier_name(name))
            .or_else(|| inferred_name.map(str::to_owned));
        let has_static = infos.iter().any(|info| info.is_static);
        let instances = infos
            .iter()
            .any(|info| !info.is_static && info.kind != PrivateKind::Field)
            .then(|| {
                let ident = self.private_state_ident(display.as_deref(), "instances");
                self.push_temp_hoist(&ident);
                ident
            });
        if let Some(temp) = static_target
            && let Some(scope) = self.expression_temp_scopes.last_mut()
        {
            scope.retain(|hoisted| hoisted.id() != temp.id());
        }
        let alias = has_static.then(|| match static_target {
            Some(temp) => {
                self.push_temp_hoist(temp);
                temp.clone()
            }
            None => self.reserved_temp(),
        });
        let mut slots = VecDeque::with_capacity(infos.len());
        let mut weakmaps = Vec::new();
        let mut weakset = None;
        for info in &infos {
            let state = if info.is_static {
                alias.clone().expect("static private member has an alias")
            } else if info.kind == PrivateKind::Field {
                let ident = self.private_state_ident(display.as_deref(), &info.name);
                let range = ident.range();
                let value = self.new_weak_collection("WeakMap", range);
                weakmaps.push(self.temp_assignment(&ident, value, range));
                self.push_temp_hoist(&ident);
                ident
            } else {
                instances.clone().expect("instance member has the WeakSet")
            };
            let holder = (info.kind != PrivateKind::Field || info.is_static).then(|| {
                let base = format!("{}{}", info.name, info.kind.function_suffix());
                let ident = self.private_state_ident(display.as_deref(), &base);
                self.push_temp_hoist(&ident);
                ident
            });
            if info.kind != PrivateKind::Field && !info.is_static && weakset.is_none() {
                let instances_ident = instances.as_ref().expect("instance member has the WeakSet");
                let range = instances_ident.range();
                let value = self.new_weak_collection("WeakSet", range);
                weakset = Some(self.temp_assignment(instances_ident, value, range));
            }
            slots.push_back(PrivateSlot {
                name: info.name.clone(),
                kind: info.kind,
                state,
                holder,
            });
        }
        if let (true, Some(name), Some(alias)) = (has_static, class.name.as_ref(), alias.as_ref())
            && let Some(original) = self.identifier_name(name)
        {
            let class_symbol = self.model.and_then(|model| model.reference(name.id()));
            class.members = self.rename_class_self_in_members(
                std::mem::take(&mut class.members),
                &original,
                class_symbol,
                alias,
            );
        }
        if let (false, Some(temp)) = (has_static, static_target) {
            self.push_temp_hoist(temp);
        }
        let scope = PrivateClassScope {
            members: slots.iter().cloned().collect(),
        };
        self.private_class_scopes.push(scope);
        PrivatePlan {
            slots,
            alias,
            instances,
            weakmaps,
            weakset,
            functions: Vec::new(),
            static_fields: Vec::new(),
        }
    }

    /// Resolves a private name against the innermost enclosing class that
    /// declares it. A name carrying only the other accessor side answers
    /// with the accessor kind and no holder, which is the helper's
    /// throw-at-runtime form.
    pub(super) fn resolve_private(
        &self,
        name: &str,
        access: PrivateAccess,
    ) -> Option<ResolvedPrivate> {
        for scope in self.private_class_scopes.iter().rev() {
            let matches: Vec<&PrivateSlot> = scope
                .members
                .iter()
                .filter(|slot| slot.name == name)
                .collect();
            if matches.is_empty() {
                continue;
            }
            let (slot, bare) = match access {
                PrivateAccess::In => (*matches.first()?, false),
                PrivateAccess::Read => (
                    preferred_slot(&matches, PrivateKind::Get),
                    matches.iter().all(|slot| slot.kind == PrivateKind::Set),
                ),
                PrivateAccess::Write => (
                    preferred_slot(&matches, PrivateKind::Set),
                    matches.iter().all(|slot| slot.kind == PrivateKind::Get),
                ),
            };
            let holder = if bare { None } else { slot.holder.clone() };
            return Some(ResolvedPrivate {
                state: slot.state.clone(),
                kind: slot.kind.label(),
                holder,
            });
        }
        None
    }

    /// `__classPrivateFieldGet(receiver, state, kind, f)`.
    pub(super) fn private_get_call(
        &mut self,
        receiver: Expr,
        resolved: &ResolvedPrivate,
        range: TextRange,
    ) -> Expr {
        let helper = self.helper_ident(HelperKind::ClassPrivateFieldGet);
        let mut arguments = vec![
            CallArgument::Expression(Box::new(receiver)),
            self.state_argument(&resolved.state),
            self.kind_argument(resolved.kind, range),
        ];
        if let Some(holder) = resolved.holder.as_ref() {
            arguments.push(CallArgument::Expression(Box::new(
                self.node(holder.range(), Expression::Identifier(holder.clone())),
            )));
        }
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(helper),
                optional: false,
                type_arguments: None,
                arguments,
            }),
        )
    }

    /// `__classPrivateFieldSet(receiver, state, value, kind, f)`.
    pub(super) fn private_set_call(
        &mut self,
        receiver: Expr,
        value: Expr,
        resolved: &ResolvedPrivate,
        range: TextRange,
    ) -> Expr {
        let helper = self.helper_ident(HelperKind::ClassPrivateFieldSet);
        let mut arguments = vec![
            CallArgument::Expression(Box::new(receiver)),
            self.state_argument(&resolved.state),
            CallArgument::Expression(Box::new(value)),
            self.kind_argument(resolved.kind, range),
        ];
        if let Some(holder) = resolved.holder.as_ref() {
            arguments.push(CallArgument::Expression(Box::new(
                self.node(holder.range(), Expression::Identifier(holder.clone())),
            )));
        }
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(helper),
                optional: false,
                type_arguments: None,
                arguments,
            }),
        )
    }

    /// `__classPrivateFieldIn(state, receiver)`.
    pub(super) fn private_in_call(
        &mut self,
        receiver: Expr,
        resolved: &ResolvedPrivate,
        range: TextRange,
    ) -> Expr {
        let helper = self.helper_ident(HelperKind::ClassPrivateFieldIn);
        let arguments = vec![
            self.state_argument(&resolved.state),
            CallArgument::Expression(Box::new(receiver)),
        ];
        self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(helper),
                optional: false,
                type_arguments: None,
                arguments,
            }),
        )
    }

    /// A receiver that is read twice: `this` stays as written, and so does a
    /// plain name ahead of a call. Anything else lands in a temporary, which
    /// a read captures in parentheses and a write captures bare.
    pub(super) fn private_captured_receiver(
        &mut self,
        receiver: &Expr,
        access: PrivateAccess,
    ) -> (Expr, Expr) {
        let rewritten = self.rewrite_expr(receiver);
        let reused = match rewritten.data() {
            Expression::This => true,
            Expression::Identifier(_) => access == PrivateAccess::Read,
            _ => false,
        };
        if reused {
            return (rewritten.clone(), rewritten);
        }
        let range = rewritten.range();
        let temp = self.expression_temp();
        let reference = self.node(temp.range(), Expression::Identifier(temp.clone()));
        let target = self.node(temp.range(), AssignmentTarget::Identifier(temp));
        let assignment = self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: target,
                right: Box::new(rewritten),
            }),
        );
        let first = match access {
            PrivateAccess::Read => {
                self.node(range, Expression::Parenthesized(Box::new(assignment)))
            }
            PrivateAccess::Write | PrivateAccess::In => assignment,
        };
        (first, reference)
    }

    /// Rewrites `this.#m(args)` into `__classPrivateFieldGet(...).call(receiver, args)`,
    /// with the null-guarded form for `?.()`.
    pub(super) fn lower_private_member_call(
        &mut self,
        expression: &Expr,
        call: &CallExpression,
    ) -> Option<Expr> {
        let Expression::Member(member) = call.callee.data() else {
            return None;
        };
        let name = self.private_member_name(&member.property)?;
        let range = expression.range();
        let object_range = member.object.range();
        let arguments = self.rewrite_call_arguments(&call.arguments);
        let Some(resolved) = self.resolve_private(&name, PrivateAccess::Read) else {
            let object = self.rewrite_expr(&member.object);
            let callee = self.empty_property_member(object, range);
            return Some(self.node(
                range,
                Expression::Call(CallExpression {
                    callee: Box::new(callee),
                    optional: false,
                    type_arguments: None,
                    arguments,
                }),
            ));
        };
        let (get_receiver, use_receiver) =
            self.private_captured_receiver(&member.object, PrivateAccess::Read);
        let get = self.private_get_call(get_receiver, &resolved, object_range);
        if call.optional {
            let result = self.expression_temp();
            let get_range = get.range();
            let capture_target =
                self.node(result.range(), AssignmentTarget::Identifier(result.clone()));
            let capture = self.node(
                get_range,
                Expression::Assignment(AssignmentExpression {
                    operator: AssignmentOperator::Assign,
                    left: capture_target,
                    right: Box::new(get),
                }),
            );
            let captured = self.node(get_range, Expression::Parenthesized(Box::new(capture)));
            let reference = self.node(result.range(), Expression::Identifier(result.clone()));
            let null_check = self.strict_equal_null(&captured, range);
            let void_check = self.strict_equal_void(&reference, range);
            let test = self.node(
                range,
                Expression::Logical(LogicalExpression {
                    operator: LogicalOperator::Or,
                    left: Box::new(null_check),
                    right: Box::new(void_check),
                }),
            );
            let callee = self.member_access(reference, "call", range);
            let mut call_arguments = vec![CallArgument::Expression(Box::new(use_receiver))];
            call_arguments.extend(arguments);
            let invoked = self.node(
                range,
                Expression::Call(CallExpression {
                    callee: Box::new(callee),
                    optional: false,
                    type_arguments: None,
                    arguments: call_arguments,
                }),
            );
            let skipped = self.void_zero(range);
            return Some(self.node(
                range,
                Expression::Conditional(ConditionalExpression {
                    test: Box::new(test),
                    consequent: Box::new(skipped),
                    alternate: Box::new(invoked),
                }),
            ));
        }
        let callee = self.member_access(get, "call", range);
        let mut call_arguments = vec![CallArgument::Expression(Box::new(use_receiver))];
        call_arguments.extend(arguments);
        Some(self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: call_arguments,
            }),
        ))
    }

    /// Rewrites ``this.#m`tpl` `` into `__classPrivateFieldGet(...).bind(receiver)`.
    pub(super) fn lower_private_tagged_template(
        &mut self,
        expression: &Expr,
        tagged: &TaggedTemplateExpression,
    ) -> Option<Expr> {
        let Expression::Member(member) = tagged.tag.data() else {
            return None;
        };
        let name = self.private_member_name(&member.property)?;
        let range = expression.range();
        let object_range = member.object.range();
        let template = self.rewrite_template(&tagged.template);
        let Some(resolved) = self.resolve_private(&name, PrivateAccess::Read) else {
            let object = self.rewrite_expr(&member.object);
            let tag = self.empty_property_member(object, range);
            return Some(self.node(
                range,
                Expression::TaggedTemplate(TaggedTemplateExpression {
                    tag: Box::new(tag),
                    template,
                }),
            ));
        };
        let (get_receiver, use_receiver) =
            self.private_captured_receiver(&member.object, PrivateAccess::Read);
        let get = self.private_get_call(get_receiver, &resolved, object_range);
        let callee = self.member_access(get, "bind", range);
        let tag = self.call_expression(range, callee, vec![use_receiver]);
        Some(self.node(
            range,
            Expression::TaggedTemplate(TaggedTemplateExpression {
                tag: Box::new(tag),
                template,
            }),
        ))
    }

    /// Rewrites an assignment whose target is a private member into the
    /// `__classPrivateFieldSet` form; a compound operator reads the old
    /// value through `__classPrivateFieldGet` first.
    pub(super) fn lower_private_member_assignment(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
    ) -> Option<Expr> {
        let (object, property, object_range) = match assignment.left.data() {
            AssignmentTarget::Member(member) => (
                member.object.as_ref(),
                &member.property,
                member.object.range(),
            ),
            AssignmentTarget::Invalid(operand) => {
                let member = asserted_member(operand)?;
                (
                    member.object.as_ref(),
                    &member.property,
                    member.object.range(),
                )
            }
            _ => return None,
        };
        let name = self.private_member_name(property)?;
        let range = expression.range();
        let Some(resolved) = self.resolve_private(&name, PrivateAccess::Write) else {
            let right = self.rewrite_expr(&assignment.right);
            let object = self.rewrite_expr(object);
            let target = self.empty_property_target(object, object_range);
            return Some(self.node(
                range,
                Expression::Assignment(AssignmentExpression {
                    operator: assignment.operator,
                    left: target,
                    right: Box::new(right),
                }),
            ));
        };
        if assignment.operator == AssignmentOperator::Assign {
            let right = self.rewrite_expr(&assignment.right);
            let receiver = self.rewrite_expr(object);
            return Some(self.private_set_call(receiver, right, &resolved, range));
        }
        let receivers = if matches!(object.data(), Expression::This) {
            let rewritten = self.rewrite_expr(object);
            (rewritten.clone(), rewritten)
        } else {
            self.private_captured_receiver(object, PrivateAccess::Write)
        };
        let right = self.rewrite_expr(&assignment.right);
        let read = self.private_get_call(receivers.1, &resolved, object_range);
        let value = if assignment.operator == AssignmentOperator::ExponentiateAssign {
            self.math_pow(read, right, range)
        } else {
            let binary_operator = compound_operator(assignment.operator);
            self.node(
                range,
                Expression::Binary(BinaryExpression {
                    operator: binary_operator,
                    left: Box::new(read),
                    right: Box::new(right),
                }),
            )
        };
        Some(self.private_set_call(receivers.0, value, &resolved, range))
    }

    /// Rewrites `++this.#x` and friends: a prefix and a discarded postfix
    /// set the stepped value, a read postfix keeps the old value in one
    /// more temp and evaluates to it.
    pub(super) fn lower_private_member_update(
        &mut self,
        expression: &Expr,
        update: &UpdateExpression,
    ) -> Option<Expr> {
        let AssignmentTarget::Member(member) = update.argument.data() else {
            return None;
        };
        let name = self.private_member_name(&member.property)?;
        let range = expression.range();
        let object_range = member.object.range();
        let resolved = self.resolve_private(&name, PrivateAccess::Read)?;
        let keeps_value = self.statement_expression != Some(expression.id());
        let receivers = if matches!(member.object.data(), Expression::This) {
            let rewritten = self.rewrite_expr(&member.object);
            (rewritten.clone(), rewritten)
        } else {
            self.private_captured_receiver(&member.object, PrivateAccess::Write)
        };
        let old = (!update.prefix && keeps_value).then(|| self.expression_temp());
        let current = self.expression_temp();
        let read = self.private_get_call(receivers.1, &resolved, object_range);
        let read_assignment = self.temp_assignment(&current, read, range);
        let step_target = self.node(
            current.range(),
            AssignmentTarget::Identifier(current.clone()),
        );
        let stepped = self.node(
            range,
            Expression::Update(UpdateExpression {
                operator: update.operator,
                argument: Box::new(step_target),
                prefix: update.prefix,
            }),
        );
        let final_value = self.node(current.range(), Expression::Identifier(current.clone()));
        let stored = match &old {
            Some(old_temp) => {
                let stepped_assignment = self.temp_assignment(old_temp, stepped, range);
                self.sequence(
                    vec![read_assignment, stepped_assignment, final_value],
                    range,
                )
            }
            None if update.prefix => self.sequence(vec![read_assignment, stepped], range),
            None => self.sequence(vec![read_assignment, stepped, final_value], range),
        };
        let set = self.private_set_call(receivers.0, stored, &resolved, range);
        Some(match old {
            Some(old_temp) => {
                let old_value = self.node(old_temp.range(), Expression::Identifier(old_temp));
                self.sequence(vec![set, old_value], range)
            }
            None => set,
        })
    }

    /// The member access an unresolved private name collapses to: the
    /// property prints empty and the checker's error stays.
    fn empty_property_member(&mut self, object: Expr, range: TextRange) -> Expr {
        let property = MemberProperty::Named(self.ident(""));
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(object),
                property,
                optional: false,
            }),
        )
    }

    fn empty_property_target(&mut self, object: Expr, range: TextRange) -> AssignmentTargetNode {
        let property = MemberProperty::Named(self.ident(""));
        self.node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        )
    }

    /// `_X_name.set(this, init)` — the constructor's private field store.
    pub(super) fn private_field_set_statement(
        &mut self,
        state: &IdentifierNode,
        value: Expr,
        range: TextRange,
    ) -> Stmt {
        let receiver = self.node(range, Expression::This);
        let map = self.node(state.range(), Expression::Identifier(state.clone()));
        let callee = self.member_access(map, "set", range);
        let call = self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(receiver)),
                    CallArgument::Expression(Box::new(value)),
                ],
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    /// `_X_instances.add(this)` — the brand check of a method class.
    pub(super) fn private_brand_statement(
        &mut self,
        instances: &IdentifierNode,
        range: TextRange,
    ) -> Stmt {
        let receiver = self.node(range, Expression::This);
        let set = self.node(instances.range(), Expression::Identifier(instances.clone()));
        let callee = self.member_access(set, "add", range);
        let call = self.call_expression(range, callee, vec![receiver]);
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    /// The `_a = A` item of the post-class comma for a declaration.
    pub(super) fn private_alias_assignment(
        &mut self,
        alias: &IdentifierNode,
        class_name: &IdentifierNode,
    ) -> Expr {
        let range = class_name.range();
        let value = self.node(range, Expression::Identifier(class_name.clone()));
        self.temp_assignment(alias, value, range)
    }

    /// `_A_m = function _A_m(params) { ... }`: a private method or accessor
    /// leaves the class and becomes a function the helpers call.
    pub(super) fn private_function_assignment(
        &mut self,
        holder: &IdentifierNode,
        function: FunctionLike,
        range: TextRange,
    ) -> Expr {
        let function = FunctionLike {
            name: Some(holder.clone()),
            ..function
        };
        let value = self.node(range, Expression::Function(FunctionExpression { function }));
        self.temp_assignment(holder, value, range)
    }

    /// What follows the class: the storage of its private members, then one
    /// `_A_f = { value: init };` per static field. A declaration joins the
    /// storage into one comma expression that starts with the alias; a class
    /// expression keeps the items apart for the comma list it already sits in.
    pub(super) fn private_postlude(
        &mut self,
        plan: PrivatePlan,
        declared_name: Option<&IdentifierNode>,
        range: TextRange,
    ) -> Vec<Stmt> {
        let mut storage = Vec::new();
        if let (Some(alias), Some(name)) = (plan.alias.as_ref(), declared_name) {
            storage.push(self.private_alias_assignment(alias, name));
        }
        storage.extend(plan.weakmaps);
        storage.extend(plan.weakset);
        storage.extend(plan.functions);
        let mut out = Vec::new();
        if declared_name.is_none() {
            for item in storage {
                out.push(self.expression_statement(item, range));
            }
        } else if !storage.is_empty() {
            let joined = if storage.len() == 1 {
                storage.remove(0)
            } else {
                self.sequence(storage, range)
            };
            out.push(self.expression_statement(joined, range));
        }
        for (holder, init) in plan.static_fields {
            let name = self.ident("value");
            let property = ObjectProperty {
                name: PropertyName::Identifier(name),
                value: Box::new(init),
                modifier: PropertyModifier::None,
                shorthand: false,
            };
            let member = self.syn_node(range, ObjectMember::Property(property));
            let record = self.syn_node(
                range,
                Expression::Object(ObjectLiteral {
                    members: vec![member],
                }),
            );
            self.alternate_layout.insert(record.id());
            let assignment = self.temp_assignment(&holder, record, range);
            out.push(self.expression_statement(assignment, range));
        }
        out
    }

    fn private_state_ident(&mut self, display: Option<&str>, member: &str) -> IdentifierNode {
        let base = match display {
            Some(class) => format!("_{class}_{member}"),
            None => format!("_{member}"),
        };
        let occupied = self
            .occupied_names
            .get_or_insert_with(|| super::identifier_names(self.file));
        let mut suffix = 0;
        let name = loop {
            let candidate = if suffix == 0 {
                base.clone()
            } else {
                format!("{base}_{suffix}")
            };
            if occupied.insert(candidate.clone()) {
                break candidate;
            }
            suffix += 1;
        };
        self.ident(&name)
    }

    /// A private storage name or class alias joins the temporaries of the
    /// enclosing function.
    fn push_temp_hoist(&mut self, ident: &IdentifierNode) {
        if let Some(scope) = self.expression_temp_scopes.last_mut() {
            scope.push(ident.clone());
        }
    }

    fn temp_assignment(&mut self, target: &IdentifierNode, value: Expr, range: TextRange) -> Expr {
        let left = self.node(target.range(), AssignmentTarget::Identifier(target.clone()));
        self.node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        )
    }

    fn new_weak_collection(&mut self, collection: &str, range: TextRange) -> Expr {
        let callee = self.ident_expr(collection);
        self.node(
            range,
            Expression::New(NewExpression {
                callee: Box::new(callee),
                type_arguments: None,
                arguments: Vec::new(),
            }),
        )
    }

    fn state_argument(&mut self, state: &IdentifierNode) -> CallArgument {
        CallArgument::Expression(Box::new(
            self.node(state.range(), Expression::Identifier(state.clone())),
        ))
    }

    fn kind_argument(&mut self, kind: &str, range: TextRange) -> CallArgument {
        let literal = self.string_literal(kind);
        CallArgument::Expression(Box::new(
            self.node(range, Expression::Literal(Literal::String(literal))),
        ))
    }

    /// Whether a destructuring pattern writes a private member: a `this.#x`
    /// style member target or an invalid target wrapping one, at any depth.
    pub(super) fn pattern_has_private_target(&self, target: &AssignmentTargetNode) -> bool {
        match target.data() {
            AssignmentTarget::Object(pattern) => pattern
                .properties
                .iter()
                .any(|property| self.pattern_has_private_target(&property.target)),
            AssignmentTarget::Array(pattern) => pattern.elements.iter().any(|element| {
                match element {
                    AssignmentArrayElement::Target(target)
                    | AssignmentArrayElement::Rest(target) => {
                        self.pattern_has_private_target(target)
                    }
                    AssignmentArrayElement::Elision | AssignmentArrayElement::Missing(_) => false,
                }
            }),
            AssignmentTarget::Member(member) => {
                matches!(member.property, MemberProperty::Private(_))
            }
            AssignmentTarget::Invalid(operand) => asserted_member(operand).is_some_and(|member| {
                matches!(member.property, MemberProperty::Private(_))
            }),
            _ => false,
        }
    }

    /// Rewrites a destructuring assignment whose pattern writes private
    /// members: each private target becomes a setter that routes the write
    /// through `__classPrivateFieldSet`. Receivers that are not plain
    /// identifiers are captured once, after the right-hand side, and the
    /// captures lead the assignment inside one sequence: the right-hand side
    /// runs first, matching destructuring evaluation order. Captures stay
    /// outside the setter body because `this` inside the setter would bind to
    /// the setter's own object literal.
    pub(super) fn lower_private_destructured_assignment(
        &mut self,
        expression: &Expr,
        assignment: &AssignmentExpression,
    ) -> Option<Expr> {
        if !matches!(
            assignment.left.data(),
            AssignmentTarget::Object(_) | AssignmentTarget::Array(_)
        ) || !self.private_lowering_active()
            || !self.pattern_has_private_target(&assignment.left)
        {
            return None;
        }
        let right = self.rewrite_expr(&assignment.right);
        let mut captures = Vec::new();
        let left = self.rewrite_private_destructured_target(&assignment.left, &mut captures);
        if captures.is_empty() {
            return Some(self.node(
                expression.range(),
                Expression::Assignment(AssignmentExpression {
                    operator: assignment.operator,
                    left,
                    right: Box::new(right),
                }),
            ));
        }
        let rhs_temp = self.expression_temp();
        let rhs_capture = self.temp_assignment(&rhs_temp, right, expression.range());
        let rhs_ref = self.node(
            rhs_temp.range(),
            Expression::Identifier(rhs_temp),
        );
        let mut parts = Vec::with_capacity(captures.len() + 2);
        parts.push(rhs_capture);
        parts.extend(captures);
        parts.push(self.node(
            expression.range(),
            Expression::Assignment(AssignmentExpression {
                operator: assignment.operator,
                left,
                right: Box::new(rhs_ref),
            }),
        ));
        Some(self.sequence(parts, expression.range()))
    }

    /// Rewrites one destructuring target, routing private member targets
    /// through the setter form and delegating every other target to the
    /// ordinary assignment-target rewrite so exports and member objects
    /// still lower.
    fn rewrite_private_destructured_target(
        &mut self,
        target: &AssignmentTargetNode,
        captures: &mut Vec<Expr>,
    ) -> AssignmentTargetNode {
        match target.data() {
            AssignmentTarget::Object(pattern) => {
                let properties = pattern
                    .properties
                    .iter()
                    .map(|property| AssignmentObjectProperty {
                        name: self.rewrite_property_name(&property.name),
                        target: self.rewrite_private_destructured_target(
                            &property.target,
                            captures,
                        ),
                        initializer: property
                            .initializer
                            .as_deref()
                            .map(|value| Box::new(self.rewrite_expr(value))),
                        rest: property.rest,
                    })
                    .collect();
                self.node(
                    target.range(),
                    AssignmentTarget::Object(AssignmentObjectPattern { properties }),
                )
            }
            AssignmentTarget::Array(pattern) => {
                let elements = pattern
                    .elements
                    .iter()
                    .map(|element| match element {
                        AssignmentArrayElement::Target(inner) => {
                            AssignmentArrayElement::Target(
                                self.rewrite_private_destructured_target(inner, captures),
                            )
                        }
                        AssignmentArrayElement::Rest(inner) => AssignmentArrayElement::Rest(
                            self.rewrite_private_destructured_target(inner, captures),
                        ),
                        other => other.clone(),
                    })
                    .collect();
                self.node(
                    target.range(),
                    AssignmentTarget::Array(AssignmentArrayPattern { elements }),
                )
            }
            AssignmentTarget::Member(member) => {
                if let Some(name) = self.private_member_name(&member.property) {
                    return self.rewrite_private_destructured_member(
                        member.object.as_ref(),
                        &name,
                        captures,
                        target.range(),
                    );
                }
                self.rewrite_member_target(member, target.range())
            }
            AssignmentTarget::Invalid(operand) => {
                if let Some(member) = asserted_member(operand)
                    && let Some(name) = self.private_member_name(&member.property)
                {
                    return self.rewrite_private_destructured_member(
                        member.object.as_ref(),
                        &name,
                        captures,
                        target.range(),
                    );
                }
                target.clone()
            }
            _ => self.rewrite_assignment_target(target),
        }
    }

    /// Rewrites one private member target inside a destructuring pattern
    /// into `({ set value(v) { __classPrivateFieldSet(receiver, state, v,
    /// kind, f); } }).value`. A plain identifier receiver is used as is;
    /// any other receiver is captured into a hoisted temporary by the caller,
    /// after the right-hand side, so `this` keeps its outer binding.
    fn rewrite_private_destructured_member(
        &mut self,
        object: &Expr,
        name: &str,
        captures: &mut Vec<Expr>,
        range: TextRange,
    ) -> AssignmentTargetNode {
        let Some(resolved) = self.resolve_private(name, PrivateAccess::Write) else {
            let rewritten_object = self.rewrite_expr(object);
            let property = MemberProperty::Named(self.ident(""));
            return self.node(
                range,
                AssignmentTarget::Member(AssignmentMemberTarget {
                    object: Box::new(rewritten_object),
                    property,
                }),
            );
        };
        let rewritten_object = self.rewrite_expr(object);
        let receiver = match rewritten_object.data() {
            Expression::Identifier(_) => rewritten_object,
            _ => {
                let temp = self.expression_temp();
                let capture = self.temp_assignment(&temp, rewritten_object, range);
                captures.push(capture);
                self.node(temp.range(), Expression::Identifier(temp))
            }
        };
        let setter = self.private_destructured_setter(receiver, &resolved, range);
        self.node(range, AssignmentTarget::Invalid(Box::new(setter)))
    }

    /// `({ set value(v) { __classPrivateFieldSet(receiver, state, v, kind,
    /// f); } }).value` — the assignment-target form of a private write
    /// that a destructuring pattern can carry.
    fn private_destructured_setter(
        &mut self,
        receiver: Expr,
        resolved: &ResolvedPrivate,
        range: TextRange,
    ) -> Expr {
        let value_name = self.temp_ident();
        let value_ident = self.node(
            value_name.range(),
            Expression::Identifier(value_name.clone()),
        );
        let call = self.private_set_call(receiver, value_ident, resolved, range);
        let statement = self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        );
        let block = self.node(range, Block { statements: vec![statement] });
        let binding = self.node(
            value_name.range(),
            BindingPattern::Identifier(value_name.clone()),
        );
        let parameter = self.node(
            range,
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers::default(),
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let function = FunctionLike {
            decorators: Vec::new(),
            name: None,
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters: vec![parameter],
            return_type: None,
            body: Some(FunctionBody::Block(block)),
        };
        let property_name = self.ident("value");
        let method = self.syn_node(
            range,
            ObjectMember::Method(ObjectMethod {
                name: PropertyName::Identifier(property_name.clone()),
                modifier: PropertyModifier::Set,
                function,
            }),
        );
        let object = self.syn_node(
            range,
            Expression::Object(ObjectLiteral {
                members: vec![method],
            }),
        );
        self.alternate_layout.insert(object.id());
        let parenthesized = self.syn_node(range, Expression::Parenthesized(Box::new(object)));
        self.node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(parenthesized),
                property: MemberProperty::Named(property_name),
                optional: false,
            }),
        )
    }
}

fn preferred_slot<'s>(matches: &[&'s PrivateSlot], preferred: PrivateKind) -> &'s PrivateSlot {
    matches
        .iter()
        .find(|slot| slot.kind == preferred)
        .or_else(|| matches.iter().find(|slot| slot.kind == PrivateKind::Field))
        .or_else(|| matches.iter().find(|slot| slot.kind == PrivateKind::Method))
        .unwrap_or(matches.first().expect("non-empty matches"))
}

fn compound_operator(operator: AssignmentOperator) -> BinaryOperator {
    match operator {
        AssignmentOperator::AddAssign => BinaryOperator::Add,
        AssignmentOperator::SubtractAssign => BinaryOperator::Subtract,
        AssignmentOperator::MultiplyAssign => BinaryOperator::Multiply,
        AssignmentOperator::DivideAssign => BinaryOperator::Divide,
        AssignmentOperator::RemainderAssign => BinaryOperator::Remainder,
        AssignmentOperator::ExponentiateAssign => BinaryOperator::Exponentiate,
        AssignmentOperator::LeftShiftAssign => BinaryOperator::LeftShift,
        AssignmentOperator::SignedRightShiftAssign => BinaryOperator::SignedRightShift,
        AssignmentOperator::UnsignedRightShiftAssign => BinaryOperator::UnsignedRightShift,
        AssignmentOperator::BitAndAssign => BinaryOperator::BitAnd,
        AssignmentOperator::BitXorAssign => BinaryOperator::BitXor,
        AssignmentOperator::BitOrAssign => BinaryOperator::BitOr,
        AssignmentOperator::Assign
        | AssignmentOperator::LogicalAndAssign
        | AssignmentOperator::LogicalOrAssign
        | AssignmentOperator::NullishAssign => BinaryOperator::Add,
    }
}

/// The member expression left once parentheses, assertions, and non-null
/// marks around an invalid assignment target's operand are erased.
fn asserted_member(expression: &Expr) -> Option<&MemberExpression> {
    match expression.data() {
        Expression::Parenthesized(inner) => asserted_member(inner),
        Expression::As(cast) => asserted_member(&cast.expression),
        Expression::Satisfies(cast) => asserted_member(&cast.expression),
        Expression::TypeAssertion(cast) => asserted_member(&cast.expression),
        Expression::NonNull(non_null) => asserted_member(&non_null.expression),
        Expression::Member(member) => Some(member),
        _ => None,
    }
}
