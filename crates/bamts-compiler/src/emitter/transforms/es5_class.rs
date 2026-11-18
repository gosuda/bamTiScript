//! Classes below ES2015: a constructor function and prototype assignments
//! inside an immediately invoked function.
//!
//! `class D extends C { m() {} }` becomes `var D = /** @class */ (function
//! (_super) { __extends(D, _super); function D() {...} D.prototype.m =
//! function () {}; return D; }(C));`. The ES2015 lowering has already moved
//! field initializers into the constructor and static members after the
//! class, so this module only converts the lowered class.

use crate::source::TextRange;
use crate::syntax::*;

use super::helpers::HelperKind;
use super::legacy_decorators::is_decorated;
use super::{ClassLowering, ExportWrapper, FieldInit, FieldMode, Rewriter};

/// Where the code of one class member runs, for `this` and `super`.
#[derive(Clone, Copy)]
pub(super) struct MemberScope {
    pub(super) is_static: bool,
    /// Derived constructors and the field initializers that run in them read
    /// `this` through the `_this` the super call returns.
    pub(super) rebinds_this: bool,
}

/// The class member being rewritten, which decides what `super` means.
pub(super) struct SuperContext {
    pub(super) is_static: bool,
}

/// Whether the ES5 lowering covers this class; anything else keeps the
/// diagnostic and the class unchanged.
pub(super) fn es5_class_supported(class: &ClassDeclaration, decorators_lowered: bool) -> bool {
    let undecorated = |decorators: &[DecoratorNode]| decorators_lowered || decorators.is_empty();
    let undecorated_parameters = |parameters: &[ParameterNode]| {
        decorators_lowered
            || parameters
                .iter()
                .all(|parameter| parameter.data().decorators.is_empty())
    };
    undecorated(&class.decorators)
        && class.members.iter().all(|member| match member.data() {
            ClassMember::Constructor(constructor) => {
                undecorated(&constructor.decorators)
                    && undecorated_parameters(&constructor.parameters)
            }
            ClassMember::Method(method) => {
                undecorated(&method.function.decorators)
                    && !matches!(method.name, PropertyName::Private(_))
                    && undecorated_parameters(&method.function.parameters)
            }
            ClassMember::Property(property) => {
                undecorated(&property.decorators)
                    && !matches!(property.name, PropertyName::Private(_))
            }
            ClassMember::AutoAccessor(_) => false,
            ClassMember::StaticBlock(_)
            | ClassMember::IndexSignature(_)
            | ClassMember::Missing(_)
            | ClassMember::Semicolon => true,
        })
}

fn is_forwarded_arguments(call: &CallExpression) -> bool {
    matches!(
        call.arguments.as_slice(),
        [CallArgument::Spread(spread)] if matches!(spread.argument.data(), Expression::Identifier(_))
    )
}

fn is_super_call_statement(statement: &Stmt) -> bool {
    matches!(
        statement.data(),
        Statement::Expression(expression)
            if matches!(
                expression.expression.data(),
                Expression::Call(call) if matches!(call.callee.data(), Expression::Super)
            )
    )
}

impl Rewriter<'_> {
    /// Runs `run` with the capture scope and `super` context of one class
    /// member. Returns the `_this` name the member's arrows captured (or, for
    /// a rebinding scope, the name it binds).
    pub(super) fn with_class_member<T>(
        &mut self,
        scope: Option<MemberScope>,
        run: impl FnOnce(&mut Self) -> T,
    ) -> (T, Option<IdentifierNode>) {
        let Some(scope) = scope else {
            return (run(self), None);
        };
        let mut captures = super::CaptureScope::default();
        if scope.rebinds_this {
            captures.this_always = true;
            captures.this = Some(self.capture_name("_this"));
        }
        self.capture_scopes.push(captures);
        self.super_contexts.push(SuperContext {
            is_static: scope.is_static,
        });
        let result = run(self);
        self.super_contexts.pop();
        let captures = self.capture_scopes.pop().unwrap_or_default();
        (result, captures.this)
    }

    /// `_super.prototype` in an instance member, `_super` in a static one.
    pub(super) fn rewrite_super_object(&mut self, range: TextRange) -> Option<Expr> {
        let is_static = self.super_contexts.last()?.is_static;
        let base = self.ident("_super");
        if is_static {
            return Some(self.syn_node(range, Expression::Identifier(base)));
        }
        Some(self.member_ident(&base, "prototype", range))
    }

    /// `super.m(args)` as `_super.prototype.m.call(this, args)`.
    pub(super) fn lower_super_method_call(
        &mut self,
        expression: &Expr,
        call: &CallExpression,
    ) -> Expr {
        let range = expression.range();
        let Expression::Member(member) = call.callee.data() else {
            unreachable!("a super method call has a member callee");
        };
        let object = self
            .rewrite_super_object(member.object.range())
            .expect("a super method call reads the class member context");
        let property = match &member.property {
            MemberProperty::Computed(key) => {
                MemberProperty::Computed(Box::new(self.rewrite_expr(key)))
            }
            other => other.clone(),
        };
        let method = self.syn_node(
            call.callee.range(),
            Expression::Member(MemberExpression {
                object: Box::new(object),
                property,
                optional: false,
            }),
        );
        let this = self.syn_node(range, Expression::This);
        let this = self.rewrite_this(&this);
        let (verb, mut arguments) = match call.arguments.as_slice() {
            [CallArgument::Spread(spread)] => {
                let argument = self.rewrite_expr(&spread.argument);
                ("apply", vec![CallArgument::Expression(Box::new(argument))])
            }
            _ => ("call", self.rewrite_call_arguments(&call.arguments)),
        };
        arguments.insert(0, CallArgument::Expression(Box::new(this)));
        let verb = self.ident(verb);
        let callee = self.syn_node(
            range,
            Expression::Member(MemberExpression {
                object: Box::new(method),
                property: MemberProperty::Named(verb),
                optional: false,
            }),
        );
        self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments,
            }),
        )
    }

    /// The statements a class declaration becomes, or `None` when the lowering
    /// does not cover the class.
    pub(super) fn lower_es5_class_statement(
        &mut self,
        statement: &Stmt,
        class_range: TextRange,
        class: &ClassDeclaration,
        wrapper: ExportWrapper,
    ) -> Option<Vec<Stmt>> {
        let decorators_lowered = self.options.experimental_decorators;
        if !es5_class_supported(class, decorators_lowered) {
            return None;
        }
        let mut class = class.clone();
        let (name, name_text) = match &class.name {
            Some(name) => (
                name.clone(),
                self.token_text(name.data().token()).to_owned(),
            ),
            None => {
                let name = self.ident("default_1");
                class.name = Some(name.clone());
                (name, String::from("default_1"))
            }
        };
        let decorations = if decorators_lowered && is_decorated(&class) {
            self.es5_class_decorations(&mut class, &name, &name_text, class_range)
        } else {
            Vec::new()
        };
        let mut lowered = self.lower_class(&class, class_range, None, None);
        lowered.postlude.extend(decorations);
        let (mut statements, iife) = self.es5_class_iife(&name, lowered, class_range);
        let variable = self.class_variable(&name, iife, class_range);
        match wrapper {
            ExportWrapper::None => statements.push(variable),
            ExportWrapper::Named => statements.push(self.node(
                statement.range(),
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(Box::new(variable)),
                )),
            )),
            ExportWrapper::Default => {
                statements.push(variable);
                let value = self.syn_node(name.range(), Expression::Identifier(name.clone()));
                statements.push(self.node(
                    statement.range(),
                    Statement::Export(ExportDeclaration::Default(ExportDefaultDeclaration {
                        value: ExportDefaultValue::Expression(Box::new(value)),
                    })),
                ));
            }
        }
        Some(statements)
    }

    /// A class expression as `/** @class */ (function () {...}())`, or `None`
    /// when the lowering does not cover the class.
    pub(super) fn lower_es5_class_expression(
        &mut self,
        expression: &Expr,
        class: &ClassDeclaration,
    ) -> Option<Expr> {
        if !es5_class_supported(class, false) {
            return None;
        }
        let range = expression.range();
        let mut class = class.clone();
        let name = match &class.name {
            Some(name) => name.clone(),
            None => {
                let name = self.source_name_ident("class");
                class.name = Some(name.clone());
                name
            }
        };
        let lowered = self.lower_class(&class, range, None, None);
        if !lowered.prelude.is_empty() {
            return None;
        }
        let suspends = lowered.postlude.iter().any(|statement| {
            super::count_branch_yields(std::slice::from_ref(statement)) > 0
                || super::statements_contain_await(std::slice::from_ref(statement))
        });
        if suspends {
            self.diag(
                super::codes::GENERATOR_REQUIRES_ES2015,
                range,
                "generators require ScriptTarget::Es2015 or later",
            );
            return Some(expression.clone());
        }
        Some(self.es5_class_iife(&name, lowered, range).1)
    }

    fn class_variable(&mut self, name: &IdentifierNode, value: Expr, range: TextRange) -> Stmt {
        let declarator = self.make_declarator(name.clone(), Some(value), range);
        self.syn_node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                kind: VariableKind::Var,
                declarations: vec![declarator],
            }),
        )
    }

    /// The IIFE for one lowered class, with the statements that must precede
    /// the declaration (computed-key temporaries).
    fn es5_class_iife(
        &mut self,
        name: &IdentifierNode,
        lowered: ClassLowering,
        range: TextRange,
    ) -> (Vec<Stmt>, Expr) {
        let ClassLowering {
            class,
            prelude,
            postlude,
            static_this,
        } = lowered;
        let derived = class.extends.is_some();
        let base = class
            .extends
            .as_ref()
            .map(|heritage| (*heritage.expression).clone());
        let mut body = Vec::new();
        let super_name = self.ident("_super");
        if derived {
            body.push(self.extends_statement(name, &super_name, range));
        }
        let mut constructor = None;
        let mut members = Vec::new();
        for member in class.members {
            match member.data() {
                ClassMember::Constructor(_) => constructor = Some(member),
                _ => members.push(member),
            }
        }
        body.push(self.es5_constructor(name, constructor, derived, range));
        let mut consumed = vec![false; members.len()];
        for index in 0..members.len() {
            if consumed[index] {
                continue;
            }
            let member = &members[index];
            let ClassMember::Method(method) = member.data() else {
                continue;
            };
            if method.function.body.is_none() {
                continue;
            }
            let statement = match method.modifier {
                PropertyModifier::None => self.prototype_assignment(name, method, member.range()),
                _ => {
                    let partner = self.accessor_partner(&members, &consumed, index);
                    if let Some(partner) = partner {
                        consumed[partner] = true;
                    }
                    self.accessor_definition(name, &members, index, partner)
                }
            };
            body.push(statement);
        }
        if static_this {
            let value = self.syn_node(name.range(), Expression::Identifier(name.clone()));
            let this_name = self.capture_name("_this");
            body.push(self.make_temp_declaration(this_name, value, range));
        }
        body.extend(postlude);
        let returned = self.syn_node(name.range(), Expression::Identifier(name.clone()));
        body.push(self.syn_node(
            range,
            Statement::Return(ReturnStatement {
                argument: Some(Box::new(returned)),
            }),
        ));
        let parameters = if derived {
            vec![self.plain_parameter(&super_name, range)]
        } else {
            Vec::new()
        };
        let block = self.syn_node(range, Block { statements: body });
        let function = FunctionLike {
            decorators: Vec::new(),
            name: None,
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters,
            return_type: None,
            body: Some(FunctionBody::Block(block)),
        };
        let callee = self.syn_node(range, Expression::Function(FunctionExpression { function }));
        let arguments = base
            .into_iter()
            .map(|base| CallArgument::Expression(Box::new(base)))
            .collect();
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments,
            }),
        );
        let wrapped = self.syn_node(range, Expression::Parenthesized(Box::new(call)));
        self.class_iifes.insert(wrapped.id());
        (prelude, wrapped)
    }

    fn plain_parameter(&mut self, name: &IdentifierNode, range: TextRange) -> ParameterNode {
        let binding = self.node(name.range(), BindingPattern::Identifier(name.clone()));
        self.node(
            range,
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers::default(),
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        )
    }

    fn extends_statement(
        &mut self,
        class_name: &IdentifierNode,
        super_name: &IdentifierNode,
        range: TextRange,
    ) -> Stmt {
        let helper = self.helper_ident(HelperKind::Extends);
        let class = self.syn_node(
            class_name.range(),
            Expression::Identifier(class_name.clone()),
        );
        let base = self.syn_node(range, Expression::Identifier(super_name.clone()));
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(helper),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(class)),
                    CallArgument::Expression(Box::new(base)),
                ],
            }),
        );
        self.expression_statement(call, range)
    }

    /// `function C(params) { body }`; a derived class returns `_this`.
    fn es5_constructor(
        &mut self,
        name: &IdentifierNode,
        constructor: Option<ClassMemberNode>,
        derived: bool,
        range: TextRange,
    ) -> Stmt {
        let (parameters, body, body_range) = match constructor.as_ref().map(ClassMemberNode::data) {
            Some(ClassMember::Constructor(constructor)) => (
                constructor.parameters.clone(),
                Some(constructor.body.clone()),
                constructor.body.range(),
            ),
            _ => (Vec::new(), None, range),
        };
        let injections = self.parameter_property_assignments(&parameters, derived);
        let block = match (derived, body) {
            (true, body) => {
                let statements = match body {
                    Some(body) => body.data().statements.clone(),
                    None => vec![self.super_forward_call(range)],
                };
                let statements = self.derived_constructor_body(&statements, injections, body_range);
                self.syn_node(body_range, Block { statements })
            }
            (false, Some(body)) if injections.is_empty() => body,
            (false, Some(body)) => {
                let mut statements = injections;
                statements.extend(body.data().statements.iter().cloned());
                self.syn_node(body_range, Block { statements })
            }
            (false, None) => self.syn_node(
                body_range,
                Block {
                    statements: injections,
                },
            ),
        };
        let function = FunctionLike {
            decorators: Vec::new(),
            name: Some(name.clone()),
            is_async: false,
            is_generator: false,
            type_parameters: None,
            parameters,
            return_type: None,
            body: Some(FunctionBody::Block(block)),
        };
        self.syn_node(range, Statement::Function(FunctionDeclaration { function }))
    }

    /// `this.x = x;` for each parameter property, through `_this` in a
    /// derived constructor.
    fn parameter_property_assignments(
        &mut self,
        parameters: &[ParameterNode],
        derived: bool,
    ) -> Vec<Stmt> {
        let receiver = derived.then(|| self.capture_name("_this"));
        let mut statements = Vec::new();
        for parameter in parameters {
            let data = parameter.data();
            if data.modifiers.accessibility.is_none() && !data.modifiers.is_readonly {
                continue;
            }
            let BindingPattern::Identifier(name) = data.binding.data() else {
                continue;
            };
            let init = self.syn_node(name.range(), Expression::Identifier(name.clone()));
            let field = FieldInit {
                name: PropertyName::Identifier(name.clone()),
                init,
                range: parameter.range(),
            };
            statements.push(self.field_statement(receiver.as_ref(), &field, FieldMode::Assign));
        }
        statements
    }

    /// The body of a derived constructor: the super call becomes
    /// `var _this = _super.call(this, ...) || this;`, the parameter property
    /// assignments follow it, and the body ends with `return _this;`. A
    /// constructor that only forwards its arguments returns the call directly.
    fn derived_constructor_body(
        &mut self,
        statements: &[Stmt],
        injections: Vec<Stmt>,
        range: TextRange,
    ) -> Vec<Stmt> {
        let this_name = self.capture_name("_this");
        let mut out = Vec::new();
        let mut replaced = false;
        let mut injections = Some(injections);
        let only_forwarding = statements.len() == 1
            && injections.as_ref().is_some_and(Vec::is_empty)
            && self.synthesized_ids.contains(&statements[0].id())
            && is_super_call_statement(&statements[0]);
        for statement in statements {
            if replaced || !is_super_call_statement(statement) {
                out.push(statement.clone());
                continue;
            }
            replaced = true;
            let Statement::Expression(expression) = statement.data() else {
                unreachable!("a super call statement is an expression statement");
            };
            let Expression::Call(call) = expression.expression.data() else {
                unreachable!("a super call statement holds a call");
            };
            let guarded =
                self.synthesized_ids.contains(&statement.id()) && is_forwarded_arguments(call);
            let value = self.super_call_value(call, guarded, statement.range());
            if only_forwarding {
                out.push(self.syn_node(
                    statement.range(),
                    Statement::Return(ReturnStatement {
                        argument: Some(Box::new(value)),
                    }),
                ));
                return out;
            }
            let declarator =
                self.make_declarator(this_name.clone(), Some(value), statement.range());
            out.push(self.syn_node(
                statement.range(),
                Statement::Variable(VariableDeclaration {
                    range: statement.range(),
                    kind: VariableKind::Var,
                    declarations: vec![declarator],
                }),
            ));
            out.extend(injections.take().into_iter().flatten());
        }
        if replaced {
            let end = TextRange::new(range.end(), range.end())
                .expect("an empty range at a valid position is valid");
            let returned = self.syn_node(end, Expression::Identifier(this_name));
            out.push(self.syn_node(
                end,
                Statement::Return(ReturnStatement {
                    argument: Some(Box::new(returned)),
                }),
            ));
        }
        out
    }

    /// `_super.call(this, args) || this`, or for a forwarded `arguments`
    /// `_super !== null && _super.apply(this, arguments) || this`.
    fn super_call_value(&mut self, call: &CallExpression, guarded: bool, range: TextRange) -> Expr {
        let base = self.ident("_super");
        let (verb, arguments) = match call.arguments.as_slice() {
            [CallArgument::Spread(spread)] => (
                "apply",
                vec![CallArgument::Expression(spread.argument.clone())],
            ),
            _ => ("call", call.arguments.clone()),
        };
        let this = self.syn_node(range, Expression::This);
        let mut all_arguments = vec![CallArgument::Expression(Box::new(this))];
        all_arguments.extend(arguments);
        let callee = self.member_ident(&base, verb, range);
        let invoked = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: all_arguments,
            }),
        );
        let invoked = if guarded {
            let base_value = self.syn_node(range, Expression::Identifier(base));
            let null = self.null_expr();
            let present = self.syn_node(
                range,
                Expression::Binary(BinaryExpression {
                    operator: BinaryOperator::StrictNotEqual,
                    left: Box::new(base_value),
                    right: Box::new(null),
                }),
            );
            self.syn_node(
                range,
                Expression::Logical(LogicalExpression {
                    operator: LogicalOperator::And,
                    left: Box::new(present),
                    right: Box::new(invoked),
                }),
            )
        } else {
            invoked
        };
        let fallback = self.syn_node(range, Expression::This);
        self.syn_node(
            range,
            Expression::Logical(LogicalExpression {
                operator: LogicalOperator::Or,
                left: Box::new(invoked),
                right: Box::new(fallback),
            }),
        )
    }

    /// `C.prototype.m = function () {...};` or `C.m = ...` for a static one.
    fn prototype_assignment(
        &mut self,
        class_name: &IdentifierNode,
        method: &MethodDeclaration,
        range: TextRange,
    ) -> Stmt {
        let owner = self.member_owner(class_name, method.modifiers.is_static, range);
        let property = self.member_property(&method.name, range);
        let target = self.syn_node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(owner),
                property,
            }),
        );
        let function = self.method_function_like(method, range);
        let assignment = self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left: target,
                right: Box::new(function),
            }),
        );
        self.expression_statement(assignment, range)
    }

    /// The object a member attaches to: the class or its prototype.
    fn member_owner(
        &mut self,
        class_name: &IdentifierNode,
        is_static: bool,
        range: TextRange,
    ) -> Expr {
        if is_static {
            return self.syn_node(
                class_name.range(),
                Expression::Identifier(class_name.clone()),
            );
        }
        self.member_ident(class_name, "prototype", range)
    }

    fn method_function_like(&mut self, method: &MethodDeclaration, range: TextRange) -> Expr {
        let function = FunctionLike {
            decorators: Vec::new(),
            name: None,
            type_parameters: None,
            return_type: None,
            ..method.function.clone()
        };
        self.syn_node(range, Expression::Function(FunctionExpression { function }))
    }

    /// The index of the other accessor with the same static name, when this
    /// accessor is the first of the pair.
    fn accessor_partner(
        &self,
        members: &[ClassMemberNode],
        consumed: &[bool],
        index: usize,
    ) -> Option<usize> {
        let ClassMember::Method(accessor) = members[index].data() else {
            return None;
        };
        let name = self.static_member_name(&accessor.name)?;
        members
            .iter()
            .enumerate()
            .skip(index + 1)
            .find_map(|(other, member)| {
                let ClassMember::Method(candidate) = member.data() else {
                    return None;
                };
                let pairs = !consumed[other]
                    && !matches!(candidate.modifier, PropertyModifier::None)
                    && std::mem::discriminant(&candidate.modifier)
                        != std::mem::discriminant(&accessor.modifier)
                    && candidate.modifiers.is_static == accessor.modifiers.is_static
                    && self.static_member_name(&candidate.name) == Some(name);
                pairs.then_some(other)
            })
    }

    fn static_member_name(&self, name: &PropertyName) -> Option<&str> {
        match name {
            PropertyName::Identifier(identifier) => {
                Some(self.token_text(identifier.data().token()))
            }
            PropertyName::String(literal) => Some(self.token_text(literal.data().token())),
            PropertyName::Number(literal) => Some(self.token_text(literal.data().token())),
            PropertyName::Computed(_) | PropertyName::Private(_) | PropertyName::Missing(_) => None,
        }
    }

    /// `Object.defineProperty(owner, key, { get, set, enumerable, configurable })`.
    fn accessor_definition(
        &mut self,
        class_name: &IdentifierNode,
        members: &[ClassMemberNode],
        index: usize,
        partner: Option<usize>,
    ) -> Stmt {
        let range = members[index].range();
        let ClassMember::Method(first) = members[index].data() else {
            unreachable!("an accessor definition starts at a method");
        };
        let second = partner.map(|partner| match members[partner].data() {
            ClassMember::Method(method) => method,
            _ => unreachable!("an accessor partner is a method"),
        });
        let (getter, setter) = match first.modifier {
            PropertyModifier::Get => (Some(first), second),
            _ => (second, Some(first)),
        };
        let mut entries = Vec::new();
        for (key, method) in [("get", getter), ("set", setter)] {
            if let Some(method) = method {
                entries.push((key, self.method_function_like(method, range)));
            }
        }
        entries.push(("enumerable", self.boolean_expr(false)));
        entries.push(("configurable", self.boolean_expr(true)));
        let descriptor = self.object_literal(entries, range);
        let object = self.ident("Object");
        let callee = self.member_ident(&object, "defineProperty", range);
        let owner = self.member_owner(class_name, first.modifiers.is_static, range);
        let key = self.property_key_expression(&first.name, range);
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![
                    CallArgument::Expression(Box::new(owner)),
                    CallArgument::Expression(Box::new(key)),
                    CallArgument::Expression(Box::new(descriptor)),
                ],
            }),
        );
        self.expression_statement(call, range)
    }
}
