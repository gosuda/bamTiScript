//! Namespace declarations as the function calls that build them at runtime.
//!
//! `namespace N { export var x = 1; }` becomes a `var N;` and a call that fills
//! the container: `(function (N) { N.x = 1; })(N || (N = {}));`. Only the first
//! declaration of a name in a scope declares it, so merged blocks share one
//! binding and a namespace merged into a class or function reuses theirs.

use std::collections::BTreeSet;

use crate::checker::{SymbolId, SymbolKind};
use crate::source::TextRange;
use crate::syntax::*;

use super::Rewriter;

/// One namespace body being lowered.
pub(super) struct NamespaceFrame {
    container: SymbolId,
    /// The body function's parameter, which holds the container.
    parameter: String,
    /// Temporaries taken in this body so far.
    temps: usize,
}

/// How a declaration reaches the container it fills.
pub(super) enum ContainerBinding {
    /// `N || (N = {})`
    Local,
    /// `N = parent.N || (parent.N = {})`, for a member of `parent`.
    Member(String),
    /// `N || (exports.N = N = {})`
    CommonJs,
    /// `export var N;` declares it, and the call is then the local one.
    Export,
}

impl Rewriter<'_> {
    pub(super) fn lower_namespace(
        &mut self,
        statement: &Stmt,
        namespace: &NamespaceDeclaration,
        binding: ContainerBinding,
        range: TextRange,
    ) -> Vec<Stmt> {
        let plan = self
            .model
            .and_then(|model| model.namespace_facts().declaration(statement.id()));
        let (Some(plan), NamespaceName::Identifier { name, .. }) = (plan, &namespace.name) else {
            return vec![statement.clone()];
        };
        if !plan.is_value_bearing() {
            // Nothing to build; the printer decides what this one reports.
            return vec![statement.clone()];
        }
        let Some(local) = self.identifier_name(name) else {
            return vec![statement.clone()];
        };
        let parameter = self.namespace_parameter(&local, namespace.body.range());
        let body = self.lower_namespace_body(namespace, plan.container(), &parameter);
        let mut out = Vec::new();
        out.extend(self.container_declaration(&local, &binding, range));
        let argument = self.container_argument(&local, &binding, range);
        out.push(self.container_call(&parameter, body, argument, range));
        out
    }

    fn lower_namespace_body(
        &mut self,
        namespace: &NamespaceDeclaration,
        container: SymbolId,
        parameter: &str,
    ) -> Vec<Stmt> {
        self.namespace_frames.push(NamespaceFrame {
            container,
            parameter: parameter.to_owned(),
            temps: 0,
        });
        self.declared_names.push(BTreeSet::new());
        self.expression_temp_scopes.push(Vec::new());
        let mut body = Vec::new();
        for member in &namespace.body.data().statements {
            self.record_declaration(member);
            body.extend(self.rewrite_namespace_member(member, parameter));
        }
        let temps = self.expression_temp_scopes.pop().unwrap_or_default();
        if let Some(declaration) = self.temp_declaration(temps, namespace.body.range()) {
            body.insert(0, declaration);
        }
        self.declared_names.pop();
        self.namespace_frames.pop();
        body
    }

    fn rewrite_namespace_member(&mut self, member: &Stmt, parameter: &str) -> Vec<Stmt> {
        let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(inner))) =
            member.data()
        else {
            return self.rewrite_statement(member);
        };
        let range = member.range();
        let exported = match inner.data() {
            Statement::Variable(declaration) => {
                return self.namespace_export_variables(declaration, parameter, range);
            }
            Statement::Namespace(namespace) => {
                let binding = ContainerBinding::Member(parameter.to_owned());
                return self.lower_namespace(inner, namespace, binding, range);
            }
            Statement::Function(function) if function.function.body.is_some() => {
                function.function.name.as_ref()
            }
            Statement::Class(class) => class.name.as_ref(),
            _ => None,
        };
        let mut out = self.rewrite_statement(inner);
        if !out.is_empty() {
            // Claiming the `export` keyword brings the comments above it along.
            let first = out.remove(0);
            out.insert(0, Node::new(first.id(), range, first.into_data()));
        }
        if let Some(name) = exported.and_then(|name| self.identifier_name(name)) {
            let value = self.ident_expr(&name);
            let assignment = self.member_assignment(parameter, &name, value, range);
            out.push(self.expression_statement(assignment, range));
        }
        out
    }

    /// An exported variable lives only on the container, so its declaration
    /// is the assignment of its initializer, and it has none without one.
    fn namespace_export_variables(
        &mut self,
        declaration: &VariableDeclaration,
        parameter: &str,
        range: TextRange,
    ) -> Vec<Stmt> {
        let mut assignments = Vec::new();
        for declarator in &declaration.declarations {
            let data = declarator.data();
            if let Some(initializer) = data.initializer.as_deref() {
                let value = self.rewrite_expr(initializer);
                self.flatten_export(&data.binding, value, parameter, &mut assignments);
            }
        }
        let expression = match assignments.len() {
            0 => return Vec::new(),
            1 => assignments.remove(0),
            _ => self.syn_node(
                range,
                Expression::Sequence(SequenceExpression {
                    expressions: assignments,
                }),
            ),
        };
        vec![self.expression_statement(expression, range)]
    }

    /// Assignments taking `pattern` apart onto the container. A pattern that
    /// reads its source more than once holds it in a temporary first.
    fn flatten_export(
        &mut self,
        pattern: &Pattern,
        value: Expr,
        parameter: &str,
        out: &mut Vec<Expr>,
    ) {
        let range = pattern.range();
        match pattern.data() {
            BindingPattern::Identifier(ident) => {
                if let Some(name) = self.identifier_name(ident) {
                    out.push(self.member_assignment(parameter, &name, value, ident.range()));
                }
            }
            BindingPattern::Object(object) => {
                let source = self.single_read_source(value, object.properties.len(), range, out);
                for property in &object.properties {
                    let name = self.rewrite_property_name(&property.name);
                    let read = self.property_read(&source, name, range);
                    let read = self.with_default(read, property.initializer.as_deref(), out);
                    self.flatten_export(&property.binding, read, parameter, out);
                }
            }
            BindingPattern::Array(array) => {
                let source = self.single_read_source(value, array.elements.len(), range, out);
                for (index, element) in array.elements.iter().enumerate() {
                    let ArrayBindingElement::Binding(binding) = element else {
                        continue;
                    };
                    let index = self.number_expr(&index.to_string());
                    let property = MemberProperty::Computed(Box::new(index));
                    let read = self.member_expr(&source, property, range);
                    self.flatten_export(binding, read, parameter, out);
                }
            }
            BindingPattern::Assignment(assignment) => {
                let read = self.with_default(value, Some(&*assignment.right), out);
                self.flatten_export(&assignment.left, read, parameter, out);
            }
            BindingPattern::Rest(_) | BindingPattern::Missing(_) => {}
        }
    }

    fn single_read_source(
        &mut self,
        value: Expr,
        reads: usize,
        range: TextRange,
        out: &mut Vec<Expr>,
    ) -> Expr {
        if reads == 1 || matches!(value.data(), Expression::Identifier(_)) {
            return value;
        }
        self.hold_in_temp(value, range, out)
    }

    fn hold_in_temp(&mut self, value: Expr, range: TextRange, out: &mut Vec<Expr>) -> Expr {
        let temp = self.namespace_temp();
        let left = self.syn_node(range, AssignmentTarget::Identifier(temp.clone()));
        out.push(self.assignment(left, value, range));
        self.node(temp.range(), Expression::Identifier(temp))
    }

    /// The next free `_a`-style name in the innermost body, declared with it.
    fn namespace_temp(&mut self) -> IdentifierNode {
        const LETTERS: &[u8] = b"abcdefghjklmopqrstuvwxyz";
        let file = self.file;
        let occupied = self
            .occupied_names
            .get_or_insert_with(|| super::identifier_names(file));
        let frame = self
            .namespace_frames
            .last_mut()
            .expect("an exported pattern is lowered inside a namespace body");
        let (index, name) = (frame.temps..)
            .map(|index| match LETTERS.get(index) {
                Some(&letter) => (index, format!("_{}", char::from(letter))),
                None => (index, format!("_{}", index - LETTERS.len())),
            })
            .find(|(_, candidate)| !occupied.contains(candidate))
            .expect("an unbounded index range reaches an unused name");
        frame.temps = index + 1;
        let temp = self.ident(&name);
        if let Some(scope) = self.expression_temp_scopes.last_mut() {
            scope.push(temp.clone());
        }
        temp
    }

    fn property_read(&mut self, source: &Expr, name: PropertyName, range: TextRange) -> Expr {
        let property = match name {
            PropertyName::Identifier(ident) => MemberProperty::Named(ident),
            PropertyName::Computed(key) => MemberProperty::Computed(key),
            PropertyName::String(literal) => MemberProperty::Computed(Box::new(self.node(
                literal.range(),
                Expression::Literal(Literal::String(literal)),
            ))),
            PropertyName::Number(literal) => MemberProperty::Computed(Box::new(self.node(
                literal.range(),
                Expression::Literal(Literal::Number(literal)),
            ))),
            PropertyName::Private(_) | PropertyName::Missing(_) => return source.clone(),
        };
        self.member_expr(source, property, range)
    }

    /// `_a === void 0 ? default : _a` over a read held in a temporary.
    fn with_default(&mut self, read: Expr, default: Option<&Expr>, out: &mut Vec<Expr>) -> Expr {
        let Some(default) = default else {
            return read;
        };
        let range = read.range();
        let held = self.hold_in_temp(read, range, out);
        let Expression::Identifier(temp) = held.data() else {
            return held;
        };
        let default = self.rewrite_expr(default);
        self.default_ternary(temp, &default, range)
    }

    /// The parameter name for a namespace body. It is the namespace's own name
    /// unless something inside declares that name, which would shadow it.
    fn namespace_parameter(&mut self, local: &str, body: TextRange) -> String {
        if !self.declares_value_inside(local, body) {
            return local.to_owned();
        }
        let file = self.file;
        let occupied = self
            .occupied_names
            .get_or_insert_with(|| super::identifier_names(file));
        (1u32..)
            .map(|suffix| format!("{local}_{suffix}"))
            .find(|candidate| occupied.insert(candidate.clone()))
            .expect("an unbounded suffix range reaches an unused name")
    }

    fn declares_value_inside(&mut self, name: &str, body: TextRange) -> bool {
        let Some(model) = self.model else {
            return false;
        };
        let ranges = self.value_symbol_ranges.get_or_insert_with(|| {
            let mut ranges: std::collections::HashMap<String, Vec<TextRange>> =
                std::collections::HashMap::new();
            for symbol in model.symbols() {
                if !matches!(
                    symbol.kind(),
                    SymbolKind::Interface
                        | SymbolKind::TypeAlias
                        | SymbolKind::TypeParameter
                        | SymbolKind::IntrinsicType
                ) {
                    ranges
                        .entry(symbol.name().to_owned())
                        .or_default()
                        .push(symbol.range());
                }
            }
            ranges
        });
        ranges.get(name).is_some_and(|ranges| {
            ranges
                .iter()
                .any(|range| range.start() >= body.start() && range.end() <= body.end())
        })
    }

    /// The name of the parameter holding the container a use resolved to,
    /// when `reference` reads a namespace member rather than a local.
    pub(super) fn namespace_member_parameter(&self, reference: NodeId) -> Option<String> {
        let member = self.model?.namespace_facts().member_use(reference)?;
        self.namespace_frames
            .iter()
            .rev()
            .find(|frame| frame.container == member.container())
            .map(|frame| frame.parameter.clone())
    }

    pub(super) fn namespace_member(
        &mut self,
        parameter: &str,
        name: &str,
        range: TextRange,
    ) -> Expr {
        let object = self.ident_expr(parameter);
        let property = MemberProperty::Named(self.ident(name));
        self.member_expr(&object, property, range)
    }

    /// Records a declaration that owns its name before anything merges with it.
    pub(super) fn record_declaration(&mut self, statement: &Stmt) {
        let declaration = match statement.data() {
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            ))) => inner.data(),
            data => data,
        };
        let name = match declaration {
            Statement::Class(class) => class.name.as_ref(),
            Statement::Function(function) => function.function.name.as_ref(),
            _ => None,
        };
        if let Some(name) = name.and_then(|name| self.identifier_name(name))
            && let Some(names) = self.declared_names.last_mut()
        {
            names.insert(name);
        }
    }

    /// `var N;` for the first declaration of `local` in this scope. Below the
    /// top level the binding is block scoped.
    fn container_declaration(
        &mut self,
        local: &str,
        binding: &ContainerBinding,
        range: TextRange,
    ) -> Option<Stmt> {
        if !self.declared_names.last_mut()?.insert(local.to_owned()) {
            return None;
        }
        let kind = if self.declared_names.len() > 1 {
            VariableKind::Let
        } else {
            VariableKind::Var
        };
        let name = self.ident(local);
        let declarator = self.make_declarator(name, None, range);
        let declaration = self.syn_node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                kind,
                declarations: vec![declarator],
            }),
        );
        Some(if matches!(binding, ContainerBinding::Export) {
            self.syn_node(
                range,
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(Box::new(declaration)),
                )),
            )
        } else {
            declaration
        })
    }

    fn container_argument(
        &mut self,
        local: &str,
        binding: &ContainerBinding,
        range: TextRange,
    ) -> Expr {
        let empty = self.syn_node(
            range,
            Expression::Object(ObjectLiteral {
                members: Vec::new(),
            }),
        );
        match binding {
            ContainerBinding::Local | ContainerBinding::Export => {
                let read = self.ident_expr(local);
                let create = self.name_assignment(local, empty, range);
                self.or_create(read, create, range)
            }
            ContainerBinding::CommonJs => {
                let read = self.ident_expr(local);
                let create = self.name_assignment(local, empty, range);
                let left = self.cjs_export_target(local, range);
                let publish = self.assignment(left, create, range);
                self.or_create(read, publish, range)
            }
            ContainerBinding::Member(parent) => {
                let read = self.namespace_member(parent, local, range);
                let create = self.member_assignment(parent, local, empty, range);
                let either = self.or_create(read, create, range);
                self.name_assignment(local, either, range)
            }
        }
    }

    /// `(function (parameter) { body })(argument);`
    fn container_call(
        &mut self,
        parameter: &str,
        body: Vec<Stmt>,
        argument: Expr,
        range: TextRange,
    ) -> Stmt {
        let name = self.ident(parameter);
        let binding = self.syn_node(range, BindingPattern::Identifier(name));
        let parameter = self.syn_node(
            range,
            Parameter {
                decorators: Vec::new(),
                modifiers: ParameterModifiers {
                    accessibility: None,
                    is_readonly: false,
                    is_override: false,
                },
                binding,
                optional: false,
                type_annotation: None,
                initializer: None,
            },
        );
        let body = self.syn_node(range, Block { statements: body });
        let function = self.syn_node(
            range,
            Expression::Function(FunctionExpression {
                function: FunctionLike {
                    decorators: Vec::new(),
                    name: None,
                    is_async: false,
                    is_generator: false,
                    type_parameters: None,
                    parameters: vec![parameter],
                    return_type: None,
                    body: Some(FunctionBody::Block(body)),
                },
            }),
        );
        let callee = self.syn_node(range, Expression::Parenthesized(Box::new(function)));
        let call = self.syn_node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(callee),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(argument))],
            }),
        );
        self.expression_statement(call, range)
    }

    fn or_create(&mut self, read: Expr, create: Expr, range: TextRange) -> Expr {
        let create = self.syn_node(range, Expression::Parenthesized(Box::new(create)));
        self.syn_node(
            range,
            Expression::Logical(LogicalExpression {
                operator: LogicalOperator::Or,
                left: Box::new(read),
                right: Box::new(create),
            }),
        )
    }

    fn name_assignment(&mut self, name: &str, value: Expr, range: TextRange) -> Expr {
        let name = self.ident(name);
        let left = self.syn_node(range, AssignmentTarget::Identifier(name));
        self.assignment(left, value, range)
    }

    fn member_assignment(
        &mut self,
        parameter: &str,
        name: &str,
        value: Expr,
        range: TextRange,
    ) -> Expr {
        let object = self.ident_expr(parameter);
        let property = MemberProperty::Named(self.ident(name));
        let left = self.syn_node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        );
        self.assignment(left, value, range)
    }

    fn assignment(&mut self, left: AssignmentTargetNode, value: Expr, range: TextRange) -> Expr {
        self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        )
    }

    fn expression_statement(&mut self, expression: Expr, range: TextRange) -> Stmt {
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(expression),
            }),
        )
    }
}
