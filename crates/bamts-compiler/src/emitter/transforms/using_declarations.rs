//! `using` and `await using` declarations below ESNext: the statement list
//! that holds one runs inside a `try` whose `finally` disposes what the
//! declarations registered.
//!
//! ```text
//! const env_1 = { stack: [], error: void 0, hasError: false };
//! try {
//!     const d = __addDisposableResource(env_1, value, false);
//! }
//! catch (e_1) {
//!     env_1.error = e_1;
//!     env_1.hasError = true;
//! }
//! finally {
//!     __disposeResources(env_1);
//! }
//! ```
//!
//! An environment takes its name before the statements inside it are
//! rewritten and its catch binding after, so nested environments number
//! outside-in and their catch bindings inside-out.

use std::collections::BTreeSet;

use crate::source::TextRange;
use crate::syntax::*;

use super::helpers::HelperKind;
use super::{LanguageFeature, Rewriter, ScriptTarget, declared_binding_names};

/// How a disposal environment is drained when its statements complete.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Disposal {
    Sync,
    Async,
}

/// What a top-level statement contributes once its file guards a resource.
enum RootSlot<'a> {
    /// Rewritten in place, in source order.
    Guarded(Vec<Stmt>),
    /// A declaration whose names hoist; it is rewritten after the hoisted
    /// functions, which is the order tsc numbers generated names in.
    Hoisted(&'a Stmt),
    /// A namespace or enum, rewritten in the same late pass.
    Container(&'a Stmt),
    Function(&'a Stmt),
    AfterGuard(Vec<Stmt>),
}

fn is_resource_kind(kind: VariableKind) -> bool {
    matches!(kind, VariableKind::Using | VariableKind::AwaitUsing)
}

fn disposal_of(statements: &[Stmt]) -> Option<Disposal> {
    let mut disposal = None;
    for statement in statements {
        let Statement::Variable(declaration) = statement.data() else {
            continue;
        };
        match declaration.kind {
            VariableKind::AwaitUsing => return Some(Disposal::Async),
            VariableKind::Using => disposal = Some(Disposal::Sync),
            _ => {}
        }
    }
    disposal
}

impl Rewriter<'_> {
    pub(super) fn lowers_resources(&self, kind: VariableKind) -> bool {
        is_resource_kind(kind) && Self::needs(LanguageFeature::Using, self.options)
    }

    /// The declaration kind of a generated binding: `const`, or `var` where
    /// the target has no block scoping.
    fn generated_binding_kind(&self) -> VariableKind {
        if self.options.target <= ScriptTarget::Es5 {
            VariableKind::Var
        } else {
            VariableKind::Const
        }
    }

    /// Names the environment for a statement list that declares a resource.
    pub(super) fn open_disposal_environment(&mut self, statements: &[Stmt]) -> Option<Disposal> {
        if !Self::needs(LanguageFeature::Using, self.options) {
            return None;
        }
        let disposal = disposal_of(statements)?;
        let environment = self.source_name_ident("env");
        self.disposal_environments.push(environment);
        Some(disposal)
    }

    /// `const d = __addDisposableResource(env_1, value, false);`
    pub(super) fn register_resources(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let Some(environment) = self.disposal_environments.last().cloned() else {
            return vec![statement.clone()];
        };
        let is_async = declaration.kind == VariableKind::AwaitUsing;
        let mut declarations = Vec::with_capacity(declaration.declarations.len());
        for declarator in &declaration.declarations {
            let registered = self.registered_resource(declarator, &environment, is_async);
            declarations.push(self.node(
                declarator.range(),
                VariableDeclarator {
                    binding: declarator.data().binding.clone(),
                    definite: false,
                    type_annotation: None,
                    initializer: Some(Box::new(registered)),
                },
            ));
        }
        let lowered = VariableDeclaration {
            range: declaration.range,
            kind: self.generated_binding_kind(),
            declarations,
        };
        vec![self.syn_node(statement.range(), Statement::Variable(lowered))]
    }

    fn registered_resource(
        &mut self,
        declarator: &VariableDeclaratorNode,
        environment: &IdentifierNode,
        is_async: bool,
    ) -> Expr {
        let range = declarator.range();
        let value = match &declarator.data().initializer {
            Some(initializer) => self.rewrite_expr(initializer),
            None => self.void_zero(range),
        };
        self.resource_registration(value, environment, is_async, range)
    }

    fn resource_registration(
        &mut self,
        value: Expr,
        environment: &IdentifierNode,
        is_async: bool,
        range: TextRange,
    ) -> Expr {
        let callee = self.helper_ident(HelperKind::AddDisposableResource);
        let environment = self.node(range, Expression::Identifier(environment.clone()));
        let flag = self.boolean_expr(is_async);
        self.call_expression(range, callee, vec![environment, value, flag])
    }

    /// `for (using d of xs) body` iterates a plain `const d_1` and registers
    /// each value in an environment that lives for one iteration.
    pub(super) fn lower_resource_for_of(
        &mut self,
        statement: &Stmt,
        for_of: &ForOfStatement,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let range = statement.range();
        let Some(BindingPattern::Identifier(resource)) = declaration
            .declarations
            .first()
            .map(|declarator| declarator.data().binding.data())
        else {
            return vec![statement.clone()];
        };
        let name = self.token_text(resource.data().token()).to_owned();
        let iterated = self.source_name_ident(&name);
        let iterable = self.rewrite_expr(&for_of.iterable);
        let environment = self.source_name_ident("env");
        self.disposal_environments.push(environment.clone());
        let is_async = declaration.kind == VariableKind::AwaitUsing;
        let value = self.node(range, Expression::Identifier(iterated.clone()));
        let registered = self.resource_registration(value, &environment, is_async, range);
        let mut body = vec![self.const_statement(resource.clone(), registered, range)];
        match for_of.body.data() {
            Statement::Block(block) => {
                for inner in &block.data().statements {
                    body.extend(self.rewrite_statement(inner));
                }
            }
            _ => body.extend(self.rewrite_statement(&for_of.body)),
        }
        let disposal = if is_async {
            Disposal::Async
        } else {
            Disposal::Sync
        };
        let statements = self.close_disposal_environment(body, disposal, range);
        let block = self.node(range, Block { statements });
        let body = self.node(range, Statement::Block(block));
        let head = VariableDeclaration {
            range: declaration.range,
            kind: self.generated_binding_kind(),
            declarations: vec![self.make_declarator(iterated, None, range)],
        };
        vec![self.node(
            range,
            Statement::ForOf(ForOfStatement {
                mode: for_of.mode,
                binding: ForBinding::Variable(head),
                iterable: Box::new(iterable),
                body: Box::new(body),
            }),
        )]
    }

    /// `for (using d = v;;) body` becomes a block that declares the resource
    /// and then runs the loop without an initializer.
    pub(super) fn lower_resource_for(
        &mut self,
        statement: &Stmt,
        for_statement: &ForStatement,
    ) -> Vec<Stmt> {
        let Some(ForInitializer::Variable(declaration)) = &for_statement.initializer else {
            return vec![statement.clone()];
        };
        let range = statement.range();
        let resources = self.node(range, Statement::Variable(declaration.clone()));
        let looped = self.node(
            range,
            Statement::For(ForStatement {
                initializer: None,
                ..for_statement.clone()
            }),
        );
        let statements = self.rewrite_statements(&[resources, looped]);
        let block = self.node(range, Block { statements });
        vec![self.node(range, Statement::Block(block))]
    }

    /// A file whose top level declares a resource. Function declarations
    /// move above the guard and the names of the other declarations hoist
    /// into one `var`, so code after the guard still reaches them.
    pub(super) fn rewrite_root_resources(
        &mut self,
        statements: &[Stmt],
        disposal: Disposal,
        range: TextRange,
    ) -> Vec<Stmt> {
        self.declared_names.push(BTreeSet::new());
        let mut names = Vec::with_capacity(statements.len());
        let mut slots = Vec::with_capacity(statements.len());
        for statement in statements {
            self.record_declaration(statement);
            let (slot, declared) = self.root_slot(statement);
            slots.push(slot);
            names.push(declared);
        }
        let exit = self.disposal_exit(disposal, range);
        let mut out = Vec::new();
        for slot in &slots {
            if let RootSlot::Function(function) = slot {
                out.extend(self.rewrite_statement(function));
            }
        }
        let mut guarded = Vec::new();
        let mut after = Vec::new();
        for (slot, declared) in slots.into_iter().zip(&mut names) {
            match slot {
                RootSlot::Guarded(rewritten) => guarded.extend(rewritten),
                RootSlot::Hoisted(statement) => guarded.extend(self.hoisted_assignments(statement)),
                RootSlot::Container(statement) => {
                    let (rewritten, variable) = self.hoisted_container(statement);
                    guarded.extend(rewritten);
                    *declared = variable;
                }
                RootSlot::AfterGuard(rewritten) => after.extend(rewritten),
                RootSlot::Function(_) => {}
            }
        }
        self.declared_names.pop();
        let hoisted: Vec<IdentifierNode> = names
            .into_iter()
            .flatten()
            .map(|name| self.ident(&name))
            .collect();
        out.extend(self.temp_declaration(hoisted, range));
        out.extend(self.guard_statements(guarded, exit, range));
        out.extend(after);
        out
    }

    fn root_slot<'a>(&mut self, statement: &'a Stmt) -> (RootSlot<'a>, Vec<String>) {
        match statement.data() {
            Statement::Function(_) => (RootSlot::Function(statement), Vec::new()),
            Statement::Variable(_) => (
                RootSlot::Hoisted(statement),
                declared_binding_names(self.file, statement),
            ),
            Statement::Class(class) => {
                let name = class
                    .name
                    .as_ref()
                    .map(|name| self.token_text(name.data().token()).to_owned());
                (RootSlot::Hoisted(statement), name.into_iter().collect())
            }
            Statement::Namespace(_) | Statement::Enum(_) => {
                (RootSlot::Container(statement), Vec::new())
            }
            Statement::Import(_) | Statement::Export(_) => (
                RootSlot::AfterGuard(self.rewrite_statement(statement)),
                Vec::new(),
            ),
            _ => {
                let mut rewritten = self.rewrite_statement(statement);
                rewritten.extend(self.cjs_publish_declared(statement));
                (RootSlot::Guarded(rewritten), Vec::new())
            }
        }
    }

    /// A namespace or enum keeps its closure inside the guard; the variable
    /// it declares for itself joins the hoisted names instead.
    fn hoisted_container(&mut self, statement: &Stmt) -> (Vec<Stmt>, Vec<String>) {
        let mut rewritten = self.rewrite_statement(statement);
        let declared: Vec<String> = match rewritten.first().map(Node::data) {
            Some(Statement::Variable(declaration)) => declaration
                .declarations
                .iter()
                .filter_map(|declarator| match declarator.data().binding.data() {
                    BindingPattern::Identifier(name) => Some(self.bank_text(name.data().token())),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        if !declared.is_empty() {
            rewritten.remove(0);
        }
        (rewritten, declared)
    }

    fn hoisted_assignments(&mut self, statement: &Stmt) -> Vec<Stmt> {
        match statement.data() {
            Statement::Variable(declaration) if is_resource_kind(declaration.kind) => {
                self.resource_assignments(statement, declaration)
            }
            Statement::Variable(declaration) => {
                self.system_variable_statement(statement, declaration)
            }
            Statement::Class(class) => self.class_assignments(statement, class),
            _ => self.rewrite_statement(statement),
        }
    }

    /// `d = __addDisposableResource(env_1, value, false);`
    fn resource_assignments(
        &mut self,
        statement: &Stmt,
        declaration: &VariableDeclaration,
    ) -> Vec<Stmt> {
        let Some(environment) = self.disposal_environments.last().cloned() else {
            return vec![statement.clone()];
        };
        let is_async = declaration.kind == VariableKind::AwaitUsing;
        let mut out = Vec::with_capacity(declaration.declarations.len());
        for declarator in &declaration.declarations {
            let BindingPattern::Identifier(name) = declarator.data().binding.data() else {
                continue;
            };
            let name = self.token_text(name.data().token()).to_owned();
            let registered = self.registered_resource(declarator, &environment, is_async);
            out.push(self.system_plain_assignment(&name, registered, declarator.range()));
        }
        out
    }

    /// `C = class C { ... };`
    fn class_assignments(&mut self, statement: &Stmt, class: &ClassDeclaration) -> Vec<Stmt> {
        let mut out = Vec::new();
        for rewritten in self.rewrite_class_statement(statement, class) {
            let range = rewritten.range();
            match rewritten.into_data() {
                Statement::Class(class) => {
                    let Some(name) = class
                        .name
                        .as_ref()
                        .map(|name| self.bank_text(name.data().token()))
                    else {
                        out.push(self.node(range, Statement::Class(class)));
                        continue;
                    };
                    let value = self.syn_node(range, Expression::Class(ClassExpression { class }));
                    out.push(self.system_plain_assignment(&name, value, range));
                }
                other => out.push(self.node(range, other)),
            }
        }
        out
    }

    /// Wraps the rewritten statements of the innermost environment.
    pub(super) fn close_disposal_environment(
        &mut self,
        body: Vec<Stmt>,
        disposal: Disposal,
        range: TextRange,
    ) -> Vec<Stmt> {
        let exit = self.disposal_exit(disposal, range);
        self.guard_statements(body, exit, range)
    }

    /// The catch and finally of the innermost environment. Their generated
    /// names are taken here, so the caller decides where they fall in the
    /// file's numbering.
    fn disposal_exit(
        &mut self,
        disposal: Disposal,
        range: TextRange,
    ) -> Option<(CatchClauseNode, BlockNode)> {
        let environment = self.disposal_environments.last().cloned()?;
        let handler = self.disposal_handler(&environment, range);
        let finalizer = self.disposal_finalizer(&environment, disposal, range);
        Some((handler, finalizer))
    }

    fn guard_statements(
        &mut self,
        body: Vec<Stmt>,
        exit: Option<(CatchClauseNode, BlockNode)>,
        range: TextRange,
    ) -> Vec<Stmt> {
        let (Some(environment), Some((handler, finalizer))) =
            (self.disposal_environments.pop(), exit)
        else {
            return body;
        };
        let record = self.disposal_record(&environment, range);
        let block = self.node(range, Block { statements: body });
        let guarded = self.syn_node(
            range,
            Statement::Try(TryStatement {
                block,
                handler: Some(handler),
                finalizer: Some(finalizer),
            }),
        );
        vec![record, guarded]
    }

    fn disposal_record(&mut self, environment: &IdentifierNode, range: TextRange) -> Stmt {
        let stack = self.array_literal(Vec::new(), range);
        let error = self.void_zero(range);
        let has_error = self.boolean_expr(false);
        let record = self.object_literal(
            vec![("stack", stack), ("error", error), ("hasError", has_error)],
            range,
        );
        self.alternate_layout.insert(record.id());
        self.const_statement(environment.clone(), record, range)
    }

    fn const_statement(&mut self, name: IdentifierNode, value: Expr, range: TextRange) -> Stmt {
        let declarator = self.make_declarator(name, Some(value), range);
        self.syn_node(
            range,
            Statement::Variable(VariableDeclaration {
                range,
                kind: self.generated_binding_kind(),
                declarations: vec![declarator],
            }),
        )
    }

    fn disposal_handler(
        &mut self,
        environment: &IdentifierNode,
        range: TextRange,
    ) -> CatchClauseNode {
        let caught = self.source_name_ident("e");
        let caught_value = self.node(range, Expression::Identifier(caught.clone()));
        let record_error = self.environment_assignment(environment, "error", caught_value, range);
        let raised = self.boolean_expr(true);
        let record_flag = self.environment_assignment(environment, "hasError", raised, range);
        let binding = self.node(caught.range(), BindingPattern::Identifier(caught));
        let body = self.node(
            range,
            Block {
                statements: vec![record_error, record_flag],
            },
        );
        self.node(
            range,
            CatchClause {
                binding: Some(binding),
                body,
            },
        )
    }

    fn environment_assignment(
        &mut self,
        environment: &IdentifierNode,
        field: &str,
        value: Expr,
        range: TextRange,
    ) -> Stmt {
        let object = self.node(range, Expression::Identifier(environment.clone()));
        let property = self.named_or_computed(field, range);
        let left = self.syn_node(
            range,
            AssignmentTarget::Member(AssignmentMemberTarget {
                object: Box::new(object),
                property,
            }),
        );
        let assignment = self.syn_node(
            range,
            Expression::Assignment(AssignmentExpression {
                operator: AssignmentOperator::Assign,
                left,
                right: Box::new(value),
            }),
        );
        self.expression_statement(assignment, range)
    }

    fn disposal_finalizer(
        &mut self,
        environment: &IdentifierNode,
        disposal: Disposal,
        range: TextRange,
    ) -> BlockNode {
        let callee = self.helper_ident(HelperKind::DisposeResources);
        let argument = self.node(range, Expression::Identifier(environment.clone()));
        let drained = self.call_expression(range, callee, vec![argument]);
        let statements = match disposal {
            Disposal::Sync => vec![self.expression_statement(drained, range)],
            Disposal::Async => self.await_pending_disposal(drained, range),
        };
        self.node(range, Block { statements })
    }

    /// `const result_1 = __disposeResources(env_1); if (result_1) await result_1;`
    fn await_pending_disposal(&mut self, drained: Expr, range: TextRange) -> Vec<Stmt> {
        let pending = self.source_name_ident("result");
        let test = self.node(range, Expression::Identifier(pending.clone()));
        let awaited = self.node(range, Expression::Identifier(pending.clone()));
        let wait = self.syn_node(
            range,
            Expression::Await(AwaitExpression {
                argument: Box::new(awaited),
            }),
        );
        let consequent = self.expression_statement(wait, range);
        let hold = self.const_statement(pending, drained, range);
        let settle = self.syn_node(
            range,
            Statement::If(IfStatement {
                test: Box::new(test),
                consequent: Box::new(consequent),
                alternate: None,
            }),
        );
        self.alternate_layout.insert(settle.id());
        vec![hold, settle]
    }
}
