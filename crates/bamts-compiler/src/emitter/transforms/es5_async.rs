//! The `__generator` machine shapes beyond the straight-line core: logical
//! and conditional expressions that suspend in a branch, blocks and try
//! statements in machine bodies, variable hoisting inside verbatim regions,
//! labeled jumps out of clean loops, and the `this`/`arguments` capture
//! that lowers an async arrow to a function expression.
//!
//! Authority: `es5-asyncFunction*` baselines under
//! `tests/baselines/reference/`, target es5.

use crate::source::TextRange;
use crate::syntax::*;

use super::MachineCtx;
use super::{contains_yield, count_branch_yields, identifier_names};

impl super::Rewriter<'_> {
    /// One statement of a machine body. This is the dispatch the
    /// straight-line core keeps in `generator_machine`; the richer shapes
    /// live in this module.
    pub(super) fn machine_statement(
        &mut self,
        statement: &Stmt,
        block_range: TextRange,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        match statement.data() {
            Statement::Variable(declaration) if declaration.kind == VariableKind::Var => {
                for declarator in &declaration.declarations {
                    let BindingPattern::Identifier(name) = declarator.data().binding.data() else {
                        return None;
                    };
                    let name = name.clone();
                    ctx.hoisted.push(name.clone());
                    if let Some(initializer) = &declarator.data().initializer {
                        let value = if contains_yield(initializer) {
                            self.eval(initializer, ctx)?
                        } else {
                            initializer.as_ref().clone()
                        };
                        let assign = self.assign_statement(&name, value, block_range);
                        ctx.push(assign);
                    }
                }
            }
            Statement::Expression(expression) => {
                self.machine_emit_expression(&expression.expression, ctx)?;
            }
            Statement::If(if_statement) => {
                self.machine_emit_if(statement, if_statement, ctx)?;
            }
            Statement::While(while_statement) => {
                self.machine_emit_while(statement, while_statement, None, ctx)?;
            }
            Statement::DoWhile(do_statement) => {
                self.machine_emit_do(statement, do_statement, None, ctx)?;
            }
            Statement::For(for_statement) => {
                self.machine_emit_for(statement, for_statement, None, ctx)?;
            }
            Statement::Switch(switch_statement) => {
                self.machine_emit_switch(statement, switch_statement, ctx)?;
            }
            Statement::Labeled(labeled) => {
                let name = self.identifier_name(&labeled.label)?;
                ctx.loop_labels.push(name);
                let result = self.machine_emit_labeled(statement, &labeled.body, ctx);
                ctx.loop_labels.pop();
                result?;
            }
            Statement::Return(returned) => {
                let terminator = match &returned.argument {
                    Some(value) if contains_yield(value) => {
                        let evaluated = self.eval(value, ctx)?;
                        let sentinel = self.number_expr("2 /*return*/");
                        let array = self.array_literal(vec![sentinel, evaluated], block_range);
                        self.machine_return(array, block_range)
                    }
                    Some(value) => {
                        let sentinel = self.number_expr("2 /*return*/");
                        let array =
                            self.array_literal(vec![sentinel, value.as_ref().clone()], block_range);
                        self.machine_return(array, block_range)
                    }
                    None => {
                        let sentinel = self.return_sentinel(block_range);
                        self.machine_return(sentinel, block_range)
                    }
                };
                ctx.push(terminator);
                ctx.terminated = true;
            }
            Statement::Block(block) => {
                self.machine_block_statement(statement, block, ctx)?;
            }
            Statement::Try(try_statement) => {
                self.machine_try_statement(statement, try_statement, ctx)?;
            }
            Statement::Function(_) => {
                // Function declarations hoist above the machine call; their
                // bodies were rewritten on the way in.
                ctx.declarations.push(statement.clone());
            }
            _ => return None,
        }
        Some(())
    }

    /// Evaluates `left <op> right` where the right operand suspends: the
    /// left value is held in a temp, the guard skips the right when the
    /// temp already decides the result, and the resume stores the sent
    /// value back into the temp before falling into the join label.
    pub(super) fn machine_logical(
        &mut self,
        logical: &LogicalExpression,
        ctx: &mut MachineCtx,
        range: TextRange,
    ) -> Option<Expr> {
        if matches!(logical.operator, LogicalOperator::Nullish) {
            return None;
        }
        if !contains_yield(&logical.right) {
            let left = self.eval(&logical.left, ctx)?;
            let left = self.paren_if_sent(left, logical.left.range());
            return Some(self.node(
                range,
                Expression::Logical(LogicalExpression {
                    operator: logical.operator,
                    left: Box::new(left),
                    right: logical.right.clone(),
                }),
            ));
        }
        let left = self.machine_operand(&logical.left, ctx)?;
        let temp = self.temp_of(&left)?;
        let base_segment = ctx.segments.len() - 1;
        let insertion = ctx.segments[base_segment].len();
        let value = self.eval(&logical.right, ctx)?;
        let skip = ctx.segments.len() as u32;
        let guard =
            self.machine_guard(&left, logical.operator == LogicalOperator::And, skip, range);
        ctx.segments[base_segment].insert(insertion, guard);
        let value = self.paren_if_sent(value, range);
        ctx.push(self.assign_statement(&temp, value, range));
        let state = ctx.state.clone();
        ctx.push(self.label_assignment(skip, &state, range));
        ctx.segments.push(Vec::new());
        Some(self.node(range, Expression::Identifier(temp)))
    }

    /// Evaluates `test ? consequent : alternate` with a suspending branch:
    /// both branch values land in one fresh temp, the guard jumps to the
    /// else segment, and the join label follows the alternate segment.
    pub(super) fn machine_conditional(
        &mut self,
        conditional: &ConditionalExpression,
        ctx: &mut MachineCtx,
        range: TextRange,
    ) -> Option<Expr> {
        let cons_suspends = contains_yield(&conditional.consequent);
        let alt_suspends = contains_yield(&conditional.alternate);
        if !cons_suspends && !alt_suspends {
            let test = self.eval(&conditional.test, ctx)?;
            let test = self.paren_if_sent(test, conditional.test.range());
            return Some(self.node(
                range,
                Expression::Conditional(ConditionalExpression {
                    test: Box::new(test),
                    consequent: conditional.consequent.clone(),
                    alternate: conditional.alternate.clone(),
                }),
            ));
        }
        let temp = self.temp_ident();
        ctx.temps.push(temp.clone());
        let test = if contains_yield(&conditional.test) {
            let value = self.eval(&conditional.test, ctx)?;
            self.paren_if_sent(value, conditional.test.range())
        } else {
            conditional.test.as_ref().clone()
        };
        let base_segment = ctx.segments.len() - 1;
        let insertion = ctx.segments[base_segment].len();
        let cons_value = if cons_suspends {
            self.eval(&conditional.consequent, ctx)?
        } else {
            conditional.consequent.as_ref().clone()
        };
        ctx.push(self.assign_statement(&temp, cons_value, range));
        let mut join_breaks = Vec::new();
        self.push_patchable_break(ctx, &mut join_breaks, range);
        let else_label = ctx.segments.len() as u32;
        ctx.segments.push(Vec::new());
        let alt_value = if alt_suspends {
            self.eval(&conditional.alternate, ctx)?
        } else {
            conditional.alternate.as_ref().clone()
        };
        ctx.push(self.assign_statement(&temp, alt_value, range));
        let state = ctx.state.clone();
        let end_label = ctx.segments.len() as u32;
        ctx.push(self.label_assignment(end_label, &state, range));
        ctx.segments.push(Vec::new());
        let guard = self.machine_guard(&test, true, else_label, range);
        ctx.segments[base_segment].insert(insertion, guard);
        self.patch_breaks(ctx, join_breaks, end_label, range);
        Some(self.node(range, Expression::Identifier(temp)))
    }

    /// Evaluates one operand into a temp: a plain expression is stored as
    /// written, a suspending one reassembles around the sent value first.
    fn machine_operand(&mut self, expression: &Expr, ctx: &mut MachineCtx) -> Option<Expr> {
        if contains_yield(expression) {
            let value = self.eval(expression, ctx)?;
            let value = self.paren_if_sent(value, expression.range());
            self.materialize(value, ctx, expression.range())
        } else {
            self.materialize(expression.clone(), ctx, expression.range())
        }
    }

    /// `if (!value) return [3 /*break*/, label];` for `&&` and a
    /// conditional test, the positive guard for `||`.
    fn machine_guard(&mut self, value: &Expr, negate: bool, label: u32, range: TextRange) -> Stmt {
        let test = if negate {
            self.node(
                value.range(),
                Expression::Unary(UnaryExpression {
                    operator: UnaryOperator::Not,
                    argument: Box::new(value.clone()),
                }),
            )
        } else {
            value.clone()
        };
        let jump = self.break_to(label, range);
        self.node(
            range,
            Statement::If(IfStatement {
                test: Box::new(test),
                consequent: Box::new(jump),
                alternate: None,
            }),
        )
    }

    /// The identifier a materialized temp expression reads.
    fn temp_of(&self, expression: &Expr) -> Option<IdentifierNode> {
        match expression.data() {
            Expression::Identifier(ident) => Some(ident.clone()),
            _ => None,
        }
    }

    /// A nested block in a machine body: a suspending block flattens its
    /// statements into the machine, a clean one prints with its braces and
    /// hoists the vars inside.
    pub(super) fn machine_block_statement(
        &mut self,
        statement: &Stmt,
        block: &BlockNode,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        if count_branch_yields(&block.data().statements) > 0 {
            let range = block.range();
            for inner in &block.data().statements {
                if ctx.terminated {
                    return None;
                }
                self.machine_statement(inner, range, ctx)?;
            }
            return Some(());
        }
        for rewritten in self.machine_prepare_verbatim(statement, ctx)? {
            ctx.push(rewritten);
        }
        Some(())
    }

    /// A try statement in a machine body. A try with no suspension anywhere
    /// prints verbatim; otherwise the trys row is pushed ahead of the body
    /// ops, the catch segment starts with `e_N = state.sent()`, the finally
    /// segment ends with `return [7 /*endfinally*/]`, and every region
    /// closes with a break to the shared end label.
    pub(super) fn machine_try_statement(
        &mut self,
        statement: &Stmt,
        try_statement: &TryStatement,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = statement.range();
        let try_stmts = &try_statement.block.data().statements;
        let handler = try_statement.handler.as_ref();
        let finalizer = try_statement.finalizer.as_ref();
        let try_suspends = count_branch_yields(try_stmts) > 0;
        let catch_suspends = handler
            .is_some_and(|handler| count_branch_yields(&handler.data().body.data().statements) > 0);
        let finally_suspends = finalizer
            .is_some_and(|finalizer| count_branch_yields(&finalizer.data().statements) > 0);
        if !try_suspends && !catch_suspends && !finally_suspends {
            for rewritten in self.machine_prepare_verbatim(statement, ctx)? {
                ctx.push(rewritten);
            }
            return Some(());
        }
        let base = ctx.segments.len() as u32 - 1;
        let insertion = ctx.segments.last()?.len();
        let mut join_breaks = Vec::new();

        let try_terminated =
            self.machine_region(try_stmts, try_suspends, try_statement.block.range(), ctx)?;
        if !try_terminated {
            self.push_patchable_break(ctx, &mut join_breaks, range);
        }

        let mut catch_label = None;
        if let Some(handler) = handler {
            catch_label = Some(ctx.segments.len() as u32);
            ctx.segments.push(Vec::new());
            let catch_terminated = self.machine_catch(handler, catch_suspends, ctx)?;
            if !catch_terminated {
                self.push_patchable_break(ctx, &mut join_breaks, range);
            }
        }

        let mut finally_label = None;
        if let Some(finalizer) = finalizer {
            finally_label = Some(ctx.segments.len() as u32);
            ctx.segments.push(Vec::new());
            self.machine_finally(finalizer, finally_suspends, ctx)?;
        }

        let end = ctx.segments.len() as u32;
        ctx.segments.push(Vec::new());
        ctx.terminated = false;

        let state = ctx.state.clone();
        let row = self.trys_row(base, catch_label, finally_label, end, range);
        let push = self.trys_push(&state, row, range);
        let segment = &mut ctx.segments[base as usize];
        segment.insert(insertion, push);
        self.patch_breaks(ctx, join_breaks, end, range);
        Some(())
    }

    /// One try region: machine ops when it suspends, verbatim statements
    /// with hoisted vars otherwise. Returns whether the region returned.
    fn machine_region(
        &mut self,
        statements: &[Stmt],
        suspends: bool,
        range: TextRange,
        ctx: &mut MachineCtx,
    ) -> Option<bool> {
        if suspends {
            for inner in statements {
                if ctx.terminated {
                    return None;
                }
                self.machine_statement(inner, range, ctx)?;
            }
            return Some(ctx.terminated);
        }
        self.machine_verbatim_region(statements, ctx)
    }

    /// Pushes verbatim statements and reports whether the region's last
    /// statement is a converted return, which needs no join break.
    fn machine_verbatim_region(
        &mut self,
        statements: &[Stmt],
        ctx: &mut MachineCtx,
    ) -> Option<bool> {
        let mark = ctx.segments.last()?.len();
        for statement in statements {
            for rewritten in self.machine_prepare_verbatim(statement, ctx)? {
                ctx.push(rewritten);
            }
        }
        let segment = ctx.segments.last()?;
        Some(
            segment.len() > mark
                && matches!(segment.last().map(|s| s.data()), Some(Statement::Return(_))),
        )
    }

    /// The catch segment: `e_N = state.sent();` ahead of the renamed body,
    /// which keeps the hoisted exception temp the body references read.
    fn machine_catch(
        &mut self,
        handler: &CatchClauseNode,
        suspends: bool,
        ctx: &mut MachineCtx,
    ) -> Option<bool> {
        let range = handler.data().body.range();
        let statements = handler.data().body.data().statements.to_vec();
        let statements = match &handler.data().binding {
            Some(binding) => {
                let BindingPattern::Identifier(name) = binding.data() else {
                    return None;
                };
                let original = self.identifier_name(name)?;
                let temp = self.catch_temp_ident(ctx);
                let sent = self.state_sent_call(&ctx.state, range);
                let assign = self.assign_statement(&temp, sent, range);
                ctx.push(assign);
                self.rename_catch_statements(statements, &original, &temp)
            }
            None => statements,
        };
        if suspends {
            for inner in &statements {
                if ctx.terminated {
                    return None;
                }
                self.machine_statement(inner, range, ctx)?;
            }
            return Some(ctx.terminated);
        }
        self.machine_verbatim_region(&statements, ctx)
    }

    /// The finally segment, closed by the endfinally sentinel unless the
    /// body itself returned.
    fn machine_finally(
        &mut self,
        finalizer: &BlockNode,
        suspends: bool,
        ctx: &mut MachineCtx,
    ) -> Option<()> {
        let range = finalizer.range();
        let terminated = self.machine_region(&finalizer.data().statements, suspends, range, ctx)?;
        if terminated {
            return Some(());
        }
        let sentinel = self.number_expr("7 /*endfinally*/");
        let array = self.array_literal(vec![sentinel], range);
        ctx.push(self.machine_return(array, range));
        Some(())
    }

    /// Renames the catch binding's references to the hoisted `e_N` temp,
    /// matching the binding-aware rename the class-self lowering uses.
    fn rename_catch_statements(
        &mut self,
        statements: Vec<Stmt>,
        original: &str,
        temp: &IdentifierNode,
    ) -> Vec<Stmt> {
        self.rename_class_self_in_statements(statements, original, None, temp)
    }

    /// The `_this` the awaiter receives: the enclosing function's capture,
    /// registered on first use so `var _this = this;` hoists there.
    pub(super) fn capture_this_for_awaiter(&mut self) -> IdentifierNode {
        if let Some(existing) = self
            .capture_scopes
            .last()
            .and_then(|scope| scope.this.clone())
        {
            return existing;
        }
        let name = self.capture_name("_this");
        if let Some(scope) = self.capture_scopes.last_mut() {
            scope.this = Some(name.clone());
        }
        name
    }

    /// The `arguments_N` the lowered function hoists, unique per file.
    pub(super) fn capture_arguments_for_awaiter(&mut self) -> IdentifierNode {
        let file = self.file;
        let occupied = self
            .occupied_names
            .get_or_insert_with(|| identifier_names(file));
        let mut suffix = 1;
        let mut name = String::from("arguments_1");
        while occupied.contains(&name) {
            suffix += 1;
            name = format!("arguments_{suffix}");
        }
        occupied.insert(name.clone());
        self.ident(&name)
    }

    /// Renames `arguments` references in an async arrow body to the hoisted
    /// temp before the await conversion runs.
    pub(super) fn rename_arguments_in_body(
        &mut self,
        body: &FunctionBody,
        temp: &IdentifierNode,
    ) -> FunctionBody {
        match body {
            FunctionBody::Expression(expr) => {
                let renamed = self.rename_class_self_in_expression(
                    expr.as_ref().clone(),
                    "arguments",
                    None,
                    temp,
                );
                FunctionBody::Expression(Box::new(renamed))
            }
            FunctionBody::Block(block) => {
                let renamed = self.rename_class_self_in_statements(
                    block.data().statements.clone(),
                    "arguments",
                    None,
                    temp,
                );
                let range = block.range();
                FunctionBody::Block(self.node(
                    range,
                    Block {
                        statements: renamed,
                    },
                ))
            }
            FunctionBody::Missing(_) => body.clone(),
        }
    }

    /// A fresh hoisted `e_N`, numbered once per file like tsc's exception
    /// temps.
    fn catch_temp_ident(&mut self, ctx: &mut MachineCtx) -> IdentifierNode {
        let name = self.next_catch_temp_name();
        let ident = self.ident(&name);
        ctx.hoisted.push(ident.clone());
        ident
    }

    /// The `[start, catch, finally, end]` row with elisions for absent
    /// regions, as the `__generator` helper's `trys` protocol reads it.
    fn trys_row(
        &mut self,
        base: u32,
        catch_label: Option<u32>,
        finally_label: Option<u32>,
        end: u32,
        range: TextRange,
    ) -> Expr {
        let mut elements = vec![ArrayElement::Expression(Box::new(
            self.number_expr(&base.to_string()),
        ))];
        elements.push(match catch_label {
            Some(label) => ArrayElement::Expression(Box::new(self.number_expr(&label.to_string()))),
            None => ArrayElement::Elision,
        });
        elements.push(match finally_label {
            Some(label) => ArrayElement::Expression(Box::new(self.number_expr(&label.to_string()))),
            None => ArrayElement::Elision,
        });
        elements.push(ArrayElement::Expression(Box::new(
            self.number_expr(&end.to_string()),
        )));
        self.node(range, Expression::Array(ArrayLiteral { elements }))
    }

    /// `state.trys.push([...]);`
    fn trys_push(&mut self, state: &str, row: Expr, range: TextRange) -> Stmt {
        let state_expr = self.ident_expr(state);
        let trys = self.member_access(state_expr, "trys", range);
        let push = self.member_access(trys, "push", range);
        let call = self.node(
            range,
            Expression::Call(CallExpression {
                callee: Box::new(push),
                optional: false,
                type_arguments: None,
                arguments: vec![CallArgument::Expression(Box::new(row))],
            }),
        );
        self.syn_node(
            range,
            Statement::Expression(ExpressionStatement {
                expression: Box::new(call),
            }),
        )
    }

    /// A break whose target label is filled in once the end segment exists.
    fn push_patchable_break(
        &mut self,
        ctx: &mut MachineCtx,
        breaks: &mut Vec<(usize, NodeId)>,
        range: TextRange,
    ) {
        let placeholder = self.break_to(0, range);
        let id = placeholder.id();
        let segment = ctx.segments.len() - 1;
        ctx.segments[segment].push(placeholder);
        breaks.push((segment, id));
    }

    /// Replaces each recorded placeholder with the final break.
    fn patch_breaks(
        &mut self,
        ctx: &mut MachineCtx,
        breaks: Vec<(usize, NodeId)>,
        end: u32,
        range: TextRange,
    ) {
        for (segment, id) in breaks {
            if let Some(index) = ctx.segments[segment]
                .iter()
                .position(|statement| statement.id() == id)
            {
                ctx.segments[segment][index] = self.break_to(end, range);
            }
        }
    }

    /// Rewrites a statement for verbatim machine placement: vars become
    /// assignments with hoisted names, and labeled jumps out to a machine
    /// loop become break returns.
    pub(super) fn machine_prepare_verbatim(
        &mut self,
        statement: &Stmt,
        ctx: &mut MachineCtx,
    ) -> Option<Vec<Stmt>> {
        let statements = self.machine_rewrite_vars(statement.clone(), ctx)?;
        let mut rewritten = Vec::with_capacity(statements.len());
        for statement in statements {
            rewritten.push(self.machine_clean_jumps(statement, ctx)?);
        }
        Some(rewritten)
    }

    /// Converts `var` declarations inside a verbatim region into
    /// assignments and hoists every name to the machine's var list.
    pub(super) fn machine_rewrite_vars(
        &mut self,
        statement: Stmt,
        ctx: &mut MachineCtx,
    ) -> Option<Vec<Stmt>> {
        let range = statement.range();
        match statement.into_data() {
            Statement::Variable(declaration) if declaration.kind == VariableKind::Var => {
                let mut statements = Vec::new();
                for declarator in declaration.declarations {
                    let BindingPattern::Identifier(name) = declarator.data().binding.data() else {
                        return None;
                    };
                    let name = name.clone();
                    ctx.hoisted.push(name.clone());
                    if let Some(initializer) = declarator.into_data().initializer {
                        statements.push(self.assign_statement(&name, *initializer, range));
                    }
                }
                Some(statements)
            }
            Statement::Block(block) => {
                let mut statements = Vec::new();
                for inner in block.into_data().statements {
                    statements.extend(self.machine_rewrite_vars(inner, ctx)?);
                }
                let block = self.node(range, Block { statements });
                Some(vec![self.node(range, Statement::Block(block))])
            }
            Statement::If(if_statement) => {
                let consequent = self.machine_rewrite_branch(&if_statement.consequent, ctx)?;
                let alternate = match if_statement.alternate {
                    Some(alternate) => {
                        Some(Box::new(self.machine_rewrite_branch(&alternate, ctx)?))
                    }
                    None => None,
                };
                Some(vec![self.node(
                    range,
                    Statement::If(IfStatement {
                        test: if_statement.test.clone(),
                        consequent: Box::new(consequent),
                        alternate,
                    }),
                )])
            }
            Statement::While(while_statement) => {
                let body = self.machine_rewrite_branch(&while_statement.body, ctx)?;
                Some(vec![self.node(
                    range,
                    Statement::While(WhileStatement {
                        test: while_statement.test.clone(),
                        body: Box::new(body),
                    }),
                )])
            }
            Statement::DoWhile(do_statement) => {
                let body = self.machine_rewrite_branch(&do_statement.body, ctx)?;
                Some(vec![self.node(
                    range,
                    Statement::DoWhile(DoWhileStatement {
                        test: do_statement.test.clone(),
                        body: Box::new(body),
                    }),
                )])
            }
            Statement::Labeled(labeled) => {
                let LabeledStatement { label, body } = labeled;
                let rewritten = self.machine_rewrite_vars(*body, ctx)?;
                let body = match rewritten.as_slice() {
                    [one] => one.clone(),
                    [] => self.node(range, Statement::Empty),
                    _ => return None,
                };
                Some(vec![self.node(
                    range,
                    Statement::Labeled(LabeledStatement {
                        label,
                        body: Box::new(body),
                    }),
                )])
            }
            Statement::Try(try_statement) => {
                let mut statements = Vec::new();
                for inner in try_statement.block.into_data().statements {
                    statements.extend(self.machine_rewrite_vars(inner, ctx)?);
                }
                let block = self.node(range, Block { statements });
                let handler = match try_statement.handler {
                    Some(handler) => {
                        let handler_range = handler.range();
                        let CatchClause { binding, body } = handler.into_data();
                        let mut statements = Vec::new();
                        for inner in body.into_data().statements {
                            statements.extend(self.machine_rewrite_vars(inner, ctx)?);
                        }
                        let body = self.node(handler_range, Block { statements });
                        Some(self.node(handler_range, CatchClause { binding, body }))
                    }
                    None => None,
                };
                let finalizer = match try_statement.finalizer {
                    Some(finalizer) => {
                        let finalizer_range = finalizer.range();
                        let mut statements = Vec::new();
                        for inner in finalizer.into_data().statements {
                            statements.extend(self.machine_rewrite_vars(inner, ctx)?);
                        }
                        Some(self.node(finalizer_range, Block { statements }))
                    }
                    None => None,
                };
                Some(vec![self.node(
                    range,
                    Statement::Try(TryStatement {
                        block,
                        handler,
                        finalizer,
                    }),
                )])
            }
            Statement::Return(returned) => {
                let terminator = match returned.argument {
                    Some(value) => {
                        let sentinel = self.number_expr("2 /*return*/");
                        let array = self.array_literal(vec![sentinel, *value], range);
                        self.machine_return(array, range)
                    }
                    None => {
                        let sentinel = self.return_sentinel(range);
                        self.machine_return(sentinel, range)
                    }
                };
                Some(vec![terminator])
            }
            other => Some(vec![self.node(range, other)]),
        }
    }

    /// Rewrites one branch or loop body, keeping a single statement when
    /// the rewrite yields exactly one and collapsing an emptied block.
    fn machine_rewrite_branch(&mut self, branch: &Stmt, ctx: &mut MachineCtx) -> Option<Stmt> {
        let rewritten = self.machine_rewrite_vars(branch.clone(), ctx)?;
        match rewritten.as_slice() {
            [one] => Some(one.clone()),
            [] => {
                let range = branch.range();
                let block = self.node(
                    range,
                    Block {
                        statements: Vec::new(),
                    },
                );
                Some(self.node(range, Statement::Block(block)))
            }
            _ => None,
        }
    }

    /// Rewrites labeled jumps in a verbatim statement so a `continue` or
    /// `break` naming a machine loop becomes `return [3 /*break*/, label]`.
    /// Labels bound by loops inside the verbatim statement shadow the
    /// machine ones.
    pub(super) fn machine_clean_jumps(
        &mut self,
        statement: Stmt,
        ctx: &mut MachineCtx,
    ) -> Option<Stmt> {
        let mut shadows = Vec::new();
        self.clean_jump_walk(statement, &mut shadows, ctx)
    }

    fn clean_jump_walk(
        &mut self,
        statement: Stmt,
        shadows: &mut Vec<String>,
        ctx: &mut MachineCtx,
    ) -> Option<Stmt> {
        let range = statement.range();
        match statement.into_data() {
            Statement::Continue(jump) => {
                let original = self.node(range, Statement::Continue(jump));
                self.clean_jump_target(original, true, shadows, ctx, range)
            }
            Statement::Break(jump) => {
                let original = self.node(range, Statement::Break(jump));
                self.clean_jump_target(original, false, shadows, ctx, range)
            }
            Statement::Block(block) => {
                let mut statements = Vec::new();
                for inner in block.into_data().statements {
                    statements.push(self.clean_jump_walk(inner, shadows, ctx)?);
                }
                let block = self.node(range, Block { statements });
                Some(self.node(range, Statement::Block(block)))
            }
            Statement::If(if_statement) => {
                let consequent = self.clean_jump_walk(*if_statement.consequent, shadows, ctx)?;
                let alternate = match if_statement.alternate {
                    Some(alternate) => {
                        Some(Box::new(self.clean_jump_walk(*alternate, shadows, ctx)?))
                    }
                    None => None,
                };
                Some(self.node(
                    range,
                    Statement::If(IfStatement {
                        test: if_statement.test,
                        consequent: Box::new(consequent),
                        alternate,
                    }),
                ))
            }
            Statement::Labeled(labeled) => {
                let name = self.identifier_name(&labeled.label)?;
                shadows.push(name);
                let body = self.clean_jump_walk(*labeled.body, shadows, ctx);
                shadows.pop();
                Some(self.node(
                    range,
                    Statement::Labeled(LabeledStatement {
                        label: labeled.label,
                        body: Box::new(body?),
                    }),
                ))
            }
            Statement::While(while_statement) => {
                let body = self.clean_jump_walk(*while_statement.body, shadows, ctx)?;
                Some(self.node(
                    range,
                    Statement::While(WhileStatement {
                        test: while_statement.test,
                        body: Box::new(body),
                    }),
                ))
            }
            Statement::DoWhile(do_statement) => {
                let body = self.clean_jump_walk(*do_statement.body, shadows, ctx)?;
                Some(self.node(
                    range,
                    Statement::DoWhile(DoWhileStatement {
                        test: do_statement.test,
                        body: Box::new(body),
                    }),
                ))
            }
            Statement::For(for_statement) => {
                let body = self.clean_jump_walk(*for_statement.body, shadows, ctx)?;
                Some(self.node(
                    range,
                    Statement::For(ForStatement {
                        initializer: for_statement.initializer,
                        test: for_statement.test,
                        update: for_statement.update,
                        body: Box::new(body),
                    }),
                ))
            }
            Statement::Try(try_statement) => {
                let block = self.clean_jump_block(try_statement.block, shadows, ctx)?;
                let handler = match try_statement.handler {
                    Some(handler) => {
                        let handler_range = handler.range();
                        let CatchClause { binding, body } = handler.into_data();
                        let body = self.clean_jump_block(body, shadows, ctx)?;
                        Some(self.node(handler_range, CatchClause { binding, body }))
                    }
                    None => None,
                };
                let finalizer = match try_statement.finalizer {
                    Some(finalizer) => Some(self.clean_jump_block(finalizer, shadows, ctx)?),
                    None => None,
                };
                Some(self.node(
                    range,
                    Statement::Try(TryStatement {
                        block,
                        handler,
                        finalizer,
                    }),
                ))
            }
            other => Some(self.node(range, other)),
        }
    }

    fn clean_jump_block(
        &mut self,
        block: BlockNode,
        shadows: &mut Vec<String>,
        ctx: &mut MachineCtx,
    ) -> Option<BlockNode> {
        let range = block.range();
        let mut statements = Vec::new();
        for inner in block.into_data().statements {
            statements.push(self.clean_jump_walk(inner, shadows, ctx)?);
        }
        Some(self.node(range, Block { statements }))
    }

    /// A labeled jump to a machine loop becomes `return [3 /*break*/,
    /// label];`; any other jump keeps its native form.
    fn clean_jump_target(
        &mut self,
        statement: Stmt,
        is_continue: bool,
        shadows: &[String],
        ctx: &MachineCtx,
        range: TextRange,
    ) -> Option<Stmt> {
        let jump = match statement.data() {
            Statement::Continue(jump) | Statement::Break(jump) => jump,
            _ => return Some(statement),
        };
        let Some(label) = &jump.label else {
            return Some(statement);
        };
        let name = self.identifier_name(label)?;
        if shadows.iter().any(|shadow| shadow == &name) {
            return Some(statement);
        }
        let Some((_, continue_target, break_target)) = ctx
            .loop_jumps
            .iter()
            .rev()
            .find(|(candidate, _, _)| candidate == &name)
        else {
            return Some(statement);
        };
        let target = if is_continue {
            *continue_target
        } else {
            *break_target
        };
        Some(self.machine_return_array_label(target, range))
    }

    /// `return [3 /*break*/, label];`
    fn machine_return_array_label(&mut self, label: u32, range: TextRange) -> Stmt {
        let sentinel = self.number_expr("3 /*break*/");
        let target = self.number_expr(&label.to_string());
        let array = self.array_literal(vec![sentinel, target], range);
        self.machine_return(array, range)
    }
}
