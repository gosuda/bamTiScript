//! Unused local and parameter detection for `noUnusedLocals` and `noUnusedParameters`.
use std::collections::{HashMap, HashSet};

use crate::diagnostic::Diagnostic;
use crate::source::TextRange;
use crate::syntax::SourceFile;
use crate::syntax::{
    Accessibility, ArrayBindingElement, BindingPattern, ClassDeclaration, ClassMember,
    ExportDeclaration, ExportDefaultValue, ExportNamedDeclaration, Expression, ForBinding,
    ForInitializer, FunctionBody, FunctionLike, IdentifierNode, MemberProperty, NamespaceName,
    ParameterNode, Pattern, PropertyModifier, PropertyName, Statement, Stmt, VariableDeclaration,
};

use super::binder::{SemanticModel, SymbolId};
use super::unused_reads::{
    FileReads, binding_symbols, exported_local_names, file_reads, is_exported_name, is_symbol_read,
    unused_diagnostic, unused_elements_diagnostic, unused_variables_diagnostic,
};

#[derive(Debug, Default)]
pub(crate) struct UnusedDiagnostics {
    pub locals: Vec<Diagnostic>,
    pub params: Vec<Diagnostic>,
}

#[must_use]
pub(crate) fn unused_diagnostics(source: &SourceFile, model: &SemanticModel) -> UnusedDiagnostics {
    let mut outcome = UnusedDiagnostics::default();
    if source.source_text().is_declaration_file() {
        return outcome;
    }
    let mut walker = Walker {
        source,
        model,
        reads: file_reads(source, model),
        bindings: binding_symbols(model),
        exported: exported_local_names(source),
        marked: HashSet::new(),
        locals: Vec::new(),
        params: Vec::new(),
    };
    walker.walk_stmts(source.statements());
    outcome.locals = walker.locals;
    outcome.params = walker.params;
    outcome
}

struct Walker<'a> {
    source: &'a SourceFile,
    model: &'a SemanticModel,
    reads: FileReads,
    bindings: HashMap<(usize, usize), SymbolId>,
    exported: HashSet<String>,
    marked: HashSet<SymbolId>,
    locals: Vec<Diagnostic>,
    params: Vec<Diagnostic>,
}

impl Walker<'_> {
    fn walk_stmts(&mut self, statements: &[Stmt]) {
        for statement in statements {
            self.walk_stmt(statement);
        }
    }

    fn walk_stmt(&mut self, statement: &Stmt) {
        let range = statement.range();
        match statement.data() {
            Statement::Expression(inner) => self.walk_expr(&inner.expression),
            Statement::Variable(declaration) => self.walk_var_declaration(declaration, range),
            Statement::Function(function) => {
                self.walk_function_like(&function.function, range);
            }
            Statement::Class(class) => self.walk_class(class),
            Statement::Namespace(namespace) => self.walk_namespace(namespace, range),
            Statement::Enum(declaration) => self.walk_enum(declaration),
            Statement::Interface(_) | Statement::TypeAlias(_) => {}
            Statement::Import(_) | Statement::ImportEquals(_) => {}
            Statement::Export(export) => self.walk_export(export, range),
            Statement::Declare(_) => {}
            Statement::If(value) => {
                self.walk_expr(&value.test);
                self.walk_stmt(&value.consequent);
                if let Some(alternate) = value.alternate.as_deref() {
                    self.walk_stmt(alternate);
                }
            }
            Statement::Switch(value) => {
                self.walk_expr(&value.discriminant);
                for case in &value.cases {
                    if let Some(test) = case.data().test.as_deref() {
                        self.walk_expr(test);
                    }
                    self.walk_stmts(&case.data().consequent);
                }
            }
            Statement::For(value) => {
                match value.initializer.as_ref() {
                    Some(ForInitializer::Variable(declaration)) => {
                        self.walk_var_declaration(declaration, declaration.range);
                    }
                    Some(ForInitializer::Expression(expression)) => {
                        self.walk_expr(expression);
                    }
                    None => {}
                }
                if let Some(test) = value.test.as_deref() {
                    self.walk_expr(test);
                }
                if let Some(update) = value.update.as_deref() {
                    self.walk_expr(update);
                }
                self.walk_stmt(&value.body);
            }
            Statement::ForIn(value) => {
                self.walk_for_binding(&value.binding);
                self.walk_expr(&value.object);
                self.walk_stmt(&value.body);
            }
            Statement::ForOf(value) => {
                self.walk_for_binding(&value.binding);
                self.walk_expr(&value.iterable);
                self.walk_stmt(&value.body);
            }
            Statement::While(value) => {
                self.walk_expr(&value.test);
                self.walk_stmt(&value.body);
            }
            Statement::DoWhile(value) => {
                self.walk_stmt(&value.body);
                self.walk_expr(&value.test);
            }
            Statement::With(value) => {
                self.walk_expr(&value.object);
                self.walk_stmt(&value.body);
            }
            Statement::Try(value) => {
                self.walk_stmts(&value.block.data().statements);
                if let Some(handler) = value.handler.as_ref().map(|node| node.data()) {
                    self.walk_stmts(&handler.body.data().statements);
                }
                if let Some(finalizer) = value.finalizer.as_ref().map(|node| node.data()) {
                    self.walk_stmts(&finalizer.statements);
                }
            }
            Statement::Labeled(value) => self.walk_stmt(&value.body),
            Statement::Return(value) => {
                if let Some(argument) = value.argument.as_deref() {
                    self.walk_expr(argument);
                }
            }
            Statement::Throw(value) => self.walk_expr(&value.argument),
            Statement::Block(value) => self.walk_stmts(&value.data().statements),
            Statement::Debugger
            | Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Empty => {}
            Statement::Missing(_) => {}
        }
    }

    fn walk_var_declaration(&mut self, declaration: &VariableDeclaration, home: TextRange) {
        let mut reported = Vec::new();
        let mut all_dead = !declaration.declarations.is_empty();
        for declarator in &declaration.declarations {
            let data = declarator.data();
            let dead = match data.binding.data() {
                BindingPattern::Identifier(identifier) => {
                    if let Some((span, name)) = self.unused_binding(identifier, declarator.range())
                    {
                        reported.push(unused_diagnostic(self.source, span, &name));
                        true
                    } else {
                        false
                    }
                }
                _ => {
                    let (mut reports, dead) = self.check_pattern(&data.binding, declarator.range());
                    reported.append(&mut reports);
                    dead
                }
            };
            all_dead = all_dead && dead;
            self.walk_initializer(data.initializer.as_deref());
        }
        if declaration.declarations.len() > 1 && all_dead {
            self.locals
                .push(unused_variables_diagnostic(self.source, home));
        } else {
            self.locals.append(&mut reported);
        }
    }

    fn walk_for_binding(&mut self, binding: &ForBinding) {
        match binding {
            ForBinding::Variable(declaration) => {
                self.walk_var_declaration(declaration, declaration.range);
            }
            ForBinding::Target(_) => {}
        }
    }

    fn walk_function_like(&mut self, function: &FunctionLike, home: TextRange) {
        let Some(body) = function.body.as_ref() else {
            return;
        };
        if let Some(name) = function.name.as_ref()
            && let Some((span, text)) = self.unused_binding(name, home)
        {
            self.locals
                .push(unused_diagnostic(self.source, span, &text));
        }
        self.walk_params(&function.parameters);
        self.walk_function_body(body);
    }

    fn walk_params(&mut self, parameters: &[ParameterNode]) {
        for parameter in parameters {
            let data = parameter.data();
            for decorator in &data.decorators {
                self.walk_expr(&decorator.data().expression);
            }
            if data.modifiers.accessibility.is_some() {
                continue;
            }
            self.walk_initializer(data.initializer.as_deref());
            match data.binding.data() {
                BindingPattern::Identifier(identifier) => {
                    if self.is_this_ident(identifier) {
                        continue;
                    }
                    if let Some((span, text)) =
                        self.unused_exempt_binding(identifier, parameter.range())
                    {
                        self.params
                            .push(unused_diagnostic(self.source, span, &text));
                    }
                }
                _ => {
                    let (reports, _) = self.check_pattern(&data.binding, parameter.range());
                    self.params.extend(reports);
                }
            }
        }
    }

    fn walk_function_body(&mut self, body: &FunctionBody) {
        match body {
            FunctionBody::Block(block) => self.walk_stmts(&block.data().statements),
            FunctionBody::Expression(expression) => self.walk_expr(expression),
            FunctionBody::Missing(_) => {}
        }
    }

    fn walk_namespace(&mut self, namespace: &crate::syntax::NamespaceDeclaration, home: TextRange) {
        if let NamespaceName::Identifier { name, .. } = &namespace.name
            && let Some((span, text)) = self.unused_binding(name, home)
        {
            self.locals
                .push(unused_diagnostic(self.source, span, &text));
        }
        self.walk_stmts(&namespace.body.data().statements);
    }

    fn walk_enum(&mut self, declaration: &crate::syntax::EnumDeclaration) {
        for member in &declaration.members {
            self.walk_initializer(member.data().initializer.as_deref());
        }
    }

    fn walk_class(&mut self, class: &ClassDeclaration) {
        let mut getters = HashSet::new();
        for member in &class.members {
            if let ClassMember::Method(method) = member.data() {
                if !matches!(method.modifier, PropertyModifier::Get) {
                    continue;
                }
                match &method.name {
                    PropertyName::Identifier(name) => {
                        if let Some(text) = self.ident_text(name) {
                            getters.insert(text);
                        }
                    }
                    PropertyName::Private(name) => {
                        if let Some(text) = self.private_ident_text(name) {
                            getters.insert(text);
                        }
                    }
                    _ => {}
                }
            }
        }
        for decorator in &class.decorators {
            self.walk_expr(&decorator.data().expression);
        }
        if let Some(heritage) = class.extends.as_ref() {
            self.walk_expr(&heritage.expression);
        }
        for member in &class.members {
            self.walk_member(member.data(), member.range(), &getters);
        }
    }

    fn walk_member(&mut self, member: &ClassMember, home: TextRange, getters: &HashSet<String>) {
        match member {
            ClassMember::Constructor(constructor) => {
                for decorator in &constructor.decorators {
                    self.walk_expr(&decorator.data().expression);
                }
                self.walk_params(&constructor.parameters);
                self.walk_stmts(&constructor.body.data().statements);
            }
            ClassMember::Method(method) => {
                if method.modifiers.is_declare {
                    return;
                }
                self.walk_computed_name(&method.name);
                let Some(body) = method.function.body.as_ref() else {
                    return;
                };
                if matches!(method.modifiers.accessibility, Some(Accessibility::Private))
                    || matches!(method.name, PropertyName::Private(_))
                {
                    self.check_member_name(&method.name, &method.modifier, getters, home);
                }
                self.walk_params(&method.function.parameters);
                self.walk_function_body(body);
            }
            ClassMember::Property(property) => {
                if property.modifiers.is_declare || property.modifiers.is_abstract {
                    return;
                }
                for decorator in &property.decorators {
                    self.walk_expr(&decorator.data().expression);
                }
                self.walk_computed_name(&property.name);
                self.walk_initializer(property.initializer.as_deref());
                if matches!(
                    property.modifiers.accessibility,
                    Some(Accessibility::Private)
                ) || matches!(property.name, PropertyName::Private(_))
                {
                    self.check_private_name(&property.name, home);
                }
            }
            ClassMember::AutoAccessor(accessor) => {
                if accessor.modifiers.is_declare || accessor.modifiers.is_abstract {
                    return;
                }
                for decorator in &accessor.decorators {
                    self.walk_expr(&decorator.data().expression);
                }
                self.walk_computed_name(&accessor.name);
                self.walk_initializer(accessor.initializer.as_deref());
                if matches!(
                    accessor.modifiers.accessibility,
                    Some(Accessibility::Private)
                ) || matches!(accessor.name, PropertyName::Private(_))
                {
                    self.check_private_name(&accessor.name, home);
                }
            }
            ClassMember::StaticBlock(block) => self.walk_stmts(&block.data().statements),
            ClassMember::IndexSignature(_) | ClassMember::Missing(_) | ClassMember::Semicolon => {}
        }
    }

    fn check_member_name(
        &mut self,
        name: &PropertyName,
        modifier: &PropertyModifier,
        getters: &HashSet<String>,
        home: TextRange,
    ) {
        match name {
            PropertyName::Identifier(identifier) => {
                if matches!(modifier, PropertyModifier::Set)
                    && let Some(text) = self.ident_text(identifier)
                    && getters.contains(&text)
                {
                    return;
                }
                if let Some((span, text)) = self.unused_binding(identifier, home) {
                    self.locals
                        .push(unused_diagnostic(self.source, span, &text));
                }
            }
            PropertyName::Private(private) => {
                if matches!(modifier, PropertyModifier::Set)
                    && let Some(text) = self.private_ident_text(private)
                    && getters.contains(&text)
                {
                    return;
                }
                if let Some((span, text)) = self.unused_private_binding(private, home) {
                    self.locals
                        .push(unused_diagnostic(self.source, span, &text));
                }
            }
            _ => {}
        }
    }

    fn check_private_name(&mut self, name: &PropertyName, home: TextRange) {
        match name {
            PropertyName::Identifier(identifier) => {
                if let Some((span, text)) = self.unused_binding(identifier, home) {
                    self.locals
                        .push(unused_diagnostic(self.source, span, &text));
                }
            }
            PropertyName::Private(private) => {
                if let Some((span, text)) = self.unused_private_binding(private, home) {
                    self.locals
                        .push(unused_diagnostic(self.source, span, &text));
                }
            }
            _ => {}
        }
    }

    fn walk_export(&mut self, export: &ExportDeclaration, home: TextRange) {
        match export {
            ExportDeclaration::Named(inner) => match inner {
                ExportNamedDeclaration::Declaration(statement) => {
                    self.mark_exported_stmt(statement);
                    self.walk_stmt(statement);
                }
                ExportNamedDeclaration::Specifiers { .. } => {}
            },
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    if let Some(name) = function.name.as_ref() {
                        self.mark_ident(name);
                    }
                    self.walk_function_like(function, home);
                }
                ExportDefaultValue::Expression(expression) => {
                    self.walk_expr(expression);
                }
                ExportDefaultValue::Class(class) => {
                    self.walk_class(class);
                }
                ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => {}
            },
            ExportDeclaration::Assignment(expression) => {
                self.walk_expr(expression);
            }
            _ => {}
        }
    }

    fn mark_exported_stmt(&mut self, statement: &Stmt) {
        match statement.data() {
            Statement::Variable(declaration) => {
                for declarator in &declaration.declarations {
                    self.collect_pattern_symbols(&declarator.data().binding);
                }
            }
            Statement::Function(function) => {
                if let Some(name) = function.function.name.as_ref() {
                    self.mark_ident(name);
                }
            }
            Statement::Namespace(namespace) => {
                if let NamespaceName::Identifier { name, .. } = &namespace.name {
                    self.mark_ident(name);
                }
            }
            _ => {}
        }
    }

    fn collect_pattern_symbols(&mut self, pattern: &Pattern) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => self.mark_ident(identifier),
            BindingPattern::Object(object) => {
                for property in &object.properties {
                    self.collect_pattern_symbols(&property.binding);
                }
            }
            BindingPattern::Array(array) => {
                for element in &array.elements {
                    if let ArrayBindingElement::Binding(inner) = element {
                        self.collect_pattern_symbols(inner);
                    }
                }
            }
            BindingPattern::Rest(rest) => self.collect_pattern_symbols(&rest.argument),
            BindingPattern::Assignment(assignment) => {
                self.collect_pattern_symbols(&assignment.left);
            }
            BindingPattern::Missing(_) => {}
        }
    }

    fn mark_ident(&mut self, identifier: &IdentifierNode) {
        let key = (
            identifier.range().start().get(),
            identifier.range().end().get(),
        );
        if let Some(symbol) = self.bindings.get(&key).copied() {
            self.marked.insert(symbol);
        }
    }

    fn check_pattern(&mut self, pattern: &Pattern, home: TextRange) -> (Vec<Diagnostic>, bool) {
        match pattern.data() {
            BindingPattern::Identifier(identifier) => {
                self.check_single_identifier(identifier, pattern.range(), home)
            }
            BindingPattern::Object(object) => self.check_object_pattern(pattern, object, home),
            BindingPattern::Array(array) => self.check_array_pattern(pattern, array, home),
            BindingPattern::Rest(rest) => self.check_pattern(&rest.argument, home),
            BindingPattern::Assignment(assignment) => {
                self.walk_expr(&assignment.right);
                self.check_pattern(&assignment.left, home)
            }
            BindingPattern::Missing(_) => (Vec::new(), false),
        }
    }

    fn check_single_identifier(
        &mut self,
        identifier: &IdentifierNode,
        span: TextRange,
        home: TextRange,
    ) -> (Vec<Diagnostic>, bool) {
        let Some((_, name)) = self.unused_binding(identifier, home) else {
            return (Vec::new(), false);
        };
        if self.is_underscore_text(identifier) {
            return (Vec::new(), true);
        }
        (vec![unused_diagnostic(self.source, span, &name)], true)
    }

    fn check_object_pattern(
        &mut self,
        pattern: &Pattern,
        object: &crate::syntax::ObjectBindingPattern,
        home: TextRange,
    ) -> (Vec<Diagnostic>, bool) {
        let mut rest_present = false;
        for property in &object.properties {
            if matches!(property.binding.data(), BindingPattern::Rest(_)) {
                rest_present = true;
            }
        }
        if let [property] = object.properties.as_slice()
            && !rest_present
            && let BindingPattern::Identifier(identifier) = property.binding.data()
        {
            self.walk_computed_name(&property.name);
            self.walk_initializer(property.initializer.as_deref());
            return self.check_single_identifier(identifier, pattern.range(), home);
        }
        let mut reports = Vec::new();
        let mut all_dead = !object.properties.is_empty();
        for property in &object.properties {
            self.walk_computed_name(&property.name);
            self.walk_initializer(property.initializer.as_deref());
            let is_rest = matches!(property.binding.data(), BindingPattern::Rest(_));
            if rest_present && !is_rest {
                all_dead = false;
                continue;
            }
            if self.is_renamed_underscore(&property.name, &property.binding) {
                all_dead = false;
                continue;
            }
            match property.binding.data() {
                BindingPattern::Identifier(identifier) => {
                    let dead = self.check_identifier_element(identifier, home, &mut reports);
                    all_dead = all_dead && dead;
                }
                _ => {
                    let (mut inner_reports, dead) = self.check_pattern(&property.binding, home);
                    reports.append(&mut inner_reports);
                    all_dead = all_dead && dead;
                }
            }
        }
        if object.properties.len() >= 2 && all_dead {
            return (
                vec![unused_elements_diagnostic(self.source, pattern.range())],
                true,
            );
        }
        (reports, all_dead)
    }

    fn check_array_pattern(
        &mut self,
        pattern: &Pattern,
        array: &crate::syntax::ArrayBindingPattern,
        home: TextRange,
    ) -> (Vec<Diagnostic>, bool) {
        let mut bindings = Vec::new();
        for element in &array.elements {
            if let ArrayBindingElement::Binding(inner) = element {
                bindings.push(inner);
            }
        }
        if let [single] = bindings.as_slice()
            && let BindingPattern::Identifier(identifier) = single.data()
        {
            return self.check_single_identifier(identifier, pattern.range(), home);
        }
        let mut reports = Vec::new();
        let mut total = 0;
        let mut dead = 0;
        for inner in bindings {
            total += 1;
            match inner.data() {
                BindingPattern::Identifier(identifier) => {
                    if self.check_identifier_element(identifier, home, &mut reports) {
                        dead += 1;
                    }
                }
                _ => {
                    let (mut inner_reports, element_dead) = self.check_pattern(inner, home);
                    reports.append(&mut inner_reports);
                    if element_dead {
                        dead += 1;
                    }
                }
            }
        }
        if total >= 2 && dead == total {
            return (
                vec![unused_elements_diagnostic(self.source, pattern.range())],
                true,
            );
        }
        (reports, dead == total && total > 0)
    }

    fn check_identifier_element(
        &mut self,
        identifier: &IdentifierNode,
        home: TextRange,
        reports: &mut Vec<Diagnostic>,
    ) -> bool {
        let Some((span, name)) = self.unused_binding(identifier, home) else {
            return false;
        };
        if !self.is_underscore_text(identifier) {
            reports.push(unused_diagnostic(self.source, span, &name));
        }
        true
    }

    fn is_renamed_underscore(&self, name: &PropertyName, binding: &Pattern) -> bool {
        let PropertyName::Identifier(property) = name else {
            return false;
        };
        let BindingPattern::Identifier(identifier) = binding.data() else {
            return false;
        };
        let Some(property_text) = self.ident_text(property) else {
            return false;
        };
        let Some(binding_text) = self.ident_text(identifier) else {
            return false;
        };
        property_text != binding_text && binding_text.starts_with('_')
    }

    fn unused_binding(
        &self,
        identifier: &IdentifierNode,
        home: TextRange,
    ) -> Option<(TextRange, String)> {
        let key = (
            identifier.range().start().get(),
            identifier.range().end().get(),
        );
        let symbol = self.bindings.get(&key).copied()?;
        if self.marked.contains(&symbol) {
            return None;
        }
        let name = self.source.identifier_text(identifier.data().token())?;
        let name: &str = &name;
        if is_exported_name(self.model, &self.exported, name, symbol) {
            return None;
        }
        if is_symbol_read(&self.reads, symbol, home) {
            return None;
        }
        Some((identifier.range(), name.to_owned()))
    }

    fn unused_exempt_binding(
        &self,
        identifier: &IdentifierNode,
        home: TextRange,
    ) -> Option<(TextRange, String)> {
        if self.is_underscore_text(identifier) {
            return None;
        }
        self.unused_binding(identifier, home)
    }

    fn is_this_ident(&self, identifier: &IdentifierNode) -> bool {
        self.ident_text(identifier)
            .is_some_and(|text| text == "this")
    }

    fn is_underscore_text(&self, identifier: &IdentifierNode) -> bool {
        self.ident_text(identifier)
            .is_some_and(|text| text.starts_with('_'))
    }

    fn ident_text(&self, identifier: &IdentifierNode) -> Option<String> {
        self.source
            .identifier_text(identifier.data().token())
            .map(|name| name.into_owned())
    }

    fn private_ident_text(
        &self,
        identifier: &crate::syntax::PrivateIdentifierNode,
    ) -> Option<String> {
        self.source
            .token_text(identifier.data().token())
            .map(|name| name.to_owned())
    }

    fn unused_private_binding(
        &self,
        identifier: &crate::syntax::PrivateIdentifierNode,
        home: TextRange,
    ) -> Option<(TextRange, String)> {
        let key = (
            identifier.range().start().get(),
            identifier.range().end().get(),
        );
        let symbol = self.bindings.get(&key).copied()?;
        if self.marked.contains(&symbol) {
            return None;
        }
        let name = self
            .source
            .token_text(identifier.data().token())?
            .to_owned();
        if is_exported_name(self.model, &self.exported, &name, symbol) {
            return None;
        }
        if is_symbol_read(&self.reads, symbol, home) {
            return None;
        }
        Some((identifier.range(), name))
    }

    fn walk_computed_name(&mut self, name: &PropertyName) {
        if let PropertyName::Computed(key) = name {
            self.walk_expr(key);
        }
    }

    fn walk_initializer(&mut self, initializer: Option<&crate::syntax::Expr>) {
        if let Some(expression) = initializer {
            self.walk_expr(expression);
        }
    }

    fn walk_expr(&mut self, expression: &crate::syntax::Expr) {
        match expression.data() {
            Expression::Identifier(_)
            | Expression::Literal(_)
            | Expression::This
            | Expression::Super
            | Expression::Meta(_)
            | Expression::Missing(_) => {}
            Expression::NonNull(value) => self.walk_expr(&value.expression),
            Expression::Await(value) => self.walk_expr(&value.argument),
            Expression::Yield(value) => {
                if let Some(argument) = value.argument.as_deref() {
                    self.walk_expr(argument);
                }
            }
            Expression::Unary(value) => self.walk_expr(&value.argument),
            Expression::Update(_) => {}
            Expression::Binary(value) => {
                self.walk_expr(&value.left);
                self.walk_expr(&value.right);
            }
            Expression::Logical(value) => {
                self.walk_expr(&value.left);
                self.walk_expr(&value.right);
            }
            Expression::Conditional(value) => {
                self.walk_expr(&value.test);
                self.walk_expr(&value.consequent);
                self.walk_expr(&value.alternate);
            }
            Expression::Sequence(value) => {
                for inner in &value.expressions {
                    self.walk_expr(inner);
                }
            }
            Expression::Parenthesized(inner) => self.walk_expr(inner),
            Expression::As(value) => self.walk_expr(&value.expression),
            Expression::Satisfies(value) => self.walk_expr(&value.expression),
            Expression::TypeAssertion(value) => self.walk_expr(&value.expression),
            Expression::Assignment(assignment) => {
                self.walk_expr(&assignment.right);
            }
            Expression::Call(value) => {
                self.walk_expr(&value.callee);
                self.walk_call_arguments(&value.arguments);
            }
            Expression::New(value) => {
                self.walk_expr(&value.callee);
                self.walk_call_arguments(&value.arguments);
            }
            Expression::Member(value) => {
                self.walk_expr(&value.object);
                if let MemberProperty::Computed(key) = &value.property {
                    self.walk_expr(key);
                }
            }
            Expression::Array(value) => {
                for element in &value.elements {
                    match element {
                        crate::syntax::ArrayElement::Expression(inner) => {
                            self.walk_expr(inner);
                        }
                        crate::syntax::ArrayElement::Spread(spread) => {
                            self.walk_expr(&spread.argument);
                        }
                        crate::syntax::ArrayElement::Elision
                        | crate::syntax::ArrayElement::Missing(_) => {}
                    }
                }
            }
            Expression::Object(value) => {
                for member in &value.members {
                    match member.data() {
                        crate::syntax::ObjectMember::Property(property) => {
                            self.walk_computed_name(&property.name);
                            self.walk_expr(&property.value);
                        }
                        crate::syntax::ObjectMember::Method(method) => {
                            self.walk_function_like(&method.function, member.range());
                        }
                        crate::syntax::ObjectMember::Spread(spread) => {
                            self.walk_expr(&spread.argument);
                        }
                        crate::syntax::ObjectMember::Missing(_) => {}
                    }
                }
            }
            Expression::Function(value) => {
                self.walk_function_like(&value.function, expression.range());
            }
            Expression::Class(value) => {
                self.walk_class(&value.class);
            }
            Expression::Arrow(value) => {
                self.walk_params(&value.parameters);
                self.walk_function_body(&value.body);
            }
            Expression::Template(value) => {
                for inner in &value.expressions {
                    self.walk_expr(inner);
                }
            }
            Expression::TaggedTemplate(value) => {
                self.walk_expr(&value.tag);
                for inner in &value.template.expressions {
                    self.walk_expr(inner);
                }
            }
            Expression::Import(value) => {
                self.walk_expr(&value.source);
                if let Some(options) = value.options.as_deref() {
                    self.walk_expr(options);
                }
            }
            Expression::JsxElement(value) => {
                for attribute in &value.opening.data().attributes {
                    self.walk_jsx_attribute(attribute);
                }
                self.walk_jsx_children(&value.children);
            }
            Expression::JsxFragment(value) => self.walk_jsx_children(&value.children),
            Expression::JsxSelfClosingElement(value) => {
                for attribute in &value.attributes {
                    self.walk_jsx_attribute(attribute);
                }
            }
        }
    }

    fn walk_call_arguments(&mut self, arguments: &[crate::syntax::CallArgument]) {
        for argument in arguments {
            match argument {
                crate::syntax::CallArgument::Expression(inner) => {
                    self.walk_expr(inner);
                }
                crate::syntax::CallArgument::Spread(spread) => {
                    self.walk_expr(&spread.argument);
                }
                crate::syntax::CallArgument::Missing(_) => {}
            }
        }
    }

    fn walk_jsx_children(&mut self, children: &[crate::syntax::JsxChild]) {
        for child in children {
            match child {
                crate::syntax::JsxChild::ExpressionContainer(container) => {
                    if let Some(expression) = container.data().expression.as_deref() {
                        self.walk_expr(expression);
                    }
                }
                crate::syntax::JsxChild::Spread(spread) => {
                    self.walk_expr(&spread.data().expression);
                }
                crate::syntax::JsxChild::Element(expression) => {
                    self.walk_expr(expression);
                }
                crate::syntax::JsxChild::Text(_) => {}
            }
        }
    }

    fn walk_jsx_attribute(&mut self, attribute: &crate::syntax::JsxAttributeItem) {
        match attribute {
            crate::syntax::JsxAttributeItem::Attribute(inner) => {
                if let Some(crate::syntax::JsxAttributeInitializer::Expression(container)) =
                    inner.data().initializer.as_ref()
                    && let Some(expression) = container.data().expression.as_deref()
                {
                    self.walk_expr(expression);
                }
            }
            crate::syntax::JsxAttributeItem::Spread(spread) => {
                self.walk_expr(&spread.data().expression);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::checker::binder::bind_source;
    use crate::source::{SourceId, SourceText};

    fn check(text: &str) -> UnusedDiagnostics {
        let source_text = Arc::new(SourceText::new(text).expect("test source fits the budget"));
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            crate::source::ScriptKind::TypeScript,
            source_text,
        ));
        let file = parsed.product();
        let (model, _) = bind_source(file);
        unused_diagnostics(file, &model)
    }

    fn messages(diagnostics: &[Diagnostic]) -> Vec<String> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message().to_owned())
            .collect()
    }
    fn codes(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    #[test]
    fn write_only_variable_is_reported() {
        let outcome = check("function f() { var x = 0; x = 1; return 0; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn used_before_unused_parameter_pair_reports_only_the_unused_one() {
        let outcome = check("function g(used, unused) { return used; }");
        assert_eq!(outcome.params.len(), 1, "{outcome:?}");
        assert_eq!(
            outcome.params[0].message(),
            "'unused' is declared but its value is never read."
        );
        assert_eq!(outcome.locals.len(), 1, "{outcome:?}");
    }

    #[test]
    fn underscore_prefixed_parameter_is_exempt() {
        let outcome = check("function h(_a, b) { return b; }");
        assert!(outcome.params.is_empty(), "{outcome:?}");
        assert_eq!(outcome.locals.len(), 1, "{outcome:?}");
    }

    #[test]
    fn all_unused_destructured_elements_report_once() {
        let outcome = check("function k() { const {a, b} = {a: 1, b: 2}; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"All destructured elements are unused.".to_owned()));
    }

    #[test]
    fn all_unused_declarators_report_once() {
        let outcome = check("function m() { var x = 1, y = 2; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"All variables are unused.".to_owned()));
    }
    #[test]
    fn rest_reports_only_rest_binding() {
        let outcome = check("function three() { const foo = { a: 1, b: 2 }; const { a, ...bar } = foo; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'three' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'bar' is declared but its value is never read.".to_owned()));
        assert!(!texts.iter().any(|m| m.contains("destructured")), "{outcome:?}");
    }

    #[test]
    fn hash_private_unused_reports() {
        let outcome = check("class C { #x = 1; }");
        assert_eq!(outcome.locals.len(), 1, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'#x' is declared but its value is never read."
        );
    }

    #[test]
    fn hash_private_used_is_clean() {
        let outcome = check("class C { #x = 1; m() { return this.#x; } } export const c = new C();");
        assert_eq!(codes(&outcome.locals), Vec::<&str>::new(), "{outcome:?}");
        assert_eq!(codes(&outcome.params), Vec::<&str>::new(), "{outcome:?}");
    }

    #[test]
    fn declaration_file_locals_are_clean() {
        let source_text = Arc::new(SourceText::new("const x = 1;\n").expect("test source fits the budget").with_declaration_file(true));
        let parsed = crate::parser::parse(crate::scanner::scan(
            SourceId::new(0),
            crate::source::ScriptKind::TypeScript,
            source_text,
        ));
        let file = parsed.product();
        let (model, _) = bind_source(file);
        let outcome = unused_diagnostics(file, &model);
        assert_eq!(codes(&outcome.locals), Vec::<&str>::new(), "{outcome:?}");
        assert_eq!(codes(&outcome.params), Vec::<&str>::new(), "{outcome:?}");
    }

    #[test]
    fn exported_local_is_clean() {
        let outcome = check("export const x = 1;");
        assert_eq!(codes(&outcome.locals), Vec::<&str>::new(), "{outcome:?}");
        assert_eq!(codes(&outcome.params), Vec::<&str>::new(), "{outcome:?}");
    }

    #[test]
    fn partial_object_pattern_reports_only_unused() {
        let outcome = check("function f() { const o = { a: 1, b: 2 }; const { a, b } = o; return a; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'b' is declared but its value is never read.".to_owned()));
        assert!(!texts.iter().any(|m| m.contains("'a'")), "{outcome:?}");
    }

    #[test]
    fn partial_array_pattern_reports_only_unused() {
        let outcome = check("function f() { const [a, b] = [1, 2]; return a; }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'b' is declared but its value is never read.".to_owned()));
        assert!(!texts.iter().any(|m| m.contains("destructured")), "{outcome:?}");
    }

    #[test]
    fn for_of_unused_binding_reports() {
        let outcome = check("function f() { const arr = [1]; for (const x of arr) { } }");
        assert_eq!(outcome.locals.len(), 2, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
    }

    #[test]
    fn compound_assignment_counts_as_read() {
        let outcome = check("function f() { var x = 0; x += 1; return 1; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn update_counts_as_read() {
        let outcome = check("function f() { var x = 0; x++; return 1; }");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'f' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn destructuring_assignment_target_is_write_only() {
        let outcome = check("function f() { var x = 0; [x] = [1]; return 0; }");
        assert_eq!(codes(&outcome.locals), ["6133", "6133"], "{outcome:?}");
        let texts = messages(&outcome.locals);
        assert!(texts.contains(&"'f' is declared but its value is never read.".to_owned()));
        assert!(texts.contains(&"'x' is declared but its value is never read.".to_owned()));
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }
    #[test]
    fn auto_accessor_initializer_read_keeps_seed_clean() {
        let outcome = check("const seed = 1; class C { accessor x = seed; }");
        assert!(outcome.locals.is_empty(), "{outcome:?}");
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn auto_accessor_initializer_nested_body_reports_unused() {
        let outcome = check("class C { accessor p = () => { var z = 1; }; }");
        assert_eq!(outcome.locals.len(), 1, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'z' is declared but its value is never read."
        );
        assert!(outcome.params.is_empty(), "{outcome:?}");
    }

    #[test]
    fn private_getter_setter_pair_reports_getter_only() {
        let outcome = check("class C { get #x() { return 1; } set #x(v: number) {} }");
        assert_eq!(outcome.locals.len(), 1, "{outcome:?}");
        assert_eq!(codes(&outcome.locals), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.locals[0].message(),
            "'#x' is declared but its value is never read."
        );
        assert_eq!(outcome.params.len(), 1, "{outcome:?}");
        assert_eq!(codes(&outcome.params), ["6133"], "{outcome:?}");
        assert_eq!(
            outcome.params[0].message(),
            "'v' is declared but its value is never read."
        );
    }
    #[test]
    fn unused_catch_binding_is_clean() {
        let outcome = check("try {} catch (e) {}");
        assert_eq!(codes(&outcome.locals), Vec::<&str>::new(), "{outcome:?}");
        assert_eq!(codes(&outcome.params), Vec::<&str>::new(), "{outcome:?}");
    }

    #[test]
    fn used_catch_binding_is_clean() {
        let outcome = check("try {} catch (e) { throw e; }");
        assert_eq!(codes(&outcome.locals), Vec::<&str>::new(), "{outcome:?}");
        assert_eq!(codes(&outcome.params), Vec::<&str>::new(), "{outcome:?}");
    }

}
