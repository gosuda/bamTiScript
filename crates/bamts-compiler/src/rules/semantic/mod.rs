use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    checker::{
        AnalysisFacts, HazardFact, ProgramSemanticModel, ResolvedModuleEdge, SemanticHazard,
        SemanticModel, SymbolKind, is_numeric_enum_initializer, relations::TypeRelations,
    },
    diagnostic::{Diagnostic, Recovered},
    lint::{LintTable, SourceDialect, rule_by_code},
    source::{SourceId, TextRange},
    syntax::*,
};

mod coercions;
mod control_flow;
mod enums;
mod flow_safety;
mod functions;
mod intrinsics;
mod members;
mod modules;
mod object_types;

pub(crate) struct SemanticRuleContext<'a> {
    source: &'a SourceFile,
    model: &'a SemanticModel,
    levels: &'a LintTable,
    dialect: SourceDialect,
}

impl<'a> SemanticRuleContext<'a> {
    fn diagnostic(
        &self,
        code: &'static str,
        range: TextRange,
        message: &'static str,
    ) -> Option<Diagnostic> {
        let rule = rule_by_code(code).expect("semantic rule code must be registered");
        Diagnostic::lint(
            self.levels.level_for_source(rule.id(), self.dialect),
            rule.id(),
            self.source.source_id(),
            range,
            message,
        )
    }
}

pub(crate) fn analyze(
    source: &SourceFile,
    model: &SemanticModel,
    _program: Option<&ProgramSemanticModel>,
    levels: &LintTable,
) -> Vec<Diagnostic> {
    let dialect = match source.script_kind() {
        crate::source::ScriptKind::JavaScript | crate::source::ScriptKind::JavaScriptReact => {
            SourceDialect::JavaScript
        }
        _ => SourceDialect::TypeScript,
    };
    let context = SemanticRuleContext {
        source,
        model,
        levels,
        dialect,
    };
    let mut diagnostics = Vec::new();
    object_types::analyze(&context, &mut diagnostics);
    functions::analyze(&context, &mut diagnostics);
    flow_safety::analyze(&context, &mut diagnostics);
    modules::analyze(&context, &mut diagnostics);
    members::analyze(&context, &mut diagnostics);
    enums::analyze(&context, &mut diagnostics);
    control_flow::analyze(&context, &mut diagnostics);
    intrinsics::analyze(&context, &mut diagnostics);
    coercions::analyze(&context, &mut diagnostics);
    diagnostics.sort();
    diagnostics
}

pub(crate) fn emit(
    context: &SemanticRuleContext<'_>,
    diagnostics: &mut Vec<Diagnostic>,
    hazard: SemanticHazard,
    code: &'static str,
    message: &'static str,
    help: &'static str,
) {
    for fact in context
        .model
        .facts()
        .hazards()
        .iter()
        .filter(|fact| fact.hazard == hazard)
    {
        if let Some(mut diagnostic) = context.diagnostic(code, fact.range, message) {
            if let Some(note) = &fact.note {
                diagnostic = diagnostic.with_note(note.to_string());
            }
            diagnostics.push(diagnostic.with_help(help));
        }
    }
}

/// Builds immutable checker evidence from parsed nodes and resolved symbols.
pub(crate) fn collect_facts(source: &SourceFile, model: &SemanticModel) -> AnalysisFacts {
    let mut collector = AstFactCollector::new(source, model);
    collector.index_declarations(source.statements());
    collector.collect_called_names(source.statements());
    collector.visit_statements(source.statements());
    collector.finish()
}

#[derive(Clone)]
struct ClassFacts {
    base: Option<String>,
    accessors: HashSet<String>,
    methods: HashSet<String>,
}

struct AstFactCollector<'a> {
    source: &'a SourceFile,
    model: &'a SemanticModel,
    facts: AnalysisFacts,
    index_signature_types: HashSet<String>,
    numeric_enums: HashSet<String>,
    variable_types: HashMap<String, String>,
    readonly_aliases: HashSet<String>,
    called_names: HashSet<String>,
    safe_json_parses: HashSet<TextRange>,
    sorted_object_keys: HashSet<TextRange>,
    classes: HashMap<String, ClassFacts>,
    union_variants: HashMap<String, usize>,
}

impl<'a> AstFactCollector<'a> {
    fn new(source: &'a SourceFile, model: &'a SemanticModel) -> Self {
        Self {
            source,
            model,
            facts: AnalysisFacts::default(),
            index_signature_types: HashSet::new(),
            numeric_enums: HashSet::new(),
            variable_types: HashMap::new(),
            readonly_aliases: HashSet::new(),
            called_names: HashSet::new(),
            safe_json_parses: HashSet::new(),
            sorted_object_keys: HashSet::new(),
            classes: HashMap::new(),
            union_variants: HashMap::new(),
        }
    }

    fn finish(self) -> AnalysisFacts {
        self.facts
    }

    fn push(&mut self, hazard: SemanticHazard, range: TextRange) {
        self.facts.push(HazardFact {
            hazard,
            range,
            note: None,
        });
    }

    fn identifier(&self, identifier: &IdentifierNode) -> Cow<'_, str> {
        self.source
            .identifier_text(identifier.data().token())
            .unwrap_or_default()
    }

    fn property_name(&self, name: &PropertyName) -> Option<String> {
        match name {
            PropertyName::Identifier(identifier) => Some(self.identifier(identifier).into_owned()),
            PropertyName::Private(identifier) => self
                .source
                .token_text(identifier.data().token())
                .map(ToOwned::to_owned),
            PropertyName::String(string) => Some(
                self.source
                    .token_text(string.data().token())
                    .unwrap_or("")
                    .trim_matches(['\"', '\''])
                    .to_owned(),
            ),
            PropertyName::Number(number) => self
                .source
                .token_text(number.data().token())
                .map(ToOwned::to_owned),
            PropertyName::Computed(_) | PropertyName::Missing(_) => None,
        }
    }

    fn reference_type_name(&self, ty: &Ty) -> Option<String> {
        let TypeNode::Reference(reference) = ty.data() else {
            return None;
        };
        let EntityName::Identifier(identifier) = &reference.name else {
            return None;
        };
        Some(self.identifier(identifier).into_owned())
    }

    fn annotation_type_name(&self, annotation: &TypeAnnotationNode) -> Option<String> {
        match annotation.data().type_node.data() {
            TypeNode::Keyword(KeywordType::Number) => Some("number".to_owned()),
            _ => self.reference_type_name(&annotation.data().type_node),
        }
    }

    fn type_contains_undefined(ty: &Ty) -> bool {
        match ty.data() {
            TypeNode::Keyword(KeywordType::Any | KeywordType::Unknown | KeywordType::Undefined) => {
                true
            }
            TypeNode::Union(members) => members.iter().any(Self::type_contains_undefined),
            TypeNode::Parenthesized(inner) => Self::type_contains_undefined(inner),
            _ => false,
        }
    }

    fn type_is_readonly(ty: &Ty) -> bool {
        match ty.data() {
            TypeNode::Operator {
                operator: TypeOperator::Readonly,
                ..
            } => true,
            TypeNode::Object(object) => object.members.iter().any(|member| {
                matches!(
                    member.data(),
                    TypeMember::Property(TypePropertySignature { readonly: true, .. })
                        | TypeMember::Index(TypeIndexSignature { readonly: true, .. })
                )
            }),
            TypeNode::Parenthesized(inner) => Self::type_is_readonly(inner),
            _ => false,
        }
    }

    fn type_is_keyof_array(ty: &Ty) -> bool {
        match ty.data() {
            TypeNode::Array(element) => Self::type_is_keyof(element),
            TypeNode::Parenthesized(inner) => Self::type_is_keyof_array(inner),
            _ => false,
        }
    }

    fn type_is_keyof(ty: &Ty) -> bool {
        match ty.data() {
            TypeNode::Operator {
                operator: TypeOperator::Keyof,
                ..
            } => true,
            TypeNode::Parenthesized(inner) => Self::type_is_keyof(inner),
            _ => false,
        }
    }

    fn has_explicit_undefined_optional(&self, annotation: &Ty, initializer: &Expr) -> bool {
        let (TypeNode::Object(object_type), Expression::Object(object)) =
            (annotation.data(), initializer.data())
        else {
            return false;
        };
        object_type.members.iter().any(|member| {
            let TypeMember::Property(property) = member.data() else {
                return false;
            };
            if !property.optional
                || property.type_annotation.as_ref().is_some_and(|annotation| {
                    Self::type_contains_undefined(&annotation.data().type_node)
                })
            {
                return false;
            }
            let Some(expected_name) = self.property_name(&property.name) else {
                return false;
            };
            object.members.iter().any(|member| {
                let ObjectMember::Property(actual) = member.data() else {
                    return false;
                };
                self.property_name(&actual.name).as_deref() == Some(expected_name.as_str())
                    && self.is_global_identifier(&actual.value, "undefined")
            })
        })
    }

    fn is_global_identifier(&self, expression: &Expr, expected: &str) -> bool {
        let Expression::Identifier(identifier) = expression.data() else {
            return false;
        };
        if self.identifier(identifier) != expected {
            return false;
        }
        self.model
            .reference(identifier.id())
            .is_some_and(|symbol| self.model.symbol(symbol).kind() == SymbolKind::IntrinsicValue)
    }

    fn member_name(&self, member: &MemberExpression) -> Option<String> {
        match &member.property {
            MemberProperty::Named(identifier) => Some(self.identifier(identifier).into_owned()),
            _ => None,
        }
    }

    fn index_declarations(&mut self, statements: &[Stmt]) {
        for statement in statements {
            let statement = match statement.data() {
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(inner),
                )) => inner.data(),
                other => other,
            };
            if let Statement::Export(ExportDeclaration::Default(default)) = statement {
                if let ExportDefaultValue::Interface(interface) = &default.value
                    && interface
                        .members
                        .iter()
                        .any(|member| matches!(member.data(), TypeMember::Index(_)))
                {
                    self.index_signature_types
                        .insert(self.identifier(&interface.name).into_owned());
                }
                continue;
            }

            match statement {
                Statement::Interface(interface) => {
                    if interface
                        .members
                        .iter()
                        .any(|member| matches!(member.data(), TypeMember::Index(_)))
                    {
                        self.index_signature_types
                            .insert(self.identifier(&interface.name).into_owned());
                    }
                }
                Statement::TypeAlias(alias) => {
                    if let TypeNode::Union(members) = alias.type_node.data() {
                        self.union_variants
                            .insert(self.identifier(&alias.name).into_owned(), members.len());
                    }
                }
                Statement::Enum(enumeration) => {
                    if enumeration.members.iter().all(|member| {
                        member
                            .data()
                            .initializer
                            .as_deref()
                            .is_none_or(is_numeric_enum_initializer)
                    }) {
                        self.numeric_enums
                            .insert(self.identifier(&enumeration.name).into_owned());
                    }
                }
                Statement::Class(class) => {
                    let Some(name) = class
                        .name
                        .as_ref()
                        .map(|name| self.identifier(name).into_owned())
                    else {
                        continue;
                    };
                    let base = class.extends.as_ref().and_then(|heritage| {
                        let Expression::Identifier(identifier) = heritage.expression.data() else {
                            return None;
                        };
                        Some(self.identifier(identifier).into_owned())
                    });
                    let mut accessors = HashSet::new();
                    let mut methods = HashSet::new();
                    for member in &class.members {
                        if let ClassMember::Method(method) = member.data()
                            && let Some(member_name) = self.property_name(&method.name)
                        {
                            methods.insert(member_name.clone());
                            if matches!(
                                method.modifier,
                                PropertyModifier::Get | PropertyModifier::Set
                            ) {
                                accessors.insert(member_name);
                            }
                        }
                    }
                    self.classes.insert(
                        name,
                        ClassFacts {
                            base,
                            accessors,
                            methods,
                        },
                    );
                }
                _ => {}
            }
        }
    }

    fn collect_called_names(&mut self, statements: &[Stmt]) {
        for statement in statements {
            self.collect_calls_statement(statement);
        }
    }

    fn collect_calls_statement(&mut self, statement: &Stmt) {
        match statement.data() {
            Statement::Variable(variable) => {
                for declaration in &variable.declarations {
                    if let Some(initializer) = &declaration.data().initializer {
                        self.collect_calls_expr(initializer);
                    }
                }
            }
            Statement::Expression(statement) => self.collect_calls_expr(&statement.expression),
            Statement::Block(block) => self.collect_called_names(&block.data().statements),
            Statement::Function(function) => {
                self.collect_calls_body(function.function.body.as_ref())
            }
            Statement::Class(class) => self.collect_calls_class(class),
            Statement::If(branch) => {
                self.collect_calls_expr(&branch.test);
                self.collect_calls_statement(&branch.consequent);
                if let Some(alternate) = &branch.alternate {
                    self.collect_calls_statement(alternate);
                }
            }
            Statement::Return(statement) => {
                if let Some(argument) = &statement.argument {
                    self.collect_calls_expr(argument);
                }
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            )))
            | Statement::Declare(inner) => self.collect_calls_statement(inner),
            Statement::Export(ExportDeclaration::Default(default)) => match &default.value {
                ExportDefaultValue::Function(function) => {
                    self.collect_calls_body(function.body.as_ref())
                }
                ExportDefaultValue::Class(class) => self.collect_calls_class(class),
                ExportDefaultValue::Expression(expression) => self.collect_calls_expr(expression),
                ExportDefaultValue::Interface(_) | ExportDefaultValue::Missing(_) => {}
            },
            Statement::Export(ExportDeclaration::Assignment(expression)) => {
                self.collect_calls_expr(expression)
            }
            Statement::Namespace(namespace) => {
                self.collect_called_names(&namespace.body.data().statements)
            }
            Statement::Switch(switch) => {
                self.collect_calls_expr(&switch.discriminant);
                for case in &switch.cases {
                    if let Some(test) = &case.data().test {
                        self.collect_calls_expr(test);
                    }
                    self.collect_called_names(&case.data().consequent);
                }
            }
            Statement::For(statement) => {
                if let Some(initializer) = &statement.initializer {
                    match initializer {
                        ForInitializer::Variable(variable) => {
                            for declaration in &variable.declarations {
                                if let Some(initializer) = &declaration.data().initializer {
                                    self.collect_calls_expr(initializer);
                                }
                            }
                        }
                        ForInitializer::Expression(expression) => {
                            self.collect_calls_expr(expression)
                        }
                    }
                }
                if let Some(test) = &statement.test {
                    self.collect_calls_expr(test);
                }
                if let Some(update) = &statement.update {
                    self.collect_calls_expr(update);
                }
                self.collect_calls_statement(&statement.body);
            }
            Statement::ForIn(statement) => {
                self.collect_calls_expr(&statement.object);
                self.collect_calls_statement(&statement.body);
            }
            Statement::ForOf(statement) => {
                self.collect_calls_expr(&statement.iterable);
                self.collect_calls_statement(&statement.body);
            }
            Statement::While(statement) => {
                self.collect_calls_expr(&statement.test);
                self.collect_calls_statement(&statement.body);
            }
            Statement::DoWhile(statement) => {
                self.collect_calls_statement(&statement.body);
                self.collect_calls_expr(&statement.test);
            }
            Statement::Try(statement) => {
                self.collect_called_names(&statement.block.data().statements);
                if let Some(handler) = &statement.handler {
                    self.collect_called_names(&handler.data().body.data().statements);
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.collect_called_names(&finalizer.data().statements);
                }
            }
            Statement::With(statement) => {
                self.collect_calls_expr(&statement.object);
                self.collect_calls_statement(&statement.body);
            }
            Statement::Labeled(statement) => self.collect_calls_statement(&statement.body),
            Statement::Throw(statement) => self.collect_calls_expr(&statement.argument),
            Statement::Enum(enumeration) => {
                for member in &enumeration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.collect_calls_expr(initializer);
                    }
                }
            }
            Statement::Import(_)
            | Statement::ImportEquals(_)
            | Statement::Export(ExportDeclaration::All(_))
            | Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Specifiers {
                ..
            }))
            | Statement::Interface(_)
            | Statement::TypeAlias(_)
            | Statement::Empty
            | Statement::Break(_)
            | Statement::Continue(_)
            | Statement::Debugger
            | Statement::Missing(_) => {}
        }
    }

    fn collect_calls_class(&mut self, class: &ClassDeclaration) {
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(constructor) => {
                    self.collect_called_names(&constructor.body.data().statements)
                }
                ClassMember::Method(method) => {
                    self.collect_calls_body(method.function.body.as_ref())
                }
                ClassMember::Property(property) => {
                    if let Some(initializer) = &property.initializer {
                        self.collect_calls_expr(initializer);
                    }
                }
                ClassMember::AutoAccessor(accessor) => {
                    if let Some(initializer) = &accessor.initializer {
                        self.collect_calls_expr(initializer);
                    }
                }
                ClassMember::StaticBlock(block) => {
                    self.collect_called_names(&block.data().statements)
                }
                _ => {}
            }
        }
    }

    fn collect_calls_body(&mut self, body: Option<&FunctionBody>) {
        match body {
            Some(FunctionBody::Block(block)) => self.collect_called_names(&block.data().statements),
            Some(FunctionBody::Expression(expression)) => self.collect_calls_expr(expression),
            _ => {}
        }
    }

    fn collect_calls_expr(&mut self, expression: &Expr) {
        match expression.data() {
            Expression::Call(call) => {
                if let Expression::Identifier(identifier) = call.callee.data() {
                    self.called_names
                        .insert(self.identifier(identifier).into_owned());
                }
                if let Expression::Member(member) = call.callee.data()
                    && self.member_name(member).as_deref() == Some("sort")
                    && let Expression::Call(inner) = member.object.data()
                    && self.is_object_keys_call(inner)
                {
                    self.sorted_object_keys.insert(member.object.range());
                }
                self.collect_calls_expr(&call.callee);
                for argument in &call.arguments {
                    if let CallArgument::Expression(argument) = argument {
                        self.collect_calls_expr(argument);
                    }
                }
            }
            Expression::Member(member) => self.collect_calls_expr(&member.object),
            Expression::Parenthesized(inner)
            | Expression::NonNull(NonNullExpression { expression: inner }) => {
                self.collect_calls_expr(inner)
            }
            Expression::Binary(binary) => {
                self.collect_calls_expr(&binary.left);
                self.collect_calls_expr(&binary.right);
            }
            Expression::Arrow(arrow) => self.collect_calls_body(Some(&arrow.body)),
            Expression::Function(function) => {
                self.collect_calls_body(function.function.body.as_ref())
            }
            _ => {}
        }
    }

    fn visit_statements(&mut self, statements: &[Stmt]) {
        for statement in statements {
            self.visit_statement(statement, false);
        }
    }

    fn visit_statement(&mut self, statement: &Stmt, in_constructor: bool) {
        match statement.data() {
            Statement::Variable(variable) => self.visit_variable(variable),
            Statement::Function(function) => self.visit_function(&function.function),
            Statement::Class(class) => self.visit_class(class),
            Statement::Block(block) => self.visit_statements(&block.data().statements),
            Statement::Expression(statement) => {
                self.visit_expr(&statement.expression, in_constructor)
            }
            Statement::If(branch) => {
                self.visit_expr(&branch.test, in_constructor);
                self.visit_statement(&branch.consequent, in_constructor);
                if let Some(alternate) = &branch.alternate {
                    self.visit_statement(alternate, in_constructor);
                }
            }
            Statement::Switch(switch) => {
                self.visit_switch(statement.range(), switch);
                self.visit_expr(&switch.discriminant, in_constructor);
                for case in &switch.cases {
                    if let Some(test) = &case.data().test {
                        self.visit_expr(test, in_constructor);
                    }
                    self.visit_statements(&case.data().consequent);
                }
            }
            Statement::For(statement) => {
                if let Some(initializer) = &statement.initializer {
                    match initializer {
                        ForInitializer::Variable(variable) => self.visit_variable(variable),
                        ForInitializer::Expression(expression) => {
                            self.visit_expr(expression, in_constructor)
                        }
                    }
                }
                if let Some(test) = &statement.test {
                    self.visit_expr(test, in_constructor);
                }
                if let Some(update) = &statement.update {
                    self.visit_expr(update, in_constructor);
                }
                self.visit_statement(&statement.body, in_constructor);
            }
            Statement::ForIn(statement) => {
                if let ForBinding::Variable(variable) = &statement.binding {
                    self.visit_variable(variable);
                }
                self.visit_expr(&statement.object, in_constructor);
                self.visit_statement(&statement.body, in_constructor);
            }
            Statement::ForOf(statement) => {
                if let ForBinding::Variable(variable) = &statement.binding {
                    self.visit_variable(variable);
                }
                self.visit_expr(&statement.iterable, in_constructor);
                self.visit_statement(&statement.body, in_constructor);
            }
            Statement::While(statement) => {
                self.visit_expr(&statement.test, in_constructor);
                self.visit_statement(&statement.body, in_constructor);
            }
            Statement::DoWhile(statement) => {
                self.visit_statement(&statement.body, in_constructor);
                self.visit_expr(&statement.test, in_constructor);
            }
            Statement::With(statement) => {
                self.visit_expr(&statement.object, in_constructor);
                self.visit_statement(&statement.body, in_constructor);
            }
            Statement::Labeled(statement) => self.visit_statement(&statement.body, in_constructor),
            Statement::Return(statement) => {
                if let Some(argument) = &statement.argument {
                    self.visit_expr(argument, in_constructor);
                }
            }
            Statement::Throw(statement) => self.visit_expr(&statement.argument, in_constructor),
            Statement::Enum(enumeration) => {
                for member in &enumeration.members {
                    if let Some(initializer) = &member.data().initializer {
                        self.visit_expr(initializer, in_constructor);
                    }
                }
            }
            Statement::Export(ExportDeclaration::Default(export)) => match &export.value {
                ExportDefaultValue::Function(function) => self.visit_function(function),
                ExportDefaultValue::Class(class) => self.visit_class(class),
                ExportDefaultValue::Expression(expression) => {
                    self.visit_expr(expression, in_constructor)
                }
                ExportDefaultValue::Missing(_) => {}
                ExportDefaultValue::Interface(_) => {}
            },
            Statement::Export(ExportDeclaration::Assignment(expression)) => {
                self.visit_expr(expression, in_constructor)
            }
            Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                inner,
            )))
            | Statement::Declare(inner) => self.visit_statement(inner, in_constructor),
            Statement::Namespace(namespace) => {
                self.visit_statements(&namespace.body.data().statements)
            }
            Statement::Try(statement) => {
                self.visit_statements(&statement.block.data().statements);
                if let Some(handler) = &statement.handler {
                    self.visit_statements(&handler.data().body.data().statements);
                }
                if let Some(finalizer) = &statement.finalizer {
                    self.visit_statements(&finalizer.data().statements);
                }
            }
            _ => {}
        }
    }

    fn visit_variable(&mut self, variable: &VariableDeclaration) {
        for declaration in &variable.declarations {
            let declaration = declaration.data();
            let binding_name = match declaration.binding.data() {
                BindingPattern::Identifier(identifier) => {
                    Some(self.identifier(identifier).into_owned())
                }
                _ => None,
            };
            let annotation_name = declaration
                .type_annotation
                .as_ref()
                .and_then(|annotation| self.annotation_type_name(annotation));
            if let (Some(name), Some(type_name)) = (&binding_name, &annotation_name) {
                self.variable_types.insert(name.clone(), type_name.clone());
            }
            if let Some(initializer) = &declaration.initializer {
                if declaration
                    .type_annotation
                    .as_ref()
                    .is_some_and(|annotation| {
                        matches!(
                            annotation.data().type_node.data(),
                            TypeNode::Keyword(KeywordType::Unknown)
                        )
                    })
                    && self.is_json_parse_expr(initializer)
                {
                    self.safe_json_parses.insert(initializer.range());
                }
                if let (Some(alias), Expression::Member(_)) = (&binding_name, initializer.data())
                    && self.called_names.contains(alias)
                {
                    self.push(SemanticHazard::DetachedMethod, initializer.range());
                }
                if let (Some(alias), Expression::Identifier(source)) =
                    (&binding_name, initializer.data())
                    && declaration
                        .type_annotation
                        .as_ref()
                        .is_some_and(|annotation| {
                            Self::type_is_readonly(&annotation.data().type_node)
                        })
                {
                    self.readonly_aliases
                        .insert(self.identifier(source).into_owned());
                    self.readonly_aliases.insert(alias.clone());
                }
                if let (Some(target), Expression::Identifier(source)) =
                    (annotation_name.as_deref(), initializer.data())
                    && let Some(source_type) =
                        self.variable_types.get(self.identifier(source).as_ref())
                    && ((target == "number" && self.numeric_enums.contains(source_type))
                        || (self.numeric_enums.contains(target) && source_type == "number"))
                {
                    self.push(SemanticHazard::NumericEnumNumber, initializer.range());
                }
                if let Some(annotation) = &declaration.type_annotation
                    && self
                        .has_explicit_undefined_optional(&annotation.data().type_node, initializer)
                {
                    self.push(
                        SemanticHazard::ExplicitUndefinedOptional,
                        initializer.range(),
                    );
                }
                if let Some(annotation) = &declaration.type_annotation
                    && let TypeNode::Function(expected) = annotation.data().type_node.data()
                    && let Expression::Arrow(actual) = initializer.data()
                {
                    if expected.parameters.len() > actual.parameters.len() {
                        self.push(SemanticHazard::FewerCallbackParameters, initializer.range());
                    }
                    if matches!(
                        expected.return_type.data(),
                        TypeNode::Keyword(KeywordType::Void)
                    ) && matches!(&actual.body, FunctionBody::Expression(_))
                    {
                        self.push(SemanticHazard::ValueReturnedToVoid, initializer.range());
                    }
                }
                self.visit_expr(initializer, false);
            }
        }
    }

    fn visit_function(&mut self, function: &FunctionLike) {
        let mut shadowed_types = Vec::new();
        for parameter in &function.parameters {
            if let (BindingPattern::Identifier(identifier), Some(annotation)) = (
                parameter.data().binding.data(),
                parameter.data().type_annotation.as_ref(),
            ) && let Some(type_name) = self.reference_type_name(&annotation.data().type_node)
            {
                let name = self.identifier(identifier).into_owned();
                shadowed_types.push((name.clone(), self.variable_types.insert(name, type_name)));
            }
            if parameter.data().type_annotation.is_none() {
                self.push(SemanticHazard::ImplicitAny, parameter.range());
            }
            if let Some(initializer) = &parameter.data().initializer {
                self.visit_expr(initializer, false);
            }
        }
        self.visit_body(function.body.as_ref(), false);
        for (name, previous) in shadowed_types {
            if let Some(previous) = previous {
                self.variable_types.insert(name, previous);
            } else {
                self.variable_types.remove(&name);
            }
        }
    }

    fn visit_body(&mut self, body: Option<&FunctionBody>, in_constructor: bool) {
        match body {
            Some(FunctionBody::Block(block)) => {
                for statement in &block.data().statements {
                    self.visit_statement(statement, in_constructor);
                }
            }
            Some(FunctionBody::Expression(expression)) => {
                self.visit_expr(expression, in_constructor)
            }
            _ => {}
        }
    }

    fn visit_class(&mut self, class: &ClassDeclaration) {
        let base = class
            .name
            .as_ref()
            .and_then(|name| self.classes.get(self.identifier(name).as_ref()))
            .and_then(|class| class.base.as_ref())
            .and_then(|base| self.classes.get(base))
            .cloned();
        let mut accessor_types = HashMap::new();
        let relations = TypeRelations::new(self.model.types());
        for member in &class.members {
            match member.data() {
                ClassMember::Constructor(constructor) => {
                    for statement in &constructor.body.data().statements {
                        self.visit_statement(statement, true);
                    }
                }
                ClassMember::Method(method) => {
                    if let Some(name) = self.property_name(&method.name) {
                        let implicit_override = base
                            .as_ref()
                            .is_some_and(|base| base.methods.contains(&name))
                            && !method.modifiers.is_override
                            && !method.modifiers.is_static
                            && method.modifiers.accessibility != Some(Accessibility::Private);
                        if matches!(
                            method.modifier,
                            PropertyModifier::Get | PropertyModifier::Set
                        ) {
                            let annotation =
                                if method.modifier == PropertyModifier::Get {
                                    method.function.return_type.as_ref()
                                } else {
                                    method.function.parameters.first().and_then(|parameter| {
                                        parameter.data().type_annotation.as_ref()
                                    })
                                };
                            let current = annotation
                                .and_then(|annotation| {
                                    self.model.resolved_type(annotation.data().type_node.id())
                                })
                                .unwrap_or_else(|| self.model.types().any());
                            let key = (method.modifiers.is_static, name);
                            if let Some(&previous) = accessor_types.get(&key)
                                && !relations.equivalent(previous, current)
                            {
                                self.push(SemanticHazard::DivergentAccessor, member.range());
                            }
                            accessor_types.insert(key, current);
                        }
                        if implicit_override {
                            self.push(SemanticHazard::ImplicitOverride, member.range());
                        }
                    }
                    self.visit_function(&method.function);
                }
                ClassMember::Property(property) => {
                    if let Some(name) = self.property_name(&property.name)
                        && base
                            .as_ref()
                            .is_some_and(|base| base.accessors.contains(&name))
                        && !property.modifiers.is_declare
                    {
                        self.push(
                            if property.initializer.is_some() {
                                SemanticHazard::InitializedFieldShadowsAccessor
                            } else {
                                SemanticHazard::UninitializedFieldShadowsAccessor
                            },
                            member.range(),
                        );
                    }
                    if let Some(initializer) = &property.initializer {
                        self.visit_expr(initializer, false);
                    }
                }
                ClassMember::AutoAccessor(accessor) => {
                    if let Some(initializer) = &accessor.initializer {
                        self.visit_expr(initializer, false);
                    }
                }
                ClassMember::StaticBlock(block) => self.visit_statements(&block.data().statements),
                _ => {}
            }
        }
    }

    fn visit_switch(&mut self, range: TextRange, switch: &SwitchStatement) {
        let identifier = match switch.discriminant.data() {
            Expression::Identifier(identifier) => identifier,
            Expression::Member(MemberExpression { object, .. }) => {
                let Expression::Identifier(identifier) = object.data() else {
                    return;
                };
                identifier
            }
            _ => return,
        };
        let Some(type_name) = self
            .variable_types
            .get(self.identifier(identifier).as_ref())
            .cloned()
        else {
            return;
        };
        let Some(variant_count) = self.union_variants.get(&type_name).copied() else {
            return;
        };
        let covered = switch
            .cases
            .iter()
            .filter(|case| case.data().test.is_some())
            .count();
        if covered < variant_count && !switch.cases.iter().any(|case| case.data().test.is_none()) {
            self.push(SemanticHazard::NonExhaustiveSwitch, range);
        }
    }

    fn visit_expr(&mut self, expression: &Expr, in_constructor: bool) {
        match expression.data() {
            Expression::As(assertion) => {
                self.push(SemanticHazard::UncheckedAssertion, expression.range());
                if let Expression::Call(call) = assertion.expression.data()
                    && self.is_object_keys_call(call)
                    && assertion
                        .type_node
                        .as_deref()
                        .is_some_and(Self::type_is_keyof_array)
                {
                    self.push(SemanticHazard::OpenObjectKeys, expression.range());
                }
                self.visit_expr(&assertion.expression, in_constructor);
            }
            Expression::TypeAssertion(assertion) => {
                self.push(SemanticHazard::UncheckedAssertion, expression.range());
                self.visit_expr(&assertion.expression, in_constructor);
            }
            Expression::Member(member) => {
                self.visit_member(expression.range(), member);
                self.visit_expr(&member.object, in_constructor);
                if let MemberProperty::Computed(property) = &member.property {
                    self.visit_expr(property, in_constructor);
                }
            }
            Expression::Call(call) => {
                self.visit_call(expression.range(), call, in_constructor);
                self.visit_expr(&call.callee, in_constructor);
                for argument in &call.arguments {
                    let argument = match argument {
                        CallArgument::Expression(argument) => argument,
                        CallArgument::Spread(spread) => &spread.argument,
                        CallArgument::Missing(_) => continue,
                    };
                    if let Expression::Identifier(identifier) = argument.data() {
                        let name = self.identifier(identifier).into_owned();
                        self.readonly_aliases.remove(name.as_str());
                    }
                    self.visit_expr(argument, in_constructor);
                }
            }
            Expression::Binary(binary) => {
                if matches!(
                    binary.operator,
                    BinaryOperator::Equal | BinaryOperator::NotEqual
                ) {
                    self.push(SemanticHazard::LooseEqualityCoercion, expression.range());
                }
                if binary.operator == BinaryOperator::Add
                    && (self.is_object_create_call(&binary.left)
                        || self.is_object_create_call(&binary.right))
                {
                    self.push(SemanticHazard::ObjectToPrimitive, expression.range());
                }
                self.visit_expr(&binary.left, in_constructor);
                self.visit_expr(&binary.right, in_constructor);
            }
            Expression::Template(template) => {
                for interpolation in &template.expressions {
                    if self.is_symbol_call(interpolation) {
                        self.push(SemanticHazard::SymbolInterpolation, interpolation.range());
                    }
                    self.visit_expr(interpolation, in_constructor);
                }
            }
            Expression::Object(object) => {
                for member in &object.members {
                    if let ObjectMember::Property(property) = member.data() {
                        if self.is_to_string_tag(&property.name)
                            && !matches!(
                                property.value.data(),
                                Expression::Literal(Literal::String(_))
                            )
                        {
                            self.push(SemanticHazard::UnsafeToStringTag, member.range());
                        }
                        self.visit_expr(&property.value, in_constructor);
                    }
                }
            }
            Expression::Array(array) => {
                for element in &array.elements {
                    match element {
                        ArrayElement::Expression(element) => {
                            self.visit_expr(element, in_constructor)
                        }
                        ArrayElement::Spread(spread) => {
                            self.visit_expr(&spread.argument, in_constructor)
                        }
                        _ => {}
                    }
                }
            }
            Expression::Function(function) => self.visit_function(&function.function),
            Expression::Arrow(arrow) => {
                for parameter in &arrow.parameters {
                    if parameter.data().type_annotation.is_none() {
                        self.push(SemanticHazard::ImplicitAny, parameter.range());
                    }
                }
                self.visit_body(Some(&arrow.body), false);
            }
            Expression::Class(class) => self.visit_class(&class.class),
            Expression::Logical(logical) => {
                self.visit_expr(&logical.left, in_constructor);
                self.visit_expr(&logical.right, in_constructor);
            }
            Expression::Conditional(conditional) => {
                self.visit_expr(&conditional.test, in_constructor);
                self.visit_expr(&conditional.consequent, in_constructor);
                self.visit_expr(&conditional.alternate, in_constructor);
            }
            Expression::Update(update) => {
                self.visit_assignment_target(&update.argument, in_constructor)
            }
            Expression::Assignment(assignment) => {
                if let AssignmentTarget::Member(member) = assignment.left.data()
                    && let Expression::Identifier(identifier) = member.object.data()
                    && self
                        .readonly_aliases
                        .contains(self.identifier(identifier).as_ref())
                {
                    self.push(SemanticHazard::ReadonlyAliasMutation, expression.range());
                }
                self.visit_assignment_target(&assignment.left, in_constructor);
                self.visit_expr(&assignment.right, in_constructor);
            }
            Expression::Sequence(sequence) => {
                for expression in &sequence.expressions {
                    self.visit_expr(expression, in_constructor);
                }
            }
            Expression::Parenthesized(inner) => self.visit_expr(inner, in_constructor),
            Expression::Satisfies(assertion) => {
                self.visit_expr(&assertion.expression, in_constructor)
            }
            Expression::NonNull(assertion) => {
                self.visit_expr(&assertion.expression, in_constructor)
            }
            Expression::Await(await_expression) => {
                self.visit_expr(&await_expression.argument, in_constructor)
            }
            Expression::Yield(yield_expression) => {
                if let Some(argument) = &yield_expression.argument {
                    self.visit_expr(argument, in_constructor);
                }
            }
            Expression::Unary(unary) => self.visit_expr(&unary.argument, in_constructor),
            Expression::New(call) => {
                self.visit_expr(&call.callee, in_constructor);
                for argument in &call.arguments {
                    if let CallArgument::Expression(argument) = argument {
                        self.visit_expr(argument, in_constructor);
                    }
                }
            }
            Expression::TaggedTemplate(tagged) => {
                self.visit_expr(&tagged.tag, in_constructor);
                for expression in &tagged.template.expressions {
                    self.visit_expr(expression, in_constructor);
                }
            }
            Expression::Import(import) => {
                self.visit_expr(&import.source, in_constructor);
                if let Some(options) = &import.options {
                    self.visit_expr(options, in_constructor);
                }
            }
            _ => {}
        }
    }

    fn visit_assignment_target(&mut self, target: &AssignmentTargetNode, in_constructor: bool) {
        match target.data() {
            AssignmentTarget::Member(member) => {
                self.visit_expr(&member.object, in_constructor);
                if let MemberProperty::Computed(property) = &member.property {
                    self.visit_expr(property, in_constructor);
                }
            }
            AssignmentTarget::Object(object) => {
                for property in &object.properties {
                    self.visit_assignment_target(&property.target, in_constructor);
                    if let Some(initializer) = &property.initializer {
                        self.visit_expr(initializer, in_constructor);
                    }
                }
            }
            AssignmentTarget::Array(array) => {
                for element in &array.elements {
                    if let AssignmentArrayElement::Target(target) = element {
                        self.visit_assignment_target(target, in_constructor);
                    }
                }
            }
            AssignmentTarget::Identifier(_) | AssignmentTarget::Missing(_) => {}
            AssignmentTarget::Invalid(operand) => {
                self.visit_expr(operand, in_constructor);
            }
        }
    }

    fn visit_member(&mut self, range: TextRange, member: &MemberExpression) {
        let Expression::Identifier(object) = member.object.data() else {
            return;
        };
        let object_name = self.identifier(object).into_owned();
        if self
            .variable_types
            .get(&object_name)
            .is_some_and(|ty| self.index_signature_types.contains(ty))
        {
            self.push(
                if matches!(member.property, MemberProperty::Computed(_)) {
                    SemanticHazard::UncheckedIndexRead
                } else {
                    SemanticHazard::IndexSignatureDotAccess
                },
                range,
            );
        }
        if self.numeric_enums.contains(&object_name)
            && matches!(member.property, MemberProperty::Computed(_))
        {
            self.push(SemanticHazard::NumericEnumReverseLookup, range);
        }
    }

    fn visit_call(&mut self, range: TextRange, call: &CallExpression, in_constructor: bool) {
        let Expression::Member(member) = call.callee.data() else {
            return;
        };
        let Some(method) = self.member_name(member) else {
            return;
        };
        if in_constructor
            && matches!(member.object.data(), Expression::This)
            && method != "constructor"
        {
            self.push(SemanticHazard::VirtualCallInConstructor, range);
        }
        if self.is_global_identifier(&member.object, "Object")
            && method == "keys"
            && call.arguments.first().is_some_and(|argument| {
                let CallArgument::Expression(argument) = argument else {
                    return false;
                };
                let Expression::Object(object) = argument.data() else {
                    return false;
                };
                object.members.iter().any(|member| {
                    let ObjectMember::Property(property) = member.data() else {
                        return false;
                    };
                    match &property.name {
                        PropertyName::Number(_) => true,
                        PropertyName::String(string) => self
                            .source
                            .token_text(string.data().token())
                            .unwrap_or("")
                            .trim_matches(['"', '\''])
                            .parse::<u32>()
                            .is_ok(),
                        _ => false,
                    }
                })
            })
            && !self.sorted_object_keys.contains(&range)
        {
            self.push(SemanticHazard::NumericKeyOrder, range);
        }
        if self.is_global_identifier(&member.object, "JSON") {
            if method == "parse" && !self.safe_json_parses.contains(&range) {
                self.push(SemanticHazard::UncheckedJsonParse, range);
            } else if method == "stringify"
                && call.arguments.len() == 1
                && call.arguments.first().is_some_and(|argument| {
                    matches!(
                        argument,
                        CallArgument::Expression(argument)
                            if self.json_unserializable(argument)
                    )
                })
            {
                self.push(SemanticHazard::JsonStringifyUnserializable, range);
            }
        }
        if matches!(method.as_str(), "toString" | "toFixed")
            && let Some(CallArgument::Expression(argument)) = call.arguments.first()
            && let Expression::Literal(Literal::Number(number)) = argument.data()
            && let Ok(value) = self
                .source
                .token_text(number.data().token())
                .unwrap_or("")
                .parse::<i32>()
            && ((method == "toString" && !(2..=36).contains(&value))
                || (method == "toFixed" && !(0..=100).contains(&value)))
        {
            self.push(SemanticHazard::InvalidNumberFormatting, range);
        }
        if method == "sort"
            && call.arguments.is_empty()
            && matches!(member.object.data(), Expression::Array(_))
        {
            self.push(SemanticHazard::NumericDefaultSort, range);
        }
    }

    fn json_unserializable(&self, expression: &Expr) -> bool {
        match expression.data() {
            Expression::Literal(Literal::BigInt(_))
            | Expression::Function(_)
            | Expression::Arrow(_) => true,
            Expression::Identifier(identifier) => {
                self.is_global_identifier(expression, "undefined")
                    || self
                        .variable_types
                        .get(self.identifier(identifier).as_ref())
                        .is_some_and(|ty| {
                            matches!(ty.as_str(), "bigint" | "BigInt" | "symbol" | "Symbol")
                        })
            }
            Expression::Call(_) => self.is_symbol_call(expression),
            _ => false,
        }
    }

    fn is_object_keys_call(&self, call: &CallExpression) -> bool {
        let Expression::Member(member) = call.callee.data() else {
            return false;
        };
        self.is_global_identifier(&member.object, "Object")
            && self.member_name(member).as_deref() == Some("keys")
    }

    fn is_json_parse_expr(&self, expression: &Expr) -> bool {
        let Expression::Call(call) = expression.data() else {
            return false;
        };
        let Expression::Member(member) = call.callee.data() else {
            return false;
        };
        self.is_global_identifier(&member.object, "JSON")
            && self.member_name(member).as_deref() == Some("parse")
    }

    fn is_object_create_call(&self, expression: &Expr) -> bool {
        let Expression::Call(call) = expression.data() else {
            return false;
        };
        let Expression::Member(member) = call.callee.data() else {
            return false;
        };
        self.is_global_identifier(&member.object, "Object")
            && self.member_name(member).as_deref() == Some("create")
    }

    fn is_symbol_call(&self, expression: &Expr) -> bool {
        let Expression::Call(call) = expression.data() else {
            return false;
        };
        self.is_global_identifier(&call.callee, "Symbol")
    }

    fn is_to_string_tag(&self, name: &PropertyName) -> bool {
        let PropertyName::Computed(expression) = name else {
            return false;
        };
        let Expression::Member(member) = expression.data() else {
            return false;
        };
        self.is_global_identifier(&member.object, "Symbol")
            && self.member_name(member).as_deref() == Some("toStringTag")
    }
}

pub(crate) fn collect_program_facts(
    sources: &[Recovered<SourceFile>],
    edges: &[ResolvedModuleEdge],
    models: &mut BTreeMap<SourceId, SemanticModel>,
) {
    let source_map = sources
        .iter()
        .map(|source| (source.product().source_id(), source.product()))
        .collect::<BTreeMap<_, _>>();
    let mut additions = BTreeMap::<SourceId, Vec<HazardFact>>::new();

    for recovered in sources {
        let source = recovered.product();
        let source_id = source.source_id();
        let has_local_edge = edges.iter().any(|edge| edge.from == source_id);
        for statement in source.statements() {
            let edge = edges
                .iter()
                .find(|edge| edge.from == source_id && edge.specifier == statement.id());
            match statement.data() {
                Statement::Import(import) => {
                    if import.clause.is_none() {
                        if edge.is_none() {
                            push_program_fact(
                                &mut additions,
                                source_id,
                                SemanticHazard::UncheckedSideEffectImport,
                                statement.range(),
                                None,
                            );
                        }
                        continue;
                    }
                    let Some(edge) = edge else {
                        continue;
                    };
                    let Some(target) = source_map.get(&edge.to).copied() else {
                        continue;
                    };
                    let target_model = models
                        .get(&edge.to)
                        .expect("program model contains the edge target");
                    let commonjs = commonjs_exports(target, target_model);
                    let clause = import.clause.as_ref().expect("checked above");
                    if clause.default.is_some()
                        && commonjs.is_commonjs
                        && !has_esm_default_export(target)
                    {
                        push_program_fact(
                            &mut additions,
                            source_id,
                            SemanticHazard::InteropDependentDefaultImport,
                            statement.range(),
                            None,
                        );
                    }
                    if let Some(ImportBinding::Named(specifiers)) = &clause.binding {
                        let type_exports = exported_type_names(target);
                        for specifier in specifiers {
                            let Some(name) = module_export_name(source, &specifier.data().imported)
                            else {
                                continue;
                            };
                            if !import.type_only
                                && specifier.data().mode == ImportSpecifierMode::Value
                                && type_exports.contains(name.as_ref())
                            {
                                push_program_fact(
                                    &mut additions,
                                    source_id,
                                    SemanticHazard::TypeImportedAsValue,
                                    specifier.range(),
                                    None,
                                );
                            }
                            if commonjs.is_commonjs && !commonjs.named.contains(name.as_ref()) {
                                push_program_fact(
                                    &mut additions,
                                    source_id,
                                    SemanticHazard::CjsEsmNamedExportMismatch,
                                    specifier.range(),
                                    Some(
                                        format!(
                                            "CommonJS target does not statically export `{name}`"
                                        )
                                        .into_boxed_str(),
                                    ),
                                );
                            }
                        }
                    }
                }
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Specifiers {
                        type_only,
                        specifiers,
                        source: Some(_),
                        ..
                    },
                )) => {
                    let Some(edge) = edge else {
                        continue;
                    };
                    let Some(target) = source_map.get(&edge.to).copied() else {
                        continue;
                    };
                    let type_exports = exported_type_names(target);
                    for specifier in specifiers {
                        let Some(name) = module_export_name(source, &specifier.data().local) else {
                            continue;
                        };
                        if !*type_only
                            && specifier.data().mode == ExportSpecifierMode::Value
                            && type_exports.contains(name.as_ref())
                        {
                            push_program_fact(
                                &mut additions,
                                source_id,
                                SemanticHazard::TypeReexportedAsValue,
                                specifier.range(),
                                None,
                            );
                        }
                    }
                }
                Statement::Export(ExportDeclaration::Named(
                    ExportNamedDeclaration::Declaration(declaration),
                )) if has_local_edge && declaration_depends_on_inference(declaration) => {
                    push_program_fact(
                        &mut additions,
                        source_id,
                        SemanticHazard::DeclarationInferenceDependency,
                        declaration.range(),
                        None,
                    );
                }
                _ => {}
            }
        }
    }

    for (source_id, facts) in additions {
        let model = models
            .get_mut(&source_id)
            .expect("program facts only target checked modules");
        model.facts_mut().extend(facts);
    }
}

fn push_program_fact(
    additions: &mut BTreeMap<SourceId, Vec<HazardFact>>,
    source_id: SourceId,
    hazard: SemanticHazard,
    range: TextRange,
    note: Option<Box<str>>,
) {
    additions.entry(source_id).or_default().push(HazardFact {
        hazard,
        range,
        note,
    });
}

fn declaration_depends_on_inference(statement: &Stmt) -> bool {
    match statement.data() {
        Statement::Variable(variable) => variable
            .declarations
            .iter()
            .any(|declaration| declaration.data().type_annotation.is_none()),
        Statement::Function(function) => function.function.return_type.is_none(),
        _ => false,
    }
}

fn exported_type_names<'a>(source: &'a SourceFile) -> HashSet<Cow<'a, str>> {
    source
        .statements()
        .iter()
        .filter_map(|statement| {
            let Statement::Export(ExportDeclaration::Named(ExportNamedDeclaration::Declaration(
                declaration,
            ))) = statement.data()
            else {
                return None;
            };
            match declaration.data() {
                Statement::Interface(interface) => {
                    source.identifier_text(interface.name.data().token())
                }
                Statement::TypeAlias(alias) => source.identifier_text(alias.name.data().token()),
                _ => None,
            }
        })
        .collect()
}

struct CommonJsExports {
    is_commonjs: bool,
    named: HashSet<String>,
}

/// Returns whether `identifier` denotes the host-provided CommonJS global
/// (`module` or `exports`) rather than a user declaration that shadows it.
fn is_commonjs_global(model: &SemanticModel, identifier: &IdentifierNode) -> bool {
    model
        .reference(identifier.id())
        .is_none_or(|symbol| model.symbol(symbol).kind() == SymbolKind::IntrinsicValue)
}

fn commonjs_exports(source: &SourceFile, model: &SemanticModel) -> CommonJsExports {
    let mut exports = CommonJsExports {
        is_commonjs: false,
        named: HashSet::new(),
    };
    for statement in source.statements() {
        let Statement::Expression(statement) = statement.data() else {
            continue;
        };
        let Expression::Assignment(assignment) = statement.expression.data() else {
            continue;
        };
        let AssignmentTarget::Member(member) = assignment.left.data() else {
            continue;
        };
        let MemberProperty::Named(property) = &member.property else {
            continue;
        };
        let property_name = source
            .identifier_text(property.data().token())
            .unwrap_or_default();
        if let Expression::Member(namespace) = member.object.data() {
            let Expression::Identifier(module) = namespace.object.data() else {
                continue;
            };
            let MemberProperty::Named(namespace_property) = &namespace.property else {
                continue;
            };
            let module_name = source
                .identifier_text(module.data().token())
                .unwrap_or_default();
            let namespace_name = source
                .identifier_text(namespace_property.data().token())
                .unwrap_or_default();
            if module_name == "module"
                && namespace_name == "exports"
                && is_commonjs_global(model, module)
            {
                exports.is_commonjs = true;
                exports.named.insert(property_name.into_owned());
            }
            continue;
        }
        let Expression::Identifier(object) = member.object.data() else {
            continue;
        };
        let object_name = source
            .identifier_text(object.data().token())
            .unwrap_or_default();
        if !is_commonjs_global(model, object)
            || !matches!(object_name.as_ref(), "module" | "exports")
        {
            continue;
        }
        match (object_name.as_ref(), property_name.as_ref()) {
            ("module", "exports") => {
                exports.is_commonjs = true;
                let Expression::Object(object) = assignment.right.data() else {
                    continue;
                };
                for member in &object.members {
                    let name = match member.data() {
                        ObjectMember::Property(property) => &property.name,
                        ObjectMember::Method(method) => &method.name,
                        ObjectMember::Spread(_) | ObjectMember::Missing(_) => continue,
                    };
                    let name = match name {
                        PropertyName::Identifier(identifier) => {
                            source.identifier_text(identifier.data().token())
                        }
                        PropertyName::String(string) => source
                            .token_text(string.data().token())
                            .map(|name| Cow::Borrowed(name.trim_matches(['"', '\'']))),
                        _ => None,
                    };
                    if let Some(name) = name {
                        exports.named.insert(name.into_owned());
                    }
                }
            }
            ("exports", name) => {
                exports.is_commonjs = true;
                exports.named.insert(name.to_owned());
            }
            _ => {}
        }
    }
    exports
}

fn has_esm_default_export(source: &SourceFile) -> bool {
    source.statements().iter().any(|statement| {
        matches!(
            statement.data(),
            Statement::Export(ExportDeclaration::Default(_))
        )
    })
}

fn module_export_name<'a>(source: &'a SourceFile, name: &ModuleExportName) -> Option<Cow<'a, str>> {
    match name {
        ModuleExportName::Identifier(node) => source.identifier_text(node.data().token()),
        ModuleExportName::String(node) => {
            let text = source.source_text();
            let range = node.range();
            let start = text.utf16_to_byte(range.start()).ok()?;
            let end = text.utf16_to_byte(range.end()).ok()?;
            text.as_str()
                .get(start..end)
                .map(|value| Cow::Borrowed(value.trim_matches(['"', '\''])))
        }
        ModuleExportName::Missing(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::{
        checker::{
            ProgramCheckInput, ProgramCheckOptions, ResolvedModuleEdge, check_program,
            check_program_with_options, check_with_lints,
        },
        lint::{LintProfile, LintTable},
        parser, scanner,
        source::{ScriptKind, SourceId, SourceText},
        syntax::SourceFile,
    };
    fn parsed(
        source_id: u32,
        source: &str,
        kind: ScriptKind,
    ) -> crate::diagnostic::Recovered<SourceFile> {
        parser::parse(scanner::scan(
            SourceId::new(source_id),
            kind,
            Arc::new(SourceText::new(source).expect("test source fits the per-file budget")),
        ))
    }

    fn codes(source: &str) -> Vec<&'static str> {
        let parsed = parsed(0, source, ScriptKind::TypeScript);
        check_with_lints(&parsed, &LintTable::new(LintProfile::Pedantic))
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect()
    }

    #[test]
    fn implicit_any_ranges_stay_ordered_after_non_ascii_prefixes() {
        let source = "const café = call(); function plain(value) {}";
        let parsed = parsed(0, source, ScriptKind::TypeScript);
        let result = check_with_lints(&parsed, &LintTable::new(LintProfile::Pedantic));
        let diagnostic = result
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code().as_str() == "BAMTS-W018")
            .expect("untyped parameter is diagnosed");
        let expected_start = parsed
            .product()
            .source_text()
            .byte_to_utf16(source.find("value").expect("parameter is present"))
            .expect("parameter starts on a UTF-8 boundary");
        assert_eq!(diagnostic.range().start(), expected_start);
        assert!(diagnostic.range().start() <= diagnostic.range().end());
    }

    #[test]
    fn unary_non_number_enum_initializer_is_not_a_numeric_enum() {
        let source = "enum E { A = -C } let e: E = E.A; let n: number = e;";
        assert!(
            !codes(source).contains(&"BAMTS-W045"),
            "a nonnumeric enum initializer must not create a numeric-enum hazard"
        );
    }

    #[test]
    fn accessor_types_compare_by_canonical_checker_identity() {
        let equivalent = "type Value = number|string; class C { get x(): Value { return 1; } set x(value: number | string) {} }";
        assert!(
            !codes(equivalent).contains(&"BAMTS-W011"),
            "aliases and formatting must not make equivalent accessor types diverge"
        );

        let different = "class C { get x(): number { return 1; } set x(value: string) {} }";
        assert!(
            codes(different).contains(&"BAMTS-W011"),
            "different accessor types must still diverge"
        );
    }

    #[test]
    fn static_and_instance_accessor_pairs_do_not_diverge() {
        let static_get_instance_set =
            "class C { static get x(): number { return 1; } set x(value: string) {} }";
        assert!(
            !codes(static_get_instance_set).contains(&"BAMTS-W011"),
            "static and instance accessors are independent and must not be compared"
        );

        let static_get_static_set_divergent =
            "class C { static get x(): number { return 1; } static set x(value: string) {} }";
        assert!(
            codes(static_get_static_set_divergent).contains(&"BAMTS-W011"),
            "same-staticness divergent accessor pairs must still report divergence"
        );
    }

    #[test]
    fn every_single_file_rule_has_a_trigger_and_high_risk_near_miss() {
        let cases = [
            (
                "BAMTS-W008",
                "interface D {[key: string]: number} declare const d:D; declare const k:string; const n=d[k];",
                "const colors: Record<'red', number>={red:1}; const n=colors['red'];",
            ),
            (
                "BAMTS-W009",
                "const o: {p?: number} = {p: undefined};",
                "const o: {p?: number | undefined} = {p: undefined};",
            ),
            ("BAMTS-W010", "const f = obj.method; f();", "obj.method();"),
            (
                "BAMTS-W011",
                "class C { get x(): number {return 1} set x(v: string | number) {} }",
                "class C { get x(): number {return 1} set x(v: number) {} }",
            ),
            (
                "BAMTS-W012",
                "const m={x:1}; const r:{readonly x:number}=m; m.x=2;",
                "const m={x:1}; const r:{readonly x:number}=m; publishReadonly(m); m.x=2;",
            ),
            (
                "BAMTS-W013",
                "const f: (x:number,y:string)=>void = () => {};",
                "const f: (x:number,y:string)=>void = (x,y) => {};",
            ),
            (
                "BAMTS-W014",
                "const f: () => void = () => 42;",
                "const f: () => void = () => { consume(42); };",
            ),
            (
                "BAMTS-W015",
                "const ks = Object.keys(x) as (keyof typeof x)[];",
                "const ks = Object.keys(x);",
            ),
            (
                "BAMTS-W016",
                "interface D {[key:string]: number} declare const d:D; d.username;",
                "interface D {[key:string]: number} declare const d:D; d['username'];",
            ),
            (
                "BAMTS-W018",
                "function f(value) { return value; }",
                "function f(value: unknown) { return value; }",
            ),
            (
                "BAMTS-W019",
                "const user = value as User;",
                "if (isUser(value)) { const user: User = value; }",
            ),
            (
                "BAMTS-W038",
                "class B { constructor(){ this.init() } init(){} }",
                "class B { constructor(){ initializeDirectly() } init(){} }",
            ),
            (
                "BAMTS-W040",
                "class B { get data():number{return 1} } class D extends B { data = 1; }",
                "class B { get data():number{return 1} } class D extends B { declare data:number; }",
            ),
            (
                "BAMTS-W041",
                "class B { run(){} } class D extends B { run(){} }",
                "class B { run(){} } class D extends B { override run(){} }",
            ),
            (
                "BAMTS-W045",
                "enum E { A } let e:E=E.A; let n:number=e;",
                "enum E { A } const e=E.A;",
            ),
            (
                "BAMTS-W048",
                "enum E { A } const name=E[E.A];",
                "enum E { A } const value=E.A;",
            ),
            (
                "BAMTS-W063",
                "type S={kind:'a'}|{kind:'b'}; declare const s:S; switch (s.kind) { case 'a': break; }",
                "type S={kind:'a'}|{kind:'b'}; declare const s:S; switch (s.kind) { case 'a': break; case 'b': break; }",
            ),
            ("BAMTS-W071", "(42).toString(1);", "(42).toString(36);"),
            (
                "BAMTS-W072",
                "Object.keys({ b: 1, \"2\": 2 });",
                "Object.keys({ b: 1, \"2\": 2 }).sort();",
            ),
            (
                "BAMTS-W073",
                "JSON.stringify(10n);",
                "JSON.stringify(10n, (_key, value) => typeof value === 'bigint' ? String(value) : value);",
            ),
            (
                "BAMTS-W074",
                "const user: User = JSON.parse(text);",
                "const raw: unknown = JSON.parse(text);",
            ),
            (
                "BAMTS-W075",
                "[10, 2, 5].sort();",
                "[10, 2, 5].sort((a,b)=>a-b);",
            ),
            ("BAMTS-W076", "\"0\" == false;", "\"0\" === String(false);"),
            (
                "BAMTS-W077",
                "\"key_\" + Object.create(null);",
                "\"key_\" + String(Object.create(null));",
            ),
            (
                "BAMTS-W078",
                "`ID: ${Symbol('x')}`;",
                "tag`ID: ${Symbol('x')}`;",
            ),
            (
                "BAMTS-W080",
                "const tagged = { [Symbol.toStringTag]: 123 };",
                "const tagged = { [Symbol.toStringTag]: 'Widget' };",
            ),
            (
                "BAMTS-W081",
                "class B { get data():number{return 1} } class D extends B { data:number; }",
                "class B { get data():number{return 1} } class D extends B { declare data:number; }",
            ),
        ];
        for (code, trigger, safe) in cases {
            assert!(
                codes(trigger).contains(&code),
                "{code} did not fire for {trigger}"
            );
            assert!(
                !codes(safe).contains(&code),
                "{code} fired for near miss {safe}"
            );
        }
    }

    #[test]
    fn program_rules_use_resolved_edges_and_type_value_origins() {
        let levels = LintTable::new(LintProfile::Pedantic);
        for (code, from, to, safe_from, safe_to) in [
            (
                "BAMTS-W028",
                "import { make } from './types.js'; export const value = make();",
                "export const make = () => ({x:1});",
                "export const value: {x:number} = {x:1};",
                "export const make = () => ({x:1});",
            ),
            (
                "BAMTS-W031",
                "import { User } from './types.js'; let user: User;",
                "export interface User { id:number }",
                "import { User } from './types.js'; new User();",
                "export class User { id=1 }",
            ),
            (
                "BAMTS-W032",
                "export { User } from './types.js';",
                "export interface User { id:number }",
                "export { User } from './types.js';",
                "export class User { id=1 }",
            ),
        ] {
            let files = [
                parsed(0, from, ScriptKind::TypeScript),
                parsed(1, to, ScriptKind::TypeScript),
            ];
            let edge = [ResolvedModuleEdge {
                from: SourceId::new(0),
                specifier: files[0].product().statements()[0].id(),
                to: SourceId::new(1),
            }];
            let result = check_program(
                ProgramCheckInput {
                    files: &files,
                    edges: &edge,
                },
                &levels,
            );
            assert!(
                result
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code().as_str() == code),
                "{code} did not fire"
            );

            let safe_files = [
                parsed(0, safe_from, ScriptKind::TypeScript),
                parsed(1, safe_to, ScriptKind::TypeScript),
            ];
            let safe = check_program(
                ProgramCheckInput {
                    files: &safe_files,
                    edges: &[ResolvedModuleEdge {
                        from: SourceId::new(0),
                        specifier: safe_files[0].product().statements()[0].id(),
                        to: SourceId::new(1),
                    }],
                },
                &levels,
            );
            assert!(
                safe.diagnostics()
                    .iter()
                    .all(|diagnostic| diagnostic.code().as_str() != code),
                "{code} fired for the dual-namespace or local-inference near miss"
            );
        }
    }

    #[test]
    fn javascript_only_keeps_spec_footguns_as_warnings() {
        let parsed = parsed(
            0,
            "(42).toString(1); const x = value as User;",
            ScriptKind::JavaScript,
        );
        let result = check_with_lints(&parsed, &LintTable::new(LintProfile::Pedantic));
        assert!(result.diagnostics().iter().any(|diagnostic| {
            diagnostic.code().as_str() == "BAMTS-W071" && diagnostic.is_warning()
        }));
        assert!(
            result
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code().as_str() != "BAMTS-W019")
        );
    }

    #[test]
    fn user_shadow_of_module_global_is_not_treated_as_commonjs() {
        // In a CommonJS environment `module` is an intrinsic. A user-declared
        // `const module = ...` shadows it, so `module.exports.x = 1` must NOT
        // be classified as a CommonJS export — otherwise W037/W086 fire falsely.
        let files = [
            parsed(
                0,
                "const module = { exports: {} }; module.exports.x = 1;",
                ScriptKind::JavaScript,
            ),
            parsed(1, "export const y = 1;", ScriptKind::TypeScript),
        ];
        let edge = [ResolvedModuleEdge {
            from: SourceId::new(0),
            specifier: files[0].product().statements()[0].id(),
            to: SourceId::new(1),
        }];
        let result = check_program_with_options(
            ProgramCheckInput {
                files: &files,
                edges: &edge,
            },
            &LintTable::new(LintProfile::Pedantic),
            ProgramCheckOptions::commonjs(),
        );
        assert!(
            !result
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code().as_str() == "BAMTS-W086"),
            "a user-shadowed `module` must not be treated as the CommonJS global"
        );
    }

    #[test]
    fn sorted_object_keys_inside_loop_is_not_flagged_w072() {
        let source = "for (const _ of xs) { Object.keys({ b: 1, \"2\": 2 }).sort(); }";
        assert!(
            !codes(source).contains(&"BAMTS-W072"),
            "Object.keys(...).sort() inside a loop must not be flagged when keys are sorted"
        );
    }

    #[test]
    fn detached_method_inside_try_block_is_detected_w010() {
        let source = "try { const f = obj.method; f(); } catch (e) {}";
        assert!(
            codes(source).contains(&"BAMTS-W010"),
            "a detached method call inside a try block must be detected by the call-collection walk"
        );
    }
}
