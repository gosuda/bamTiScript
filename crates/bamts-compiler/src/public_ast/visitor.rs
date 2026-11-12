//! Borrow-only traversal of public AST node families.

use std::ops::ControlFlow;

use super::NodeRef;
use crate::syntax::*;

/// Receives parser-owned nodes. Returning `Break` stops the whole traversal.
pub trait Visitor<'ast> {
    type Break;

    fn visit(&mut self, node: NodeRef<'ast>) -> ControlFlow<Self::Break>;
}

pub fn visit_source_file<'ast, V>(
    file: &'ast crate::syntax::SourceFile,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    visit_node(NodeRef::SourceFile(file), visitor)
}

pub fn visit_node<'ast, V>(node: NodeRef<'ast>, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    visitor.visit(node)?;
    match node {
        NodeRef::SourceFile(file) => {
            for statement in file.statements() {
                visit_node(NodeRef::Statement(statement), visitor)?;
            }
        }
        NodeRef::Statement(statement) => visit_statement(statement, visitor)?,
        NodeRef::Expression(expression) => visit_expression(expression, visitor)?,
        NodeRef::Block(block) => {
            for statement in &block.data().statements {
                visit_node(NodeRef::Statement(statement), visitor)?;
            }
        }
        NodeRef::SwitchCase(case) => {
            if let Some(test) = &case.data().test {
                visit_node(NodeRef::Expression(test), visitor)?;
            }
            for statement in &case.data().consequent {
                visit_node(NodeRef::Statement(statement), visitor)?;
            }
        }
        NodeRef::CatchClause(clause) => {
            if let Some(binding) = &clause.data().binding {
                visit_node(NodeRef::BindingPattern(binding), visitor)?;
            }
            visit_node(NodeRef::Block(&clause.data().body), visitor)?;
        }
        NodeRef::Decorator(decorator) => {
            visit_node(NodeRef::Expression(&decorator.data().expression), visitor)?;
        }
        NodeRef::TypeAnnotation(annotation) => {
            visit_node(NodeRef::TypeNode(&annotation.data().type_node), visitor)?;
        }
        NodeRef::TypeParameter(parameter) => {
            if let Some(constraint) = &parameter.data().constraint {
                visit_node(NodeRef::TypeNode(constraint), visitor)?;
            }
            if let Some(default) = &parameter.data().default {
                visit_node(NodeRef::TypeNode(default), visitor)?;
            }
        }
        NodeRef::Parameter(parameter) => visit_parameter(parameter, visitor)?,
        NodeRef::TypeNode(node) => visit_type(node, visitor)?,
        NodeRef::BindingPattern(pattern) => visit_pattern(pattern, visitor)?,
        NodeRef::AssignmentTarget(target) => visit_assignment_target(target, visitor)?,
        NodeRef::VariableDeclarator(declarator) => {
            let data = declarator.data();
            visit_node(NodeRef::BindingPattern(&data.binding), visitor)?;
            if let Some(annotation) = &data.type_annotation {
                visit_node(NodeRef::TypeAnnotation(annotation), visitor)?;
            }
            if let Some(initializer) = &data.initializer {
                visit_node(NodeRef::Expression(initializer), visitor)?;
            }
        }
        NodeRef::ClassMember(member) => visit_class_member(member, visitor)?,
        NodeRef::ObjectMember(member) => visit_object_member(member, visitor)?,
        NodeRef::TypeMember(member) => visit_type_member(member, visitor)?,
        NodeRef::EnumMember(member) => {
            visit_property_name(&member.data().name, visitor)?;
            if let Some(initializer) = &member.data().initializer {
                visit_node(NodeRef::Expression(initializer), visitor)?;
            }
        }
        NodeRef::ImportSpecifier(_)
        | NodeRef::ExportSpecifier(_)
        | NodeRef::Identifier(_)
        | NodeRef::StringLiteral(_)
        | NodeRef::JsxText(_)
        | NodeRef::Token(_) => {}
        NodeRef::JsxOpeningElement(node) => visit_jsx_opening_element(node, visitor)?,
        NodeRef::JsxClosingElement(node) => visit_jsx_element_name(&node.data().name, visitor)?,
        NodeRef::JsxAttribute(node) => visit_jsx_attribute(node, visitor)?,
        NodeRef::JsxSpreadAttribute(node) => visit_node(
            NodeRef::Expression(node.data().expression.as_ref()),
            visitor,
        )?,
        NodeRef::JsxExpressionContainer(node) => {
            if let Some(expression) = node.data().expression.as_ref() {
                visit_node(NodeRef::Expression(expression.as_ref()), visitor)?;
            }
        }
        NodeRef::JsxSpreadChild(node) => visit_node(
            NodeRef::Expression(node.data().expression.as_ref()),
            visitor,
        )?,
    }
    ControlFlow::Continue(())
}

fn visit_statement<'ast, V>(
    statement: &'ast crate::syntax::Stmt,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match statement.data() {
        Statement::Import(value) => {
            if let Some(ImportClause {
                binding: Some(ImportBinding::Named(specifiers)),
                ..
            }) = &value.clause
            {
                for specifier in specifiers {
                    visit_node(NodeRef::ImportSpecifier(specifier), visitor)?;
                }
            }
        }
        Statement::Export(value) => match value {
            ExportDeclaration::Named(ExportNamedDeclaration::Declaration(statement)) => {
                visit_node(NodeRef::Statement(statement), visitor)?;
            }
            ExportDeclaration::Named(ExportNamedDeclaration::Specifiers { specifiers, .. }) => {
                for specifier in specifiers {
                    visit_node(NodeRef::ExportSpecifier(specifier), visitor)?;
                }
            }
            ExportDeclaration::Default(default) => match &default.value {
                ExportDefaultValue::Function(function) => visit_function(function, visitor)?,
                ExportDefaultValue::Class(class) => visit_class(class, visitor)?,
                ExportDefaultValue::Expression(expression) => {
                    visit_node(NodeRef::Expression(expression), visitor)?;
                }
                ExportDefaultValue::Interface(interface) => {
                    visit_type_parameters(interface.type_parameters.as_ref(), visitor)?;
                    for heritage in &interface.extends {
                        visit_type_arguments(heritage.type_arguments.as_ref(), visitor)?;
                    }
                    for member in &interface.members {
                        visit_node(NodeRef::TypeMember(member), visitor)?;
                    }
                }
                ExportDefaultValue::Missing(_) => {}
            },
            ExportDeclaration::Assignment(expression) => {
                visit_node(NodeRef::Expression(expression), visitor)?;
            }
            ExportDeclaration::All(_) => {}
        },
        Statement::Variable(value) => {
            for declarator in &value.declarations {
                visit_node(NodeRef::VariableDeclarator(declarator), visitor)?;
            }
        }
        Statement::Function(value) => visit_function(&value.function, visitor)?,
        Statement::Class(value) => visit_class(value, visitor)?,
        Statement::Interface(value) => {
            visit_type_parameters(value.type_parameters.as_ref(), visitor)?;
            for heritage in &value.extends {
                visit_type_arguments(heritage.type_arguments.as_ref(), visitor)?;
            }
            for member in &value.members {
                visit_node(NodeRef::TypeMember(member), visitor)?;
            }
        }
        Statement::TypeAlias(value) => {
            visit_type_parameters(value.type_parameters.as_ref(), visitor)?;
            visit_node(NodeRef::TypeNode(&value.type_node), visitor)?;
        }
        Statement::Enum(value) => {
            for member in &value.members {
                visit_node(NodeRef::EnumMember(member), visitor)?;
            }
        }
        Statement::Namespace(value) => visit_node(NodeRef::Block(&value.body), visitor)?,
        Statement::Declare(inner) => visit_node(NodeRef::Statement(inner), visitor)?,
        Statement::Block(block) => {
            for statement in &block.data().statements {
                visit_node(NodeRef::Statement(statement), visitor)?;
            }
        }
        Statement::Expression(value) => {
            visit_node(NodeRef::Expression(&value.expression), visitor)?;
        }
        Statement::If(value) => {
            visit_node(NodeRef::Expression(&value.test), visitor)?;
            visit_node(NodeRef::Statement(&value.consequent), visitor)?;
            if let Some(alternate) = &value.alternate {
                visit_node(NodeRef::Statement(alternate), visitor)?;
            }
        }
        Statement::Switch(value) => {
            visit_node(NodeRef::Expression(&value.discriminant), visitor)?;
            for case in &value.cases {
                visit_node(NodeRef::SwitchCase(case), visitor)?;
            }
        }
        Statement::For(value) => {
            if let Some(initializer) = &value.initializer {
                match initializer {
                    ForInitializer::Variable(declaration) => {
                        visit_variable_declaration(declaration, visitor)?;
                    }
                    ForInitializer::Expression(expression) => {
                        visit_node(NodeRef::Expression(expression), visitor)?;
                    }
                }
            }
            if let Some(test) = &value.test {
                visit_node(NodeRef::Expression(test), visitor)?;
            }
            if let Some(update) = &value.update {
                visit_node(NodeRef::Expression(update), visitor)?;
            }
            visit_node(NodeRef::Statement(&value.body), visitor)?;
        }
        Statement::ForIn(value) => {
            visit_for_binding(&value.binding, visitor)?;
            visit_node(NodeRef::Expression(&value.object), visitor)?;
            visit_node(NodeRef::Statement(&value.body), visitor)?;
        }
        Statement::ForOf(value) => {
            visit_for_binding(&value.binding, visitor)?;
            visit_node(NodeRef::Expression(&value.iterable), visitor)?;
            visit_node(NodeRef::Statement(&value.body), visitor)?;
        }
        Statement::While(value) => {
            visit_node(NodeRef::Expression(&value.test), visitor)?;
            visit_node(NodeRef::Statement(&value.body), visitor)?;
        }
        Statement::DoWhile(value) => {
            visit_node(NodeRef::Statement(&value.body), visitor)?;
            visit_node(NodeRef::Expression(&value.test), visitor)?;
        }
        Statement::Try(value) => {
            visit_node(NodeRef::Block(&value.block), visitor)?;
            if let Some(handler) = &value.handler {
                visit_node(NodeRef::CatchClause(handler), visitor)?;
            }
            if let Some(finalizer) = &value.finalizer {
                visit_node(NodeRef::Block(finalizer), visitor)?;
            }
        }
        Statement::With(value) => {
            visit_node(NodeRef::Expression(&value.object), visitor)?;
            visit_node(NodeRef::Statement(&value.body), visitor)?;
        }
        Statement::Labeled(value) => visit_node(NodeRef::Statement(&value.body), visitor)?,
        Statement::Return(value) => {
            if let Some(argument) = &value.argument {
                visit_node(NodeRef::Expression(argument), visitor)?;
            }
        }
        Statement::Throw(value) => visit_node(NodeRef::Expression(&value.argument), visitor)?,
        _ => {}
    }
    ControlFlow::Continue(())
}

fn visit_expression<'ast, V>(
    expression: &'ast crate::syntax::Expr,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match expression.data() {
        Expression::Identifier(identifier) => {
            visit_node(NodeRef::Identifier(identifier), visitor)?;
        }
        Expression::Literal(Literal::String(string)) => {
            visit_node(NodeRef::StringLiteral(string), visitor)?;
        }
        Expression::Template(value) => {
            for expression in &value.expressions {
                visit_node(NodeRef::Expression(expression), visitor)?;
            }
        }
        Expression::TaggedTemplate(value) => {
            visit_node(NodeRef::Expression(&value.tag), visitor)?;
            for expression in &value.template.expressions {
                visit_node(NodeRef::Expression(expression), visitor)?;
            }
        }
        Expression::Array(array) => {
            for element in &array.elements {
                match element {
                    ArrayElement::Expression(value) => {
                        visit_node(NodeRef::Expression(value), visitor)?
                    }
                    ArrayElement::Spread(value) => {
                        visit_node(NodeRef::Expression(&value.argument), visitor)?
                    }
                    ArrayElement::Elision | ArrayElement::Missing(_) => {}
                }
            }
        }
        Expression::Object(object) => {
            for member in &object.members {
                visit_node(NodeRef::ObjectMember(member), visitor)?;
            }
        }
        Expression::Function(value) => visit_function(&value.function, visitor)?,
        Expression::Class(value) => visit_class(&value.class, visitor)?,
        Expression::Arrow(value) => {
            visit_type_parameters(value.type_parameters.as_ref(), visitor)?;
            for parameter in &value.parameters {
                visit_node(NodeRef::Parameter(parameter), visitor)?;
            }
            if let Some(return_type) = &value.return_type {
                visit_node(NodeRef::TypeAnnotation(return_type), visitor)?;
            }
            visit_function_body(&value.body, visitor)?;
        }
        Expression::Call(call) => {
            visit_node(NodeRef::Expression(&call.callee), visitor)?;
            visit_type_arguments(call.type_arguments.as_ref(), visitor)?;
            for argument in &call.arguments {
                match argument {
                    CallArgument::Expression(value) => {
                        visit_node(NodeRef::Expression(value), visitor)?
                    }
                    CallArgument::Spread(value) => {
                        visit_node(NodeRef::Expression(&value.argument), visitor)?
                    }
                    CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Member(value) => {
            visit_node(NodeRef::Expression(&value.object), visitor)?;
            visit_member_property(&value.property, visitor)?;
        }
        Expression::New(call) => {
            visit_node(NodeRef::Expression(&call.callee), visitor)?;
            visit_type_arguments(call.type_arguments.as_ref(), visitor)?;
            for argument in &call.arguments {
                match argument {
                    CallArgument::Expression(value) => {
                        visit_node(NodeRef::Expression(value), visitor)?
                    }
                    CallArgument::Spread(value) => {
                        visit_node(NodeRef::Expression(&value.argument), visitor)?
                    }
                    CallArgument::Missing(_) => {}
                }
            }
        }
        Expression::Await(value) => {
            visit_node(NodeRef::Expression(&value.argument), visitor)?;
        }
        Expression::Unary(value) => {
            visit_node(NodeRef::Expression(&value.argument), visitor)?;
        }
        Expression::Yield(value) => {
            if let Some(argument) = &value.argument {
                visit_node(NodeRef::Expression(argument), visitor)?;
            }
        }
        Expression::Update(value) => {
            visit_node(NodeRef::AssignmentTarget(&value.argument), visitor)?;
        }
        Expression::Binary(value) => {
            visit_node(NodeRef::Expression(&value.left), visitor)?;
            visit_node(NodeRef::Expression(&value.right), visitor)?;
        }
        Expression::Logical(value) => {
            visit_node(NodeRef::Expression(&value.left), visitor)?;
            visit_node(NodeRef::Expression(&value.right), visitor)?;
        }
        Expression::Conditional(value) => {
            visit_node(NodeRef::Expression(&value.test), visitor)?;
            visit_node(NodeRef::Expression(&value.consequent), visitor)?;
            visit_node(NodeRef::Expression(&value.alternate), visitor)?;
        }
        Expression::Assignment(value) => {
            visit_node(NodeRef::AssignmentTarget(&value.left), visitor)?;
            visit_node(NodeRef::Expression(&value.right), visitor)?;
        }
        Expression::Sequence(value) => {
            for expression in &value.expressions {
                visit_node(NodeRef::Expression(expression), visitor)?;
            }
        }
        Expression::Parenthesized(value) => visit_node(NodeRef::Expression(value), visitor)?,
        Expression::As(value) => {
            visit_node(NodeRef::Expression(&value.expression), visitor)?;
            if let Some(node) = &value.type_node {
                visit_node(NodeRef::TypeNode(node), visitor)?;
            }
        }
        Expression::Satisfies(value) => {
            visit_node(NodeRef::Expression(&value.expression), visitor)?;
            visit_node(NodeRef::TypeNode(&value.type_node), visitor)?;
        }
        Expression::TypeAssertion(value) => {
            visit_node(NodeRef::TypeNode(&value.type_node), visitor)?;
            visit_node(NodeRef::Expression(&value.expression), visitor)?;
        }
        Expression::NonNull(value) => visit_node(NodeRef::Expression(&value.expression), visitor)?,
        Expression::Import(value) => {
            visit_node(NodeRef::Expression(&value.source), visitor)?;
            if let Some(options) = &value.options {
                visit_node(NodeRef::Expression(options), visitor)?;
            }
        }
        Expression::JsxElement(value) => {
            visit_node(NodeRef::JsxOpeningElement(&value.opening), visitor)?;
            for child in &value.children {
                visit_jsx_child(child, visitor)?;
            }
            visit_node(NodeRef::JsxClosingElement(&value.closing), visitor)?;
        }
        Expression::JsxSelfClosingElement(value) => {
            visit_jsx_element_name(&value.name, visitor)?;
            visit_jsx_attributes(&value.attributes, visitor)?;
        }
        Expression::JsxFragment(value) => {
            for child in &value.children {
                visit_jsx_child(child, visitor)?;
            }
        }
        _ => {}
    }
    ControlFlow::Continue(())
}
fn visit_jsx_element_name<'ast, V>(
    name: &'ast JsxElementName,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match name {
        JsxElementName::Identifier(identifier) => {
            visit_node(NodeRef::Identifier(identifier), visitor)?
        }
        JsxElementName::Member(member) => {
            visit_jsx_element_name(&member.object, visitor)?;
            visit_node(NodeRef::Identifier(&member.property), visitor)?;
        }
        JsxElementName::Namespace(name) => {
            visit_node(NodeRef::Identifier(&name.namespace), visitor)?;
            visit_node(NodeRef::Identifier(&name.name), visitor)?;
        }
    }
    ControlFlow::Continue(())
}

fn visit_jsx_child<'ast, V>(child: &'ast JsxChild, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match child {
        JsxChild::Text(node) => visit_node(NodeRef::JsxText(node), visitor)?,
        JsxChild::ExpressionContainer(node) => {
            visit_node(NodeRef::JsxExpressionContainer(node), visitor)?
        }
        JsxChild::Spread(node) => visit_node(NodeRef::JsxSpreadChild(node), visitor)?,
        JsxChild::Element(node) => visit_node(NodeRef::Expression(node), visitor)?,
    }
    ControlFlow::Continue(())
}

fn visit_jsx_attribute<'ast, V>(
    node: &'ast JsxAttributeNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    let data = node.data();
    match &data.name {
        JsxAttributeName::Identifier(identifier) => {
            visit_node(NodeRef::Identifier(identifier), visitor)?
        }
        JsxAttributeName::Namespace(name) => {
            visit_node(NodeRef::Identifier(&name.namespace), visitor)?;
            visit_node(NodeRef::Identifier(&name.name), visitor)?;
        }
    }
    if let Some(initializer) = &data.initializer {
        match initializer {
            JsxAttributeInitializer::String(string) => {
                visit_node(NodeRef::StringLiteral(string), visitor)?
            }
            JsxAttributeInitializer::Expression(expression) => {
                visit_node(NodeRef::JsxExpressionContainer(expression), visitor)?
            }
        }
    }
    ControlFlow::Continue(())
}

fn visit_jsx_attributes<'ast, V>(
    attributes: &'ast [JsxAttributeItem],
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    for entry in attributes {
        match entry {
            JsxAttributeItem::Attribute(attribute) => {
                visit_node(NodeRef::JsxAttribute(attribute), visitor)?
            }
            JsxAttributeItem::Spread(spread) => {
                visit_node(NodeRef::JsxSpreadAttribute(spread), visitor)?
            }
        }
    }
    ControlFlow::Continue(())
}

fn visit_jsx_opening_element<'ast, V>(
    node: &'ast JsxOpeningElementNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    let data = node.data();
    visit_jsx_element_name(&data.name, visitor)?;
    visit_jsx_attributes(&data.attributes, visitor)?;
    ControlFlow::Continue(())
}

fn visit_variable_declaration<'ast, V>(
    declaration: &'ast VariableDeclaration,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    for declarator in &declaration.declarations {
        visit_node(NodeRef::VariableDeclarator(declarator), visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_for_binding<'ast, V>(binding: &'ast ForBinding, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match binding {
        ForBinding::Variable(declaration) => visit_variable_declaration(declaration, visitor),
        ForBinding::Target(target) => visit_node(NodeRef::AssignmentTarget(target), visitor),
    }
}

fn visit_type_parameters<'ast, V>(
    parameters: Option<&'ast TypeParameterList>,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    if let Some(parameters) = parameters {
        for parameter in &parameters.parameters {
            visit_node(NodeRef::TypeParameter(parameter), visitor)?;
        }
    }
    ControlFlow::Continue(())
}

fn visit_type_arguments<'ast, V>(
    arguments: Option<&'ast TypeArgumentList>,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    if let Some(arguments) = arguments {
        for argument in &arguments.arguments {
            visit_node(NodeRef::TypeNode(argument), visitor)?;
        }
    }
    ControlFlow::Continue(())
}

fn visit_parameter<'ast, V>(
    parameter: &'ast ParameterNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    let data = parameter.data();
    for decorator in &data.decorators {
        visit_node(NodeRef::Decorator(decorator), visitor)?;
    }
    visit_node(NodeRef::BindingPattern(&data.binding), visitor)?;
    if let Some(annotation) = &data.type_annotation {
        visit_node(NodeRef::TypeAnnotation(annotation), visitor)?;
    }
    if let Some(initializer) = &data.initializer {
        visit_node(NodeRef::Expression(initializer), visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_function<'ast, V>(function: &'ast FunctionLike, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    for decorator in &function.decorators {
        visit_node(NodeRef::Decorator(decorator), visitor)?;
    }
    visit_type_parameters(function.type_parameters.as_ref(), visitor)?;
    for parameter in &function.parameters {
        visit_node(NodeRef::Parameter(parameter), visitor)?;
    }
    if let Some(return_type) = &function.return_type {
        visit_node(NodeRef::TypeAnnotation(return_type), visitor)?;
    }
    if let Some(body) = &function.body {
        visit_function_body(body, visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_function_body<'ast, V>(body: &'ast FunctionBody, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match body {
        FunctionBody::Block(block) => visit_node(NodeRef::Block(block), visitor),
        FunctionBody::Expression(expression) => {
            visit_node(NodeRef::Expression(expression), visitor)
        }
        FunctionBody::Missing(_) => ControlFlow::Continue(()),
    }
}

fn visit_class<'ast, V>(class: &'ast ClassDeclaration, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    for decorator in &class.decorators {
        visit_node(NodeRef::Decorator(decorator), visitor)?;
    }
    visit_type_parameters(class.type_parameters.as_ref(), visitor)?;
    if let Some(heritage) = &class.extends {
        visit_node(NodeRef::Expression(&heritage.expression), visitor)?;
        visit_type_arguments(heritage.type_arguments.as_ref(), visitor)?;
    }
    for implementation in &class.implements {
        visit_node(NodeRef::TypeNode(implementation), visitor)?;
    }
    for member in &class.members {
        visit_node(NodeRef::ClassMember(member), visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_property_name<'ast, V>(name: &'ast PropertyName, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    if let PropertyName::Computed(expression) = name {
        visit_node(NodeRef::Expression(expression), visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_member_property<'ast, V>(
    property: &'ast MemberProperty,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    if let MemberProperty::Computed(expression) = property {
        visit_node(NodeRef::Expression(expression), visitor)?;
    }
    ControlFlow::Continue(())
}

fn visit_pattern<'ast, V>(pattern: &'ast Pattern, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match pattern.data() {
        BindingPattern::Object(object) => {
            for property in &object.properties {
                visit_property_name(&property.name, visitor)?;
                visit_node(NodeRef::BindingPattern(&property.binding), visitor)?;
                if let Some(initializer) = &property.initializer {
                    visit_node(NodeRef::Expression(initializer), visitor)?;
                }
            }
        }
        BindingPattern::Array(array) => {
            for element in &array.elements {
                if let ArrayBindingElement::Binding(binding) = element {
                    visit_node(NodeRef::BindingPattern(binding), visitor)?;
                }
            }
        }
        BindingPattern::Rest(rest) => {
            visit_node(NodeRef::BindingPattern(&rest.argument), visitor)?;
        }
        BindingPattern::Assignment(assignment) => {
            visit_node(NodeRef::BindingPattern(&assignment.left), visitor)?;
            visit_node(NodeRef::Expression(&assignment.right), visitor)?;
        }
        BindingPattern::Identifier(_) | BindingPattern::Missing(_) => {}
    }
    ControlFlow::Continue(())
}

fn visit_assignment_target<'ast, V>(
    target: &'ast AssignmentTargetNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match target.data() {
        AssignmentTarget::Member(member) => {
            visit_node(NodeRef::Expression(&member.object), visitor)?;
            visit_member_property(&member.property, visitor)?;
        }
        AssignmentTarget::Object(object) => {
            for property in &object.properties {
                visit_property_name(&property.name, visitor)?;
                visit_node(NodeRef::AssignmentTarget(&property.target), visitor)?;
                if let Some(initializer) = &property.initializer {
                    visit_node(NodeRef::Expression(initializer), visitor)?;
                }
            }
        }
        AssignmentTarget::Array(array) => {
            for element in &array.elements {
                if let AssignmentArrayElement::Target(target)
                | AssignmentArrayElement::Rest(target) = element
                {
                    visit_node(NodeRef::AssignmentTarget(target), visitor)?;
                }
            }
        }
        AssignmentTarget::Identifier(_) | AssignmentTarget::Missing(_) => {}
        AssignmentTarget::Invalid(operand) => {
            visit_node(NodeRef::Expression(operand), visitor)?;
        }
    }
    ControlFlow::Continue(())
}

fn visit_object_member<'ast, V>(
    member: &'ast ObjectMemberNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match member.data() {
        ObjectMember::Property(property) => {
            visit_property_name(&property.name, visitor)?;
            visit_node(NodeRef::Expression(&property.value), visitor)?;
        }
        ObjectMember::Method(method) => {
            visit_property_name(&method.name, visitor)?;
            visit_function(&method.function, visitor)?;
        }
        ObjectMember::Spread(spread) => {
            visit_node(NodeRef::Expression(&spread.argument), visitor)?;
        }
        ObjectMember::Missing(_) => {}
    }
    ControlFlow::Continue(())
}

fn visit_class_member<'ast, V>(
    member: &'ast ClassMemberNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match member.data() {
        ClassMember::Constructor(constructor) => {
            for decorator in &constructor.decorators {
                visit_node(NodeRef::Decorator(decorator), visitor)?;
            }
            for parameter in &constructor.parameters {
                visit_node(NodeRef::Parameter(parameter), visitor)?;
            }
            visit_node(NodeRef::Block(&constructor.body), visitor)?;
        }
        ClassMember::Method(method) => {
            visit_property_name(&method.name, visitor)?;
            visit_function(&method.function, visitor)?;
        }
        ClassMember::Property(property) => {
            for decorator in &property.decorators {
                visit_node(NodeRef::Decorator(decorator), visitor)?;
            }
            visit_property_name(&property.name, visitor)?;
            if let Some(annotation) = &property.type_annotation {
                visit_node(NodeRef::TypeAnnotation(annotation), visitor)?;
            }
            if let Some(initializer) = &property.initializer {
                visit_node(NodeRef::Expression(initializer), visitor)?;
            }
        }
        ClassMember::AutoAccessor(accessor) => {
            for decorator in &accessor.decorators {
                visit_node(NodeRef::Decorator(decorator), visitor)?;
            }
            visit_property_name(&accessor.name, visitor)?;
            if let Some(annotation) = &accessor.type_annotation {
                visit_node(NodeRef::TypeAnnotation(annotation), visitor)?;
            }
            if let Some(initializer) = &accessor.initializer {
                visit_node(NodeRef::Expression(initializer), visitor)?;
            }
        }
        ClassMember::StaticBlock(block) => visit_node(NodeRef::Block(block), visitor)?,
        ClassMember::IndexSignature(signature) => {
            for parameter in &signature.parameters {
                visit_node(NodeRef::Parameter(parameter), visitor)?;
            }
            visit_node(NodeRef::TypeAnnotation(&signature.type_annotation), visitor)?;
        }
        ClassMember::Missing(_) | ClassMember::Semicolon => {}
    }
    ControlFlow::Continue(())
}

fn visit_function_type<'ast, V>(
    function: &'ast FunctionType,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    visit_type_parameters(function.type_parameters.as_ref(), visitor)?;
    for parameter in &function.parameters {
        visit_node(NodeRef::TypeAnnotation(&parameter.type_annotation), visitor)?;
    }
    visit_node(NodeRef::TypeNode(&function.return_type), visitor)
}

fn visit_type_member<'ast, V>(
    member: &'ast TypeMemberNode,
    visitor: &mut V,
) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match member.data() {
        TypeMember::Property(property) => {
            visit_property_name(&property.name, visitor)?;
            if let Some(annotation) = &property.type_annotation {
                visit_node(NodeRef::TypeAnnotation(annotation), visitor)?;
            }
        }
        TypeMember::Method(method) => {
            visit_property_name(&method.name, visitor)?;
            visit_function_type(&method.function, visitor)?;
        }
        TypeMember::Call(call) => visit_function_type(&call.function, visitor)?,
        TypeMember::Construct(construct) => {
            visit_function_type(&construct.function.function, visitor)?
        }
        TypeMember::Index(index) => {
            for parameter in &index.parameters {
                visit_node(NodeRef::TypeAnnotation(&parameter.type_annotation), visitor)?;
            }
            visit_node(NodeRef::TypeAnnotation(&index.type_annotation), visitor)?;
        }
        TypeMember::Missing(_) => {}
    }
    ControlFlow::Continue(())
}

fn visit_type<'ast, V>(node: &'ast Ty, visitor: &mut V) -> ControlFlow<V::Break>
where
    V: Visitor<'ast>,
{
    match node.data() {
        TypeNode::Literal(TypeLiteral::Unary { operand, .. }) => {
            visit_node(NodeRef::TypeNode(operand), visitor)?;
        }
        TypeNode::Reference(reference) => {
            visit_type_arguments(reference.type_arguments.as_ref(), visitor)?;
        }
        TypeNode::Union(types) | TypeNode::Intersection(types) => {
            for node in types {
                visit_node(NodeRef::TypeNode(node), visitor)?;
            }
        }
        TypeNode::Array(element) | TypeNode::Parenthesized(element) => {
            visit_node(NodeRef::TypeNode(element), visitor)?;
        }
        TypeNode::Tuple(tuple) => {
            for element in &tuple.elements {
                visit_node(NodeRef::TypeNode(&element.type_node), visitor)?;
            }
        }
        TypeNode::Object(object) => {
            for member in &object.members {
                visit_node(NodeRef::TypeMember(member), visitor)?;
            }
        }
        TypeNode::Function(function) => visit_function_type(function, visitor)?,
        TypeNode::Constructor(constructor) => visit_function_type(&constructor.function, visitor)?,
        TypeNode::Query(query) => visit_type_arguments(query.type_arguments.as_ref(), visitor)?,
        TypeNode::Operator { operand, .. } => visit_node(NodeRef::TypeNode(operand), visitor)?,
        TypeNode::IndexedAccess(indexed) => {
            visit_node(NodeRef::TypeNode(&indexed.object_type), visitor)?;
            visit_node(NodeRef::TypeNode(&indexed.index_type), visitor)?;
        }
        TypeNode::Conditional(conditional) => {
            visit_node(NodeRef::TypeNode(&conditional.check_type), visitor)?;
            visit_node(NodeRef::TypeNode(&conditional.extends_type), visitor)?;
            visit_node(NodeRef::TypeNode(&conditional.true_type), visitor)?;
            visit_node(NodeRef::TypeNode(&conditional.false_type), visitor)?;
        }
        TypeNode::Mapped(mapped) => {
            visit_node(NodeRef::TypeParameter(&mapped.parameter), visitor)?;
            if let Some(name) = &mapped.name_type {
                visit_node(NodeRef::TypeNode(name), visitor)?;
            }
            if let Some(value) = &mapped.value_type {
                visit_node(NodeRef::TypeNode(value), visitor)?;
            }
        }
        TypeNode::Infer(infer) => visit_node(NodeRef::TypeParameter(&infer.parameter), visitor)?,
        TypeNode::Import(import) => visit_type_arguments(import.type_arguments.as_ref(), visitor)?,
        TypeNode::TemplateLiteral(template) => {
            for node in &template.types {
                visit_node(NodeRef::TypeNode(node), visitor)?;
            }
        }
        TypeNode::Predicate(predicate) => {
            if let Some(node) = &predicate.type_node {
                visit_node(NodeRef::TypeNode(node), visitor)?;
            }
        }
        TypeNode::Keyword(_) | TypeNode::Literal(_) | TypeNode::This | TypeNode::Missing(_) => {}
    }
    ControlFlow::Continue(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::{TextRange, Utf16Pos};

    fn range(start: usize, end: usize) -> TextRange {
        TextRange::new(Utf16Pos::new(start), Utf16Pos::new(end)).unwrap()
    }

    struct Recorder(Vec<NodeId>);

    impl<'ast> Visitor<'ast> for Recorder {
        type Break = ();

        fn visit(&mut self, node: NodeRef<'ast>) -> ControlFlow<Self::Break> {
            if let Some(id) = node.id() {
                self.0.push(id);
            }
            ControlFlow::Continue(())
        }
    }

    #[test]
    fn binary_children_are_visited_in_source_order() {
        let left = Node::new(NodeId::new(2), range(0, 1), Expression::This);
        let right = Node::new(NodeId::new(3), range(4, 5), Expression::Super);
        let root = Node::new(
            NodeId::new(1),
            range(0, 5),
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::Add,
                left: Box::new(left),
                right: Box::new(right),
            }),
        );
        let mut recorder = Recorder(Vec::new());
        let result = visit_node(NodeRef::Expression(&root), &mut recorder);
        assert!(result.is_continue());
        assert_eq!(recorder.0, [NodeId::new(1), NodeId::new(2), NodeId::new(3)]);
    }

    struct StopAt(NodeId);

    impl<'ast> Visitor<'ast> for StopAt {
        type Break = NodeId;

        fn visit(&mut self, node: NodeRef<'ast>) -> ControlFlow<Self::Break> {
            match node.id() {
                Some(id) if id == self.0 => ControlFlow::Break(id),
                _ => ControlFlow::Continue(()),
            }
        }
    }

    #[test]
    fn break_stops_before_later_siblings() {
        let left = Node::new(NodeId::new(2), range(0, 1), Expression::This);
        let right = Node::new(NodeId::new(3), range(4, 5), Expression::Super);
        let root = Node::new(
            NodeId::new(1),
            range(0, 5),
            Expression::Binary(BinaryExpression {
                operator: BinaryOperator::Add,
                left: Box::new(left),
                right: Box::new(right),
            }),
        );
        assert_eq!(
            visit_node(NodeRef::Expression(&root), &mut StopAt(NodeId::new(2))),
            ControlFlow::Break(NodeId::new(2))
        );
    }
}
